use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsStr,
    fmt, fs, io,
    io::{Read, Write},
    num::{NonZeroU64, NonZeroUsize},
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
    sync::{Arc, Mutex, OnceLock},
    thread,
    time::Instant,
};

#[cfg(test)]
use npa_cert::decode_module_cert;
use npa_cert::{
    decode_module_cert_header, decode_module_cert_observed,
    verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations,
    verify_decoded_module_cert_with_observations,
    verify_retained_decoded_module_cert_with_import_refs_and_kernel_options_and_observations,
    verify_retained_decoded_module_cert_with_observations, AxiomPolicy, CertError, CertHeader,
    CertificateMeasurementDetail, CertificateMeasurementSummary, CertificatePayloadObservation,
    CertificateTermMaterializationObservation, CertificateVerificationObservationSinks,
    CoreFeature, DeclCert, DeclPayload, ModuleCert, ModuleHashes, Name, RetainedDecodedModuleCert,
    TermNode, VerifiedModule, VerifierSession,
};
use npa_checker_ref::{
    check_certificate, check_certificate_with_observation, ReferenceCertificateSection,
    ReferenceCheckError, ReferenceCheckErrorKind, ReferenceCheckObservation, ReferenceCheckReason,
    ReferenceCheckResult, ReferenceCheckedModule, ReferenceCheckerPolicy, ReferenceCoreFeature,
    ReferenceImportStore, ReferenceModuleName, ReferenceTrustMode,
};
use npa_kernel::KernelExecutionOptions;
#[cfg(any(test, feature = "planning-benchmark"))]
use npa_package::PackageGraphPlanningCounterSummary;
use npa_package::{
    build_package_lock_graph, format_package_hash, package_audit_process_memo_key,
    package_file_hash, package_import_context_export_cache_entry_json,
    package_import_context_export_cache_key, parse_package_import_context_export_cache_entry_json,
    validate_observed_package_lock_against_manifest_indexed,
    validate_package_lock_against_manifest_graph, validate_package_lock_against_manifest_indexed,
    validate_package_path, HashedPackageLockArtifact, IndexedPackageLockGraph,
    IndexedPackageLockGraphError, PackageArtifactErrorReason, PackageAuditCacheKeyInput,
    PackageAuditCheckerIdentity, PackageAuditImportIdentity, PackageCertificateArtifactSnapshot,
    PackageHash, PackageImportContextExportCacheEntry, PackageImportContextExportCacheKeyInput,
    PackageImportContextExportData, PackageLockEntry, PackageLockEntryOrigin, PackageLockGraph,
    PackageLockManifest, PackageLockResolvedImport, PackagePath, PreparedArtifactRelease,
    PreparedArtifactReleaseReason, PreparedPackageArtifactView, PreparedPackageArtifacts,
    ValidatedPackageManifest, CHECKER_PROFILE_REFERENCE_V0_1, PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA,
    PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA,
    PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR, PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA,
};

use crate::independent_checker::{
    independent_checker_file_hash, independent_checker_request_materialize,
    parse_independent_checker_import_lock_manifest, IndependentCheckerCommandError,
    IndependentCheckerImportLockCertificate, IndependentCheckerImportLockEntry,
    IndependentCheckerImportLockManifest, IndependentCheckerMachineCheckRequest,
    IndependentCheckerRequestStoreManifest, IndependentCheckerRunnerPolicy,
};
use crate::types::{machine_api_name_canonical_bytes, parse_module_name_wire};
use crate::{
    PackageCertificateArtifactObservation, PerformanceDeclarationMeasurement,
    PerformanceMeasurementLabel, PerformanceMeasurementMode, PerformanceMeasurementRecorder,
    PerformanceMeasurementReport, PerformanceModuleMeasurement, PerformancePackageLayerMeasurement,
    PerformancePackageModuleShardingMeasurement, PerformancePackageShardCostModel,
    PerformancePackageShardMeasurement, PerformancePackageShardMemoryModel,
    PerformancePackageShardReductionReason, PerformancePackageShardingMeasurement,
    PerformanceWorkerMeasurement, PERFORMANCE_DECLARATION_DETAIL_LIMIT,
    PERFORMANCE_MODULE_DETAIL_LIMIT, PERFORMANCE_WORKER_DETAIL_LIMIT,
};

const PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;
const PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1: u64 = 4_096;
const PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1: u64 = 1024 * 1024 * 1024;
const PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1: u64 = 8 * 1024 * 1024;
const PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1: u64 = 4;
const PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2: u64 = 268_435_456;
static NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
thread_local! {
    static SNAPSHOT_MEMO_HEADER_DECODE_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// Result type for source-free package verification.
pub type PackageVerificationResult<T> = Result<T, PackageVerificationError>;

/// Certificate artifact bytes supplied by the caller.
#[derive(Clone, Debug)]
pub struct PackageCertificateArtifact<'a> {
    /// Package-relative certificate path.
    pub path: PackagePath,
    /// Exact certificate bytes at [`Self::path`].
    pub bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug)]
enum PackageCertificateInput<'a> {
    Raw {
        bytes: &'a [u8],
    },
    Hashed {
        bytes: &'a [u8],
        file_hash: PackageHash,
    },
    Prepared {
        artifact: &'a PackageCertificateArtifactSnapshot,
    },
}

impl<'a> PackageCertificateInput<'a> {
    fn bytes(self) -> &'a [u8] {
        match self {
            Self::Raw { bytes } => bytes,
            Self::Hashed { bytes, .. } => bytes,
            Self::Prepared { artifact } => artifact.bytes(),
        }
    }

    fn observed_file_hash(self) -> PackageHash {
        match self {
            Self::Raw { bytes } => package_file_hash(bytes),
            Self::Hashed { file_hash, .. } => file_hash,
            Self::Prepared { artifact } => artifact.file_hash(),
        }
    }

    fn retained_decoded(self) -> Option<&'a RetainedDecodedModuleCert> {
        match self {
            Self::Prepared { artifact } => artifact.retained_decoded(),
            Self::Raw { .. } | Self::Hashed { .. } => None,
        }
    }

    fn retained_header(self) -> Option<&'a CertHeader> {
        match self {
            Self::Prepared { artifact } => artifact.decoded_header(),
            Self::Raw { .. } | Self::Hashed { .. } => None,
        }
    }

    fn is_owned(self) -> bool {
        !matches!(self, Self::Raw { .. })
    }

    fn reuses_file_hash(self) -> bool {
        !matches!(self, Self::Raw { .. })
    }
}

/// Package verification mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationMode {
    /// Fast local verifier backed by `npa_cert::verify_module_cert`.
    FastKernel,
    /// Source-free independent reference checker mode backed by `npa-checker-ref`.
    Reference,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PackageFastParallelStrategy {
    #[cfg(test)]
    LegacyLayer,
    ShardRunner,
}

/// Execution options for source-free package verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerificationExecutionOptions {
    /// Maximum worker count for verifier implementations that support it.
    pub jobs: usize,
    /// Requested modules for partial verification.
    ///
    /// The verifier may also execute transitive imports required to construct
    /// a sound import context for these modules.
    pub selected_modules: Option<BTreeSet<Name>>,
    /// Optional process-local memoization mode.
    pub memoization: PackageVerificationMemoMode,
    /// Decode/import cache policy. This is independent of observation mode.
    pub decode_cache: PackageVerificationDecodeCacheMode,
    /// Collect counters for the selected decode-cache policy. This option does
    /// not enable a cache or permit persistent cache I/O.
    pub collect_decode_cache_counters: bool,
    /// Diagnostic measurement mode. This never changes verifier policy.
    pub measurement_mode: PerformanceMeasurementMode,
}

impl Default for PackageVerificationExecutionOptions {
    fn default() -> Self {
        Self {
            jobs: 1,
            selected_modules: None,
            memoization: PackageVerificationMemoMode::Disabled,
            decode_cache: PackageVerificationDecodeCacheMode::Disabled,
            collect_decode_cache_counters: false,
            measurement_mode: PerformanceMeasurementMode::Off,
        }
    }
}

/// Decode/import caching policy for one verifier operation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PackageVerificationDecodeCacheMode {
    /// Do not read or write process-local or persistent decode caches.
    #[default]
    Disabled,
    /// Reuse certificate and import-context decoding within this process.
    ProcessLocal,
    /// Also reuse and write the persistent import-context export cache.
    ProcessLocalAndPersistent,
}

impl PackageVerificationDecodeCacheMode {
    const fn process_local(self) -> bool {
        !matches!(self, Self::Disabled)
    }

    const fn persistent(self) -> bool {
        matches!(self, Self::ProcessLocalAndPersistent)
    }
}

/// Process-local package verifier memoization mode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackageVerificationMemoMode {
    /// Do not read or write the process-local verifier memo.
    Disabled,
    /// Reuse exact verifier results through the supplied caller-owned store.
    ProcessLocal(PackageVerificationProcessMemoHandle),
}

impl PackageVerificationMemoMode {
    /// Return whether process-local memoization is enabled.
    pub const fn is_enabled(&self) -> bool {
        match self {
            Self::Disabled => false,
            Self::ProcessLocal(_) => true,
        }
    }
}

/// Explicit capacity limits for one caller-owned package verification memo.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageVerificationProcessMemoLimits {
    /// Maximum number of exact verifier results retained by the handle.
    pub max_entries: NonZeroUsize,
    /// Maximum aggregate certificate-byte weight retained by the handle.
    pub max_weighted_certificate_bytes: NonZeroU64,
}

/// Stable management error for a caller-owned process memo.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationProcessMemoAccessError {
    /// The handle's mutex was poisoned by a panicking caller.
    Poisoned,
}

/// Coherent bounded-store statistics for one caller-owned process memo.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageVerificationProcessMemoStats {
    /// Number of currently retained exact results.
    pub retained_entries: usize,
    /// Aggregate checked-certificate byte weight currently retained.
    pub retained_weighted_certificate_bytes: u64,
    /// Saturating count of successful lookups.
    pub cumulative_hits: u64,
    /// Saturating count of exact-key lookup misses.
    pub cumulative_misses: u64,
    /// Saturating count of accepted insertions.
    pub cumulative_inserted: u64,
    /// Saturating count of capacity evictions.
    pub cumulative_evicted: u64,
    /// Saturating count of individually oversized rejected insertions.
    pub cumulative_rejected_oversize: u64,
}

/// Per-run process-local verifier memo counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageVerificationMemoCounters {
    /// Exact memo hits reused in this verifier run.
    pub hits: usize,
    /// Exact memo misses in this verifier run.
    pub misses: usize,
    /// New exact verifier results inserted by this verifier run.
    pub inserted: usize,
    /// Exact execution-scoped memo keys built in this verifier run.
    pub keys_built: usize,
    /// Certificate bytes hashed while constructing memo keys.
    pub certificate_bytes_hashed: u64,
    /// Entries evicted by accepted insertions in this verifier run.
    pub evicted: usize,
    /// Individually oversized entries rejected in this verifier run.
    pub rejected_oversize: usize,
    /// Store-access failures that disabled memoization for this run.
    pub bypassed_store_unavailable: usize,
}

/// Per-run process-local certificate decode/import context cache counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageVerificationDecodeCacheCounters {
    /// Decoded certificate cache hits in this verifier run.
    pub certificate_hits: usize,
    /// Decoded certificate cache misses in this verifier run.
    pub certificate_misses: usize,
    /// Decoded certificate entries inserted in this verifier run.
    pub certificate_inserted: usize,
    /// Decoded certificate admissions rejected by the combined cache bounds.
    pub certificate_capacity_stops: usize,
    /// Import context cache hits in this verifier run.
    pub import_context_hits: usize,
    /// Import context cache misses in this verifier run.
    pub import_context_misses: usize,
    /// Import context entries inserted in this verifier run.
    pub import_context_inserted: usize,
    /// Import-context admissions rejected by the combined cache bounds.
    pub import_context_capacity_stops: usize,
    /// Disk-backed import-context export-data cache hits in this verifier run.
    pub import_context_disk_hits: usize,
    /// Disk-backed import-context export-data cache misses in this verifier run.
    pub import_context_disk_misses: usize,
    /// Disk-backed import-context export-data stale entries in this verifier run.
    pub import_context_disk_stale: usize,
    /// Disk-backed import-context export-data schema misses in this verifier run.
    pub import_context_disk_schema_misses: usize,
    /// Disk-backed import-context export-data entries written in this verifier run.
    pub import_context_disk_inserted: usize,
}

impl PackageVerificationDecodeCacheCounters {
    /// Return whether any decode/import cache activity was observed.
    pub const fn is_active(self) -> bool {
        self.certificate_hits > 0
            || self.certificate_misses > 0
            || self.certificate_inserted > 0
            || self.certificate_capacity_stops > 0
            || self.import_context_hits > 0
            || self.import_context_misses > 0
            || self.import_context_inserted > 0
            || self.import_context_capacity_stops > 0
            || self.import_context_disk_hits > 0
            || self.import_context_disk_misses > 0
            || self.import_context_disk_stale > 0
            || self.import_context_disk_schema_misses > 0
            || self.import_context_disk_inserted > 0
    }

    fn add(&mut self, other: Self) {
        self.certificate_hits = self.certificate_hits.saturating_add(other.certificate_hits);
        self.certificate_misses = self
            .certificate_misses
            .saturating_add(other.certificate_misses);
        self.certificate_inserted = self
            .certificate_inserted
            .saturating_add(other.certificate_inserted);
        self.certificate_capacity_stops = self
            .certificate_capacity_stops
            .saturating_add(other.certificate_capacity_stops);
        self.import_context_hits = self
            .import_context_hits
            .saturating_add(other.import_context_hits);
        self.import_context_misses = self
            .import_context_misses
            .saturating_add(other.import_context_misses);
        self.import_context_inserted = self
            .import_context_inserted
            .saturating_add(other.import_context_inserted);
        self.import_context_capacity_stops = self
            .import_context_capacity_stops
            .saturating_add(other.import_context_capacity_stops);
        self.import_context_disk_hits = self
            .import_context_disk_hits
            .saturating_add(other.import_context_disk_hits);
        self.import_context_disk_misses = self
            .import_context_disk_misses
            .saturating_add(other.import_context_disk_misses);
        self.import_context_disk_stale = self
            .import_context_disk_stale
            .saturating_add(other.import_context_disk_stale);
        self.import_context_disk_schema_misses = self
            .import_context_disk_schema_misses
            .saturating_add(other.import_context_disk_schema_misses);
        self.import_context_disk_inserted = self
            .import_context_disk_inserted
            .saturating_add(other.import_context_disk_inserted);
    }
}

impl PackageVerificationMemoCounters {
    /// Return whether any memo activity was observed.
    pub const fn is_active(self) -> bool {
        self.hits > 0
            || self.misses > 0
            || self.inserted > 0
            || self.keys_built > 0
            || self.certificate_bytes_hashed > 0
            || self.evicted > 0
            || self.rejected_oversize > 0
            || self.bypassed_store_unavailable > 0
    }
}

impl PackageVerificationMode {
    /// Return the stable mode string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastKernel => "fast-kernel",
            Self::Reference => "reference",
        }
    }
}

/// Source of the package verification verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationVerdictSource {
    /// Verdict came from the fast certificate verifier, not `npa-checker-ref`.
    FastKernelCertificateVerifier,
    /// Verdict came from `npa-checker-ref`.
    ReferenceChecker,
}

impl PackageVerificationVerdictSource {
    /// Return the stable verdict-source string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastKernelCertificateVerifier => "fast-kernel-certificate-verifier",
            Self::ReferenceChecker => "npa-checker-ref",
        }
    }

    /// Return whether this verdict came from the independent reference checker.
    pub const fn is_reference_checker_verdict(self) -> bool {
        match self {
            Self::FastKernelCertificateVerifier => false,
            Self::ReferenceChecker => true,
        }
    }
}

/// Overall package verification status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationStatus {
    /// Every lock entry verified successfully.
    Passed,
    /// At least one lock entry failed or was skipped after an earlier failure.
    Failed,
}

impl PackageVerificationStatus {
    /// Return the stable status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Passed => "passed",
            Self::Failed => "failed",
        }
    }
}

/// Per-module package verification status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageModuleVerificationStatus {
    /// Certificate bytes verified successfully.
    Passed,
    /// Certificate bytes failed deterministic fast-kernel verification.
    Failed,
    /// Certificate verification was not attempted after an earlier failure.
    Skipped,
}

impl PackageModuleVerificationStatus {
    /// Return the stable status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Passed => "passed",
            Self::Failed => "failed",
            Self::Skipped => "skipped",
        }
    }
}

/// Evidence source for one package verification module result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageModuleVerificationEvidence {
    /// The module was checked by the selected live checker in this run.
    LiveChecker,
    /// The module result was synthesized from the local audit cache.
    LocalAuditCache,
    /// The module result was synthesized from the local disk-backed verifier memo.
    DiskVerifierMemo,
    /// The module result was synthesized from the local reference summary cache.
    ReferenceSummaryCache,
}

impl PackageModuleVerificationEvidence {
    /// Return the stable evidence string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LiveChecker => "live-checker",
            Self::LocalAuditCache => "local-audit-cache",
            Self::DiskVerifierMemo => "disk-verifier-memo",
            Self::ReferenceSummaryCache => "reference-summary-cache",
        }
    }

    /// Return whether this result is proof evidence from a live checker.
    pub const fn is_proof_evidence(self) -> bool {
        match self {
            Self::LiveChecker => true,
            Self::LocalAuditCache | Self::DiskVerifierMemo | Self::ReferenceSummaryCache => false,
        }
    }
}

/// Source-free package verification report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerificationReport {
    /// Verification mode used for every module in this report.
    pub mode: PackageVerificationMode,
    /// Expected axiom-policy identity hash for this verification run.
    pub axiom_policy_hash: PackageHash,
    /// Explicit verdict source, to distinguish fast results from reference checker results.
    pub verdict_source: PackageVerificationVerdictSource,
    /// Convenience field that is true only for independent reference checker verdicts.
    pub reference_checker_verdict: bool,
    /// Whether any module result was synthesized from local audit cache.
    pub locally_accelerated: bool,
    /// Overall status.
    pub status: PackageVerificationStatus,
    /// Topological lock-graph verification order.
    pub topological_order: Vec<Name>,
    /// Per-module results in [`Self::topological_order`].
    pub modules: Vec<PackageModuleVerificationResult>,
    /// Process-local memo counters for this verifier run.
    pub memo_counters: PackageVerificationMemoCounters,
    /// Optional process-local decode/import cache counters for this verifier run.
    pub decode_cache_counters: Option<PackageVerificationDecodeCacheCounters>,
    /// Diagnostic-only measurements. These never contribute proof evidence.
    pub measurements: Option<PerformanceMeasurementReport>,
}

/// Per-module source-free verification result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageModuleVerificationResult {
    /// Module name from the package lock entry.
    pub module: Name,
    /// Verification mode used for this module.
    pub checker_mode: PackageVerificationMode,
    /// Per-module status.
    pub status: PackageModuleVerificationStatus,
    /// Evidence source for this module result.
    pub evidence: PackageModuleVerificationEvidence,
    /// Expected export hash from the package lock entry.
    pub export_hash: PackageHash,
    /// Expected axiom report hash from the package lock entry.
    pub axiom_report_hash: PackageHash,
    /// Expected certificate hash from the package lock entry.
    pub certificate_hash: PackageHash,
    /// Exact certificate format decoded from the checked module header.
    pub certificate_format: Option<String>,
    /// Exact core specification decoded from the checked module header.
    pub core_spec: Option<String>,
    /// Deterministic failure details for failed or skipped modules.
    pub error: Option<PackageVerificationError>,
}

/// Verified module payload accepted by the fast source-free package verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedModuleRecord {
    /// Module name from the package lock entry.
    pub module: Name,
    /// Whether this module is local to the package or an external hash-pinned import.
    pub origin: PackageLockEntryOrigin,
    /// Package-relative certificate path.
    pub certificate: PackagePath,
    /// Exact SHA-256 hash of the certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Verified module export hash.
    pub export_hash: PackageHash,
    /// Verified module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Verified module certificate hash.
    pub certificate_hash: PackageHash,
    /// Kernel-verified module data used by later certificate-derived projections.
    pub verified_module: VerifiedModule,
}

/// Fast source-free package verification report with collected verified modules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageFastSourceFreeVerification {
    /// Fast verifier summary.
    pub report: PackageVerificationReport,
    /// Verified modules in package-lock topological order.
    pub verified_modules: Vec<PackageVerifiedModuleRecord>,
}

#[derive(Clone, Debug)]
enum PackageVerificationMemoEntry {
    FastPassed {
        result: PackageModuleVerificationResult,
        record: Box<PackageVerifiedModuleRecord>,
    },
    ReferencePassed {
        result: PackageModuleVerificationResult,
        checked: Box<ReferenceCheckedModule>,
    },
    Failed {
        result: PackageModuleVerificationResult,
    },
}

#[derive(Clone, Debug)]
struct BoundedMemoEntry {
    value: Arc<PackageVerificationMemoEntry>,
    weighted_certificate_bytes: u64,
    last_used: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoundedMemoInsertOutcome {
    Inserted { evicted: usize },
    RejectedOversize,
}

#[derive(Debug, Default)]
struct BoundedPackageVerificationProcessMemo {
    entries: BTreeMap<String, BoundedMemoEntry>,
    recency: BTreeSet<(u64, String)>,
    retained_weighted_certificate_bytes: u64,
    recency_sequence: u64,
    cumulative_hits: u64,
    cumulative_misses: u64,
    cumulative_inserted: u64,
    cumulative_evicted: u64,
    cumulative_rejected_oversize: u64,
}

impl BoundedPackageVerificationProcessMemo {
    fn stats(&self) -> PackageVerificationProcessMemoStats {
        PackageVerificationProcessMemoStats {
            retained_entries: self.entries.len(),
            retained_weighted_certificate_bytes: self.retained_weighted_certificate_bytes,
            cumulative_hits: self.cumulative_hits,
            cumulative_misses: self.cumulative_misses,
            cumulative_inserted: self.cumulative_inserted,
            cumulative_evicted: self.cumulative_evicted,
            cumulative_rejected_oversize: self.cumulative_rejected_oversize,
        }
    }

    fn clear(&mut self) {
        *self = Self::default();
    }

    fn next_recency(&mut self) -> u64 {
        if self.recency_sequence == u64::MAX {
            let ordered_keys = self
                .recency
                .iter()
                .map(|(_, key)| key.clone())
                .collect::<Vec<_>>();
            self.recency.clear();
            for (index, key) in ordered_keys.into_iter().enumerate() {
                let timestamp = u64::try_from(index).unwrap_or(u64::MAX - 1);
                let entry = self
                    .entries
                    .get_mut(&key)
                    .expect("recency key must have a matching memo entry");
                entry.last_used = timestamp;
                self.recency.insert((timestamp, key));
            }
            self.recency_sequence = u64::try_from(self.entries.len()).unwrap_or(u64::MAX - 1);
        }
        let timestamp = self.recency_sequence;
        self.recency_sequence = self.recency_sequence.saturating_add(1);
        timestamp
    }

    fn lookup(&mut self, key: &str) -> Option<Arc<PackageVerificationMemoEntry>> {
        let Some((last_used, value)) = self
            .entries
            .get(key)
            .map(|entry| (entry.last_used, Arc::clone(&entry.value)))
        else {
            self.cumulative_misses = self.cumulative_misses.saturating_add(1);
            return None;
        };
        self.recency.remove(&(last_used, key.to_owned()));
        let refreshed = self.next_recency();
        self.entries
            .get_mut(key)
            .expect("looked-up memo entry remains resident")
            .last_used = refreshed;
        self.recency.insert((refreshed, key.to_owned()));
        self.cumulative_hits = self.cumulative_hits.saturating_add(1);
        Some(value)
    }

    fn insert(
        &mut self,
        limits: PackageVerificationProcessMemoLimits,
        key: String,
        value: Arc<PackageVerificationMemoEntry>,
        weighted_certificate_bytes: u64,
    ) -> BoundedMemoInsertOutcome {
        if weighted_certificate_bytes > limits.max_weighted_certificate_bytes.get() {
            self.cumulative_rejected_oversize = self.cumulative_rejected_oversize.saturating_add(1);
            return BoundedMemoInsertOutcome::RejectedOversize;
        }

        if let Some(replaced) = self.entries.remove(&key) {
            self.recency.remove(&(replaced.last_used, key.clone()));
            self.retained_weighted_certificate_bytes = self
                .retained_weighted_certificate_bytes
                .saturating_sub(replaced.weighted_certificate_bytes);
        }

        let mut evicted = 0usize;
        while self.entries.len() >= limits.max_entries.get()
            || self
                .retained_weighted_certificate_bytes
                .saturating_add(weighted_certificate_bytes)
                > limits.max_weighted_certificate_bytes.get()
        {
            let Some((last_used, evicted_key)) = self.recency.iter().next().cloned() else {
                break;
            };
            self.recency.remove(&(last_used, evicted_key.clone()));
            let removed = self
                .entries
                .remove(&evicted_key)
                .expect("recency key must have a matching memo entry");
            self.retained_weighted_certificate_bytes = self
                .retained_weighted_certificate_bytes
                .saturating_sub(removed.weighted_certificate_bytes);
            evicted = evicted.saturating_add(1);
        }

        let last_used = self.next_recency();
        self.retained_weighted_certificate_bytes = self
            .retained_weighted_certificate_bytes
            .saturating_add(weighted_certificate_bytes);
        self.entries.insert(
            key.clone(),
            BoundedMemoEntry {
                value,
                weighted_certificate_bytes,
                last_used,
            },
        );
        self.recency.insert((last_used, key));
        self.cumulative_inserted = self.cumulative_inserted.saturating_add(1);
        self.cumulative_evicted = self
            .cumulative_evicted
            .saturating_add(u64::try_from(evicted).unwrap_or(u64::MAX));
        BoundedMemoInsertOutcome::Inserted { evicted }
    }
}

/// Caller-owned, capacity-bounded exact package-verification memo.
#[derive(Clone)]
pub struct PackageVerificationProcessMemoHandle {
    limits: PackageVerificationProcessMemoLimits,
    inner: Arc<Mutex<BoundedPackageVerificationProcessMemo>>,
}

impl PackageVerificationProcessMemoHandle {
    /// Construct one fresh independent store with explicit nonzero limits.
    pub fn new(limits: PackageVerificationProcessMemoLimits) -> Self {
        Self {
            limits,
            inner: Arc::new(Mutex::new(BoundedPackageVerificationProcessMemo::default())),
        }
    }

    /// Return the immutable limits without acquiring the store lock.
    pub const fn limits(&self) -> PackageVerificationProcessMemoLimits {
        self.limits
    }

    /// Return one coherent store snapshot.
    pub fn stats(
        &self,
    ) -> Result<PackageVerificationProcessMemoStats, PackageVerificationProcessMemoAccessError>
    {
        self.inner
            .lock()
            .map(|store| store.stats())
            .map_err(|_| PackageVerificationProcessMemoAccessError::Poisoned)
    }

    /// Clear retained entries, recency state, and cumulative counters.
    pub fn clear(&self) -> Result<(), PackageVerificationProcessMemoAccessError> {
        self.inner
            .lock()
            .map(|mut store| store.clear())
            .map_err(|_| PackageVerificationProcessMemoAccessError::Poisoned)
    }

    fn lookup(
        &self,
        key: &str,
    ) -> Result<Option<Arc<PackageVerificationMemoEntry>>, PackageVerificationProcessMemoAccessError>
    {
        self.lookup_then(key, std::convert::identity)
    }

    fn lookup_then<R>(
        &self,
        key: &str,
        after_unlock: impl FnOnce(
            Result<
                Option<Arc<PackageVerificationMemoEntry>>,
                PackageVerificationProcessMemoAccessError,
            >,
        ) -> R,
    ) -> R {
        let retained_value = self
            .inner
            .lock()
            .map(|mut store| store.lookup(key))
            .map_err(|_| PackageVerificationProcessMemoAccessError::Poisoned);
        after_unlock(retained_value)
    }

    fn insert(
        &self,
        key: String,
        value: Arc<PackageVerificationMemoEntry>,
        weighted_certificate_bytes: u64,
    ) -> Result<BoundedMemoInsertOutcome, PackageVerificationProcessMemoAccessError> {
        self.inner
            .lock()
            .map(|mut store| store.insert(self.limits, key, value, weighted_certificate_bytes))
            .map_err(|_| PackageVerificationProcessMemoAccessError::Poisoned)
    }
}

impl fmt::Debug for PackageVerificationProcessMemoHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PackageVerificationProcessMemoHandle")
            .field("limits", &self.limits)
            .finish_non_exhaustive()
    }
}

impl PartialEq for PackageVerificationProcessMemoHandle {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for PackageVerificationProcessMemoHandle {}

#[derive(Debug)]
struct RetainedReferenceImportContext {
    value: Arc<ReferenceImportStore>,
    value_charge: u64,
}

impl RetainedReferenceImportContext {
    fn precharged(
        value: Arc<ReferenceImportStore>,
        charge: impl FnOnce(&ReferenceImportStore) -> u64,
    ) -> Self {
        let value_charge =
            npa_cert::PACKAGE_SHARED_ARC_METADATA_BYTES_V1.saturating_add(charge(value.as_ref()));
        Self {
            value,
            value_charge,
        }
    }

    #[cfg(test)]
    fn new(value: Arc<ReferenceImportStore>) -> Self {
        Self::precharged(value, ReferenceImportStore::logical_retained_bytes_v1)
    }
}

#[derive(Debug, Default)]
struct PackageVerificationDecodeCache {
    fast_certificates: BTreeMap<String, ModuleCert>,
    reference_import_contexts: BTreeMap<String, RetainedReferenceImportContext>,
    retained_entries: usize,
    retained_bytes: u64,
}

impl PackageVerificationDecodeCache {
    fn fast_charge(key_capacity: usize, value: &ModuleCert) -> u64 {
        npa_cert::PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1
            .saturating_add(u64::try_from(key_capacity).unwrap_or(u64::MAX))
            .saturating_add(value.logical_retained_bytes_v1())
    }

    fn reference_charge(key_capacity: usize, value_charge: u64) -> u64 {
        npa_cert::PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1
            .saturating_add(u64::try_from(key_capacity).unwrap_or(u64::MAX))
            .saturating_add(value_charge)
    }

    fn replacement_fits(&self, old_charge: u64, new_charge: u64, adds_entry: bool) -> bool {
        if new_charge == u64::MAX {
            return false;
        }
        let next_entries = self
            .retained_entries
            .saturating_add(usize::from(adds_entry));
        if next_entries > npa_cert::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1 {
            return false;
        }
        self.retained_bytes
            .saturating_sub(old_charge)
            .checked_add(new_charge)
            .is_some_and(|bytes| bytes <= npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1)
    }

    fn insert_fast(&mut self, key: String, value: ModuleCert) -> bool {
        let existing = self.fast_certificates.get_key_value(&key);
        let adds_entry = existing.is_none();
        let retained_key_capacity = existing
            .map(|(stored_key, _)| stored_key.capacity())
            .unwrap_or_else(|| key.capacity());
        let old_charge =
            existing.map_or(0, |(_, old)| Self::fast_charge(retained_key_capacity, old));
        let new_charge = Self::fast_charge(retained_key_capacity, &value);
        if !self.replacement_fits(old_charge, new_charge, adds_entry) {
            return false;
        }
        self.fast_certificates.insert(key, value);
        self.retained_entries = self
            .retained_entries
            .saturating_add(usize::from(adds_entry));
        self.retained_bytes = self
            .retained_bytes
            .saturating_sub(old_charge)
            .saturating_add(new_charge);
        true
    }

    fn insert_reference(&mut self, key: String, value: RetainedReferenceImportContext) -> bool {
        let existing = self.reference_import_contexts.get_key_value(&key);
        let adds_entry = existing.is_none();
        let retained_key_capacity = existing
            .map(|(stored_key, _)| stored_key.capacity())
            .unwrap_or_else(|| key.capacity());
        let old_charge = existing.map_or(0, |(_, old)| {
            Self::reference_charge(retained_key_capacity, old.value_charge)
        });
        let new_charge = Self::reference_charge(retained_key_capacity, value.value_charge);
        if !self.replacement_fits(old_charge, new_charge, adds_entry) {
            return false;
        }
        self.reference_import_contexts.insert(key, value);
        self.retained_entries = self
            .retained_entries
            .saturating_add(usize::from(adds_entry));
        self.retained_bytes = self
            .retained_bytes
            .saturating_sub(old_charge)
            .saturating_add(new_charge);
        true
    }
}

static PACKAGE_VERIFICATION_DECODE_CACHE: OnceLock<Mutex<PackageVerificationDecodeCache>> =
    OnceLock::new();

fn lock_package_verification_decode_cache(
    cache: &Mutex<PackageVerificationDecodeCache>,
) -> std::sync::MutexGuard<'_, PackageVerificationDecodeCache> {
    cache
        .lock()
        .expect("package verification decode cache mutex should not be poisoned")
}

fn package_fast_decode_cache_lookup(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: &str,
) -> Option<ModuleCert> {
    package_fast_decode_cache_lookup_then(cache, key, std::convert::identity)
}

fn package_fast_decode_cache_lookup_then<R>(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: &str,
    after_unlock: impl FnOnce(Option<ModuleCert>) -> R,
) -> R {
    let retained_certificate = {
        lock_package_verification_decode_cache(cache)
            .fast_certificates
            .get(key)
            .cloned()
    };
    after_unlock(retained_certificate)
}

fn package_reference_cache_lookup(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: &str,
) -> Option<Arc<ReferenceImportStore>> {
    package_reference_cache_lookup_then(cache, key, std::convert::identity)
}

fn package_reference_cache_lookup_then<R>(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: &str,
    after_unlock: impl FnOnce(Option<Arc<ReferenceImportStore>>) -> R,
) -> R {
    let retained_imports = {
        lock_package_verification_decode_cache(cache)
            .reference_import_contexts
            .get(key)
            .map(|retained| Arc::clone(&retained.value))
    };
    after_unlock(retained_imports)
}

fn package_reference_cache_insert(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: String,
    value: Arc<ReferenceImportStore>,
) -> bool {
    package_reference_cache_insert_with_charge(
        cache,
        key,
        value,
        ReferenceImportStore::logical_retained_bytes_v1,
    )
}

fn package_reference_cache_insert_with_charge(
    cache: &Mutex<PackageVerificationDecodeCache>,
    key: String,
    value: Arc<ReferenceImportStore>,
    charge: impl FnOnce(&ReferenceImportStore) -> u64,
) -> bool {
    let retained = RetainedReferenceImportContext::precharged(value, charge);
    lock_package_verification_decode_cache(cache).insert_reference(key, retained)
}

/// Clear the process-local package verification decode/import cache.
///
/// This cache stores decoded certificate structures and materialized import
/// contexts only. It does not store checker acceptance verdicts and does not
/// touch disk-backed audit cache or verifier memo entries.
pub fn clear_package_verification_decode_cache() {
    *lock_package_verification_decode_cache(package_verification_decode_cache()) =
        PackageVerificationDecodeCache::default();
}

/// Request clearing the disk-backed import-context export-data cache rooted at
/// the current working directory.
///
/// This cache stores local acceleration metadata only. Online deletion is
/// intentionally disabled on platforms without an identity-conditional
/// unlink primitive, so this request safely preserves the untrusted residue.
/// Preserving it cannot change verifier acceptance because every hit is
/// revalidated against the complete expected entry.
pub fn clear_package_import_context_export_disk_cache() {
    let Ok(cwd) = std::env::current_dir() else {
        return;
    };
    let _ = remove_import_context_export_cache_at(&cwd);
}

/// Return the current disk-backed import-context export-data cache file count.
pub fn package_import_context_export_disk_cache_entry_count() -> usize {
    std::env::current_dir()
        .ok()
        .and_then(|cwd| open_import_context_export_cache_at(&cwd, false).ok())
        .and_then(|cache| cache.regular_file_names().ok())
        .map(|names| {
            names
                .iter()
                .filter(|name| Path::new(name).extension() == Some(OsStr::new("json")))
                .count()
        })
        .unwrap_or(0)
}

/// Return the current process-local package verification decode/import cache size.
pub fn package_verification_decode_cache_entry_count() -> usize {
    let cache = lock_package_verification_decode_cache(package_verification_decode_cache());
    debug_assert_eq!(
        cache.retained_entries,
        cache.fast_certificates.len() + cache.reference_import_contexts.len()
    );
    cache.retained_entries
}

/// Return the mandatory logical retained-byte total of the combined decode cache.
pub fn package_verification_decode_cache_retained_bytes() -> u64 {
    lock_package_verification_decode_cache(package_verification_decode_cache()).retained_bytes
}

/// Operation-local ownership observations for package verification payloads.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackagePayloadOwnershipObservation {
    /// Explicit hot-path decoded/verified payload handle clones.
    pub module_payload_handle_clones: u64,
    /// Logical bytes that would have been copied by those handle clones.
    pub avoided_module_payload_clone_bytes: u64,
    /// Combined decode-cache logical bytes sampled after the operation.
    pub decode_cache_retained_bytes: u64,
    /// Maximum combined decode-cache logical bytes sampled during the operation.
    pub decode_cache_peak_retained_bytes: u64,
    /// Decode/import cache admissions rejected by the hard bounds.
    pub decode_cache_capacity_stops: u64,
    /// Immutable process-memo value handle clones.
    pub process_memo_payload_handle_clones: u64,
    /// Whether arithmetic saturated while accumulating this observation.
    pub overflowed: bool,
}

impl PackagePayloadOwnershipObservation {
    fn add(field: &mut u64, value: u64, overflowed: &mut bool) {
        let (sum, overflow) = field.overflowing_add(value);
        *field = if overflow { u64::MAX } else { sum };
        *overflowed |= overflow;
    }

    /// Seed cache current and peak from the mandatory bounded-cache state.
    pub fn seed_decode_cache(&mut self) {
        let current = package_verification_decode_cache_retained_bytes();
        self.decode_cache_retained_bytes = current;
        self.decode_cache_peak_retained_bytes = current;
    }

    /// Sample the current mandatory cache state after an access or mutation.
    pub fn sample_decode_cache(&mut self) {
        let current = package_verification_decode_cache_retained_bytes();
        self.decode_cache_retained_bytes = current;
        self.decode_cache_peak_retained_bytes = self.decode_cache_peak_retained_bytes.max(current);
    }

    fn observe_module_handle_clone(&mut self, logical_bytes: u64) {
        Self::add(
            &mut self.module_payload_handle_clones,
            1,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.avoided_module_payload_clone_bytes,
            logical_bytes,
            &mut self.overflowed,
        );
    }

    fn observe_decode_cache_capacity_stop(&mut self) {
        Self::add(
            &mut self.decode_cache_capacity_stops,
            1,
            &mut self.overflowed,
        );
    }

    fn observe_process_memo_handle_clone(&mut self) {
        Self::add(
            &mut self.process_memo_payload_handle_clones,
            1,
            &mut self.overflowed,
        );
    }

    /// Merge one worker-local observation in a completion-order-independent way.
    pub fn merge_worker(&mut self, worker: Self) {
        Self::add(
            &mut self.module_payload_handle_clones,
            worker.module_payload_handle_clones,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.avoided_module_payload_clone_bytes,
            worker.avoided_module_payload_clone_bytes,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.decode_cache_capacity_stops,
            worker.decode_cache_capacity_stops,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.process_memo_payload_handle_clones,
            worker.process_memo_payload_handle_clones,
            &mut self.overflowed,
        );
        self.decode_cache_peak_retained_bytes = self
            .decode_cache_peak_retained_bytes
            .max(worker.decode_cache_peak_retained_bytes);
        self.overflowed |= worker.overflowed;
    }
}

/// Per-module Phase 8 import lock derived from a package lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePhase8ImportLockMaterialization {
    /// Module this import lock verifies.
    pub module: Name,
    /// Deterministic package-relative path for the generated import lock JSON.
    pub path: String,
    /// Phase 8 import lock manifest containing only direct imports.
    pub manifest: IndependentCheckerImportLockManifest,
    /// Exact file hash of [`Self::manifest`] canonical JSON.
    pub manifest_hash: npa_cert::Hash,
}

/// Per-module Phase 8 machine-check request derived from a package lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePhase8RequestMaterialization {
    /// Module this request verifies.
    pub module: Name,
    /// Phase 8 checker profile used for this request.
    pub checker_profile: String,
    /// Deterministic package-relative path for the generated import lock JSON.
    pub import_lock_path: String,
    /// Phase 8 import lock manifest containing only direct imports.
    pub import_lock_manifest: IndependentCheckerImportLockManifest,
    /// Exact file hash of [`Self::import_lock_manifest`] canonical JSON.
    pub import_lock_manifest_hash: npa_cert::Hash,
    /// Deterministic package-relative path for the generated request JSON.
    pub request_path: String,
    /// Materialized Phase 8 machine-check request.
    pub request: IndependentCheckerMachineCheckRequest,
    /// Exact file hash of [`Self::request`] canonical JSON.
    pub request_file_hash: npa_cert::Hash,
}

/// Package-level Phase 8 machine-check request materialization result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePhase8RequestMaterializationReport {
    /// Per-module requests in package-lock topological order.
    pub modules: Vec<PackagePhase8RequestMaterialization>,
    /// Final request-store manifest after adding every generated request.
    pub request_store: IndependentCheckerRequestStoreManifest,
    /// Exact file hash of [`Self::request_store`] canonical JSON.
    pub request_store_file_hash: npa_cert::Hash,
    /// Whether the request store needs to be written or replaced.
    pub request_store_rewrite_required: bool,
}

/// Structured source-free package verification error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerificationError {
    /// Stable error category.
    pub kind: PackageVerificationErrorKind,
    /// Stable artifact-local path, for example `entries[0].certificate`.
    pub path: String,
    /// Module context for entry-local package verification errors.
    pub module: Option<Box<String>>,
    /// Field name when the error is attached to one object field.
    pub field: Option<Box<String>>,
    /// Stable machine-readable reason code.
    pub reason_code: PackageVerificationErrorReason,
    /// Expected value or type when useful.
    pub expected_value: Option<String>,
    /// Actual value or type when useful.
    pub actual_value: Option<String>,
    /// Checker-local structured rejection details, when the error came from a checker.
    pub checker_error: Option<Box<PackageVerificationCheckerError>>,
}

/// Structured checker-local package verification error details.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerificationCheckerError {
    /// Checker implementation that produced the error.
    pub checker: String,
    /// Checker-local stable error kind.
    pub kind: String,
    /// Checker-local certificate section.
    pub section: Option<String>,
    /// Checker-local byte offset, when applicable.
    pub offset: Option<usize>,
    /// Checker-local stable reason code.
    pub reason_code: Option<String>,
}

impl PackageVerificationError {
    pub(crate) fn package_lock_stale(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            path,
            Some("package_lock".to_owned()),
            PackageVerificationErrorReason::PackageLockStale,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    fn package_identity_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            path,
            Some(field.into()),
            PackageVerificationErrorReason::PackageIdentityMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    fn lock_graph_invalid(actual: impl Into<String>) -> Self {
        Self::new(
            PackageVerificationErrorKind::LockGraph,
            "lock",
            None,
            PackageVerificationErrorReason::LockGraphInvalid,
            Some("valid package lock graph matching manifest imports".to_owned()),
            Some(actual.into()),
        )
    }

    fn invalid_job_count(actual: usize) -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            "execution.jobs",
            Some("jobs".to_owned()),
            PackageVerificationErrorReason::InvalidJobCount,
            Some("integer greater than or equal to 1".to_owned()),
            Some(actual.to_string()),
        )
    }

    fn unsupported_parallel_checker(mode: PackageVerificationMode, jobs: usize) -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            "execution.jobs",
            Some("jobs".to_owned()),
            PackageVerificationErrorReason::UnsupportedParallelChecker,
            Some("jobs=1 for this checker mode".to_owned()),
            Some(format!("mode={};jobs={jobs}", mode.as_str())),
        )
    }

    fn unsupported_lazy_memoization() -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            "execution.memoization",
            Some("memoization".to_owned()),
            PackageVerificationErrorReason::UnsupportedLazyMemoization,
            Some("disabled memoization for path-backed lazy artifact verification".to_owned()),
            Some("process-local memoization requested".to_owned()),
        )
    }

    fn fast_worker_infrastructure_failed(
        layer_index: usize,
        shard_index: usize,
        first_module: &Name,
        reason_code: PackageVerificationErrorReason,
    ) -> Self {
        let failure_kind = match reason_code {
            PackageVerificationErrorReason::FastWorkerSpawnFailed => "spawn",
            PackageVerificationErrorReason::FastWorkerJoinFailed => "join",
            _ => unreachable!("worker infrastructure constructor requires a worker reason"),
        };
        Self::new(
            PackageVerificationErrorKind::Kernel,
            format!("execution.layers[{layer_index}].shards[{shard_index}]"),
            Some("worker".to_owned()),
            reason_code,
            Some("worker thread spawned and joined successfully".to_owned()),
            Some(format!(
                "{failure_kind}_failed;first_module={}",
                first_module.as_dotted()
            )),
        )
        .with_module(first_module.as_dotted())
    }

    fn selected_module_missing(module: &Name) -> Self {
        Self::new(
            PackageVerificationErrorKind::Input,
            "execution.selected_modules",
            Some("selected_modules".to_owned()),
            PackageVerificationErrorReason::SelectedModuleMissing,
            Some("package lock module".to_owned()),
            Some(module.as_dotted()),
        )
    }

    fn duplicate_certificate_artifact(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageVerificationErrorKind::Artifact,
            path,
            Some("certificate".to_owned()),
            PackageVerificationErrorReason::DuplicateCertificateArtifact,
            Some("unique certificate artifact path".to_owned()),
            Some(actual.into()),
        )
    }

    pub(crate) fn certificate_artifact_missing(
        path: impl Into<String>,
        expected: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageVerificationErrorKind::Artifact,
            path,
            Some("certificate".to_owned()),
            PackageVerificationErrorReason::CertificateArtifactMissing,
            Some(expected.into()),
            None,
        )
    }

    fn certificate_file_hash_mismatch(
        path: impl Into<String>,
        expected: PackageHash,
        actual: PackageHash,
    ) -> Self {
        Self::hash_mismatch(
            PackageVerificationErrorKind::CertificateIdentity,
            path,
            "certificate_file_hash",
            PackageVerificationErrorReason::CertificateFileHashMismatch,
            expected,
            actual,
        )
    }

    fn certificate_decode_failed(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageVerificationErrorKind::CertificateDecode,
            path,
            Some("certificate".to_owned()),
            PackageVerificationErrorReason::CertificateDecodeFailed,
            Some("decodable npa module certificate".to_owned()),
            Some(actual.into()),
        )
    }

    fn certificate_module_mismatch(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageVerificationErrorKind::CertificateIdentity,
            path,
            Some("module".to_owned()),
            PackageVerificationErrorReason::CertificateModuleMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    fn export_hash_mismatch(
        path: impl Into<String>,
        expected: PackageHash,
        actual: PackageHash,
    ) -> Self {
        Self::hash_mismatch(
            PackageVerificationErrorKind::CertificateIdentity,
            path,
            "export_hash",
            PackageVerificationErrorReason::ExportHashMismatch,
            expected,
            actual,
        )
    }

    fn axiom_report_hash_mismatch(
        path: impl Into<String>,
        expected: PackageHash,
        actual: PackageHash,
    ) -> Self {
        Self::hash_mismatch(
            PackageVerificationErrorKind::CertificateIdentity,
            path,
            "axiom_report_hash",
            PackageVerificationErrorReason::AxiomReportHashMismatch,
            expected,
            actual,
        )
    }

    fn certificate_hash_mismatch(
        path: impl Into<String>,
        expected: PackageHash,
        actual: PackageHash,
    ) -> Self {
        Self::hash_mismatch(
            PackageVerificationErrorKind::CertificateIdentity,
            path,
            "certificate_hash",
            PackageVerificationErrorReason::CertificateHashMismatch,
            expected,
            actual,
        )
    }

    fn verify_failed(path: impl Into<String>, source: CertError) -> Self {
        let reason_code = match source {
            CertError::ForbiddenAxiom { .. } | CertError::SorryDenied { .. } => {
                PackageVerificationErrorReason::AxiomPolicyRejected
            }
            CertError::UnsupportedCoreFeature { .. } => {
                PackageVerificationErrorReason::UnsupportedCoreFeature
            }
            _ => PackageVerificationErrorReason::KernelVerificationFailed,
        };
        Self::new_with_checker_error(
            PackageVerificationErrorKind::Kernel,
            path,
            Some("certificate".to_owned()),
            reason_code,
            Some("kernel-verifiable module certificate".to_owned()),
            Some(format!("{source:?}")),
            Some(PackageVerificationCheckerError {
                checker: "npa-cert".to_owned(),
                kind: "certificate_verifier".to_owned(),
                section: None,
                offset: None,
                reason_code: Some(reason_code.as_str().to_owned()),
            }),
        )
    }

    fn reference_checker_rejected(path: impl Into<String>, source: ReferenceCheckError) -> Self {
        let reason_code = package_reference_checker_reason(&source);
        Self::new_with_checker_error(
            PackageVerificationErrorKind::ReferenceChecker,
            path,
            Some("certificate".to_owned()),
            reason_code,
            Some("reference-checker-verifiable module certificate".to_owned()),
            Some(format!("{source:?}")),
            Some(reference_checker_error_details(&source)),
        )
    }

    fn phase8_import_lock_invalid(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageVerificationErrorKind::Phase8Adapter,
            path,
            Some("imports.manifest".to_owned()),
            PackageVerificationErrorReason::Phase8ImportLockMaterializationFailed,
            Some("valid independent checker import lock manifest".to_owned()),
            Some(actual.into()),
        )
    }

    fn phase8_request_materialization_failed(
        path: impl Into<String>,
        source: IndependentCheckerCommandError,
    ) -> Self {
        let expected_value = source
            .expected_value
            .map(|value| value.to_string())
            .or_else(|| {
                source
                    .expected_hash
                    .as_deref()
                    .map(|hash| format_package_hash(&PackageHash::from(*hash)))
            });
        let actual_value = source
            .actual_value
            .map(|value| value.to_string())
            .or_else(|| {
                source
                    .actual_hash
                    .as_deref()
                    .map(|hash| format_package_hash(&PackageHash::from(*hash)))
            });
        Self::new(
            PackageVerificationErrorKind::Phase8Adapter,
            path,
            source.field.as_deref().map(str::to_owned),
            PackageVerificationErrorReason::Phase8RequestMaterializationFailed,
            expected_value,
            actual_value,
        )
    }

    fn earlier_module_failed(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageVerificationErrorKind::Dependency,
            path,
            Some("module".to_owned()),
            PackageVerificationErrorReason::EarlierModuleFailed,
            Some("all prior package lock entries passed".to_owned()),
            Some(actual.into()),
        )
    }

    fn hash_mismatch(
        kind: PackageVerificationErrorKind,
        path: impl Into<String>,
        field: impl Into<String>,
        reason_code: PackageVerificationErrorReason,
        expected: PackageHash,
        actual: PackageHash,
    ) -> Self {
        Self::new(
            kind,
            path,
            Some(field.into()),
            reason_code,
            Some(format_package_hash(&expected)),
            Some(format_package_hash(&actual)),
        )
    }

    fn new(
        kind: PackageVerificationErrorKind,
        path: impl Into<String>,
        field: Option<String>,
        reason_code: PackageVerificationErrorReason,
        expected_value: Option<String>,
        actual_value: Option<String>,
    ) -> Self {
        Self::new_with_checker_error(
            kind,
            path,
            field,
            reason_code,
            expected_value,
            actual_value,
            None,
        )
    }

    fn new_with_checker_error(
        kind: PackageVerificationErrorKind,
        path: impl Into<String>,
        field: Option<String>,
        reason_code: PackageVerificationErrorReason,
        expected_value: Option<String>,
        actual_value: Option<String>,
        checker_error: Option<PackageVerificationCheckerError>,
    ) -> Self {
        Self {
            kind,
            path: path.into(),
            module: None,
            field: field.map(Box::new),
            reason_code,
            expected_value,
            actual_value,
            checker_error: checker_error.map(Box::new),
        }
    }

    pub fn with_module(mut self, module: impl Into<String>) -> Self {
        self.module = Some(Box::new(module.into()));
        self
    }
}

/// Stable package verification error category.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationErrorKind {
    /// Caller supplied inconsistent manifest or lock identity.
    Input,
    /// Package lock graph validation failed before certificate verification.
    LockGraph,
    /// Required certificate artifact bytes are absent or duplicated.
    Artifact,
    /// Certificate bytes could not be decoded syntactically.
    CertificateDecode,
    /// Certificate identity does not match the package lock entry.
    CertificateIdentity,
    /// Kernel certificate verification failed.
    Kernel,
    /// Independent reference checker verification failed.
    ReferenceChecker,
    /// Phase 8 import-lock or request adapter materialization failed.
    Phase8Adapter,
    /// Verification was skipped because an earlier lock entry failed.
    Dependency,
}

/// Stable package verification error reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationErrorReason {
    /// Manifest and lock package identity differ.
    PackageIdentityMismatch,
    /// Checked package lock no longer matches manifest and certificate artifacts.
    PackageLockStale,
    /// Lock graph or manifest import accountability validation failed.
    LockGraphInvalid,
    /// Execution options specified an invalid job count.
    InvalidJobCount,
    /// Parallel execution is not supported for the selected checker.
    UnsupportedParallelChecker,
    /// Process-local verifier memoization is not supported by lazy artifact verification.
    UnsupportedLazyMemoization,
    /// A fast verifier shard worker could not be spawned.
    FastWorkerSpawnFailed,
    /// A fast verifier shard worker unwound before returning its result.
    FastWorkerJoinFailed,
    /// A selected module is not present in the package lock.
    SelectedModuleMissing,
    /// Caller supplied duplicate artifact bytes for one certificate path.
    DuplicateCertificateArtifact,
    /// Certificate artifact bytes are missing.
    CertificateArtifactMissing,
    /// Certificate file hash differs from the lock entry.
    CertificateFileHashMismatch,
    /// Certificate bytes do not decode as an NPA module certificate.
    CertificateDecodeFailed,
    /// Certificate module name differs from the lock entry.
    CertificateModuleMismatch,
    /// Certificate export hash differs from the lock entry.
    ExportHashMismatch,
    /// Certificate axiom report hash differs from the lock entry.
    AxiomReportHashMismatch,
    /// Certificate canonical hash differs from the lock entry.
    CertificateHashMismatch,
    /// Certificate was rejected by package-derived axiom policy.
    AxiomPolicyRejected,
    /// Certificate requires a core feature unsupported by the selected checker profile.
    UnsupportedCoreFeature,
    /// Certificate was rejected by the fast kernel verifier.
    KernelVerificationFailed,
    /// Certificate was rejected by the independent reference checker.
    ReferenceCheckerRejected,
    /// Phase 8 import lock could not be materialized from package data.
    Phase8ImportLockMaterializationFailed,
    /// Phase 8 machine-check request could not be materialized from package data.
    Phase8RequestMaterializationFailed,
    /// Module was skipped because an earlier topological dependency failed.
    EarlierModuleFailed,
}

impl PackageVerificationErrorReason {
    /// Return the stable wire reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PackageIdentityMismatch => "package_identity_mismatch",
            Self::PackageLockStale => "package_lock_stale",
            Self::LockGraphInvalid => "lock_graph_invalid",
            Self::InvalidJobCount => "invalid_job_count",
            Self::UnsupportedParallelChecker => "unsupported_parallel_checker",
            Self::UnsupportedLazyMemoization => "unsupported_lazy_memoization",
            Self::FastWorkerSpawnFailed => "fast_worker_spawn_failed",
            Self::FastWorkerJoinFailed => "fast_worker_join_failed",
            Self::SelectedModuleMissing => "selected_module_missing",
            Self::DuplicateCertificateArtifact => "duplicate_certificate_artifact",
            Self::CertificateArtifactMissing => "certificate_artifact_missing",
            Self::CertificateFileHashMismatch => "certificate_file_hash_mismatch",
            Self::CertificateDecodeFailed => "certificate_decode_failed",
            Self::CertificateModuleMismatch => "certificate_module_mismatch",
            Self::ExportHashMismatch => "export_hash_mismatch",
            Self::AxiomReportHashMismatch => "axiom_report_hash_mismatch",
            Self::CertificateHashMismatch => "certificate_hash_mismatch",
            Self::AxiomPolicyRejected => "axiom_policy_rejected",
            Self::UnsupportedCoreFeature => "unsupported_core_feature",
            Self::KernelVerificationFailed => "kernel_verification_failed",
            Self::ReferenceCheckerRejected => "reference_checker_rejected",
            Self::Phase8ImportLockMaterializationFailed => {
                "independent_checker_import_lock_materialization_failed"
            }
            Self::Phase8RequestMaterializationFailed => {
                "independent_checker_request_materialization_failed"
            }
            Self::EarlierModuleFailed => "earlier_module_failed",
        }
    }
}

/// Verify package certificates source-free with the fast kernel verifier.
///
/// The verifier consumes only a validated package manifest, a package lock, and
/// caller-provided certificate bytes. It never reads source, replay, metadata,
/// theorem-index, AI trace, or checker-result files.
pub fn verify_package_fast_source_free<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_options(
        validated,
        lock,
        artifacts,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Verify package certificates source-free with the fast kernel verifier,
/// reading certificate artifacts lazily from a package root.
///
/// This path avoids preloading all certificate bytes into memory. It reads only
/// the current module certificate needed by the verifier loop.
pub fn verify_package_fast_source_free_from_root(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: impl AsRef<Path>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_from_root_with_options(
        validated,
        lock,
        package_root,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Verify package certificates source-free with the fast kernel verifier and
/// explicit execution options, reading certificate artifacts lazily from a
/// package root.
///
/// Path-backed verification currently supports `jobs = 1` and disabled
/// process-local verifier memoization so that certificate bytes are not
/// preloaded to compute memo keys.
pub fn verify_package_fast_source_free_from_root_with_options(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: impl AsRef<Path>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::FastKernel,
            options.jobs,
        ));
    }
    if options.memoization.is_enabled() {
        return Err(PackageVerificationError::unsupported_lazy_memoization());
    }
    Ok(verify_package_fast_source_free_from_root_serial(
        validated,
        lock,
        package_root.as_ref(),
        options,
    )?
    .report)
}

/// Verify package certificates source-free with explicit execution options.
pub fn verify_package_fast_source_free_with_options<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if use_fast_serial_report_path(&options) {
        return verify_package_fast_source_free_report(validated, lock, artifacts);
    }
    Ok(verify_package_fast_source_free_execution(validated, lock, artifacts, options)?.report)
}

/// Verify fast certificates from owned artifacts whose file hashes were
/// already bound by canonical lock derivation.
///
/// The verifier still decodes and checks the authoritative certificate bytes.
/// Only the redundant checker-local file hash is reused. Parallel fast
/// execution is supported.
pub fn verify_package_fast_source_free_with_hashed_artifacts<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_hashed_artifacts_and_options(
        validated,
        lock,
        artifacts,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Hashed-artifact fast verification with explicit execution options.
pub fn verify_package_fast_source_free_with_hashed_artifacts_and_options<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_fast_source_free_with_hashed_artifacts_and_options_indexed(
        validated, &indexed, artifacts, options,
    )
}

/// Hashed-artifact fast verification over one validated graph index.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_hashed_artifacts_and_options_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let (artifact_bytes, artifact_file_hashes) = hashed_artifact_maps(artifacts)?;
    Ok(
        verify_package_fast_source_free_execution_indexed_with_artifact_maps(
            validated,
            indexed,
            artifact_bytes,
            Some(artifact_file_hashes),
            options,
            PackageFastParallelStrategy::ShardRunner,
        )?
        .report,
    )
}

/// Verify package certificates from one operation-owned artifact snapshot.
///
/// The owner binds authoritative bytes to the file hash produced by canonical
/// lock derivation. A retained decoded capability bypasses only the redundant
/// checker-local decode; every trusted certificate verification gate still
/// executes against the authoritative bytes. Remaining prepared values are
/// released before this function returns, including on an error.
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_options(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
        validated, lock, artifacts, options, None,
    )
}

/// Snapshot fast verification with optional cross-phase artifact work observation.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    options: PackageVerificationExecutionOptions,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    let result = (|| {
        validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
        if options.jobs != 1 {
            return Err(PackageVerificationError::unsupported_parallel_checker(
                PackageVerificationMode::FastKernel,
                options.jobs,
            ));
        }
        validate_manifest_lock_identity(validated, lock)?;
        let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
            .map_err(indexed_lock_graph_verification_error)?;
        verify_package_fast_source_free_with_artifact_snapshots_serial_indexed(
            validated,
            &indexed,
            artifacts,
            options,
            artifact_observation,
        )
    })();
    artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    result.map(|verification| verification.report)
}

/// Snapshot fast verification using one already validated operation index.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation_indexed(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &mut PreparedPackageArtifacts,
    options: PackageVerificationExecutionOptions,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    let result = verify_package_fast_source_free_with_artifact_snapshots_serial_indexed(
        validated,
        indexed,
        artifacts,
        options,
        artifact_observation,
    );
    artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    result.map(|verification| verification.report)
}

fn verify_package_fast_source_free_with_artifact_snapshots_serial_indexed(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &mut PreparedPackageArtifacts,
    options: PackageVerificationExecutionOptions,
    mut artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    if options.jobs != 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::FastKernel,
            options.jobs,
        ));
    }
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let lock = indexed.lock();
    let graph = indexed.graph();
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_indexed(indexed, &options)?;

    // Keep cheap shared handles alive for planning/report projection. This does
    // not copy certificate bytes and lets the mutable prepared owner release
    // decoded capabilities as soon as their live range ends.
    let artifact_handles = entries
        .iter()
        .filter_map(|(_, entry)| {
            artifacts
                .clone_hashed_raw(&entry.certificate)
                .map(|artifact| (entry.certificate.clone(), artifact))
        })
        .collect::<Vec<_>>();
    let artifact_bytes = artifact_handles
        .iter()
        .map(|(path, artifact)| (path.clone(), artifact.bytes()))
        .collect::<BTreeMap<_, _>>();

    for (_, entry) in &entries {
        if !execution_modules.contains(&entry.module) {
            release_prepared_artifact(artifacts, entry, PreparedArtifactReleaseReason::Unselected)?;
        }
    }
    if execution_modules.is_empty() {
        return Ok(PackageFastSourceFreeVerification {
            report: empty_package_verification_report(
                validated,
                lock,
                &entries,
                &options,
                PackageVerificationMode::FastKernel,
            ),
            verified_modules: Vec::new(),
        });
    }

    let execution_layers = execution_layers_for_indexed(indexed, &execution_modules);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let policy = package_fast_kernel_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::FastKernel,
    )
    .with_process_local_cache(options.decode_cache.process_local())
    .with_persistent_import_context_export_cache(options.decode_cache.persistent());
    let mut session = VerifierSession::new();
    let mut blocked_modules = BTreeSet::<Name>::new();
    let mut results_by_module = BTreeMap::<Name, PackageModuleVerificationResult>::new();
    let mut verified_modules_by_module = BTreeMap::<Name, PackageVerifiedModuleRecord>::new();
    let mut planning_state =
        PackageFastPlanningState::new(&entries, graph, &execution_modules, &artifact_bytes);
    planning_state.prepared_shared_bytes = artifacts.retained_decoded_bytes();
    let mut memo_run = PackageVerificationMemoRun::for_snapshot_run(
        &options,
        validated,
        indexed,
        &execution_modules,
        artifacts,
        PackageVerificationMode::FastKernel,
    )?;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);
    if let Some(measurements) = measurement_state.as_mut() {
        if let Some(observation) = package_fast_execution_cost_observation(
            &entries,
            graph,
            &execution_modules,
            &execution_layers,
            &planning_state,
        ) {
            measurements.configure_fast_sharding(options.jobs, observation);
        }
    }

    for (layer_index, layer) in execution_layers.into_iter().enumerate() {
        let mut runnable = Vec::<(usize, &PackageLockEntry)>::new();
        for module in &layer {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("layer modules are lock entries");
            if let Some(blocked_import) =
                blocked_direct_import(graph, *entry_index, &blocked_modules)
            {
                let input = prepared_artifact_input(artifacts, *entry_index, entry)?;
                results_by_module.insert(
                    entry.module.clone(),
                    module_result_for_input(
                        entry,
                        PackageModuleVerificationStatus::Skipped,
                        Some(PackageVerificationError::earlier_module_failed(
                            format!("entries[{entry_index}].module"),
                            blocked_import.as_dotted(),
                        )),
                        PackageVerificationMode::FastKernel,
                        input,
                    ),
                );
                blocked_modules.insert(entry.module.clone());
                release_prepared_artifact(
                    artifacts,
                    entry,
                    PreparedArtifactReleaseReason::BlockedOrSkippedResult,
                )?;
                continue;
            }
            let memo_lookup = memo_run.lookup(&entry.module);
            if memo_lookup.is_some() {
                if let Some(measurements) = measurement_state.as_mut() {
                    measurements
                        .package_payload
                        .observe_process_memo_handle_clone();
                }
            }
            match memo_lookup.as_deref() {
                Some(PackageVerificationMemoEntry::FastPassed { result, record }) => {
                    if let Some(measurements) = measurement_state.as_mut() {
                        let mut observation =
                            PackageEntryCheckObservation::new(options.measurement_mode);
                        observation.observe_certificate_bytes(
                            prepared_artifact_input(artifacts, *entry_index, entry)?.bytes(),
                        );
                        observation.observe_verified_module(&entry.module, &record.verified_module);
                        measurements.record_module(entry, &observation, 0, None, false);
                    }
                    session.register_verified_module_with_trust(
                        record.verified_module.clone(),
                        policy.mode,
                    );
                    if let Some(measurements) = measurement_state.as_mut() {
                        measurements.package_payload.observe_module_handle_clone(
                            record.verified_module.logical_retained_bytes_v1(),
                        );
                    }
                    results_by_module.insert(entry.module.clone(), result.clone());
                    verified_modules_by_module
                        .insert(entry.module.clone(), record.as_ref().clone());
                    planning_state.record_verified(*entry_index)?;
                    release_prepared_artifact(
                        artifacts,
                        entry,
                        PreparedArtifactReleaseReason::ProcessMemoHit,
                    )?;
                    continue;
                }
                Some(PackageVerificationMemoEntry::Failed { result }) => {
                    blocked_modules.insert(entry.module.clone());
                    results_by_module.insert(entry.module.clone(), result.clone());
                    release_prepared_artifact(
                        artifacts,
                        entry,
                        PreparedArtifactReleaseReason::ProcessMemoHit,
                    )?;
                    continue;
                }
                Some(PackageVerificationMemoEntry::ReferencePassed { .. }) | None => {}
            }
            runnable.push((*entry_index, *entry));
        }

        planning_state.prepared_shared_bytes = artifacts.retained_decoded_bytes();
        let plan =
            plan_fast_verifier_shards_with_state(&runnable, graph, &planning_state, options.jobs);
        let layer_started = options.measurement_mode.is_enabled().then(Instant::now);
        let mut worker_results = verify_fast_layer_with_artifact_snapshots_serial(
            &runnable,
            artifacts,
            graph,
            &verified_modules_by_module,
            &policy,
            &decode_cache_config,
            options.measurement_mode,
            artifact_observation.as_deref_mut(),
        )?;
        let layer_elapsed_ns = elapsed_nanos_if_started(layer_started);
        if options.measurement_mode.is_enabled() {
            for result in &mut worker_results {
                if let Some(mut timing) = result.worker_timing() {
                    timing.idle_elapsed_ns =
                        layer_elapsed_ns.saturating_sub(timing.active_elapsed_ns);
                    result.set_worker_timing(timing);
                }
            }
            let measurements = measurement_state
                .as_mut()
                .expect("enabled prepared layer clock has measurement state");
            measurements.record_layer_clock();
            if let Some(plan) = plan.as_ref() {
                measurements.record_fast_layer(
                    layer_index,
                    &runnable,
                    plan,
                    layer_elapsed_ns,
                    &worker_results,
                );
            }
        }

        let coordinator_started =
            (!worker_results.is_empty() && measurement_state.is_some()).then(Instant::now);
        for mut worker_result in worker_results {
            decode_cache_counters.add(worker_result.decode_cache_counters());
            let worker_declaration_details = worker_result.take_worker_declaration_details();
            if let Some(measurements) = measurement_state.as_mut() {
                measurements.record_module(
                    worker_result.entry(),
                    worker_result.measurement_observation(),
                    worker_result.checker_elapsed_ns(),
                    Some(worker_result.worker_index()),
                    worker_result.measurement_observation().checker_reached,
                );
                if let Some(declarations) = worker_declaration_details {
                    measurements.record_declaration_details(declarations);
                }
                if let Some(timing) = worker_result.worker_timing() {
                    measurements.record_worker_timing(timing, true);
                }
            }
            match worker_result {
                PackageFastLayerWorkerResult::Passed {
                    entry_index,
                    entry,
                    result,
                    record,
                    ..
                } => {
                    session.register_verified_module_with_trust(
                        record.verified_module.clone(),
                        policy.mode,
                    );
                    if let Some(measurements) = measurement_state.as_mut() {
                        measurements.package_payload.observe_module_handle_clone(
                            record.verified_module.logical_retained_bytes_v1(),
                        );
                    }
                    results_by_module.insert(entry.module.clone(), result);
                    verified_modules_by_module.insert(entry.module.clone(), *record);
                    planning_state.record_verified(entry_index)?;
                    memo_run.insert(
                        &entry.module,
                        PackageVerificationMemoEntry::FastPassed {
                            result: results_by_module
                                .get(&entry.module)
                                .expect("inserted prepared result")
                                .clone(),
                            record: Box::new(
                                verified_modules_by_module
                                    .get(&entry.module)
                                    .expect("inserted prepared record")
                                    .clone(),
                            ),
                        },
                    );
                    release_prepared_artifact(
                        artifacts,
                        entry,
                        PreparedArtifactReleaseReason::LiveResult,
                    )?;
                }
                PackageFastLayerWorkerResult::Failed { entry, result, .. } => {
                    memo_run.insert(
                        &entry.module,
                        PackageVerificationMemoEntry::Failed {
                            result: result.clone(),
                        },
                    );
                    blocked_modules.insert(entry.module.clone());
                    results_by_module.insert(entry.module.clone(), result);
                    release_prepared_artifact(
                        artifacts,
                        entry,
                        PreparedArtifactReleaseReason::LiveResult,
                    )?;
                }
            }
        }
        if let Some(started) = coordinator_started {
            measurement_state
                .as_mut()
                .expect("prepared coordinator clock has measurement state")
                .record_coordinator_merge(elapsed_nanos_if_started(Some(started)));
        }
    }

    let topological_order = graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    let modules = topological_order
        .iter()
        .map(|module| {
            results_by_module
                .remove(module)
                .expect("every prepared execution module has a result")
        })
        .collect::<Vec<_>>();
    let verified_modules = topological_order
        .iter()
        .filter_map(|module| verified_modules_by_module.remove(module))
        .collect::<Vec<_>>();
    let status = if modules
        .iter()
        .any(|module| module.status != PackageModuleVerificationStatus::Passed)
    {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;
    let measured_decode_counters = options
        .collect_decode_cache_counters
        .then_some(decode_cache_counters);
    if let Some(measurements) = measurement_state.as_mut() {
        measurements.sample_decode_cache();
    }
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options: &options,
        lock,
        entries: &entries,
        artifact_bytes: Some(&artifact_bytes),
        modules: &modules,
        measurements: measurement_state.as_ref(),
        memo_counters: memo_run.counters(),
        decode_cache_counters,
    });
    Ok(PackageFastSourceFreeVerification {
        report: PackageVerificationReport {
            mode: PackageVerificationMode::FastKernel,
            axiom_policy_hash: package_verification_policy_hash(
                validated,
                PackageVerificationMode::FastKernel,
            ),
            verdict_source,
            reference_checker_verdict: false,
            locally_accelerated: false,
            status,
            topological_order,
            modules,
            memo_counters: memo_run.counters(),
            decode_cache_counters: measured_decode_counters,
            measurements,
        },
        verified_modules,
    })
}

/// Verify fast certificates using one already validated operation graph index.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_options_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    validate_manifest_lock_identity(validated, indexed.lock())?;
    Ok(
        verify_package_fast_source_free_execution_indexed_with_strategy(
            validated,
            indexed,
            artifacts,
            options,
            PackageFastParallelStrategy::ShardRunner,
        )?
        .report,
    )
}

fn use_fast_serial_report_path(options: &PackageVerificationExecutionOptions) -> bool {
    options.jobs == 1
        && options.selected_modules.is_none()
        && !options.memoization.is_enabled()
        && options.decode_cache == PackageVerificationDecodeCacheMode::Disabled
        && !options.collect_decode_cache_counters
        && options.measurement_mode == PerformanceMeasurementMode::Off
}

/// Verify package certificates source-free with the fast kernel verifier and
/// return the verified module collection.
///
/// The returned modules are the `npa_cert::VerifiedModule` values produced by
/// the same source-free fast verifier used for the report. No source, replay,
/// metadata, theorem-index, AI trace, registry, or checker-result files are
/// read by this API.
pub fn verify_package_fast_source_free_with_modules<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    verify_package_fast_source_free_serial(validated, lock, artifacts, true)
}

fn verify_package_fast_source_free_report<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
) -> PackageVerificationResult<PackageVerificationReport> {
    Ok(verify_package_fast_source_free_serial(validated, lock, artifacts, false)?.report)
}

fn verify_package_fast_source_free_serial<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    retain_verified_modules: bool,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let policy = package_fast_kernel_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::FastKernel,
    );
    let mut session = VerifierSession::new();
    let mut results = Vec::with_capacity(graph.topological_order.len());
    let mut verified_modules = if retain_verified_modules {
        Vec::with_capacity(graph.topological_order.len())
    } else {
        Vec::new()
    };
    let mut failed_module = None::<Name>;

    for module in &graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::FastKernel,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        match verify_lock_entry(
            *entry_index,
            entry,
            &artifact_bytes,
            &mut session,
            &policy,
            &decode_cache_config,
        ) {
            Ok((verified_module, _decode_cache_counters)) => {
                if retain_verified_modules {
                    verified_modules.push(PackageVerifiedModuleRecord {
                        module: entry.module.clone(),
                        origin: entry.origin,
                        certificate: entry.certificate.clone(),
                        certificate_file_hash: entry.certificate_file_hash,
                        export_hash: entry.export_hash,
                        axiom_report_hash: entry.axiom_report_hash,
                        certificate_hash: entry.certificate_hash,
                        verified_module,
                    });
                }
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
        }
    }

    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;

    let report = PackageVerificationReport {
        mode: PackageVerificationMode::FastKernel,
        axiom_policy_hash: package_verification_policy_hash(
            validated,
            PackageVerificationMode::FastKernel,
        ),
        verdict_source,
        reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
        locally_accelerated: false,
        status,
        topological_order: graph.topological_order.clone(),
        modules: results,
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters: None,
        measurements: None,
    };

    Ok(PackageFastSourceFreeVerification {
        report,
        verified_modules,
    })
}

fn verify_package_fast_source_free_from_root_serial(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: &Path,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_options(&entries, &graph, &options)?;
    if execution_modules.is_empty() {
        return Ok(PackageFastSourceFreeVerification {
            report: empty_package_verification_report(
                validated,
                lock,
                &entries,
                &options,
                PackageVerificationMode::FastKernel,
            ),
            verified_modules: Vec::new(),
        });
    }
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let package_root = PackageCertificateRootReader::open(package_root).ok();
    let policy = package_fast_kernel_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::FastKernel,
    )
    .with_process_local_cache(options.decode_cache.process_local())
    .with_persistent_import_context_export_cache(options.decode_cache.persistent());
    let mut session = VerifierSession::new();
    let mut results = Vec::with_capacity(execution_modules.len());
    let mut failed_module = None::<Name>;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);

    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        let certificate_read =
            read_certificate_artifact_from_root(package_root.as_ref(), *entry_index, entry);
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::FastKernel,
                certificate_read.as_deref().ok(),
            ));
            continue;
        }

        let bytes = match certificate_read {
            Ok(bytes) => bytes,
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
                    None,
                ));
                continue;
            }
        };

        let checker_started = options.measurement_mode.is_enabled().then(Instant::now);
        let mut observation = PackageEntryCheckObservation::new(options.measurement_mode);
        let verification = verify_lock_entry_bytes_observed(
            *entry_index,
            entry,
            &bytes,
            PackageFastWorkerImportContext::Session(&mut session),
            &policy,
            &decode_cache_config,
            &mut observation,
        );
        let checker_elapsed_ns = elapsed_nanos_if_started(checker_started);
        decode_cache_counters.add(observation.decode_cache_counters);
        if let Some(measurements) = measurement_state.as_mut() {
            measurements.record_module(
                entry,
                &observation,
                checker_elapsed_ns,
                Some(0),
                observation.checker_reached,
            );
            measurements.record_worker_timing(
                PackageFastWorkerTiming {
                    worker_index: 0,
                    active_elapsed_ns: checker_elapsed_ns,
                    idle_elapsed_ns: 0,
                },
                false,
            );
        }
        match verification {
            Ok(_verified_module) => {
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                    Some(&bytes),
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
                    Some(&bytes),
                ));
            }
        }
    }

    let topological_order = graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;
    let measured_decode_counters = options
        .collect_decode_cache_counters
        .then_some(decode_cache_counters);
    if let Some(measurements) = measurement_state.as_mut() {
        measurements.sample_decode_cache();
    }
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options: &options,
        lock,
        entries: &entries,
        artifact_bytes: None,
        modules: &results,
        measurements: measurement_state.as_ref(),
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters,
    });

    Ok(PackageFastSourceFreeVerification {
        report: PackageVerificationReport {
            mode: PackageVerificationMode::FastKernel,
            axiom_policy_hash: package_verification_policy_hash(
                validated,
                PackageVerificationMode::FastKernel,
            ),
            verdict_source,
            reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
            locally_accelerated: false,
            status,
            topological_order,
            modules: results,
            memo_counters: PackageVerificationMemoCounters::default(),
            decode_cache_counters: measured_decode_counters,
            measurements,
        },
        verified_modules: Vec::new(),
    })
}

/// Return exact package verifier memo key inputs for all package-lock entries.
///
/// The returned key material is the same material used by the process-local
/// verifier memo. Callers that persist local-only memo entries must schema-tag
/// the key separately before serialization.
pub fn package_verification_memo_key_inputs<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    package_verification_memo_key_inputs_indexed(validated, &indexed, artifacts, mode)
}

/// Return memo-key inputs using one already validated operation graph index.
#[doc(hidden)]
pub fn package_verification_memo_key_inputs_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(indexed.lock());
    package_verification_memo_key_inputs_for_entries(
        validated,
        indexed.lock(),
        indexed.graph(),
        &entries,
        &artifact_bytes,
        mode,
    )
}

/// Return memo-key inputs from operation-owned hashed/prepared artifacts.
///
/// File hashes are reused from lock derivation. Fast retained candidates also
/// reuse their decoded header; all other inputs preserve the tolerant raw
/// header-decode omission behavior of the source-compatible entry point.
pub fn package_verification_memo_key_inputs_from_artifact_snapshots(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &PreparedPackageArtifacts,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    package_verification_memo_key_inputs_from_artifact_snapshots_indexed(
        validated, &indexed, artifacts, mode,
    )
}

/// Snapshot memo-key input boundary for an already validated operation index.
#[doc(hidden)]
pub fn package_verification_memo_key_inputs_from_artifact_snapshots_indexed(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &PreparedPackageArtifacts,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    package_verification_memo_key_inputs_from_artifact_snapshots_indexed_scoped(
        validated, indexed, artifacts, None, mode,
    )
}

fn package_verification_memo_key_inputs_from_artifact_snapshots_indexed_scoped(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &PreparedPackageArtifacts,
    execution_modules: Option<&BTreeSet<Name>>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let lock = indexed.lock();
    let lock_json = lock
        .canonical_json()
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let package_lock_hash = package_file_hash(lock_json.as_bytes());
    let package_policy_hash = package_verification_policy_hash(validated, mode);
    let checker = package_verification_checker_identity(validated, mode);
    let enabled_core_features = package_verification_enabled_core_features(validated, mode);
    let manifest = validated.manifest();
    let mut inputs = BTreeMap::new();

    // The process-memo run path must not scan the whole package before applying
    // its execution closure. Resolve only the closure's module identities
    // through the operation-owned index. The public all-entry helper retains
    // canonical topological iteration for compatibility.
    let scoped_entry_indices;
    let entry_indices = if let Some(modules) = execution_modules {
        scoped_entry_indices = snapshot_memo_scoped_entry_indices(indexed, modules);
        scoped_entry_indices.as_slice()
    } else {
        indexed.index().topological_entries()
    };

    for entry_index in entry_indices {
        let entry = &indexed.entries()[*entry_index];
        let Some(artifact) = artifacts.get(&entry.certificate) else {
            continue;
        };
        let (bytes, file_hash, retained_header) = match artifact {
            PreparedPackageArtifactView::Hashed(artifact) => {
                (artifact.bytes(), artifact.file_hash(), None)
            }
            PreparedPackageArtifactView::Prepared(artifact) => (
                artifact.bytes(),
                artifact.file_hash(),
                (mode == PackageVerificationMode::FastKernel)
                    .then(|| artifact.decoded_header())
                    .flatten(),
            ),
        };
        let header = if let Some(header) = retained_header {
            header.clone()
        } else {
            let Ok(header) = decode_snapshot_memo_header(bytes) else {
                continue;
            };
            header
        };
        let key_input = PackageAuditCacheKeyInput {
            schema: PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA.to_owned(),
            package_id: lock.package.clone(),
            package_version: lock.version.clone(),
            package_lock_schema: lock.schema.clone(),
            package_core_profile: manifest.core_spec.clone(),
            package_certificate_profile: manifest.certificate_format.clone(),
            module_certificate_format: header.format,
            module_core_spec: header.core_spec,
            package_lock_hash,
            package_policy_hash,
            checker: checker.clone(),
            module: entry.module.clone(),
            origin: entry.origin,
            certificate: entry.certificate.clone(),
            certificate_file_hash: file_hash,
            certificate_hash: entry.certificate_hash,
            export_hash: entry.export_hash,
            axiom_report_hash: entry.axiom_report_hash,
            direct_imports: indexed.graph().resolved_entry_imports[*entry_index]
                .iter()
                .map(|import| PackageAuditImportIdentity {
                    module: import.module.clone(),
                    export_hash: import.export_hash,
                    certificate_hash: import.certificate_hash,
                })
                .collect(),
            dependency_summary_hash: None,
            enabled_core_features: enabled_core_features.clone(),
        };
        inputs.insert(entry.module.clone(), key_input);
    }
    Ok(inputs)
}

fn snapshot_memo_scoped_entry_indices(
    indexed: &IndexedPackageLockGraph,
    execution_modules: &BTreeSet<Name>,
) -> Vec<usize> {
    indexed
        .index()
        .topological_entries()
        .iter()
        .copied()
        .filter(|entry_index| execution_modules.contains(&indexed.entries()[*entry_index].module))
        .collect()
}

fn decode_snapshot_memo_header(bytes: &[u8]) -> Result<CertHeader, CertError> {
    #[cfg(test)]
    SNAPSHOT_MEMO_HEADER_DECODE_COUNT.with(|count| count.set(count.get().saturating_add(1)));
    decode_module_cert_header(bytes)
}

#[cfg(test)]
fn reset_snapshot_memo_header_decode_count() {
    SNAPSHOT_MEMO_HEADER_DECODE_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
fn snapshot_memo_header_decode_count() -> usize {
    SNAPSHOT_MEMO_HEADER_DECODE_COUNT.with(std::cell::Cell::get)
}

/// Return the expected axiom-policy identity hash for a package verification run.
pub fn package_verification_axiom_policy_hash(
    validated: &ValidatedPackageManifest,
    mode: PackageVerificationMode,
) -> PackageHash {
    package_verification_policy_hash(validated, mode)
}

fn verify_package_fast_source_free_execution<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    verify_package_fast_source_free_execution_with_strategy(
        validated,
        lock,
        artifacts,
        options,
        PackageFastParallelStrategy::ShardRunner,
    )
}

fn verify_package_fast_source_free_execution_with_strategy<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
    parallel_strategy: PackageFastParallelStrategy,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    validate_execution_options(&options, PackageVerificationMode::FastKernel)?;
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_fast_source_free_execution_indexed_with_strategy(
        validated,
        &indexed,
        artifacts,
        options,
        parallel_strategy,
    )
}

fn verify_package_fast_source_free_execution_indexed_with_strategy<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
    parallel_strategy: PackageFastParallelStrategy,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    verify_package_fast_source_free_execution_indexed_with_artifact_maps(
        validated,
        indexed,
        artifact_byte_map(artifacts)?,
        None,
        options,
        parallel_strategy,
    )
}

fn verify_package_fast_source_free_execution_indexed_with_artifact_maps(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifact_bytes: BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: Option<BTreeMap<PackagePath, PackageHash>>,
    options: PackageVerificationExecutionOptions,
    parallel_strategy: PackageFastParallelStrategy,
) -> PackageVerificationResult<PackageFastSourceFreeVerification> {
    let lock = indexed.lock();
    let graph = indexed.graph();
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_indexed(indexed, &options)?;
    if execution_modules.is_empty() {
        return Ok(PackageFastSourceFreeVerification {
            report: empty_package_verification_report(
                validated,
                lock,
                &entries,
                &options,
                PackageVerificationMode::FastKernel,
            ),
            verified_modules: Vec::new(),
        });
    }
    let execution_layers = execution_layers_for_indexed(indexed, &execution_modules);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let policy = package_fast_kernel_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::FastKernel,
    )
    .with_process_local_cache(options.decode_cache.process_local())
    .with_persistent_import_context_export_cache(options.decode_cache.persistent());
    let mut memo_run = PackageVerificationMemoRun::for_hashed_run(
        &options,
        validated,
        lock,
        graph,
        &entries,
        &execution_modules,
        &artifact_bytes,
        artifact_file_hashes.as_ref(),
        PackageVerificationMode::FastKernel,
    )?;
    let mut session = VerifierSession::new();
    let mut blocked_modules = BTreeSet::<Name>::new();
    let mut results_by_module = BTreeMap::<Name, PackageModuleVerificationResult>::new();
    let mut verified_modules_by_module = BTreeMap::<Name, PackageVerifiedModuleRecord>::new();
    let mut planning_state =
        PackageFastPlanningState::new(&entries, graph, &execution_modules, &artifact_bytes);
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);
    if let Some(measurements) = measurement_state.as_mut() {
        if let Some(observation) = package_fast_execution_cost_observation(
            &entries,
            graph,
            &execution_modules,
            &execution_layers,
            &planning_state,
        ) {
            measurements.configure_fast_sharding(options.jobs, observation);
        }
    }

    for (layer_index, layer) in execution_layers.into_iter().enumerate() {
        let mut runnable = Vec::<(usize, &PackageLockEntry)>::new();
        for module in &layer {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("layer modules are lock entries");
            if let Some(blocked_import) =
                blocked_direct_import(graph, *entry_index, &blocked_modules)
            {
                results_by_module.insert(
                    entry.module.clone(),
                    module_result(
                        entry,
                        PackageModuleVerificationStatus::Skipped,
                        Some(PackageVerificationError::earlier_module_failed(
                            format!("entries[{entry_index}].module"),
                            blocked_import.as_dotted(),
                        )),
                        PackageVerificationMode::FastKernel,
                        artifact_bytes.get(&entry.certificate).copied(),
                    ),
                );
                blocked_modules.insert(entry.module.clone());
                continue;
            }
            let memo_lookup = memo_run.lookup(&entry.module);
            if memo_lookup.is_some() {
                if let Some(measurements) = measurement_state.as_mut() {
                    measurements
                        .package_payload
                        .observe_process_memo_handle_clone();
                }
            }
            match memo_lookup.as_deref() {
                Some(PackageVerificationMemoEntry::FastPassed { result, record }) => {
                    if let Some(measurements) = measurement_state.as_mut() {
                        let mut observation =
                            PackageEntryCheckObservation::new(options.measurement_mode);
                        if let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() {
                            observation.observe_certificate_bytes(bytes);
                        }
                        observation.observe_verified_module(&entry.module, &record.verified_module);
                        measurements.record_module(entry, &observation, 0, None, false);
                    }
                    session.register_verified_module_with_trust(
                        record.verified_module.clone(),
                        policy.mode,
                    );
                    if let Some(measurements) = measurement_state.as_mut() {
                        measurements.package_payload.observe_module_handle_clone(
                            record.verified_module.logical_retained_bytes_v1(),
                        );
                    }
                    results_by_module.insert(entry.module.clone(), result.clone());
                    verified_modules_by_module
                        .insert(entry.module.clone(), record.as_ref().clone());
                    planning_state.record_verified(*entry_index)?;
                    continue;
                }
                Some(PackageVerificationMemoEntry::Failed { result }) => {
                    blocked_modules.insert(entry.module.clone());
                    results_by_module.insert(entry.module.clone(), result.clone());
                    continue;
                }
                Some(PackageVerificationMemoEntry::ReferencePassed { .. }) | None => {}
            }
            runnable.push((*entry_index, *entry));
        }

        let layer_execution = verify_fast_layer(
            &runnable,
            PackageFastLayerContext {
                layer_index,
                graph,
                verified_modules_by_module: &verified_modules_by_module,
                artifact_bytes: &artifact_bytes,
                artifact_file_hashes: artifact_file_hashes.as_ref(),
                session: &session,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
                measurement_mode: options.measurement_mode,
                planning: &planning_state,
            },
            options.jobs,
            parallel_strategy,
        )?;
        if layer_execution.layer_clock_read {
            measurement_state
                .as_mut()
                .expect("enabled layer clock has measurement state")
                .record_layer_clock();
        }
        if let (Some(measurements), Some(plan)) = (
            measurement_state.as_mut(),
            layer_execution.shard_plan.as_ref(),
        ) {
            measurements.record_fast_layer(
                layer_index,
                &runnable,
                plan,
                layer_execution.layer_elapsed_ns,
                &layer_execution.results,
            );
        }
        let coordinator_started =
            (!layer_execution.results.is_empty() && measurement_state.is_some()).then(Instant::now);
        for mut worker_result in layer_execution.results {
            decode_cache_counters.add(worker_result.decode_cache_counters());
            let worker_declaration_details = worker_result.take_worker_declaration_details();
            if let Some(measurements) = measurement_state.as_mut() {
                measurements.record_module(
                    worker_result.entry(),
                    worker_result.measurement_observation(),
                    worker_result.checker_elapsed_ns(),
                    Some(worker_result.worker_index()),
                    worker_result.measurement_observation().checker_reached,
                );
                if let Some(declarations) = worker_declaration_details {
                    measurements.record_declaration_details(declarations);
                }
                if let Some(timing) = worker_result.worker_timing() {
                    measurements.record_worker_timing(timing, true);
                }
            }
            match worker_result {
                PackageFastLayerWorkerResult::Passed {
                    entry_index,
                    entry,
                    result,
                    record,
                    decode_cache_counters: _,
                    measurement_observation: _,
                    checker_elapsed_ns: _,
                    worker_index: _,
                    worker_timing: _,
                    worker_declaration_details: _,
                } => {
                    session.register_verified_module_with_trust(
                        record.verified_module.clone(),
                        policy.mode,
                    );
                    if let Some(measurements) = measurement_state.as_mut() {
                        measurements.package_payload.observe_module_handle_clone(
                            record.verified_module.logical_retained_bytes_v1(),
                        );
                    }
                    memo_run.insert(
                        &entry.module,
                        PackageVerificationMemoEntry::FastPassed {
                            result: result.clone(),
                            record: record.clone(),
                        },
                    );
                    results_by_module.insert(entry.module.clone(), result);
                    verified_modules_by_module.insert(entry.module.clone(), *record);
                    planning_state.record_verified(entry_index)?;
                }
                PackageFastLayerWorkerResult::Failed {
                    entry_index: _,
                    entry,
                    result,
                    decode_cache_counters: _,
                    measurement_observation: _,
                    checker_elapsed_ns: _,
                    worker_index: _,
                    worker_timing: _,
                    worker_declaration_details: _,
                } => {
                    memo_run.insert(
                        &entry.module,
                        PackageVerificationMemoEntry::Failed {
                            result: result.clone(),
                        },
                    );
                    blocked_modules.insert(entry.module.clone());
                    results_by_module.insert(entry.module.clone(), result);
                }
            }
        }
        if let Some(started) = coordinator_started {
            measurement_state
                .as_mut()
                .expect("coordinator clock has measurement state")
                .record_coordinator_merge(elapsed_nanos_if_started(Some(started)));
        }
    }

    let topological_order = graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    let modules = topological_order
        .iter()
        .map(|module| {
            results_by_module
                .remove(module)
                .expect("every execution module has a result")
        })
        .collect::<Vec<_>>();
    let verified_modules = topological_order
        .iter()
        .filter_map(|module| verified_modules_by_module.remove(module))
        .collect::<Vec<_>>();
    let status = if modules
        .iter()
        .any(|module| module.status != PackageModuleVerificationStatus::Passed)
    {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;
    let measured_decode_counters = options
        .collect_decode_cache_counters
        .then_some(decode_cache_counters);
    if let Some(measurements) = measurement_state.as_mut() {
        measurements.sample_decode_cache();
    }
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options: &options,
        lock,
        entries: &entries,
        artifact_bytes: Some(&artifact_bytes),
        modules: &modules,
        measurements: measurement_state.as_ref(),
        memo_counters: memo_run.counters(),
        decode_cache_counters,
    });

    Ok(PackageFastSourceFreeVerification {
        report: PackageVerificationReport {
            mode: PackageVerificationMode::FastKernel,
            axiom_policy_hash: package_verification_policy_hash(
                validated,
                PackageVerificationMode::FastKernel,
            ),
            verdict_source,
            reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
            locally_accelerated: false,
            status,
            topological_order,
            modules,
            memo_counters: memo_run.counters(),
            decode_cache_counters: measured_decode_counters,
            measurements,
        },
        verified_modules,
    })
}

enum PackageFastLayerWorkerResult<'a> {
    Passed {
        entry_index: usize,
        entry: &'a PackageLockEntry,
        result: PackageModuleVerificationResult,
        record: Box<PackageVerifiedModuleRecord>,
        decode_cache_counters: PackageVerificationDecodeCacheCounters,
        measurement_observation: PackageEntryCheckObservation,
        checker_elapsed_ns: u64,
        worker_index: usize,
        worker_timing: Option<PackageFastWorkerTiming>,
        worker_declaration_details: Option<Vec<PerformanceDeclarationMeasurement>>,
    },
    Failed {
        entry_index: usize,
        entry: &'a PackageLockEntry,
        result: PackageModuleVerificationResult,
        decode_cache_counters: PackageVerificationDecodeCacheCounters,
        measurement_observation: PackageEntryCheckObservation,
        checker_elapsed_ns: u64,
        worker_index: usize,
        worker_timing: Option<PackageFastWorkerTiming>,
        worker_declaration_details: Option<Vec<PerformanceDeclarationMeasurement>>,
    },
}

impl PackageFastLayerWorkerResult<'_> {
    fn entry_index(&self) -> usize {
        match self {
            Self::Passed { entry_index, .. } | Self::Failed { entry_index, .. } => *entry_index,
        }
    }

    fn entry(&self) -> &PackageLockEntry {
        match self {
            Self::Passed { entry, .. } | Self::Failed { entry, .. } => entry,
        }
    }

    fn checker_elapsed_ns(&self) -> u64 {
        match self {
            Self::Passed {
                checker_elapsed_ns, ..
            }
            | Self::Failed {
                checker_elapsed_ns, ..
            } => *checker_elapsed_ns,
        }
    }

    fn worker_index(&self) -> usize {
        match self {
            Self::Passed { worker_index, .. } | Self::Failed { worker_index, .. } => *worker_index,
        }
    }

    fn decode_cache_counters(&self) -> PackageVerificationDecodeCacheCounters {
        match self {
            Self::Passed {
                decode_cache_counters,
                ..
            } => *decode_cache_counters,
            Self::Failed {
                decode_cache_counters,
                ..
            } => *decode_cache_counters,
        }
    }

    fn measurement_observation(&self) -> &PackageEntryCheckObservation {
        match self {
            Self::Passed {
                measurement_observation,
                ..
            }
            | Self::Failed {
                measurement_observation,
                ..
            } => measurement_observation,
        }
    }

    fn measurement_observation_mut(&mut self) -> &mut PackageEntryCheckObservation {
        match self {
            Self::Passed {
                measurement_observation,
                ..
            }
            | Self::Failed {
                measurement_observation,
                ..
            } => measurement_observation,
        }
    }

    fn worker_timing(&self) -> Option<PackageFastWorkerTiming> {
        match self {
            Self::Passed { worker_timing, .. } | Self::Failed { worker_timing, .. } => {
                *worker_timing
            }
        }
    }

    fn set_worker_timing(&mut self, timing: PackageFastWorkerTiming) {
        match self {
            Self::Passed { worker_timing, .. } | Self::Failed { worker_timing, .. } => {
                *worker_timing = Some(timing);
            }
        }
    }

    fn take_worker_declaration_details(
        &mut self,
    ) -> Option<Vec<PerformanceDeclarationMeasurement>> {
        match self {
            Self::Passed {
                worker_declaration_details,
                ..
            }
            | Self::Failed {
                worker_declaration_details,
                ..
            } => worker_declaration_details.take(),
        }
    }

    fn set_worker_declaration_details(
        &mut self,
        declarations: Vec<PerformanceDeclarationMeasurement>,
    ) {
        match self {
            Self::Passed {
                worker_declaration_details,
                ..
            }
            | Self::Failed {
                worker_declaration_details,
                ..
            } => *worker_declaration_details = Some(declarations),
        }
    }
}

#[derive(Clone, Copy)]
struct PackageFastWorkerObservation {
    measurement_mode: PerformanceMeasurementMode,
    worker_index: usize,
}

#[derive(Clone, Copy)]
struct PackageFastLayerContext<'a> {
    layer_index: usize,
    graph: &'a PackageLockGraph,
    verified_modules_by_module: &'a BTreeMap<Name, PackageVerifiedModuleRecord>,
    artifact_bytes: &'a BTreeMap<PackagePath, &'a [u8]>,
    artifact_file_hashes: Option<&'a BTreeMap<PackagePath, PackageHash>>,
    session: &'a VerifierSession,
    policy: &'a AxiomPolicy,
    decode_cache_config: &'a PackageVerificationDecodeCacheConfig,
    measurement_mode: PerformanceMeasurementMode,
    planning: &'a PackageFastPlanningState,
}

struct PackageFastLayerExecution<'a> {
    results: Vec<PackageFastLayerWorkerResult<'a>>,
    layer_clock_read: bool,
    layer_elapsed_ns: u64,
    shard_plan: Option<PackageFastShardPlan>,
}

fn verify_fast_layer<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    context: PackageFastLayerContext<'_>,
    jobs: usize,
    parallel_strategy: PackageFastParallelStrategy,
) -> PackageVerificationResult<PackageFastLayerExecution<'a>> {
    if runnable.is_empty() {
        return Ok(PackageFastLayerExecution {
            results: Vec::new(),
            layer_clock_read: false,
            layer_elapsed_ns: 0,
            shard_plan: None,
        });
    }
    let layer_started = context.measurement_mode.is_enabled().then(Instant::now);
    #[cfg(test)]
    let (mut results, shard_plan) = if parallel_strategy == PackageFastParallelStrategy::LegacyLayer
    {
        (
            verify_fast_layer_legacy(
                runnable,
                context.artifact_bytes,
                context.artifact_file_hashes,
                context.session,
                context.policy,
                context.decode_cache_config,
                context.measurement_mode,
                jobs,
            ),
            None,
        )
    } else {
        let execution = verify_fast_layer_shards(runnable, context, jobs)?;
        (execution.results, execution.plan)
    };
    #[cfg(not(test))]
    let (mut results, shard_plan) = {
        let _ = parallel_strategy;
        let execution = verify_fast_layer_shards(runnable, context, jobs)?;
        (execution.results, execution.plan)
    };
    let layer_elapsed_ns = elapsed_nanos_if_started(layer_started);
    results.sort_by(|left, right| {
        left.entry_index()
            .cmp(&right.entry_index())
            .then_with(|| left.entry().module.cmp(&right.entry().module))
    });
    if context.measurement_mode.is_enabled() {
        for result in &mut results {
            if let Some(mut timing) = result.worker_timing() {
                timing.idle_elapsed_ns = layer_elapsed_ns.saturating_sub(timing.active_elapsed_ns);
                result.set_worker_timing(timing);
            }
        }
    }
    Ok(PackageFastLayerExecution {
        results,
        layer_clock_read: context.measurement_mode.is_enabled(),
        layer_elapsed_ns,
        shard_plan,
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn verify_fast_layer_legacy<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: Option<&BTreeMap<PackagePath, PackageHash>>,
    session: &VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    measurement_mode: PerformanceMeasurementMode,
    jobs: usize,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    if jobs == 1 {
        let worker_started = measurement_mode.is_enabled().then(Instant::now);
        let mut serial_results = Vec::with_capacity(runnable.len());
        let mut serial_session = session.clone();
        let mut declaration_details =
            PackageFastWorkerDeclarationDetailCollector::new(PERFORMANCE_DECLARATION_DETAIL_LIMIT);
        for (entry_index, entry) in runnable {
            let mut result = verify_fast_worker(
                *entry_index,
                entry,
                artifact_bytes,
                artifact_file_hashes,
                PackageFastWorkerImportContext::Session(&mut serial_session),
                policy,
                decode_cache_config,
                PackageFastWorkerObservation {
                    measurement_mode,
                    worker_index: 0,
                },
            );
            collect_worker_declaration_details(
                &mut declaration_details,
                &mut result,
                measurement_mode,
            );
            serial_results.push(result);
        }
        attach_collected_worker_declaration_details(&mut serial_results, declaration_details);
        attach_worker_timing(&mut serial_results, 0, worker_started);
        return serial_results;
    }

    let mut results = Vec::with_capacity(runnable.len());
    let mut declaration_details_by_worker =
        BTreeMap::<usize, PackageFastWorkerDeclarationDetailCollector>::new();
    for chunk in runnable.chunks(jobs) {
        thread::scope(|scope| {
            let handles = chunk
                .iter()
                .enumerate()
                .map(|(worker_index, (entry_index, entry))| {
                    let mut worker_session = session.clone();
                    thread::Builder::new()
                        .name(format!("npa-package-fast-layer-worker-{worker_index}"))
                        .stack_size(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES)
                        .spawn_scoped(scope, move || {
                            let worker_started = measurement_mode.is_enabled().then(Instant::now);
                            let mut result = verify_fast_worker(
                                *entry_index,
                                entry,
                                artifact_bytes,
                                artifact_file_hashes,
                                PackageFastWorkerImportContext::Session(&mut worker_session),
                                policy,
                                decode_cache_config,
                                PackageFastWorkerObservation {
                                    measurement_mode,
                                    worker_index,
                                },
                            );
                            let mut declaration_details =
                                PackageFastWorkerDeclarationDetailCollector::new(
                                    PERFORMANCE_DECLARATION_DETAIL_LIMIT,
                                );
                            collect_worker_declaration_details(
                                &mut declaration_details,
                                &mut result,
                                measurement_mode,
                            );
                            attach_collected_worker_declaration_details(
                                std::slice::from_mut(&mut result),
                                declaration_details,
                            );
                            attach_worker_timing(
                                std::slice::from_mut(&mut result),
                                worker_index,
                                worker_started,
                            );
                            result
                        })
                        .expect("package fast verifier layer worker should spawn")
                })
                .collect::<Vec<_>>();

            for handle in handles {
                let mut result = handle
                    .join()
                    .expect("package fast verifier worker should not panic");
                if let Some(declarations) = result.take_worker_declaration_details() {
                    declaration_details_by_worker
                        .entry(result.worker_index())
                        .or_insert_with(|| {
                            PackageFastWorkerDeclarationDetailCollector::new(
                                PERFORMANCE_DECLARATION_DETAIL_LIMIT,
                            )
                        })
                        .record_details(declarations);
                }
                results.push(result);
            }
        });
    }
    for (worker_index, collector) in declaration_details_by_worker {
        let declarations = collector.into_details();
        if let Some(result) = results
            .iter_mut()
            .find(|result| result.worker_index() == worker_index)
        {
            result.set_worker_declaration_details(declarations);
        }
    }
    results
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackageModuleCostEstimateV1 {
    artifact_bytes: u64,
    direct_import_count: u64,
    estimated_cost: u64,
    overflowed: bool,
}

#[derive(Debug)]
struct PackageFastPlanningState {
    module_cost_by_entry: Vec<Option<PackageModuleCostEstimateV1>>,
    artifact_bytes_by_entry: Vec<Option<u64>>,
    verified_membership: Vec<bool>,
    shared_base_context_bytes: u64,
    prepared_shared_bytes: u64,
    shared_base_context_overflowed: bool,
}

impl PackageFastPlanningState {
    fn new(
        entries: &[(usize, &PackageLockEntry)],
        graph: &PackageLockGraph,
        execution_modules: &BTreeSet<Name>,
        artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    ) -> Self {
        let mut state = Self {
            module_cost_by_entry: vec![None; entries.len()],
            artifact_bytes_by_entry: vec![None; entries.len()],
            verified_membership: vec![false; entries.len()],
            shared_base_context_bytes: 0,
            prepared_shared_bytes: 0,
            shared_base_context_overflowed: false,
        };
        for (entry_index, entry) in entries {
            if !execution_modules.contains(&entry.module) {
                continue;
            }
            let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() else {
                continue;
            };
            let artifact_len = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
            let direct_import_count =
                u64::try_from(graph.resolved_entry_imports[*entry_index].len()).unwrap_or(u64::MAX);
            state.artifact_bytes_by_entry[*entry_index] = Some(artifact_len);
            state.module_cost_by_entry[*entry_index] = Some(package_module_cost_estimate_v1(
                artifact_len,
                direct_import_count,
            ));
        }
        state
    }

    fn record_verified(&mut self, entry: usize) -> PackageVerificationResult<()> {
        self.record_verified_with_sink(entry, &mut ())
    }

    fn record_verified_with_sink<S: PackageVerificationPlanningCounterSink>(
        &mut self,
        entry: usize,
        counters: &mut S,
    ) -> PackageVerificationResult<()> {
        let Some(membership) = self.verified_membership.get_mut(entry) else {
            return Err(PackageVerificationError::lock_graph_invalid(
                "internal_planning_invariant:entry_index",
            ));
        };
        if *membership {
            return Err(PackageVerificationError::lock_graph_invalid(
                "internal_planning_invariant:duplicate_verified_admission",
            ));
        }
        let artifact_bytes = self
            .artifact_bytes_by_entry
            .get(entry)
            .copied()
            .flatten()
            .ok_or_else(|| {
                PackageVerificationError::lock_graph_invalid(
                    "internal_planning_invariant:missing_verified_artifact",
                )
            })?;
        *membership = true;
        let (sum, overflowed) = saturating_add_u64(self.shared_base_context_bytes, artifact_bytes);
        self.shared_base_context_bytes = sum;
        self.shared_base_context_overflowed |= overflowed || artifact_bytes == u64::MAX;
        counters.verified_record_admitted();
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PackageFastShardReductionReason {
    None,
    RequestedOne,
    RunnableWidth,
    MemoryBudget,
    EstimateOverflow,
}

impl PackageFastShardReductionReason {
    const fn measurement(self) -> PerformancePackageShardReductionReason {
        match self {
            Self::None => PerformancePackageShardReductionReason::None,
            Self::RequestedOne => PerformancePackageShardReductionReason::RequestedOne,
            Self::RunnableWidth => PerformancePackageShardReductionReason::RunnableWidth,
            Self::MemoryBudget => PerformancePackageShardReductionReason::MemoryBudget,
            Self::EstimateOverflow => PerformancePackageShardReductionReason::EstimateOverflow,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackageFastShardMemoryEstimateV3 {
    effective_jobs: usize,
    shared_base_context_bytes: u64,
    prepared_shared_bytes: u64,
    combined_shared_bytes: u64,
    per_worker_bytes: u64,
    reduction_reason: PackageFastShardReductionReason,
    overflowed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackageFastShard {
    member_indexes: Vec<usize>,
    estimated_cost: u64,
    artifact_bytes: u64,
    overflowed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackageFastShardPlan {
    requested_jobs: usize,
    effective_jobs: usize,
    reduction_reason: PackageFastShardReductionReason,
    shared_base_context_bytes: u64,
    prepared_shared_bytes: u64,
    combined_shared_bytes: u64,
    per_worker_bytes: u64,
    estimated_total_cost: u64,
    overflowed: bool,
    module_costs: BTreeMap<usize, PackageModuleCostEstimateV1>,
    shards: Vec<PackageFastShard>,
}

impl PackageFastShardPlan {
    fn estimated_max_shard_cost(&self) -> u64 {
        self.shards
            .iter()
            .map(|shard| shard.estimated_cost)
            .max()
            .unwrap_or(0)
    }

    fn avoided_base_context_clone_bytes(&self) -> (u64, bool) {
        saturating_mul_u64(
            self.shared_base_context_bytes,
            u64::try_from(self.effective_jobs).unwrap_or(u64::MAX),
        )
    }
}

struct PackageFastShardedLayerExecution<'a> {
    results: Vec<PackageFastLayerWorkerResult<'a>>,
    plan: Option<PackageFastShardPlan>,
}

fn verify_fast_layer_shards<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    context: PackageFastLayerContext<'_>,
    jobs: usize,
) -> PackageVerificationResult<PackageFastShardedLayerExecution<'a>> {
    let Some(plan) =
        plan_fast_verifier_shards_with_state(runnable, context.graph, context.planning, jobs)
    else {
        return Ok(PackageFastShardedLayerExecution {
            results: verify_fast_layer_independent_serial(
                runnable,
                context.artifact_bytes,
                context.artifact_file_hashes,
                context.session,
                context.policy,
                context.decode_cache_config,
                context.measurement_mode,
            ),
            plan: None,
        });
    };
    if plan.shards.len() <= 1 {
        let results = plan
            .shards
            .first()
            .map(|shard| verify_fast_shard(runnable, shard, context, 0))
            .unwrap_or_default();
        return Ok(PackageFastShardedLayerExecution {
            results,
            plan: Some(plan),
        });
    }

    let mut shard_results = Vec::with_capacity(plan.shards.len());
    let infrastructure_result = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(plan.shards.len());
        let mut failures = Vec::new();
        for (shard_index, shard) in plan.shards.iter().enumerate() {
            let first_module = shard
                .member_indexes
                .first()
                .map(|member_index| runnable[*member_index].1.module.clone())
                .expect("non-empty LPT shard has a first module");
            match thread::Builder::new()
                .name(format!("npa-package-fast-shard-{shard_index}"))
                .stack_size(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES)
                .spawn_scoped(scope, move || {
                    verify_fast_shard(runnable, shard, context, shard_index)
                }) {
                Ok(handle) => handles.push((shard_index, first_module, handle)),
                Err(_) => failures.push(PackageFastWorkerInfrastructureFailure {
                    shard_index,
                    first_module,
                    kind: PackageFastWorkerInfrastructureFailureKind::Spawn,
                }),
            }
        }

        for (shard_index, first_module, handle) in handles {
            match handle.join() {
                Ok(results) => shard_results.push(results),
                Err(_) => failures.push(PackageFastWorkerInfrastructureFailure {
                    shard_index,
                    first_module,
                    kind: PackageFastWorkerInfrastructureFailureKind::Join,
                }),
            }
        }
        select_package_fast_worker_infrastructure_failure(failures)
    });
    if let Some(failure) = infrastructure_result {
        return Err(PackageVerificationError::fast_worker_infrastructure_failed(
            context.layer_index,
            failure.shard_index,
            &failure.first_module,
            match failure.kind {
                PackageFastWorkerInfrastructureFailureKind::Spawn => {
                    PackageVerificationErrorReason::FastWorkerSpawnFailed
                }
                PackageFastWorkerInfrastructureFailureKind::Join => {
                    PackageVerificationErrorReason::FastWorkerJoinFailed
                }
            },
        ));
    }
    Ok(PackageFastShardedLayerExecution {
        results: shard_results.into_iter().flatten().collect(),
        plan: Some(plan),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PackageFastWorkerInfrastructureFailureKind {
    Spawn,
    Join,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackageFastWorkerInfrastructureFailure {
    shard_index: usize,
    first_module: Name,
    kind: PackageFastWorkerInfrastructureFailureKind,
}

fn select_package_fast_worker_infrastructure_failure(
    failures: impl IntoIterator<Item = PackageFastWorkerInfrastructureFailure>,
) -> Option<PackageFastWorkerInfrastructureFailure> {
    failures.into_iter().min_by_key(|failure| {
        (
            failure.shard_index,
            match failure.kind {
                PackageFastWorkerInfrastructureFailureKind::Spawn => 0usize,
                PackageFastWorkerInfrastructureFailureKind::Join => 1usize,
            },
        )
    })
}

fn plan_fast_verifier_shards_with_state(
    runnable: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    planning: &PackageFastPlanningState,
    jobs: usize,
) -> Option<PackageFastShardPlan> {
    if runnable.is_empty() {
        let (combined_shared_bytes, combined_overflowed) = saturating_add_u64(
            planning.shared_base_context_bytes,
            planning.prepared_shared_bytes,
        );
        return Some(PackageFastShardPlan {
            requested_jobs: jobs,
            effective_jobs: 0,
            reduction_reason: PackageFastShardReductionReason::RunnableWidth,
            shared_base_context_bytes: planning.shared_base_context_bytes,
            prepared_shared_bytes: planning.prepared_shared_bytes,
            combined_shared_bytes,
            per_worker_bytes: 0,
            estimated_total_cost: 0,
            overflowed: planning.shared_base_context_overflowed || combined_overflowed,
            module_costs: BTreeMap::new(),
            shards: Vec::new(),
        });
    }
    let runnable_membership = runnable
        .iter()
        .map(|(entry, _)| *entry)
        .collect::<BTreeSet<_>>();
    for (entry_index, _) in runnable {
        let import_context_complete = graph.resolved_entry_imports[*entry_index]
            .iter()
            .all(|import| planning.verified_membership[import.entry_index]);
        let same_layer_import = graph.resolved_entry_imports[*entry_index]
            .iter()
            .any(|import| runnable_membership.contains(&import.entry_index));
        if !import_context_complete || same_layer_import {
            return None;
        }
    }

    let mut module_costs = BTreeMap::new();
    let mut members = Vec::with_capacity(runnable.len());
    let mut largest_artifact_bytes = 0u64;
    let mut estimated_total_cost = 0u64;
    let mut overflowed = planning.shared_base_context_overflowed;
    for (member_index, (entry_index, entry)) in runnable.iter().enumerate() {
        let estimate = planning
            .module_cost_by_entry
            .get(*entry_index)
            .copied()
            .flatten()?;
        largest_artifact_bytes = largest_artifact_bytes.max(estimate.artifact_bytes);
        let (next_total, total_overflowed) =
            saturating_add_u64(estimated_total_cost, estimate.estimated_cost);
        estimated_total_cost = next_total;
        overflowed |= estimate.overflowed || total_overflowed;
        module_costs.insert(member_index, estimate);
        members.push((member_index, *entry_index, entry.module.clone(), estimate));
    }

    let memory = package_fast_shard_memory_estimate_v3(
        jobs,
        runnable.len(),
        planning.shared_base_context_bytes,
        planning.prepared_shared_bytes,
        largest_artifact_bytes,
        overflowed,
    );
    overflowed |= memory.overflowed;
    let (shards, lpt_overflowed) = package_fast_lpt_shards(members, memory.effective_jobs);
    overflowed |= lpt_overflowed;
    Some(PackageFastShardPlan {
        requested_jobs: jobs,
        effective_jobs: memory.effective_jobs,
        reduction_reason: memory.reduction_reason,
        shared_base_context_bytes: memory.shared_base_context_bytes,
        prepared_shared_bytes: memory.prepared_shared_bytes,
        combined_shared_bytes: memory.combined_shared_bytes,
        per_worker_bytes: memory.per_worker_bytes,
        estimated_total_cost,
        overflowed,
        module_costs,
        shards,
    })
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn legacy_plan_fast_verifier_shards_prefix_oracle<'a>(
    runnable: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    context_modules: &BTreeSet<Name>,
    verified_certificates: impl IntoIterator<Item = &'a PackagePath>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    prepared_shared_bytes: u64,
    jobs: usize,
) -> Option<PackageFastShardPlan> {
    if runnable.is_empty() {
        return Some(PackageFastShardPlan {
            requested_jobs: jobs,
            effective_jobs: 0,
            reduction_reason: PackageFastShardReductionReason::RunnableWidth,
            shared_base_context_bytes: 0,
            prepared_shared_bytes,
            combined_shared_bytes: prepared_shared_bytes,
            per_worker_bytes: 0,
            estimated_total_cost: 0,
            overflowed: false,
            module_costs: BTreeMap::new(),
            shards: Vec::new(),
        });
    }
    let runnable_modules = runnable
        .iter()
        .map(|(_, entry)| entry.module.clone())
        .collect::<BTreeSet<_>>();
    for (entry_index, _entry) in runnable {
        let import_context_complete = graph.resolved_entry_imports[*entry_index]
            .iter()
            .all(|import| context_modules.contains(&import.module));
        let same_layer_import = graph.resolved_entry_imports[*entry_index]
            .iter()
            .any(|import| runnable_modules.contains(&import.module));
        if !import_context_complete || same_layer_import {
            return None;
        }
    }

    let mut module_costs = BTreeMap::new();
    let mut members = Vec::with_capacity(runnable.len());
    let mut largest_artifact_bytes = 0u64;
    let mut estimated_total_cost = 0u64;
    let mut overflowed = false;
    for (member_index, (entry_index, entry)) in runnable.iter().enumerate() {
        let bytes = artifact_bytes.get(&entry.certificate).copied()?;
        let artifact_len = match u64::try_from(bytes.len()) {
            Ok(value) => value,
            Err(_) => {
                overflowed = true;
                u64::MAX
            }
        };
        let direct_import_count =
            match u64::try_from(graph.resolved_entry_imports[*entry_index].len()) {
                Ok(value) => value,
                Err(_) => {
                    overflowed = true;
                    u64::MAX
                }
            };
        let estimate = package_module_cost_estimate_v1(artifact_len, direct_import_count);
        overflowed |= estimate.overflowed;
        largest_artifact_bytes = largest_artifact_bytes.max(artifact_len);
        let (next_total, total_overflowed) =
            saturating_add_u64(estimated_total_cost, estimate.estimated_cost);
        estimated_total_cost = next_total;
        overflowed |= total_overflowed;
        module_costs.insert(member_index, estimate);
        members.push((member_index, *entry_index, entry.module.clone(), estimate));
    }

    let mut shared_base_context_bytes = 0u64;
    for certificate in verified_certificates {
        let bytes = artifact_bytes
            .get(certificate)
            .copied()
            .expect("verified pre-layer module retains its supplied artifact");
        let (artifact_len, conversion_overflowed) = match u64::try_from(bytes.len()) {
            Ok(value) => (value, false),
            Err(_) => (u64::MAX, true),
        };
        let (next, did_overflow) = saturating_add_u64(shared_base_context_bytes, artifact_len);
        shared_base_context_bytes = next;
        overflowed |= conversion_overflowed || did_overflow;
    }

    let memory = package_fast_shard_memory_estimate_v3(
        jobs,
        runnable.len(),
        shared_base_context_bytes,
        prepared_shared_bytes,
        largest_artifact_bytes,
        overflowed,
    );
    overflowed |= memory.overflowed;
    let (shards, lpt_overflowed) = package_fast_lpt_shards(members, memory.effective_jobs);
    overflowed |= lpt_overflowed;
    Some(PackageFastShardPlan {
        requested_jobs: jobs,
        effective_jobs: memory.effective_jobs,
        reduction_reason: memory.reduction_reason,
        shared_base_context_bytes: memory.shared_base_context_bytes,
        prepared_shared_bytes: memory.prepared_shared_bytes,
        combined_shared_bytes: memory.combined_shared_bytes,
        per_worker_bytes: memory.per_worker_bytes,
        estimated_total_cost,
        overflowed,
        module_costs,
        shards,
    })
}

#[cfg(test)]
fn plan_fast_verifier_shards(
    runnable: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    context_modules: &BTreeSet<Name>,
    verified_modules_by_module: &BTreeMap<Name, PackageVerifiedModuleRecord>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    jobs: usize,
) -> Option<PackageFastShardPlan> {
    legacy_plan_fast_verifier_shards_prefix_oracle(
        runnable,
        graph,
        context_modules,
        verified_modules_by_module
            .values()
            .map(|record| &record.certificate),
        artifact_bytes,
        0,
        jobs,
    )
}

fn package_fast_lpt_shards(
    mut members: Vec<(usize, usize, Name, PackageModuleCostEstimateV1)>,
    effective_jobs: usize,
) -> (Vec<PackageFastShard>, bool) {
    let canonical_keys = members
        .iter()
        .map(|(member_index, entry_index, module, _)| {
            (*member_index, (*entry_index, module.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    members.sort_by(|left, right| {
        right
            .3
            .estimated_cost
            .cmp(&left.3.estimated_cost)
            .then_with(|| left.2.cmp(&right.2))
            .then_with(|| left.1.cmp(&right.1))
    });
    let mut overflowed = false;
    let mut shards = (0..effective_jobs)
        .map(|_| PackageFastShard {
            member_indexes: Vec::new(),
            estimated_cost: 0,
            artifact_bytes: 0,
            overflowed: false,
        })
        .collect::<Vec<_>>();
    for (member_index, _, _, estimate) in members {
        let shard_index = shards
            .iter()
            .enumerate()
            .min_by_key(|(shard_index, shard)| (shard.estimated_cost, *shard_index))
            .map(|(shard_index, _)| shard_index)
            .expect("non-empty layer has at least one effective shard");
        let shard = &mut shards[shard_index];
        shard.member_indexes.push(member_index);
        let (estimated_cost, cost_overflowed) =
            saturating_add_u64(shard.estimated_cost, estimate.estimated_cost);
        shard.estimated_cost = estimated_cost;
        let (artifact_total, artifact_overflowed) =
            saturating_add_u64(shard.artifact_bytes, estimate.artifact_bytes);
        shard.artifact_bytes = artifact_total;
        shard.overflowed |= estimate.overflowed || cost_overflowed || artifact_overflowed;
        overflowed |= shard.overflowed;
    }
    for shard in &mut shards {
        shard
            .member_indexes
            .sort_by(|left, right| canonical_keys[left].cmp(&canonical_keys[right]));
    }
    (shards, overflowed)
}

fn package_module_cost_estimate_v1(
    artifact_bytes: u64,
    direct_import_count: u64,
) -> PackageModuleCostEstimateV1 {
    let (import_cost, multiply_overflowed) =
        saturating_mul_u64(direct_import_count, PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1);
    let (estimated_cost, add_overflowed) = saturating_add_u64(artifact_bytes, import_cost);
    PackageModuleCostEstimateV1 {
        artifact_bytes,
        direct_import_count,
        estimated_cost: estimated_cost.max(1),
        overflowed: multiply_overflowed || add_overflowed,
    }
}

fn package_fast_shard_memory_estimate_v3(
    requested_jobs: usize,
    runnable_width: usize,
    shared_base_context_bytes: u64,
    prepared_shared_bytes: u64,
    largest_runnable_artifact_bytes: u64,
    prior_overflowed: bool,
) -> PackageFastShardMemoryEstimateV3 {
    let (scratch_bytes, scratch_overflowed) = saturating_mul_u64(
        largest_runnable_artifact_bytes,
        PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1,
    );
    let worker_stack_bytes =
        u64::try_from(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES).unwrap_or(u64::MAX);
    let (stack_and_fixed, fixed_overflowed) =
        saturating_add_u64(worker_stack_bytes, PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1);
    let (base_worker_bytes, base_worker_overflowed) =
        saturating_add_u64(stack_and_fixed, scratch_bytes);
    let (per_worker_bytes, worker_overflowed) = saturating_add_u64(
        base_worker_bytes,
        PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
    );
    let (combined_shared_bytes, shared_overflowed) =
        saturating_add_u64(shared_base_context_bytes, prepared_shared_bytes);
    let overflowed = prior_overflowed
        || scratch_overflowed
        || fixed_overflowed
        || base_worker_overflowed
        || worker_overflowed
        || shared_overflowed;
    let available_for_workers =
        PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1.saturating_sub(combined_shared_bytes);
    let memory_jobs_u64 = if overflowed {
        1
    } else {
        (available_for_workers / per_worker_bytes.max(1)).max(1)
    };
    let memory_jobs = usize::try_from(memory_jobs_u64).unwrap_or(usize::MAX);
    let requested_jobs = requested_jobs.max(1);
    let runnable_width = runnable_width.max(1);
    let effective_jobs = requested_jobs.min(runnable_width).min(memory_jobs).max(1);
    let memory_limited = combined_shared_bytes >= PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1
        || available_for_workers < per_worker_bytes
        || effective_jobs < requested_jobs.min(runnable_width);
    let reduction_reason = if overflowed {
        PackageFastShardReductionReason::EstimateOverflow
    } else if memory_limited {
        PackageFastShardReductionReason::MemoryBudget
    } else if requested_jobs == 1 {
        PackageFastShardReductionReason::RequestedOne
    } else if runnable_width < requested_jobs {
        PackageFastShardReductionReason::RunnableWidth
    } else {
        PackageFastShardReductionReason::None
    };
    PackageFastShardMemoryEstimateV3 {
        effective_jobs,
        shared_base_context_bytes,
        prepared_shared_bytes,
        combined_shared_bytes,
        per_worker_bytes,
        reduction_reason,
        overflowed,
    }
}

fn saturating_add_u64(left: u64, right: u64) -> (u64, bool) {
    match left.checked_add(right) {
        Some(value) => (value, false),
        None => (u64::MAX, true),
    }
}

fn saturating_mul_u64(left: u64, right: u64) -> (u64, bool) {
    match left.checked_mul(right) {
        Some(value) => (value, false),
        None => (u64::MAX, true),
    }
}

fn verify_fast_shard<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    shard: &PackageFastShard,
    context: PackageFastLayerContext<'_>,
    worker_index: usize,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    let observation = PackageFastWorkerObservation {
        measurement_mode: context.measurement_mode,
        worker_index,
    };
    let worker_started = observation.measurement_mode.is_enabled().then(Instant::now);
    let mut results = Vec::with_capacity(shard.member_indexes.len());
    let mut declaration_details =
        PackageFastWorkerDeclarationDetailCollector::new(PERFORMANCE_DECLARATION_DETAIL_LIMIT);
    for member_index in &shard.member_indexes {
        let (entry_index, entry) = runnable[*member_index];
        let mut result = verify_fast_worker(
            entry_index,
            entry,
            context.artifact_bytes,
            context.artifact_file_hashes,
            PackageFastWorkerImportContext::Borrowed {
                resolved_imports: &context.graph.resolved_entry_imports[entry_index],
                verified_modules_by_module: context.verified_modules_by_module,
            },
            context.policy,
            context.decode_cache_config,
            observation,
        );
        collect_worker_declaration_details(
            &mut declaration_details,
            &mut result,
            observation.measurement_mode,
        );
        results.push(result);
    }
    attach_collected_worker_declaration_details(&mut results, declaration_details);
    attach_worker_timing(&mut results, observation.worker_index, worker_started);
    results
}

fn verify_fast_layer_independent_serial<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: Option<&BTreeMap<PackagePath, PackageHash>>,
    session: &VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    measurement_mode: PerformanceMeasurementMode,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    let worker_started = measurement_mode.is_enabled().then(Instant::now);
    let mut results = Vec::with_capacity(runnable.len());
    let mut declaration_details =
        PackageFastWorkerDeclarationDetailCollector::new(PERFORMANCE_DECLARATION_DETAIL_LIMIT);
    for (entry_index, entry) in runnable {
        let mut worker_session = session.clone();
        let mut result = verify_fast_worker(
            *entry_index,
            entry,
            artifact_bytes,
            artifact_file_hashes,
            PackageFastWorkerImportContext::Session(&mut worker_session),
            policy,
            decode_cache_config,
            PackageFastWorkerObservation {
                measurement_mode,
                worker_index: 0,
            },
        );
        collect_worker_declaration_details(&mut declaration_details, &mut result, measurement_mode);
        results.push(result);
    }
    attach_collected_worker_declaration_details(&mut results, declaration_details);
    attach_worker_timing(&mut results, 0, worker_started);
    results
}

fn collect_worker_declaration_details(
    collector: &mut PackageFastWorkerDeclarationDetailCollector,
    result: &mut PackageFastLayerWorkerResult<'_>,
    measurement_mode: PerformanceMeasurementMode,
) {
    if measurement_mode.is_detailed() {
        collector.record_observation(result.measurement_observation_mut());
    }
}

fn attach_collected_worker_declaration_details(
    results: &mut [PackageFastLayerWorkerResult<'_>],
    collector: PackageFastWorkerDeclarationDetailCollector,
) {
    let declarations = collector.into_details();
    if declarations.is_empty() {
        return;
    }
    results
        .first_mut()
        .expect("non-empty details come from a worker result")
        .set_worker_declaration_details(declarations);
}

fn attach_worker_timing(
    results: &mut [PackageFastLayerWorkerResult<'_>],
    worker_index: usize,
    started: Option<Instant>,
) {
    let Some(first) = results.first_mut() else {
        return;
    };
    first.set_worker_timing(PackageFastWorkerTiming {
        worker_index,
        active_elapsed_ns: elapsed_nanos_if_started(started),
        idle_elapsed_ns: 0,
    });
}

enum PackageFastWorkerImportContext<'a> {
    Session(&'a mut VerifierSession),
    Borrowed {
        resolved_imports: &'a [PackageLockResolvedImport],
        verified_modules_by_module: &'a BTreeMap<Name, PackageVerifiedModuleRecord>,
    },
}

#[allow(clippy::too_many_arguments)]
fn verify_fast_layer_with_artifact_snapshots_serial<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifacts: &PreparedPackageArtifacts,
    graph: &PackageLockGraph,
    verified_modules_by_module: &BTreeMap<Name, PackageVerifiedModuleRecord>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    measurement_mode: PerformanceMeasurementMode,
    mut artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<Vec<PackageFastLayerWorkerResult<'a>>> {
    let worker_started = measurement_mode.is_enabled().then(Instant::now);
    let mut results = Vec::with_capacity(runnable.len());
    let mut declaration_details =
        PackageFastWorkerDeclarationDetailCollector::new(PERFORMANCE_DECLARATION_DETAIL_LIMIT);
    for (entry_index, entry) in runnable {
        let input = prepared_artifact_input(artifacts, *entry_index, entry)?;
        let mut result = verify_fast_worker_input(
            *entry_index,
            entry,
            input,
            PackageFastWorkerImportContext::Borrowed {
                resolved_imports: &graph.resolved_entry_imports[*entry_index],
                verified_modules_by_module,
            },
            policy,
            decode_cache_config,
            PackageFastWorkerObservation {
                measurement_mode,
                worker_index: 0,
            },
        );
        let observation = result.measurement_observation();
        if observation.prepared_artifact_reused {
            if let Some(artifact_observation) = artifact_observation.as_deref_mut() {
                artifact_observation.observe_prepared_reuse();
            }
        }
        if observation.owned_artifact_full_decodes > 0 {
            if let Some(artifact_observation) = artifact_observation.as_deref_mut() {
                let (sum, overflowed) = artifact_observation
                    .artifact_full_decodes
                    .overflowing_add(observation.owned_artifact_full_decodes);
                artifact_observation.artifact_full_decodes =
                    if overflowed { u64::MAX } else { sum };
                artifact_observation.overflowed |= overflowed;
            }
        }
        collect_worker_declaration_details(&mut declaration_details, &mut result, measurement_mode);
        results.push(result);
    }
    attach_collected_worker_declaration_details(&mut results, declaration_details);
    attach_worker_timing(&mut results, 0, worker_started);
    Ok(results)
}

fn verify_fast_worker_input<'a>(
    entry_index: usize,
    entry: &'a PackageLockEntry,
    input: PackageCertificateInput<'_>,
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: PackageFastWorkerObservation,
) -> PackageFastLayerWorkerResult<'a> {
    let checker_started = observation.measurement_mode.is_enabled().then(Instant::now);
    let mut measurement_observation =
        PackageEntryCheckObservation::new(observation.measurement_mode);
    let verification = verify_lock_entry_input_observed(
        entry_index,
        entry,
        input,
        import_context,
        policy,
        decode_cache_config,
        &mut measurement_observation,
    );
    let checker_elapsed_ns = elapsed_nanos_if_started(checker_started);
    match verification {
        Ok(verified_module) => {
            let decode_cache_counters = measurement_observation.decode_cache_counters;
            let record = PackageVerifiedModuleRecord {
                module: entry.module.clone(),
                origin: entry.origin,
                certificate: entry.certificate.clone(),
                certificate_file_hash: entry.certificate_file_hash,
                export_hash: entry.export_hash,
                axiom_report_hash: entry.axiom_report_hash,
                certificate_hash: entry.certificate_hash,
                verified_module,
            };
            PackageFastLayerWorkerResult::Passed {
                entry_index,
                entry,
                result: module_result_for_input(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                    input,
                ),
                record: Box::new(record),
                decode_cache_counters,
                measurement_observation,
                checker_elapsed_ns,
                worker_index: observation.worker_index,
                worker_timing: None,
                worker_declaration_details: None,
            }
        }
        Err(error) => {
            let decode_cache_counters = measurement_observation.decode_cache_counters;
            PackageFastLayerWorkerResult::Failed {
                entry_index,
                entry,
                result: module_result_for_input(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
                    input,
                ),
                decode_cache_counters,
                measurement_observation,
                checker_elapsed_ns,
                worker_index: observation.worker_index,
                worker_timing: None,
                worker_declaration_details: None,
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_fast_worker<'a>(
    entry_index: usize,
    entry: &'a PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: Option<&BTreeMap<PackagePath, PackageHash>>,
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: PackageFastWorkerObservation,
) -> PackageFastLayerWorkerResult<'a> {
    let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() else {
        return PackageFastLayerWorkerResult::Failed {
            entry_index,
            entry,
            result: module_result(
                entry,
                PackageModuleVerificationStatus::Failed,
                Some(PackageVerificationError::certificate_artifact_missing(
                    format!("entries[{entry_index}].certificate"),
                    entry.certificate.as_str(),
                )),
                PackageVerificationMode::FastKernel,
                None,
            ),
            decode_cache_counters: PackageVerificationDecodeCacheCounters::default(),
            measurement_observation: PackageEntryCheckObservation::new(
                observation.measurement_mode,
            ),
            checker_elapsed_ns: 0,
            worker_index: observation.worker_index,
            worker_timing: None,
            worker_declaration_details: None,
        };
    };
    let input = artifact_file_hashes
        .and_then(|hashes| hashes.get(&entry.certificate).copied())
        .map_or(PackageCertificateInput::Raw { bytes }, |file_hash| {
            PackageCertificateInput::Hashed { bytes, file_hash }
        });
    verify_fast_worker_input(
        entry_index,
        entry,
        input,
        import_context,
        policy,
        decode_cache_config,
        observation,
    )
}

/// Verify package certificates source-free with the fast kernel verifier while
/// allowing exact local audit cache hits to synthesize local-only module results.
///
/// Cached modules are never proof evidence. Any cached module needed as an import
/// by a live-checked module is conservatively live-checked in the same run.
pub fn verify_package_fast_source_free_with_local_audit_cache_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    local_cache_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_cached_hits(
        validated,
        lock,
        artifacts,
        local_cache_hits,
        PackageModuleVerificationEvidence::LocalAuditCache,
        std::iter::empty::<Name>(),
    )
}

/// Verify package certificates source-free with the fast kernel verifier while
/// allowing exact disk-backed verifier memo hits to synthesize local-only module
/// results.
///
/// Disk memo hits are never proof evidence. Any memo-hit module needed as an
/// import by a live-checked module is conservatively live-checked in the same
/// run.
pub fn verify_package_fast_source_free_with_disk_memo_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_cache_aware_disk_memo_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        std::iter::empty::<Name>(),
    )
}

/// Verify package certificates source-free with the fast kernel verifier while
/// allowing exact disk-backed verifier memo hits to synthesize clean local-only
/// module results.
///
/// Dirty modules and their reverse dependents run live. Cached modules are never
/// proof evidence, and any cached module needed as an import by a live-checked
/// module is conservatively live-checked in the same run.
pub fn verify_package_fast_source_free_with_cache_aware_disk_memo_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_cached_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        PackageModuleVerificationEvidence::DiskVerifierMemo,
        dirty_modules,
    )
}

/// Verify with local-audit hits while consuming operation-owned snapshots.
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_local_audit_cache_hits(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    local_cache_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits(
        validated,
        lock,
        artifacts,
        local_cache_hits,
        PackageModuleVerificationEvidence::LocalAuditCache,
        std::iter::empty::<Name>(),
        None,
    )
}

/// Verify with disk-memo hits while consuming operation-owned snapshots.
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_disk_memo_hits(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    disk_memo_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_artifact_snapshots_and_cache_aware_disk_memo_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        std::iter::empty::<Name>(),
    )
}

/// Verify with cache-aware disk-memo hits using operation-owned snapshots.
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_cache_aware_disk_memo_hits(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    disk_memo_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        PackageModuleVerificationEvidence::DiskVerifierMemo,
        dirty_modules,
        None,
    )
}

/// Snapshot cached-hit verifier with optional cross-phase work observation.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    let result = (|| {
        validate_manifest_lock_identity(validated, lock)?;
        let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
            .map_err(indexed_lock_graph_verification_error)?;
        verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed_indexed(
            validated,
            &indexed,
            artifacts,
            cache_hits,
            cache_evidence,
            dirty_modules,
            artifact_observation,
        )
    })();
    artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    result
}

/// Snapshot cached-hit verifier over one validated graph index.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed_indexed(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &mut PreparedPackageArtifacts,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_indexed(
        validated,
        indexed,
        artifacts,
        cache_hits,
        cache_evidence,
        dirty_modules,
        artifact_observation,
    )
}

fn verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: &mut PreparedPackageArtifacts,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    let result = (|| {
        validate_manifest_lock_identity(validated, lock)?;
        let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
            .map_err(indexed_lock_graph_verification_error)?;
        verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_indexed(
            validated,
            &indexed,
            artifacts,
            cache_hits,
            cache_evidence,
            dirty_modules,
            artifact_observation,
        )
    })();
    artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    result
}

fn verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_indexed(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: &mut PreparedPackageArtifacts,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
    mut artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> PackageVerificationResult<PackageVerificationReport> {
    let result = (|| {
        validate_manifest_lock_identity(validated, indexed.lock())?;
        let lock = indexed.lock();
        let graph = indexed.graph();
        let entries = canonical_lock_entries(lock);
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let live_modules = local_audit_cache_live_modules(indexed, cache_hits, dirty_modules)?;
        let policy = package_fast_kernel_policy(validated);
        let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
            validated,
            PackageVerificationMode::FastKernel,
        );
        let mut session = VerifierSession::new();
        let mut results = Vec::with_capacity(graph.topological_order.len());
        let mut failed_module = None::<Name>;
        let mut locally_accelerated = false;

        for module in &graph.topological_order {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("lock graph order only contains lock entries");
            let input = prepared_artifact_input(artifacts, *entry_index, entry)?;
            if let Some(failed) = &failed_module {
                results.push(module_result_for_input(
                    entry,
                    PackageModuleVerificationStatus::Skipped,
                    Some(PackageVerificationError::earlier_module_failed(
                        format!("entries[{entry_index}].module"),
                        failed.as_dotted(),
                    )),
                    PackageVerificationMode::FastKernel,
                    input,
                ));
                release_prepared_artifact(
                    artifacts,
                    entry,
                    PreparedArtifactReleaseReason::BlockedOrSkippedResult,
                )?;
                continue;
            }

            if !live_modules.contains(module) {
                locally_accelerated = true;
                results.push(cached_module_result_for_input(
                    entry,
                    PackageVerificationMode::FastKernel,
                    cache_evidence,
                    input,
                ));
                let reason = if cache_evidence == PackageModuleVerificationEvidence::LocalAuditCache
                {
                    PreparedArtifactReleaseReason::LocalAuditCacheResult
                } else {
                    PreparedArtifactReleaseReason::DiskMemoResult
                };
                release_prepared_artifact(artifacts, entry, reason)?;
                continue;
            }

            let mut observation = PackageEntryCheckObservation::default();
            let verification = verify_lock_entry_input_observed(
                *entry_index,
                entry,
                input,
                PackageFastWorkerImportContext::Session(&mut session),
                &policy,
                &decode_cache_config,
                &mut observation,
            );
            if observation.prepared_artifact_reused {
                if let Some(artifact_observation) = artifact_observation.as_deref_mut() {
                    artifact_observation.observe_prepared_reuse();
                }
            }
            if observation.owned_artifact_full_decodes > 0 {
                if let Some(artifact_observation) = artifact_observation.as_deref_mut() {
                    observe_owned_artifact_full_decodes(
                        artifact_observation,
                        observation.owned_artifact_full_decodes,
                    );
                }
            }
            match verification {
                Ok(_) => results.push(module_result_for_input(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                    input,
                )),
                Err(error) => {
                    failed_module = Some(entry.module.clone());
                    results.push(module_result_for_input(
                        entry,
                        PackageModuleVerificationStatus::Failed,
                        Some(error),
                        PackageVerificationMode::FastKernel,
                        input,
                    ));
                }
            }
            release_prepared_artifact(artifacts, entry, PreparedArtifactReleaseReason::LiveResult)?;
        }

        let status = if failed_module.is_some() {
            PackageVerificationStatus::Failed
        } else {
            PackageVerificationStatus::Passed
        };
        let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;
        Ok(PackageVerificationReport {
            mode: PackageVerificationMode::FastKernel,
            axiom_policy_hash: package_verification_policy_hash(
                validated,
                PackageVerificationMode::FastKernel,
            ),
            verdict_source,
            reference_checker_verdict: false,
            locally_accelerated,
            status,
            topological_order: graph.topological_order.clone(),
            modules: results,
            memo_counters: PackageVerificationMemoCounters::default(),
            decode_cache_counters: None,
            measurements: None,
        })
    })();
    artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    result
}

fn verify_package_fast_source_free_with_cached_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_fast_source_free_with_cached_hits_indexed(
        validated,
        &indexed,
        artifacts,
        cache_hits,
        cache_evidence,
        dirty_modules,
    )
}

/// Verify a cache-aware fast run using one validated operation graph index.
#[doc(hidden)]
pub fn verify_package_fast_source_free_with_cached_hits_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let lock = indexed.lock();
    let graph = indexed.graph();
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let live_modules = local_audit_cache_live_modules(indexed, cache_hits, dirty_modules)?;
    let policy = package_fast_kernel_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::FastKernel,
    );
    let mut session = VerifierSession::new();
    let mut results = Vec::with_capacity(graph.topological_order.len());
    let mut failed_module = None::<Name>;
    let mut locally_accelerated = false;

    for module in &graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::FastKernel,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        if !live_modules.contains(module) {
            locally_accelerated = true;
            results.push(cached_module_result(
                entry,
                PackageVerificationMode::FastKernel,
                cache_evidence,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        match verify_lock_entry(
            *entry_index,
            entry,
            &artifact_bytes,
            &mut session,
            &policy,
            &decode_cache_config,
        ) {
            Ok(_) => {
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
        }
    }

    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::FastKernelCertificateVerifier;

    Ok(PackageVerificationReport {
        mode: PackageVerificationMode::FastKernel,
        axiom_policy_hash: package_verification_policy_hash(
            validated,
            PackageVerificationMode::FastKernel,
        ),
        verdict_source,
        reference_checker_verdict: false,
        locally_accelerated,
        status,
        topological_order: graph.topological_order.clone(),
        modules: results,
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters: None,
        measurements: None,
    })
}

/// Verify package certificates source-free with the independent reference checker.
///
/// This verifier consumes only a validated package manifest, a package lock, and
/// caller-provided certificate bytes. It executes `npa-checker-ref` in-process
/// in package-lock topological order and builds each import store from modules
/// already accepted by the same reference checker.
pub fn verify_package_reference_source_free<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_options(
        validated,
        lock,
        artifacts,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Verify package certificates source-free with the independent reference
/// checker, reading certificate artifacts lazily from a package root.
///
/// This verifier reads only the current module certificate needed by the
/// topological verifier loop. Source files, replay metadata, theorem indexes,
/// AI traces, and checker-result caches are not read.
pub fn verify_package_reference_source_free_from_root(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: impl AsRef<Path>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_from_root_with_options(
        validated,
        lock,
        package_root,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Verify package certificates source-free with the independent reference
/// checker and explicit execution options, reading certificate artifacts lazily
/// from a package root.
///
/// Path-backed verification currently supports disabled process-local verifier
/// memoization so that certificate bytes are not preloaded to compute memo keys.
pub fn verify_package_reference_source_free_from_root_with_options(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: impl AsRef<Path>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::Reference,
            options.jobs,
        ));
    }
    if options.memoization.is_enabled() {
        return Err(PackageVerificationError::unsupported_lazy_memoization());
    }
    verify_package_reference_source_free_from_root_execution(
        validated,
        lock,
        package_root.as_ref(),
        options,
    )
}

/// Verify package certificates source-free with the independent reference checker
/// and explicit execution options.
pub fn verify_package_reference_source_free_with_options<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::Reference,
            options.jobs,
        ));
    }
    verify_package_reference_source_free_execution(validated, lock, artifacts, options)
}

/// Verify reference certificates from owned artifacts whose file hashes were
/// already bound by canonical lock derivation.
///
/// Only the file hash is reused. The independent checker continues to receive
/// the authoritative certificate bytes and never receives retained Rust decode
/// products.
pub fn verify_package_reference_source_free_with_hashed_artifacts<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_hashed_artifacts_and_options(
        validated,
        lock,
        artifacts,
        PackageVerificationExecutionOptions::default(),
    )
}

/// Hashed-artifact reference verification with explicit execution options.
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_options<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::Reference,
            options.jobs,
        ));
    }
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_reference_source_free_with_hashed_artifacts_and_options_indexed(
        validated, &indexed, artifacts, options,
    )
}

/// Hashed-artifact reference verification over one validated graph index.
#[doc(hidden)]
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_options_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::Reference,
            options.jobs,
        ));
    }
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let artifacts = artifacts.into_iter().collect::<Vec<_>>();
    let file_hashes = artifacts
        .iter()
        .map(|artifact| (artifact.path().clone(), artifact.file_hash()))
        .collect::<BTreeMap<_, _>>();
    verify_package_reference_source_free_execution_indexed_with_validation(
        validated,
        indexed,
        artifacts.iter().map(|artifact| PackageCertificateArtifact {
            path: artifact.path().clone(),
            bytes: artifact.bytes(),
        }),
        Some(file_hashes),
        options,
    )
}

/// Verify reference certificates using one already validated operation index.
#[doc(hidden)]
pub fn verify_package_reference_source_free_with_options_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    if options.jobs > 1 {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            PackageVerificationMode::Reference,
            options.jobs,
        ));
    }
    verify_package_reference_source_free_execution_indexed_with_validation(
        validated, indexed, artifacts, None, options,
    )
}

fn verify_package_reference_source_free_execution<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_execution_with_validation(
        validated,
        lock,
        artifacts,
        options,
        PackageVerificationInputValidationMode::RequireManifestPins,
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PackageVerificationInputValidationMode {
    RequireManifestPins,
    ObserveLocalArtifacts,
}

pub(crate) fn verify_package_reference_source_free_execution_with_validation<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    options: PackageVerificationExecutionOptions,
    input_validation: PackageVerificationInputValidationMode,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = match input_validation {
        PackageVerificationInputValidationMode::RequireManifestPins => {
            validate_package_lock_against_manifest_indexed(validated, lock)
        }
        PackageVerificationInputValidationMode::ObserveLocalArtifacts => {
            validate_observed_package_lock_against_manifest_indexed(validated, lock)
        }
    }
    .map_err(indexed_lock_graph_verification_error)?;
    verify_package_reference_source_free_execution_indexed_with_validation(
        validated, &indexed, artifacts, None, options,
    )
}

fn verify_package_reference_source_free_execution_indexed_with_validation<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    artifact_file_hashes: Option<BTreeMap<PackagePath, PackageHash>>,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let lock = indexed.lock();
    let graph = indexed.graph();
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_indexed(indexed, &options)?;
    if execution_modules.is_empty() {
        return Ok(empty_package_verification_report(
            validated,
            lock,
            &entries,
            &options,
            PackageVerificationMode::Reference,
        ));
    }
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let policy = package_reference_checker_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::Reference,
    )
    .with_process_local_cache(options.decode_cache.process_local())
    .with_persistent_import_context_export_cache(options.decode_cache.persistent());
    let mut memo_run = PackageVerificationMemoRun::for_hashed_run(
        &options,
        validated,
        lock,
        graph,
        &entries,
        &execution_modules,
        &artifact_bytes,
        artifact_file_hashes.as_ref(),
        PackageVerificationMode::Reference,
    )?;
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses =
        reference_import_use_counts(&entries, graph, &execution_modules);
    let mut results = Vec::with_capacity(graph.topological_order.len());
    let mut failed_module = None::<Name>;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);

    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::Reference,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        let memo_lookup = memo_run.lookup(&entry.module);
        if memo_lookup.is_some() {
            if let Some(measurements) = measurement_state.as_mut() {
                measurements
                    .package_payload
                    .observe_process_memo_handle_clone();
            }
        }
        match memo_lookup.as_deref() {
            Some(PackageVerificationMemoEntry::ReferencePassed { result, checked }) => {
                if let Some(measurements) = measurement_state.as_mut() {
                    let mut observation =
                        PackageEntryCheckObservation::new(options.measurement_mode);
                    if let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() {
                        observation.observe_certificate_bytes(bytes);
                    }
                    observation.observe_reference_declaration_count(checked.declaration_count());
                    measurements.record_module(entry, &observation, 0, None, false);
                }
                record_reference_checked_module_for_dependents(
                    &mut checked_by_module,
                    &remaining_import_uses,
                    entry,
                    checked.as_ref().clone(),
                );
                retire_reference_imports_after_module(
                    *entry_index,
                    graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(result.clone());
                continue;
            }
            Some(PackageVerificationMemoEntry::Failed { result }) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                results.push(result.clone());
                continue;
            }
            Some(PackageVerificationMemoEntry::FastPassed { .. }) | None => {}
        }

        let resolved_imports = &graph.resolved_entry_imports[*entry_index];
        let checker_started = options.measurement_mode.is_enabled().then(Instant::now);
        let mut observation = PackageEntryCheckObservation::new(options.measurement_mode);
        let verification = verify_reference_lock_entry_observed(
            *entry_index,
            entry,
            resolved_imports,
            PackageReferenceEntryContext {
                lock,
                entries: &entries,
                artifact_bytes: &artifact_bytes,
                artifact_file_hashes: artifact_file_hashes.as_ref(),
                checked_by_module: &checked_by_module,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
            },
            &mut observation,
        );
        let checker_elapsed_ns = elapsed_nanos_if_started(checker_started);
        decode_cache_counters.add(observation.decode_cache_counters);
        if let Some(measurements) = measurement_state.as_mut() {
            measurements.record_module(
                entry,
                &observation,
                checker_elapsed_ns,
                Some(0),
                observation.checker_reached,
            );
            measurements.record_worker_timing(
                PackageFastWorkerTiming {
                    worker_index: 0,
                    active_elapsed_ns: checker_elapsed_ns,
                    idle_elapsed_ns: 0,
                },
                false,
            );
        }
        match verification {
            Ok(checked) => {
                let result = module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::Reference,
                    artifact_bytes.get(&entry.certificate).copied(),
                );
                memo_run.insert(
                    &entry.module,
                    PackageVerificationMemoEntry::ReferencePassed {
                        result: result.clone(),
                        checked: Box::new(checked.clone()),
                    },
                );
                record_reference_checked_module_for_dependents(
                    &mut checked_by_module,
                    &remaining_import_uses,
                    entry,
                    checked,
                );
                retire_reference_imports_after_module(
                    *entry_index,
                    graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(result);
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                let result = module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::Reference,
                    artifact_bytes.get(&entry.certificate).copied(),
                );
                memo_run.insert(
                    &entry.module,
                    PackageVerificationMemoEntry::Failed {
                        result: result.clone(),
                    },
                );
                results.push(result);
            }
        }
    }

    let topological_order = graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::ReferenceChecker;
    let measured_decode_counters = options
        .collect_decode_cache_counters
        .then_some(decode_cache_counters);
    if let Some(measurements) = measurement_state.as_mut() {
        measurements.sample_decode_cache();
    }
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options: &options,
        lock,
        entries: &entries,
        artifact_bytes: Some(&artifact_bytes),
        modules: &results,
        measurements: measurement_state.as_ref(),
        memo_counters: memo_run.counters(),
        decode_cache_counters,
    });

    Ok(PackageVerificationReport {
        mode: PackageVerificationMode::Reference,
        axiom_policy_hash: package_verification_policy_hash(
            validated,
            PackageVerificationMode::Reference,
        ),
        verdict_source,
        reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
        locally_accelerated: false,
        status,
        topological_order,
        modules: results,
        memo_counters: memo_run.counters(),
        decode_cache_counters: measured_decode_counters,
        measurements,
    })
}

fn verify_package_reference_source_free_from_root_execution(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    package_root: &Path,
    options: PackageVerificationExecutionOptions,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_options(&entries, &graph, &options)?;
    if execution_modules.is_empty() {
        return Ok(empty_package_verification_report(
            validated,
            lock,
            &entries,
            &options,
            PackageVerificationMode::Reference,
        ));
    }
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let package_root = PackageCertificateRootReader::open(package_root).ok();
    let policy = package_reference_checker_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::Reference,
    )
    .with_process_local_cache(options.decode_cache.process_local())
    .with_persistent_import_context_export_cache(options.decode_cache.persistent());
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses =
        reference_import_use_counts(&entries, &graph, &execution_modules);
    let mut results = Vec::with_capacity(execution_modules.len());
    let mut failed_module = None::<Name>;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);

    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        let certificate_read =
            read_certificate_artifact_from_root(package_root.as_ref(), *entry_index, entry);
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::Reference,
                certificate_read.as_deref().ok(),
            ));
            continue;
        }

        let bytes = match certificate_read {
            Ok(bytes) => bytes,
            Err(error) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::Reference,
                    None,
                ));
                continue;
            }
        };

        let resolved_imports = &graph.resolved_entry_imports[*entry_index];
        let checker_started = options.measurement_mode.is_enabled().then(Instant::now);
        let mut observation = PackageEntryCheckObservation::new(options.measurement_mode);
        let verification = verify_reference_lock_entry_bytes_observed(
            *entry_index,
            entry,
            resolved_imports,
            &bytes,
            None,
            PackageReferenceEntryBytesContext {
                lock,
                entries: &entries,
                checked_by_module: &checked_by_module,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
            },
            &mut observation,
        );
        let checker_elapsed_ns = elapsed_nanos_if_started(checker_started);
        decode_cache_counters.add(observation.decode_cache_counters);
        if let Some(measurements) = measurement_state.as_mut() {
            measurements.record_module(
                entry,
                &observation,
                checker_elapsed_ns,
                Some(0),
                observation.checker_reached,
            );
            measurements.record_worker_timing(
                PackageFastWorkerTiming {
                    worker_index: 0,
                    active_elapsed_ns: checker_elapsed_ns,
                    idle_elapsed_ns: 0,
                },
                false,
            );
        }
        match verification {
            Ok(checked) => {
                let result = module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::Reference,
                    Some(&bytes),
                );
                record_reference_checked_module_for_dependents(
                    &mut checked_by_module,
                    &remaining_import_uses,
                    entry,
                    checked,
                );
                retire_reference_imports_after_module(
                    *entry_index,
                    &graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(result);
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                let result = module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::Reference,
                    Some(&bytes),
                );
                results.push(result);
            }
        }
    }

    let topological_order = graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::ReferenceChecker;
    let measured_decode_counters = options
        .collect_decode_cache_counters
        .then_some(decode_cache_counters);
    if let Some(measurements) = measurement_state.as_mut() {
        measurements.sample_decode_cache();
    }
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options: &options,
        lock,
        entries: &entries,
        artifact_bytes: None,
        modules: &results,
        measurements: measurement_state.as_ref(),
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters,
    });

    Ok(PackageVerificationReport {
        mode: PackageVerificationMode::Reference,
        axiom_policy_hash: package_verification_policy_hash(
            validated,
            PackageVerificationMode::Reference,
        ),
        verdict_source,
        reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
        locally_accelerated: false,
        status,
        topological_order,
        modules: results,
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters: measured_decode_counters,
        measurements,
    })
}

/// Verify package certificates source-free with the independent reference checker
/// while allowing exact local audit cache hits to synthesize local-only module
/// results.
///
/// Cached modules are never proof evidence. Any cached module needed as an import
/// by a live-checked module is conservatively live-checked in the same run.
pub fn verify_package_reference_source_free_with_local_audit_cache_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    local_cache_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_cached_hits(
        validated,
        lock,
        artifacts,
        local_cache_hits,
        PackageModuleVerificationEvidence::LocalAuditCache,
        std::iter::empty::<Name>(),
    )
}

/// Verify package certificates source-free with the independent reference
/// checker while allowing exact disk-backed verifier memo hits to synthesize
/// local-only module results.
///
/// Disk memo hits are never proof evidence. Any memo-hit module needed as an
/// import by a live-checked module is conservatively live-checked in the same
/// run.
pub fn verify_package_reference_source_free_with_disk_memo_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_cache_aware_disk_memo_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        std::iter::empty::<Name>(),
    )
}

/// Verify package certificates source-free with the independent reference
/// checker while allowing exact disk-backed verifier memo hits to synthesize
/// clean local-only module results.
///
/// Dirty modules and their reverse dependents run live. Cached modules are never
/// proof evidence, and any cached module needed as an import by a live-checked
/// module is conservatively live-checked in the same run.
pub fn verify_package_reference_source_free_with_cache_aware_disk_memo_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_cached_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        PackageModuleVerificationEvidence::DiskVerifierMemo,
        dirty_modules,
    )
}

/// Reference local-audit wrapper over lock-derived hashed artifacts.
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_local_audit_cache_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    local_cache_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits(
        validated,
        lock,
        artifacts,
        local_cache_hits,
        PackageModuleVerificationEvidence::LocalAuditCache,
        std::iter::empty::<Name>(),
    )
}

/// Reference disk-memo wrapper over lock-derived hashed artifacts.
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_disk_memo_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_hashed_artifacts_and_cache_aware_disk_memo_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        std::iter::empty::<Name>(),
    )
}

/// Cache-aware reference disk-memo wrapper over lock-derived hashed artifacts.
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_cache_aware_disk_memo_hits<
    'a,
>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    disk_memo_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits(
        validated,
        lock,
        artifacts,
        disk_memo_hits,
        PackageModuleVerificationEvidence::DiskVerifierMemo,
        dirty_modules,
    )
}

fn verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits_indexed(
        validated,
        &indexed,
        artifacts,
        cache_hits,
        cache_evidence,
        dirty_modules,
    )
}

/// Reference cached-hit verification over hashed artifacts and one graph index.
#[doc(hidden)]
pub fn verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let artifacts = artifacts.into_iter().collect::<Vec<_>>();
    let file_hashes = artifacts
        .iter()
        .map(|artifact| (artifact.path().clone(), artifact.file_hash()))
        .collect::<BTreeMap<_, _>>();
    verify_package_reference_source_free_with_cached_hits_indexed_prehashed(
        validated,
        indexed,
        artifacts.iter().map(|artifact| PackageCertificateArtifact {
            path: artifact.path().clone(),
            bytes: artifact.bytes(),
        }),
        Some(file_hashes),
        cache_hits,
        cache_evidence,
        dirty_modules,
    )
}

fn verify_package_reference_source_free_with_cached_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, lock)?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, lock)
        .map_err(indexed_lock_graph_verification_error)?;
    verify_package_reference_source_free_with_cached_hits_indexed(
        validated,
        &indexed,
        artifacts,
        cache_hits,
        cache_evidence,
        dirty_modules,
    )
}

/// Verify a cache-aware reference run using one validated operation graph index.
#[doc(hidden)]
pub fn verify_package_reference_source_free_with_cached_hits_indexed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    verify_package_reference_source_free_with_cached_hits_indexed_prehashed(
        validated,
        indexed,
        artifacts,
        None,
        cache_hits,
        cache_evidence,
        dirty_modules,
    )
}

fn verify_package_reference_source_free_with_cached_hits_indexed_prehashed<'a>(
    validated: &ValidatedPackageManifest,
    indexed: &IndexedPackageLockGraph,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    artifact_file_hashes: Option<BTreeMap<PackagePath, PackageHash>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, indexed.lock())?;
    let lock = indexed.lock();
    let graph = indexed.graph();
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let live_modules = local_audit_cache_live_modules(indexed, cache_hits, dirty_modules)?;
    let policy = package_reference_checker_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::Reference,
    );
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses = reference_import_use_counts(&entries, graph, &live_modules);
    let mut results = Vec::with_capacity(graph.topological_order.len());
    let mut failed_module = None::<Name>;
    let mut locally_accelerated = false;

    for module in &graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::Reference,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        if !live_modules.contains(module) {
            locally_accelerated = true;
            results.push(cached_module_result(
                entry,
                PackageVerificationMode::Reference,
                cache_evidence,
                artifact_bytes.get(&entry.certificate).copied(),
            ));
            continue;
        }

        let resolved_imports = &graph.resolved_entry_imports[*entry_index];
        match verify_reference_lock_entry(
            *entry_index,
            entry,
            resolved_imports,
            PackageReferenceEntryContext {
                lock,
                entries: &entries,
                artifact_bytes: &artifact_bytes,
                artifact_file_hashes: artifact_file_hashes.as_ref(),
                checked_by_module: &checked_by_module,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
            },
        ) {
            Ok((checked, _decode_cache_counters)) => {
                record_reference_checked_module_for_dependents(
                    &mut checked_by_module,
                    &remaining_import_uses,
                    entry,
                    checked,
                );
                retire_reference_imports_after_module(
                    *entry_index,
                    graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::Reference,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::Reference,
                    artifact_bytes.get(&entry.certificate).copied(),
                ));
            }
        }
    }

    let status = if failed_module.is_some() {
        PackageVerificationStatus::Failed
    } else {
        PackageVerificationStatus::Passed
    };
    let verdict_source = PackageVerificationVerdictSource::ReferenceChecker;

    Ok(PackageVerificationReport {
        mode: PackageVerificationMode::Reference,
        axiom_policy_hash: package_verification_policy_hash(
            validated,
            PackageVerificationMode::Reference,
        ),
        verdict_source,
        reference_checker_verdict: verdict_source.is_reference_checker_verdict()
            && !locally_accelerated,
        locally_accelerated,
        status,
        topological_order: graph.topological_order.clone(),
        modules: results,
        memo_counters: PackageVerificationMemoCounters::default(),
        decode_cache_counters: None,
        measurements: None,
    })
}

/// Materialize one Phase 8 import lock per package-lock entry.
///
/// Each generated import lock contains exactly the module's direct certificate
/// imports from the package lock. No source, replay, metadata, theorem-index,
/// AI trace, registry, or solver data is introduced.
pub fn materialize_package_phase8_import_locks(
    lock: &PackageLockManifest,
    checker_profile: &str,
) -> PackageVerificationResult<Vec<PackagePhase8ImportLockMaterialization>> {
    let graph = build_package_lock_graph(lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let mut materialized = Vec::with_capacity(graph.topological_order.len());

    for module in &graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        let import_lock = materialize_phase8_import_lock_for_entry(
            lock,
            *entry_index,
            entry,
            &graph.resolved_entry_imports[*entry_index],
            &entries,
            checker_profile,
        )?;
        materialized.push(import_lock);
    }

    Ok(materialized)
}

/// Materialize Phase 8 machine-check requests for every package-lock entry.
///
/// This derives per-module direct-import locks from the package lock and then
/// delegates request construction to the existing Phase 8 request materializer,
/// preserving request-hash recomputation and request-store behavior.
pub fn materialize_package_phase8_requests<'a>(
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    policy: &IndependentCheckerRunnerPolicy,
    checker_profile: &str,
    existing_store: Option<&IndependentCheckerRequestStoreManifest>,
) -> PackageVerificationResult<PackagePhase8RequestMaterializationReport> {
    let graph = build_package_lock_graph(lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let mut current_store =
        existing_store
            .cloned()
            .unwrap_or(IndependentCheckerRequestStoreManifest {
                requests: Vec::new(),
            });
    let mut request_store_file_hash =
        independent_checker_file_hash(current_store.canonical_json().as_bytes());
    let mut request_store_rewrite_required = false;
    let mut modules = Vec::with_capacity(graph.topological_order.len());

    for module in &graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .expect("lock graph order only contains lock entries");
        let bytes = artifact_bytes
            .get(&entry.certificate)
            .copied()
            .ok_or_else(|| {
                PackageVerificationError::certificate_artifact_missing(
                    format!("entries[{entry_index}].certificate"),
                    entry.certificate.as_str(),
                )
            })?;
        let actual_file_hash = package_file_hash(bytes);
        if entry.certificate_file_hash != actual_file_hash {
            return Err(PackageVerificationError::certificate_file_hash_mismatch(
                format!("entries[{entry_index}].certificate_file_hash"),
                entry.certificate_file_hash,
                actual_file_hash,
            ));
        }

        let import_lock = materialize_phase8_import_lock_for_entry(
            lock,
            *entry_index,
            entry,
            &graph.resolved_entry_imports[*entry_index],
            &entries,
            checker_profile,
        )?;
        let import_lock_json = import_lock.manifest.canonical_json();
        let request_id = package_phase8_request_id(lock, &entry.module, checker_profile);
        let request_path = package_phase8_request_path(lock, &entry.module, checker_profile);
        let materialized = independent_checker_request_materialize(
            policy,
            entry.module.as_dotted(),
            entry.certificate.as_str(),
            bytes,
            &import_lock.path,
            import_lock_json.as_bytes(),
            import_lock.manifest_hash,
            checker_profile,
            &request_id,
            &request_path,
            Some(&current_store),
        )
        .map_err(|error| {
            PackageVerificationError::phase8_request_materialization_failed(
                format!("entries[{entry_index}].independent_checker_request"),
                error,
            )
        })?;

        let actual_certificate_hash =
            PackageHash::from(materialized.request.certificate.expected_certificate_hash);
        if actual_certificate_hash != entry.certificate_hash {
            return Err(PackageVerificationError::certificate_hash_mismatch(
                format!("entries[{entry_index}].certificate_hash"),
                entry.certificate_hash,
                actual_certificate_hash,
            ));
        }

        request_store_rewrite_required |= materialized.request_store_rewrite_required;
        current_store = materialized.request_store.clone();
        request_store_file_hash = materialized.request_store_file_hash;
        modules.push(PackagePhase8RequestMaterialization {
            module: entry.module.clone(),
            checker_profile: checker_profile.to_owned(),
            import_lock_path: import_lock.path,
            import_lock_manifest: import_lock.manifest,
            import_lock_manifest_hash: import_lock.manifest_hash,
            request_path,
            request: materialized.request,
            request_file_hash: materialized.request_file_hash,
        });
    }

    Ok(PackagePhase8RequestMaterializationReport {
        modules,
        request_store: current_store,
        request_store_file_hash,
        request_store_rewrite_required,
    })
}

fn materialize_phase8_import_lock_for_entry(
    lock: &PackageLockManifest,
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    entries: &[(usize, &PackageLockEntry)],
    checker_profile: &str,
) -> PackageVerificationResult<PackagePhase8ImportLockMaterialization> {
    let mut imports = resolved_imports
        .iter()
        .map(|import| {
            let import_entry = entries
                .get(import.entry_index)
                .map(|(_, entry)| *entry)
                .expect("resolved import index points into canonical lock entries");
            IndependentCheckerImportLockEntry {
                module: import.module.as_dotted(),
                export_hash: import.export_hash.into_bytes(),
                certificate: IndependentCheckerImportLockCertificate {
                    path: import_entry.certificate.as_str().to_owned(),
                    file_hash: import_entry.certificate_file_hash.into_bytes(),
                    certificate_hash: import.certificate_hash.into_bytes(),
                },
            }
        })
        .collect::<Vec<_>>();
    imports.sort_by(|left, right| {
        phase8_import_lock_module_sort_key(&left.module)
            .cmp(&phase8_import_lock_module_sort_key(&right.module))
            .then_with(|| left.certificate.path.cmp(&right.certificate.path))
            .then_with(|| {
                left.certificate
                    .certificate_hash
                    .cmp(&right.certificate.certificate_hash)
            })
            .then_with(|| left.certificate.file_hash.cmp(&right.certificate.file_hash))
    });
    let manifest = IndependentCheckerImportLockManifest { imports };
    let manifest_json = manifest.canonical_json();
    parse_independent_checker_import_lock_manifest(&manifest_json).map_err(|error| {
        PackageVerificationError::phase8_import_lock_invalid(
            format!("entries[{entry_index}].independent_checker_import_lock"),
            format!("{error:?}"),
        )
    })?;
    let manifest_hash = independent_checker_file_hash(manifest_json.as_bytes());

    Ok(PackagePhase8ImportLockMaterialization {
        module: entry.module.clone(),
        path: package_phase8_import_lock_path(lock, &entry.module, checker_profile),
        manifest,
        manifest_hash,
    })
}

fn phase8_import_lock_module_sort_key(module: &str) -> Vec<u8> {
    parse_module_name_wire(module)
        .and_then(|name| machine_api_name_canonical_bytes(&name))
        .unwrap_or_else(|_| module.as_bytes().to_vec())
}

fn package_phase8_request_id(
    lock: &PackageLockManifest,
    module: &Name,
    checker_profile: &str,
) -> String {
    format!(
        "package:{}:{}:{}:{}",
        lock.package.as_str(),
        lock.version.as_str(),
        module.as_dotted(),
        checker_profile
    )
}

fn package_phase8_import_lock_path(
    lock: &PackageLockManifest,
    module: &Name,
    checker_profile: &str,
) -> String {
    format!(
        "{}/imports.json",
        package_phase8_module_dir(lock, module, checker_profile)
    )
}

fn package_phase8_request_path(
    lock: &PackageLockManifest,
    module: &Name,
    checker_profile: &str,
) -> String {
    format!(
        "{}/request.json",
        package_phase8_module_dir(lock, module, checker_profile)
    )
}

fn package_phase8_module_dir(
    lock: &PackageLockManifest,
    module: &Name,
    checker_profile: &str,
) -> String {
    format!(
        "generated/checker-requests/{}/{}/{}/{}",
        lock.package.as_str(),
        lock.version.as_str(),
        module.as_dotted(),
        checker_profile
    )
}

fn validate_manifest_lock_identity(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageVerificationResult<()> {
    let manifest = validated.manifest();
    if lock.package != manifest.package {
        return Err(PackageVerificationError::package_identity_mismatch(
            "package",
            "package",
            manifest.package.as_str(),
            lock.package.as_str(),
        ));
    }
    if lock.version != manifest.version {
        return Err(PackageVerificationError::package_identity_mismatch(
            "version",
            "version",
            manifest.version.as_str(),
            lock.version.as_str(),
        ));
    }
    Ok(())
}

fn artifact_byte_map<'a>(
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
) -> PackageVerificationResult<BTreeMap<PackagePath, &'a [u8]>> {
    let mut artifact_bytes = BTreeMap::new();
    for artifact in artifacts {
        if artifact_bytes
            .insert(artifact.path.clone(), artifact.bytes)
            .is_some()
        {
            return Err(PackageVerificationError::duplicate_certificate_artifact(
                "artifacts",
                artifact.path.as_str(),
            ));
        }
    }
    Ok(artifact_bytes)
}

type HashedArtifactMaps<'a> = (
    BTreeMap<PackagePath, &'a [u8]>,
    BTreeMap<PackagePath, PackageHash>,
);

fn hashed_artifact_maps<'a>(
    artifacts: impl IntoIterator<Item = &'a HashedPackageLockArtifact>,
) -> PackageVerificationResult<HashedArtifactMaps<'a>> {
    let mut artifact_bytes = BTreeMap::new();
    let mut artifact_file_hashes = BTreeMap::new();
    for artifact in artifacts {
        let path = artifact.path().clone();
        if artifact_bytes
            .insert(path.clone(), artifact.bytes())
            .is_some()
        {
            return Err(PackageVerificationError::duplicate_certificate_artifact(
                "artifacts",
                path.as_str(),
            ));
        }
        artifact_file_hashes.insert(path, artifact.file_hash());
    }
    Ok((artifact_bytes, artifact_file_hashes))
}

#[derive(Debug, Default)]
struct PackageEntryCheckObservation {
    measurement_mode: PerformanceMeasurementMode,
    checker_reached: bool,
    decode_cache_counters: PackageVerificationDecodeCacheCounters,
    physical_certificate_decodes: u64,
    certificate_bytes: u64,
    declaration_count: u64,
    declaration_attempted: u64,
    declarations: Vec<PerformanceDeclarationMeasurement>,
    term_materialization: Option<CertificateTermMaterializationObservation>,
    certificate_payload: Option<CertificatePayloadObservation>,
    package_payload: Option<PackagePayloadOwnershipObservation>,
    prepared_artifact_reused: bool,
    owned_artifact_full_decodes: u64,
    certificate_file_hash_reused: bool,
}

impl PackageEntryCheckObservation {
    fn new(measurement_mode: PerformanceMeasurementMode) -> Self {
        let mut package_payload = measurement_mode
            .is_enabled()
            .then(PackagePayloadOwnershipObservation::default);
        if let Some(package_payload) = package_payload.as_mut() {
            package_payload.seed_decode_cache();
        }
        Self {
            measurement_mode,
            term_materialization: measurement_mode
                .is_enabled()
                .then(CertificateTermMaterializationObservation::default),
            certificate_payload: measurement_mode
                .is_enabled()
                .then(CertificatePayloadObservation::default),
            package_payload,
            ..Self::default()
        }
    }

    fn sample_decode_cache(&mut self) {
        if let Some(package_payload) = self.package_payload.as_mut() {
            package_payload.sample_decode_cache();
        }
    }

    fn observe_module_handle_clone(&mut self, logical_bytes: u64) {
        if let Some(package_payload) = self.package_payload.as_mut() {
            package_payload.observe_module_handle_clone(logical_bytes);
        }
    }

    fn observe_decode_cache_capacity_stop(&mut self) {
        if let Some(package_payload) = self.package_payload.as_mut() {
            package_payload.observe_decode_cache_capacity_stop();
        }
    }

    fn certificate_observation_sinks(&mut self) -> CertificateVerificationObservationSinks<'_> {
        let mut sinks = CertificateVerificationObservationSinks::new();
        if let Some(term) = self.term_materialization.as_mut() {
            sinks = sinks.with_term(term);
        }
        if let Some(payload) = self.certificate_payload.as_mut() {
            sinks = sinks.with_payload(payload);
        }
        sinks
    }

    fn observe_certificate_bytes(&mut self, bytes: &[u8]) {
        if self.measurement_mode.is_enabled() {
            self.checker_reached = true;
            self.certificate_bytes = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
        }
    }

    fn observe_fast_certificate(&mut self, module: &Name, certificate: &ModuleCert) {
        self.observe_certificate_parts(
            module,
            certificate.name_table(),
            certificate.term_table(),
            certificate.declarations(),
        );
    }

    fn observe_retained_certificate(
        &mut self,
        module: &Name,
        certificate: &RetainedDecodedModuleCert,
    ) {
        if !self.measurement_mode.is_enabled() {
            return;
        }
        let detail = if self.measurement_mode.is_detailed() {
            CertificateMeasurementDetail::Detailed
        } else {
            CertificateMeasurementDetail::Summary
        };
        self.observe_retained_measurement_summary(module, certificate.measurement_summary(detail));
    }

    fn observe_retained_measurement_summary(
        &mut self,
        module: &Name,
        summary: CertificateMeasurementSummary,
    ) {
        self.declaration_count = summary.declaration_count;
        self.declaration_attempted = summary.declaration_count;
        if !self.measurement_mode.is_detailed() {
            return;
        }
        self.declarations = summary
            .declarations
            .into_iter()
            .take(PERFORMANCE_DECLARATION_DETAIL_LIMIT)
            .map(|declaration| PerformanceDeclarationMeasurement {
                module: module.as_dotted(),
                declaration_index: declaration.declaration_index,
                declaration: declaration.declaration,
                term_nodes: declaration.term_nodes,
                elaboration_elapsed_ns: 0,
                kernel: None,
            })
            .collect();
    }

    fn observe_verified_module(&mut self, module: &Name, verified: &VerifiedModule) {
        self.observe_certificate_parts(
            module,
            verified.name_table(),
            verified.term_table(),
            verified.declarations(),
        );
    }

    fn observe_reference_declaration_count(&mut self, declaration_count: usize) {
        if !self.measurement_mode.is_enabled() {
            return;
        }
        self.declaration_count = u64::try_from(declaration_count).unwrap_or(u64::MAX);
    }

    fn observe_reference_certificate(
        &mut self,
        module: &Name,
        observation: &ReferenceCheckObservation,
    ) {
        if !self.measurement_mode.is_enabled() {
            return;
        }
        self.declaration_count = u64::try_from(observation.declaration_count).unwrap_or(u64::MAX);
        self.declaration_attempted = self.declaration_count;
        if !self.measurement_mode.is_detailed() {
            return;
        }
        self.declarations = observation
            .declarations
            .iter()
            .take(PERFORMANCE_DECLARATION_DETAIL_LIMIT)
            .map(|declaration| PerformanceDeclarationMeasurement {
                module: module.as_dotted(),
                declaration_index: u64::try_from(declaration.declaration_index).unwrap_or(u64::MAX),
                declaration: declaration.declaration.dotted(),
                term_nodes: u64::try_from(declaration.term_nodes).unwrap_or(u64::MAX),
                elaboration_elapsed_ns: 0,
                kernel: None,
            })
            .collect();
    }

    fn observe_certificate_parts(
        &mut self,
        module: &Name,
        name_table: &[Name],
        term_table: &[TermNode],
        declarations: &[DeclCert],
    ) {
        if !self.measurement_mode.is_enabled() {
            return;
        }
        self.declaration_count = u64::try_from(declarations.len()).unwrap_or(u64::MAX);
        self.declaration_attempted = self.declaration_count;
        if !self.measurement_mode.is_detailed() {
            return;
        }
        self.declarations = declarations
            .iter()
            .take(PERFORMANCE_DECLARATION_DETAIL_LIMIT)
            .enumerate()
            .map(
                |(declaration_index, declaration)| PerformanceDeclarationMeasurement {
                    module: module.as_dotted(),
                    declaration_index: u64::try_from(declaration_index).unwrap_or(u64::MAX),
                    declaration: certificate_declaration_name(
                        name_table,
                        declaration,
                        declaration_index,
                    ),
                    term_nodes: certificate_declaration_term_nodes(term_table, declaration),
                    elaboration_elapsed_ns: 0,
                    kernel: None,
                },
            )
            .collect();
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct PackageFastWorkerTiming {
    worker_index: usize,
    active_elapsed_ns: u64,
    idle_elapsed_ns: u64,
}

struct PackageFastWorkerDeclarationDetailCollector {
    limit: usize,
    retained: BTreeMap<(String, u64, String), PerformanceDeclarationMeasurement>,
}

impl PackageFastWorkerDeclarationDetailCollector {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            retained: BTreeMap::new(),
        }
    }

    fn record_observation(&mut self, observation: &mut PackageEntryCheckObservation) {
        self.record_details(observation.declarations.drain(..));
    }

    fn record_details(
        &mut self,
        declarations: impl IntoIterator<Item = PerformanceDeclarationMeasurement>,
    ) {
        for declaration in declarations {
            self.retained.insert(
                (
                    declaration.module.clone(),
                    declaration.declaration_index,
                    declaration.declaration.clone(),
                ),
                declaration,
            );
            while self.retained.len() > self.limit {
                self.retained.pop_last();
            }
        }
    }

    fn into_details(self) -> Vec<PerformanceDeclarationMeasurement> {
        self.retained.into_values().collect()
    }
}

struct PackageFastExecutionCostObservation {
    modules: BTreeMap<Name, PerformancePackageModuleShardingMeasurement>,
    critical_path_cost: u64,
    critical_path_module_count: u64,
    critical_path_identity: String,
    overflowed: bool,
}

struct PackageFastCriticalPathState {
    cost: u64,
    predecessor: Option<usize>,
    module: Name,
    depth: usize,
    jump_ancestors: Vec<Option<usize>>,
    overflowed: bool,
}

/// Verifier-local work counts collected only by tests and the explicit benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct PackageVerificationPlanningCounterSummary {
    complete_entry_fixed_point_scans: u64,
    verified_prefix_record_visits: u64,
    cumulative_verified_updates: u64,
    critical_path_state_nodes: u64,
    critical_path_equal_cost_comparisons: u64,
    critical_path_ancestor_steps: u64,
    path_prefix_clone_elements: u64,
    final_reconstructed_path_length: u64,
    overflowed: bool,
}

trait PackageVerificationPlanningCounterSink {
    fn verified_record_admitted(&mut self) {}
    fn critical_path_state_created(&mut self) {}
    fn critical_path_equal_cost_compared(&mut self) {}
    fn critical_path_ancestor_steps(&mut self, _count: usize) {}
    fn critical_path_reconstructed(&mut self, _length: usize) {}
}

impl PackageVerificationPlanningCounterSink for () {}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageVerificationPlanningCounterSummary {
    fn increment(value: &mut u64, overflowed: &mut bool) {
        let (next, overflow) = value.overflowing_add(1);
        *value = if overflow { u64::MAX } else { next };
        *overflowed |= overflow;
    }

    fn set_usize(value: &mut u64, input: usize, overflowed: &mut bool) {
        let converted = u64::try_from(input).unwrap_or(u64::MAX);
        *value = converted;
        *overflowed |= converted == u64::MAX && input != usize::MAX;
    }
}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageVerificationPlanningCounterSink for PackageVerificationPlanningCounterSummary {
    fn verified_record_admitted(&mut self) {
        Self::increment(&mut self.cumulative_verified_updates, &mut self.overflowed);
    }

    fn critical_path_state_created(&mut self) {
        Self::increment(&mut self.critical_path_state_nodes, &mut self.overflowed);
    }

    fn critical_path_equal_cost_compared(&mut self) {
        Self::increment(
            &mut self.critical_path_equal_cost_comparisons,
            &mut self.overflowed,
        );
    }

    fn critical_path_ancestor_steps(&mut self, count: usize) {
        let addend = u64::try_from(count).unwrap_or(u64::MAX);
        let (next, overflow) = self.critical_path_ancestor_steps.overflowing_add(addend);
        self.critical_path_ancestor_steps = if overflow { u64::MAX } else { next };
        self.overflowed |= overflow || addend == u64::MAX;
    }

    fn critical_path_reconstructed(&mut self, length: usize) {
        Self::set_usize(
            &mut self.final_reconstructed_path_length,
            length,
            &mut self.overflowed,
        );
    }
}

fn critical_path_modules(
    paths: &[Option<PackageFastCriticalPathState>],
    mut entry: usize,
) -> Vec<Name> {
    let mut modules = Vec::new();
    loop {
        let state = paths[entry]
            .as_ref()
            .expect("critical-path predecessor is already assigned");
        modules.push(state.module.clone());
        let Some(predecessor) = state.predecessor else {
            break;
        };
        entry = predecessor;
    }
    modules.reverse();
    modules
}

#[cfg(test)]
fn critical_path_state_cmp(
    paths: &[Option<PackageFastCriticalPathState>],
    left: usize,
    right: usize,
) -> std::cmp::Ordering {
    critical_path_state_cmp_with_sink(paths, left, right, &mut ())
}

fn critical_path_state_cmp_with_sink<S: PackageVerificationPlanningCounterSink>(
    paths: &[Option<PackageFastCriticalPathState>],
    left: usize,
    right: usize,
    counters: &mut S,
) -> std::cmp::Ordering {
    let left_state = paths[left].as_ref().expect("left path exists");
    let right_state = paths[right].as_ref().expect("right path exists");
    match left_state.cost.cmp(&right_state.cost) {
        std::cmp::Ordering::Equal => {
            counters.critical_path_equal_cost_compared();
            critical_path_lex_cmp_with_sink(paths, right, left, counters)
        }
        ordering => ordering,
    }
}

fn critical_path_ancestor_at_depth_with_sink<S: PackageVerificationPlanningCounterSink>(
    paths: &[Option<PackageFastCriticalPathState>],
    mut entry: usize,
    target_depth: usize,
    counters: &mut S,
) -> usize {
    let depth = paths[entry].as_ref().expect("path exists").depth;
    debug_assert!(target_depth >= 1 && target_depth <= depth);
    let mut distance = depth - target_depth;
    let mut bit = 0usize;
    let mut steps = 0usize;
    while distance != 0 {
        if distance & 1 == 1 {
            steps = steps.saturating_add(1);
            entry = paths[entry]
                .as_ref()
                .and_then(|state| state.jump_ancestors.get(bit).copied().flatten())
                .expect("requested critical-path ancestor exists");
        }
        distance >>= 1;
        bit += 1;
    }
    counters.critical_path_ancestor_steps(steps);
    entry
}

#[cfg(test)]
fn critical_path_lca(
    paths: &[Option<PackageFastCriticalPathState>],
    left: usize,
    right: usize,
) -> Option<usize> {
    critical_path_lca_with_sink(paths, left, right, &mut ())
}

fn critical_path_lca_with_sink<S: PackageVerificationPlanningCounterSink>(
    paths: &[Option<PackageFastCriticalPathState>],
    left: usize,
    right: usize,
    counters: &mut S,
) -> Option<usize> {
    let common_depth = paths[left]
        .as_ref()
        .expect("left path exists")
        .depth
        .min(paths[right].as_ref().expect("right path exists").depth);
    let mut left = critical_path_ancestor_at_depth_with_sink(paths, left, common_depth, counters);
    let mut right = critical_path_ancestor_at_depth_with_sink(paths, right, common_depth, counters);
    if left == right {
        return Some(left);
    }
    let max_jump = paths[left]
        .as_ref()
        .expect("left path exists")
        .jump_ancestors
        .len()
        .max(
            paths[right]
                .as_ref()
                .expect("right path exists")
                .jump_ancestors
                .len(),
        );
    for jump in (0..max_jump).rev() {
        let left_ancestor = paths[left]
            .as_ref()
            .and_then(|state| state.jump_ancestors.get(jump).copied().flatten());
        let right_ancestor = paths[right]
            .as_ref()
            .and_then(|state| state.jump_ancestors.get(jump).copied().flatten());
        if left_ancestor != right_ancestor {
            if let (Some(next_left), Some(next_right)) = (left_ancestor, right_ancestor) {
                counters.critical_path_ancestor_steps(2);
                left = next_left;
                right = next_right;
            }
        }
    }
    let left_parent = paths[left].as_ref().and_then(|state| state.predecessor);
    let right_parent = paths[right].as_ref().and_then(|state| state.predecessor);
    (left_parent == right_parent)
        .then_some(left_parent)
        .flatten()
}

fn critical_path_lex_cmp_with_sink<S: PackageVerificationPlanningCounterSink>(
    paths: &[Option<PackageFastCriticalPathState>],
    left: usize,
    right: usize,
    counters: &mut S,
) -> std::cmp::Ordering {
    if left == right {
        return std::cmp::Ordering::Equal;
    }
    let lca = critical_path_lca_with_sink(paths, left, right, counters);
    if lca == Some(left) {
        return std::cmp::Ordering::Less;
    }
    if lca == Some(right) {
        return std::cmp::Ordering::Greater;
    }
    let child_depth = lca
        .map(|entry| paths[entry].as_ref().expect("common path exists").depth + 1)
        .unwrap_or(1);
    let left_child = critical_path_ancestor_at_depth_with_sink(paths, left, child_depth, counters);
    let right_child =
        critical_path_ancestor_at_depth_with_sink(paths, right, child_depth, counters);
    paths[left_child]
        .as_ref()
        .expect("left child exists")
        .module
        .cmp(
            &paths[right_child]
                .as_ref()
                .expect("right child exists")
                .module,
        )
}

fn package_fast_execution_cost_observation(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
    execution_layers: &[Vec<Name>],
    planning: &PackageFastPlanningState,
) -> Option<PackageFastExecutionCostObservation> {
    package_fast_execution_cost_observation_with_sink(
        entries,
        graph,
        execution_modules,
        execution_layers,
        planning,
        &mut (),
    )
}

fn package_fast_execution_cost_observation_with_sink<S: PackageVerificationPlanningCounterSink>(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
    execution_layers: &[Vec<Name>],
    planning: &PackageFastPlanningState,
    counters: &mut S,
) -> Option<PackageFastExecutionCostObservation> {
    let entries_by_module = entries
        .iter()
        .map(|(entry_index, entry)| (entry.module.clone(), (*entry_index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let layer_by_module = execution_layers
        .iter()
        .enumerate()
        .flat_map(|(layer_index, layer)| {
            layer
                .iter()
                .cloned()
                .map(move |module| (module, layer_index))
        })
        .collect::<BTreeMap<_, _>>();
    let mut modules = BTreeMap::new();
    let mut paths = (0..entries.len())
        .map(|_| None)
        .collect::<Vec<Option<PackageFastCriticalPathState>>>();
    let mut overflowed = false;
    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, _entry) = entries_by_module.get(module).copied()?;
        let estimate = planning
            .module_cost_by_entry
            .get(entry_index)
            .copied()
            .flatten()?;
        overflowed |= estimate.overflowed;
        modules.insert(
            module.clone(),
            PerformancePackageModuleShardingMeasurement {
                cost_model: PerformancePackageShardCostModel::FastShardCostV1,
                artifact_bytes: estimate.artifact_bytes,
                direct_import_count: estimate.direct_import_count,
                estimated_cost: estimate.estimated_cost,
                layer_index: layer_by_module
                    .get(module)
                    .and_then(|index| u64::try_from(*index).ok()),
                shard_index: None,
                cost_overflowed: estimate.overflowed,
                critical_path: false,
            },
        );
        let mut best_prefix_entry = None;
        for import in graph.resolved_entry_imports[entry_index]
            .iter()
            .filter(|import| execution_modules.contains(&import.module))
        {
            best_prefix_entry = Some(match best_prefix_entry {
                None => import.entry_index,
                Some(current) => match critical_path_state_cmp_with_sink(
                    &paths,
                    current,
                    import.entry_index,
                    counters,
                ) {
                    std::cmp::Ordering::Greater => current,
                    _ => import.entry_index,
                },
            });
        }
        let prefix = best_prefix_entry.and_then(|entry| paths[entry].as_ref());
        let (cost, cost_overflowed) = saturating_add_u64(
            prefix.map_or(0, |state| state.cost),
            estimate.estimated_cost,
        );
        let path_overflowed =
            prefix.is_some_and(|state| state.overflowed) || estimate.overflowed || cost_overflowed;
        overflowed |= path_overflowed;
        let depth = prefix.map_or(1, |state| state.depth.saturating_add(1));
        let mut jump_ancestors = Vec::new();
        if let Some(predecessor) = best_prefix_entry {
            jump_ancestors.push(Some(predecessor));
            let mut jump = 1usize;
            while let Some(ancestor) = jump_ancestors[jump - 1] {
                let next = paths[ancestor]
                    .as_ref()
                    .and_then(|state| state.jump_ancestors.get(jump - 1).copied().flatten());
                let Some(next) = next else { break };
                jump_ancestors.push(Some(next));
                jump += 1;
            }
        }
        paths[entry_index] = Some(PackageFastCriticalPathState {
            cost,
            predecessor: best_prefix_entry,
            module: module.clone(),
            depth,
            jump_ancestors,
            overflowed: path_overflowed,
        });
        counters.critical_path_state_created();
    }
    let mut critical_entry = None;
    for (entry, state) in paths.iter().enumerate() {
        if state.is_none() {
            continue;
        }
        critical_entry = Some(match critical_entry {
            None => entry,
            Some(current) => {
                match critical_path_state_cmp_with_sink(&paths, current, entry, counters) {
                    std::cmp::Ordering::Greater => current,
                    _ => entry,
                }
            }
        });
    }
    let critical_modules = critical_entry
        .map(|entry| critical_path_modules(&paths, entry))
        .unwrap_or_default();
    counters.critical_path_reconstructed(critical_modules.len());
    for module in &critical_modules {
        if let Some(measurement) = modules.get_mut(module) {
            measurement.critical_path = true;
        }
    }
    let mut identity_bytes = Vec::new();
    identity_bytes.extend_from_slice(
        PerformancePackageShardCostModel::FastShardCostV1
            .as_str()
            .as_bytes(),
    );
    identity_bytes.push(0);
    for module in &critical_modules {
        let dotted = module.as_dotted();
        identity_bytes.extend_from_slice(
            &u64::try_from(dotted.len())
                .unwrap_or(u64::MAX)
                .to_be_bytes(),
        );
        identity_bytes.extend_from_slice(dotted.as_bytes());
        identity_bytes.extend_from_slice(
            &modules
                .get(module)
                .expect("critical path module has a cost measurement")
                .estimated_cost
                .to_be_bytes(),
        );
    }
    Some(PackageFastExecutionCostObservation {
        modules,
        critical_path_cost: critical_entry
            .and_then(|entry| paths[entry].as_ref())
            .map_or(0, |state| state.cost),
        critical_path_module_count: u64::try_from(critical_modules.len()).unwrap_or(u64::MAX),
        critical_path_identity: format_package_hash(&package_file_hash(&identity_bytes)),
        overflowed: overflowed
            || critical_entry
                .and_then(|entry| paths[entry].as_ref())
                .is_some_and(|state| state.overflowed),
    })
}

#[cfg(any(test, feature = "planning-benchmark"))]
#[derive(Clone)]
struct LegacyPackageFastCriticalPathState {
    cost: u64,
    modules: Vec<Name>,
    overflowed: bool,
}

/// Frozen pre-index critical-path implementation. Unlike the production
/// predecessor/jump representation, this intentionally retains and compares a
/// complete path vector for every selected entry.
#[cfg(any(test, feature = "planning-benchmark"))]
fn legacy_package_fast_execution_cost_vector_oracle(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
    execution_layers: &[Vec<Name>],
    planning: &PackageFastPlanningState,
) -> Option<PackageFastExecutionCostObservation> {
    let entries_by_module = entries
        .iter()
        .map(|(entry_index, entry)| (entry.module.clone(), (*entry_index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let layer_by_module = execution_layers
        .iter()
        .enumerate()
        .flat_map(|(layer_index, layer)| {
            layer
                .iter()
                .cloned()
                .map(move |module| (module, layer_index))
        })
        .collect::<BTreeMap<_, _>>();
    let mut modules = BTreeMap::new();
    let mut paths = BTreeMap::<Name, LegacyPackageFastCriticalPathState>::new();
    let mut overflowed = false;
    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, _entry) = entries_by_module.get(module).copied()?;
        let estimate = planning
            .module_cost_by_entry
            .get(entry_index)
            .copied()
            .flatten()?;
        overflowed |= estimate.overflowed;
        modules.insert(
            module.clone(),
            PerformancePackageModuleShardingMeasurement {
                cost_model: PerformancePackageShardCostModel::FastShardCostV1,
                artifact_bytes: estimate.artifact_bytes,
                direct_import_count: estimate.direct_import_count,
                estimated_cost: estimate.estimated_cost,
                layer_index: layer_by_module
                    .get(module)
                    .and_then(|index| u64::try_from(*index).ok()),
                shard_index: None,
                cost_overflowed: estimate.overflowed,
                critical_path: false,
            },
        );
        let mut best_prefix = graph.resolved_entry_imports[entry_index]
            .iter()
            .filter(|import| execution_modules.contains(&import.module))
            .filter_map(|import| paths.get(&import.module).cloned())
            .max_by(|left, right| {
                left.cost
                    .cmp(&right.cost)
                    .then_with(|| right.modules.cmp(&left.modules))
            })
            .unwrap_or(LegacyPackageFastCriticalPathState {
                cost: 0,
                modules: Vec::new(),
                overflowed: false,
            });
        let (cost, cost_overflowed) = saturating_add_u64(best_prefix.cost, estimate.estimated_cost);
        best_prefix.cost = cost;
        best_prefix.modules.push(module.clone());
        best_prefix.overflowed |= estimate.overflowed || cost_overflowed;
        overflowed |= best_prefix.overflowed;
        paths.insert(module.clone(), best_prefix);
    }
    let critical_path = paths
        .into_values()
        .max_by(|left, right| {
            left.cost
                .cmp(&right.cost)
                .then_with(|| right.modules.cmp(&left.modules))
        })
        .unwrap_or(LegacyPackageFastCriticalPathState {
            cost: 0,
            modules: Vec::new(),
            overflowed: false,
        });
    for module in &critical_path.modules {
        if let Some(measurement) = modules.get_mut(module) {
            measurement.critical_path = true;
        }
    }
    let mut identity_bytes = Vec::new();
    identity_bytes.extend_from_slice(
        PerformancePackageShardCostModel::FastShardCostV1
            .as_str()
            .as_bytes(),
    );
    identity_bytes.push(0);
    for module in &critical_path.modules {
        let dotted = module.as_dotted();
        identity_bytes.extend_from_slice(
            &u64::try_from(dotted.len())
                .unwrap_or(u64::MAX)
                .to_be_bytes(),
        );
        identity_bytes.extend_from_slice(dotted.as_bytes());
        identity_bytes.extend_from_slice(
            &modules
                .get(module)
                .expect("critical path module has a cost measurement")
                .estimated_cost
                .to_be_bytes(),
        );
    }
    Some(PackageFastExecutionCostObservation {
        modules,
        critical_path_cost: critical_path.cost,
        critical_path_module_count: u64::try_from(critical_path.modules.len()).unwrap_or(u64::MAX),
        critical_path_identity: format_package_hash(&package_file_hash(&identity_bytes)),
        overflowed: overflowed || critical_path.overflowed,
    })
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn package_fast_execution_cost_observations_match(
    actual: &PackageFastExecutionCostObservation,
    expected: &PackageFastExecutionCostObservation,
) -> bool {
    actual.modules == expected.modules
        && actual.critical_path_cost == expected.critical_path_cost
        && actual.critical_path_module_count == expected.critical_path_module_count
        && actual.critical_path_identity == expected.critical_path_identity
        && actual.overflowed == expected.overflowed
}

#[derive(Debug)]
struct PackageVerifierMeasurementState {
    mode: PerformanceMeasurementMode,
    modules_checked: u64,
    modules_decoded: u64,
    certificate_bytes: u64,
    declarations: u64,
    coarse_stage_clock_reads: u64,
    worker_active_elapsed_ns: u64,
    worker_idle_elapsed_ns: u64,
    coordinator_merge_elapsed_ns: u64,
    effective_jobs: usize,
    module_details: BTreeMap<String, PerformanceModuleMeasurement>,
    declaration_details: BTreeMap<(String, u64, String), PerformanceDeclarationMeasurement>,
    declaration_attempted: u64,
    workers: BTreeMap<usize, PerformanceWorkerMeasurement>,
    package_sharding: Option<PerformancePackageShardingMeasurement>,
    package_module_sharding: BTreeMap<Name, PerformancePackageModuleShardingMeasurement>,
    package_layers: BTreeMap<u64, PerformancePackageLayerMeasurement>,
    package_layer_attempted: u64,
    package_shards: BTreeMap<(u64, u64), PerformancePackageShardMeasurement>,
    package_shard_attempted: u64,
    package_shard_estimated_cost: u64,
    package_shard_elapsed_ns: u64,
    package_shard_modules: u64,
    package_shard_bytes: u64,
    package_max_layer_width: u64,
    package_avoided_base_context_clones: u64,
    package_avoided_base_context_clone_bytes: u64,
    package_estimate_overflowed: bool,
    term_materialization: CertificateTermMaterializationObservation,
    certificate_payload: CertificatePayloadObservation,
    package_payload: PackagePayloadOwnershipObservation,
}

impl PackageVerifierMeasurementState {
    fn new(mode: PerformanceMeasurementMode) -> Option<Self> {
        mode.is_enabled().then(|| {
            let mut package_payload = PackagePayloadOwnershipObservation::default();
            package_payload.seed_decode_cache();
            Self {
                mode,
                modules_checked: 0,
                modules_decoded: 0,
                certificate_bytes: 0,
                declarations: 0,
                coarse_stage_clock_reads: 0,
                worker_active_elapsed_ns: 0,
                worker_idle_elapsed_ns: 0,
                coordinator_merge_elapsed_ns: 0,
                effective_jobs: 0,
                module_details: BTreeMap::new(),
                declaration_details: BTreeMap::new(),
                declaration_attempted: 0,
                workers: BTreeMap::new(),
                package_sharding: None,
                package_module_sharding: BTreeMap::new(),
                package_layers: BTreeMap::new(),
                package_layer_attempted: 0,
                package_shards: BTreeMap::new(),
                package_shard_attempted: 0,
                package_shard_estimated_cost: 0,
                package_shard_elapsed_ns: 0,
                package_shard_modules: 0,
                package_shard_bytes: 0,
                package_max_layer_width: 0,
                package_avoided_base_context_clones: 0,
                package_avoided_base_context_clone_bytes: 0,
                package_estimate_overflowed: false,
                term_materialization: CertificateTermMaterializationObservation::default(),
                certificate_payload: CertificatePayloadObservation::default(),
                package_payload,
            }
        })
    }

    fn sample_decode_cache(&mut self) {
        self.package_payload.sample_decode_cache();
    }

    fn configure_fast_sharding(
        &mut self,
        requested_jobs: usize,
        observation: PackageFastExecutionCostObservation,
    ) {
        self.package_estimate_overflowed |= observation.overflowed;
        self.package_module_sharding = observation.modules;
        self.package_sharding = Some(PerformancePackageShardingMeasurement {
            cost_model: PerformancePackageShardCostModel::FastShardCostV1,
            memory_model: PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention,
            import_weight: PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1,
            memory_budget_bytes: PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
            fixed_worker_bytes: PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1,
            scratch_multiplier: PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1,
            requested_jobs: u64::try_from(requested_jobs).unwrap_or(u64::MAX),
            effective_jobs: 0,
            reduction_reason: PerformancePackageShardReductionReason::None,
            shared_base_context_bytes: 0,
            prepared_shared_bytes: 0,
            combined_shared_bytes: 0,
            per_worker_bytes: 0,
            term_materialization_bytes_per_worker:
                PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
            avoided_base_context_clone_bytes: 0,
            estimate_overflowed: observation.overflowed,
            critical_path_cost: observation.critical_path_cost,
            critical_path_module_count: observation.critical_path_module_count,
            critical_path_identity: observation.critical_path_identity,
            critical_path_checker_elapsed_ns: 0,
            barrier_elapsed_ns: 0,
        });
    }

    fn record_fast_layer(
        &mut self,
        layer_index: usize,
        runnable: &[(usize, &PackageLockEntry)],
        plan: &PackageFastShardPlan,
        layer_elapsed_ns: u64,
        results: &[PackageFastLayerWorkerResult<'_>],
    ) {
        self.effective_jobs = self.effective_jobs.max(plan.effective_jobs);
        self.package_max_layer_width = self
            .package_max_layer_width
            .max(u64::try_from(runnable.len()).unwrap_or(u64::MAX));
        self.package_estimate_overflowed |= plan.overflowed;
        let avoided_clones = u64::try_from(plan.effective_jobs).unwrap_or(u64::MAX);
        let (avoided_base_context_clones, avoided_clones_overflowed) =
            saturating_add_u64(self.package_avoided_base_context_clones, avoided_clones);
        self.package_avoided_base_context_clones = avoided_base_context_clones;
        let (avoided_clone_bytes, clone_bytes_overflowed) = plan.avoided_base_context_clone_bytes();
        let (avoided_base_context_clone_bytes, clone_sum_overflowed) = saturating_add_u64(
            self.package_avoided_base_context_clone_bytes,
            avoided_clone_bytes,
        );
        self.package_avoided_base_context_clone_bytes = avoided_base_context_clone_bytes;
        self.package_estimate_overflowed |=
            avoided_clones_overflowed || clone_bytes_overflowed || clone_sum_overflowed;
        let (barrier_elapsed_ns, barrier_elapsed_overflowed) = saturating_add_u64(
            self.package_sharding
                .as_ref()
                .map(|summary| summary.barrier_elapsed_ns)
                .unwrap_or(0),
            layer_elapsed_ns,
        );
        self.package_estimate_overflowed |= barrier_elapsed_overflowed;
        if let Some(summary) = self.package_sharding.as_mut() {
            summary.effective_jobs = summary
                .effective_jobs
                .max(u64::try_from(plan.effective_jobs).unwrap_or(u64::MAX));
            let reduction_reason = plan.reduction_reason.measurement();
            if reduction_reason > summary.reduction_reason {
                summary.reduction_reason = reduction_reason;
            }
            summary.shared_base_context_bytes = summary
                .shared_base_context_bytes
                .max(plan.shared_base_context_bytes);
            summary.prepared_shared_bytes = summary
                .prepared_shared_bytes
                .max(plan.prepared_shared_bytes);
            summary.combined_shared_bytes = summary
                .combined_shared_bytes
                .max(plan.combined_shared_bytes);
            summary.per_worker_bytes = summary.per_worker_bytes.max(plan.per_worker_bytes);
            summary.avoided_base_context_clone_bytes =
                self.package_avoided_base_context_clone_bytes;
            summary.estimate_overflowed |= plan.overflowed
                || avoided_clones_overflowed
                || clone_bytes_overflowed
                || clone_sum_overflowed
                || barrier_elapsed_overflowed;
            summary.barrier_elapsed_ns = barrier_elapsed_ns;
        }
        let layer_index_u64 = u64::try_from(layer_index).unwrap_or(u64::MAX);
        if self.mode.is_detailed() {
            self.package_layer_attempted = self.package_layer_attempted.saturating_add(1);
            self.package_layers.insert(
                layer_index_u64,
                PerformancePackageLayerMeasurement {
                    layer_index: layer_index_u64,
                    runnable_width: u64::try_from(runnable.len()).unwrap_or(u64::MAX),
                    estimated_total_cost: plan.estimated_total_cost,
                    estimated_max_shard_cost: plan.estimated_max_shard_cost(),
                    requested_jobs: u64::try_from(plan.requested_jobs).unwrap_or(u64::MAX),
                    effective_jobs: u64::try_from(plan.effective_jobs).unwrap_or(u64::MAX),
                    reduction_reason: plan.reduction_reason.measurement(),
                    shared_base_context_bytes: plan.shared_base_context_bytes,
                    prepared_shared_bytes: plan.prepared_shared_bytes,
                    combined_shared_bytes: plan.combined_shared_bytes,
                    per_worker_bytes: plan.per_worker_bytes,
                    term_materialization_bytes_per_worker:
                        PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
                    memory_budget_bytes: PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
                    estimate_overflowed: plan.overflowed,
                    elapsed_ns: layer_elapsed_ns,
                },
            );
            while self.package_layers.len() > PERFORMANCE_MODULE_DETAIL_LIMIT {
                self.package_layers.pop_last();
            }
        }
        for (shard_index, shard) in plan.shards.iter().enumerate() {
            let active_elapsed_ns = results
                .iter()
                .filter(|result| result.worker_index() == shard_index)
                .filter_map(PackageFastLayerWorkerResult::worker_timing)
                .map(|timing| timing.active_elapsed_ns)
                .next()
                .unwrap_or(0);
            let (shard_estimated_cost, shard_cost_overflowed) =
                saturating_add_u64(self.package_shard_estimated_cost, shard.estimated_cost);
            self.package_shard_estimated_cost = shard_estimated_cost;
            let (shard_elapsed_ns, shard_elapsed_overflowed) =
                saturating_add_u64(self.package_shard_elapsed_ns, active_elapsed_ns);
            self.package_shard_elapsed_ns = shard_elapsed_ns;
            let (shard_modules, shard_modules_overflowed) = saturating_add_u64(
                self.package_shard_modules,
                u64::try_from(shard.member_indexes.len()).unwrap_or(u64::MAX),
            );
            self.package_shard_modules = shard_modules;
            let (shard_bytes, shard_bytes_overflowed) =
                saturating_add_u64(self.package_shard_bytes, shard.artifact_bytes);
            self.package_shard_bytes = shard_bytes;
            self.package_estimate_overflowed |= shard.overflowed
                || shard_cost_overflowed
                || shard_elapsed_overflowed
                || shard_modules_overflowed
                || shard_bytes_overflowed;
            let shard_index_u64 = u64::try_from(shard_index).unwrap_or(u64::MAX);
            for member_index in &shard.member_indexes {
                let entry = runnable[*member_index].1;
                if let Some(module) = self.package_module_sharding.get_mut(&entry.module) {
                    module.layer_index = Some(layer_index_u64);
                    module.shard_index = Some(shard_index_u64);
                }
            }
            if self.mode.is_detailed() {
                self.package_shard_attempted = self.package_shard_attempted.saturating_add(1);
                self.package_shards.insert(
                    (layer_index_u64, shard_index_u64),
                    PerformancePackageShardMeasurement {
                        layer_index: layer_index_u64,
                        shard_index: shard_index_u64,
                        estimated_cost: shard.estimated_cost,
                        artifact_bytes: shard.artifact_bytes,
                        member_count: u64::try_from(shard.member_indexes.len()).unwrap_or(u64::MAX),
                        active_elapsed_ns,
                        estimate_overflowed: shard.overflowed,
                    },
                );
                while self.package_shards.len() > PERFORMANCE_WORKER_DETAIL_LIMIT {
                    self.package_shards.pop_last();
                }
            }
        }
    }

    fn record_module(
        &mut self,
        entry: &PackageLockEntry,
        observation: &PackageEntryCheckObservation,
        checker_elapsed_ns: u64,
        worker_index: Option<usize>,
        checker_reached: bool,
    ) {
        if checker_reached {
            self.modules_checked = self.modules_checked.saturating_add(1);
        }
        if worker_index.is_some() {
            self.coarse_stage_clock_reads = self.coarse_stage_clock_reads.saturating_add(1);
        }
        self.modules_decoded = self
            .modules_decoded
            .saturating_add(observation.physical_certificate_decodes);
        self.certificate_bytes = self
            .certificate_bytes
            .saturating_add(observation.certificate_bytes);
        self.declarations = self
            .declarations
            .saturating_add(observation.declaration_count);
        if let Some(term_materialization) = observation.term_materialization {
            self.term_materialization.merge(term_materialization);
        }
        if let Some(certificate_payload) = observation.certificate_payload {
            self.certificate_payload.merge(certificate_payload);
        }
        if let Some(package_payload) = observation.package_payload {
            self.package_payload.merge_worker(package_payload);
        }
        let module = entry.module.as_dotted();
        if self.mode.is_detailed() {
            let package_sharding = self.package_module_sharding.get(&entry.module).cloned();
            self.module_details.insert(
                module.clone(),
                PerformanceModuleMeasurement {
                    module: module.clone(),
                    certificate_bytes: observation.certificate_bytes,
                    declaration_count: observation.declaration_count,
                    import_count: u64::try_from(entry.imports.len()).unwrap_or(u64::MAX),
                    checker_elapsed_ns,
                    package_sharding,
                },
            );
            while self.module_details.len() > PERFORMANCE_MODULE_DETAIL_LIMIT {
                self.module_details.pop_last();
            }
            self.declaration_attempted = self
                .declaration_attempted
                .saturating_add(observation.declaration_attempted);
            for declaration in &observation.declarations {
                self.record_declaration_detail(declaration.clone());
            }
        }
        if self
            .package_module_sharding
            .get(&entry.module)
            .is_some_and(|module| module.critical_path)
        {
            let current_elapsed_ns = self
                .package_sharding
                .as_ref()
                .map(|summary| summary.critical_path_checker_elapsed_ns)
                .unwrap_or(0);
            let (critical_path_checker_elapsed_ns, overflowed) =
                saturating_add_u64(current_elapsed_ns, checker_elapsed_ns);
            self.package_estimate_overflowed |= overflowed;
            if let Some(summary) = self.package_sharding.as_mut() {
                summary.critical_path_checker_elapsed_ns = critical_path_checker_elapsed_ns;
                summary.estimate_overflowed |= overflowed;
            }
        }
        if let Some(worker_index) = worker_index {
            self.effective_jobs = self.effective_jobs.max(worker_index.saturating_add(1));
            if self.mode.is_detailed() {
                let worker = self.workers.entry(worker_index).or_insert_with(|| {
                    PerformanceWorkerMeasurement {
                        worker_index: u64::try_from(worker_index).unwrap_or(u64::MAX),
                        module_count: 0,
                        certificate_bytes: 0,
                        active_elapsed_ns: 0,
                        idle_elapsed_ns: 0,
                    }
                });
                worker.module_count = worker.module_count.saturating_add(1);
                worker.certificate_bytes = worker
                    .certificate_bytes
                    .saturating_add(observation.certificate_bytes);
                while self.workers.len() > PERFORMANCE_WORKER_DETAIL_LIMIT {
                    self.workers.pop_last();
                }
            }
        }
    }

    fn record_declaration_details(&mut self, declarations: Vec<PerformanceDeclarationMeasurement>) {
        if !self.mode.is_detailed() {
            return;
        }
        for declaration in declarations {
            self.record_declaration_detail(declaration);
        }
    }

    fn record_declaration_detail(&mut self, declaration: PerformanceDeclarationMeasurement) {
        self.declaration_details.insert(
            (
                declaration.module.clone(),
                declaration.declaration_index,
                declaration.declaration.clone(),
            ),
            declaration,
        );
        while self.declaration_details.len() > PERFORMANCE_DECLARATION_DETAIL_LIMIT {
            self.declaration_details.pop_last();
        }
    }

    fn record_worker_timing(&mut self, timing: PackageFastWorkerTiming, clock_read: bool) {
        self.effective_jobs = self
            .effective_jobs
            .max(timing.worker_index.saturating_add(1));
        self.worker_active_elapsed_ns = self
            .worker_active_elapsed_ns
            .saturating_add(timing.active_elapsed_ns);
        self.worker_idle_elapsed_ns = self
            .worker_idle_elapsed_ns
            .saturating_add(timing.idle_elapsed_ns);
        if clock_read {
            self.coarse_stage_clock_reads = self.coarse_stage_clock_reads.saturating_add(1);
        }
        if let Some(worker) = self.workers.get_mut(&timing.worker_index) {
            worker.active_elapsed_ns = worker
                .active_elapsed_ns
                .saturating_add(timing.active_elapsed_ns);
            worker.idle_elapsed_ns = worker
                .idle_elapsed_ns
                .saturating_add(timing.idle_elapsed_ns);
        }
    }

    fn record_layer_clock(&mut self) {
        self.coarse_stage_clock_reads = self.coarse_stage_clock_reads.saturating_add(1);
    }

    fn record_coordinator_merge(&mut self, elapsed_ns: u64) {
        self.coordinator_merge_elapsed_ns =
            self.coordinator_merge_elapsed_ns.saturating_add(elapsed_ns);
        self.coarse_stage_clock_reads = self.coarse_stage_clock_reads.saturating_add(1);
    }
}

struct PackageMeasurementReportInput<'input, 'bytes> {
    options: &'input PackageVerificationExecutionOptions,
    lock: &'input PackageLockManifest,
    entries: &'input [(usize, &'input PackageLockEntry)],
    artifact_bytes: Option<&'input BTreeMap<PackagePath, &'bytes [u8]>>,
    modules: &'input [PackageModuleVerificationResult],
    measurements: Option<&'input PackageVerifierMeasurementState>,
    memo_counters: PackageVerificationMemoCounters,
    decode_cache_counters: PackageVerificationDecodeCacheCounters,
}

fn package_measurement_report(
    input: PackageMeasurementReportInput<'_, '_>,
) -> Option<PerformanceMeasurementReport> {
    let PackageMeasurementReportInput {
        options,
        lock,
        entries,
        artifact_bytes,
        modules,
        measurements,
        memo_counters,
        decode_cache_counters,
    } = input;
    let measurements = measurements?;
    let mut recorder = PerformanceMeasurementRecorder::new(options.measurement_mode);
    if let Ok(canonical_lock) = lock.canonical_json() {
        recorder = recorder.with_input_identity(format_package_hash(&package_file_hash(
            canonical_lock.as_bytes(),
        )));
    }
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageRequestedJobs,
        u64::try_from(options.jobs).unwrap_or(u64::MAX),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageEffectiveJobs,
        u64::try_from(measurements.effective_jobs).unwrap_or(u64::MAX),
    );
    recorder.observe_coarse_stage_clock_reads(measurements.coarse_stage_clock_reads);
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageWorkerActiveElapsed,
        measurements.worker_active_elapsed_ns,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageWorkerIdleElapsed,
        measurements.worker_idle_elapsed_ns,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageCoordinatorMergeElapsed,
        measurements.coordinator_merge_elapsed_ns,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageSharedBaseContextBytes,
        measurements
            .package_sharding
            .as_ref()
            .map(|summary| summary.shared_base_context_bytes)
            .unwrap_or(0),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageAvoidedBaseContextClones,
        measurements.package_avoided_base_context_clones,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageAvoidedBaseContextCloneBytes,
        measurements.package_avoided_base_context_clone_bytes,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageShardEstimatedCost,
        measurements.package_shard_estimated_cost,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageShardElapsed,
        measurements.package_shard_elapsed_ns,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageShardModules,
        measurements.package_shard_modules,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageShardBytes,
        measurements.package_shard_bytes,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDagCriticalPathLayers,
        measurements
            .package_sharding
            .as_ref()
            .map(|summary| summary.critical_path_module_count)
            .unwrap_or(0),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDagLayerWidth,
        measurements.package_max_layer_width,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDagLayerElapsed,
        measurements
            .package_sharding
            .as_ref()
            .map(|summary| summary.barrier_elapsed_ns)
            .unwrap_or(0),
    );
    recorder.observe_certificate_term_materialization(&measurements.term_materialization);
    recorder.observe_certificate_payload_ownership(
        &measurements.certificate_payload,
        &measurements.package_payload,
    );
    if measurements.package_estimate_overflowed {
        recorder.mark_overflowed();
    }

    let non_skipped_results = modules
        .iter()
        .filter(|module| module.status != PackageModuleVerificationStatus::Skipped)
        .count();
    let cache_results = modules
        .iter()
        .filter(|module| {
            matches!(
                module.evidence,
                PackageModuleVerificationEvidence::LocalAuditCache
                    | PackageModuleVerificationEvidence::ReferenceSummaryCache
            )
        })
        .count();
    let disk_memo_results = modules
        .iter()
        .filter(|module| module.evidence == PackageModuleVerificationEvidence::DiskVerifierMemo)
        .count();
    let memo_results = disk_memo_results.saturating_add(memo_counters.hits);
    let live_results = non_skipped_results
        .saturating_sub(cache_results)
        .saturating_sub(memo_results);
    for (label, count) in [
        (
            PerformanceMeasurementLabel::PackageLiveResults,
            live_results,
        ),
        (
            PerformanceMeasurementLabel::PackageCacheResults,
            cache_results,
        ),
        (
            PerformanceMeasurementLabel::PackageMemoResults,
            memo_results,
        ),
        (
            PerformanceMeasurementLabel::PackageModulesChecked,
            usize::try_from(measurements.modules_checked).unwrap_or(usize::MAX),
        ),
    ] {
        recorder.add_counter(label, u64::try_from(count).unwrap_or(u64::MAX));
    }

    let entries_by_module = entries
        .iter()
        .map(|(_, entry)| (&entry.module, *entry))
        .collect::<BTreeMap<_, _>>();
    let mut observed_certificate_bytes = 0u64;
    let mut observed_imports = 0u64;
    for result in modules {
        let Some(entry) = entries_by_module.get(&result.module).copied() else {
            continue;
        };
        let observed = measurements.module_details.get(&result.module.as_dotted());
        let certificate_bytes = observed
            .map(|module| module.certificate_bytes)
            .or_else(|| {
                artifact_bytes
                    .and_then(|artifacts| artifacts.get(&entry.certificate).copied())
                    .map(|bytes| u64::try_from(bytes.len()).unwrap_or(u64::MAX))
            })
            .unwrap_or(0);
        let declaration_count = observed.map(|module| module.declaration_count).unwrap_or(0);
        let import_count = u64::try_from(entry.imports.len()).unwrap_or(u64::MAX);
        observed_certificate_bytes = observed_certificate_bytes.saturating_add(certificate_bytes);
        observed_imports = observed_imports.saturating_add(import_count);
        recorder.record_module(PerformanceModuleMeasurement {
            module: result.module.as_dotted(),
            certificate_bytes,
            declaration_count,
            import_count,
            checker_elapsed_ns: observed
                .map(|module| module.checker_elapsed_ns)
                .unwrap_or(0),
            package_sharding: observed
                .and_then(|module| module.package_sharding.clone())
                .or_else(|| {
                    measurements
                        .package_module_sharding
                        .get(&result.module)
                        .cloned()
                }),
        });
    }
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageCertificateBytes,
        if artifact_bytes.is_some() {
            observed_certificate_bytes
        } else {
            measurements.certificate_bytes
        },
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDeclarations,
        measurements.declarations,
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageImports,
        observed_imports,
    );
    for declaration in measurements.declaration_details.values() {
        recorder.record_declaration(declaration.clone());
    }
    recorder.observe_declaration_attempts(
        measurements.declaration_attempted.saturating_sub(
            u64::try_from(measurements.declaration_details.len()).unwrap_or(u64::MAX),
        ),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDecodeCacheHits,
        u64::try_from(
            decode_cache_counters
                .certificate_hits
                .saturating_add(decode_cache_counters.import_context_hits)
                .saturating_add(decode_cache_counters.import_context_disk_hits),
        )
        .unwrap_or(u64::MAX),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageDecodeCacheMisses,
        u64::try_from(
            decode_cache_counters
                .certificate_misses
                .saturating_add(decode_cache_counters.import_context_misses)
                .saturating_add(decode_cache_counters.import_context_disk_misses)
                .saturating_add(decode_cache_counters.import_context_disk_stale)
                .saturating_add(decode_cache_counters.import_context_disk_schema_misses),
        )
        .unwrap_or(u64::MAX),
    );
    recorder.add_counter(
        PerformanceMeasurementLabel::PackageModulesDecoded,
        measurements.modules_decoded,
    );
    for worker in measurements.workers.values() {
        recorder.record_worker(worker.clone());
    }
    recorder.observe_worker_attempts(
        u64::try_from(
            measurements
                .effective_jobs
                .saturating_sub(measurements.workers.len()),
        )
        .unwrap_or(u64::MAX),
    );
    if let Some(package_sharding) = &measurements.package_sharding {
        let mut package_sharding = package_sharding.clone();
        package_sharding.estimate_overflowed |= measurements.package_estimate_overflowed;
        recorder.set_package_sharding(package_sharding);
    }
    for layer in measurements.package_layers.values() {
        recorder.record_package_layer(layer.clone());
    }
    recorder.observe_package_layer_attempts(
        measurements
            .package_layer_attempted
            .saturating_sub(u64::try_from(measurements.package_layers.len()).unwrap_or(u64::MAX)),
    );
    for shard in measurements.package_shards.values() {
        recorder.record_package_shard(shard.clone());
    }
    recorder.observe_package_shard_attempts(
        measurements
            .package_shard_attempted
            .saturating_sub(u64::try_from(measurements.package_shards.len()).unwrap_or(u64::MAX)),
    );
    recorder.report()
}

fn certificate_declaration_name(
    name_table: &[Name],
    declaration: &DeclCert,
    declaration_index: usize,
) -> String {
    let name = match &declaration.decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    name_table
        .get(name)
        .map(Name::as_dotted)
        .unwrap_or_else(|| format!("declaration[{declaration_index}]"))
}

fn certificate_declaration_term_nodes(term_table: &[TermNode], declaration: &DeclCert) -> u64 {
    let mut pending = declaration_term_roots(&declaration.decl);
    let mut visited = BTreeSet::new();
    while let Some(term_id) = pending.pop() {
        if !visited.insert(term_id) {
            continue;
        }
        let Some(node) = term_table.get(term_id) else {
            continue;
        };
        match node {
            TermNode::App(function, argument) => {
                pending.push(*function);
                pending.push(*argument);
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                pending.push(*ty);
                pending.push(*body);
            }
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
        }
    }
    u64::try_from(visited.len()).unwrap_or(u64::MAX)
}

fn declaration_term_roots(declaration: &DeclPayload) -> Vec<usize> {
    match declaration {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => vec![*ty],
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            vec![*ty, *value]
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => vec![*ty, *proof],
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => params
            .iter()
            .chain(indices)
            .map(|binder| binder.ty)
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .chain(&inductive.indices)
                    .map(|binder| binder.ty)
                    .chain(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    )
                    .chain(inductive.recursor.iter().map(|recursor| recursor.ty))
            })
            .collect(),
    }
}

fn elapsed_nanos_if_started(started: Option<Instant>) -> u64 {
    started
        .map(|started| u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX))
        .unwrap_or(0)
}

fn indexed_lock_graph_verification_error(
    error: IndexedPackageLockGraphError,
) -> PackageVerificationError {
    match error {
        IndexedPackageLockGraphError::Lock(error) => {
            PackageVerificationError::lock_graph_invalid(format!("{error:?}"))
        }
        IndexedPackageLockGraphError::InternalInvariant(error) => {
            PackageVerificationError::lock_graph_invalid(format!(
                "internal_index_invariant:{}",
                error.invariant()
            ))
        }
    }
}

fn read_certificate_artifact_from_root(
    package_root: Option<&PackageCertificateRootReader>,
    entry_index: usize,
    entry: &PackageLockEntry,
) -> PackageVerificationResult<Vec<u8>> {
    package_root
        .and_then(|root| root.read(&entry.certificate).ok())
        .ok_or_else(|| {
            PackageVerificationError::certificate_artifact_missing(
                format!("entries[{entry_index}].certificate"),
                entry.certificate.as_str(),
            )
        })
}

/// Retained package-root capability for lazy certificate verification.
///
/// Each component is opened relative to the preceding live descriptor with
/// `O_NOFOLLOW`; the final regular file is bounded before and during the read.
#[cfg(unix)]
struct PackageCertificateRootReader {
    root: fs::File,
}

#[cfg(unix)]
impl PackageCertificateRootReader {
    fn open(path: &Path) -> io::Result<Self> {
        use std::{
            ffi::{CString, OsStr, OsString},
            os::{fd::FromRawFd, unix::ffi::OsStrExt},
            path::Component,
        };

        let mut normalized = Vec::<OsString>::new();
        let absolute = path.is_absolute();
        let start = if absolute { "/" } else { "." };
        for component in path.components() {
            match component {
                Component::RootDir | Component::CurDir => {}
                Component::Normal(value) => normalized.push(value.to_owned()),
                Component::ParentDir => {
                    if !absolute
                        && normalized
                            .last()
                            .is_none_or(|value| value.as_os_str() == OsStr::new(".."))
                    {
                        normalized.push(OsString::from(".."));
                    } else if normalized.pop().is_none() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            "package root escapes its retained starting directory",
                        ));
                    }
                }
                Component::Prefix(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "unsupported package-root prefix",
                    ));
                }
            }
        }
        // macOS exposes `/var` and `/tmp` as fixed compatibility symlinks
        // into `/private`. Rewrite only those operating-system aliases before
        // the no-follow walk; every package-controlled component still opens
        // descriptor-relative with `O_NOFOLLOW`.
        if cfg!(target_os = "macos")
            && path.is_absolute()
            && normalized.first().is_some_and(|component| {
                component == OsStr::new("var") || component == OsStr::new("tmp")
            })
        {
            normalized.insert(0, OsString::from("private"));
        }
        let start = CString::new(start).expect("filesystem start has no NUL");
        // SAFETY: the constant pathname is NUL terminated. A successful
        // descriptor is transferred to `File` exactly once.
        let descriptor = unsafe {
            libc::open(
                start.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the descriptor is freshly owned.
        let mut directory = unsafe { fs::File::from_raw_fd(descriptor) };
        for component in normalized {
            let component = CString::new(component.as_bytes()).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidInput, "package root contains NUL")
            })?;
            use std::os::fd::{AsRawFd, FromRawFd as _};
            // SAFETY: parent descriptor and component are live and valid.
            let descriptor = unsafe {
                libc::openat(
                    directory.as_raw_fd(),
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            };
            if descriptor < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: the descriptor is freshly owned.
            directory = unsafe { fs::File::from_raw_fd(descriptor) };
        }
        Ok(Self { root: directory })
    }

    fn read(&self, path: &PackagePath) -> io::Result<Vec<u8>> {
        use std::{
            ffi::CString,
            os::{
                fd::{AsRawFd, FromRawFd},
                unix::ffi::OsStrExt,
            },
            path::Component,
        };

        validate_package_path(path, "package_certificate.path")
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid package path"))?;
        let mut components = Path::new(path.as_str()).components().peekable();
        let mut directory = self.root.try_clone()?;
        while let Some(component) = components.next() {
            let Component::Normal(component) = component else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "invalid package path component",
                ));
            };
            let component = CString::new(component.as_bytes()).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidInput, "package path contains NUL")
            })?;
            if components.peek().is_some() {
                // SAFETY: parent descriptor and component are live and valid.
                let descriptor = unsafe {
                    libc::openat(
                        directory.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly owned.
                directory = unsafe { fs::File::from_raw_fd(descriptor) };
                continue;
            }

            // O_NONBLOCK prevents a hostile FIFO from blocking before fstat.
            // SAFETY: parent descriptor and component are live and valid.
            let descriptor = unsafe {
                libc::openat(
                    directory.as_raw_fd(),
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                )
            };
            if descriptor < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: descriptor is freshly owned.
            let mut file = unsafe { fs::File::from_raw_fd(descriptor) };
            let metadata = file.metadata()?;
            let limit = npa_cert::MAX_CERTIFICATE_BYTES as u64;
            if !metadata.file_type().is_file() || metadata.len() > limit {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "package certificate is not a bounded regular file",
                ));
            }
            let mut bytes =
                Vec::with_capacity(usize::try_from(metadata.len()).unwrap_or(0).min(1_048_576));
            std::io::Read::by_ref(&mut file)
                .take(limit + 1)
                .read_to_end(&mut bytes)?;
            if bytes.len() as u64 > limit {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "package certificate exceeds its byte limit",
                ));
            }
            return Ok(bytes);
        }
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "package certificate path is empty",
        ))
    }
}

#[cfg(not(unix))]
struct PackageCertificateRootReader;

#[cfg(not(unix))]
impl PackageCertificateRootReader {
    fn open(_path: &Path) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "descriptor-relative package certificate reads require Unix",
        ))
    }

    fn read(&self, _path: &PackagePath) -> io::Result<Vec<u8>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "descriptor-relative package certificate reads require Unix",
        ))
    }
}

fn canonical_lock_entries(lock: &PackageLockManifest) -> Vec<(usize, &PackageLockEntry)> {
    let mut entries = lock.entries.iter().collect::<Vec<_>>();
    entries.sort_by(|left, right| left.module.cmp(&right.module));
    entries.into_iter().enumerate().collect()
}

fn validate_execution_options(
    options: &PackageVerificationExecutionOptions,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<()> {
    if options.jobs == 0 {
        return Err(PackageVerificationError::invalid_job_count(options.jobs));
    }
    if options.jobs > 1 && mode == PackageVerificationMode::Reference {
        return Err(PackageVerificationError::unsupported_parallel_checker(
            mode,
            options.jobs,
        ));
    }
    Ok(())
}

fn empty_package_verification_report(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
    options: &PackageVerificationExecutionOptions,
    mode: PackageVerificationMode,
) -> PackageVerificationReport {
    let verdict_source = match mode {
        PackageVerificationMode::FastKernel => {
            PackageVerificationVerdictSource::FastKernelCertificateVerifier
        }
        PackageVerificationMode::Reference => PackageVerificationVerdictSource::ReferenceChecker,
    };
    let memo_counters = PackageVerificationMemoCounters::default();
    let decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);
    let measurements = package_measurement_report(PackageMeasurementReportInput {
        options,
        lock,
        entries,
        artifact_bytes: None,
        modules: &[],
        measurements: measurement_state.as_ref(),
        memo_counters,
        decode_cache_counters,
    });
    PackageVerificationReport {
        mode,
        axiom_policy_hash: package_verification_policy_hash(validated, mode),
        verdict_source,
        reference_checker_verdict: verdict_source.is_reference_checker_verdict(),
        locally_accelerated: false,
        status: PackageVerificationStatus::Passed,
        topological_order: Vec::new(),
        modules: Vec::new(),
        memo_counters,
        decode_cache_counters: options
            .collect_decode_cache_counters
            .then_some(decode_cache_counters),
        measurements,
    }
}

fn package_verification_decode_cache() -> &'static Mutex<PackageVerificationDecodeCache> {
    PACKAGE_VERIFICATION_DECODE_CACHE
        .get_or_init(|| Mutex::new(PackageVerificationDecodeCache::default()))
}

#[derive(Clone, Debug)]
struct PackageVerificationDecodeCacheConfig {
    checker_mode: PackageVerificationMode,
    package_certificate_profile: String,
    package_core_profile: String,
    enabled_core_features: Vec<String>,
    checker_policy_hash: PackageHash,
    process_local_cache: bool,
    persistent_import_context_export_cache: bool,
}

impl PackageVerificationDecodeCacheConfig {
    fn for_mode(validated: &ValidatedPackageManifest, mode: PackageVerificationMode) -> Self {
        let manifest = validated.manifest();
        Self {
            checker_mode: mode,
            package_certificate_profile: manifest.certificate_format.clone(),
            package_core_profile: manifest.core_spec.clone(),
            enabled_core_features: package_verification_enabled_core_features(validated, mode),
            checker_policy_hash: package_verification_policy_hash(validated, mode),
            process_local_cache: false,
            persistent_import_context_export_cache: false,
        }
    }

    fn with_process_local_cache(mut self, enabled: bool) -> Self {
        self.process_local_cache = enabled;
        self
    }

    fn with_persistent_import_context_export_cache(mut self, enabled: bool) -> Self {
        self.persistent_import_context_export_cache = enabled;
        self
    }
}

#[cfg(test)]
struct PackageDecodeCacheLookup<T> {
    value: T,
    counters: PackageVerificationDecodeCacheCounters,
}

#[derive(Clone, Copy)]
struct PackageReferenceImportContext<'a> {
    lock: &'a PackageLockManifest,
    entries: &'a [(usize, &'a PackageLockEntry)],
    checked_by_module: &'a BTreeMap<Name, ReferenceCheckedModule>,
    owner_header: &'a CertHeader,
    config: &'a PackageVerificationDecodeCacheConfig,
}

fn decode_fast_certificate_with_cache(
    entry_index: usize,
    entry: &PackageLockEntry,
    bytes: &[u8],
    actual_file_hash: PackageHash,
    config: &PackageVerificationDecodeCacheConfig,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<ModuleCert> {
    if !config.process_local_cache {
        let cert = decode_module_cert_observed(bytes, observation.certificate_payload.as_mut())
            .map_err(|source| {
                PackageVerificationError::certificate_decode_failed(
                    format!("entries[{entry_index}].certificate"),
                    format!("{source:?}"),
                )
            })?;
        if observation.measurement_mode.is_enabled() {
            observation.physical_certificate_decodes =
                observation.physical_certificate_decodes.saturating_add(1);
        }
        return Ok(cert);
    }

    let header = decode_module_cert_header(bytes).map_err(|source| {
        PackageVerificationError::certificate_decode_failed(
            format!("entries[{entry_index}].certificate"),
            format!("{source:?}"),
        )
    })?;
    let key = package_decode_cache_certificate_key(entry, actual_file_hash, &header, config);
    let cached_cert = package_fast_decode_cache_lookup(package_verification_decode_cache(), &key);
    if let Some(cert) = cached_cert {
        observation.observe_module_handle_clone(cert.logical_retained_bytes_v1());
        observation.decode_cache_counters.certificate_hits = observation
            .decode_cache_counters
            .certificate_hits
            .saturating_add(1);
        observation.sample_decode_cache();
        return Ok(cert);
    }

    observation.decode_cache_counters.certificate_misses = observation
        .decode_cache_counters
        .certificate_misses
        .saturating_add(1);
    let cert = decode_module_cert_observed(bytes, observation.certificate_payload.as_mut())
        .map_err(|source| {
            PackageVerificationError::certificate_decode_failed(
                format!("entries[{entry_index}].certificate"),
                format!("{source:?}"),
            )
        })?;
    if observation.measurement_mode.is_enabled() {
        observation.physical_certificate_decodes =
            observation.physical_certificate_decodes.saturating_add(1);
    }
    observation.observe_module_handle_clone(cert.logical_retained_bytes_v1());
    let inserted = {
        let mut cache = lock_package_verification_decode_cache(package_verification_decode_cache());
        cache.insert_fast(key, cert.clone())
    };
    if inserted {
        observation.decode_cache_counters.certificate_inserted = observation
            .decode_cache_counters
            .certificate_inserted
            .saturating_add(1);
    } else {
        observation.decode_cache_counters.certificate_capacity_stops = observation
            .decode_cache_counters
            .certificate_capacity_stops
            .saturating_add(1);
        observation.observe_decode_cache_capacity_stop();
    }
    observation.sample_decode_cache();
    Ok(cert)
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn reference_import_store_with_cache(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
    owner_header: &CertHeader,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<PackageDecodeCacheLookup<Arc<ReferenceImportStore>>> {
    let mut counters = PackageVerificationDecodeCacheCounters::default();
    let value = reference_import_store_with_cache_observed(
        entry_index,
        entry,
        resolved_imports,
        PackageReferenceImportContext {
            lock,
            entries,
            checked_by_module,
            owner_header,
            config,
        },
        &mut counters,
        None,
    )?;
    Ok(PackageDecodeCacheLookup { value, counters })
}

fn reference_import_store_with_cache_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    context: PackageReferenceImportContext<'_>,
    counters: &mut PackageVerificationDecodeCacheCounters,
    mut payload: Option<&mut PackagePayloadOwnershipObservation>,
) -> PackageVerificationResult<Arc<ReferenceImportStore>> {
    let PackageReferenceImportContext {
        lock,
        entries,
        checked_by_module,
        owner_header,
        config,
    } = context;
    let key = config
        .process_local_cache
        .then(|| {
            package_decode_cache_import_context_key(resolved_imports, checked_by_module, config)
        })
        .transpose()?;
    if let Some(key) = &key {
        let cached_imports =
            package_reference_cache_lookup(package_verification_decode_cache(), key);
        if let Some(imports) = cached_imports {
            counters.import_context_hits = counters.import_context_hits.saturating_add(1);
            if let Some(payload) = payload.as_deref_mut() {
                payload.sample_decode_cache();
            }
            validate_reference_import_context_hit(
                entry_index,
                resolved_imports,
                checked_by_module,
            )?;
            return Ok(imports);
        }
    }

    if config.process_local_cache {
        counters.import_context_misses = counters.import_context_misses.saturating_add(1);
    }
    let mut pending_import_context_export_cache_write = None;
    if config.persistent_import_context_export_cache {
        let expected_disk_entry = import_context_export_cache_entry_for_context(
            entry,
            resolved_imports,
            lock,
            entries,
            checked_by_module,
            owner_header,
            config,
        )?;
        let disk_cache_root = std::env::current_dir().ok();
        match disk_cache_root
            .as_deref()
            .map_or(ImportContextExportCacheLookup::Stale, |root| {
                read_import_context_export_cache_lookup(root, entry, &expected_disk_entry)
            }) {
            ImportContextExportCacheLookup::Hit => {
                counters.import_context_disk_hits =
                    counters.import_context_disk_hits.saturating_add(1);
                validate_reference_import_context_hit(
                    entry_index,
                    resolved_imports,
                    checked_by_module,
                )?;
            }
            ImportContextExportCacheLookup::Missing => {
                counters.import_context_disk_misses =
                    counters.import_context_disk_misses.saturating_add(1);
                pending_import_context_export_cache_write =
                    disk_cache_root.map(|root| (root, expected_disk_entry));
            }
            ImportContextExportCacheLookup::Stale => {
                counters.import_context_disk_stale =
                    counters.import_context_disk_stale.saturating_add(1);
                pending_import_context_export_cache_write =
                    disk_cache_root.map(|root| (root, expected_disk_entry));
            }
            ImportContextExportCacheLookup::SchemaMiss => {
                counters.import_context_disk_schema_misses =
                    counters.import_context_disk_schema_misses.saturating_add(1);
                pending_import_context_export_cache_write =
                    disk_cache_root.map(|root| (root, expected_disk_entry));
            }
        }
    }

    let import_modules = resolved_imports
        .iter()
        .map(|import| {
            checked_by_module
                .get(&import.module)
                .cloned()
                .ok_or_else(|| {
                    PackageVerificationError::earlier_module_failed(
                        format!("entries[{entry_index}].imports"),
                        import.module.as_dotted(),
                    )
                })
        })
        .collect::<PackageVerificationResult<Vec<_>>>()?;
    let imports = ReferenceImportStore::from_checked_modules(import_modules).map_err(|source| {
        PackageVerificationError::reference_checker_rejected(
            format!("entries[{entry_index}].imports"),
            source,
        )
    })?;
    if let Some((disk_cache_root, expected_disk_entry)) = pending_import_context_export_cache_write
    {
        if write_import_context_export_cache_entry(&disk_cache_root, entry, &expected_disk_entry) {
            counters.import_context_disk_inserted =
                counters.import_context_disk_inserted.saturating_add(1);
        }
    }
    let imports = Arc::new(imports);
    if let Some(key) = key {
        let inserted = package_reference_cache_insert(
            package_verification_decode_cache(),
            key,
            Arc::clone(&imports),
        );
        if inserted {
            counters.import_context_inserted = counters.import_context_inserted.saturating_add(1);
        } else {
            counters.import_context_capacity_stops =
                counters.import_context_capacity_stops.saturating_add(1);
            if let Some(payload) = payload.as_deref_mut() {
                payload.observe_decode_cache_capacity_stop();
            }
        }
        if let Some(payload) = payload {
            payload.sample_decode_cache();
        }
    }
    Ok(imports)
}

enum ImportContextExportCacheLookup {
    Hit,
    Missing,
    Stale,
    SchemaMiss,
}

const MAX_IMPORT_CONTEXT_EXPORT_ENTRY_BYTES: u64 = 134_217_728;

/// Directory capability for the fixed local import-context cache.
///
/// Every component is opened relative to a retained descriptor with
/// `O_NOFOLLOW`; entry reads and writes therefore cannot escape through a
/// symbolic-link component even if the process working directory is hostile.
#[cfg(unix)]
struct NoFollowCacheDirectory {
    file: fs::File,
}

#[cfg(unix)]
impl NoFollowCacheDirectory {
    fn open_absolute(path: &Path, create: bool) -> io::Result<Self> {
        use std::os::fd::FromRawFd;

        if !path.is_absolute() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "cache root must be absolute",
            ));
        }
        let root = std::ffi::CString::new("/").expect("filesystem root has no NUL");
        // SAFETY: `root` is NUL-terminated and successful ownership transfers
        // to `File` exactly once.
        let descriptor = unsafe {
            libc::open(
                root.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the descriptor is newly returned and uniquely owned.
        let mut directory = Self {
            file: unsafe { fs::File::from_raw_fd(descriptor) },
        };
        for component in path.components() {
            match component {
                std::path::Component::RootDir => {}
                std::path::Component::Normal(component) => {
                    directory = directory.open_directory(component, create)?;
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "cache root is not normalized",
                    ));
                }
            }
        }
        Ok(directory)
    }

    fn open_directory(&self, component: &OsStr, create: bool) -> io::Result<Self> {
        use std::os::{fd::AsRawFd, fd::FromRawFd};

        let component = cache_component_c_string(component)?;
        let mut descriptor = cache_open_directory_at(self.file.as_raw_fd(), &component);
        if descriptor
            .as_ref()
            .is_err_and(|error| create && error.kind() == io::ErrorKind::NotFound)
        {
            // SAFETY: the parent descriptor is live and the component is valid.
            if unsafe { libc::mkdirat(self.file.as_raw_fd(), component.as_ptr(), 0o700) } != 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::AlreadyExists {
                    return Err(error);
                }
            }
            descriptor = cache_open_directory_at(self.file.as_raw_fd(), &component);
        }
        let descriptor = descriptor?;
        // SAFETY: the descriptor is newly returned and uniquely owned.
        Ok(Self {
            file: unsafe { fs::File::from_raw_fd(descriptor) },
        })
    }

    fn read_regular_file(&self, component: &OsStr) -> io::Result<Option<String>> {
        use std::os::{fd::AsRawFd, fd::FromRawFd};

        let component = cache_component_c_string(component)?;
        // SAFETY: the retained parent descriptor is live and component is valid.
        let descriptor = unsafe {
            libc::openat(
                self.file.as_raw_fd(),
                component.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
            )
        };
        if descriptor < 0 {
            let error = io::Error::last_os_error();
            return if error.kind() == io::ErrorKind::NotFound {
                Ok(None)
            } else {
                Err(error)
            };
        }
        // SAFETY: the descriptor is newly returned and uniquely owned.
        let mut file = unsafe { fs::File::from_raw_fd(descriptor) };
        let metadata = file.metadata()?;
        if !metadata.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "cache entry is not a regular file",
            ));
        }
        if metadata.len() > MAX_IMPORT_CONTEXT_EXPORT_ENTRY_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "import-context export entry exceeds its byte limit",
            ));
        }
        let mut source = String::new();
        std::io::Read::by_ref(&mut file)
            .take(MAX_IMPORT_CONTEXT_EXPORT_ENTRY_BYTES + 1)
            .read_to_string(&mut source)?;
        if source.len() as u64 > MAX_IMPORT_CONTEXT_EXPORT_ENTRY_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "import-context export entry exceeds its byte limit",
            ));
        }
        Ok(Some(source))
    }

    fn write_atomic(&self, temporary: &OsStr, destination: &OsStr, bytes: &[u8]) -> io::Result<()> {
        use std::os::{fd::AsRawFd, fd::FromRawFd};

        let byte_length = u64::try_from(bytes.len()).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "import-context export entry length is not representable",
            )
        })?;
        if byte_length > MAX_IMPORT_CONTEXT_EXPORT_ENTRY_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "import-context export entry exceeds its byte limit",
            ));
        }
        let temporary_c = cache_component_c_string(temporary)?;
        let destination_c = cache_component_c_string(destination)?;
        // SAFETY: the parent descriptor is live, the component is valid, and a
        // mode is supplied because O_CREAT is set.
        let descriptor = unsafe {
            libc::openat(
                self.file.as_raw_fd(),
                temporary_c.as_ptr(),
                libc::O_WRONLY | libc::O_CLOEXEC | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW,
                0o600,
            )
        };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the descriptor is newly returned and uniquely owned.
        let mut file = unsafe { fs::File::from_raw_fd(descriptor) };
        let result = (|| {
            file.write_all(bytes)?;
            // SAFETY: `file` is a live descriptor opened by this function.
            if unsafe { libc::fchmod(file.as_raw_fd(), 0o600) } != 0 {
                return Err(io::Error::last_os_error());
            }
            file.sync_all()?;
            let opened = cache_fstat(file.as_raw_fd())?;
            if opened.st_mode & libc::S_IFMT != libc::S_IFREG
                || opened.st_mode & 0o777 != 0o600
                || opened.st_nlink != 1
                || opened.st_size < 0
                || u64::try_from(opened.st_size).ok() != Some(byte_length)
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "cache temporary entry violates its exact file policy",
                ));
            }
            cache_rename_no_replace(self.file.as_raw_fd(), &temporary_c, &destination_c)?;
            let named = cache_stat_at(self.file.as_raw_fd(), &destination_c)?;
            if named.st_mode & libc::S_IFMT != libc::S_IFREG
                || named.st_mode & 0o777 != 0o600
                || named.st_nlink != 1
                || named.st_dev != opened.st_dev
                || named.st_ino != opened.st_ino
                || named.st_size != opened.st_size
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "published cache entry does not match its retained source",
                ));
            }
            self.file.sync_all()?;
            let opened_after = cache_fstat(file.as_raw_fd())?;
            let named_after = cache_stat_at(self.file.as_raw_fd(), &destination_c)?;
            if opened_after.st_dev != opened.st_dev
                || opened_after.st_ino != opened.st_ino
                || opened_after.st_mode != opened.st_mode
                || opened_after.st_nlink != 1
                || opened_after.st_size != opened.st_size
                || named_after.st_dev != opened.st_dev
                || named_after.st_ino != opened.st_ino
                || named_after.st_mode != opened.st_mode
                || named_after.st_nlink != 1
                || named_after.st_size != opened.st_size
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "cache entry changed during durable no-replace publication",
                ));
            }
            Ok(())
        })();
        // A failed write deliberately preserves the unique temporary entry.
        // A non-cooperating same-owner process could replace its name between
        // observation and unlink, so online cleanup cannot be identity-safe.
        result
    }

    fn regular_file_names(&self) -> io::Result<Vec<std::ffi::OsString>> {
        use std::os::fd::AsRawFd;

        let mut names = Vec::new();
        for name in cache_directory_entry_names(self.file.as_raw_fd())? {
            let component = cache_component_c_string(&name)?;
            if cache_stat_at(self.file.as_raw_fd(), &component)
                .is_ok_and(|status| status.st_mode & libc::S_IFMT == libc::S_IFREG)
            {
                names.push(name);
            }
        }
        Ok(names)
    }

    fn remove_flat_managed_cache_directory(&self, component: &OsStr) -> io::Result<()> {
        let _ = cache_component_c_string(component)?;
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "online cache cleanup is disabled; preserved cache entries are untrusted residue",
        ))
    }
}

#[cfg(not(unix))]
struct NoFollowCacheDirectory;

#[cfg(not(unix))]
impl NoFollowCacheDirectory {
    fn open_absolute(_path: &Path, _create: bool) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "no-follow import-context cache is unavailable on this platform",
        ))
    }

    fn open_directory(&self, _component: &OsStr, _create: bool) -> io::Result<Self> {
        Self::open_absolute(Path::new(""), false)
    }

    fn read_regular_file(&self, _component: &OsStr) -> io::Result<Option<String>> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "unsupported"))
    }

    fn write_atomic(&self, _temp: &OsStr, _destination: &OsStr, _bytes: &[u8]) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "unsupported"))
    }

    fn regular_file_names(&self) -> io::Result<Vec<std::ffi::OsString>> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "unsupported"))
    }

    fn remove_flat_managed_cache_directory(&self, _component: &OsStr) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "unsupported"))
    }
}

#[cfg(unix)]
fn cache_component_c_string(component: &OsStr) -> io::Result<std::ffi::CString> {
    use std::os::unix::ffi::OsStrExt;

    let path = Path::new(component);
    if component.is_empty()
        || path.components().count() != 1
        || matches!(component.as_bytes(), b"." | b"..")
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "expected one non-dot cache path component",
        ));
    }
    std::ffi::CString::new(component.as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains NUL"))
}

#[cfg(unix)]
fn cache_open_directory_at(parent: libc::c_int, component: &std::ffi::CString) -> io::Result<i32> {
    // SAFETY: parent is live and component is a valid NUL-terminated name.
    let descriptor = unsafe {
        libc::openat(
            parent,
            component.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
        )
    };
    if descriptor < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(descriptor)
    }
}

#[cfg(unix)]
fn cache_stat_at(parent: libc::c_int, component: &std::ffi::CString) -> io::Result<libc::stat> {
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: status is writable, parent is live, and component is valid.
    if unsafe {
        libc::fstatat(
            parent,
            component.as_ptr(),
            status.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fstatat initialized the complete value.
    Ok(unsafe { status.assume_init() })
}

#[cfg(unix)]
fn cache_fstat(descriptor: libc::c_int) -> io::Result<libc::stat> {
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: status is writable and descriptor is live.
    if unsafe { libc::fstat(descriptor, status.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fstat initialized the complete value.
    Ok(unsafe { status.assume_init() })
}

#[cfg(all(unix, target_vendor = "apple"))]
fn cache_rename_no_replace(
    parent: libc::c_int,
    source: &std::ffi::CString,
    destination: &std::ffi::CString,
) -> io::Result<()> {
    // SAFETY: the retained parent and validated names are live.
    if unsafe {
        libc::renameatx_np(
            parent,
            source.as_ptr(),
            parent,
            destination.as_ptr(),
            libc::RENAME_EXCL,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn cache_rename_no_replace(
    parent: libc::c_int,
    source: &std::ffi::CString,
    destination: &std::ffi::CString,
) -> io::Result<()> {
    // SAFETY: the retained parent and validated names are live.
    if unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            parent,
            source.as_ptr(),
            parent,
            destination.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(all(
    unix,
    not(any(target_vendor = "apple", target_os = "linux", target_os = "android"))
))]
fn cache_rename_no_replace(
    _parent: libc::c_int,
    _source: &std::ffi::CString,
    _destination: &std::ffi::CString,
) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "atomic no-replace cache publication is unavailable",
    ))
}

#[cfg(all(
    unix,
    any(target_vendor = "apple", target_os = "linux", target_os = "android")
))]
fn cache_directory_entry_names(descriptor: libc::c_int) -> io::Result<Vec<std::ffi::OsString>> {
    use std::os::unix::ffi::OsStringExt;

    // SAFETY: descriptor is live; dup returns an independently owned fd.
    let duplicate = unsafe { libc::dup(descriptor) };
    if duplicate < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fdopendir takes ownership of duplicate.
    let stream = unsafe { libc::fdopendir(duplicate) };
    if stream.is_null() {
        let error = io::Error::last_os_error();
        // SAFETY: fdopendir failed, so ownership was not transferred.
        unsafe { libc::close(duplicate) };
        return Err(error);
    }
    let mut names = Vec::new();
    let mut read_error = None;
    loop {
        // SAFETY: each supported libc exposes the calling thread's errno slot.
        unsafe { *cache_errno_location() = 0 };
        // SAFETY: stream remains live until closedir below.
        let entry = unsafe { libc::readdir(stream) };
        if entry.is_null() {
            // SAFETY: see the reset above. A nonzero errno distinguishes an
            // interrupted/error return from true end-of-directory.
            let errno = unsafe { *cache_errno_location() };
            if errno != 0 {
                read_error = Some(io::Error::from_raw_os_error(errno));
            }
            break;
        }
        // SAFETY: d_name is NUL-terminated within the live dirent.
        let bytes = unsafe { std::ffi::CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if !matches!(bytes, b"." | b"..") {
            names.push(std::ffi::OsString::from_vec(bytes.to_vec()));
        }
    }
    // SAFETY: stream is live and owns duplicate.
    if unsafe { libc::closedir(stream) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if let Some(error) = read_error {
        return Err(error);
    }
    Ok(names)
}

#[cfg(target_vendor = "apple")]
unsafe fn cache_errno_location() -> *mut libc::c_int {
    // SAFETY: delegated to the caller; libc returns the current thread slot.
    unsafe { libc::__error() }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
unsafe fn cache_errno_location() -> *mut libc::c_int {
    // SAFETY: delegated to the caller; libc returns the current thread slot.
    unsafe { libc::__errno_location() }
}

#[cfg(all(
    unix,
    not(any(target_vendor = "apple", target_os = "linux", target_os = "android"))
))]
fn cache_directory_entry_names(_descriptor: libc::c_int) -> io::Result<Vec<std::ffi::OsString>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "bounded cache catalog enumeration is unavailable on this platform",
    ))
}

fn import_context_export_cache_entry_for_context(
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
    owner_header: &CertHeader,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<PackageImportContextExportCacheEntry> {
    let dependency_exports = resolved_imports
        .iter()
        .map(|import| {
            let Some((_, dependency)) = entries.get(import.entry_index) else {
                return Err(PackageVerificationError::lock_graph_invalid(format!(
                    "missing dependency entry index {} for {}",
                    import.entry_index,
                    import.module.as_dotted(),
                )));
            };
            if dependency.module != import.module
                || dependency.export_hash != import.export_hash
                || dependency.certificate_hash != import.certificate_hash
            {
                return Err(PackageVerificationError::lock_graph_invalid(format!(
                    "dependency identity mismatch for {}",
                    import.module.as_dotted(),
                )));
            }
            let checked = checked_by_module.get(&import.module).ok_or_else(|| {
                PackageVerificationError::earlier_module_failed(
                    "import_context_export_cache.dependency_exports",
                    import.module.as_dotted(),
                )
            })?;
            Ok(PackageImportContextExportData {
                module: dependency.module.clone(),
                origin: dependency.origin,
                package: dependency.package.clone(),
                version: dependency.version.clone(),
                export_hash: dependency.export_hash,
                certificate_hash: dependency.certificate_hash,
                axiom_report_hash: dependency.axiom_report_hash,
                certificate_format: checked.certificate_format().to_owned(),
                core_spec: checked.core_spec().to_owned(),
            })
        })
        .collect::<PackageVerificationResult<Vec<_>>>()?;
    let key_input = PackageImportContextExportCacheKeyInput {
        schema: PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA.to_owned(),
        package_id: lock.package.clone(),
        package_version: lock.version.clone(),
        package_lock_schema: lock.schema.clone(),
        package_core_profile: config.package_core_profile.clone(),
        package_certificate_profile: config.package_certificate_profile.clone(),
        owner_certificate_format: owner_header.format.clone(),
        owner_core_spec: owner_header.core_spec.clone(),
        checker_policy_hash: config.checker_policy_hash,
        owner_module: entry.module.clone(),
        dependency_exports,
    };
    Ok(PackageImportContextExportCacheEntry {
        schema: PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA.to_owned(),
        cache_key: package_import_context_export_cache_key(&key_input),
        trusted: false,
        proof_evidence: false,
        dependency_exports: key_input.dependency_exports.clone(),
        key_input,
        trust_boundary: "import context export cache entry is local-only and not proof evidence"
            .to_owned(),
    })
}

fn read_import_context_export_cache_lookup(
    cache_root: &Path,
    entry: &PackageLockEntry,
    expected: &PackageImportContextExportCacheEntry,
) -> ImportContextExportCacheLookup {
    let cache = match open_import_context_export_cache_at(cache_root, false) {
        Ok(cache) => cache,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return ImportContextExportCacheLookup::Missing;
        }
        Err(_) => return ImportContextExportCacheLookup::Stale,
    };
    let filename = import_context_export_cache_entry_filename(entry, &expected.key_input);
    let source = match cache.read_regular_file(OsStr::new(&filename)) {
        Ok(Some(source)) => source,
        Ok(None) => return ImportContextExportCacheLookup::Missing,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return ImportContextExportCacheLookup::Missing;
        }
        Err(_) => return ImportContextExportCacheLookup::Stale,
    };
    if source == package_import_context_export_cache_entry_json(expected) {
        return ImportContextExportCacheLookup::Hit;
    }
    match parse_package_import_context_export_cache_entry_json(&source) {
        Ok(entry) if &entry == expected => ImportContextExportCacheLookup::Hit,
        Ok(_) => ImportContextExportCacheLookup::Stale,
        Err(error) if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema => {
            ImportContextExportCacheLookup::SchemaMiss
        }
        Err(_) => ImportContextExportCacheLookup::Stale,
    }
}

fn write_import_context_export_cache_entry(
    cache_root: &Path,
    owner: &PackageLockEntry,
    entry: &PackageImportContextExportCacheEntry,
) -> bool {
    let Ok(cache) = open_import_context_export_cache_at(cache_root, true) else {
        return false;
    };
    let filename = import_context_export_cache_entry_filename(owner, &entry.key_input);
    let temp_index = NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
    let temp_filename = format!(
        "{}.{}.{}.tmp",
        import_context_export_cache_slot_key(owner, &entry.key_input),
        std::process::id(),
        temp_index
    );
    cache
        .write_atomic(
            OsStr::new(&temp_filename),
            OsStr::new(&filename),
            package_import_context_export_cache_entry_json(entry).as_bytes(),
        )
        .is_ok()
}

fn open_import_context_export_cache_at(
    root: &Path,
    create: bool,
) -> io::Result<NoFollowCacheDirectory> {
    let mut directory = NoFollowCacheDirectory::open_absolute(root, false)?;
    for component in Path::new(PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR).components() {
        let std::path::Component::Normal(component) = component else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "cache layout must contain only normal components",
            ));
        };
        directory = directory.open_directory(component, create)?;
    }
    Ok(directory)
}

fn remove_import_context_export_cache_at(root: &Path) -> io::Result<()> {
    let mut directory = NoFollowCacheDirectory::open_absolute(root, false)?;
    let mut components = Path::new(PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR)
        .components()
        .map(|component| match component {
            std::path::Component::Normal(component) => Ok(component.to_owned()),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "cache layout must contain only normal components",
            )),
        })
        .collect::<io::Result<Vec<_>>>()?;
    let leaf = components
        .pop()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "cache layout is empty"))?;
    for component in components {
        directory = directory.open_directory(&component, false)?;
    }
    match directory.remove_flat_managed_cache_directory(&leaf) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        result => result,
    }
}

fn import_context_export_cache_entry_filename(
    owner: &PackageLockEntry,
    input: &PackageImportContextExportCacheKeyInput,
) -> String {
    format!(
        "{}.{}.json",
        import_context_export_cache_slot_key(owner, input),
        package_import_context_export_cache_key(input)
    )
}

fn import_context_export_cache_slot_key(
    owner: &PackageLockEntry,
    input: &PackageImportContextExportCacheKeyInput,
) -> String {
    let material = format!(
        "schema=npa.package.import_context_export_cache_slot.v0.2\npackage_id={}\npackage_version={}\npackage_lock_schema={}\npackage_core_profile={}\npackage_certificate_profile={}\nowner_certificate_format={}\nowner_core_spec={}\nchecker_policy_hash={}\nowner_module={}\n",
        input.package_id.as_str(),
        input.package_version.as_str(),
        input.package_lock_schema,
        input.package_core_profile,
        input.package_certificate_profile,
        input.owner_certificate_format,
        input.owner_core_spec,
        format_package_hash(&input.checker_policy_hash),
        owner.module.as_dotted(),
    );
    format_package_hash(&package_file_hash(material.as_bytes()))
}

fn validate_reference_import_context_hit(
    entry_index: usize,
    resolved_imports: &[PackageLockResolvedImport],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
) -> PackageVerificationResult<()> {
    for import in resolved_imports {
        let checked = checked_by_module.get(&import.module).ok_or_else(|| {
            PackageVerificationError::earlier_module_failed(
                format!("entries[{entry_index}].imports"),
                import.module.as_dotted(),
            )
        })?;
        let actual_export_hash = PackageHash::from(*checked.export_hash());
        if actual_export_hash != import.export_hash {
            return Err(PackageVerificationError::export_hash_mismatch(
                format!("entries[{entry_index}].imports"),
                import.export_hash,
                actual_export_hash,
            ));
        }
        let actual_certificate_hash = PackageHash::from(*checked.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Err(PackageVerificationError::certificate_hash_mismatch(
                format!("entries[{entry_index}].imports"),
                import.certificate_hash,
                actual_certificate_hash,
            ));
        }
    }
    Ok(())
}

fn package_decode_cache_certificate_key(
    entry: &PackageLockEntry,
    certificate_file_hash: PackageHash,
    header: &CertHeader,
    config: &PackageVerificationDecodeCacheConfig,
) -> String {
    let mut material = format!(
        "schema=npa.package.decode_cache.certificate.v0.2\nmode={}\ncertificate_format={}\ncore_spec={}\ncertificate_file_hash={}\ncertificate_hash={}\nenabled_core_features={}\n",
        config.checker_mode.as_str(),
        header.format,
        header.core_spec,
        format_package_hash(&certificate_file_hash),
        format_package_hash(&entry.certificate_hash),
        config.enabled_core_features.len(),
    );
    for feature in &config.enabled_core_features {
        material.push_str("enabled_core_feature=");
        material.push_str(feature);
        material.push('\n');
    }
    format_package_hash(&package_file_hash(material.as_bytes()))
}

fn package_decode_cache_import_context_key(
    resolved_imports: &[PackageLockResolvedImport],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<String> {
    let mut material = format!(
        "schema=npa.package.decode_cache.import_context.v0.2\nmode={}\nchecker_policy_hash={}\ndirect_imports={}\n",
        config.checker_mode.as_str(),
        format_package_hash(&config.checker_policy_hash),
        resolved_imports.len(),
    );
    for import in resolved_imports {
        material.push_str("direct_import=");
        material.push_str(&import.module.as_dotted());
        material.push(';');
        material.push_str(&format_package_hash(&import.export_hash));
        material.push(';');
        material.push_str(&format_package_hash(&import.certificate_hash));
        let checked = checked_by_module.get(&import.module).ok_or_else(|| {
            PackageVerificationError::earlier_module_failed(
                "decode_cache.import_context.direct_imports",
                import.module.as_dotted(),
            )
        })?;
        material.push(';');
        material.push_str(checked.certificate_format());
        material.push(';');
        material.push_str(checked.core_spec());
        material.push('\n');
    }
    Ok(format_package_hash(&package_file_hash(material.as_bytes())))
}

struct PackageVerificationMemoRun {
    handle: Option<PackageVerificationProcessMemoHandle>,
    store_available: bool,
    keys_by_module: BTreeMap<Name, MemoKeyAndWeight>,
    counters: PackageVerificationMemoCounters,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemoKeyAndWeight {
    key: String,
    weighted_certificate_bytes: u64,
}

impl PackageVerificationMemoRun {
    fn disabled() -> Self {
        Self {
            handle: None,
            store_available: false,
            keys_by_module: BTreeMap::new(),
            counters: PackageVerificationMemoCounters::default(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn for_run(
        options: &PackageVerificationExecutionOptions,
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        graph: &PackageLockGraph,
        entries: &[(usize, &PackageLockEntry)],
        execution_modules: &BTreeSet<Name>,
        artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
        mode: PackageVerificationMode,
    ) -> PackageVerificationResult<Self> {
        let PackageVerificationMemoMode::ProcessLocal(handle) = &options.memoization else {
            return Ok(Self::disabled());
        };
        let (keys_by_module, keys_built, certificate_bytes_hashed) =
            package_verification_memo_keys(
                validated,
                lock,
                graph,
                entries,
                execution_modules,
                artifact_bytes,
                mode,
            )?;
        Ok(Self {
            handle: Some(handle.clone()),
            store_available: true,
            keys_by_module,
            counters: PackageVerificationMemoCounters {
                keys_built,
                certificate_bytes_hashed,
                ..PackageVerificationMemoCounters::default()
            },
        })
    }

    fn for_snapshot_run(
        options: &PackageVerificationExecutionOptions,
        validated: &ValidatedPackageManifest,
        indexed: &IndexedPackageLockGraph,
        execution_modules: &BTreeSet<Name>,
        artifacts: &PreparedPackageArtifacts,
        mode: PackageVerificationMode,
    ) -> PackageVerificationResult<Self> {
        let PackageVerificationMemoMode::ProcessLocal(handle) = &options.memoization else {
            return Ok(Self::disabled());
        };
        let inputs = package_verification_memo_key_inputs_from_artifact_snapshots_indexed_scoped(
            validated,
            indexed,
            artifacts,
            Some(execution_modules),
            mode,
        )?;
        let mut keys_by_module = BTreeMap::new();
        for (module, input) in inputs {
            let Some(entry_index) = indexed.index().entry_by_module(&module) else {
                continue;
            };
            let entry = &indexed.entries()[entry_index];
            let Some(artifact) = artifacts.get(&entry.certificate) else {
                continue;
            };
            let weighted_certificate_bytes = match artifact {
                PreparedPackageArtifactView::Hashed(artifact) => artifact.bytes().len(),
                PreparedPackageArtifactView::Prepared(artifact) => artifact.bytes().len(),
            };
            keys_by_module.insert(
                module,
                MemoKeyAndWeight {
                    key: package_audit_process_memo_key(&input),
                    weighted_certificate_bytes: u64::try_from(weighted_certificate_bytes)
                        .unwrap_or(u64::MAX),
                },
            );
        }
        let keys_built = keys_by_module.len();
        Ok(Self {
            handle: Some(handle.clone()),
            store_available: true,
            keys_by_module,
            counters: PackageVerificationMemoCounters {
                keys_built,
                // Snapshot keys reuse the file hash bound by lock derivation.
                certificate_bytes_hashed: 0,
                ..PackageVerificationMemoCounters::default()
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn for_hashed_run(
        options: &PackageVerificationExecutionOptions,
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        graph: &PackageLockGraph,
        entries: &[(usize, &PackageLockEntry)],
        execution_modules: &BTreeSet<Name>,
        artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
        artifact_file_hashes: Option<&BTreeMap<PackagePath, PackageHash>>,
        mode: PackageVerificationMode,
    ) -> PackageVerificationResult<Self> {
        let Some(artifact_file_hashes) = artifact_file_hashes else {
            return Self::for_run(
                options,
                validated,
                lock,
                graph,
                entries,
                execution_modules,
                artifact_bytes,
                mode,
            );
        };
        let PackageVerificationMemoMode::ProcessLocal(handle) = &options.memoization else {
            return Ok(Self::disabled());
        };
        let (keys_by_module, keys_built) = package_verification_memo_keys_prehashed(
            validated,
            lock,
            graph,
            entries,
            execution_modules,
            artifact_bytes,
            artifact_file_hashes,
            mode,
        )?;
        Ok(Self {
            handle: Some(handle.clone()),
            store_available: true,
            keys_by_module,
            counters: PackageVerificationMemoCounters {
                keys_built,
                // Hashed-artifact keys reuse the file hash bound by lock derivation.
                certificate_bytes_hashed: 0,
                ..PackageVerificationMemoCounters::default()
            },
        })
    }

    fn mark_store_unavailable(&mut self) {
        if self.store_available {
            self.store_available = false;
            self.counters.bypassed_store_unavailable =
                self.counters.bypassed_store_unavailable.saturating_add(1);
        }
    }

    fn lookup(&mut self, module: &Name) -> Option<Arc<PackageVerificationMemoEntry>> {
        if !self.store_available {
            return None;
        }
        let key = self.keys_by_module.get(module)?.key.clone();
        let handle = self.handle.as_ref()?.clone();
        match handle.lookup(&key) {
            Ok(hit) => {
                if hit.is_some() {
                    self.counters.hits = self.counters.hits.saturating_add(1);
                } else {
                    self.counters.misses = self.counters.misses.saturating_add(1);
                }
                hit
            }
            Err(PackageVerificationProcessMemoAccessError::Poisoned) => {
                self.mark_store_unavailable();
                None
            }
        }
    }

    fn insert(&mut self, module: &Name, entry: PackageVerificationMemoEntry) {
        if !self.store_available {
            return;
        }
        let Some(key) = self.keys_by_module.get(module).cloned() else {
            return;
        };
        let Some(handle) = self.handle.as_ref().cloned() else {
            return;
        };
        match handle.insert(key.key, Arc::new(entry), key.weighted_certificate_bytes) {
            Ok(BoundedMemoInsertOutcome::Inserted { evicted }) => {
                self.counters.inserted = self.counters.inserted.saturating_add(1);
                self.counters.evicted = self.counters.evicted.saturating_add(evicted);
            }
            Ok(BoundedMemoInsertOutcome::RejectedOversize) => {
                self.counters.rejected_oversize = self.counters.rejected_oversize.saturating_add(1);
            }
            Err(PackageVerificationProcessMemoAccessError::Poisoned) => {
                self.mark_store_unavailable();
            }
        }
    }

    fn counters(&self) -> PackageVerificationMemoCounters {
        self.counters
    }
}

fn package_verification_memo_keys(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    execution_modules: &BTreeSet<Name>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<(BTreeMap<Name, MemoKeyAndWeight>, usize, u64)> {
    let inputs = package_verification_memo_key_inputs_for_entries_scoped(
        validated,
        lock,
        graph,
        entries,
        Some(execution_modules),
        artifact_bytes,
        mode,
    )?;
    let keys_built = inputs.len();
    let mut certificate_bytes_hashed = 0u64;
    let keys = inputs
        .into_iter()
        .map(|(module, (input, weighted_certificate_bytes))| {
            certificate_bytes_hashed =
                certificate_bytes_hashed.saturating_add(weighted_certificate_bytes);
            (
                module,
                MemoKeyAndWeight {
                    key: package_audit_process_memo_key(&input),
                    weighted_certificate_bytes,
                },
            )
        })
        .collect();
    Ok((keys, keys_built, certificate_bytes_hashed))
}

#[allow(clippy::too_many_arguments)]
fn package_verification_memo_keys_prehashed(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    execution_modules: &BTreeSet<Name>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: &BTreeMap<PackagePath, PackageHash>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<(BTreeMap<Name, MemoKeyAndWeight>, usize)> {
    let inputs = package_verification_memo_key_inputs_for_entries_scoped_with_hashes(
        validated,
        lock,
        graph,
        entries,
        Some(execution_modules),
        artifact_bytes,
        Some(artifact_file_hashes),
        mode,
    )?;
    let keys_built = inputs.len();
    let keys = inputs
        .into_iter()
        .map(|(module, (input, weighted_certificate_bytes))| {
            (
                module,
                MemoKeyAndWeight {
                    key: package_audit_process_memo_key(&input),
                    weighted_certificate_bytes,
                },
            )
        })
        .collect();
    Ok((keys, keys_built))
}

fn package_verification_memo_key_inputs_for_entries(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
    Ok(package_verification_memo_key_inputs_for_entries_scoped(
        validated,
        lock,
        graph,
        entries,
        None,
        artifact_bytes,
        mode,
    )?
    .into_iter()
    .map(|(module, (input, _))| (module, input))
    .collect())
}

fn package_verification_memo_key_inputs_for_entries_scoped(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    execution_modules: Option<&BTreeSet<Name>>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, (PackageAuditCacheKeyInput, u64)>> {
    package_verification_memo_key_inputs_for_entries_scoped_with_hashes(
        validated,
        lock,
        graph,
        entries,
        execution_modules,
        artifact_bytes,
        None,
        mode,
    )
}

#[allow(clippy::too_many_arguments)]
fn package_verification_memo_key_inputs_for_entries_scoped_with_hashes(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    execution_modules: Option<&BTreeSet<Name>>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    artifact_file_hashes: Option<&BTreeMap<PackagePath, PackageHash>>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, (PackageAuditCacheKeyInput, u64)>> {
    let lock_json = lock
        .canonical_json()
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let package_lock_hash = package_file_hash(lock_json.as_bytes());
    let package_policy_hash = package_verification_policy_hash(validated, mode);
    let checker = package_verification_checker_identity(validated, mode);
    let enabled_core_features = package_verification_enabled_core_features(validated, mode);
    let manifest = validated.manifest();
    let mut inputs = BTreeMap::new();

    for (entry_index, entry) in entries {
        if execution_modules
            .is_some_and(|execution_modules| !execution_modules.contains(&entry.module))
        {
            continue;
        }
        let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() else {
            continue;
        };
        let Ok(header) = decode_module_cert_header(bytes) else {
            // Pair-unaware or malformed inputs cannot participate in a v0.2 memo key. The live
            // verifier still receives them and produces the authoritative structured failure.
            continue;
        };
        let key_input = PackageAuditCacheKeyInput {
            schema: PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA.to_owned(),
            package_id: lock.package.clone(),
            package_version: lock.version.clone(),
            package_lock_schema: lock.schema.clone(),
            package_core_profile: manifest.core_spec.clone(),
            package_certificate_profile: manifest.certificate_format.clone(),
            module_certificate_format: header.format,
            module_core_spec: header.core_spec,
            package_lock_hash,
            package_policy_hash,
            checker: checker.clone(),
            module: entry.module.clone(),
            origin: entry.origin,
            certificate: entry.certificate.clone(),
            certificate_file_hash: match artifact_file_hashes {
                Some(file_hashes) => {
                    let Some(file_hash) = file_hashes.get(&entry.certificate).copied() else {
                        continue;
                    };
                    file_hash
                }
                None => package_file_hash(bytes),
            },
            certificate_hash: entry.certificate_hash,
            export_hash: entry.export_hash,
            axiom_report_hash: entry.axiom_report_hash,
            direct_imports: graph.resolved_entry_imports[*entry_index]
                .iter()
                .map(|import| PackageAuditImportIdentity {
                    module: import.module.clone(),
                    export_hash: import.export_hash,
                    certificate_hash: import.certificate_hash,
                })
                .collect(),
            dependency_summary_hash: None,
            enabled_core_features: enabled_core_features.clone(),
        };
        inputs.insert(
            entry.module.clone(),
            (key_input, u64::try_from(bytes.len()).unwrap_or(u64::MAX)),
        );
    }

    Ok(inputs)
}

fn package_verification_policy_hash(
    validated: &ValidatedPackageManifest,
    mode: PackageVerificationMode,
) -> PackageHash {
    if mode == PackageVerificationMode::FastKernel {
        return PackageHash::new(package_fast_kernel_policy(validated).policy_hash());
    }

    let policy = package_reference_checker_policy(validated);
    let mut allowed_axioms = policy.allowed_axioms;
    allowed_axioms.sort();
    allowed_axioms.dedup();
    let trust_mode = match policy.trust_mode {
        ReferenceTrustMode::Normal => "normal",
        ReferenceTrustMode::HighTrust => "high_trust",
    };
    let mut enabled_core_features = policy
        .supported_core_features
        .iter()
        .copied()
        .map(ReferenceCoreFeature::as_str)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    enabled_core_features.sort();
    enabled_core_features.dedup();

    let mut material = format!(
        "schema=npa.package.reference_verification_axiom_policy.v0.1\nmode={}\ntrust_mode={trust_mode}\ndeny_sorry={}\ndeny_custom_axioms={}\nallow_standard_axiom_exceptions={}\nallowed_axioms={}\nenabled_core_features={}\n",
        mode.as_str(),
        policy.deny_sorry,
        policy.deny_custom_axioms,
        policy.allow_standard_axiom_exceptions,
        allowed_axioms.len(),
        enabled_core_features.len(),
    );
    for axiom in allowed_axioms {
        material.push_str("allowed_axiom=");
        material.push_str(&axiom);
        material.push('\n');
    }
    for feature in enabled_core_features {
        material.push_str("enabled_core_feature=");
        material.push_str(&feature);
        material.push('\n');
    }
    package_file_hash(material.as_bytes())
}

fn package_verification_checker_identity(
    validated: &ValidatedPackageManifest,
    mode: PackageVerificationMode,
) -> PackageAuditCheckerIdentity {
    let checker_id = match mode {
        PackageVerificationMode::FastKernel => "fast-kernel-certificate-verifier",
        PackageVerificationMode::Reference => "npa-checker-ref",
    };
    let checker_profile = match mode {
        PackageVerificationMode::FastKernel => "fast-kernel".to_owned(),
        PackageVerificationMode::Reference => validated.manifest().checker_profile.clone(),
    };
    let checker_version = env!("CARGO_PKG_VERSION").to_owned();
    let build_material = format!(
        "schema=npa.package.verification_process_memo_checker_identity.v0.1\nmode={}\nchecker_id={checker_id}\nchecker_version={checker_version}\nchecker_profile={checker_profile}\n",
        mode.as_str(),
    );

    PackageAuditCheckerIdentity {
        mode: mode.as_str().to_owned(),
        checker_id: checker_id.to_owned(),
        checker_version,
        checker_build_hash: package_file_hash(build_material.as_bytes()),
        checker_profile,
        runner_policy_hash: None,
    }
}

fn package_verification_enabled_core_features(
    validated: &ValidatedPackageManifest,
    mode: PackageVerificationMode,
) -> Vec<String> {
    let mut features = match mode {
        PackageVerificationMode::FastKernel => package_fast_kernel_policy(validated)
            .supported_core_features
            .iter()
            .copied()
            .map(CoreFeature::as_str)
            .map(str::to_owned)
            .collect::<Vec<_>>(),
        PackageVerificationMode::Reference => {
            reference_checker_supported_core_features(&validated.manifest().checker_profile)
                .iter()
                .copied()
                .map(ReferenceCoreFeature::as_str)
                .map(str::to_owned)
                .collect::<Vec<_>>()
        }
    };
    features.sort();
    features.dedup();
    features
}

fn execution_modules_for_options(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    options: &PackageVerificationExecutionOptions,
) -> PackageVerificationResult<BTreeSet<Name>> {
    let entry_by_module = entries
        .iter()
        .map(|(entry_index, entry)| (entry.module.clone(), *entry_index))
        .collect::<BTreeMap<_, _>>();
    let mut selected = vec![false; entries.len()];
    let mut pending = Vec::new();
    match &options.selected_modules {
        Some(seeds) => {
            for module in seeds {
                let entry = entry_by_module
                    .get(module)
                    .copied()
                    .ok_or_else(|| PackageVerificationError::selected_module_missing(module))?;
                if !selected[entry] {
                    selected[entry] = true;
                    pending.push(entry);
                }
            }
        }
        None => {
            for (entry_index, _) in entries {
                selected[*entry_index] = true;
                pending.push(*entry_index);
            }
        }
    }
    while let Some(entry) = pending.pop() {
        for import in &graph.resolved_entry_imports[entry] {
            if !selected[import.entry_index] {
                selected[import.entry_index] = true;
                pending.push(import.entry_index);
            }
        }
    }
    Ok(entries
        .iter()
        .filter(|(entry_index, _)| selected[*entry_index])
        .map(|(_, entry)| entry.module.clone())
        .collect())
}

/// Frozen pre-index selected-closure implementation used only by differential
/// tests and the explicit planning benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
fn legacy_execution_modules_fixed_point_oracle(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    options: &PackageVerificationExecutionOptions,
) -> PackageVerificationResult<BTreeSet<Name>> {
    let known_modules = entries
        .iter()
        .map(|(_, entry)| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let mut execution_modules = match &options.selected_modules {
        Some(selected) => {
            for module in selected {
                if !known_modules.contains(module) {
                    return Err(PackageVerificationError::selected_module_missing(module));
                }
            }
            selected.clone()
        }
        None => known_modules,
    };

    loop {
        let mut changed = false;
        for (entry_index, entry) in entries {
            if !execution_modules.contains(&entry.module) {
                continue;
            }
            for import in &graph.resolved_entry_imports[*entry_index] {
                changed |= execution_modules.insert(import.module.clone());
            }
        }
        if !changed {
            return Ok(execution_modules);
        }
    }
}

fn execution_modules_for_indexed(
    indexed: &IndexedPackageLockGraph,
    options: &PackageVerificationExecutionOptions,
) -> PackageVerificationResult<BTreeSet<Name>> {
    let selected = match &options.selected_modules {
        Some(seeds) => {
            for module in seeds {
                if indexed.index().entry_by_module(module).is_none() {
                    return Err(PackageVerificationError::selected_module_missing(module));
                }
            }
            indexed.index().dependency_closure(seeds).map_err(|error| {
                PackageVerificationError::lock_graph_invalid(format!(
                    "internal_index_invariant:{}",
                    error.invariant()
                ))
            })?
        }
        None => vec![true; indexed.entries().len()],
    };
    Ok(indexed
        .index()
        .topological_entries()
        .iter()
        .filter(|entry| selected[**entry])
        .map(|entry| {
            indexed
                .index()
                .module_by_entry(*entry)
                .expect("validated index contains every entry")
                .clone()
        })
        .collect())
}

fn reference_import_use_counts(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
) -> BTreeMap<Name, usize> {
    let mut remaining_import_uses = BTreeMap::<Name, usize>::new();
    for (entry_index, entry) in entries {
        if !execution_modules.contains(&entry.module) {
            continue;
        }
        for import in &graph.resolved_entry_imports[*entry_index] {
            if execution_modules.contains(&import.module) {
                *remaining_import_uses
                    .entry(import.module.clone())
                    .or_insert(0) += 1;
            }
        }
    }
    remaining_import_uses
}

fn record_reference_checked_module_for_dependents(
    checked_by_module: &mut BTreeMap<Name, ReferenceCheckedModule>,
    remaining_import_uses: &BTreeMap<Name, usize>,
    entry: &PackageLockEntry,
    checked: ReferenceCheckedModule,
) {
    if remaining_import_uses
        .get(&entry.module)
        .copied()
        .unwrap_or(0)
        > 0
    {
        checked_by_module.insert(entry.module.clone(), checked);
    }
}

fn retire_reference_imports_after_module(
    entry_index: usize,
    graph: &PackageLockGraph,
    checked_by_module: &mut BTreeMap<Name, ReferenceCheckedModule>,
    remaining_import_uses: &mut BTreeMap<Name, usize>,
) {
    for module in
        reference_modules_to_retire_after_module(entry_index, graph, remaining_import_uses)
    {
        checked_by_module.remove(&module);
    }
}

fn reference_modules_to_retire_after_module(
    entry_index: usize,
    graph: &PackageLockGraph,
    remaining_import_uses: &mut BTreeMap<Name, usize>,
) -> Vec<Name> {
    let mut retired = Vec::new();
    for import in &graph.resolved_entry_imports[entry_index] {
        let Some(remaining) = remaining_import_uses.get_mut(&import.module) else {
            continue;
        };
        debug_assert!(*remaining > 0);
        if *remaining > 0 {
            *remaining -= 1;
        }
        if *remaining == 0 {
            retired.push(import.module.clone());
        }
    }
    for module in &retired {
        remaining_import_uses.remove(module);
    }
    retired
}

#[cfg(test)]
fn execution_layers_for_modules(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
) -> Vec<Vec<Name>> {
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), *index))
        .collect::<BTreeMap<_, _>>();
    let mut layer_by_entry = vec![0usize; entries.len()];
    let mut layers = Vec::<Vec<Name>>::new();
    for module in &graph.topological_order {
        if !execution_modules.contains(module) {
            continue;
        }
        let entry = *entries_by_module
            .get(module)
            .expect("graph order only contains lock entries");
        let layer = graph.resolved_entry_imports[entry]
            .iter()
            .filter(|import| execution_modules.contains(&import.module))
            .map(|import| layer_by_entry[import.entry_index].saturating_add(1))
            .max()
            .unwrap_or(0);
        if layers.len() <= layer {
            layers.resize_with(layer + 1, Vec::new);
        }
        layers[layer].push(module.clone());
        layer_by_entry[entry] = layer;
    }

    layers
}

/// Frozen pre-index repeated-ready-scan implementation used only by
/// differential tests and the explicit planning benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
fn legacy_execution_layers_ready_scan_oracle(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
) -> Vec<Vec<Name>> {
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), *index))
        .collect::<BTreeMap<_, _>>();
    let mut remaining = execution_modules.clone();
    let mut assigned = BTreeSet::<Name>::new();
    let mut layers = Vec::<Vec<Name>>::new();

    while !remaining.is_empty() {
        let layer = graph
            .topological_order
            .iter()
            .filter(|module| remaining.contains(*module))
            .filter(|module| {
                let entry_index = entries_by_module
                    .get(*module)
                    .expect("graph order only contains lock entries");
                graph.resolved_entry_imports[*entry_index]
                    .iter()
                    .all(|import| {
                        !execution_modules.contains(&import.module)
                            || assigned.contains(&import.module)
                    })
            })
            .cloned()
            .collect::<Vec<_>>();

        if layer.is_empty() {
            break;
        }

        for module in &layer {
            remaining.remove(module);
            assigned.insert(module.clone());
        }
        layers.push(layer);
    }

    layers
}

#[cfg(any(test, feature = "planning-benchmark"))]
const LINEAR_DAG_BENCHMARK_MODULE_COUNT: usize = 4_096;

/// Closed synthetic graph family used by the package-planning release gate.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerifierLinearDagBenchmarkShape {
    Chain4096,
    Wide4096,
    Diamond4096,
}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageVerifierLinearDagBenchmarkShape {
    /// Return the closed scenario component.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Chain4096 => "chain4096",
            Self::Wide4096 => "wide4096",
            Self::Diamond4096 => "diamond4096",
        }
    }

    const fn expected_edges(self) -> u64 {
        match self {
            Self::Chain4096 | Self::Wide4096 => 4_095,
            Self::Diamond4096 => 5_119,
        }
    }

    const fn expected_layers(self) -> u64 {
        match self {
            Self::Chain4096 => 4_096,
            Self::Wide4096 => 2,
            Self::Diamond4096 => 3_072,
        }
    }

    const fn expected_critical_path(self) -> u64 {
        match self {
            Self::Chain4096 => 4_096,
            Self::Wide4096 => 2,
            Self::Diamond4096 => 3_072,
        }
    }

    const fn expected_stream_hash(self) -> &'static str {
        match self {
            Self::Chain4096 => "99e310a352a917a89d175c7e98695d49ef620327142c4fe029cc5aa3b3a3ba7c",
            Self::Wide4096 => "a5ef4fdc1913fb28834d300e0fd812b07a6f4b4792b8b8c73b91eefc2d4b8c64",
            Self::Diamond4096 => "409160e7b1b020f041573867619ec4c9525adadd68e018d4771c8298010956a9",
        }
    }
}

/// Exact complexity counters emitted by the closed planning adapter.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageVerifierLinearDagBenchmarkCounters {
    pub graph_index_constructions: u64,
    pub reverse_list_sort_calls: u64,
    pub forward_vertex_dequeues: u64,
    pub forward_edge_visits: u64,
    pub layer_assignments: u64,
    pub complete_entry_fixed_point_scans: u64,
    pub verified_prefix_record_visits: u64,
    pub critical_path_state_nodes: u64,
    pub path_prefix_clone_elements: u64,
    pub final_reconstructed_path_length: u64,
}

/// Immutable v3 shard inputs and per-layer stream identity.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifierLinearDagBenchmarkShardProfile {
    pub cost_model: PerformancePackageShardCostModel,
    pub memory_model: PerformancePackageShardMemoryModel,
    pub import_weight: u64,
    pub memory_budget_bytes: u64,
    pub worker_stack_bytes: u64,
    pub fixed_worker_bytes: u64,
    pub scratch_multiplier: u64,
    pub requested_jobs: u64,
    pub artifact_bytes_per_module: u64,
    pub term_materialization_bytes_per_worker: u64,
    pub per_worker_bytes: u64,
    pub prepared_shared_bytes: u64,
    pub peak_shared_base_context_bytes: u64,
    pub peak_combined_shared_context_bytes: u64,
    pub minimum_memory_jobs: u64,
    pub estimate_overflowed: bool,
    pub layer_input_sha256: String,
}

/// Closed deterministic observation returned by the planning adapter.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifierLinearDagBenchmarkObservation {
    pub module_count: u64,
    pub edge_count: u64,
    pub selected_count: u64,
    pub layer_count: u64,
    pub critical_path_length: u64,
    pub oracle_match: bool,
    pub shard_profile: PackageVerifierLinearDagBenchmarkShardProfile,
    pub counters: PackageVerifierLinearDagBenchmarkCounters,
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn linear_dag_benchmark_name(index: usize) -> Name {
    Name::from_dotted(format!("Bench.M{index:04x}"))
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn linear_dag_benchmark_import_indexes(
    shape: PackageVerifierLinearDagBenchmarkShape,
    index: usize,
) -> Vec<usize> {
    match shape {
        PackageVerifierLinearDagBenchmarkShape::Chain4096 => {
            index.checked_sub(1).into_iter().collect()
        }
        PackageVerifierLinearDagBenchmarkShape::Wide4096 => {
            if index + 1 == LINEAR_DAG_BENCHMARK_MODULE_COUNT {
                (0..index).collect()
            } else {
                Vec::new()
            }
        }
        PackageVerifierLinearDagBenchmarkShape::Diamond4096 => match index % 4 {
            0 => index.checked_sub(1).into_iter().collect(),
            1 | 2 => vec![index - index % 4],
            3 => vec![index - 2, index - 1],
            _ => unreachable!(),
        },
    }
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn linear_dag_benchmark_lock(shape: PackageVerifierLinearDagBenchmarkShape) -> PackageLockManifest {
    let hash = PackageHash::new([0; 32]);
    let entries = (0..LINEAR_DAG_BENCHMARK_MODULE_COUNT)
        .map(|index| PackageLockEntry {
            module: linear_dag_benchmark_name(index),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(format!("generated/Bench.M{index:04x}.npcert")),
            certificate_file_hash: hash,
            export_hash: hash,
            axiom_report_hash: hash,
            certificate_hash: hash,
            imports: linear_dag_benchmark_import_indexes(shape, index)
                .into_iter()
                .map(|dependency| npa_package::PackageLockImport {
                    module: linear_dag_benchmark_name(dependency),
                    export_hash: hash,
                    certificate_hash: hash,
                })
                .collect(),
            package: None,
            version: None,
        })
        .collect();
    PackageLockManifest {
        schema: npa_package::PACKAGE_LOCK_SCHEMA.to_owned(),
        package: npa_package::PackageId::new("linear-dag-benchmark"),
        version: npa_package::PackageVersion::new("0.0.0"),
        manifest: npa_package::PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: hash,
        },
        entries,
    }
}

#[cfg(test)]
const LINEAR_DAG_BOUNDED_MODULE_COUNT: usize = 4;

#[cfg(test)]
fn linear_dag_bounded_name(logical_index: usize, reverse_names: bool) -> Name {
    let name_index = if reverse_names {
        LINEAR_DAG_BOUNDED_MODULE_COUNT - 1 - logical_index
    } else {
        logical_index
    };
    Name::from_dotted(format!("Bounded.M{name_index}"))
}

#[cfg(test)]
fn linear_dag_bounded_edge_bit(dependent: usize, dependency: usize) -> usize {
    debug_assert!(dependency < dependent);
    dependent * (dependent - 1) / 2 + dependency
}

#[cfg(test)]
fn linear_dag_bounded_lock(edge_mask: u64, reverse_names: bool) -> PackageLockManifest {
    let hash = PackageHash::new([0; 32]);
    let entries = (0..LINEAR_DAG_BOUNDED_MODULE_COUNT)
        .map(|dependent| {
            let module = linear_dag_bounded_name(dependent, reverse_names);
            PackageLockEntry {
                module: module.clone(),
                origin: PackageLockEntryOrigin::Local,
                certificate: PackagePath::new(format!("generated/{}.npcert", module.as_dotted())),
                certificate_file_hash: hash,
                export_hash: hash,
                axiom_report_hash: hash,
                certificate_hash: hash,
                imports: (0..dependent)
                    .filter(|dependency| {
                        edge_mask & (1 << linear_dag_bounded_edge_bit(dependent, *dependency)) != 0
                    })
                    .map(|dependency| npa_package::PackageLockImport {
                        module: linear_dag_bounded_name(dependency, reverse_names),
                        export_hash: hash,
                        certificate_hash: hash,
                    })
                    .collect(),
                package: None,
                version: None,
            }
        })
        .collect();
    PackageLockManifest {
        schema: npa_package::PACKAGE_LOCK_SCHEMA.to_owned(),
        package: npa_package::PackageId::new("linear-dag-bounded-oracle"),
        version: npa_package::PackageVersion::new("0.0.0"),
        manifest: npa_package::PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: hash,
        },
        entries,
    }
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn linear_dag_benchmark_error(message: impl Into<String>) -> PackageVerificationError {
    PackageVerificationError::lock_graph_invalid(format!("linear_dag_benchmark:{}", message.into()))
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn linear_dag_benchmark_stream_hash(stream: &[u8]) -> String {
    use sha2::Digest;
    format!("{:x}", sha2::Sha256::digest(stream))
}

/// Run the production indexed planners over one closed 4,096-node graph.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
pub fn benchmark_package_verifier_linear_dag_planning(
    shape: PackageVerifierLinearDagBenchmarkShape,
    measurement_mode: PerformanceMeasurementMode,
) -> Result<PackageVerifierLinearDagBenchmarkObservation, PackageVerificationError> {
    let lock = linear_dag_benchmark_lock(shape);
    let mut graph_counters = PackageGraphPlanningCounterSummary::default();
    let indexed = npa_package::build_indexed_package_lock_graph_with_planning_counters(
        &lock,
        &mut graph_counters,
    )
    .map_err(indexed_lock_graph_verification_error)?;
    let seed = linear_dag_benchmark_name(LINEAR_DAG_BENCHMARK_MODULE_COUNT - 1);
    let options = PackageVerificationExecutionOptions {
        jobs: 4,
        selected_modules: Some(BTreeSet::from([seed])),
        measurement_mode,
        ..PackageVerificationExecutionOptions::default()
    };
    let selected_bits = indexed
        .index()
        .dependency_closure_with_planning_counters(
            options
                .selected_modules
                .as_ref()
                .expect("closed benchmark always has one seed"),
            &mut graph_counters,
        )
        .map_err(|error| {
            PackageVerificationError::lock_graph_invalid(format!(
                "internal_index_invariant:{}",
                error.invariant()
            ))
        })?;
    let selected = indexed
        .index()
        .topological_entries()
        .iter()
        .filter(|entry| selected_bits[**entry])
        .map(|entry| {
            indexed
                .index()
                .module_by_entry(*entry)
                .expect("validated index contains every entry")
                .clone()
        })
        .collect::<BTreeSet<_>>();
    let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
    let legacy_selected =
        legacy_execution_modules_fixed_point_oracle(&entries, indexed.graph(), &options)?;
    let selected_closure_oracle_match = selected == legacy_selected;
    let layers = indexed
        .index()
        .topological_layers_with_planning_counters(&selected_bits, &mut graph_counters)
        .into_iter()
        .map(|layer| {
            layer
                .into_iter()
                .map(|entry| {
                    indexed
                        .index()
                        .module_by_entry(entry)
                        .expect("validated index contains every entry")
                        .clone()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let legacy_layers =
        legacy_execution_layers_ready_scan_oracle(&entries, indexed.graph(), &selected);
    let layer_oracle_match = layers == legacy_layers;

    static ARTIFACT: [u8; 1] = [0];
    let artifacts = entries
        .iter()
        .map(|(_, entry)| (entry.certificate.clone(), ARTIFACT.as_slice()))
        .collect::<BTreeMap<_, _>>();
    let mut planning =
        PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
    planning.prepared_shared_bytes = 0;
    let mut layer_stream = Vec::new();
    let mut peak_shared = 0u64;
    let mut peak_combined = 0u64;
    let mut minimum_memory_jobs = u64::MAX;
    let mut verifier_counters = PackageVerificationPlanningCounterSummary::default();
    let mut legacy_verified_entries = Vec::<usize>::new();
    let mut shard_oracle_match = true;
    for (layer_index, layer) in layers.iter().enumerate() {
        let runnable = layer
            .iter()
            .map(|module| {
                let entry = indexed
                    .index()
                    .entry_by_module(module)
                    .expect("selected layer module exists in index");
                (entry, &indexed.entries()[entry])
            })
            .collect::<Vec<_>>();
        let plan = plan_fast_verifier_shards_with_state(&runnable, indexed.graph(), &planning, 4)
            .ok_or_else(|| linear_dag_benchmark_error("shard_plan_unavailable"))?;
        let legacy_context_modules = legacy_verified_entries
            .iter()
            .map(|entry| indexed.entries()[*entry].module.clone())
            .collect::<BTreeSet<_>>();
        let legacy_plan = legacy_plan_fast_verifier_shards_prefix_oracle(
            &runnable,
            indexed.graph(),
            &legacy_context_modules,
            legacy_verified_entries
                .iter()
                .map(|entry| &indexed.entries()[*entry].certificate),
            &artifacts,
            planning.prepared_shared_bytes,
            4,
        );
        shard_oracle_match &= legacy_plan.as_ref() == Some(&plan);
        let largest_artifact = plan
            .module_costs
            .values()
            .map(|cost| cost.artifact_bytes)
            .max()
            .unwrap_or(0);
        let available =
            PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1.saturating_sub(plan.combined_shared_bytes);
        minimum_memory_jobs =
            minimum_memory_jobs.min((available / plan.per_worker_bytes.max(1)).max(1));
        peak_shared = peak_shared.max(plan.shared_base_context_bytes);
        peak_combined = peak_combined.max(plan.combined_shared_bytes);
        use std::io::Write as _;
        writeln!(
            layer_stream,
            "{layer_index},{},{},{},{},{},{},{},{},{}",
            runnable.len(),
            plan.shared_base_context_bytes,
            plan.prepared_shared_bytes,
            plan.combined_shared_bytes,
            largest_artifact,
            PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
            plan.per_worker_bytes,
            plan.effective_jobs,
            plan.reduction_reason.measurement().as_str(),
        )
        .expect("writing to a byte vector cannot fail");
        for (entry, _) in runnable {
            planning.record_verified_with_sink(entry, &mut verifier_counters)?;
            legacy_verified_entries.push(entry);
        }
    }
    let layer_input_sha256 = linear_dag_benchmark_stream_hash(&layer_stream);
    if layer_input_sha256 != shape.expected_stream_hash() {
        return Err(linear_dag_benchmark_error(format!(
            "layer_stream_hash:{layer_input_sha256}"
        )));
    }
    let (critical_path_length, critical_path_oracle_match) = if measurement_mode.is_enabled() {
        let observation = package_fast_execution_cost_observation_with_sink(
            &entries,
            indexed.graph(),
            &selected,
            &layers,
            &planning,
            &mut verifier_counters,
        )
        .ok_or_else(|| linear_dag_benchmark_error("critical_path_unavailable"))?;
        let legacy_observation = legacy_package_fast_execution_cost_vector_oracle(
            &entries,
            indexed.graph(),
            &selected,
            &layers,
            &planning,
        )
        .ok_or_else(|| linear_dag_benchmark_error("critical_path_oracle_unavailable"))?;
        (
            observation.critical_path_module_count,
            package_fast_execution_cost_observations_match(&observation, &legacy_observation),
        )
    } else {
        (0, true)
    };
    let oracle_match = selected_closure_oracle_match
        && layer_oracle_match
        && shard_oracle_match
        && critical_path_oracle_match;
    if !oracle_match {
        return Err(linear_dag_benchmark_error(format!(
            "oracle_mismatch:closure={selected_closure_oracle_match},layers={layer_oracle_match},shards={shard_oracle_match},critical_path={critical_path_oracle_match}"
        )));
    }
    let module_count = u64::try_from(indexed.entries().len()).unwrap_or(u64::MAX);
    let edge_count = indexed
        .graph()
        .resolved_entry_imports
        .iter()
        .map(|imports| u64::try_from(imports.len()).unwrap_or(u64::MAX))
        .fold(0u64, u64::saturating_add);
    let selected_count = u64::try_from(selected.len()).unwrap_or(u64::MAX);
    let layer_count = u64::try_from(layers.len()).unwrap_or(u64::MAX);
    let expected_path = if measurement_mode.is_enabled() {
        shape.expected_critical_path()
    } else {
        0
    };
    if module_count != 4_096
        || edge_count != shape.expected_edges()
        || selected_count != 4_096
        || layer_count != shape.expected_layers()
        || critical_path_length != expected_path
        || peak_shared != 4_095
        || peak_combined != 4_095
        || minimum_memory_jobs != 3
        || graph_counters.graph_index_invariant_failures != 0
        || graph_counters.layer_dependency_edge_visits != edge_count
        || graph_counters.reverse_vertex_dequeues != 0
        || graph_counters.reverse_edge_visits != 0
        || graph_counters.provenance_pair_dequeues != 0
        || graph_counters.provenance_edge_visits != 0
        || graph_counters.overflowed
        || verifier_counters.cumulative_verified_updates != selected_count
        || verifier_counters.overflowed
    {
        return Err(linear_dag_benchmark_error("closed_profile_mismatch"));
    }
    let worker_stack_bytes =
        u64::try_from(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES).unwrap_or(u64::MAX);
    let per_worker_bytes = worker_stack_bytes
        .saturating_add(PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1)
        .saturating_add(PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1)
        .saturating_add(PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2);
    Ok(PackageVerifierLinearDagBenchmarkObservation {
        module_count,
        edge_count,
        selected_count,
        layer_count,
        critical_path_length,
        oracle_match,
        shard_profile: PackageVerifierLinearDagBenchmarkShardProfile {
            cost_model: PerformancePackageShardCostModel::FastShardCostV1,
            memory_model: PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention,
            import_weight: PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1,
            memory_budget_bytes: PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
            worker_stack_bytes,
            fixed_worker_bytes: PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1,
            scratch_multiplier: PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1,
            requested_jobs: 4,
            artifact_bytes_per_module: 1,
            term_materialization_bytes_per_worker:
                PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
            per_worker_bytes,
            prepared_shared_bytes: 0,
            peak_shared_base_context_bytes: peak_shared,
            peak_combined_shared_context_bytes: peak_combined,
            minimum_memory_jobs,
            estimate_overflowed: false,
            layer_input_sha256,
        },
        counters: PackageVerifierLinearDagBenchmarkCounters {
            graph_index_constructions: graph_counters.graph_index_constructions,
            reverse_list_sort_calls: graph_counters.reverse_list_sort_calls,
            forward_vertex_dequeues: graph_counters.forward_vertex_dequeues,
            forward_edge_visits: graph_counters.forward_edge_visits,
            layer_assignments: graph_counters.layer_assignments,
            complete_entry_fixed_point_scans: verifier_counters.complete_entry_fixed_point_scans,
            verified_prefix_record_visits: verifier_counters.verified_prefix_record_visits,
            critical_path_state_nodes: verifier_counters.critical_path_state_nodes,
            path_prefix_clone_elements: verifier_counters.path_prefix_clone_elements,
            final_reconstructed_path_length: verifier_counters.final_reconstructed_path_length,
        },
    })
}

#[cfg(all(test, feature = "planning-benchmark"))]
mod linear_dag_benchmark_tests {
    use super::*;

    #[test]
    fn linear_dag_benchmark_generators_are_exact() {
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            assert!(shape.as_str().ends_with("4096"));
            let lock = linear_dag_benchmark_lock(shape);
            assert_eq!(lock.entries.len(), 4_096);
            assert_eq!(
                lock.entries.first().unwrap().module.as_dotted(),
                "Bench.M0000"
            );
            assert_eq!(
                lock.entries.last().unwrap().module.as_dotted(),
                "Bench.M0fff"
            );
            assert!(lock
                .entries
                .windows(2)
                .all(|entries| entries[0].module < entries[1].module));
            let edges = lock
                .entries
                .iter()
                .map(|entry| entry.imports.len())
                .sum::<usize>();
            assert_eq!(u64::try_from(edges).unwrap(), shape.expected_edges());
            for (index, entry) in lock.entries.iter().enumerate() {
                assert!(entry.imports.iter().all(|import| {
                    lock.entries[..index]
                        .iter()
                        .any(|dependency| dependency.module == import.module)
                }));
            }
        }
    }

    #[test]
    fn linear_dag_benchmark_shard_profiles_are_exact() {
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            let observations = [
                PerformanceMeasurementMode::Off,
                PerformanceMeasurementMode::Summary,
                PerformanceMeasurementMode::Detailed,
            ]
            .map(|mode| benchmark_package_verifier_linear_dag_planning(shape, mode).unwrap());
            assert_eq!(observations[0].shard_profile, observations[1].shard_profile);
            assert_eq!(observations[1].shard_profile, observations[2].shard_profile);
            let profile = &observations[0].shard_profile;
            assert_eq!(
                profile.memory_model.as_str(),
                "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
            );
            assert_eq!(profile.term_materialization_bytes_per_worker, 268_435_456);
            assert_eq!(profile.per_worker_bytes, 343_932_932);
            assert_eq!(profile.minimum_memory_jobs, 3);
            assert_eq!(profile.layer_input_sha256, shape.expected_stream_hash());
        }
    }

    #[test]
    fn linear_dag_benchmark_profiles_match_oracles_and_bounds() {
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            for mode in [
                PerformanceMeasurementMode::Off,
                PerformanceMeasurementMode::Summary,
                PerformanceMeasurementMode::Detailed,
            ] {
                let observation =
                    benchmark_package_verifier_linear_dag_planning(shape, mode).unwrap();
                assert!(observation.oracle_match);
                // These are values emitted by operation-owned sinks at the
                // production index, closure, layer, and critical-path sites.
                // The legacy-only fields remain explicit zero oracles.
                assert_eq!(observation.counters.graph_index_constructions, 1);
                assert_eq!(observation.counters.reverse_list_sort_calls, 0);
                assert_eq!(observation.counters.forward_vertex_dequeues, 4_096);
                assert_eq!(
                    observation.counters.forward_edge_visits,
                    shape.expected_edges()
                );
                assert_eq!(observation.counters.layer_assignments, 4_096);
                assert_eq!(observation.counters.complete_entry_fixed_point_scans, 0);
                assert_eq!(observation.counters.verified_prefix_record_visits, 0);
                assert_eq!(observation.counters.path_prefix_clone_elements, 0);
                assert_eq!(
                    observation.counters.critical_path_state_nodes,
                    if mode.is_enabled() { 4_096 } else { 0 }
                );
                assert_eq!(
                    observation.counters.final_reconstructed_path_length,
                    if mode.is_enabled() {
                        shape.expected_critical_path()
                    } else {
                        0
                    }
                );
            }
        }
    }
}

fn execution_layers_for_indexed(
    indexed: &IndexedPackageLockGraph,
    execution_modules: &BTreeSet<Name>,
) -> Vec<Vec<Name>> {
    let mut selected = vec![false; indexed.entries().len()];
    for module in execution_modules {
        if let Some(entry) = indexed.index().entry_by_module(module) {
            selected[entry] = true;
        }
    }
    indexed
        .index()
        .topological_layers(&selected)
        .into_iter()
        .map(|layer| {
            layer
                .into_iter()
                .map(|entry| {
                    indexed
                        .index()
                        .module_by_entry(entry)
                        .expect("validated index contains every entry")
                        .clone()
                })
                .collect()
        })
        .collect()
}

fn blocked_direct_import(
    graph: &PackageLockGraph,
    entry_index: usize,
    blocked_modules: &BTreeSet<Name>,
) -> Option<Name> {
    graph.resolved_entry_imports[entry_index]
        .iter()
        .find(|import| blocked_modules.contains(&import.module))
        .map(|import| import.module.clone())
}

fn package_fast_kernel_policy(validated: &ValidatedPackageManifest) -> AxiomPolicy {
    let package_policy = &validated.manifest().policy;
    if package_policy.allow_custom_axioms {
        AxiomPolicy::normal()
    } else {
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .extend(package_policy.allowed_axioms.iter().cloned());
        policy
    }
}

fn package_reference_checker_policy(
    validated: &ValidatedPackageManifest,
) -> ReferenceCheckerPolicy {
    let package_policy = &validated.manifest().policy;
    ReferenceCheckerPolicy {
        trust_mode: ReferenceTrustMode::HighTrust,
        allowed_axioms: package_policy
            .allowed_axioms
            .iter()
            .map(Name::as_dotted)
            .collect(),
        deny_sorry: true,
        deny_custom_axioms: !package_policy.allow_custom_axioms,
        allow_standard_axiom_exceptions: false,
        supported_core_features: reference_checker_supported_core_features(
            &validated.manifest().checker_profile,
        ),
    }
}

fn reference_checker_supported_core_features(profile: &str) -> Vec<ReferenceCoreFeature> {
    match profile {
        CHECKER_PROFILE_REFERENCE_V0_1 => Vec::new(),
        _ => Vec::new(),
    }
}

fn verify_lock_entry(
    entry_index: usize,
    entry: &PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<(VerifiedModule, PackageVerificationDecodeCacheCounters)> {
    let mut observation = PackageEntryCheckObservation::default();
    let verified = verify_lock_entry_observed(
        entry_index,
        entry,
        artifact_bytes,
        session,
        policy,
        decode_cache_config,
        &mut observation,
    )?;
    Ok((verified, observation.decode_cache_counters))
}

fn verify_lock_entry_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<VerifiedModule> {
    verify_lock_entry_with_context_observed(
        entry_index,
        entry,
        artifact_bytes,
        PackageFastWorkerImportContext::Session(session),
        policy,
        decode_cache_config,
        observation,
    )
}

fn verify_lock_entry_with_context_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<VerifiedModule> {
    let entry_path = format!("entries[{entry_index}]");
    let bytes = artifact_bytes
        .get(&entry.certificate)
        .copied()
        .ok_or_else(|| {
            PackageVerificationError::certificate_artifact_missing(
                format!("{entry_path}.certificate"),
                entry.certificate.as_str(),
            )
        })?;
    verify_lock_entry_bytes_observed(
        entry_index,
        entry,
        bytes,
        import_context,
        policy,
        decode_cache_config,
        observation,
    )
}

fn verify_lock_entry_bytes_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    bytes: &[u8],
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<VerifiedModule> {
    verify_lock_entry_input_observed(
        entry_index,
        entry,
        PackageCertificateInput::Raw { bytes },
        import_context,
        policy,
        decode_cache_config,
        observation,
    )
}

fn verify_lock_entry_input_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    input: PackageCertificateInput<'_>,
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<VerifiedModule> {
    let entry_path = format!("entries[{entry_index}]");
    let bytes = input.bytes();
    observation.observe_certificate_bytes(bytes);
    observation.certificate_file_hash_reused = input.reuses_file_hash();
    let actual_file_hash = input.observed_file_hash();
    if entry.certificate_file_hash != actual_file_hash {
        return Err(PackageVerificationError::certificate_file_hash_mismatch(
            format!("{entry_path}.certificate_file_hash"),
            entry.certificate_file_hash,
            actual_file_hash,
        ));
    }

    let verified = if let Some(cert) = input.retained_decoded() {
        observation.prepared_artifact_reused = true;
        observation.observe_retained_certificate(&entry.module, cert);
        if cert.header().module != entry.module {
            return Err(PackageVerificationError::certificate_module_mismatch(
                format!("{entry_path}.certificate"),
                entry.module.as_dotted(),
                cert.header().module.as_dotted(),
            ));
        }
        check_entry_hash_values(entry_index, entry, cert.hashes())?;
        match import_context {
            PackageFastWorkerImportContext::Session(session) => {
                verify_retained_decoded_module_cert_with_observations(
                    cert,
                    bytes,
                    session,
                    policy,
                    observation.certificate_observation_sinks(),
                )
            }
            PackageFastWorkerImportContext::Borrowed {
                resolved_imports,
                verified_modules_by_module,
            } => {
                let imports = exact_fast_import_refs(resolved_imports, verified_modules_by_module);
                verify_retained_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
                    cert,
                    bytes,
                    &imports,
                    policy,
                    KernelExecutionOptions::default(),
                    observation.certificate_observation_sinks(),
                )
            }
        }
    } else {
        if input.is_owned() {
            observation.owned_artifact_full_decodes = observation
                .owned_artifact_full_decodes
                .saturating_add(1);
        }
        let cert = decode_fast_certificate_with_cache(
            entry_index,
            entry,
            bytes,
            actual_file_hash,
            decode_cache_config,
            observation,
        )?;
        observation.observe_fast_certificate(&entry.module, &cert);
        if cert.header().module != entry.module {
            return Err(PackageVerificationError::certificate_module_mismatch(
                format!("{entry_path}.certificate"),
                entry.module.as_dotted(),
                cert.header().module.as_dotted(),
            ));
        }
        check_entry_hashes(entry_index, entry, &cert)?;
        match import_context {
            PackageFastWorkerImportContext::Session(session) => {
                verify_decoded_module_cert_with_observations(
                    &cert,
                    bytes,
                    session,
                    policy,
                    observation.certificate_observation_sinks(),
                )
            }
            PackageFastWorkerImportContext::Borrowed {
                resolved_imports,
                verified_modules_by_module,
            } => {
                let imports = exact_fast_import_refs(resolved_imports, verified_modules_by_module);
                verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
                    &cert,
                    bytes,
                    &imports,
                    policy,
                    KernelExecutionOptions::default(),
                    observation.certificate_observation_sinks(),
                )
            }
        }
    }
    .map_err(|source| {
        PackageVerificationError::verify_failed(format!("{entry_path}.certificate"), source)
    })?;
    if verified.module() != &entry.module {
        return Err(PackageVerificationError::certificate_module_mismatch(
            format!("{entry_path}.certificate"),
            entry.module.as_dotted(),
            verified.module().as_dotted(),
        ));
    }
    let actual_export_hash = PackageHash::from(verified.export_hash());
    if actual_export_hash != entry.export_hash {
        return Err(PackageVerificationError::export_hash_mismatch(
            format!("{entry_path}.export_hash"),
            entry.export_hash,
            actual_export_hash,
        ));
    }
    let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
    if actual_certificate_hash != entry.certificate_hash {
        return Err(PackageVerificationError::certificate_hash_mismatch(
            format!("{entry_path}.certificate_hash"),
            entry.certificate_hash,
            actual_certificate_hash,
        ));
    }

    Ok(verified)
}

fn exact_fast_import_refs<'a>(
    resolved_imports: &[PackageLockResolvedImport],
    verified_modules_by_module: &'a BTreeMap<Name, PackageVerifiedModuleRecord>,
) -> Vec<&'a VerifiedModule> {
    resolved_imports
        .iter()
        .filter_map(|resolved| {
            verified_modules_by_module
                .get(&resolved.module)
                .filter(|record| {
                    record.module == resolved.module
                        && record.export_hash == resolved.export_hash
                        && record.certificate_hash == resolved.certificate_hash
                })
                .map(|record| &record.verified_module)
        })
        .collect()
}

#[derive(Clone, Copy)]
struct PackageReferenceEntryContext<'a> {
    lock: &'a PackageLockManifest,
    entries: &'a [(usize, &'a PackageLockEntry)],
    artifact_bytes: &'a BTreeMap<PackagePath, &'a [u8]>,
    artifact_file_hashes: Option<&'a BTreeMap<PackagePath, PackageHash>>,
    checked_by_module: &'a BTreeMap<Name, ReferenceCheckedModule>,
    policy: &'a ReferenceCheckerPolicy,
    decode_cache_config: &'a PackageVerificationDecodeCacheConfig,
}

#[derive(Clone, Copy)]
struct PackageReferenceEntryBytesContext<'a> {
    lock: &'a PackageLockManifest,
    entries: &'a [(usize, &'a PackageLockEntry)],
    checked_by_module: &'a BTreeMap<Name, ReferenceCheckedModule>,
    policy: &'a ReferenceCheckerPolicy,
    decode_cache_config: &'a PackageVerificationDecodeCacheConfig,
}

fn verify_reference_lock_entry(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    context: PackageReferenceEntryContext<'_>,
) -> PackageVerificationResult<(
    ReferenceCheckedModule,
    PackageVerificationDecodeCacheCounters,
)> {
    let mut observation = PackageEntryCheckObservation::default();
    let checked = verify_reference_lock_entry_observed(
        entry_index,
        entry,
        resolved_imports,
        context,
        &mut observation,
    )?;
    Ok((checked, observation.decode_cache_counters))
}

fn verify_reference_lock_entry_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    context: PackageReferenceEntryContext<'_>,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<ReferenceCheckedModule> {
    let entry_path = format!("entries[{entry_index}]");
    let bytes = context
        .artifact_bytes
        .get(&entry.certificate)
        .copied()
        .ok_or_else(|| {
            PackageVerificationError::certificate_artifact_missing(
                format!("{entry_path}.certificate"),
                entry.certificate.as_str(),
            )
        })?;
    verify_reference_lock_entry_bytes_observed(
        entry_index,
        entry,
        resolved_imports,
        bytes,
        context
            .artifact_file_hashes
            .and_then(|hashes| hashes.get(&entry.certificate).copied()),
        PackageReferenceEntryBytesContext {
            lock: context.lock,
            entries: context.entries,
            checked_by_module: context.checked_by_module,
            policy: context.policy,
            decode_cache_config: context.decode_cache_config,
        },
        observation,
    )
}

fn verify_reference_lock_entry_bytes_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    bytes: &[u8],
    precomputed_file_hash: Option<PackageHash>,
    context: PackageReferenceEntryBytesContext<'_>,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<ReferenceCheckedModule> {
    let entry_path = format!("entries[{entry_index}]");
    observation.observe_certificate_bytes(bytes);
    let actual_file_hash = precomputed_file_hash.unwrap_or_else(|| package_file_hash(bytes));
    if entry.certificate_file_hash != actual_file_hash {
        return Err(PackageVerificationError::certificate_file_hash_mismatch(
            format!("{entry_path}.certificate_file_hash"),
            entry.certificate_file_hash,
            actual_file_hash,
        ));
    }

    let owner_header = decode_module_cert_header(bytes).map_err(|source| {
        PackageVerificationError::certificate_decode_failed(
            format!("{entry_path}.certificate"),
            format!("{source:?}"),
        )
    })?;

    let imports = reference_import_store_with_cache_observed(
        entry_index,
        entry,
        resolved_imports,
        PackageReferenceImportContext {
            lock: context.lock,
            entries: context.entries,
            checked_by_module: context.checked_by_module,
            owner_header: &owner_header,
            config: context.decode_cache_config,
        },
        &mut observation.decode_cache_counters,
        observation.package_payload.as_mut(),
    )?;
    let check_result = if observation.measurement_mode.is_enabled() {
        let declaration_detail_limit = if observation.measurement_mode.is_detailed() {
            PERFORMANCE_DECLARATION_DETAIL_LIMIT
        } else {
            0
        };
        let (result, check_observation) = check_certificate_with_observation(
            bytes,
            imports.as_ref(),
            context.policy,
            declaration_detail_limit,
        );
        if check_observation.certificate_decoded {
            observation.physical_certificate_decodes =
                observation.physical_certificate_decodes.saturating_add(1);
            observation.observe_reference_certificate(&entry.module, &check_observation);
        }
        result
    } else {
        check_certificate(bytes, imports.as_ref(), context.policy)
    };
    let checked = match check_result {
        ReferenceCheckResult::Checked(checked) => checked,
        ReferenceCheckResult::Rejected(error) => {
            return Err(PackageVerificationError::reference_checker_rejected(
                format!("{entry_path}.certificate"),
                error,
            ));
        }
    };

    let actual_module = reference_name_to_package_name(checked.module());
    if actual_module != entry.module {
        return Err(PackageVerificationError::certificate_module_mismatch(
            format!("{entry_path}.certificate"),
            entry.module.as_dotted(),
            actual_module.as_dotted(),
        ));
    }
    let actual_export_hash = PackageHash::from(*checked.export_hash());
    if actual_export_hash != entry.export_hash {
        return Err(PackageVerificationError::export_hash_mismatch(
            format!("{entry_path}.export_hash"),
            entry.export_hash,
            actual_export_hash,
        ));
    }
    let actual_axiom_report_hash = PackageHash::from(*checked.axiom_report_hash());
    if actual_axiom_report_hash != entry.axiom_report_hash {
        return Err(PackageVerificationError::axiom_report_hash_mismatch(
            format!("{entry_path}.axiom_report_hash"),
            entry.axiom_report_hash,
            actual_axiom_report_hash,
        ));
    }
    let actual_certificate_hash = PackageHash::from(*checked.certificate_hash());
    if actual_certificate_hash != entry.certificate_hash {
        return Err(PackageVerificationError::certificate_hash_mismatch(
            format!("{entry_path}.certificate_hash"),
            entry.certificate_hash,
            actual_certificate_hash,
        ));
    }

    Ok(checked)
}

fn check_entry_hashes(
    entry_index: usize,
    entry: &PackageLockEntry,
    cert: &npa_cert::ModuleCert,
) -> PackageVerificationResult<()> {
    check_entry_hash_values(entry_index, entry, cert.hashes())
}

fn check_entry_hash_values(
    entry_index: usize,
    entry: &PackageLockEntry,
    hashes: &ModuleHashes,
) -> PackageVerificationResult<()> {
    let entry_path = format!("entries[{entry_index}]");
    let actual_export_hash = PackageHash::from(hashes.export_hash);
    if entry.export_hash != actual_export_hash {
        return Err(PackageVerificationError::export_hash_mismatch(
            format!("{entry_path}.export_hash"),
            entry.export_hash,
            actual_export_hash,
        ));
    }
    let actual_axiom_report_hash = PackageHash::from(hashes.axiom_report_hash);
    if entry.axiom_report_hash != actual_axiom_report_hash {
        return Err(PackageVerificationError::axiom_report_hash_mismatch(
            format!("{entry_path}.axiom_report_hash"),
            entry.axiom_report_hash,
            actual_axiom_report_hash,
        ));
    }
    let actual_certificate_hash = PackageHash::from(hashes.certificate_hash);
    if entry.certificate_hash != actual_certificate_hash {
        return Err(PackageVerificationError::certificate_hash_mismatch(
            format!("{entry_path}.certificate_hash"),
            entry.certificate_hash,
            actual_certificate_hash,
        ));
    }

    Ok(())
}

fn reference_name_to_package_name(name: &ReferenceModuleName) -> Name {
    Name(name.components().to_vec())
}

fn package_reference_checker_reason(
    source: &ReferenceCheckError,
) -> PackageVerificationErrorReason {
    if source.kind == ReferenceCheckErrorKind::UnsupportedCoreFeature
        || source.reason == Some(ReferenceCheckReason::UnsupportedCoreFeature)
    {
        return PackageVerificationErrorReason::UnsupportedCoreFeature;
    }
    if matches!(
        source.reason,
        Some(ReferenceCheckReason::ForbiddenAxiom | ReferenceCheckReason::SorryDenied)
    ) {
        return PackageVerificationErrorReason::AxiomPolicyRejected;
    }
    if source.kind == ReferenceCheckErrorKind::AxiomPolicy {
        return PackageVerificationErrorReason::AxiomPolicyRejected;
    }
    PackageVerificationErrorReason::ReferenceCheckerRejected
}

fn reference_checker_error_details(
    source: &ReferenceCheckError,
) -> PackageVerificationCheckerError {
    PackageVerificationCheckerError {
        checker: "npa-checker-ref".to_owned(),
        kind: reference_check_error_kind_code(source.kind).to_owned(),
        section: Some(reference_certificate_section_code(source.section).to_owned()),
        offset: Some(source.offset),
        reason_code: source
            .reason
            .map(reference_check_reason_code)
            .map(str::to_owned),
    }
}

fn reference_check_error_kind_code(kind: ReferenceCheckErrorKind) -> &'static str {
    match kind {
        ReferenceCheckErrorKind::EmptyCertificate => "empty_certificate",
        ReferenceCheckErrorKind::MalformedCertificate => "malformed_certificate",
        ReferenceCheckErrorKind::HashMismatch => "hash_mismatch",
        ReferenceCheckErrorKind::ImportResolution => "import_resolution",
        ReferenceCheckErrorKind::AxiomReportMismatch => "axiom_report_mismatch",
        ReferenceCheckErrorKind::AxiomPolicy => "axiom_policy",
        ReferenceCheckErrorKind::TypeCheck => "type_check",
        ReferenceCheckErrorKind::UnsupportedSkeleton => "unsupported_skeleton",
        ReferenceCheckErrorKind::UnsupportedCoreFeature => "unsupported_core_feature",
    }
}

fn reference_certificate_section_code(section: ReferenceCertificateSection) -> &'static str {
    match section {
        ReferenceCertificateSection::HeaderFormat => "header_format",
        ReferenceCertificateSection::HeaderCoreSpec => "header_core_spec",
        ReferenceCertificateSection::HeaderModule => "header_module",
        ReferenceCertificateSection::Imports => "imports",
        ReferenceCertificateSection::NameTable => "name_table",
        ReferenceCertificateSection::LevelTable => "level_table",
        ReferenceCertificateSection::TermTable => "term_table",
        ReferenceCertificateSection::Declarations => "declarations",
        ReferenceCertificateSection::ExportBlock => "export_block",
        ReferenceCertificateSection::AxiomReport => "axiom_report",
        ReferenceCertificateSection::Hashes => "hashes",
        ReferenceCertificateSection::ImportStore => "import_store",
        ReferenceCertificateSection::FullCertificate => "full_certificate",
    }
}

fn reference_check_reason_code(reason: ReferenceCheckReason) -> &'static str {
    match reason {
        ReferenceCheckReason::UnexpectedEof => "unexpected_eof",
        ReferenceCheckReason::NonCanonicalUvar => "non_canonical_uvar",
        ReferenceCheckReason::UvarOverflow => "uvar_overflow",
        ReferenceCheckReason::LengthOverflow => "length_overflow",
        ReferenceCheckReason::UnknownTag { .. } => "unknown_tag",
        ReferenceCheckReason::InvalidUtf8 => "invalid_utf8",
        ReferenceCheckReason::FormatMismatch => "format_mismatch",
        ReferenceCheckReason::CoreSpecMismatch => "core_spec_mismatch",
        ReferenceCheckReason::EmptyModuleName => "empty_module_name",
        ReferenceCheckReason::EmptyModuleNameComponent => "empty_module_name_component",
        ReferenceCheckReason::DottedNameComponent => "dotted_name_component",
        ReferenceCheckReason::InvalidNameComponent => "invalid_name_component",
        ReferenceCheckReason::DanglingReference => "dangling_reference",
        ReferenceCheckReason::NonCanonicalOrder => "non_canonical_order",
        ReferenceCheckReason::DuplicateName => "duplicate_name",
        ReferenceCheckReason::DuplicateDeclarationName => "duplicate_declaration_name",
        ReferenceCheckReason::ReservedCorePrimitive => "reserved_core_primitive",
        ReferenceCheckReason::DuplicateImport => "duplicate_import",
        ReferenceCheckReason::ImportCycle => "import_cycle",
        ReferenceCheckReason::NonNormalizedLevel => "non_normalized_level",
        ReferenceCheckReason::NonNormalizedTerm => "non_normalized_term",
        ReferenceCheckReason::UnusedTableEntry => "unused_table_entry",
        ReferenceCheckReason::TrailingBytes => "trailing_bytes",
        ReferenceCheckReason::SourceInputForbidden => "source_input_forbidden",
        ReferenceCheckReason::MissingImport => "missing_import",
        ReferenceCheckReason::ImportExportHashMismatch => "import_export_hash_mismatch",
        ReferenceCheckReason::MissingImportCertificateHash => "missing_import_certificate_hash",
        ReferenceCheckReason::ImportCertificateHashMismatch => "import_certificate_hash_mismatch",
        ReferenceCheckReason::UncheckedImport => "unchecked_import",
        ReferenceCheckReason::UnknownReference => "unknown_reference",
        ReferenceCheckReason::UnsupportedCoreFeature => "unsupported_core_feature",
        ReferenceCheckReason::BadUniverseArity => "bad_universe_arity",
        ReferenceCheckReason::DuplicateUniverseParam => "duplicate_universe_param",
        ReferenceCheckReason::DuplicateUniverseConstraint => "duplicate_universe_constraint",
        ReferenceCheckReason::UnresolvedMetavariable => "unresolved_metavariable",
        ReferenceCheckReason::UnsupportedUniverseConstraint => "unsupported_universe_constraint",
        ReferenceCheckReason::ConstrainedExportRequiresFormatUpgrade => {
            "constrained_export_requires_format_upgrade"
        }
        ReferenceCheckReason::UnsatisfiableUniverseConstraints => {
            "unsatisfiable_universe_constraints"
        }
        ReferenceCheckReason::UniverseConstraintViolation => "universe_constraint_violation",
        ReferenceCheckReason::InvalidBVar => "invalid_bvar",
        ReferenceCheckReason::ExpectedSort => "expected_sort",
        ReferenceCheckReason::ExpectedFunction => "expected_function",
        ReferenceCheckReason::TypeMismatch => "type_mismatch",
        ReferenceCheckReason::ResourceLimit => "resource_limit",
        ReferenceCheckReason::BadConstructorResult => "bad_constructor_result",
        ReferenceCheckReason::ConstructorUniverseBoundViolation => {
            "constructor_universe_bound_violation"
        }
        ReferenceCheckReason::NonPositiveOccurrence => "non_positive_occurrence",
        ReferenceCheckReason::BadRecursorRule => "bad_recursor_rule",
        ReferenceCheckReason::BadRecursorParam => "bad_recursor_param",
        ReferenceCheckReason::BadRecursorMotive => "bad_recursor_motive",
        ReferenceCheckReason::BadRecursorMajor => "bad_recursor_major",
        ReferenceCheckReason::BadRecursorMinor => "bad_recursor_minor",
        ReferenceCheckReason::BadRecursorResult => "bad_recursor_result",
        ReferenceCheckReason::BadRecursorType => "bad_recursor_type",
        ReferenceCheckReason::HashMismatch { .. } => "hash_mismatch",
        ReferenceCheckReason::AxiomReportMismatch => "axiom_report_mismatch",
        ReferenceCheckReason::SorryDenied => "sorry_denied",
        ReferenceCheckReason::ForbiddenAxiom => "forbidden_axiom",
        ReferenceCheckReason::WrongReferenceKind => "wrong_reference_kind",
        ReferenceCheckReason::TargetNotEarlier => "target_not_earlier",
        ReferenceCheckReason::TargetNotOpaque => "target_not_opaque",
        ReferenceCheckReason::InterfaceHashMismatch => "interface_hash_mismatch",
        ReferenceCheckReason::CertificateHashMismatch => "certificate_hash_mismatch",
        ReferenceCheckReason::MissingImplementationDependency => {
            "missing_implementation_dependency"
        }
        ReferenceCheckReason::SurplusImplementationDependency => {
            "surplus_implementation_dependency"
        }
        ReferenceCheckReason::ReferenceCheckerBodyUnimplemented => {
            "reference_checker_body_unimplemented"
        }
    }
}

fn module_result(
    entry: &PackageLockEntry,
    status: PackageModuleVerificationStatus,
    error: Option<PackageVerificationError>,
    checker_mode: PackageVerificationMode,
    certificate_bytes: Option<&[u8]>,
) -> PackageModuleVerificationResult {
    let pair = certificate_bytes.and_then(|bytes| decode_module_cert_header(bytes).ok());
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status,
        evidence: PackageModuleVerificationEvidence::LiveChecker,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        certificate_format: pair.as_ref().map(|header| header.format.clone()),
        core_spec: pair.map(|header| header.core_spec),
        error,
    }
}

fn module_result_for_input(
    entry: &PackageLockEntry,
    status: PackageModuleVerificationStatus,
    error: Option<PackageVerificationError>,
    checker_mode: PackageVerificationMode,
    input: PackageCertificateInput<'_>,
) -> PackageModuleVerificationResult {
    let retained_header = input.retained_header();
    let decoded_fallback = retained_header
        .is_none()
        .then(|| decode_module_cert_header(input.bytes()).ok())
        .flatten();
    let header = retained_header.or(decoded_fallback.as_ref());
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status,
        evidence: PackageModuleVerificationEvidence::LiveChecker,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        certificate_format: header.map(|header| header.format.clone()),
        core_spec: header.map(|header| header.core_spec.clone()),
        error,
    }
}

fn prepared_artifact_input<'a>(
    artifacts: &'a PreparedPackageArtifacts,
    entry_index: usize,
    entry: &PackageLockEntry,
) -> PackageVerificationResult<PackageCertificateInput<'a>> {
    match artifacts.get(&entry.certificate) {
        Some(PreparedPackageArtifactView::Hashed(artifact)) => {
            Ok(PackageCertificateInput::Hashed {
                bytes: artifact.bytes(),
                file_hash: artifact.file_hash(),
            })
        }
        Some(PreparedPackageArtifactView::Prepared(artifact)) => {
            Ok(PackageCertificateInput::Prepared { artifact })
        }
        None => Err(PackageVerificationError::certificate_artifact_missing(
            format!("entries[{entry_index}].certificate"),
            entry.certificate.as_str(),
        )),
    }
}

fn release_prepared_artifact(
    artifacts: &mut PreparedPackageArtifacts,
    entry: &PackageLockEntry,
    reason: PreparedArtifactReleaseReason,
) -> PackageVerificationResult<()> {
    match artifacts.release_decoded(&entry.certificate, reason) {
        PreparedArtifactRelease::Charged { .. }
        | PreparedArtifactRelease::RawFallbackTransition
        | PreparedArtifactRelease::AlreadyRaw => Ok(()),
        PreparedArtifactRelease::NotFound => {
            Err(PackageVerificationError::certificate_artifact_missing(
                "artifacts",
                entry.certificate.as_str(),
            ))
        }
    }
}

fn observe_owned_artifact_full_decodes(
    observation: &mut PackageCertificateArtifactObservation,
    count: u64,
) {
    let (sum, overflowed) = observation.artifact_full_decodes.overflowing_add(count);
    observation.artifact_full_decodes = if overflowed { u64::MAX } else { sum };
    observation.overflowed |= overflowed;
}

fn cached_module_result(
    entry: &PackageLockEntry,
    checker_mode: PackageVerificationMode,
    evidence: PackageModuleVerificationEvidence,
    certificate_bytes: Option<&[u8]>,
) -> PackageModuleVerificationResult {
    let pair = certificate_bytes.and_then(|bytes| decode_module_cert_header(bytes).ok());
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status: PackageModuleVerificationStatus::Passed,
        evidence,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        certificate_format: pair.as_ref().map(|header| header.format.clone()),
        core_spec: pair.map(|header| header.core_spec),
        error: None,
    }
}

fn cached_module_result_for_input(
    entry: &PackageLockEntry,
    checker_mode: PackageVerificationMode,
    evidence: PackageModuleVerificationEvidence,
    input: PackageCertificateInput<'_>,
) -> PackageModuleVerificationResult {
    let retained_header = input.retained_header();
    let decoded_fallback = retained_header
        .is_none()
        .then(|| decode_module_cert_header(input.bytes()).ok())
        .flatten();
    let header = retained_header.or(decoded_fallback.as_ref());
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status: PackageModuleVerificationStatus::Passed,
        evidence,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        certificate_format: header.map(|header| header.format.clone()),
        core_spec: header.map(|header| header.core_spec.clone()),
        error: None,
    }
}

fn local_audit_cache_live_modules(
    indexed: &IndexedPackageLockGraph,
    local_cache_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<BTreeSet<Name>> {
    local_audit_cache_live_modules_with_sink(indexed, local_cache_hits, dirty_modules, &mut ())
}

trait LocalAuditLivePlanningCounterSink {
    fn reverse_vertex_dequeued(&mut self) {}
    fn reverse_edges_visited(&mut self, _count: usize) {}
    fn forward_vertex_dequeued(&mut self) {}
    fn forward_edges_visited(&mut self, _count: usize) {}
}

impl LocalAuditLivePlanningCounterSink for () {}

#[cfg(any(test, feature = "planning-benchmark"))]
impl LocalAuditLivePlanningCounterSink for PackageGraphPlanningCounterSummary {
    fn reverse_vertex_dequeued(&mut self) {
        let (next, overflowed) = self.reverse_vertex_dequeues.overflowing_add(1);
        self.reverse_vertex_dequeues = if overflowed { u64::MAX } else { next };
        self.overflowed |= overflowed;
    }

    fn reverse_edges_visited(&mut self, count: usize) {
        let addend = u64::try_from(count).unwrap_or(u64::MAX);
        let (next, overflowed) = self.reverse_edge_visits.overflowing_add(addend);
        self.reverse_edge_visits = if overflowed { u64::MAX } else { next };
        self.overflowed |= overflowed || (addend == u64::MAX && count != usize::MAX);
    }

    fn forward_vertex_dequeued(&mut self) {
        let (next, overflowed) = self.forward_vertex_dequeues.overflowing_add(1);
        self.forward_vertex_dequeues = if overflowed { u64::MAX } else { next };
        self.overflowed |= overflowed;
    }

    fn forward_edges_visited(&mut self, count: usize) {
        let addend = u64::try_from(count).unwrap_or(u64::MAX);
        let (next, overflowed) = self.forward_edge_visits.overflowing_add(addend);
        self.forward_edge_visits = if overflowed { u64::MAX } else { next };
        self.overflowed |= overflowed || (addend == u64::MAX && count != usize::MAX);
    }
}

fn local_audit_cache_live_modules_with_sink<S: LocalAuditLivePlanningCounterSink>(
    indexed: &IndexedPackageLockGraph,
    local_cache_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
    counters: &mut S,
) -> PackageVerificationResult<BTreeSet<Name>> {
    let local_cache_hits = local_cache_hits.into_iter().collect::<BTreeSet<_>>();
    let dirty_modules = dirty_modules.into_iter().collect::<BTreeSet<_>>();
    for module in &dirty_modules {
        if indexed.index().entry_by_module(module).is_none() {
            return Err(PackageVerificationError::selected_module_missing(module));
        }
    }
    let mut live = vec![false; indexed.entries().len()];
    for (entry_index, entry) in indexed.entries().iter().enumerate() {
        live[entry_index] = !local_cache_hits.contains(&entry.module);
    }
    let mut reverse_visited = vec![false; indexed.entries().len()];
    let mut reverse_pending = Vec::with_capacity(dirty_modules.len());
    for dirty in &dirty_modules {
        let entry = indexed
            .index()
            .entry_by_module(dirty)
            .expect("dirty module membership was checked above");
        live[entry] = true;
        reverse_visited[entry] = true;
        reverse_pending.push(entry);
    }
    while let Some(entry) = reverse_pending.pop() {
        counters.reverse_vertex_dequeued();
        let dependents = indexed
            .index()
            .reverse_dependencies(entry)
            .expect("validated index contains every reverse-adjacency slot");
        counters.reverse_edges_visited(dependents.len());
        for dependent in dependents {
            live[*dependent] = true;
            if !reverse_visited[*dependent] {
                reverse_visited[*dependent] = true;
                reverse_pending.push(*dependent);
            }
        }
    }
    let mut forward_visited = vec![false; indexed.entries().len()];
    let mut forward_pending = indexed
        .index()
        .topological_entries()
        .iter()
        .copied()
        .filter(|entry_index| live[*entry_index])
        .collect::<Vec<_>>();
    while let Some(entry) = forward_pending.pop() {
        if forward_visited[entry] {
            continue;
        }
        forward_visited[entry] = true;
        counters.forward_vertex_dequeued();
        let dependencies = indexed
            .index()
            .dependencies(entry)
            .expect("validated index contains every dependency-adjacency slot");
        counters.forward_edges_visited(dependencies.len());
        for dependency in dependencies {
            live[*dependency] = true;
            if !forward_visited[*dependency] {
                forward_pending.push(*dependency);
            }
        }
    }
    Ok(indexed
        .index()
        .topological_entries()
        .iter()
        .copied()
        .filter(|entry_index| live[*entry_index])
        .map(|entry_index| {
            indexed
                .index()
                .module_by_entry(entry_index)
                .expect("validated index contains every module")
                .clone()
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        path::{Path, PathBuf},
        sync::{Mutex, MutexGuard},
    };

    use npa_cert::{
        build_module_cert, encode_module_cert, term_hash, CoreModule, DeclPayload, TermNode,
    };
    use npa_kernel::{Decl, Expr, Level};
    use npa_package::{
        build_package_lock_and_snapshot_owned_artifacts, build_package_lock_from_artifacts,
        package_audit_disk_memo_key, package_audit_disk_memo_key_input,
        package_audit_process_memo_key, package_reference_summary_cache_key,
        package_reference_summary_cache_key_input, parse_manifest_str, parse_package_lock_json,
        validate_manifest, OwnedPackageLockArtifact, PackageArtifactPreparationObservation,
        PackageId, PackageLockArtifact, PackageLockErrorKind, PackageLockErrorReason,
        PackageLockManifest, PackageManifest, PackageModule, PackagePath, PackagePolicy,
        PackageVersion, PreparedArtifactObservationMode, PreparedArtifactRetentionPolicy,
        PreparedPackageArtifacts, ValidatedPackageManifest, CERTIFICATE_FORMAT_CANONICAL_V0_1,
        CORE_SPEC_V0_1, KERNEL_PROFILE_V0_1, PACKAGE_MANIFEST_SCHEMA,
    };
    use sha2::{Digest, Sha256};

    use crate::independent_checker::{
        independent_checker_machine_check_request_hash,
        parse_independent_checker_import_lock_manifest,
        parse_independent_checker_machine_check_request,
        parse_independent_checker_request_store_manifest, IndependentCheckerAllowlistEntry,
        IndependentCheckerRunnerAxiomPolicy, IndependentCheckerRunnerBudget,
        IndependentCheckerRunnerImportPolicy, IndependentCheckerRunnerPolicy,
        IndependentCheckerTrustMode,
    };

    use super::*;

    const PACKAGE_FAST_VERIFIER_TEST_STACK_BYTES: usize = 64 * 1024 * 1024;

    fn unique_import_context_cache_policy_hash(tag: u8) -> PackageHash {
        let unique = NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
        let mut hash = test_hash(tag);
        hash[..std::mem::size_of::<usize>()].copy_from_slice(&unique.to_be_bytes());
        hash[8..12].copy_from_slice(&std::process::id().to_be_bytes());
        PackageHash::new(hash)
    }

    #[cfg(unix)]
    #[test]
    fn import_context_cache_cleanup_is_disabled_and_preserves_every_entry() {
        use std::os::unix::fs::symlink;

        let root = std::env::temp_dir().join(format!(
            "npa-import-context-cleanup-{}-{}",
            std::process::id(),
            NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir_all(&root).unwrap();
        let root = fs::canonicalize(root).unwrap();
        let parent = NoFollowCacheDirectory::open_absolute(&root, false).unwrap();
        let managed_name = OsStr::new("managed");
        let managed = parent.open_directory(managed_name, true).unwrap();
        let entry =
            OsStr::new("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json");
        managed
            .write_atomic(OsStr::new("temporary"), entry, b"{}")
            .unwrap();
        let collision = managed
            .write_atomic(OsStr::new("temporary-collision"), entry, b"changed")
            .expect_err("cache publication must never replace an existing name");
        assert_eq!(collision.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(fs::read(root.join("managed").join(entry)).unwrap(), b"{}");
        assert_eq!(
            fs::read(root.join("managed/temporary-collision")).unwrap(),
            b"changed"
        );
        fs::write(root.join("managed/unknown"), b"sentinel").unwrap();
        assert!(parent
            .remove_flat_managed_cache_directory(managed_name)
            .is_err());
        assert_eq!(fs::read(root.join("managed/unknown")).unwrap(), b"sentinel");
        assert!(root.join("managed").join(entry).exists());

        let error = parent
            .remove_flat_managed_cache_directory(managed_name)
            .expect_err("online cleanup must preserve even a closed managed cache");
        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
        assert!(root.join("managed").join(entry).exists());
        assert_eq!(fs::read(root.join("managed/unknown")).unwrap(), b"sentinel");

        assert!(symlink(root.join("managed"), root.join("managed-link")).is_ok());
        assert!(parent
            .remove_flat_managed_cache_directory(OsStr::new("managed-link"))
            .is_err());
        assert_eq!(fs::read(root.join("managed/unknown")).unwrap(), b"sentinel");
    }

    #[test]
    fn linear_dag_local_audit_live_reuses_one_index_and_counted_adjacency() {
        #[derive(Default)]
        struct Counters {
            reverse_vertex_dequeues: u64,
            reverse_edge_visits: u64,
            forward_vertex_dequeues: u64,
            forward_edge_visits: u64,
        }
        impl LocalAuditLivePlanningCounterSink for Counters {
            fn reverse_vertex_dequeued(&mut self) {
                self.reverse_vertex_dequeues += 1;
            }
            fn reverse_edges_visited(&mut self, count: usize) {
                self.reverse_edge_visits += u64::try_from(count).unwrap();
            }
            fn forward_vertex_dequeued(&mut self) {
                self.forward_vertex_dequeues += 1;
            }
            fn forward_edges_visited(&mut self, count: usize) {
                self.forward_edge_visits += u64::try_from(count).unwrap();
            }
        }
        let lock = proof_lock();
        let mut counters = Counters::default();
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let cache_hits = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let dirty = indexed
            .index()
            .topological_entries()
            .first()
            .map(|entry| indexed.entries()[*entry].module.clone())
            .into_iter();

        let live =
            local_audit_cache_live_modules_with_sink(&indexed, cache_hits, dirty, &mut counters)
                .unwrap();

        assert!(!live.is_empty());
        assert!(counters.reverse_vertex_dequeues > 0);
        assert!(counters.forward_vertex_dequeues > 0);
        assert!(counters.reverse_edge_visits > 0);
        assert!(counters.forward_edge_visits > 0);
    }

    #[test]
    fn linear_dag_unknown_selected_error_preserves_sorted_first_diagnostic() {
        let lock = proof_lock();
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let options = PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::from([
                Name::from_dotted("Missing.Z"),
                Name::from_dotted("Missing.A"),
            ])),
            ..PackageVerificationExecutionOptions::default()
        };

        let error = execution_modules_for_indexed(&indexed, &options).unwrap_err();

        assert_eq!(error.kind, PackageVerificationErrorKind::Input);
        assert_eq!(error.path, "execution.selected_modules");
        assert_eq!(
            error.field.as_deref().map(String::as_str),
            Some("selected_modules")
        );
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::SelectedModuleMissing
        );
        assert_eq!(error.expected_value.as_deref(), Some("package lock module"));
        assert_eq!(error.actual_value.as_deref(), Some("Missing.A"));
    }

    fn run_on_large_stack(name: &str, test: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(name.to_owned())
            .stack_size(PACKAGE_FAST_VERIFIER_TEST_STACK_BYTES)
            .spawn(test)
            .expect("package fast verifier test thread should spawn")
            .join()
            .expect("package fast verifier test thread should not panic");
    }

    #[test]
    fn package_reference_diagnostic_keeps_unknown_reference_identity() {
        let source = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 417,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(npa_checker_ref::ReferenceCheckReference::Builtin {
                declaration: ReferenceModuleName::from_dotted("Std.Logic.Eq.rec").unwrap(),
                decl_interface_hash: [0xab; 32],
            }),
            structural_limit: None,
        };

        let error =
            PackageVerificationError::reference_checker_rejected("modules[0].certificate", source);
        assert_eq!(
            error
                .checker_error
                .as_ref()
                .and_then(|details| details.reason_code.as_deref()),
            Some("unknown_reference")
        );
        let actual = error.actual_value.expect("debug diagnostic payload");
        assert!(actual.contains("Builtin"), "{actual}");
        assert!(
            actual.contains("Std\", \"Logic\", \"Eq\", \"rec"),
            "{actual}"
        );
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("npa-api crate lives under crates/")
            .to_path_buf()
    }

    fn proofs_root() -> PathBuf {
        repo_root().join("testdata/package/proofs")
    }

    fn read(path: PathBuf) -> Vec<u8> {
        fs::read(&path).unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
    }

    fn read_to_string(path: PathBuf) -> String {
        String::from_utf8(read(path)).expect("fixture is UTF-8")
    }

    fn proof_manifest_source() -> String {
        read_to_string(proofs_root().join("npa-package.toml"))
    }

    fn filtered_proof_fixture() -> (ValidatedPackageManifest, PackageLockManifest) {
        let mut manifest = parse_manifest_str(&proof_manifest_source()).unwrap();
        let mut lock = parse_package_lock_json(&read_to_string(
            proofs_root().join("generated/package-lock.json"),
        ))
        .unwrap();
        let removed = unsupported_proof_fixture_modules(&manifest, &lock);
        manifest
            .modules
            .retain(|module| !removed.contains(&module.module));
        lock.entries
            .retain(|entry| !removed.contains(&entry.module));
        (validate_manifest(manifest).unwrap(), lock)
    }

    fn proof_manifest() -> npa_package::PackageManifest {
        filtered_proof_fixture().0.into_manifest()
    }

    fn validated_proof_manifest() -> ValidatedPackageManifest {
        filtered_proof_fixture().0
    }

    fn proof_lock() -> PackageLockManifest {
        filtered_proof_fixture().1
    }

    fn unsupported_proof_fixture_modules(
        manifest: &npa_package::PackageManifest,
        lock: &PackageLockManifest,
    ) -> BTreeSet<Name> {
        let root = proofs_root();
        let manifest_modules = manifest
            .modules
            .iter()
            .map(|module| module.module.clone())
            .chain(
                manifest
                    .imports
                    .as_deref()
                    .unwrap_or(&[])
                    .iter()
                    .map(|import| import.module.clone()),
            )
            .collect::<BTreeSet<_>>();
        let mut removed = lock
            .entries
            .iter()
            .filter_map(|entry| {
                if !manifest_modules.contains(&entry.module) {
                    return Some(entry.module.clone());
                }
                let bytes = match fs::read(root.join(entry.certificate.as_str())) {
                    Ok(bytes) => bytes,
                    Err(_) => return Some(entry.module.clone()),
                };
                decode_module_cert(&bytes)
                    .is_err()
                    .then(|| entry.module.clone())
            })
            .collect::<BTreeSet<_>>();

        let mut reverse = BTreeMap::<Name, Vec<Name>>::new();
        for entry in &lock.entries {
            for import in &entry.imports {
                reverse
                    .entry(import.module.clone())
                    .or_default()
                    .push(entry.module.clone());
            }
        }
        let mut stack = removed.iter().cloned().collect::<Vec<_>>();
        while let Some(module) = stack.pop() {
            for dependent in reverse.get(&module).cloned().unwrap_or_default() {
                if removed.insert(dependent.clone()) {
                    stack.push(dependent);
                }
            }
        }
        removed
    }

    fn proof_certificate_artifacts(lock: &PackageLockManifest) -> BTreeMap<PackagePath, Vec<u8>> {
        let root = proofs_root();
        lock.entries
            .iter()
            .map(|entry| {
                (
                    entry.certificate.clone(),
                    read(root.join(entry.certificate.as_str())),
                )
            })
            .collect()
    }

    fn package_certificate_artifacts(
        artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    ) -> Vec<PackageCertificateArtifact<'_>> {
        artifacts
            .iter()
            .map(|(path, bytes)| PackageCertificateArtifact {
                path: path.clone(),
                bytes: bytes.as_slice(),
            })
            .collect()
    }

    fn proof_prepared_artifacts(
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        policy: PreparedArtifactRetentionPolicy,
    ) -> (
        PreparedPackageArtifacts,
        PackageArtifactPreparationObservation,
    ) {
        let bytes = proof_certificate_artifacts(lock);
        let owned = bytes
            .into_iter()
            .map(|(path, bytes)| OwnedPackageLockArtifact::from_vec(path, bytes))
            .collect::<Vec<_>>();
        let mut preparation = PackageArtifactPreparationObservation::default();
        let snapshots = build_package_lock_and_snapshot_owned_artifacts(
            validated,
            PackagePath::new("npa-package.toml"),
            proof_manifest_source().as_bytes(),
            owned,
            policy,
            PreparedArtifactObservationMode::Aggregate,
            Some(&mut preparation),
        )
        .unwrap();
        let (derived_lock, artifacts) = snapshots.into_parts();
        assert_eq!(&derived_lock, lock);
        (artifacts, preparation)
    }

    #[test]
    fn package_snapshot_fast_input_matches_raw_and_releases_retention() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let raw = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        let (mut prepared, preparation) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let initial = prepared.retention_observation().unwrap();
        assert_eq!(preparation.artifact_file_hashes, lock.entries.len() as u64);
        assert_eq!(preparation.artifact_full_decodes, lock.entries.len() as u64);
        assert_eq!(initial.admissions, lock.entries.len() as u64);
        let mut artifact_observation = PackageCertificateArtifactObservation::default();
        artifact_observation.merge_preparation(preparation);
        let snapshot =
            verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
                &validated,
                &lock,
                &mut prepared,
                PackageVerificationExecutionOptions::default(),
                Some(&mut artifact_observation),
            )
            .unwrap();

        assert_eq!(snapshot, raw);
        assert_eq!(
            artifact_observation.artifact_file_hashes,
            lock.entries.len() as u64
        );
        assert_eq!(
            artifact_observation.artifact_full_decodes,
            lock.entries.len() as u64
        );
        assert_eq!(
            artifact_observation.artifact_prepared_reuses,
            lock.entries.len() as u64
        );
        assert_eq!(prepared.retained_decoded_entries(), 0);
        assert_eq!(prepared.retained_decoded_bytes(), 0);
        let final_retention = prepared.retention_observation().unwrap();
        assert_eq!(final_retention.current_entries, 0);
        assert_eq!(final_retention.current_bytes, 0);
        assert_eq!(final_retention.charged_releases, initial.admissions);
        assert_eq!(final_retention.released_bytes, initial.admitted_bytes);
    }

    #[test]
    fn package_verification_memo_snapshot_lane_key_parity() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        for mode in [
            PackageVerificationMode::FastKernel,
            PackageVerificationMode::Reference,
        ] {
            let raw = package_verification_memo_key_inputs(
                &validated,
                &lock,
                package_certificate_artifacts(&bytes),
                mode,
            )
            .unwrap();
            let snapshot = package_verification_memo_key_inputs_from_artifact_snapshots(
                &validated, &lock, &prepared, mode,
            )
            .unwrap();
            assert_eq!(snapshot, raw);
        }

        let raw_reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        let hashed = lock
            .entries
            .iter()
            .map(|entry| prepared.clone_hashed_raw(&entry.certificate).unwrap())
            .collect::<Vec<_>>();
        let hashed_reference = verify_package_reference_source_free_with_hashed_artifacts(
            &validated,
            &lock,
            hashed.iter(),
        )
        .unwrap();
        assert_eq!(hashed_reference, raw_reference);

        let mut mismatched_manifest = proof_manifest();
        let target = mismatched_manifest.modules[0].module.clone();
        let mismatched_hash = PackageHash::new(test_hash(0xc3));
        mismatched_manifest.modules[0].expected_certificate_file_hash = mismatched_hash;
        let mismatched_validated = validate_manifest(mismatched_manifest).unwrap();
        let mut mismatched_lock = lock.clone();
        mismatched_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module == target)
            .unwrap()
            .certificate_file_hash = mismatched_hash;
        let raw_mismatch = verify_package_reference_source_free(
            &mismatched_validated,
            &mismatched_lock,
            package_certificate_artifacts(&bytes),
        )
        .unwrap();
        let hashed_mismatch = verify_package_reference_source_free_with_hashed_artifacts(
            &mismatched_validated,
            &mismatched_lock,
            hashed.iter(),
        )
        .unwrap();
        assert_eq!(hashed_mismatch, raw_mismatch);
        assert_eq!(hashed_mismatch.status, PackageVerificationStatus::Failed);
        assert_eq!(
            hashed_mismatch
                .modules
                .iter()
                .find(|module| module.module == target)
                .and_then(|module| module.error.as_ref())
                .map(|error| error.reason_code),
            Some(PackageVerificationErrorReason::CertificateFileHashMismatch),
        );

        let all_modules = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let raw_cached = verify_package_reference_source_free_with_local_audit_cache_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            all_modules.clone(),
        )
        .unwrap();
        let hashed_cached =
            verify_package_reference_source_free_with_hashed_artifacts_and_local_audit_cache_hits(
                &validated,
                &lock,
                hashed.iter(),
                all_modules.clone(),
            )
            .unwrap();
        assert_eq!(hashed_cached, raw_cached);
        let raw_disk = verify_package_reference_source_free_with_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            all_modules.clone(),
        )
        .unwrap();
        let hashed_disk =
            verify_package_reference_source_free_with_hashed_artifacts_and_disk_memo_hits(
                &validated,
                &lock,
                hashed.iter(),
                all_modules,
            )
            .unwrap();
        assert_eq!(hashed_disk, raw_disk);
    }

    fn assert_fast_hashed_artifact_contract() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let (prepared, _) =
            proof_prepared_artifacts(&validated, &lock, PreparedArtifactRetentionPolicy::RawOnly);
        let hashed = lock
            .entries
            .iter()
            .map(|entry| prepared.clone_hashed_raw(&entry.certificate).unwrap())
            .collect::<Vec<_>>();
        let hashed_bytes = hashed
            .iter()
            .map(|artifact| (artifact.path().clone(), artifact.bytes()))
            .collect::<BTreeMap<_, _>>();
        let hashed_file_hashes = hashed
            .iter()
            .map(|artifact| (artifact.path().clone(), artifact.file_hash()))
            .collect::<BTreeMap<_, _>>();
        let entries = canonical_lock_entries(&lock);
        let (entry_index, entry) = entries
            .iter()
            .copied()
            .find(|(_, entry)| entry.imports.is_empty())
            .unwrap();
        let mut session = VerifierSession::new();
        let worker = verify_fast_worker(
            entry_index,
            entry,
            &hashed_bytes,
            Some(&hashed_file_hashes),
            PackageFastWorkerImportContext::Session(&mut session),
            &package_fast_kernel_policy(&validated),
            &PackageVerificationDecodeCacheConfig::for_mode(
                &validated,
                PackageVerificationMode::FastKernel,
            ),
            PackageFastWorkerObservation {
                measurement_mode: PerformanceMeasurementMode::Summary,
                worker_index: 0,
            },
        );
        assert!(
            worker
                .measurement_observation()
                .certificate_file_hash_reused
        );

        for selected_modules in [
            None,
            Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
            Some(BTreeSet::new()),
        ] {
            for jobs in [1, 4] {
                let raw_handle = test_process_memo_handle();
                let options = PackageVerificationExecutionOptions {
                    jobs,
                    selected_modules: selected_modules.clone(),
                    memoization: PackageVerificationMemoMode::ProcessLocal(raw_handle),
                    ..PackageVerificationExecutionOptions::default()
                };
                let raw = verify_package_fast_source_free_with_options(
                    &validated,
                    &lock,
                    package_certificate_artifacts(&bytes),
                    options.clone(),
                )
                .unwrap();
                let hashed_handle = test_process_memo_handle();
                let hashed_report =
                    verify_package_fast_source_free_with_hashed_artifacts_and_options(
                        &validated,
                        &lock,
                        hashed.iter(),
                        PackageVerificationExecutionOptions {
                            memoization: PackageVerificationMemoMode::ProcessLocal(hashed_handle),
                            ..options
                        },
                    )
                    .unwrap();
                assert_report_functional_parity(&hashed_report, &raw);
                assert_eq!(
                    hashed_report.memo_counters.keys_built,
                    raw.memo_counters.keys_built
                );
                assert_eq!(hashed_report.memo_counters.hits, raw.memo_counters.hits);
                assert_eq!(hashed_report.memo_counters.misses, raw.memo_counters.misses);
                assert_eq!(
                    hashed_report.memo_counters.inserted,
                    raw.memo_counters.inserted
                );
                if raw.topological_order.is_empty() {
                    assert_eq!(raw.memo_counters.certificate_bytes_hashed, 0);
                } else {
                    assert!(raw.memo_counters.certificate_bytes_hashed > 0);
                }
                assert_eq!(hashed_report.memo_counters.certificate_bytes_hashed, 0);
            }
        }

        let missing_path = hashed[0].path().clone();
        let missing_module = lock
            .entries
            .iter()
            .find(|entry| entry.certificate == missing_path)
            .unwrap()
            .module
            .clone();
        let raw_missing = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes)
                .into_iter()
                .filter(|artifact| artifact.path != missing_path),
            PackageVerificationExecutionOptions {
                jobs: 4,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let hashed_missing = verify_package_fast_source_free_with_hashed_artifacts_and_options(
            &validated,
            &lock,
            hashed
                .iter()
                .filter(|artifact| artifact.path() != &missing_path),
            PackageVerificationExecutionOptions {
                jobs: 4,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_report_functional_parity(&hashed_missing, &raw_missing);
        assert_eq!(hashed_missing.status, PackageVerificationStatus::Failed);
        assert_eq!(
            hashed_missing
                .modules
                .iter()
                .find(|module| module.module == missing_module)
                .and_then(|module| module.error.as_ref())
                .map(|error| error.reason_code),
            Some(PackageVerificationErrorReason::CertificateArtifactMissing)
        );

        let duplicate = verify_package_fast_source_free_with_hashed_artifacts(
            &validated,
            &lock,
            hashed.iter().chain(hashed.first()),
        )
        .unwrap_err();
        assert_eq!(
            duplicate.reason_code,
            PackageVerificationErrorReason::DuplicateCertificateArtifact
        );

        let mut stale_manifest = proof_manifest();
        let stale_module = stale_manifest.modules[0].module.clone();
        let stale_hash = PackageHash::new(test_hash(0xc3));
        stale_manifest.modules[0].expected_certificate_file_hash = stale_hash;
        let stale_validated = validate_manifest(stale_manifest).unwrap();
        let mut stale_lock = lock.clone();
        stale_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module == stale_module)
            .unwrap()
            .certificate_file_hash = stale_hash;
        let mismatch = verify_package_fast_source_free_with_hashed_artifacts(
            &stale_validated,
            &stale_lock,
            hashed.iter(),
        )
        .unwrap();
        assert_eq!(mismatch.status, PackageVerificationStatus::Failed);
        assert_eq!(
            mismatch
                .modules
                .iter()
                .find(|module| module.module == stale_module)
                .and_then(|module| module.error.as_ref())
                .map(|error| error.reason_code),
            Some(PackageVerificationErrorReason::CertificateFileHashMismatch)
        );
    }

    #[test]
    fn package_verification_memo_owned_slots_reuse_file_hash() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let indexed = validate_package_lock_against_manifest_indexed(&validated, &lock).unwrap();
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let selected = BTreeSet::from([lock.entries[0].module.clone()]);
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
            ..PackageVerificationExecutionOptions::default()
        };

        let run = PackageVerificationMemoRun::for_snapshot_run(
            &options,
            &validated,
            &indexed,
            &selected,
            &prepared,
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert_eq!(run.keys_by_module.len(), 1);
        assert_eq!(run.counters.keys_built, 1);
        assert_eq!(run.counters.certificate_bytes_hashed, 0);
    }

    #[test]
    fn package_verification_memo_snapshot_scope_preserves_topological_order() {
        let hash = PackageHash::new([0; 32]);
        let dependency = Name::from_dotted("Z.Dependency");
        let dependent = Name::from_dotted("A.Dependent");
        let lock = PackageLockManifest {
            schema: npa_package::PACKAGE_LOCK_SCHEMA.to_owned(),
            package: PackageId::new("snapshot-memo-order"),
            version: PackageVersion::new("0.0.0"),
            manifest: npa_package::PackageLockManifestReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash,
            },
            entries: vec![
                PackageLockEntry {
                    module: dependent.clone(),
                    origin: PackageLockEntryOrigin::Local,
                    certificate: PackagePath::new("generated/A.Dependent.npcert"),
                    certificate_file_hash: hash,
                    export_hash: hash,
                    axiom_report_hash: hash,
                    certificate_hash: hash,
                    imports: vec![npa_package::PackageLockImport {
                        module: dependency.clone(),
                        export_hash: hash,
                        certificate_hash: hash,
                    }],
                    package: None,
                    version: None,
                },
                PackageLockEntry {
                    module: dependency.clone(),
                    origin: PackageLockEntryOrigin::Local,
                    certificate: PackagePath::new("generated/Z.Dependency.npcert"),
                    certificate_file_hash: hash,
                    export_hash: hash,
                    axiom_report_hash: hash,
                    certificate_hash: hash,
                    imports: Vec::new(),
                    package: None,
                    version: None,
                },
            ],
        };
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let execution_modules = BTreeSet::from([dependent.clone(), dependency.clone()]);

        let entry_indices = snapshot_memo_scoped_entry_indices(&indexed, &execution_modules);
        let ordered_modules = entry_indices
            .iter()
            .map(|entry_index| indexed.entries()[*entry_index].module.clone())
            .collect::<Vec<_>>();

        assert_eq!(ordered_modules, vec![dependency, dependent]);
        assert_ne!(
            ordered_modules,
            execution_modules.into_iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn package_verification_memo_fast_retained_slot_reuses_header() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let indexed = validate_package_lock_against_manifest_indexed(&validated, &lock).unwrap();
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let selected = BTreeSet::from([lock.entries[0].module.clone()]);
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
            ..PackageVerificationExecutionOptions::default()
        };

        reset_snapshot_memo_header_decode_count();
        let run = PackageVerificationMemoRun::for_snapshot_run(
            &options,
            &validated,
            &indexed,
            &selected,
            &prepared,
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert_eq!(run.keys_by_module.len(), 1);
        assert_eq!(snapshot_memo_header_decode_count(), 0);
    }

    #[test]
    fn package_verification_memo_fast_fallback_decodes_header_once() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let indexed = validate_package_lock_against_manifest_indexed(&validated, &lock).unwrap();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let selected_entry = &lock.entries[0];
        let selected = BTreeSet::from([selected_entry.module.clone()]);
        assert!(matches!(
            prepared.release_decoded(
                &selected_entry.certificate,
                PreparedArtifactReleaseReason::Unselected,
            ),
            PreparedArtifactRelease::Charged { .. }
        ));
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
            ..PackageVerificationExecutionOptions::default()
        };

        reset_snapshot_memo_header_decode_count();
        let run = PackageVerificationMemoRun::for_snapshot_run(
            &options,
            &validated,
            &indexed,
            &selected,
            &prepared,
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert_eq!(run.keys_by_module.len(), 1);
        assert_eq!(snapshot_memo_header_decode_count(), 1);
    }

    #[test]
    fn package_verification_memo_reference_slots_decode_raw_header_once() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let indexed = validate_package_lock_against_manifest_indexed(&validated, &lock).unwrap();
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let selected = BTreeSet::from([lock.entries[0].module.clone()]);
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
            ..PackageVerificationExecutionOptions::default()
        };

        reset_snapshot_memo_header_decode_count();
        let run = PackageVerificationMemoRun::for_snapshot_run(
            &options,
            &validated,
            &indexed,
            &selected,
            &prepared,
            PackageVerificationMode::Reference,
        )
        .unwrap();
        assert_eq!(run.keys_by_module.len(), 1);
        assert_eq!(snapshot_memo_header_decode_count(), 1);
    }

    #[test]
    fn package_snapshot_cached_fast_paths_match_raw_and_release_all() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let all_modules = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let raw = verify_package_fast_source_free_with_local_audit_cache_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            all_modules.clone(),
        )
        .unwrap();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let snapshot =
            verify_package_fast_source_free_with_artifact_snapshots_and_local_audit_cache_hits(
                &validated,
                &lock,
                &mut prepared,
                all_modules,
            )
            .unwrap();
        assert_eq!(snapshot, raw);
        assert_eq!(prepared.retained_decoded_entries(), 0);
        assert_eq!(prepared.retained_decoded_bytes(), 0);
    }

    #[test]
    fn package_snapshot_cached_outer_validation_errors_release_all() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let mut mismatched_lock = lock.clone();
        mismatched_lock.package = PackageId::new("snapshot-mismatched-package");

        let (mut local_audit_artifacts, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        assert!(local_audit_artifacts.retained_decoded_entries() > 0);
        let error =
            verify_package_fast_source_free_with_artifact_snapshots_and_local_audit_cache_hits(
                &validated,
                &mismatched_lock,
                &mut local_audit_artifacts,
                std::iter::empty::<Name>(),
            )
            .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::PackageIdentityMismatch
        );
        assert_eq!(local_audit_artifacts.retained_decoded_entries(), 0);
        assert_eq!(local_audit_artifacts.retained_decoded_bytes(), 0);

        let (mut observed_artifacts, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        assert!(observed_artifacts.retained_decoded_entries() > 0);
        let mut observation = PackageCertificateArtifactObservation::default();
        let error =
            verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed(
                &validated,
                &mismatched_lock,
                &mut observed_artifacts,
                std::iter::empty::<Name>(),
                PackageModuleVerificationEvidence::LocalAuditCache,
                std::iter::empty::<Name>(),
                Some(&mut observation),
            )
            .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::PackageIdentityMismatch
        );
        assert_eq!(observed_artifacts.retained_decoded_entries(), 0);
        assert_eq!(observed_artifacts.retained_decoded_bytes(), 0);
    }

    #[test]
    fn package_snapshot_process_memo_reuses_keys_without_rehashing_artifacts() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let handle = test_process_memo_handle();
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(handle),
            ..PackageVerificationExecutionOptions::default()
        };
        let (mut first_artifacts, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let first = verify_package_fast_source_free_with_artifact_snapshots_and_options(
            &validated,
            &lock,
            &mut first_artifacts,
            options.clone(),
        )
        .unwrap();
        let (mut second_artifacts, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let second = verify_package_fast_source_free_with_artifact_snapshots_and_options(
            &validated,
            &lock,
            &mut second_artifacts,
            options,
        )
        .unwrap();
        assert_eq!(first.memo_counters.keys_built, lock.entries.len());
        assert_eq!(first.memo_counters.certificate_bytes_hashed, 0);
        assert_eq!(second.memo_counters.hits, lock.entries.len());
        assert_eq!(second.memo_counters.certificate_bytes_hashed, 0);
        assert_eq!(second_artifacts.retained_decoded_entries(), 0);
        assert_eq!(second_artifacts.retained_decoded_bytes(), 0);
    }

    #[test]
    fn package_hashed_reference_process_memo_reuses_file_hash_and_hits() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let raw = verify_package_reference_source_free(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
        )
        .unwrap();
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let hashed = lock
            .entries
            .iter()
            .map(|entry| prepared.clone_hashed_raw(&entry.certificate).unwrap())
            .collect::<Vec<_>>();
        let handle = test_process_memo_handle();
        let options = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(handle),
            ..PackageVerificationExecutionOptions::default()
        };
        let first = verify_package_reference_source_free_with_hashed_artifacts_and_options(
            &validated,
            &lock,
            hashed.iter(),
            options.clone(),
        )
        .unwrap();
        let second = verify_package_reference_source_free_with_hashed_artifacts_and_options(
            &validated,
            &lock,
            hashed.iter(),
            options,
        )
        .unwrap();

        assert_eq!(first.status, raw.status);
        assert_eq!(first.modules, raw.modules);
        assert_eq!(second.status, raw.status);
        assert_eq!(second.modules, raw.modules);
        assert_eq!(first.memo_counters.keys_built, lock.entries.len());
        assert_eq!(first.memo_counters.certificate_bytes_hashed, 0);
        assert_eq!(second.memo_counters.keys_built, lock.entries.len());
        assert_eq!(second.memo_counters.hits, lock.entries.len());
        assert_eq!(second.memo_counters.certificate_bytes_hashed, 0);
    }

    #[test]
    fn package_decode_cache_charges_retained_key_capacity_at_exact_limit() {
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock)
            .into_values()
            .next()
            .expect("proof fixture has a certificate");
        let certificate = decode_module_cert(&bytes).unwrap();
        let mut fast_key = String::with_capacity(512);
        fast_key.push_str("capacity-sensitive-fast-key");
        let retained_fast_key_capacity = fast_key.capacity();
        let fast_charge =
            PackageVerificationDecodeCache::fast_charge(retained_fast_key_capacity, &certificate);
        let mut fast_cache = PackageVerificationDecodeCache {
            retained_bytes: npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
                .checked_sub(fast_charge)
                .expect("fixture charge fits the cache bound"),
            ..PackageVerificationDecodeCache::default()
        };
        assert!(fast_cache.insert_fast(fast_key, certificate.clone()));
        assert_eq!(
            fast_cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        let mut oversized_replacement_key = String::with_capacity(1_024);
        oversized_replacement_key.push_str("capacity-sensitive-fast-key");
        assert!(fast_cache.insert_fast(oversized_replacement_key, certificate));
        assert_eq!(
            fast_cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        assert_eq!(
            fast_cache
                .fast_certificates
                .get_key_value("capacity-sensitive-fast-key")
                .unwrap()
                .0
                .capacity(),
            retained_fast_key_capacity
        );

        let imports = Arc::new(ReferenceImportStore::default());
        let mut reference_key = String::with_capacity(384);
        reference_key.push_str("capacity-sensitive-reference-key");
        let retained_reference_key_capacity = reference_key.capacity();
        let retained_imports = RetainedReferenceImportContext::new(Arc::clone(&imports));
        let reference_charge = PackageVerificationDecodeCache::reference_charge(
            retained_reference_key_capacity,
            retained_imports.value_charge,
        );
        let mut reference_cache = PackageVerificationDecodeCache {
            retained_bytes: npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
                .checked_sub(reference_charge)
                .expect("fixture charge fits the cache bound"),
            ..PackageVerificationDecodeCache::default()
        };
        assert!(reference_cache.insert_reference(reference_key, retained_imports));
        assert_eq!(
            reference_cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        let mut oversized_replacement_key = String::with_capacity(768);
        oversized_replacement_key.push_str("capacity-sensitive-reference-key");
        assert!(reference_cache.insert_reference(
            oversized_replacement_key,
            RetainedReferenceImportContext::new(imports)
        ));
        assert_eq!(
            reference_cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        assert_eq!(
            reference_cache
                .reference_import_contexts
                .get_key_value("capacity-sensitive-reference-key")
                .unwrap()
                .0
                .capacity(),
            retained_reference_key_capacity
        );
    }

    fn decode_cache_test_certificate() -> ModuleCert {
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock)
            .into_values()
            .next()
            .expect("proof fixture has a certificate");
        decode_module_cert(&bytes).unwrap()
    }

    fn certificate_with_additional_name_capacity(
        certificate: &ModuleCert,
        additional: usize,
    ) -> ModuleCert {
        let mut parts = certificate.clone().into_parts();
        let old_names = std::mem::take(&mut parts.name_table);
        let mut names = Vec::with_capacity(old_names.len().saturating_add(additional));
        names.extend(old_names);
        parts.name_table = names;
        ModuleCert::from_parts(parts)
    }

    #[test]
    fn package_decode_cache_fast_admission_pins_exact_limits_and_non_transition() {
        let certificate = decode_cache_test_certificate();
        let exact_key = String::from("fast-exact-limit");
        let exact_charge =
            PackageVerificationDecodeCache::fast_charge(exact_key.capacity(), &certificate);
        let mut cache = PackageVerificationDecodeCache {
            retained_bytes: npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1 - exact_charge,
            ..PackageVerificationDecodeCache::default()
        };
        assert!(cache.insert_fast(exact_key.clone(), certificate.clone()));
        assert_eq!(
            cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );

        let before_entries = cache.retained_entries;
        let before_bytes = cache.retained_bytes;
        assert!(!cache.insert_fast("one-byte-over".to_owned(), certificate.clone()));
        assert!(!cache.fast_certificates.contains_key("one-byte-over"));
        assert_eq!(cache.retained_entries, before_entries);
        assert_eq!(cache.retained_bytes, before_bytes);

        let mut entry_limited = PackageVerificationDecodeCache {
            retained_entries: npa_cert::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1,
            ..PackageVerificationDecodeCache::default()
        };
        assert!(!entry_limited.insert_fast("entry-over".to_owned(), certificate));
        assert!(entry_limited.fast_certificates.is_empty());
    }

    #[test]
    fn package_decode_cache_reference_admission_shares_combined_budget() {
        let certificate = decode_cache_test_certificate();
        let imports = Arc::new(ReferenceImportStore::default());
        let reference_key = String::from("reference-exact-limit");
        let retained_imports = RetainedReferenceImportContext::new(Arc::clone(&imports));
        let reference_charge = PackageVerificationDecodeCache::reference_charge(
            reference_key.capacity(),
            retained_imports.value_charge,
        );
        let mut cache = PackageVerificationDecodeCache::default();
        assert!(cache.insert_fast("fast-partition".to_owned(), certificate));
        cache.retained_bytes =
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1 - reference_charge;
        assert!(cache.insert_reference(reference_key.clone(), retained_imports));
        assert_eq!(
            cache.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        let before_entries = cache.retained_entries;
        let before_bytes = cache.retained_bytes;
        assert!(!cache.insert_reference(
            "reference-over".to_owned(),
            RetainedReferenceImportContext::new(Arc::clone(&imports))
        ));
        assert!(!cache
            .reference_import_contexts
            .contains_key("reference-over"));
        assert_eq!(cache.retained_entries, before_entries);
        assert_eq!(cache.retained_bytes, before_bytes);
        assert!(imports.is_empty());
    }

    #[test]
    fn package_decode_cache_replacement_pins_grow_reject_and_shrink_deltas() {
        let compact = decode_cache_test_certificate();
        let expanded = certificate_with_additional_name_capacity(&compact, 64);
        let key = String::from("replace-certificate");
        let compact_charge = PackageVerificationDecodeCache::fast_charge(key.capacity(), &compact);
        let expanded_charge =
            PackageVerificationDecodeCache::fast_charge(key.capacity(), &expanded);
        assert!(expanded_charge > compact_charge);
        assert_eq!(compact, expanded);

        let mut exact_growth = PackageVerificationDecodeCache::default();
        assert!(exact_growth.insert_fast(key.clone(), compact.clone()));
        exact_growth.retained_bytes = npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
            .saturating_sub(expanded_charge)
            .saturating_add(compact_charge);
        assert!(exact_growth.insert_fast(key.clone(), expanded.clone()));
        assert_eq!(
            exact_growth.retained_bytes,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
        assert_eq!(
            exact_growth
                .fast_certificates
                .get(&key)
                .unwrap()
                .logical_retained_bytes_v1(),
            expanded.logical_retained_bytes_v1()
        );

        let mut rejected_growth = PackageVerificationDecodeCache::default();
        assert!(rejected_growth.insert_fast(key.clone(), compact.clone()));
        rejected_growth.retained_bytes = npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
            .saturating_sub(expanded_charge)
            .saturating_add(compact_charge)
            .saturating_add(1);
        let before = rejected_growth.retained_bytes;
        assert!(!rejected_growth.insert_fast(key.clone(), expanded.clone()));
        assert_eq!(rejected_growth.retained_bytes, before);
        assert_eq!(
            rejected_growth
                .fast_certificates
                .get(&key)
                .unwrap()
                .logical_retained_bytes_v1(),
            compact.logical_retained_bytes_v1()
        );

        let mut shrink = PackageVerificationDecodeCache::default();
        assert!(shrink.insert_fast(key.clone(), expanded));
        let before_shrink = shrink.retained_bytes;
        assert!(shrink.insert_fast(key, compact));
        assert_eq!(
            shrink.retained_bytes,
            before_shrink.saturating_sub(expanded_charge - compact_charge)
        );
    }

    #[test]
    fn clear_package_verification_decode_cache_resets_accounting_idempotently() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let certificate = decode_cache_test_certificate();
        let imports = Arc::new(ReferenceImportStore::default());
        {
            let mut cache =
                lock_package_verification_decode_cache(package_verification_decode_cache());
            assert!(cache.insert_fast("clear-fast".to_owned(), certificate));
            assert!(cache.insert_reference(
                "clear-reference".to_owned(),
                RetainedReferenceImportContext::new(imports)
            ));
            assert_eq!(cache.retained_entries, 2);
            assert!(cache.retained_bytes > 0);
        }
        clear_package_verification_decode_cache();
        assert_eq!(package_verification_decode_cache_entry_count(), 0);
        assert_eq!(package_verification_decode_cache_retained_bytes(), 0);
        clear_package_verification_decode_cache();
        assert_eq!(package_verification_decode_cache_entry_count(), 0);
        assert_eq!(package_verification_decode_cache_retained_bytes(), 0);
    }

    #[test]
    fn package_decode_cache_capacity_pins_entry_byte_saturation_and_poison_boundaries() {
        let certificate = decode_cache_test_certificate();
        let mut entry_bound = PackageVerificationDecodeCache::default();
        for index in 0..npa_cert::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1 {
            assert!(entry_bound.insert_fast(format!("entry-{index}"), certificate.clone()));
        }
        let exact_entries = entry_bound.retained_entries;
        let exact_bytes = entry_bound.retained_bytes;
        assert_eq!(exact_entries, npa_cert::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1);
        assert!(!entry_bound.insert_fast("entry-one-over".to_owned(), certificate));
        assert_eq!(entry_bound.retained_entries, exact_entries);
        assert_eq!(entry_bound.retained_bytes, exact_bytes);
        assert!(!entry_bound.replacement_fits(0, u64::MAX, true));

        let poisoned = Arc::new(Mutex::new(PackageVerificationDecodeCache::default()));
        let poisoner = Arc::clone(&poisoned);
        assert!(std::thread::spawn(move || {
            let _guard = lock_package_verification_decode_cache(&poisoner);
            panic!("intentional decode-cache poison");
        })
        .join()
        .is_err());
        assert!(std::panic::catch_unwind(|| {
            drop(lock_package_verification_decode_cache(&poisoned));
        })
        .is_err());
    }

    #[test]
    fn package_fast_decode_cache_mutex_scope_releases_before_projection_work() {
        let certificate = decode_cache_test_certificate();
        let cache = Mutex::new(PackageVerificationDecodeCache::default());
        assert!(lock_package_verification_decode_cache(&cache)
            .insert_fast("fast".to_owned(), certificate));
        let hit = package_fast_decode_cache_lookup_then(&cache, "fast", |hit| {
            let available = cache
                .try_lock()
                .expect("fast lookup released the cache before projection callback");
            drop(available);
            let hit = hit.expect("inserted certificate is retained");
            assert!(!hit.header().format.is_empty());
            hit
        });
        assert_eq!(
            hit,
            package_fast_decode_cache_lookup(&cache, "fast").unwrap()
        );
    }

    #[test]
    fn package_reference_cache_mutex_scope_releases_before_validation_work() {
        let imports = Arc::new(ReferenceImportStore::default());
        let cache = Mutex::new(PackageVerificationDecodeCache::default());
        assert!(package_reference_cache_insert_with_charge(
            &cache,
            "reference".to_owned(),
            imports,
            |store| {
                let available = cache
                    .try_lock()
                    .expect("reference charge runs before the cache admission lock");
                drop(available);
                store.logical_retained_bytes_v1()
            }
        ));
        let hit = package_reference_cache_lookup_then(&cache, "reference", |hit| {
            let available = cache
                .try_lock()
                .expect("reference lookup released the cache before validation callback");
            drop(available);
            let hit = hit.expect("inserted import context is retained");
            assert!(hit.is_empty());
            hit
        });
        assert!(Arc::ptr_eq(
            &hit,
            &package_reference_cache_lookup(&cache, "reference").unwrap()
        ));
    }

    #[test]
    fn package_measurements_count_actual_checker_and_decode_boundaries() {
        fn counter(
            report: &PerformanceMeasurementReport,
            label: PerformanceMeasurementLabel,
        ) -> u64 {
            report
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
                .expect("measurement counter is present")
        }

        let lock = proof_lock();
        let entries = canonical_lock_entries(&lock);
        let entry = entries.first().expect("proof fixture has a lock entry").1;
        let corrupt_certificate = b"not a certificate".to_vec();
        let artifact_bytes =
            BTreeMap::from([(entry.certificate.clone(), corrupt_certificate.as_slice())]);
        let modules = vec![module_result(
            entry,
            PackageModuleVerificationStatus::Failed,
            Some(PackageVerificationError::certificate_decode_failed(
                "entries[0].certificate",
                "invalid certificate",
            )),
            PackageVerificationMode::FastKernel,
            Some(&corrupt_certificate),
        )];
        let options = PackageVerificationExecutionOptions {
            measurement_mode: PerformanceMeasurementMode::Detailed,
            ..PackageVerificationExecutionOptions::default()
        };
        let mut measurement_state =
            PackageVerifierMeasurementState::new(options.measurement_mode).unwrap();
        let mut observation = PackageEntryCheckObservation::new(options.measurement_mode);
        observation.observe_certificate_bytes(&corrupt_certificate);
        measurement_state.record_module(entry, &observation, 7, Some(0), true);
        measurement_state.record_worker_timing(
            PackageFastWorkerTiming {
                worker_index: 0,
                active_elapsed_ns: 11,
                idle_elapsed_ns: 4,
            },
            true,
        );
        measurement_state.record_coordinator_merge(5);

        let report = package_measurement_report(PackageMeasurementReportInput {
            options: &options,
            lock: &lock,
            entries: &entries,
            artifact_bytes: Some(&artifact_bytes),
            modules: &modules,
            measurements: Some(&measurement_state),
            memo_counters: PackageVerificationMemoCounters::default(),
            decode_cache_counters: PackageVerificationDecodeCacheCounters::default(),
        })
        .expect("measurements enabled");

        assert_eq!(
            counter(&report, PerformanceMeasurementLabel::PackageModulesChecked),
            1
        );
        assert_eq!(
            counter(&report, PerformanceMeasurementLabel::PackageModulesDecoded),
            0
        );
        assert_eq!(report.workers.len(), 1);
        assert_eq!(report.workers[0].module_count, 1);
        assert_eq!(report.workers[0].active_elapsed_ns, 11);
        assert_eq!(report.workers[0].idle_elapsed_ns, 4);
        assert_eq!(
            counter(
                &report,
                PerformanceMeasurementLabel::PackageCoordinatorMergeElapsed
            ),
            5
        );

        let missing_modules = vec![module_result(
            entry,
            PackageModuleVerificationStatus::Failed,
            Some(PackageVerificationError::certificate_artifact_missing(
                "entries[0].certificate",
                entry.certificate.as_str(),
            )),
            PackageVerificationMode::FastKernel,
            None,
        )];
        let empty_artifacts = BTreeMap::new();
        let empty_measurements =
            PackageVerifierMeasurementState::new(options.measurement_mode).unwrap();
        let report = package_measurement_report(PackageMeasurementReportInput {
            options: &options,
            lock: &lock,
            entries: &entries,
            artifact_bytes: Some(&empty_artifacts),
            modules: &missing_modules,
            measurements: Some(&empty_measurements),
            memo_counters: PackageVerificationMemoCounters::default(),
            decode_cache_counters: PackageVerificationDecodeCacheCounters::default(),
        })
        .expect("measurements enabled");

        assert_eq!(
            counter(&report, PerformanceMeasurementLabel::PackageModulesChecked),
            0
        );
        assert_eq!(
            counter(&report, PerformanceMeasurementLabel::PackageModulesDecoded),
            0
        );
        assert_eq!(
            counter(&report, PerformanceMeasurementLabel::PackageEffectiveJobs),
            0
        );
        assert!(report.workers.is_empty());
    }

    #[test]
    fn package_checker_declaration_measurements_use_v0_3_without_kernel_details() {
        let fast_certificate = build_module_cert(unchecked_import_provider(), &[]).unwrap();
        let mut fast = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Detailed);
        fast.observe_fast_certificate(&Name::from_dotted("Fast.Fixture"), &fast_certificate);

        let reference_observation = ReferenceCheckObservation {
            certificate_decoded: true,
            declaration_count: 1,
            declarations: vec![npa_checker_ref::ReferenceCheckDeclarationObservation {
                declaration_index: 0,
                declaration: ReferenceModuleName::from_dotted("Reference.Fixture.theorem").unwrap(),
                term_nodes: 3,
            }],
        };
        let mut reference = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Detailed);
        reference.observe_reference_certificate(
            &Name::from_dotted("Reference.Fixture"),
            &reference_observation,
        );

        assert!(!fast.declarations.is_empty());
        assert!(fast
            .declarations
            .iter()
            .chain(&reference.declarations)
            .all(|declaration| declaration.kernel.is_none()));

        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        for declaration in fast.declarations.into_iter().chain(reference.declarations) {
            recorder.record_declaration(declaration);
        }
        let report = recorder.report().unwrap();
        assert_eq!(report.schema, crate::PERFORMANCE_MEASUREMENTS_SCHEMA);
        assert_eq!(
            crate::performance_measurement_report_json(&report)
                .matches("\"kernel\":null")
                .count(),
            2
        );
    }

    #[test]
    fn package_verifier_off_mode_has_no_measurement_state_or_detail_storage() {
        assert!(PackageVerifierMeasurementState::new(PerformanceMeasurementMode::Off).is_none());
        let observation = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Off);
        assert!(observation.declarations.is_empty());
        assert_eq!(observation.certificate_bytes, 0);
        assert_eq!(observation.declaration_count, 0);
    }

    #[test]
    fn package_worker_declaration_details_keep_one_canonical_bounded_sample() {
        fn detail(module: &str, declaration_index: u64) -> PerformanceDeclarationMeasurement {
            PerformanceDeclarationMeasurement {
                module: module.to_owned(),
                declaration_index,
                declaration: format!("{module}.d{declaration_index}"),
                term_nodes: 1,
                elaboration_elapsed_ns: 0,
                kernel: None,
            }
        }

        let mut later = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Detailed);
        later.declarations = vec![detail("Z", 0), detail("Z", 1)];
        let mut earlier = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Detailed);
        earlier.declarations = vec![detail("A", 0)];
        let mut collector = PackageFastWorkerDeclarationDetailCollector::new(2);

        collector.record_observation(&mut later);
        collector.record_observation(&mut earlier);
        let retained = collector.into_details();

        assert!(later.declarations.is_empty());
        assert!(earlier.declarations.is_empty());
        assert_eq!(retained.len(), 2);
        assert_eq!(retained[0].module, "A");
        assert_eq!(retained[1].module, "Z");
        assert_eq!(retained[1].declaration_index, 0);
    }

    fn test_hash(byte: u8) -> npa_cert::Hash {
        [byte; 32]
    }

    fn unchecked_import_id_type() -> Expr {
        Expr::pi(
            "A",
            Expr::sort(Level::param("u")),
            Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn unchecked_import_id_proof() -> Expr {
        Expr::lam(
            "A",
            Expr::sort(Level::param("u")),
            Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
        )
    }

    fn unchecked_import_provider() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Boundary.Provider"),
            declarations: vec![Decl::Theorem {
                name: "Boundary.Provider.id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: unchecked_import_id_type(),
                proof: unchecked_import_id_proof(),
            }],
        }
    }

    fn unchecked_import_consumer() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Boundary.Consumer"),
            declarations: vec![Decl::Theorem {
                name: "Boundary.Consumer.id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: unchecked_import_id_type(),
                proof: Expr::konst("Boundary.Provider.id", vec![Level::param("u")]),
            }],
        }
    }

    fn unchecked_import_hash_with_domain(domain: &[u8], payload: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(domain);
        hasher.update(payload);
        hasher.finalize().into()
    }

    fn recompute_unchecked_import_module_hash(cert: ModuleCert) -> ModuleCert {
        let encoded = encode_module_cert(&cert).unwrap();
        let payload = &encoded[..encoded.len() - 32];
        let mut parts = cert.into_parts();
        parts.hashes.certificate_hash =
            unchecked_import_hash_with_domain(b"NPA-MODULE-CERT-0.4.0", payload);
        ModuleCert::from_parts(parts)
    }

    fn semantically_invalid_unchecked_import_provider(cert: ModuleCert) -> ModuleCert {
        let bvar_zero = cert
            .term_table()
            .iter()
            .position(|term| matches!(term, TermNode::BVar(0)))
            .expect("identity certificate contains bvar 0");
        let bvar_one = cert
            .term_table()
            .iter()
            .position(|term| matches!(term, TermNode::BVar(1)))
            .expect("identity certificate contains bvar 1");
        let inner_lambda = cert
            .term_table()
            .iter()
            .position(|term| {
                matches!(
                    term,
                    TermNode::Lam { ty, body } if *ty == bvar_zero && *body == bvar_zero
                )
            })
            .expect("identity certificate contains its inner lambda");
        let mut parts = cert.into_parts();
        match &mut parts.term_table[inner_lambda] {
            TermNode::Lam { body, .. } => *body = bvar_one,
            term => panic!("expected inner identity lambda, got {term:?}"),
        }
        let cert = ModuleCert::from_parts(parts);
        let proof = match cert.declarations()[0].decl {
            DeclPayload::Theorem { proof, .. } => proof,
            ref decl => panic!("expected identity theorem, got {decl:?}"),
        };
        let mut payload = Vec::new();
        payload.extend(cert.declarations()[0].hashes.decl_interface_hash);
        payload.extend(term_hash(&cert, proof).unwrap());
        payload.push(0); // Empty dependency vector.
        let mut parts = cert.into_parts();
        parts.declarations[0].hashes.decl_certificate_hash =
            unchecked_import_hash_with_domain(b"NPA-DECL-CERT-0.4.0", &payload);
        recompute_unchecked_import_module_hash(ModuleCert::from_parts(parts))
    }

    fn unchecked_import_package_module(
        module: &str,
        source: &str,
        certificate: &str,
        imports: Vec<Name>,
        cert: &ModuleCert,
        bytes: &[u8],
    ) -> PackageModule {
        PackageModule {
            module: Name::from_dotted(module),
            source: PackagePath::new(source),
            certificate: PackagePath::new(certificate),
            imports,
            expected_source_hash: PackageHash::new([0; 32]),
            expected_certificate_file_hash: package_file_hash(bytes),
            expected_export_hash: PackageHash::new(cert.hashes().export_hash),
            expected_axiom_report_hash: PackageHash::new(cert.hashes().axiom_report_hash),
            expected_certificate_hash: PackageHash::new(cert.hashes().certificate_hash),
            meta: None,
            replay: None,
            producer_profile: None,
            inductives: None,
            definitions: None,
            theorems: None,
            axioms: None,
            tags: None,
        }
    }

    fn phase8_reference_runner_policy() -> IndependentCheckerRunnerPolicy {
        IndependentCheckerRunnerPolicy {
            id: "package-reference-check".to_owned(),
            version: 1,
            trust_mode: IndependentCheckerTrustMode::Pr,
            required_checker_profiles: vec!["reference".to_owned()],
            optional_checker_profiles: Vec::new(),
            checker_allowlist: vec![IndependentCheckerAllowlistEntry {
                profile: "reference".to_owned(),
                checker_id: "npa-checker-ref".to_owned(),
                checker_version: None,
                raw_result_schema: None,
                certificate_format: None,
                core_spec: None,
                binary_id: "npa-checker-ref-test".to_owned(),
                binary_hash: test_hash(10),
                build_hash: test_hash(11),
                allowed_args: vec!["--json".to_owned(), "--canonical-only".to_owned()],
            }],
            checker_identity_manifest: None,
            import_policy: IndependentCheckerRunnerImportPolicy {
                mode: "locked_store".to_owned(),
                network: "forbidden".to_owned(),
                require_import_lock_hash: true,
            },
            axiom_policy: IndependentCheckerRunnerAxiomPolicy {
                path: "generated/checker-requests/axiom-policy.toml".to_owned(),
                hash: test_hash(12),
            },
            budgets: BTreeMap::from([(
                "reference".to_owned(),
                IndependentCheckerRunnerBudget {
                    max_steps: 10_000_000,
                    max_memory_mb: 2048,
                    timeout_ms: 60_000,
                },
            )]),
        }
    }

    #[test]
    fn package_fast_verifier_axiom_report_exposes_canonical_policy_hash() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();

        let report = verify_package_fast_source_free_from_root_with_options(
            &validated,
            &lock,
            proofs_root(),
            selected_module_options("Std.Logic.Eq"),
        )
        .unwrap();
        let expected = PackageHash::new(package_fast_kernel_policy(&validated).policy_hash());

        assert_eq!(report.axiom_policy_hash, expected);
        assert_eq!(
            package_verification_policy_hash(&validated, PackageVerificationMode::FastKernel),
            expected
        );
    }

    #[test]
    fn package_verifier_axiom_allowlist_change_changes_policy_hash() {
        let base = validate_manifest(proof_manifest()).unwrap();
        let mut changed_manifest = proof_manifest();
        changed_manifest
            .policy
            .allowed_axioms
            .push(Name::from_dotted("Test.Extra"));
        let changed = validate_manifest(changed_manifest).unwrap();

        assert_ne!(
            package_verification_policy_hash(&base, PackageVerificationMode::FastKernel),
            package_verification_policy_hash(&changed, PackageVerificationMode::FastKernel)
        );
    }

    #[test]
    fn package_fast_verifier_axiom_rejects_unallowlisted_certificate_axiom() {
        let mut manifest = proof_manifest();
        manifest.policy.allowed_axioms.clear();
        for module in &mut manifest.modules {
            module.axioms = Some(Vec::new());
        }
        let validated = validate_manifest(manifest).unwrap();
        let lock = proof_lock();

        let report = verify_package_fast_source_free_from_root_with_options(
            &validated,
            &lock,
            proofs_root(),
            selected_module_options("Proofs.Ai.Algebra.AbstractGroup"),
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("one module fails");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            failed.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::AxiomPolicyRejected
        );
    }

    fn verify_proof_package(
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    ) -> PackageVerificationResult<PackageVerificationReport> {
        verify_package_fast_source_free(validated, lock, package_certificate_artifacts(artifacts))
    }

    fn verify_proof_package_reference(
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    ) -> PackageVerificationResult<PackageVerificationReport> {
        verify_package_reference_source_free(
            validated,
            lock,
            package_certificate_artifacts(artifacts),
        )
    }

    fn without_memo_counters(mut report: PackageVerificationReport) -> PackageVerificationReport {
        report.memo_counters = PackageVerificationMemoCounters::default();
        report
    }

    fn without_decode_cache_counters(
        mut report: PackageVerificationReport,
    ) -> PackageVerificationReport {
        report.decode_cache_counters = None;
        report
    }

    fn module_evidence(
        report: &PackageVerificationReport,
        module: &Name,
    ) -> PackageModuleVerificationEvidence {
        report
            .modules
            .iter()
            .find(|result| &result.module == module)
            .map(|result| result.evidence)
            .expect("module result exists")
    }

    fn selected_module_options(module: &str) -> PackageVerificationExecutionOptions {
        PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::from([Name::from_dotted(module)])),
            ..PackageVerificationExecutionOptions::default()
        }
    }

    fn test_process_memo_handle() -> PackageVerificationProcessMemoHandle {
        PackageVerificationProcessMemoHandle::new(PackageVerificationProcessMemoLimits {
            max_entries: NonZeroUsize::new(10_000).unwrap(),
            max_weighted_certificate_bytes: NonZeroU64::new(1 << 40).unwrap(),
        })
    }

    fn test_process_memo_limits(
        max_entries: usize,
        max_weighted_certificate_bytes: u64,
    ) -> PackageVerificationProcessMemoLimits {
        PackageVerificationProcessMemoLimits {
            max_entries: NonZeroUsize::new(max_entries).unwrap(),
            max_weighted_certificate_bytes: NonZeroU64::new(max_weighted_certificate_bytes)
                .unwrap(),
        }
    }

    fn test_failed_memo_value(module: &str) -> Arc<PackageVerificationMemoEntry> {
        Arc::new(PackageVerificationMemoEntry::Failed {
            result: PackageModuleVerificationResult {
                module: Name::from_dotted(module),
                checker_mode: PackageVerificationMode::FastKernel,
                status: PackageModuleVerificationStatus::Failed,
                evidence: PackageModuleVerificationEvidence::LiveChecker,
                export_hash: PackageHash::new(test_hash(1)),
                axiom_report_hash: PackageHash::new(test_hash(2)),
                certificate_hash: PackageHash::new(test_hash(3)),
                certificate_format: None,
                core_spec: None,
                error: None,
            },
        })
    }

    #[test]
    fn package_verification_process_memo_limits_are_explicit_nonzero_values() {
        let limits = test_process_memo_limits(3, 17);
        assert_eq!(limits.max_entries.get(), 3);
        assert_eq!(limits.max_weighted_certificate_bytes.get(), 17);
    }

    #[test]
    fn package_verification_process_memo_access_error_is_stable() {
        let error = PackageVerificationProcessMemoAccessError::Poisoned;
        assert_eq!(error, error.clone());
        assert_eq!(format!("{error:?}"), "Poisoned");
    }

    #[test]
    fn package_verification_process_memo_stats_has_closed_fields() {
        let stats = PackageVerificationProcessMemoStats::default();
        assert_eq!(
            stats,
            PackageVerificationProcessMemoStats {
                retained_entries: 0,
                retained_weighted_certificate_bytes: 0,
                cumulative_hits: 0,
                cumulative_misses: 0,
                cumulative_inserted: 0,
                cumulative_evicted: 0,
                cumulative_rejected_oversize: 0,
            }
        );
    }

    #[test]
    fn package_verification_process_memo_empty_store_invariants() {
        let store = BoundedPackageVerificationProcessMemo::default();
        assert!(store.entries.is_empty());
        assert!(store.recency.is_empty());
        assert_eq!(
            store.stats(),
            PackageVerificationProcessMemoStats::default()
        );
    }

    #[test]
    fn package_verification_process_memo_handle_new_is_fresh() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 9));
        assert_eq!(
            handle.stats().unwrap(),
            PackageVerificationProcessMemoStats::default()
        );
    }

    #[test]
    fn package_verification_process_memo_limits_are_lock_free() {
        let limits = test_process_memo_limits(2, 9);
        let handle = PackageVerificationProcessMemoHandle::new(limits);
        let poisoned = handle.clone();
        let _ = std::thread::spawn(move || {
            let _guard = poisoned.inner.lock().unwrap();
            panic!("poison memo store for limits test");
        })
        .join();
        assert_eq!(handle.limits(), limits);
        assert_eq!(
            handle.stats(),
            Err(PackageVerificationProcessMemoAccessError::Poisoned)
        );
    }

    #[test]
    fn package_verification_process_memo_clone_shares_store() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 9));
        let clone = handle.clone();
        clone
            .insert("a".to_owned(), test_failed_memo_value("A"), 4)
            .unwrap();
        assert_eq!(handle.stats().unwrap().retained_entries, 1);
    }

    #[test]
    fn package_verification_process_memo_handle_identity() {
        let limits = test_process_memo_limits(2, 9);
        let handle = PackageVerificationProcessMemoHandle::new(limits);
        assert_eq!(handle, handle.clone());
        assert_ne!(handle, PackageVerificationProcessMemoHandle::new(limits));
    }

    #[test]
    fn package_verification_process_memo_handle_debug_is_redacted() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 9));
        handle
            .insert(
                "secret-key".to_owned(),
                test_failed_memo_value("Secret.Module"),
                4,
            )
            .unwrap();
        let debug = format!("{handle:?}");
        assert!(debug.contains("max_entries"));
        assert!(debug.contains("max_weighted_certificate_bytes"));
        assert!(!debug.contains("secret-key"));
        assert!(!debug.contains("Secret.Module"));
    }

    #[test]
    fn package_verification_process_memo_stats_is_side_effect_free() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 9));
        let first = handle.stats().unwrap();
        let second = handle.stats().unwrap();
        assert_eq!(first, second);
    }

    #[test]
    fn package_verification_process_memo_handle_clear_postcondition() {
        let limits = test_process_memo_limits(2, 9);
        let handle = PackageVerificationProcessMemoHandle::new(limits);
        let clone = handle.clone();
        handle
            .insert("a".to_owned(), test_failed_memo_value("A"), 4)
            .unwrap();
        assert!(clone.stats().unwrap().cumulative_inserted > 0);
        clone.clear().unwrap();
        assert_eq!(
            handle.stats().unwrap(),
            PackageVerificationProcessMemoStats::default()
        );
        assert_eq!(handle.limits(), limits);
    }

    #[test]
    fn package_verification_process_memo_recency_overflow_preserves_lru_order() {
        let limits = test_process_memo_limits(2, 20);
        let mut store = BoundedPackageVerificationProcessMemo::default();
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A"), 4);
        store.insert(limits, "b".to_owned(), test_failed_memo_value("B"), 4);
        store.recency_sequence = u64::MAX;
        assert!(store.lookup("a").is_some());
        let ordered = store
            .recency
            .iter()
            .map(|(_, key)| key.as_str())
            .collect::<Vec<_>>();
        assert_eq!(ordered, vec!["b", "a"]);
        assert_eq!(store.entries.len(), store.recency.len());
    }

    #[test]
    fn package_verification_process_memo_lookup_refreshes_lru() {
        let limits = test_process_memo_limits(2, 20);
        let mut store = BoundedPackageVerificationProcessMemo::default();
        let value = test_failed_memo_value("A");
        store.insert(limits, "a".to_owned(), Arc::clone(&value), 4);
        store.insert(limits, "b".to_owned(), test_failed_memo_value("B"), 4);
        let hit = store.lookup("a").unwrap();
        assert!(Arc::ptr_eq(&value, &hit));
        store.insert(limits, "c".to_owned(), test_failed_memo_value("C"), 4);
        assert!(store.entries.contains_key("a"));
        assert!(!store.entries.contains_key("b"));
        assert!(store.entries.contains_key("c"));
        assert_eq!(store.cumulative_hits, 1);
    }

    #[test]
    fn package_verification_process_memo_oversize_rejection_does_not_evict() {
        let limits = test_process_memo_limits(2, 8);
        let mut store = BoundedPackageVerificationProcessMemo::default();
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A"), 4);
        let before = store.stats();
        assert_eq!(
            store.insert(limits, "huge".to_owned(), test_failed_memo_value("Huge"), 9),
            BoundedMemoInsertOutcome::RejectedOversize
        );
        let after = store.stats();
        assert_eq!(after.retained_entries, before.retained_entries);
        assert_eq!(
            after.retained_weighted_certificate_bytes,
            before.retained_weighted_certificate_bytes
        );
        assert_eq!(after.cumulative_evicted, before.cumulative_evicted);
    }

    #[test]
    fn package_verification_process_memo_replacement_has_exact_weight_and_recency() {
        let limits = test_process_memo_limits(2, 20);
        let mut store = BoundedPackageVerificationProcessMemo::default();
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A"), 4);
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A2"), 7);
        assert_eq!(store.entries.len(), 1);
        assert_eq!(store.recency.len(), 1);
        assert_eq!(store.retained_weighted_certificate_bytes, 7);
        assert_eq!(store.cumulative_evicted, 0);
    }

    #[test]
    fn package_verification_process_memo_multi_eviction_enforces_both_limits() {
        let limits = test_process_memo_limits(3, 10);
        let mut store = BoundedPackageVerificationProcessMemo::default();
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A"), 3);
        store.insert(limits, "b".to_owned(), test_failed_memo_value("B"), 3);
        store.insert(limits, "c".to_owned(), test_failed_memo_value("C"), 3);
        assert_eq!(
            store.insert(limits, "d".to_owned(), test_failed_memo_value("D"), 7),
            BoundedMemoInsertOutcome::Inserted { evicted: 2 }
        );
        assert_eq!(store.entries.len(), 2);
        assert_eq!(store.retained_weighted_certificate_bytes, 10);
        assert_eq!(store.cumulative_evicted, 2);
    }

    #[test]
    fn package_verification_process_memo_cumulative_counters_saturate() {
        let limits = test_process_memo_limits(1, 8);
        let mut store = BoundedPackageVerificationProcessMemo {
            cumulative_hits: u64::MAX,
            cumulative_misses: u64::MAX,
            cumulative_inserted: u64::MAX,
            cumulative_evicted: u64::MAX,
            cumulative_rejected_oversize: u64::MAX,
            ..BoundedPackageVerificationProcessMemo::default()
        };
        assert!(store.lookup("missing").is_none());
        store.insert(limits, "a".to_owned(), test_failed_memo_value("A"), 4);
        assert!(store.lookup("a").is_some());
        store.insert(limits, "b".to_owned(), test_failed_memo_value("B"), 4);
        store.insert(limits, "huge".to_owned(), test_failed_memo_value("Huge"), 9);
        let stats = store.stats();
        assert_eq!(stats.cumulative_hits, u64::MAX);
        assert_eq!(stats.cumulative_misses, u64::MAX);
        assert_eq!(stats.cumulative_inserted, u64::MAX);
        assert_eq!(stats.cumulative_evicted, u64::MAX);
        assert_eq!(stats.cumulative_rejected_oversize, u64::MAX);
    }

    #[test]
    fn package_verification_process_memo_handle_lookup_is_fallible() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 20));
        assert!(handle.lookup("a").unwrap().is_none());
        let value = test_failed_memo_value("A");
        handle
            .insert("a".to_owned(), Arc::clone(&value), 4)
            .unwrap();
        let hit = handle.lookup("a").unwrap().unwrap();
        assert!(Arc::ptr_eq(&value, &hit));
    }

    #[test]
    fn package_verification_process_memo_handle_insertion_is_fallible() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(1, 8));
        assert_eq!(
            handle
                .insert("a".to_owned(), test_failed_memo_value("A"), 4)
                .unwrap(),
            BoundedMemoInsertOutcome::Inserted { evicted: 0 }
        );
        assert_eq!(
            handle
                .insert("b".to_owned(), test_failed_memo_value("B"), 4)
                .unwrap(),
            BoundedMemoInsertOutcome::Inserted { evicted: 1 }
        );
        assert_eq!(
            handle
                .insert("huge".to_owned(), test_failed_memo_value("Huge"), 9)
                .unwrap(),
            BoundedMemoInsertOutcome::RejectedOversize
        );
    }

    #[test]
    fn package_verification_execution_options_compare_memo_handle_identity() {
        let handle = test_process_memo_handle();
        let same = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
            ..PackageVerificationExecutionOptions::default()
        };
        assert_eq!(same, same.clone());
        assert_ne!(
            same,
            PackageVerificationExecutionOptions {
                memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
                ..PackageVerificationExecutionOptions::default()
            }
        );
    }

    #[test]
    fn package_verification_memo_counters_default_to_zero() {
        let counters = PackageVerificationMemoCounters::default();
        assert!(!counters.is_active());
        assert_eq!(counters.keys_built, 0);
        assert_eq!(counters.certificate_bytes_hashed, 0);
        assert_eq!(counters.evicted, 0);
        assert_eq!(counters.rejected_oversize, 0);
        assert_eq!(counters.bypassed_store_unavailable, 0);
    }

    #[test]
    fn package_verification_memo_counter_activity_covers_every_field() {
        let cases = vec![
            PackageVerificationMemoCounters {
                hits: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                misses: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                inserted: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                keys_built: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                certificate_bytes_hashed: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                evicted: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                rejected_oversize: 1,
                ..Default::default()
            },
            PackageVerificationMemoCounters {
                bypassed_store_unavailable: 1,
                ..Default::default()
            },
        ];
        assert!(cases
            .into_iter()
            .all(PackageVerificationMemoCounters::is_active));
    }

    #[test]
    fn package_verification_empty_closure_has_zero_acceleration_work() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let handle = test_process_memo_handle();
        let options = PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::new()),
            memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
            collect_decode_cache_counters: true,
            measurement_mode: PerformanceMeasurementMode::Summary,
            ..PackageVerificationExecutionOptions::default()
        };

        let fast = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            options.clone(),
        )
        .unwrap();
        let reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            options,
        )
        .unwrap();

        for report in [&fast, &reference] {
            assert_eq!(report.status, PackageVerificationStatus::Passed);
            assert!(report.topological_order.is_empty());
            assert!(report.modules.is_empty());
            assert_eq!(
                report.memo_counters,
                PackageVerificationMemoCounters::default()
            );
            assert_eq!(
                report.decode_cache_counters,
                Some(PackageVerificationDecodeCacheCounters::default())
            );
            assert!(report.measurements.is_some());
        }
        assert_eq!(
            handle.stats().unwrap(),
            PackageVerificationProcessMemoStats::default()
        );
    }

    #[test]
    fn package_verification_empty_cut_preserves_error_precedence() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let handle = test_process_memo_handle();
        let error = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Missing.Module")])),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::SelectedModuleMissing
        );
        assert_eq!(
            handle.stats().unwrap(),
            PackageVerificationProcessMemoStats::default()
        );
    }

    #[test]
    fn package_verification_process_memo_poison_is_acceleration_only() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let handle = test_process_memo_handle();
        let poisoned = handle.clone();
        let _ = std::thread::spawn(move || {
            let _guard = poisoned.inner.lock().unwrap();
            panic!("poison memo store for verifier fallback test");
        })
        .join();

        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert_eq!(report.memo_counters.hits, 0);
        assert_eq!(report.memo_counters.misses, 0);
        assert_eq!(report.memo_counters.bypassed_store_unavailable, 1);
        assert_eq!(
            handle.stats(),
            Err(PackageVerificationProcessMemoAccessError::Poisoned)
        );
        assert_eq!(
            handle.clear(),
            Err(PackageVerificationProcessMemoAccessError::Poisoned)
        );
    }

    #[test]
    fn package_verification_process_memo_distinct_handles_are_isolated() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let first_handle = test_process_memo_handle();
        let second_handle = test_process_memo_handle();
        for handle in [&first_handle, &second_handle] {
            let report = verify_package_fast_source_free_with_options(
                &validated,
                &lock,
                package_certificate_artifacts(&artifacts),
                PackageVerificationExecutionOptions {
                    selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                    memoization: PackageVerificationMemoMode::ProcessLocal((*handle).clone()),
                    ..PackageVerificationExecutionOptions::default()
                },
            )
            .unwrap();
            assert_eq!(report.memo_counters.hits, 0);
            assert_eq!(report.memo_counters.misses, 1);
        }
        assert_eq!(first_handle.stats().unwrap().retained_entries, 1);
        assert_eq!(second_handle.stats().unwrap().retained_entries, 1);
    }

    #[test]
    fn package_verification_process_memo_shared_handle_is_capacity_safe() {
        let limits = test_process_memo_limits(4, 16);
        let handle = PackageVerificationProcessMemoHandle::new(limits);
        std::thread::scope(|scope| {
            for worker in 0..8 {
                let handle = handle.clone();
                scope.spawn(move || {
                    for item in 0..32 {
                        let key = format!("{worker}-{item}");
                        let _ = handle.insert(
                            key.clone(),
                            test_failed_memo_value(&format!("M{worker}.{item}")),
                            4,
                        );
                        let _ = handle.lookup(&key);
                    }
                });
            }
        });
        let stats = handle.stats().unwrap();
        assert!(stats.retained_entries <= limits.max_entries.get());
        assert!(
            stats.retained_weighted_certificate_bytes
                <= limits.max_weighted_certificate_bytes.get()
        );
    }

    #[test]
    fn package_verification_process_memo_concurrent_handles_are_isolated() {
        let handles = [
            PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 8)),
            PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 8)),
        ];
        std::thread::scope(|scope| {
            for (index, handle) in handles.iter().cloned().enumerate() {
                scope.spawn(move || {
                    for item in 0..16 {
                        handle
                            .insert(
                                format!("{index}-{item}"),
                                test_failed_memo_value(&format!("H{index}.{item}")),
                                4,
                            )
                            .unwrap();
                    }
                });
            }
        });
        for handle in &handles {
            let stats = handle.stats().unwrap();
            assert_eq!(stats.retained_entries, 2);
            assert_eq!(stats.retained_weighted_certificate_bytes, 8);
            assert_eq!(stats.cumulative_inserted, 16);
            assert_eq!(stats.cumulative_evicted, 14);
        }
    }

    #[test]
    fn package_memo_mutex_scope_releases_before_projection_and_live_check() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 8));
        handle
            .insert("a".to_owned(), test_failed_memo_value("A"), 4)
            .unwrap();
        let retained_value = handle.lookup_then("a", |retained_value| {
            let available = handle
                .inner
                .try_lock()
                .expect("memo lookup released the store before projection callback");
            drop(available);
            let retained_value = retained_value.unwrap().unwrap();
            assert!(matches!(
                retained_value.as_ref(),
                PackageVerificationMemoEntry::Failed { .. }
            ));
            let stats = handle.stats().unwrap();
            assert_eq!(stats.retained_entries, 1);
            retained_value
        });
        let stats = handle.stats().unwrap();
        assert_eq!(stats.retained_entries, 1);
        assert!(matches!(
            retained_value.as_ref(),
            PackageVerificationMemoEntry::Failed { .. }
        ));
    }

    #[test]
    fn package_verification_memo_key_scope_matrix() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        for selected_module in ["Proofs.Ai.Basic", "Proofs.Ai.Eq"] {
            let handle = test_process_memo_handle();
            let report = verify_package_fast_source_free_with_options(
                &validated,
                &lock,
                package_certificate_artifacts(&artifacts),
                PackageVerificationExecutionOptions {
                    selected_modules: Some(BTreeSet::from([Name::from_dotted(selected_module)])),
                    memoization: PackageVerificationMemoMode::ProcessLocal(handle),
                    ..PackageVerificationExecutionOptions::default()
                },
            )
            .unwrap();
            assert_eq!(report.memo_counters.keys_built, report.modules.len());
            let expected_bytes = report
                .modules
                .iter()
                .map(|module| {
                    let entry = lock
                        .entries
                        .iter()
                        .find(|entry| entry.module == module.module)
                        .unwrap();
                    u64::try_from(artifacts.get(&entry.certificate).unwrap().len()).unwrap()
                })
                .fold(0, u64::saturating_add);
            assert_eq!(
                report.memo_counters.certificate_bytes_hashed,
                expected_bytes
            );
        }
    }

    // These exact names are permanent task-ledger entry points. Keep each
    // wrapper substantive by routing it through the consolidated oracle that
    // now owns the corresponding invariant.
    #[test]
    fn package_verification_process_memo_handle_clone_identity_is_explicit() {
        package_verification_process_memo_clone_shares_store();
        package_verification_process_memo_handle_identity();
        package_verification_process_memo_handle_clear_postcondition();
    }

    #[test]
    fn package_fast_empty_execution_closure_returns_before_acceleration_work() {
        package_verification_empty_closure_has_zero_acceleration_work();
    }

    #[test]
    fn package_reference_empty_execution_closure_returns_before_acceleration_work() {
        package_verification_empty_closure_has_zero_acceleration_work();
    }

    #[test]
    fn package_verification_canonical_empty_report_fields() {
        package_verification_empty_closure_has_zero_acceleration_work();
    }

    #[test]
    fn package_verification_empty_cut_matches_zero_iteration_oracle() {
        package_verification_empty_closure_has_zero_acceleration_work();
    }

    #[test]
    fn package_verification_memo_disabled_run_builds_no_keys() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                memoization: PackageVerificationMemoMode::Disabled,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert_eq!(
            report.memo_counters,
            PackageVerificationMemoCounters::default()
        );
    }

    #[test]
    fn package_verification_memo_failure_differential_matrix() {
        package_verifier_memo_fast_matches_disabled_normalized_and_reuses_second_run();
        package_verifier_memo_failure_hit_still_skips_dependent_deterministically();
    }

    #[test]
    fn package_verification_memo_key_weight_is_certificate_slice_length() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected_name = Name::from_dotted("Proofs.Ai.Basic");
        let expected_weight = lock
            .entries
            .iter()
            .find(|entry| entry.module == selected_name)
            .and_then(|entry| artifacts.get(&entry.certificate))
            .map(|bytes| u64::try_from(bytes.len()).unwrap())
            .unwrap();
        let handle = test_process_memo_handle();
        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::from([selected_name])),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(
            report.memo_counters.certificate_bytes_hashed,
            expected_weight
        );
        assert_eq!(
            handle.stats().unwrap().retained_weighted_certificate_bytes,
            expected_weight
        );
    }

    #[test]
    fn package_verification_memo_keys_visit_only_execution_closure() {
        package_verification_memo_key_scope_matrix();
    }

    #[test]
    fn package_verification_memo_raw_key_work_counters_are_exact() {
        package_verification_memo_key_scope_matrix();
    }

    #[test]
    fn package_verification_process_memo_arc_value_preserves_all_variants() {
        package_verifier_memo_fast_matches_disabled_normalized_and_reuses_second_run();
        package_verifier_memo_reference_explicit_handle_reuses_second_run();
        package_verifier_memo_failure_hit_still_skips_dependent_deterministically();
    }

    #[test]
    fn package_verification_process_memo_lock_is_not_held_during_live_check() {
        package_memo_mutex_scope_releases_before_projection_and_live_check();
    }

    #[test]
    fn package_verification_process_memo_lru_sequence_is_deterministic() {
        package_verification_process_memo_lookup_refreshes_lru();
        package_verification_process_memo_replacement_has_exact_weight_and_recency();
        package_verification_process_memo_multi_eviction_enforces_both_limits();
    }

    #[test]
    fn package_verification_process_memo_store_clear_restores_fresh_state() {
        package_verification_process_memo_handle_clear_postcondition();
        package_verification_process_memo_clear_resets_saturated_state();
    }

    #[test]
    fn package_verification_process_memo_weight_is_variant_independent() {
        package_verification_memo_key_weight_is_certificate_slice_length();
        package_verifier_memo_reference_explicit_handle_reuses_second_run();
        package_verifier_memo_failure_hit_still_skips_dependent_deterministically();
    }

    #[test]
    fn package_verifier_memo_fast_explicit_handle_reuses_second_run() {
        package_verifier_memo_fast_matches_disabled_normalized_and_reuses_second_run();
    }

    #[test]
    fn package_verification_public_memo_key_inputs_remain_all_entry() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert_eq!(inputs.len(), lock.entries.len());
    }

    #[test]
    fn package_verification_memo_unrelated_lock_edit_invalidates_scoped_key() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let artifacts = proof_certificate_artifacts(&lock);
        let artifact_bytes = artifact_byte_map(package_certificate_artifacts(&artifacts)).unwrap();
        let entries = canonical_lock_entries(&lock);
        let selected = BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]);
        let first = package_verification_memo_keys(
            &validated,
            &lock,
            &graph,
            &entries,
            &selected,
            &artifact_bytes,
            PackageVerificationMode::FastKernel,
        )
        .unwrap()
        .0;

        let mut changed_lock = lock.clone();
        let unrelated = changed_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module.as_dotted() != "Proofs.Ai.Basic")
            .unwrap();
        unrelated.certificate_hash = PackageHash::new([0x5a; 32]);
        let changed_entries = canonical_lock_entries(&changed_lock);
        let second = package_verification_memo_keys(
            &validated,
            &changed_lock,
            &graph,
            &changed_entries,
            &selected,
            &artifact_bytes,
            PackageVerificationMode::FastKernel,
        )
        .unwrap()
        .0;
        assert_ne!(first, second);
        assert_eq!(first.len(), 1);
        assert_eq!(second.len(), 1);
    }

    #[test]
    fn package_fast_root_empty_selection_reads_no_certificate() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let missing_root = proofs_root().join("does-not-exist");
        let report = verify_package_fast_source_free_from_root_with_options(
            &validated,
            &lock,
            missing_root,
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::new()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert!(report.modules.is_empty());
    }

    #[test]
    fn package_reference_root_empty_selection_reads_no_certificate() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let missing_root = proofs_root().join("does-not-exist");
        let report = verify_package_reference_source_free_from_root_with_options(
            &validated,
            &lock,
            missing_root,
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::new()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert!(report.modules.is_empty());
    }

    #[test]
    fn package_verification_process_memo_clear_resets_saturated_state() {
        let handle = PackageVerificationProcessMemoHandle::new(test_process_memo_limits(2, 20));
        {
            let mut store = handle.inner.lock().unwrap();
            store.cumulative_hits = u64::MAX;
            store.cumulative_misses = u64::MAX;
            store.cumulative_inserted = u64::MAX;
            store.cumulative_evicted = u64::MAX;
            store.cumulative_rejected_oversize = u64::MAX;
            store.insert(
                handle.limits(),
                "a".to_owned(),
                test_failed_memo_value("A"),
                4,
            );
        }
        handle.clear().unwrap();
        assert_eq!(
            handle.stats().unwrap(),
            PackageVerificationProcessMemoStats::default()
        );
        assert_eq!(
            handle
                .insert("b".to_owned(), test_failed_memo_value("B"), 4)
                .unwrap(),
            BoundedMemoInsertOutcome::Inserted { evicted: 0 }
        );
    }

    #[test]
    fn use_fast_serial_report_path_accepts_only_ordinary_full_run() {
        assert!(use_fast_serial_report_path(
            &PackageVerificationExecutionOptions::default()
        ));
    }

    #[test]
    fn use_fast_serial_report_path_rejects_each_nonordinary_option() {
        let selected = PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::new()),
            ..PackageVerificationExecutionOptions::default()
        };
        let parallel = PackageVerificationExecutionOptions {
            jobs: 2,
            ..PackageVerificationExecutionOptions::default()
        };
        let memo = PackageVerificationExecutionOptions {
            memoization: PackageVerificationMemoMode::ProcessLocal(test_process_memo_handle()),
            ..PackageVerificationExecutionOptions::default()
        };
        let decode = PackageVerificationExecutionOptions {
            decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
            ..PackageVerificationExecutionOptions::default()
        };
        let counters = PackageVerificationExecutionOptions {
            collect_decode_cache_counters: true,
            ..PackageVerificationExecutionOptions::default()
        };
        let measured = PackageVerificationExecutionOptions {
            measurement_mode: PerformanceMeasurementMode::Summary,
            ..PackageVerificationExecutionOptions::default()
        };
        for options in [selected, parallel, memo, decode, counters, measured] {
            assert!(!use_fast_serial_report_path(&options));
        }
    }

    fn decode_cache_test_lock() -> MutexGuard<'static, ()> {
        static LOCK: Mutex<()> = Mutex::new(());
        LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    #[test]
    fn package_verifier_default_options_do_not_populate_decode_cache() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let fast = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(fast.status, PackageVerificationStatus::Passed);
        assert_eq!(package_verification_decode_cache_entry_count(), 0);

        let reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(reference.status, PackageVerificationStatus::Passed);
        assert_eq!(package_verification_decode_cache_entry_count(), 0);
    }

    #[test]
    fn package_verifier_from_root_matches_buffered_selected_module() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));
        let root = proofs_root();

        let fast_buffered = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let fast_root = verify_package_fast_source_free_from_root_with_options(
            &validated,
            &lock,
            &root,
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(fast_root, fast_buffered);

        let reference_buffered = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let reference_root = verify_package_reference_source_free_from_root_with_options(
            &validated,
            &lock,
            &root,
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(reference_root, reference_buffered);
    }

    #[cfg(unix)]
    #[test]
    fn package_verifier_from_root_rejects_symlink_components_and_oversized_certificates() {
        use std::os::unix::fs::symlink;

        let unique = NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
        let root = std::env::temp_dir().join(format!(
            "npa-package-verifier-root-boundary-{}-{unique}",
            std::process::id()
        ));
        let outside = std::env::temp_dir().join(format!(
            "npa-package-verifier-root-boundary-outside-{}-{unique}",
            std::process::id()
        ));
        let relative = "npa-std/Std/Logic/Eq/certificate.npcert";
        fs::create_dir_all(outside.join("npa-std/Std/Logic/Eq")).unwrap();
        fs::write(
            outside.join(relative),
            fs::read(proofs_root().join("vendor").join(relative)).unwrap(),
        )
        .unwrap();
        fs::create_dir(&root).unwrap();
        symlink(&outside, root.join("vendor")).unwrap();

        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let options = selected_module_options("Std.Logic.Eq");
        for report in [
            verify_package_fast_source_free_from_root_with_options(
                &validated,
                &lock,
                &root,
                options.clone(),
            )
            .unwrap(),
            verify_package_reference_source_free_from_root_with_options(
                &validated,
                &lock,
                &root,
                options.clone(),
            )
            .unwrap(),
        ] {
            assert_eq!(report.status, PackageVerificationStatus::Failed);
            assert_eq!(
                report.modules[0].error.as_ref().unwrap().reason_code,
                PackageVerificationErrorReason::CertificateArtifactMissing
            );
        }

        fs::remove_file(root.join("vendor")).unwrap();
        let oversized_path = root.join("vendor").join(relative);
        fs::create_dir_all(oversized_path.parent().unwrap()).unwrap();
        fs::File::create(&oversized_path)
            .unwrap()
            .set_len(npa_cert::MAX_CERTIFICATE_BYTES as u64 + 1)
            .unwrap();
        let report = verify_package_fast_source_free_from_root_with_options(
            &validated, &lock, &root, options,
        )
        .unwrap();
        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            report.modules[0].error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::CertificateArtifactMissing
        );

        fs::remove_dir_all(&root).unwrap();
        fs::remove_dir_all(&outside).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn package_verifier_from_root_accepts_macos_fixed_temp_alias() {
        let temp_root = std::env::temp_dir();
        assert!(temp_root.starts_with("/var") || temp_root.starts_with("/private/var"));
        let reader = PackageCertificateRootReader::open(&temp_root).unwrap();
        let metadata = reader.root.metadata().unwrap();
        assert!(metadata.is_dir());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn package_verifier_does_not_rewrite_relative_tmp_components() {
        use std::os::unix::fs::MetadataExt as _;

        let tmp_parent = Path::new("tmp");
        let remove_tmp_parent = !tmp_parent.exists();
        let root = PathBuf::from("tmp").join(format!(
            "npa-package-relative-tmp-{}-{}",
            std::process::id(),
            NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir_all(&root).unwrap();
        let reader = PackageCertificateRootReader::open(&root).unwrap();
        let reopened = reader.root.metadata().unwrap();
        let selected = fs::metadata(&root).unwrap();

        assert_eq!(
            (reopened.dev(), reopened.ino()),
            (selected.dev(), selected.ino())
        );
        fs::remove_dir_all(&root).unwrap();
        if remove_tmp_parent {
            // A parallel test may have created another entry after this test
            // created the shared relative parent. Leave it in place in that
            // case instead of making cleanup order observable.
            let _ = fs::remove_dir(tmp_parent);
        }
    }

    #[cfg(unix)]
    #[test]
    fn package_verifier_from_root_accepts_parent_relative_roots() {
        use std::os::unix::fs::MetadataExt as _;

        let current = std::env::current_dir().unwrap();
        let current_name = current.file_name().unwrap();
        let selected = PathBuf::from("..").join(current_name);
        let reader = PackageCertificateRootReader::open(&selected).unwrap();
        let reopened = reader.root.metadata().unwrap();
        let retained = fs::metadata(".").unwrap();

        assert_eq!(
            (reopened.dev(), reopened.ino()),
            (retained.dev(), retained.ino())
        );
    }

    #[test]
    fn package_reference_import_retention_retires_after_last_direct_dependent() {
        let dep_a = Name::from_dotted("Test.DepA");
        let dep_b = Name::from_dotted("Test.DepB");
        let consumer_one = Name::from_dotted("Test.ConsumerOne");
        let consumer_two = Name::from_dotted("Test.ConsumerTwo");
        let import = |module: &Name, entry_index| PackageLockResolvedImport {
            module: module.clone(),
            entry_index,
            export_hash: PackageHash::new(test_hash(0xa1)),
            certificate_hash: PackageHash::new(test_hash(0xa2)),
        };
        let graph = PackageLockGraph {
            topological_order: vec![
                dep_a.clone(),
                dep_b.clone(),
                consumer_one.clone(),
                consumer_two,
            ],
            resolved_entry_imports: vec![
                Vec::new(),
                Vec::new(),
                vec![import(&dep_a, 0), import(&dep_b, 1)],
                vec![import(&dep_b, 1)],
            ],
        };
        let mut remaining_import_uses = BTreeMap::from([(dep_a.clone(), 1), (dep_b.clone(), 2)]);

        let retired =
            reference_modules_to_retire_after_module(2, &graph, &mut remaining_import_uses);
        assert_eq!(retired, vec![dep_a.clone()]);
        assert!(!remaining_import_uses.contains_key(&dep_a));
        assert_eq!(remaining_import_uses.get(&dep_b), Some(&1));

        let retired =
            reference_modules_to_retire_after_module(3, &graph, &mut remaining_import_uses);
        assert_eq!(retired, vec![dep_b.clone()]);
        assert!(remaining_import_uses.is_empty());
    }

    #[test]
    fn package_fast_verifier_verifies_proof_package_source_free() {
        run_on_large_stack(
            "package_fast_verifier_verifies_proof_package_source_free",
            package_fast_verifier_verifies_proof_package_source_free_on_large_stack,
        );
    }

    #[test]
    fn package_indexed_verifier_boundaries_match_source_compatible_wrappers() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let indexed = validate_package_lock_against_manifest_indexed(&validated, &lock).unwrap();

        let fast = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        let indexed_fast = verify_package_fast_source_free_with_options_indexed(
            &validated,
            &indexed,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        assert_eq!(indexed_fast, fast);

        let reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        let indexed_reference = verify_package_reference_source_free_with_options_indexed(
            &validated,
            &indexed,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions::default(),
        )
        .unwrap();
        assert_eq!(indexed_reference, reference);

        let memo = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        let indexed_memo = package_verification_memo_key_inputs_indexed(
            &validated,
            &indexed,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert_eq!(indexed_memo, memo);
    }

    fn package_fast_verifier_verifies_proof_package_source_free_on_large_stack() {
        let mut manifest = proof_manifest();
        for module in &mut manifest.modules {
            let module_path = module.module.as_dotted().replace('.', "/");
            module.source = PackagePath::new(format!("missing/source/{module_path}.npa"));
            module.meta = Some(PackagePath::new(format!("missing/meta/{module_path}.json")));
            module.replay = Some(PackagePath::new(format!(
                "missing/replay/{module_path}.json"
            )));
        }
        let validated = validate_manifest(manifest).unwrap();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);

        let report = verify_proof_package(&validated, &lock, &artifacts).unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert_eq!(report.mode, PackageVerificationMode::FastKernel);
        assert_eq!(
            report.verdict_source,
            PackageVerificationVerdictSource::FastKernelCertificateVerifier
        );
        assert!(!report.reference_checker_verdict);
        assert_eq!(report.modules.len(), lock.entries.len());
        assert!(report
            .modules
            .iter()
            .all(|module| module.status == PackageModuleVerificationStatus::Passed));
        assert!(report.modules.iter().all(|module| {
            module.certificate_format.as_deref() == Some("NPA-CERT-0.4.0")
                && module.core_spec.as_deref() == Some("NPA-Core-0.4.0")
        }));
    }

    #[test]
    fn linear_dag_missing_artifact_authority() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = BTreeMap::new();
        let options = selected_module_options("Std.Logic.Eq");
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let entries = canonical_lock_entries(indexed.lock());
        let execution_modules = execution_modules_for_indexed(&indexed, &options).unwrap();
        let empty_artifact_bytes = BTreeMap::<PackagePath, &[u8]>::new();
        let planning = PackageFastPlanningState::new(
            &entries,
            indexed.graph(),
            &execution_modules,
            &empty_artifact_bytes,
        );
        let (entry_index, entry) = entries
            .iter()
            .find(|(_, entry)| entry.module.as_dotted() == "Std.Logic.Eq")
            .copied()
            .unwrap();
        assert_eq!(planning.artifact_bytes_by_entry[entry_index], None);
        assert_eq!(planning.module_cost_by_entry[entry_index], None);

        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            options,
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("one module fails");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            failed.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::CertificateArtifactMissing
        );
        let error = failed.error.as_ref().unwrap();
        assert_eq!(error.kind, PackageVerificationErrorKind::Artifact);
        assert_eq!(error.path, format!("entries[{entry_index}].certificate"));
        assert_eq!(
            error.field.as_deref().map(String::as_str),
            Some("certificate")
        );
        assert_eq!(
            error.expected_value.as_deref(),
            Some(entry.certificate.as_str())
        );
        assert_eq!(error.actual_value, None);
    }

    #[test]
    fn package_fast_verifier_rejects_stale_certificate_file_hash() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let stale_entry = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Std.Logic.Eq")
            .expect("proof lock contains Std.Logic.Eq");
        let stale_path = stale_entry.certificate.clone();
        let mut artifacts = BTreeMap::from([(
            stale_path.clone(),
            read(proofs_root().join(stale_path.as_str())),
        )]);
        artifacts.get_mut(&stale_path).unwrap()[0] ^= 0x01;

        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            selected_module_options("Std.Logic.Eq"),
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("one module fails");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            failed.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::CertificateFileHashMismatch
        );
    }

    #[test]
    fn package_fast_verifier_rejects_disallowed_axioms_from_certificate() {
        let mut manifest = proof_manifest();
        manifest.policy.allowed_axioms.clear();
        for module in &mut manifest.modules {
            module.axioms = Some(Vec::new());
        }
        let validated = validate_manifest(manifest).unwrap();
        let lock = proof_lock();

        let report = verify_package_fast_source_free_from_root_with_options(
            &validated,
            &lock,
            proofs_root(),
            selected_module_options("Proofs.Ai.Algebra.AbstractGroup"),
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("one module fails");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            failed.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::AxiomPolicyRejected
        );
        assert!(failed
            .error
            .as_ref()
            .unwrap()
            .actual_value
            .as_ref()
            .unwrap()
            .contains("ForbiddenAxiom"));
    }

    #[test]
    fn package_fast_verifier_uses_lock_topological_order_not_lock_entry_order() {
        run_on_large_stack(
            "package_fast_verifier_uses_lock_topological_order_not_lock_entry_order",
            package_fast_verifier_uses_lock_topological_order_not_lock_entry_order_on_large_stack,
        );
    }

    fn package_fast_verifier_uses_lock_topological_order_not_lock_entry_order_on_large_stack() {
        let validated = validated_proof_manifest();
        let mut lock = proof_lock();
        lock.entries.reverse();
        let artifacts = proof_certificate_artifacts(&lock);

        let report = verify_proof_package(&validated, &lock, &artifacts).unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        let order = report
            .topological_order
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>();
        let std_eq = order
            .iter()
            .position(|module| module == "Std.Logic.Eq")
            .unwrap();
        let local_eq = order
            .iter()
            .position(|module| module == "Proofs.Ai.Eq")
            .unwrap();
        assert!(std_eq < local_eq);
        assert_eq!(
            report
                .modules
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            order
        );
    }

    #[test]
    fn package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized() {
        run_on_large_stack(
            "package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized",
            package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized_on_large_stack,
        );
    }

    fn package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);

        let jobs_one = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let jobs_four = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(jobs_four, jobs_one);
    }

    #[test]
    fn package_verifier_shards_plan_is_deterministic_and_context_complete() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let artifact_bytes = artifact_byte_map(package_certificate_artifacts(&artifacts)).unwrap();
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let entries = canonical_lock_entries(&lock);
        let selected_options = PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")])),
            ..PackageVerificationExecutionOptions::default()
        };
        let execution_modules =
            execution_modules_for_options(&entries, &graph, &selected_options).unwrap();
        let layers = execution_layers_for_modules(&entries, &graph, &execution_modules);
        let first_layer = layers
            .first()
            .expect("selected proof fixture has executable modules");
        assert!(first_layer.len() >= 2);
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let runnable = first_layer
            .iter()
            .map(|module| {
                *entries_by_module
                    .get(module)
                    .expect("layer module is a lock entry")
            })
            .collect::<Vec<_>>();

        let plan = plan_fast_verifier_shards(
            &runnable,
            &graph,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &artifact_bytes,
            4,
        )
        .expect("first layer has complete import context");
        let mut planned_indexes = plan
            .shards
            .iter()
            .flat_map(|shard| shard.member_indexes.iter().copied())
            .collect::<Vec<_>>();
        planned_indexes.sort_unstable();

        assert!(plan.shards.len() <= 4);
        assert_eq!(planned_indexes, (0..runnable.len()).collect::<Vec<_>>());
        assert_eq!(plan.effective_jobs, plan.shards.len());
        assert!(plan
            .module_costs
            .values()
            .all(|cost| cost.estimated_cost >= cost.artifact_bytes.max(1)));
        assert_eq!(
            plan,
            plan_fast_verifier_shards(
                &runnable,
                &graph,
                &BTreeSet::new(),
                &BTreeMap::new(),
                &artifact_bytes,
                4,
            )
            .expect("first layer has complete import context")
        );
        let dependent_layer = layers
            .iter()
            .find(|layer| {
                layer
                    .iter()
                    .any(|module| module.as_dotted() == "Proofs.Ai.Eq")
            })
            .expect("selected proof fixture has a dependent layer");
        let dependent_runnable = dependent_layer
            .iter()
            .map(|module| {
                *entries_by_module
                    .get(module)
                    .expect("layer module is a lock entry")
            })
            .collect::<Vec<_>>();
        assert!(plan_fast_verifier_shards(
            &dependent_runnable,
            &graph,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &artifact_bytes,
            4,
        )
        .is_none());
    }

    #[test]
    fn linear_dag_critical_path_binary_lifting_matches_vector_order() {
        fn push_path(
            paths: &mut Vec<Option<PackageFastCriticalPathState>>,
            module: &str,
            predecessor: Option<usize>,
        ) -> usize {
            let depth = predecessor
                .and_then(|entry| paths[entry].as_ref().map(|state| state.depth + 1))
                .unwrap_or(1);
            let mut jumps = Vec::new();
            if let Some(predecessor) = predecessor {
                jumps.push(Some(predecessor));
                let mut jump = 1usize;
                while let Some(ancestor) = jumps[jump - 1] {
                    let next = paths[ancestor]
                        .as_ref()
                        .and_then(|state| state.jump_ancestors.get(jump - 1).copied().flatten());
                    let Some(next) = next else { break };
                    jumps.push(Some(next));
                    jump += 1;
                }
            }
            let entry = paths.len();
            paths.push(Some(PackageFastCriticalPathState {
                cost: 7,
                predecessor,
                module: Name::from_dotted(module),
                depth,
                jump_ancestors: jumps,
                overflowed: false,
            }));
            entry
        }

        let mut paths = Vec::new();
        let a = push_path(&mut paths, "Path.A", None);
        let b = push_path(&mut paths, "Path.B", None);
        let ax = push_path(&mut paths, "Path.X", Some(a));
        let ay = push_path(&mut paths, "Path.Y", Some(a));
        let axz = push_path(&mut paths, "Path.Z", Some(ax));
        let by = push_path(&mut paths, "Path.Y2", Some(b));
        let entries = [a, b, ax, ay, axz, by];
        for left in entries {
            for right in entries {
                let expected = paths[left]
                    .as_ref()
                    .unwrap()
                    .cost
                    .cmp(&paths[right].as_ref().unwrap().cost)
                    .then_with(|| {
                        critical_path_modules(&paths, right)
                            .cmp(&critical_path_modules(&paths, left))
                    });
                assert_eq!(critical_path_state_cmp(&paths, left, right), expected);
            }
        }
        assert_eq!(critical_path_lca(&paths, axz, ay), Some(a));
        assert_eq!(critical_path_lca(&paths, axz, by), None);
    }

    #[test]
    fn package_fast_cost_and_memory_models_saturate_and_cap_jobs_deterministically() {
        let ordinary = package_module_cost_estimate_v1(10, 2);
        assert_eq!(ordinary.artifact_bytes, 10);
        assert_eq!(ordinary.direct_import_count, 2);
        assert_eq!(ordinary.estimated_cost, 10 + 2 * 4_096);
        assert!(!ordinary.overflowed);

        let overflowed = package_module_cost_estimate_v1(u64::MAX, u64::MAX);
        assert_eq!(overflowed.estimated_cost, u64::MAX);
        assert!(overflowed.overflowed);

        let width_limited = package_fast_shard_memory_estimate_v3(8, 3, 0, 0, 1, false);
        assert_eq!(width_limited.effective_jobs, 3);
        assert_eq!(
            width_limited.per_worker_bytes,
            u64::try_from(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES).unwrap()
                + PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1
                + 4
                + PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2
        );
        assert_eq!(
            width_limited.reduction_reason,
            PackageFastShardReductionReason::RunnableWidth
        );

        let memory_limited = package_fast_shard_memory_estimate_v3(16, 16, 0, 0, 1, false);
        assert!(memory_limited.effective_jobs < 16);
        assert_eq!(
            memory_limited.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let prepared_limited = package_fast_shard_memory_estimate_v3(
            4,
            4,
            128 * 1024 * 1024,
            512 * 1024 * 1024,
            1,
            false,
        );
        assert_eq!(
            prepared_limited.shared_base_context_bytes,
            128 * 1024 * 1024
        );
        assert_eq!(prepared_limited.prepared_shared_bytes, 512 * 1024 * 1024);
        assert_eq!(prepared_limited.combined_shared_bytes, 640 * 1024 * 1024);
        assert_eq!(prepared_limited.effective_jobs, 1);
        assert_eq!(
            prepared_limited.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let context_over_budget = package_fast_shard_memory_estimate_v3(
            4,
            4,
            PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
            0,
            1,
            false,
        );
        assert_eq!(context_over_budget.effective_jobs, 1);
        assert_eq!(
            context_over_budget.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let estimate_overflow = package_fast_shard_memory_estimate_v3(4, 4, 0, 0, u64::MAX, false);
        assert_eq!(estimate_overflow.effective_jobs, 1);
        assert_eq!(
            estimate_overflow.reduction_reason,
            PackageFastShardReductionReason::EstimateOverflow
        );
    }

    #[test]
    fn package_term_memory_model_arithmetic() {
        package_fast_cost_and_memory_models_saturate_and_cap_jobs_deterministically();
    }

    #[test]
    fn package_term_memory_model_landing_history() {
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV1.as_str(),
            "npa.fast-shard-memory.v1"
        );
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV2TermMaterialization.as_str(),
            "npa.fast-shard-memory.v2-term-materialization"
        );
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention
                .as_str(),
            "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
        );
        let v3 = package_fast_shard_memory_estimate_v3(4, 4, 10, 20, 1, false);
        assert_eq!(v3.shared_base_context_bytes, 10);
        assert_eq!(v3.prepared_shared_bytes, 20);
        assert_eq!(v3.combined_shared_bytes, 30);
    }

    #[test]
    fn package_term_memory_model_job_boundaries() {
        let base = package_fast_shard_memory_estimate_v3(1, 1, 0, 0, 1, false);
        let per_worker = base.per_worker_bytes;
        for jobs in 1..=4 {
            let estimate = package_fast_shard_memory_estimate_v3(jobs, 4, 0, 0, 1, false);
            let expected = jobs.min(
                usize::try_from(PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1 / per_worker).unwrap(),
            );
            assert_eq!(estimate.effective_jobs, expected.max(1));
            assert_eq!(estimate.per_worker_bytes, per_worker);
        }

        let two_worker_boundary = PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1 - 2 * per_worker;
        let below =
            package_fast_shard_memory_estimate_v3(4, 4, two_worker_boundary - 1, 0, 1, false);
        let exact = package_fast_shard_memory_estimate_v3(4, 4, two_worker_boundary, 0, 1, false);
        let above =
            package_fast_shard_memory_estimate_v3(4, 4, two_worker_boundary + 1, 0, 1, false);
        assert_eq!(
            (
                below.effective_jobs,
                exact.effective_jobs,
                above.effective_jobs
            ),
            (2, 2, 1)
        );
        assert_eq!(
            below.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );
        assert_eq!(
            exact.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );
        assert_eq!(
            above.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let overflow = package_fast_shard_memory_estimate_v3(4, 4, u64::MAX, 1, u64::MAX, true);
        assert_eq!(overflow.effective_jobs, 1);
        assert_eq!(
            overflow.reduction_reason,
            PackageFastShardReductionReason::EstimateOverflow
        );
        assert!(overflow.overflowed);
        package_fast_cost_and_memory_models_saturate_and_cap_jobs_deterministically();
    }

    #[test]
    fn package_term_materialization_requires_memory_model() {
        let estimate = package_fast_shard_memory_estimate_v3(2, 2, 0, 0, 1, false);
        assert!(estimate.per_worker_bytes >= 268_435_456);
        assert_eq!(
            PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2,
            268_435_456
        );
    }

    #[test]
    fn package_term_observation_serial_boundary() {
        let off = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Off);
        assert!(off.term_materialization.is_none());
        let enabled = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        assert_eq!(
            enabled.term_materialization,
            Some(CertificateTermMaterializationObservation::default())
        );

        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: None,
                memoization: PackageVerificationMemoMode::Disabled,
                decode_cache: PackageVerificationDecodeCacheMode::Disabled,
                collect_decode_cache_counters: false,
                measurement_mode: PerformanceMeasurementMode::Summary,
            },
        )
        .unwrap();
        let measurements = report.measurements.unwrap();
        let counter = |label| {
            measurements
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
                .unwrap_or(0)
        };
        assert!(counter(PerformanceMeasurementLabel::CertificateTermUniqueNodesMaterialized) > 0);
        assert!(
            counter(PerformanceMeasurementLabel::CertificateTermMaterializationChargedBytes) > 0
        );
        assert_eq!(
            counter(PerformanceMeasurementLabel::CertificateTermMaterializationCapacityStops),
            0
        );
    }

    #[test]
    fn package_worker_returns_term_observation() {
        let enabled = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        assert_eq!(
            enabled.term_materialization,
            Some(CertificateTermMaterializationObservation::default())
        );
        package_term_observation_serial_boundary();
    }

    #[test]
    fn package_worker_passed_and_failed_retain_term_observation() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let entries = canonical_lock_entries(&lock);
        let (entry_index, entry) = entries
            .iter()
            .copied()
            .find(|(_, entry)| entry.imports.is_empty())
            .expect("proof fixture contains one import-free entry");
        let artifact_bytes = artifacts
            .iter()
            .map(|(path, bytes)| (path.clone(), bytes.as_slice()))
            .collect::<BTreeMap<_, _>>();
        let mut session = VerifierSession::new();
        let passed = verify_fast_worker(
            entry_index,
            entry,
            &artifact_bytes,
            None,
            PackageFastWorkerImportContext::Session(&mut session),
            &package_fast_kernel_policy(&validated),
            &PackageVerificationDecodeCacheConfig::for_mode(
                &validated,
                PackageVerificationMode::FastKernel,
            ),
            PackageFastWorkerObservation {
                measurement_mode: PerformanceMeasurementMode::Summary,
                worker_index: 3,
            },
        );
        assert!(matches!(
            passed,
            PackageFastLayerWorkerResult::Passed { .. }
        ));
        let passed_observation = passed
            .measurement_observation()
            .term_materialization
            .expect("Summary worker retains term observation");
        assert!(passed_observation.unique_nodes_materialized > 0);
        assert!(passed_observation.materialization_charged_bytes > 0);
        assert_eq!(passed.worker_index(), 3);

        let invalid = semantically_invalid_unchecked_import_provider(
            build_module_cert(unchecked_import_provider(), &[]).unwrap(),
        );
        let invalid_bytes = npa_cert::encode_module_cert(&invalid).unwrap();
        let mut invalid_entry = entry.clone();
        invalid_entry.module = invalid.header().module.clone();
        invalid_entry.export_hash = PackageHash::new(invalid.hashes().export_hash);
        invalid_entry.axiom_report_hash = PackageHash::new(invalid.hashes().axiom_report_hash);
        invalid_entry.certificate_file_hash = package_file_hash(&invalid_bytes);
        invalid_entry.certificate_hash = PackageHash::new(invalid.hashes().certificate_hash);
        let corrupt_map = BTreeMap::from([(entry.certificate.clone(), invalid_bytes.as_slice())]);
        let mut session = VerifierSession::new();
        let failed = verify_fast_worker(
            entry_index,
            &invalid_entry,
            &corrupt_map,
            None,
            PackageFastWorkerImportContext::Session(&mut session),
            &package_fast_kernel_policy(&validated),
            &PackageVerificationDecodeCacheConfig::for_mode(
                &validated,
                PackageVerificationMode::FastKernel,
            ),
            PackageFastWorkerObservation {
                measurement_mode: PerformanceMeasurementMode::Summary,
                worker_index: 1,
            },
        );
        assert!(matches!(
            failed,
            PackageFastLayerWorkerResult::Failed { .. }
        ));
        assert_eq!(failed.worker_index(), 1);
        let failed_observation = failed
            .measurement_observation()
            .term_materialization
            .expect("failed worker retains term observation");
        assert!(failed_observation.unique_nodes_materialized > 0);
        assert!(failed_observation.materialization_charged_bytes > 0);
        assert!(failed.measurement_observation().checker_reached);
    }

    #[test]
    fn package_term_observation_canonical_merge() {
        let filled = |value, overflowed| CertificateTermMaterializationObservation {
            root_requests: value,
            unique_nodes_materialized: value,
            selected_edges: value,
            reused_child_arcs: value,
            owned_root_handoffs: value,
            leaf_root_clones: value,
            compound_root_clones: value,
            materialization_slots: value,
            materialization_charged_bytes: value,
            materialization_capacity_stops: value,
            materialization_legacy_fallbacks: value,
            overflowed,
        };
        let mut first = filled(2, false);
        let second = filled(5, false);
        first.merge(second);
        assert_eq!(first, filled(7, false));

        let mut overflow = filled(u64::MAX, false);
        overflow.merge(filled(1, false));
        assert_eq!(overflow, filled(u64::MAX, true));
    }

    #[test]
    fn package_term_observation_worker_permutations() {
        let filled = |value, overflowed| CertificateTermMaterializationObservation {
            root_requests: value,
            unique_nodes_materialized: value,
            selected_edges: value,
            reused_child_arcs: value,
            owned_root_handoffs: value,
            leaf_root_clones: value,
            compound_root_clones: value,
            materialization_slots: value,
            materialization_charged_bytes: value,
            materialization_capacity_stops: value,
            materialization_legacy_fallbacks: value,
            overflowed,
        };
        let observations = [filled(2, false), filled(5, true), filled(11, false)];
        let merge = |order: [usize; 3]| {
            let mut total = CertificateTermMaterializationObservation::default();
            for index in order {
                total.merge(observations[index]);
            }
            total
        };
        let expected = filled(18, true);
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            assert_eq!(merge(order), expected);
        }
    }

    #[test]
    fn package_fast_lpt_reduces_heterogeneous_max_cost_and_is_canonical() {
        fn estimate(cost: u64) -> PackageModuleCostEstimateV1 {
            PackageModuleCostEstimateV1 {
                artifact_bytes: cost,
                direct_import_count: 0,
                estimated_cost: cost,
                overflowed: false,
            }
        }

        let members = vec![
            (0, 0, Name::from_dotted("A"), estimate(100)),
            (1, 1, Name::from_dotted("B"), estimate(90)),
            (2, 2, Name::from_dotted("C"), estimate(10)),
            (3, 3, Name::from_dotted("D"), estimate(10)),
        ];
        let (shards, overflowed) = package_fast_lpt_shards(members.clone(), 2);
        let lpt_max = shards
            .iter()
            .map(|shard| shard.estimated_cost)
            .max()
            .unwrap();
        let equal_count_max = members[..2]
            .iter()
            .map(|member| member.3.estimated_cost)
            .sum::<u64>()
            .max(
                members[2..]
                    .iter()
                    .map(|member| member.3.estimated_cost)
                    .sum::<u64>(),
            );

        assert!(!overflowed);
        assert_eq!(lpt_max, 110);
        assert!(lpt_max < equal_count_max);
        assert_eq!(shards[0].member_indexes, vec![0, 3]);
        assert_eq!(shards[1].member_indexes, vec![1, 2]);
        assert!(shards.iter().all(|shard| shard
            .member_indexes
            .windows(2)
            .all(|pair| pair[0] < pair[1])));
    }

    #[test]
    fn package_fast_worker_failure_selection_is_stable_and_spawn_precedes_join() {
        let selected = select_package_fast_worker_infrastructure_failure(vec![
            PackageFastWorkerInfrastructureFailure {
                shard_index: 2,
                first_module: Name::from_dotted("C"),
                kind: PackageFastWorkerInfrastructureFailureKind::Spawn,
            },
            PackageFastWorkerInfrastructureFailure {
                shard_index: 0,
                first_module: Name::from_dotted("A"),
                kind: PackageFastWorkerInfrastructureFailureKind::Join,
            },
            PackageFastWorkerInfrastructureFailure {
                shard_index: 0,
                first_module: Name::from_dotted("A"),
                kind: PackageFastWorkerInfrastructureFailureKind::Spawn,
            },
        ])
        .unwrap();

        assert_eq!(selected.shard_index, 0);
        assert_eq!(
            selected.kind,
            PackageFastWorkerInfrastructureFailureKind::Spawn
        );
        let error = PackageVerificationError::fast_worker_infrastructure_failed(
            3,
            selected.shard_index,
            &selected.first_module,
            PackageVerificationErrorReason::FastWorkerSpawnFailed,
        );
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::FastWorkerSpawnFailed
        );
        assert_eq!(error.path, "execution.layers[3].shards[0]");
        assert_eq!(error.module.as_deref().map(String::as_str), Some("A"));
        assert_eq!(
            error.actual_value.as_deref(),
            Some("spawn_failed;first_module=A")
        );
    }

    #[test]
    fn package_fast_planner_uses_opaque_artifact_lengths_without_decoding() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let entries = canonical_lock_entries(&lock);
        let execution_modules = entries
            .iter()
            .map(|(_, entry)| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let layers = execution_layers_for_modules(&entries, &graph, &execution_modules);
        let first_layer = &layers[0];
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let runnable = first_layer
            .iter()
            .map(|module| *entries_by_module.get(module).unwrap())
            .collect::<Vec<_>>();
        let opaque_bytes = b"not a certificate".as_slice();
        let artifacts = runnable
            .iter()
            .map(|(_, entry)| (entry.certificate.clone(), opaque_bytes))
            .collect::<BTreeMap<_, _>>();

        let plan = plan_fast_verifier_shards(
            &runnable,
            &graph,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &artifacts,
            4,
        )
        .expect("planning treats certificate bytes as opaque cost input");

        assert!(plan
            .module_costs
            .values()
            .all(|cost| cost.artifact_bytes == u64::try_from(opaque_bytes.len()).unwrap()));
    }

    #[test]
    fn package_fast_borrowed_imports_require_exact_export_and_certificate_hashes() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let verification = verify_package_fast_source_free_with_modules(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
        )
        .unwrap();
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let resolved_imports = graph
            .resolved_entry_imports
            .iter()
            .find(|imports| !imports.is_empty())
            .expect("proof fixture has a dependent module");
        let verified_modules = verification
            .verified_modules
            .into_iter()
            .map(|record| (record.module.clone(), record))
            .collect::<BTreeMap<_, _>>();

        assert_eq!(
            exact_fast_import_refs(resolved_imports, &verified_modules).len(),
            resolved_imports.len()
        );

        let imported_module = &resolved_imports[0].module;
        let mut stale_export = verified_modules.clone();
        stale_export.get_mut(imported_module).unwrap().export_hash =
            PackageHash::new(test_hash(0x51));
        assert_eq!(
            exact_fast_import_refs(resolved_imports, &stale_export).len(),
            resolved_imports.len() - 1
        );

        let mut stale_certificate = verified_modules;
        stale_certificate
            .get_mut(imported_module)
            .unwrap()
            .certificate_hash = PackageHash::new(test_hash(0x52));
        assert_eq!(
            exact_fast_import_refs(resolved_imports, &stale_certificate).len(),
            resolved_imports.len() - 1
        );
    }

    #[test]
    fn package_verifier_shards_match_serial_and_legacy_parallel_success() {
        run_on_large_stack(
            "package_verifier_shards_match_serial_and_legacy_parallel_success",
            package_verifier_shards_match_serial_and_legacy_parallel_success_on_large_stack,
        );
    }

    fn package_verifier_shards_match_serial_and_legacy_parallel_success_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let serial = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let legacy_parallel = verify_package_fast_source_free_execution_with_strategy(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
            PackageFastParallelStrategy::LegacyLayer,
        )
        .unwrap()
        .report;
        let sharded = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: selected,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(legacy_parallel, serial);
        assert_eq!(sharded, serial);
    }

    #[test]
    fn package_verifier_cost_aware_shards_emit_canonical_bounded_measurements() {
        run_on_large_stack(
            "package_verifier_cost_aware_shards_emit_canonical_bounded_measurements",
            package_verifier_cost_aware_shards_emit_canonical_bounded_measurements_on_large_stack,
        );
    }

    fn package_verifier_cost_aware_shards_emit_canonical_bounded_measurements_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
                memoization: PackageVerificationMemoMode::Disabled,
                decode_cache: PackageVerificationDecodeCacheMode::Disabled,
                collect_decode_cache_counters: false,
                measurement_mode: PerformanceMeasurementMode::Detailed,
            },
        )
        .unwrap();
        let measurements = report.measurements.as_ref().unwrap();
        let sharding = measurements.package_sharding.as_ref().unwrap();

        assert_eq!(
            sharding.cost_model,
            PerformancePackageShardCostModel::FastShardCostV1
        );
        assert_eq!(
            sharding.memory_model,
            PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention
        );
        assert_eq!(sharding.prepared_shared_bytes, 0);
        assert_eq!(
            sharding.combined_shared_bytes,
            sharding.shared_base_context_bytes
        );
        assert_eq!(
            sharding.term_materialization_bytes_per_worker,
            PACKAGE_FAST_SHARD_TERM_MATERIALIZATION_BYTES_V2
        );
        assert_eq!(sharding.requested_jobs, 4);
        assert!(sharding.effective_jobs >= 1 && sharding.effective_jobs <= 4);
        assert_eq!(
            sharding.memory_budget_bytes,
            PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1
        );
        assert!(sharding.critical_path_module_count > 0);
        assert!(sharding.critical_path_identity.starts_with("sha256:"));
        assert_eq!(sharding.critical_path_identity.len(), 71);
        assert!(!measurements.package_layers.is_empty());
        assert!(!measurements.package_shards.is_empty());
        assert!(measurements
            .package_layers
            .windows(2)
            .all(|layers| layers[0].layer_index < layers[1].layer_index));
        assert!(measurements.package_shards.windows(2).all(|shards| {
            (shards[0].layer_index, shards[0].shard_index)
                < (shards[1].layer_index, shards[1].shard_index)
        }));
        assert!(measurements.modules.iter().all(|module| {
            module.package_sharding.as_ref().is_some_and(|detail| {
                detail.cost_model == PerformancePackageShardCostModel::FastShardCostV1
                    && detail.estimated_cost >= 1
                    && detail.layer_index.is_some()
                    && detail.shard_index.is_some()
            })
        }));
        assert_eq!(
            measurements
                .modules
                .iter()
                .filter(|module| module
                    .package_sharding
                    .as_ref()
                    .is_some_and(|detail| detail.critical_path))
                .count() as u64,
            sharding.critical_path_module_count
        );
    }

    #[test]
    fn package_verifier_shards_match_serial_and_legacy_parallel_failure() {
        run_on_large_stack(
            "package_verifier_shards_match_serial_and_legacy_parallel_failure",
            package_verifier_shards_match_serial_and_legacy_parallel_failure_on_large_stack,
        );
    }

    fn package_verifier_shards_match_serial_and_legacy_parallel_failure_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let mut artifacts = proof_certificate_artifacts(&lock);
        let stale_path = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Std.Logic.Eq")
            .expect("proof lock contains Std.Logic.Eq")
            .certificate
            .clone();
        artifacts.get_mut(&stale_path).unwrap()[0] ^= 0x01;
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")]));

        let serial = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let legacy_parallel = verify_package_fast_source_free_execution_with_strategy(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
            PackageFastParallelStrategy::LegacyLayer,
        )
        .unwrap()
        .report;
        let sharded = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: selected,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(serial.status, PackageVerificationStatus::Failed);
        assert_eq!(legacy_parallel, serial);
        assert_eq!(sharded, serial);
        let skipped = sharded
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Skipped)
            .expect("dependent module is skipped");
        assert_eq!(
            skipped.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
    }

    #[test]
    fn package_verifier_memo_fast_matches_disabled_normalized_and_reuses_second_run() {
        let handle = test_process_memo_handle();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let disabled = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let first = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let second = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(
            first.memo_counters,
            PackageVerificationMemoCounters {
                hits: 0,
                misses: 1,
                inserted: 1,
                keys_built: 1,
                certificate_bytes_hashed: u64::try_from(
                    artifacts
                        .get(
                            &lock
                                .entries
                                .iter()
                                .find(|entry| entry.module.as_dotted() == "Proofs.Ai.Basic")
                                .unwrap()
                                .certificate,
                        )
                        .unwrap()
                        .len(),
                )
                .unwrap(),
                ..PackageVerificationMemoCounters::default()
            }
        );
        assert_eq!(
            second.memo_counters,
            PackageVerificationMemoCounters {
                hits: 1,
                misses: 0,
                inserted: 0,
                keys_built: 1,
                certificate_bytes_hashed: first.memo_counters.certificate_bytes_hashed,
                ..PackageVerificationMemoCounters::default()
            }
        );
        assert_eq!(handle.stats().unwrap().retained_entries, 1);
        assert_eq!(
            without_memo_counters(first),
            without_memo_counters(disabled.clone())
        );
        assert_eq!(
            without_memo_counters(second),
            without_memo_counters(disabled)
        );
    }

    #[test]
    fn package_verifier_memo_reference_explicit_handle_reuses_second_run() {
        let handle = test_process_memo_handle();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let disabled = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let first = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let second = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(first.memo_counters.hits, 0);
        assert_eq!(first.memo_counters.misses, 1);
        assert_eq!(first.memo_counters.inserted, 1);
        assert_eq!(first.memo_counters.keys_built, 1);
        assert_eq!(second.memo_counters.hits, 1);
        assert_eq!(second.memo_counters.misses, 0);
        assert_eq!(second.memo_counters.inserted, 0);
        assert_eq!(second.memo_counters.keys_built, 1);
        assert_eq!(
            second.memo_counters.certificate_bytes_hashed,
            first.memo_counters.certificate_bytes_hashed
        );
        assert_eq!(handle.stats().unwrap().retained_entries, 1);
        assert_eq!(
            without_memo_counters(first),
            without_memo_counters(disabled.clone())
        );
        assert_eq!(
            without_memo_counters(second),
            without_memo_counters(disabled)
        );
    }

    #[test]
    fn package_verifier_v0_5_identity_misses_v0_4_process_memo_without_relabeling() {
        let handle = test_process_memo_handle();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));
        let inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        let current_input = inputs
            .get(&Name::from_dotted("Proofs.Ai.Basic"))
            .expect("proof fixture contains Proofs.Ai.Basic")
            .clone();
        assert_eq!(current_input.schema, PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA);
        assert_eq!(current_input.checker.checker_version, "0.5.0");
        let current_key = package_audit_process_memo_key(&current_input);

        let mut old_input = current_input.clone();
        old_input.checker.checker_version = "0.4.0".to_owned();
        old_input.checker.checker_build_hash = package_file_hash(
            format!(
                "schema=npa.package.verification_process_memo_checker_identity.v0.1\nmode={}\nchecker_id={}\nchecker_version=0.4.0\nchecker_profile={}\n",
                old_input.checker.mode,
                old_input.checker.checker_id,
                old_input.checker.checker_profile,
            )
            .as_bytes(),
        );
        assert_eq!(old_input.schema, PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA);
        let old_key = package_audit_process_memo_key(&old_input);
        assert_ne!(old_key, current_key);

        let first = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(
            first.memo_counters,
            PackageVerificationMemoCounters {
                hits: 0,
                misses: 1,
                inserted: 1,
                keys_built: 1,
                certificate_bytes_hashed: first.memo_counters.certificate_bytes_hashed,
                ..PackageVerificationMemoCounters::default()
            }
        );
        {
            let mut memo = handle
                .inner
                .lock()
                .expect("package verification process memo mutex should not be poisoned");
            let entry = memo
                .entries
                .remove(&current_key)
                .expect("current-version run inserted its current key");
            memo.recency.remove(&(entry.last_used, current_key.clone()));
            memo.recency.insert((entry.last_used, old_key.clone()));
            memo.entries.insert(old_key.clone(), entry);
        }

        let rebuilt = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(
            rebuilt.memo_counters,
            PackageVerificationMemoCounters {
                hits: 0,
                misses: 1,
                inserted: 1,
                keys_built: 1,
                certificate_bytes_hashed: rebuilt.memo_counters.certificate_bytes_hashed,
                ..PackageVerificationMemoCounters::default()
            }
        );
        let memo = handle
            .inner
            .lock()
            .expect("package verification process memo mutex should not be poisoned");
        assert!(memo.entries.contains_key(&old_key));
        assert!(memo.entries.contains_key(&current_key));
        drop(memo);
        assert_eq!(without_memo_counters(rebuilt), without_memo_counters(first));
    }

    #[test]
    fn package_verifier_memo_keeps_fast_and_reference_namespaces_separate() {
        let handle = test_process_memo_handle();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")]));

        let fast = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        let fast_verified_count = fast.modules.len();
        let reference_verified_count = reference.modules.len();
        assert_eq!(fast.memo_counters.hits, 0);
        assert_eq!(fast.memo_counters.misses, fast_verified_count);
        assert_eq!(fast.memo_counters.inserted, fast_verified_count);
        assert_eq!(reference.memo_counters.hits, 0);
        assert_eq!(reference.memo_counters.misses, reference_verified_count);
        assert_eq!(reference.memo_counters.inserted, reference_verified_count);
        assert_eq!(
            handle.stats().unwrap().retained_entries,
            fast_verified_count + reference_verified_count
        );
        assert_eq!(reference.status, PackageVerificationStatus::Passed);
    }

    #[test]
    fn package_verifier_memo_failure_hit_still_skips_dependent_deterministically() {
        let handle = test_process_memo_handle();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let mut artifacts = proof_certificate_artifacts(&lock);
        let stale_path = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Std.Logic.Eq")
            .expect("proof lock contains Std.Logic.Eq")
            .certificate
            .clone();
        artifacts.get_mut(&stale_path).unwrap()[0] ^= 0x01;
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")]));

        let first = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let second = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                memoization: PackageVerificationMemoMode::ProcessLocal(handle.clone()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(first.status, PackageVerificationStatus::Failed);
        assert_eq!(second.status, PackageVerificationStatus::Failed);
        assert_eq!(
            second
                .modules
                .iter()
                .map(|module| (module.module.as_dotted(), module.status))
                .collect::<Vec<_>>(),
            first
                .modules
                .iter()
                .map(|module| (module.module.as_dotted(), module.status))
                .collect::<Vec<_>>()
        );
        assert!(second.memo_counters.hits > 0);
        let skipped = second
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Proofs.Ai.Eq")
            .unwrap();
        assert_eq!(
            skipped.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
    }

    #[test]
    fn package_verifier_disk_memo_key_inputs_use_process_material_with_disk_schema_split() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let mut artifacts = proof_certificate_artifacts(&lock);
        let inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        let input = inputs
            .get(&Name::from_dotted("Proofs.Ai.Basic"))
            .expect("proof fixture contains Proofs.Ai.Basic");
        let process_key = package_audit_process_memo_key(input);
        let disk_key = package_audit_disk_memo_key(input);
        assert_ne!(process_key, disk_key);

        let basic_path = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Proofs.Ai.Basic")
            .expect("proof lock contains Proofs.Ai.Basic")
            .certificate
            .clone();
        artifacts.get_mut(&basic_path).unwrap()[0] ^= 0x01;
        let changed_inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        assert!(
            !changed_inputs.contains_key(&Name::from_dotted("Proofs.Ai.Basic")),
            "an input without an exact decoded pair cannot produce a v0.2 memo key"
        );
    }

    #[test]
    fn package_verified_result_cache_key_covers_persistent_identity_material() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        let input = inputs
            .get(&Name::from_dotted("Proofs.Ai.Eq"))
            .expect("proof fixture contains Proofs.Ai.Eq")
            .clone();
        let lock_entry = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Proofs.Ai.Eq")
            .expect("proof lock contains Proofs.Ai.Eq");
        let base_key = package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&input));

        assert_eq!(input.package_id, lock.package);
        assert_eq!(input.package_version, lock.version);
        assert_eq!(input.package_lock_schema, lock.schema);
        assert_eq!(input.origin, lock_entry.origin);
        assert_eq!(input.certificate, lock_entry.certificate);
        assert!(!input.direct_imports.is_empty());

        let mut changed = input.clone();
        changed.package_id = PackageId::new("other-package");
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.package_version = PackageVersion::new("9.9.9");
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.package_lock_schema = "npa.package.lock.v9".to_owned();
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.origin = PackageLockEntryOrigin::External;
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.certificate = PackagePath::new("Proofs/Ai/Eq/changed.npcert");
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.checker.checker_profile = "npa.checker.fast.changed".to_owned();
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.certificate_file_hash = PackageHash::new(test_hash(0xee));
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );

        let mut changed = input.clone();
        changed.direct_imports[0].export_hash = PackageHash::new(test_hash(0xdd));
        assert_ne!(
            base_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&changed))
        );
    }

    #[test]
    fn package_cache_aware_dag_verifier_live_checks_dirty_reverse_dependents() {
        run_on_large_stack(
            "package_cache_aware_dag_verifier_live_checks_dirty_reverse_dependents",
            package_cache_aware_dag_verifier_live_checks_dirty_reverse_dependents_on_large_stack,
        );
    }

    fn package_cache_aware_dag_verifier_live_checks_dirty_reverse_dependents_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let all_memo_hits = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let dirty = Name::from_dotted("Proofs.Ai.Algebra.AbstractGroup");

        let report = verify_package_fast_source_free_with_cache_aware_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            all_memo_hits,
            [dirty.clone()],
        )
        .unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert!(report.locally_accelerated);
        assert_eq!(
            module_evidence(&report, &dirty),
            PackageModuleVerificationEvidence::LiveChecker
        );
        assert_eq!(
            module_evidence(
                &report,
                &Name::from_dotted("Proofs.Ai.Algebra.AbstractGroupImage"),
            ),
            PackageModuleVerificationEvidence::LiveChecker
        );
        assert_eq!(
            module_evidence(&report, &Name::from_dotted("Proofs.Ai.Basic")),
            PackageModuleVerificationEvidence::DiskVerifierMemo
        );
        let cached = report
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
            .unwrap();
        assert_eq!(cached.certificate_format.as_deref(), Some("NPA-CERT-0.4.0"));
        assert_eq!(cached.core_spec.as_deref(), Some("NPA-Core-0.4.0"));
    }

    #[test]
    fn package_reference_summary_cache_key_uses_reference_profile_and_separate_schema() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let fast_inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::FastKernel,
        )
        .unwrap();
        let reference_inputs = package_verification_memo_key_inputs(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationMode::Reference,
        )
        .unwrap();
        let reference_input = reference_inputs
            .get(&Name::from_dotted("Proofs.Ai.Eq"))
            .expect("proof fixture contains Proofs.Ai.Eq")
            .clone();
        let fast_input = fast_inputs
            .get(&Name::from_dotted("Proofs.Ai.Eq"))
            .expect("proof fixture contains Proofs.Ai.Eq");
        let reference_key_input = package_reference_summary_cache_key_input(&reference_input);
        let reference_key = package_reference_summary_cache_key(&reference_key_input);

        assert_eq!(reference_input.checker.mode, "reference");
        assert_eq!(reference_input.checker.checker_id, "npa-checker-ref");
        assert_eq!(
            reference_input.checker.checker_profile,
            validated.manifest().checker_profile
        );
        assert_ne!(
            reference_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(fast_input))
        );
        assert_ne!(
            reference_key,
            package_audit_disk_memo_key(&package_audit_disk_memo_key_input(&reference_input))
        );
        assert!(!reference_key_input.direct_imports.is_empty());

        let mut changed = reference_input.clone();
        changed.checker.checker_profile = "npa.checker.reference.changed".to_owned();
        assert_ne!(
            reference_key,
            package_reference_summary_cache_key(&package_reference_summary_cache_key_input(
                &changed
            ))
        );

        let mut changed = reference_input.clone();
        changed.direct_imports[0].certificate_hash = PackageHash::new(test_hash(0xcc));
        assert_ne!(
            reference_key,
            package_reference_summary_cache_key(&package_reference_summary_cache_key_input(
                &changed
            ))
        );
    }

    #[test]
    fn package_verifier_disk_memo_hits_mark_proof_evidence_false() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let disk_hits = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();

        let report = verify_package_fast_source_free_with_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            disk_hits,
        )
        .unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert!(report.locally_accelerated);
        let module = report
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
            .expect("proof fixture contains Proofs.Ai.Basic");
        assert_eq!(
            module.evidence,
            PackageModuleVerificationEvidence::DiskVerifierMemo
        );
        assert!(!module.evidence.is_proof_evidence());
    }

    #[test]
    fn package_verifier_decode_cache_reuses_decoded_certificates_without_reusing_verdict() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let first = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let second = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        let first_counters = first
            .decode_cache_counters
            .expect("decode cache counters are requested");
        let second_counters = second
            .decode_cache_counters
            .expect("decode cache counters are requested");
        assert_eq!(first.status, PackageVerificationStatus::Passed);
        assert_eq!(second.status, PackageVerificationStatus::Passed);
        let first_certificate_lookups =
            first_counters.certificate_hits + first_counters.certificate_misses;
        assert!(first_certificate_lookups > 0);
        assert_eq!(
            first_counters.certificate_inserted,
            first_counters.certificate_misses
        );
        assert_eq!(second_counters.certificate_hits, first_certificate_lookups);
        assert_eq!(second_counters.certificate_misses, 0);
        assert_eq!(second_counters.certificate_inserted, 0);
        assert!(second
            .modules
            .iter()
            .all(|module| module.evidence == PackageModuleVerificationEvidence::LiveChecker));
    }

    #[test]
    fn package_measurements_preserve_decode_cache_hit_on_later_verifier_failure() {
        fn counter(
            report: &PerformanceMeasurementReport,
            label: PerformanceMeasurementLabel,
        ) -> u64 {
            report
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
                .expect("measurement counter is present")
        }

        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let manifest = proof_manifest();
        let target_module = manifest
            .modules
            .first()
            .expect("proof fixture has a local module")
            .module
            .clone();
        let validated = validate_manifest(manifest.clone()).unwrap();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([target_module.clone()]));
        let options = PackageVerificationExecutionOptions {
            selected_modules: selected.clone(),
            decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
            collect_decode_cache_counters: true,
            measurement_mode: PerformanceMeasurementMode::Detailed,
            ..PackageVerificationExecutionOptions::default()
        };

        let warm = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            options.clone(),
        )
        .unwrap();
        assert_eq!(warm.status, PackageVerificationStatus::Passed);
        assert!(
            counter(
                warm.measurements.as_ref().unwrap(),
                PerformanceMeasurementLabel::PackageModulesDecoded,
            ) > 0
        );

        let rejected_axiom_report_hash = PackageHash::new(test_hash(0xa7));
        let mut rejected_lock = lock.clone();
        rejected_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module == target_module)
            .unwrap()
            .axiom_report_hash = rejected_axiom_report_hash;
        let mut rejected_manifest = manifest;
        rejected_manifest
            .modules
            .iter_mut()
            .find(|module| module.module == target_module)
            .unwrap()
            .expected_axiom_report_hash = rejected_axiom_report_hash;
        let rejected = validate_manifest(rejected_manifest).unwrap();

        let failed = verify_package_fast_source_free_with_options(
            &rejected,
            &rejected_lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                ..options
            },
        )
        .unwrap();
        assert_eq!(failed.status, PackageVerificationStatus::Failed);
        let cache_counters = failed.decode_cache_counters.unwrap();
        assert!(cache_counters.certificate_hits > 0);
        let measurements = failed.measurements.as_ref().unwrap();
        assert_eq!(
            counter(
                measurements,
                PerformanceMeasurementLabel::PackageModulesDecoded,
            ),
            0
        );
        assert!(
            counter(
                measurements,
                PerformanceMeasurementLabel::PackageDecodeCacheHits,
            ) > 0
        );
    }

    #[test]
    fn package_verifier_decode_cache_corrupt_certificate_still_fails_like_uncached_run() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        let _warm = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        let mut corrupt_lock = lock.clone();
        let mut corrupt_artifacts = artifacts.clone();
        let target = corrupt_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module.as_dotted() == "Proofs.Ai.Basic")
            .expect("proof fixture contains Proofs.Ai.Basic");
        let bytes = corrupt_artifacts
            .get_mut(&target.certificate)
            .expect("artifact exists for target");
        bytes[0] ^= 0x01;
        target.certificate_file_hash = package_file_hash(bytes);
        let target_module = target.module.clone();
        let corrupt_certificate_file_hash = target.certificate_file_hash;
        let mut corrupt_manifest = proof_manifest();
        corrupt_manifest
            .modules
            .iter_mut()
            .find(|module| module.module == target_module)
            .expect("proof manifest contains corrupt target")
            .expected_certificate_file_hash = corrupt_certificate_file_hash;
        let corrupt_validated = validate_manifest(corrupt_manifest).unwrap();

        clear_package_verification_decode_cache();
        let uncached = verify_package_fast_source_free_with_options(
            &corrupt_validated,
            &corrupt_lock,
            package_certificate_artifacts(&corrupt_artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let _rewarm = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let cached = verify_package_fast_source_free_with_options(
            &corrupt_validated,
            &corrupt_lock,
            package_certificate_artifacts(&corrupt_artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(uncached.status, PackageVerificationStatus::Failed);
        assert_eq!(cached.status, PackageVerificationStatus::Failed);
        assert_eq!(
            without_decode_cache_counters(cached),
            without_decode_cache_counters(uncached)
        );
    }

    #[test]
    fn package_verifier_decode_cache_import_identity_change_misses_context() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let artifact_bytes = artifact_byte_map(package_certificate_artifacts(&artifacts)).unwrap();
        let entries = canonical_lock_entries(&lock);
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let target_module = Name::from_dotted("Proofs.Ai.Algebra.AbstractGroup");
        let (target_index, target_entry) = entries_by_module
            .get(&target_module)
            .expect("proof fixture contains AbstractGroup");
        let owner_header = decode_module_cert_header(
            artifact_bytes
                .get(&target_entry.certificate)
                .copied()
                .unwrap(),
        )
        .unwrap();
        let policy = package_reference_checker_policy(&validated);
        let config = PackageVerificationDecodeCacheConfig::for_mode(
            &validated,
            PackageVerificationMode::Reference,
        )
        .with_process_local_cache(true);
        let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();

        for module in graph
            .topological_order
            .iter()
            .take_while(|module| *module != &target_module)
        {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("graph order only contains lock entries");
            let (checked, _counters) = verify_reference_lock_entry(
                *entry_index,
                entry,
                &graph.resolved_entry_imports[*entry_index],
                PackageReferenceEntryContext {
                    lock: &lock,
                    entries: &entries,
                    artifact_bytes: &artifact_bytes,
                    artifact_file_hashes: None,
                    checked_by_module: &checked_by_module,
                    policy: &policy,
                    decode_cache_config: &config,
                },
            )
            .unwrap();
            checked_by_module.insert(entry.module.clone(), checked);
        }

        let direct_imports = &graph.resolved_entry_imports[*target_index];
        assert!(direct_imports.len() >= 2);
        let mut first_counters = PackageVerificationDecodeCacheCounters::default();
        let mut first_payload = PackagePayloadOwnershipObservation::default();
        let first_value = reference_import_store_with_cache_observed(
            *target_index,
            target_entry,
            direct_imports,
            PackageReferenceImportContext {
                lock: &lock,
                entries: &entries,
                checked_by_module: &checked_by_module,
                owner_header: &owner_header,
                config: &config,
            },
            &mut first_counters,
            Some(&mut first_payload),
        )
        .unwrap();
        let first = PackageDecodeCacheLookup {
            value: first_value,
            counters: first_counters,
        };
        let mut second_counters = PackageVerificationDecodeCacheCounters::default();
        let mut second_payload = PackagePayloadOwnershipObservation::default();
        let second_value = reference_import_store_with_cache_observed(
            *target_index,
            target_entry,
            direct_imports,
            PackageReferenceImportContext {
                lock: &lock,
                entries: &entries,
                checked_by_module: &checked_by_module,
                owner_header: &owner_header,
                config: &config,
            },
            &mut second_counters,
            Some(&mut second_payload),
        )
        .unwrap();
        let second = PackageDecodeCacheLookup {
            value: second_value,
            counters: second_counters,
        };
        assert!(first_payload.decode_cache_retained_bytes > 0);
        assert!(second_payload.decode_cache_retained_bytes > 0);
        let unverified_hit = match reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &BTreeMap::new(),
            &owner_header,
            &config,
        ) {
            Ok(_) => panic!("cached import context hit must require verified imports in this run"),
            Err(error) => error,
        };
        let mut reordered_imports = direct_imports.to_vec();
        reordered_imports.swap(0, 1);
        assert_ne!(
            package_decode_cache_import_context_key(direct_imports, &checked_by_module, &config)
                .unwrap(),
            package_decode_cache_import_context_key(
                &reordered_imports,
                &checked_by_module,
                &config,
            )
            .unwrap(),
            "direct-import order is part of the cache identity",
        );
        let changed = reference_import_store_with_cache(
            *target_index,
            target_entry,
            &reordered_imports,
            &lock,
            &entries,
            &checked_by_module,
            &owner_header,
            &config,
        )
        .unwrap();

        assert_eq!(
            first.counters.import_context_hits + first.counters.import_context_misses,
            1
        );
        assert_eq!(
            first.counters.import_context_inserted + first.counters.import_context_capacity_stops,
            first.counters.import_context_misses
        );
        if first.counters.import_context_inserted == 1 {
            assert_eq!(second.counters.import_context_hits, 1);
        } else {
            assert_eq!(second.counters.import_context_misses, 1);
            assert_eq!(second.counters.import_context_capacity_stops, 1);
        }
        assert_eq!(
            unverified_hit.reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
        assert_eq!(changed.counters.import_context_misses, 1);
    }

    #[test]
    fn package_import_context_export_cache_reuses_disk_entry_without_changing_report() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        clear_package_import_context_export_disk_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let artifact_bytes = artifact_byte_map(package_certificate_artifacts(&artifacts)).unwrap();
        let entries = canonical_lock_entries(&lock);
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let target_module = Name::from_dotted("Proofs.Ai.Algebra.AbstractGroup");
        let (target_index, target_entry) = entries_by_module
            .get(&target_module)
            .expect("proof fixture contains AbstractGroup");
        let owner_header = decode_module_cert_header(
            artifact_bytes
                .get(&target_entry.certificate)
                .copied()
                .unwrap(),
        )
        .unwrap();
        let policy = package_reference_checker_policy(&validated);
        let mut config = PackageVerificationDecodeCacheConfig::for_mode(
            &validated,
            PackageVerificationMode::Reference,
        )
        .with_persistent_import_context_export_cache(true);
        config.checker_policy_hash = unique_import_context_cache_policy_hash(0xd1);
        let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();

        for module in graph
            .topological_order
            .iter()
            .take_while(|module| *module != &target_module)
        {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("graph order only contains lock entries");
            let (checked, _counters) = verify_reference_lock_entry(
                *entry_index,
                entry,
                &graph.resolved_entry_imports[*entry_index],
                PackageReferenceEntryContext {
                    lock: &lock,
                    entries: &entries,
                    artifact_bytes: &artifact_bytes,
                    artifact_file_hashes: None,
                    checked_by_module: &checked_by_module,
                    policy: &policy,
                    decode_cache_config: &config,
                },
            )
            .unwrap();
            checked_by_module.insert(module.clone(), checked);
        }
        let direct_imports = &graph.resolved_entry_imports[*target_index];

        clear_package_verification_decode_cache();
        let first = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &checked_by_module,
            &owner_header,
            &config,
        )
        .unwrap();
        assert_eq!(first.counters.import_context_disk_misses, 1);
        assert_eq!(first.counters.import_context_disk_inserted, 1);
        assert!(package_import_context_export_disk_cache_entry_count() > 0);

        clear_package_verification_decode_cache();
        let second = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &checked_by_module,
            &owner_header,
            &config,
        )
        .unwrap();

        assert_eq!(second.counters.import_context_disk_hits, 1);
        assert_eq!(second.counters.import_context_disk_misses, 0);
        assert_eq!(second.counters.import_context_disk_stale, 0);
        assert_eq!(second.counters.import_context_disk_schema_misses, 0);
        assert_eq!(second.counters.import_context_disk_inserted, 0);
        assert_eq!(second.value, first.value);

        let mut failed_counters = PackageVerificationDecodeCacheCounters::default();
        let owner_header = CertHeader {
            format: "NPA-CERT-0.2.0".to_owned(),
            core_spec: "NPA-Core-0.2.0".to_owned(),
            module: target_entry.module.clone(),
        };
        let failed = reference_import_store_with_cache_observed(
            *target_index,
            target_entry,
            direct_imports,
            PackageReferenceImportContext {
                lock: &lock,
                entries: &entries,
                checked_by_module: &BTreeMap::new(),
                owner_header: &owner_header,
                config: &config,
            },
            &mut failed_counters,
            None,
        )
        .expect_err("disk hit still requires verified imports in this run");
        assert_eq!(
            failed.reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
        assert_eq!(failed_counters.import_context_disk_hits, 0);
    }

    #[test]
    fn package_import_context_export_cache_uses_content_addressed_dependency_identity() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        clear_package_import_context_export_disk_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
        let artifact_bytes = artifact_byte_map(package_certificate_artifacts(&artifacts)).unwrap();
        let entries = canonical_lock_entries(&lock);
        let entries_by_module = entries
            .iter()
            .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
            .collect::<BTreeMap<_, _>>();
        let target_module = Name::from_dotted("Proofs.Ai.Algebra.AbstractGroup");
        let (target_index, target_entry) = entries_by_module
            .get(&target_module)
            .expect("proof fixture contains AbstractGroup");
        let owner_header = decode_module_cert_header(
            artifact_bytes
                .get(&target_entry.certificate)
                .copied()
                .unwrap(),
        )
        .unwrap();
        let policy = package_reference_checker_policy(&validated);
        let mut config = PackageVerificationDecodeCacheConfig::for_mode(
            &validated,
            PackageVerificationMode::Reference,
        )
        .with_persistent_import_context_export_cache(true);
        config.checker_policy_hash = unique_import_context_cache_policy_hash(0xd2);
        let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();

        for module in graph
            .topological_order
            .iter()
            .take_while(|module| *module != &target_module)
        {
            let (entry_index, entry) = entries_by_module
                .get(module)
                .expect("graph order only contains lock entries");
            let (checked, _counters) = verify_reference_lock_entry(
                *entry_index,
                entry,
                &graph.resolved_entry_imports[*entry_index],
                PackageReferenceEntryContext {
                    lock: &lock,
                    entries: &entries,
                    artifact_bytes: &artifact_bytes,
                    artifact_file_hashes: None,
                    checked_by_module: &checked_by_module,
                    policy: &policy,
                    decode_cache_config: &config,
                },
            )
            .unwrap();
            checked_by_module.insert(entry.module.clone(), checked);
        }

        let direct_imports = &graph.resolved_entry_imports[*target_index];
        let first = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &checked_by_module,
            &owner_header,
            &config,
        )
        .unwrap();
        assert_eq!(first.counters.import_context_disk_misses, 1);
        assert_eq!(first.counters.import_context_disk_inserted, 1);

        clear_package_verification_decode_cache();
        let mut changed_lock = lock.clone();
        let dependency_module = direct_imports[0].module.clone();
        changed_lock
            .entries
            .iter_mut()
            .find(|entry| entry.module == dependency_module)
            .expect("dependency module exists in changed lock")
            .axiom_report_hash = PackageHash::new(test_hash(0xee));
        let changed_entries = canonical_lock_entries(&changed_lock);
        let stale = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &changed_entries,
            &checked_by_module,
            &owner_header,
            &config,
        )
        .unwrap();

        assert_eq!(stale.counters.import_context_disk_hits, 0);
        assert_eq!(stale.counters.import_context_disk_misses, 1);
        assert_eq!(stale.counters.import_context_disk_stale, 0);
        assert_eq!(stale.counters.import_context_disk_inserted, 1);
        assert!(package_import_context_export_disk_cache_entry_count() >= 2);
    }

    #[test]
    fn package_verifier_decode_cache_hit_cannot_turn_verifier_failure_into_success() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted(
            "Proofs.Ai.Algebra.AbstractGroup",
        )]));

        let warm = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected.clone(),
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(warm.status, PackageVerificationStatus::Passed);

        let mut manifest = proof_manifest();
        manifest.policy.allowed_axioms.clear();
        for module in &mut manifest.modules {
            module.axioms = Some(Vec::new());
        }
        let restrictive = validate_manifest(manifest).unwrap();
        let failed = verify_package_fast_source_free_with_options(
            &restrictive,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
                decode_cache: PackageVerificationDecodeCacheMode::ProcessLocal,
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(failed.status, PackageVerificationStatus::Failed);
        let failed_module = failed
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("restrictive policy rejects one live-checked module");
        assert_eq!(
            failed_module.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::AxiomPolicyRejected
        );
        assert_eq!(
            failed_module.evidence,
            PackageModuleVerificationEvidence::LiveChecker
        );
    }

    #[test]
    fn package_verifier_parallel_skips_dependents_after_failed_dependency() {
        run_on_large_stack(
            "package_verifier_parallel_skips_dependents_after_failed_dependency",
            package_verifier_parallel_skips_dependents_after_failed_dependency_on_large_stack,
        );
    }

    fn package_verifier_parallel_skips_dependents_after_failed_dependency_on_large_stack() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let mut artifacts = proof_certificate_artifacts(&lock);
        let stale_path = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == "Std.Logic.Eq")
            .expect("proof lock contains Std.Logic.Eq")
            .certificate
            .clone();
        artifacts.get_mut(&stale_path).unwrap()[0] ^= 0x01;

        let report = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")])),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            report
                .modules
                .iter()
                .map(|module| (module.module.as_dotted(), module.status))
                .collect::<Vec<_>>(),
            vec![
                (
                    "Std.Logic.Eq".to_owned(),
                    PackageModuleVerificationStatus::Failed
                ),
                (
                    "Std.Nat.Basic".to_owned(),
                    PackageModuleVerificationStatus::Passed
                ),
                (
                    "Proofs.Ai.Eq".to_owned(),
                    PackageModuleVerificationStatus::Skipped
                ),
            ]
        );
        let skipped = report
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Proofs.Ai.Eq")
            .unwrap();
        assert_eq!(
            skipped.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
    }

    #[test]
    fn package_verifier_parallel_reference_mode_is_explicitly_rejected() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);

        let error = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: None,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap_err();

        assert_eq!(error.kind, PackageVerificationErrorKind::Input);
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::UnsupportedParallelChecker
        );
    }

    #[test]
    fn package_fast_verifier_rejects_missing_lock_imports_before_kernel_run() {
        let validated = validated_proof_manifest();
        let mut lock = proof_lock();
        lock.entries
            .retain(|entry| entry.module.as_dotted() != "Std.Logic.Eq");

        let error = verify_package_fast_source_free(
            &validated,
            &lock,
            Vec::<PackageCertificateArtifact<'_>>::new(),
        )
        .expect_err("lock graph is invalid");

        assert_eq!(error.kind, PackageVerificationErrorKind::LockGraph);
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
    }

    #[test]
    fn package_source_free_invalid_graph_fails_before_artifact_or_checker_lookup() {
        let validated = validated_proof_manifest();
        let mut lock = proof_lock();
        lock.entries
            .retain(|entry| entry.module.as_dotted() != "Std.Logic.Eq");

        let fast = verify_package_fast_source_free(
            &validated,
            &lock,
            Vec::<PackageCertificateArtifact<'_>>::new(),
        )
        .expect_err("invalid lock graph fails before fast verifier artifact lookup");
        let reference = verify_package_reference_source_free(
            &validated,
            &lock,
            Vec::<PackageCertificateArtifact<'_>>::new(),
        )
        .expect_err("invalid lock graph fails before reference checker artifact lookup");

        for error in [fast, reference] {
            assert_eq!(error.kind, PackageVerificationErrorKind::LockGraph);
            assert_eq!(
                error.reason_code,
                PackageVerificationErrorReason::LockGraphInvalid
            );
        }
    }

    #[test]
    fn package_reference_verifier_verifies_proof_package_source_free_in_topological_order() {
        run_on_large_stack(
            "package_reference_verifier_verifies_proof_package_source_free_in_topological_order",
            package_reference_verifier_verifies_proof_package_source_free_in_topological_order_on_large_stack,
        );
    }

    fn package_reference_verifier_verifies_proof_package_source_free_in_topological_order_on_large_stack(
    ) {
        let mut manifest = proof_manifest();
        for module in &mut manifest.modules {
            let module_path = module.module.as_dotted().replace('.', "/");
            module.source = PackagePath::new(format!("missing/source/{module_path}.npa"));
            module.meta = Some(PackagePath::new(format!("missing/meta/{module_path}.json")));
            module.replay = Some(PackagePath::new(format!(
                "missing/replay/{module_path}.json"
            )));
        }
        let validated = validate_manifest(manifest).unwrap();
        let mut lock = proof_lock();
        lock.entries.reverse();
        let artifacts = proof_certificate_artifacts(&lock);

        let report = verify_proof_package_reference(&validated, &lock, &artifacts).unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert_eq!(report.mode, PackageVerificationMode::Reference);
        assert_eq!(
            report.verdict_source,
            PackageVerificationVerdictSource::ReferenceChecker
        );
        assert!(report.reference_checker_verdict);
        assert_eq!(report.modules.len(), lock.entries.len());
        assert!(report.modules.iter().all(|module| {
            module.checker_mode == PackageVerificationMode::Reference
                && module.status == PackageModuleVerificationStatus::Passed
                && module.certificate_format.as_deref() == Some("NPA-CERT-0.4.0")
                && module.core_spec.as_deref() == Some("NPA-Core-0.4.0")
        }));
        let order = report
            .topological_order
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>();
        let std_eq = order
            .iter()
            .position(|module| module == "Std.Logic.Eq")
            .unwrap();
        let local_eq = order
            .iter()
            .position(|module| module == "Proofs.Ai.Eq")
            .unwrap();
        assert!(std_eq < local_eq);
        assert_eq!(
            report
                .modules
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            order
        );
    }

    #[test]
    fn package_reference_dag_rejects_semantically_unchecked_provider_before_leaf() {
        let good_provider = build_module_cert(unchecked_import_provider(), &[]).unwrap();
        let good_provider_bytes = encode_module_cert(&good_provider).unwrap();
        let mut session = VerifierSession::new();
        let verified_provider = npa_cert::verify_module_cert(
            &good_provider_bytes,
            &mut session,
            &AxiomPolicy::normal(),
        )
        .unwrap();

        let bad_provider = semantically_invalid_unchecked_import_provider(good_provider.clone());
        let bad_provider_bytes = encode_module_cert(&bad_provider).unwrap();
        let leaf = build_module_cert(unchecked_import_consumer(), &[verified_provider]).unwrap();
        let mut parts = leaf.into_parts();
        parts.imports[0].certificate_hash = Some(bad_provider.hashes().certificate_hash);
        let leaf = recompute_unchecked_import_module_hash(ModuleCert::from_parts(parts));
        let leaf_bytes = encode_module_cert(&leaf).unwrap();

        assert_eq!(
            good_provider.hashes().export_hash,
            bad_provider.hashes().export_hash
        );
        let unchecked_imports =
            ReferenceImportStore::from_source_free_certificates([bad_provider_bytes.as_slice()])
                .unwrap();
        assert!(matches!(
            check_certificate(
                &leaf_bytes,
                &unchecked_imports,
                &ReferenceCheckerPolicy::default(),
            ),
            ReferenceCheckResult::Checked(_)
        ));

        let provider_path = PackagePath::new("Boundary/Provider/certificate.npcert");
        let leaf_path = PackagePath::new("Boundary/Consumer/certificate.npcert");
        let manifest = PackageManifest {
            schema: PACKAGE_MANIFEST_SCHEMA.to_owned(),
            package: PackageId::new("unchecked-import-boundary"),
            version: PackageVersion::new("0.1.0"),
            core_spec: CORE_SPEC_V0_1.to_owned(),
            kernel_profile: KERNEL_PROFILE_V0_1.to_owned(),
            certificate_format: CERTIFICATE_FORMAT_CANONICAL_V0_1.to_owned(),
            checker_profile: CHECKER_PROFILE_REFERENCE_V0_1.to_owned(),
            policy: PackagePolicy {
                allow_custom_axioms: false,
                allowed_axioms: Vec::new(),
            },
            modules: vec![
                unchecked_import_package_module(
                    "Boundary.Provider",
                    "Boundary/Provider/source.npa",
                    provider_path.as_str(),
                    Vec::new(),
                    &bad_provider,
                    &bad_provider_bytes,
                ),
                unchecked_import_package_module(
                    "Boundary.Consumer",
                    "Boundary/Consumer/source.npa",
                    leaf_path.as_str(),
                    vec![Name::from_dotted("Boundary.Provider")],
                    &leaf,
                    &leaf_bytes,
                ),
            ],
            license: None,
            repository: None,
            description: None,
            imports: None,
        };
        let validated = validate_manifest(manifest).unwrap();
        assert_eq!(
            package_reference_checker_policy(&validated).trust_mode,
            ReferenceTrustMode::HighTrust
        );
        let lock = build_package_lock_from_artifacts(
            &validated,
            PackagePath::new("npa-package.toml"),
            b"unchecked import boundary fixture",
            [
                PackageLockArtifact {
                    path: provider_path.clone(),
                    bytes: &bad_provider_bytes,
                },
                PackageLockArtifact {
                    path: leaf_path.clone(),
                    bytes: &leaf_bytes,
                },
            ],
        )
        .unwrap();
        let artifacts =
            BTreeMap::from([(provider_path, bad_provider_bytes), (leaf_path, leaf_bytes)]);

        let report = verify_package_reference_source_free(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
        )
        .unwrap();

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        let provider_result = report
            .modules
            .iter()
            .find(|result| result.module.as_dotted() == "Boundary.Provider")
            .unwrap();
        assert_eq!(
            provider_result.status,
            PackageModuleVerificationStatus::Failed
        );
        let provider_error = provider_result.error.as_ref().unwrap();
        assert_eq!(
            provider_error.reason_code,
            PackageVerificationErrorReason::ReferenceCheckerRejected
        );
        let checker_error = provider_error.checker_error.as_ref().unwrap();
        assert_eq!(checker_error.kind, "type_check");
        assert_eq!(checker_error.reason_code.as_deref(), Some("type_mismatch"));

        let leaf_result = report
            .modules
            .iter()
            .find(|result| result.module.as_dotted() == "Boundary.Consumer")
            .unwrap();
        assert_eq!(leaf_result.status, PackageModuleVerificationStatus::Skipped);
        assert_eq!(
            leaf_result.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
    }

    #[test]
    fn package_lock_rejects_retired_universe_fixture_before_dag_verification() {
        let provider_bytes = read(repo_root().join(
            "testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert",
        ));
        let provider_module = Name::from_dotted("Audit.Universe");
        let provider_export_hash = test_hash(0x91);
        let provider_certificate_hash = test_hash(0x92);
        let leaf = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Audit.Leaf"),
                declarations: Vec::new(),
            },
            &[],
        )
        .unwrap();
        let mut parts = leaf.into_parts();
        parts.imports.push(npa_cert::ImportEntry {
            module: provider_module.clone(),
            export_hash: provider_export_hash,
            certificate_hash: Some(provider_certificate_hash),
        });
        let leaf = recompute_unchecked_import_module_hash(ModuleCert::from_parts(parts));
        let leaf_bytes = encode_module_cert(&leaf).unwrap();

        let provider_path = PackagePath::new("Audit/Universe/certificate.npcert");
        let leaf_path = PackagePath::new("Audit/Leaf/certificate.npcert");
        let manifest = PackageManifest {
            schema: PACKAGE_MANIFEST_SCHEMA.to_owned(),
            package: PackageId::new("inductive-universe-bound"),
            version: PackageVersion::new("0.1.0"),
            core_spec: CORE_SPEC_V0_1.to_owned(),
            kernel_profile: KERNEL_PROFILE_V0_1.to_owned(),
            certificate_format: CERTIFICATE_FORMAT_CANONICAL_V0_1.to_owned(),
            checker_profile: CHECKER_PROFILE_REFERENCE_V0_1.to_owned(),
            policy: PackagePolicy {
                allow_custom_axioms: false,
                allowed_axioms: Vec::new(),
            },
            modules: vec![
                PackageModule {
                    module: provider_module,
                    source: PackagePath::new("Audit/Universe/source.npa"),
                    certificate: provider_path.clone(),
                    imports: Vec::new(),
                    expected_source_hash: PackageHash::new([0; 32]),
                    expected_certificate_file_hash: package_file_hash(&provider_bytes),
                    expected_export_hash: PackageHash::new(provider_export_hash),
                    expected_axiom_report_hash: PackageHash::new([0; 32]),
                    expected_certificate_hash: PackageHash::new(provider_certificate_hash),
                    meta: None,
                    replay: None,
                    producer_profile: None,
                    inductives: None,
                    definitions: None,
                    theorems: None,
                    axioms: None,
                    tags: None,
                },
                unchecked_import_package_module(
                    "Audit.Leaf",
                    "Audit/Leaf/source.npa",
                    leaf_path.as_str(),
                    vec![Name::from_dotted("Audit.Universe")],
                    &leaf,
                    &leaf_bytes,
                ),
            ],
            license: None,
            repository: None,
            description: None,
            imports: None,
        };
        let validated = validate_manifest(manifest).unwrap();
        let error = build_package_lock_from_artifacts(
            &validated,
            PackagePath::new("npa-package.toml"),
            b"inductive universe bound fixture",
            [
                PackageLockArtifact {
                    path: provider_path.clone(),
                    bytes: &provider_bytes,
                },
                PackageLockArtifact {
                    path: leaf_path.clone(),
                    bytes: &leaf_bytes,
                },
            ],
        )
        .expect_err("retired certificate format must fail before DAG verification");

        assert_eq!(error.kind, PackageLockErrorKind::CertificateDecode);
        assert_eq!(
            error.reason_code,
            PackageLockErrorReason::CertificateDecodeFailed
        );
        assert_eq!(error.path, "modules[0].certificate");
        assert!(error
            .actual_value
            .as_deref()
            .is_some_and(|value| value.contains("NPA-CERT-0.1")));
    }

    #[test]
    fn package_reference_verifier_rejects_disallowed_axioms_from_certificate() {
        let mut manifest = proof_manifest();
        manifest.policy.allowed_axioms.clear();
        for module in &mut manifest.modules {
            module.axioms = Some(Vec::new());
        }
        let validated = validate_manifest(manifest).unwrap();
        let lock = proof_lock();

        let report = verify_package_reference_source_free_from_root_with_options(
            &validated,
            &lock,
            proofs_root(),
            selected_module_options("Proofs.Ai.Algebra.AbstractGroup"),
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("one module fails");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(
            failed.error.as_ref().unwrap().kind,
            PackageVerificationErrorKind::ReferenceChecker
        );
        assert_eq!(
            failed.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::AxiomPolicyRejected
        );
        assert_eq!(
            failed
                .error
                .as_ref()
                .unwrap()
                .checker_error
                .as_ref()
                .unwrap()
                .checker,
            "npa-checker-ref"
        );
    }

    #[test]
    fn package_source_free_reference_checker_failure_preserves_structured_payload() {
        let mut manifest = proof_manifest();
        manifest.policy.allowed_axioms.clear();
        for module in &mut manifest.modules {
            module.axioms = Some(Vec::new());
        }
        let validated = validate_manifest(manifest).unwrap();
        let lock = proof_lock();

        let report = verify_package_reference_source_free_from_root_with_options(
            &validated,
            &lock,
            proofs_root(),
            selected_module_options("Proofs.Ai.Algebra.AbstractGroup"),
        )
        .unwrap();
        let failed = report
            .modules
            .iter()
            .find(|module| module.status == PackageModuleVerificationStatus::Failed)
            .expect("reference checker rejects one module");
        let error = failed.error.as_ref().unwrap();
        let checker_error = error
            .checker_error
            .as_ref()
            .expect("reference checker failure carries checker payload");

        assert_eq!(report.status, PackageVerificationStatus::Failed);
        assert_eq!(error.kind, PackageVerificationErrorKind::ReferenceChecker);
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::AxiomPolicyRejected
        );
        assert_eq!(checker_error.checker, "npa-checker-ref");
        assert_eq!(checker_error.kind, "axiom_policy");
        assert_eq!(
            checker_error.reason_code.as_deref(),
            Some("forbidden_axiom")
        );
    }

    #[test]
    fn package_reference_verifier_rejects_missing_lock_imports_before_checker_run() {
        let validated = validated_proof_manifest();
        let mut lock = proof_lock();
        lock.entries
            .retain(|entry| entry.module.as_dotted() != "Std.Logic.Eq");

        let error = verify_package_reference_source_free(
            &validated,
            &lock,
            Vec::<PackageCertificateArtifact<'_>>::new(),
        )
        .expect_err("lock graph is invalid");

        assert_eq!(error.kind, PackageVerificationErrorKind::LockGraph);
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
    }

    #[test]
    fn package_phase8_import_lock_adapter_materializes_direct_imports_only() {
        let lock = proof_lock();
        let materialized = materialize_package_phase8_import_locks(&lock, "reference").unwrap();
        let canonical_entries = canonical_lock_entries(&lock);
        let entries_by_module = canonical_entries
            .iter()
            .map(|(_, entry)| (entry.module.clone(), *entry))
            .collect::<BTreeMap<_, _>>();

        assert_eq!(materialized.len(), lock.entries.len());
        for artifact in &materialized {
            let entry = entries_by_module.get(&artifact.module).unwrap();
            let parsed =
                parse_independent_checker_import_lock_manifest(&artifact.manifest.canonical_json())
                    .unwrap();
            assert_eq!(parsed, artifact.manifest);
            assert_eq!(
                artifact.manifest_hash,
                independent_checker_file_hash(artifact.manifest.canonical_json().as_bytes())
            );
            assert_eq!(
                artifact.path,
                format!(
                    "generated/checker-requests/{}/{}/{}/reference/imports.json",
                    lock.package.as_str(),
                    lock.version.as_str(),
                    artifact.module.as_dotted()
                )
            );
            assert_eq!(artifact.manifest.imports.len(), entry.imports.len());
            assert_eq!(
                artifact
                    .manifest
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect::<BTreeSet<_>>(),
                entry
                    .imports
                    .iter()
                    .map(|import| import.module.as_dotted())
                    .collect::<BTreeSet<_>>()
            );
            for import in &artifact.manifest.imports {
                let lock_import = entry
                    .imports
                    .iter()
                    .find(|candidate| candidate.module.as_dotted() == import.module)
                    .unwrap();
                let import_entry = entries_by_module.get(&lock_import.module).unwrap();
                assert_eq!(import.export_hash, lock_import.export_hash.into_bytes());
                assert_eq!(import.certificate.path, import_entry.certificate.as_str());
                assert_eq!(
                    import.certificate.file_hash,
                    import_entry.certificate_file_hash.into_bytes()
                );
                assert_eq!(
                    import.certificate.certificate_hash,
                    lock_import.certificate_hash.into_bytes()
                );
            }

            let json = artifact.manifest.canonical_json();
            for forbidden in [
                "source",
                "replay",
                "meta",
                "theorem_index",
                "ai_trace",
                "registry",
                "solver",
            ] {
                assert!(!json.contains(forbidden), "import lock leaked {forbidden}");
            }
        }
    }

    #[test]
    fn package_phase8_request_materialization_builds_valid_requests_and_hashes() {
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let policy = phase8_reference_runner_policy();

        let report = materialize_package_phase8_requests(
            &lock,
            package_certificate_artifacts(&artifacts),
            &policy,
            "reference",
            None,
        )
        .unwrap();

        let canonical_entries = canonical_lock_entries(&lock);
        let entries_by_module = canonical_entries
            .iter()
            .map(|(_, entry)| (entry.module.clone(), *entry))
            .collect::<BTreeMap<_, _>>();

        assert_eq!(report.modules.len(), lock.entries.len());
        assert_eq!(report.request_store.requests.len(), lock.entries.len());
        assert_eq!(
            parse_independent_checker_request_store_manifest(
                &report.request_store.canonical_json()
            )
            .unwrap(),
            report.request_store
        );
        assert_eq!(
            report.request_store_file_hash,
            independent_checker_file_hash(report.request_store.canonical_json().as_bytes())
        );
        assert!(report.request_store_rewrite_required);

        let second = materialize_package_phase8_requests(
            &lock,
            package_certificate_artifacts(&artifacts),
            &policy,
            "reference",
            Some(&report.request_store),
        )
        .unwrap();
        assert!(!second.request_store_rewrite_required);
        assert_eq!(second.request_store, report.request_store);

        for module in &report.modules {
            let entry = entries_by_module.get(&module.module).unwrap();
            let cert_bytes = artifacts.get(&entry.certificate).unwrap();
            let request_json = module.request.canonical_json();

            assert_eq!(
                parse_independent_checker_machine_check_request(&request_json).unwrap(),
                module.request
            );
            assert_eq!(
                independent_checker_machine_check_request_hash(&request_json).unwrap(),
                module.request.request_hash()
            );
            assert_eq!(
                module.request_file_hash,
                independent_checker_file_hash(request_json.as_bytes())
            );
            assert_eq!(
                module.request.request_id,
                format!(
                    "package:{}:{}:{}:reference",
                    lock.package.as_str(),
                    lock.version.as_str(),
                    module.module.as_dotted()
                )
            );
            assert_eq!(
                module.request_path,
                format!(
                    "generated/checker-requests/{}/{}/{}/reference/request.json",
                    lock.package.as_str(),
                    lock.version.as_str(),
                    module.module.as_dotted()
                )
            );
            assert_eq!(module.request.module, module.module.as_dotted());
            assert_eq!(module.request.checker_profile, "reference");
            assert_eq!(module.request.certificate.path, entry.certificate.as_str());
            assert_eq!(
                module.request.certificate.file_hash,
                independent_checker_file_hash(cert_bytes)
            );
            assert_eq!(
                module.request.certificate.expected_certificate_hash,
                entry.certificate_hash.into_bytes()
            );
            assert_eq!(module.request.imports.manifest, module.import_lock_path);
            assert_eq!(
                module.request.imports.manifest_hash,
                module.import_lock_manifest_hash
            );
            assert_eq!(
                parse_independent_checker_import_lock_manifest(
                    &module.import_lock_manifest.canonical_json()
                )
                .unwrap(),
                module.import_lock_manifest
            );

            for forbidden in [
                "source",
                "replay",
                "meta",
                "theorem_index",
                "ai_trace",
                "registry",
                "solver",
            ] {
                assert!(
                    !request_json.contains(forbidden),
                    "request leaked {forbidden}"
                );
            }
        }
    }

    #[test]
    fn package_payload_clone_oracle() {
        let certificate = decode_cache_test_certificate();
        let clone = certificate.clone();
        assert_eq!(clone, certificate);
        assert_eq!(
            clone.logical_retained_bytes_v1(),
            certificate.logical_retained_bytes_v1()
        );

        let handle = test_process_memo_handle();
        handle
            .insert(
                "clone-oracle".to_owned(),
                test_failed_memo_value("Clone"),
                1,
            )
            .unwrap();
        let first = handle.lookup("clone-oracle").unwrap().unwrap();
        let second = handle.lookup("clone-oracle").unwrap().unwrap();
        assert!(Arc::ptr_eq(&first, &second));
    }

    #[test]
    fn shared_payload_package_oracle() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = proof_certificate_artifacts(&lock);
        let fast = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                measurement_mode: PerformanceMeasurementMode::Summary,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let reference = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                measurement_mode: PerformanceMeasurementMode::Summary,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(fast.status, PackageVerificationStatus::Passed);
        assert_eq!(reference.status, PackageVerificationStatus::Passed);
        assert_eq!(fast.topological_order, reference.topological_order);
        assert_eq!(fast.modules.len(), reference.modules.len());
        assert!(fast.modules.iter().all(|module| {
            module.status == PackageModuleVerificationStatus::Passed
                && module.evidence == PackageModuleVerificationEvidence::LiveChecker
        }));
        assert!(reference.modules.iter().all(|module| {
            module.status == PackageModuleVerificationStatus::Passed
                && module.evidence == PackageModuleVerificationEvidence::LiveChecker
        }));
    }

    #[test]
    fn package_fast_shard() {
        package_verifier_shards_plan_is_deterministic_and_context_complete();
        package_verifier_shards_match_serial_and_legacy_parallel_success();
        let estimate = package_fast_shard_memory_estimate_v3(4, 4, 0, 0, 1, false);
        assert!((1..=4).contains(&estimate.effective_jobs));
        assert!(!estimate.overflowed);
        assert_eq!(
            estimate.reduction_reason == PackageFastShardReductionReason::None,
            estimate.effective_jobs == 4
        );
    }

    #[test]
    fn package_memo_single_arc_value() {
        let handle = test_process_memo_handle();
        handle
            .insert("one-arc".to_owned(), test_failed_memo_value("OneArc"), 1)
            .unwrap();
        let first = handle.lookup("one-arc").unwrap().unwrap();
        let second = handle.lookup("one-arc").unwrap().unwrap();
        assert!(Arc::ptr_eq(&first, &second));
        assert_eq!(handle.stats().unwrap().retained_entries, 1);
        package_verification_process_memo_arc_value_preserves_all_variants();
    }

    #[test]
    fn reference_import_store_with_cache_contract() {
        package_verifier_decode_cache_import_identity_change_misses_context();
        package_reference_cache_mutex_scope_releases_before_validation_work();
    }

    #[test]
    fn package_payload_ownership_observation_updates() {
        let mut observation = PackagePayloadOwnershipObservation::default();
        observation.observe_module_handle_clone(17);
        observation.observe_decode_cache_capacity_stop();
        observation.observe_process_memo_handle_clone();
        assert_eq!(observation.module_payload_handle_clones, 1);
        assert_eq!(observation.avoided_module_payload_clone_bytes, 17);
        assert_eq!(observation.decode_cache_capacity_stops, 1);
        assert_eq!(observation.process_memo_payload_handle_clones, 1);
        assert!(!observation.overflowed);

        observation.module_payload_handle_clones = u64::MAX;
        observation.observe_module_handle_clone(1);
        assert_eq!(observation.module_payload_handle_clones, u64::MAX);
        assert!(observation.overflowed);
    }

    #[test]
    fn package_payload_ownership_observation_merge() {
        let observations = [
            PackagePayloadOwnershipObservation {
                module_payload_handle_clones: 2,
                avoided_module_payload_clone_bytes: 3,
                decode_cache_retained_bytes: 11,
                decode_cache_peak_retained_bytes: 13,
                decode_cache_capacity_stops: 5,
                process_memo_payload_handle_clones: 7,
                overflowed: false,
            },
            PackagePayloadOwnershipObservation {
                module_payload_handle_clones: 17,
                avoided_module_payload_clone_bytes: 19,
                decode_cache_retained_bytes: 23,
                decode_cache_peak_retained_bytes: 29,
                decode_cache_capacity_stops: 31,
                process_memo_payload_handle_clones: 37,
                overflowed: true,
            },
        ];
        let merge = |order: [usize; 2]| {
            let mut aggregate = PackagePayloadOwnershipObservation::default();
            for index in order {
                aggregate.merge_worker(observations[index]);
            }
            aggregate
        };
        let aggregate = merge([0, 1]);
        assert_eq!(aggregate, merge([1, 0]));
        assert_eq!(aggregate.module_payload_handle_clones, 19);
        assert_eq!(aggregate.avoided_module_payload_clone_bytes, 22);
        assert_eq!(aggregate.decode_cache_retained_bytes, 0);
        assert_eq!(aggregate.decode_cache_peak_retained_bytes, 29);
        assert_eq!(aggregate.decode_cache_capacity_stops, 36);
        assert_eq!(aggregate.process_memo_payload_handle_clones, 44);
        assert!(aggregate.overflowed);
    }

    #[test]
    fn package_payload_observation_warm_cache() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        {
            let mut cache =
                lock_package_verification_decode_cache(package_verification_decode_cache());
            assert!(cache.insert_fast(
                "warm-observation".to_owned(),
                decode_cache_test_certificate()
            ));
        }
        let observation = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        let payload = observation.package_payload.unwrap();
        assert_eq!(
            payload.decode_cache_retained_bytes,
            package_verification_decode_cache_retained_bytes()
        );
        assert_eq!(
            payload.decode_cache_peak_retained_bytes,
            payload.decode_cache_retained_bytes
        );
        assert!(payload.decode_cache_retained_bytes > 0);
        clear_package_verification_decode_cache();
    }

    #[test]
    fn package_payload_observation_cache_samples() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let mut observation =
            PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        assert_eq!(
            observation
                .package_payload
                .as_ref()
                .unwrap()
                .decode_cache_retained_bytes,
            0
        );
        {
            let mut cache =
                lock_package_verification_decode_cache(package_verification_decode_cache());
            assert!(cache.insert_fast(
                "sample-observation".to_owned(),
                decode_cache_test_certificate()
            ));
        }
        observation.sample_decode_cache();
        observation.observe_decode_cache_capacity_stop();
        let payload = observation.package_payload.unwrap();
        assert_eq!(
            payload.decode_cache_retained_bytes,
            package_verification_decode_cache_retained_bytes()
        );
        assert_eq!(
            payload.decode_cache_peak_retained_bytes,
            payload.decode_cache_retained_bytes
        );
        assert_eq!(payload.decode_cache_capacity_stops, 1);
        clear_package_verification_decode_cache();
    }

    #[test]
    fn package_payload_observation_final_current() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        let mut measurements =
            PackageVerifierMeasurementState::new(PerformanceMeasurementMode::Summary).unwrap();
        {
            let mut cache =
                lock_package_verification_decode_cache(package_verification_decode_cache());
            assert!(cache.insert_fast(
                "final-observation".to_owned(),
                decode_cache_test_certificate()
            ));
        }
        measurements.sample_decode_cache();
        assert_eq!(
            measurements.package_payload.decode_cache_retained_bytes,
            package_verification_decode_cache_retained_bytes()
        );
        assert!(
            measurements
                .package_payload
                .decode_cache_peak_retained_bytes
                > 0
        );
        clear_package_verification_decode_cache();
    }

    #[test]
    fn package_payload_entry_observation() {
        let off = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Off);
        assert!(off.term_materialization.is_none());
        assert!(off.certificate_payload.is_none());
        assert!(off.package_payload.is_none());

        let enabled = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        assert!(enabled.term_materialization.is_some());
        assert!(enabled.certificate_payload.is_some());
        assert!(enabled.package_payload.is_some());
    }

    #[test]
    fn package_payload_observation_worker_transport() {
        let observation = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        assert!(observation.package_payload.is_some());
        package_worker_returns_term_observation();
        package_verifier_shards_match_serial_and_legacy_parallel_success();
    }

    #[test]
    fn package_payload_observation_worker_seed() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_decode_cache();
        {
            let mut cache =
                lock_package_verification_decode_cache(package_verification_decode_cache());
            assert!(cache.insert_fast("worker-seed".to_owned(), decode_cache_test_certificate()));
        }
        let observation = PackageEntryCheckObservation::new(PerformanceMeasurementMode::Summary);
        let payload = observation.package_payload.unwrap();
        assert_eq!(
            payload.decode_cache_retained_bytes,
            payload.decode_cache_peak_retained_bytes
        );
        assert!(payload.decode_cache_retained_bytes > 0);
        clear_package_verification_decode_cache();
    }

    #[test]
    fn package_payload_observation_sharded_merge() {
        package_payload_ownership_observation_merge();
        package_term_observation_worker_permutations();
    }

    #[test]
    fn package_payload_observation_post_join_current() {
        package_payload_observation_final_current();
        package_payload_ownership_observation_merge();
    }

    #[test]
    fn package_reference_memo_post_lock_clone() {
        package_memo_mutex_scope_releases_before_projection_and_live_check();
        package_verifier_memo_reference_explicit_handle_reuses_second_run();
        let mut observation = PackagePayloadOwnershipObservation::default();
        observation.observe_process_memo_handle_clone();
        assert_eq!(observation.process_memo_payload_handle_clones, 1);
        assert_eq!(observation.module_payload_handle_clones, 0);
        assert_eq!(observation.avoided_module_payload_clone_bytes, 0);
    }

    #[test]
    fn shared_payload_package_differential() {
        shared_payload_package_oracle();
        package_verifier_memo_fast_matches_disabled_normalized_and_reuses_second_run();
        package_verifier_memo_reference_explicit_handle_reuses_second_run();
    }

    fn linear_dag_layer_names(
        indexed: &IndexedPackageLockGraph,
        layers: Vec<Vec<usize>>,
    ) -> Vec<Vec<Name>> {
        layers
            .into_iter()
            .map(|layer| {
                layer
                    .into_iter()
                    .map(|entry| indexed.entries()[entry].module.clone())
                    .collect()
            })
            .collect()
    }

    fn assert_linear_dag_bounded_selected_closure_contract() {
        let graph_count = 1u64 << (LINEAR_DAG_BOUNDED_MODULE_COUNT * 3 / 2);
        for reverse_names in [false, true] {
            for edge_mask in 0..graph_count {
                let lock = linear_dag_bounded_lock(edge_mask, reverse_names);
                let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
                let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
                for seed_mask in 0..(1u64 << LINEAR_DAG_BOUNDED_MODULE_COUNT) {
                    let seeds = indexed
                        .entries()
                        .iter()
                        .enumerate()
                        .filter(|(entry, _)| seed_mask & (1u64 << *entry) != 0)
                        .map(|(_, entry)| entry.module.clone())
                        .collect::<BTreeSet<_>>();
                    let options = PackageVerificationExecutionOptions {
                        selected_modules: Some(seeds.clone()),
                        ..PackageVerificationExecutionOptions::default()
                    };
                    let expected = legacy_execution_modules_fixed_point_oracle(
                        &entries,
                        indexed.graph(),
                        &options,
                    )
                    .unwrap();
                    assert_eq!(
                        execution_modules_for_options(&entries, indexed.graph(), &options).unwrap(),
                        expected
                    );
                    assert_eq!(
                        execution_modules_for_indexed(&indexed, &options).unwrap(),
                        expected
                    );

                    let mut counters = PackageGraphPlanningCounterSummary::default();
                    let selected = indexed
                        .index()
                        .dependency_closure_with_planning_counters(&seeds, &mut counters)
                        .unwrap();
                    let selected_entries = selected
                        .iter()
                        .enumerate()
                        .filter_map(|(entry, selected)| selected.then_some(entry))
                        .collect::<Vec<_>>();
                    let reached_edges = selected_entries
                        .iter()
                        .map(|entry| indexed.index().dependencies(*entry).unwrap().len())
                        .sum::<usize>();
                    assert_eq!(
                        counters.forward_vertex_dequeues,
                        u64::try_from(selected_entries.len()).unwrap()
                    );
                    assert_eq!(
                        counters.forward_edge_visits,
                        u64::try_from(reached_edges).unwrap()
                    );
                    assert!(!counters.overflowed);
                }
            }
        }

        let lock = linear_dag_bounded_lock(0, false);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let options = PackageVerificationExecutionOptions {
            selected_modules: Some(BTreeSet::from([
                Name::from_dotted("Missing.A"),
                Name::from_dotted("Missing.Z"),
            ])),
            ..PackageVerificationExecutionOptions::default()
        };
        let expected =
            legacy_execution_modules_fixed_point_oracle(&entries, indexed.graph(), &options)
                .unwrap_err();
        let actual =
            execution_modules_for_options(&entries, indexed.graph(), &options).unwrap_err();
        assert_eq!(actual, expected);
        assert_eq!(actual.actual_value.as_deref(), Some("Missing.A"));
    }

    fn assert_linear_dag_bounded_layer_contract() {
        let graph_count = 1u64 << (LINEAR_DAG_BOUNDED_MODULE_COUNT * 3 / 2);
        for reverse_names in [false, true] {
            for edge_mask in 0..graph_count {
                let lock = linear_dag_bounded_lock(edge_mask, reverse_names);
                let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
                let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
                for selected_mask in 0..(1u64 << LINEAR_DAG_BOUNDED_MODULE_COUNT) {
                    let selected = indexed
                        .entries()
                        .iter()
                        .enumerate()
                        .filter(|(entry, _)| selected_mask & (1u64 << *entry) != 0)
                        .map(|(_, entry)| entry.module.clone())
                        .collect::<BTreeSet<_>>();
                    let selected_bits = indexed
                        .entries()
                        .iter()
                        .map(|entry| selected.contains(&entry.module))
                        .collect::<Vec<_>>();
                    let mut counters = PackageGraphPlanningCounterSummary::default();
                    let actual = linear_dag_layer_names(
                        &indexed,
                        indexed.index().topological_layers_with_planning_counters(
                            &selected_bits,
                            &mut counters,
                        ),
                    );
                    let expected = legacy_execution_layers_ready_scan_oracle(
                        &entries,
                        indexed.graph(),
                        &selected,
                    );
                    assert_eq!(actual, expected);
                    assert_eq!(
                        execution_layers_for_modules(&entries, indexed.graph(), &selected),
                        expected
                    );
                    let visited_edges = selected_bits
                        .iter()
                        .enumerate()
                        .filter(|(_, selected)| **selected)
                        .map(|(entry, _)| indexed.index().dependencies(entry).unwrap().len())
                        .sum::<usize>();
                    assert_eq!(
                        counters.layer_assignments,
                        u64::try_from(selected.len()).unwrap()
                    );
                    assert_eq!(
                        counters.layer_dependency_edge_visits,
                        u64::try_from(visited_edges).unwrap()
                    );
                    assert!(!counters.overflowed);
                }
            }
        }

        let lock = linear_dag_bounded_lock(0, false);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let hash = PackageHash::new([0; 32]);
        let first = indexed.entries()[0].module.clone();
        let second = indexed.entries()[1].module.clone();
        let mut stalled_graph = indexed.graph().clone();
        stalled_graph.resolved_entry_imports[0] = vec![PackageLockResolvedImport {
            module: second.clone(),
            entry_index: 1,
            export_hash: hash,
            certificate_hash: hash,
        }];
        stalled_graph.resolved_entry_imports[1] = vec![PackageLockResolvedImport {
            module: first.clone(),
            entry_index: 0,
            export_hash: hash,
            certificate_hash: hash,
        }];
        assert!(legacy_execution_layers_ready_scan_oracle(
            &entries,
            &stalled_graph,
            &BTreeSet::from([first, second]),
        )
        .is_empty());
        assert!(legacy_execution_layers_ready_scan_oracle(
            &entries,
            &stalled_graph,
            &BTreeSet::new(),
        )
        .is_empty());
    }

    fn assert_linear_dag_local_live_contract() {
        let lock = proof_lock();
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let all_hits = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let dirty = indexed.entries()[*indexed.index().topological_entries().first().unwrap()]
            .module
            .clone();
        let mut counters = PackageGraphPlanningCounterSummary::default();
        let live = local_audit_cache_live_modules_with_sink(
            &indexed,
            all_hits.clone(),
            [dirty],
            &mut counters,
        )
        .unwrap();
        assert!(!live.is_empty());
        assert!(counters.reverse_vertex_dequeues <= indexed.entries().len() as u64);
        assert!(counters.forward_vertex_dequeues <= indexed.entries().len() as u64);

        let unknown_hit = local_audit_cache_live_modules(
            &indexed,
            [Name::from_dotted("Missing.CacheHit")],
            BTreeSet::new(),
        )
        .unwrap();
        assert_eq!(unknown_hit.len(), indexed.entries().len());
        let error = local_audit_cache_live_modules(
            &indexed,
            all_hits,
            [Name::from_dotted("Missing.Dirty")],
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::SelectedModuleMissing
        );
        assert_eq!(error.actual_value.as_deref(), Some("Missing.Dirty"));
    }

    fn assert_linear_dag_local_live_scale_contract() {
        let lock = linear_dag_benchmark_lock(PackageVerifierLinearDagBenchmarkShape::Chain4096);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let hits = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let mut counters = PackageGraphPlanningCounterSummary::default();
        let live = local_audit_cache_live_modules_with_sink(
            &indexed,
            hits,
            [linear_dag_benchmark_name(0)],
            &mut counters,
        )
        .unwrap();
        assert_eq!(live.len(), LINEAR_DAG_BENCHMARK_MODULE_COUNT);
        assert_eq!(counters.reverse_vertex_dequeues, 4_096);
        assert_eq!(counters.reverse_edge_visits, 4_095);
        assert_eq!(counters.forward_vertex_dequeues, 4_096);
        assert_eq!(counters.forward_edge_visits, 4_095);
        assert!(!counters.overflowed);
    }

    fn assert_linear_dag_shard_contract() {
        package_verifier_shards_plan_is_deterministic_and_context_complete();
        let estimate = package_fast_shard_memory_estimate_v3(4, 4, 11, 13, 17, false);
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention
                .as_str(),
            "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
        );
        assert_eq!(estimate.shared_base_context_bytes, 11);
        assert_eq!(estimate.prepared_shared_bytes, 13);
        assert_eq!(estimate.combined_shared_bytes, 24);
        assert!(estimate.per_worker_bytes > 17);

        let graph_count = 1u64 << (LINEAR_DAG_BOUNDED_MODULE_COUNT * 3 / 2);
        for reverse_names in [false, true] {
            for edge_mask in 0..graph_count {
                let lock = linear_dag_bounded_lock(edge_mask, reverse_names);
                let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
                let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
                let selected = indexed
                    .entries()
                    .iter()
                    .map(|entry| entry.module.clone())
                    .collect::<BTreeSet<_>>();
                let selected_bits = vec![true; indexed.entries().len()];
                let layers = linear_dag_layer_names(
                    &indexed,
                    indexed.index().topological_layers(&selected_bits),
                );
                let artifact_storage = indexed
                    .entries()
                    .iter()
                    .enumerate()
                    .map(|(entry, _)| vec![0u8; entry * 3])
                    .collect::<Vec<_>>();
                let artifacts = indexed
                    .entries()
                    .iter()
                    .zip(&artifact_storage)
                    .map(|(entry, bytes)| (entry.certificate.clone(), bytes.as_slice()))
                    .collect::<BTreeMap<_, _>>();
                let mut planning =
                    PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
                planning.prepared_shared_bytes = 13;
                let mut verified_entries = Vec::<usize>::new();
                for layer in layers {
                    let runnable = layer
                        .iter()
                        .map(|module| {
                            let entry = indexed.index().entry_by_module(module).unwrap();
                            (entry, &indexed.entries()[entry])
                        })
                        .collect::<Vec<_>>();
                    let context_modules = verified_entries
                        .iter()
                        .map(|entry| indexed.entries()[*entry].module.clone())
                        .collect::<BTreeSet<_>>();
                    for jobs in [1, 4] {
                        let actual = plan_fast_verifier_shards_with_state(
                            &runnable,
                            indexed.graph(),
                            &planning,
                            jobs,
                        );
                        let expected = legacy_plan_fast_verifier_shards_prefix_oracle(
                            &runnable,
                            indexed.graph(),
                            &context_modules,
                            verified_entries
                                .iter()
                                .map(|entry| &indexed.entries()[*entry].certificate),
                            &artifacts,
                            planning.prepared_shared_bytes,
                            jobs,
                        );
                        assert_eq!(actual, expected);
                    }
                    for (entry, _) in runnable {
                        planning.record_verified(entry).unwrap();
                        verified_entries.push(entry);
                    }
                }
                assert_eq!(verified_entries.len(), indexed.entries().len());
            }
        }

        let lock = linear_dag_bounded_lock(0, false);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let selected = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let artifacts = BTreeMap::<PackagePath, &[u8]>::new();
        let planning =
            PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
        let first = indexed.index().topological_entries()[0];
        let runnable = [(first, &indexed.entries()[first])];
        assert!(
            plan_fast_verifier_shards_with_state(&runnable, indexed.graph(), &planning, 4,)
                .is_none()
        );
        assert!(legacy_plan_fast_verifier_shards_prefix_oracle(
            &runnable,
            indexed.graph(),
            &BTreeSet::new(),
            std::iter::empty::<&PackagePath>(),
            &artifacts,
            0,
            4,
        )
        .is_none());
    }

    fn assert_linear_dag_critical_path_vector_contract() {
        let graph_count = 1u64 << (LINEAR_DAG_BOUNDED_MODULE_COUNT * 3 / 2);
        for reverse_names in [false, true] {
            for edge_mask in 0..graph_count {
                let lock = linear_dag_bounded_lock(edge_mask, reverse_names);
                let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
                let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
                let selected = indexed
                    .entries()
                    .iter()
                    .map(|entry| entry.module.clone())
                    .collect::<BTreeSet<_>>();
                let selected_bits = vec![true; indexed.entries().len()];
                let layers = linear_dag_layer_names(
                    &indexed,
                    indexed.index().topological_layers(&selected_bits),
                );
                let artifact_storage = indexed
                    .entries()
                    .iter()
                    .enumerate()
                    .map(|(entry, _)| vec![0u8; entry % 3])
                    .collect::<Vec<_>>();
                let artifacts = indexed
                    .entries()
                    .iter()
                    .zip(&artifact_storage)
                    .map(|(entry, bytes)| (entry.certificate.clone(), bytes.as_slice()))
                    .collect::<BTreeMap<_, _>>();
                let planning =
                    PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
                let actual = package_fast_execution_cost_observation(
                    &entries,
                    indexed.graph(),
                    &selected,
                    &layers,
                    &planning,
                )
                .unwrap();
                let expected = legacy_package_fast_execution_cost_vector_oracle(
                    &entries,
                    indexed.graph(),
                    &selected,
                    &layers,
                    &planning,
                )
                .unwrap();
                assert!(package_fast_execution_cost_observations_match(
                    &actual, &expected
                ));

                let mut saturated = planning;
                let first = indexed.index().topological_entries()[0];
                saturated.module_cost_by_entry[first] =
                    Some(package_module_cost_estimate_v1(u64::MAX, u64::MAX));
                let actual = package_fast_execution_cost_observation(
                    &entries,
                    indexed.graph(),
                    &selected,
                    &layers,
                    &saturated,
                )
                .unwrap();
                let expected = legacy_package_fast_execution_cost_vector_oracle(
                    &entries,
                    indexed.graph(),
                    &selected,
                    &layers,
                    &saturated,
                )
                .unwrap();
                assert!(actual.overflowed);
                assert!(package_fast_execution_cost_observations_match(
                    &actual, &expected
                ));
            }
        }
    }

    fn assert_linear_dag_memo_before_plan_contract() {
        static ARTIFACT: [u8; 1] = [0];
        let lock = linear_dag_benchmark_lock(PackageVerifierLinearDagBenchmarkShape::Chain4096);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let selected = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let artifacts = indexed
            .entries()
            .iter()
            .map(|entry| (entry.certificate.clone(), ARTIFACT.as_slice()))
            .collect::<BTreeMap<_, _>>();
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let mut planning =
            PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
        let first = *indexed.index().topological_entries().first().unwrap();
        let second = indexed.index().topological_entries()[1];
        let runnable = [(second, &indexed.entries()[second])];
        assert!(
            plan_fast_verifier_shards_with_state(&runnable, indexed.graph(), &planning, 4)
                .is_none()
        );
        assert!(legacy_plan_fast_verifier_shards_prefix_oracle(
            &runnable,
            indexed.graph(),
            &BTreeSet::new(),
            std::iter::empty::<&PackagePath>(),
            &artifacts,
            0,
            4,
        )
        .is_none());
        let mut counters = PackageVerificationPlanningCounterSummary::default();
        planning
            .record_verified_with_sink(first, &mut counters)
            .unwrap();
        let actual = plan_fast_verifier_shards_with_state(&runnable, indexed.graph(), &planning, 4);
        let expected = legacy_plan_fast_verifier_shards_prefix_oracle(
            &runnable,
            indexed.graph(),
            &BTreeSet::from([indexed.entries()[first].module.clone()]),
            [&indexed.entries()[first].certificate],
            &artifacts,
            0,
            4,
        );
        assert!(actual.is_some());
        assert_eq!(actual, expected);
        assert_eq!(counters.cumulative_verified_updates, 1);
        assert_eq!(counters.verified_prefix_record_visits, 0);
    }

    fn assert_linear_dag_unsuccessful_admission_contract() {
        static ARTIFACT: [u8; 1] = [0];
        let lock = linear_dag_benchmark_lock(PackageVerifierLinearDagBenchmarkShape::Chain4096);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let selected = BTreeSet::from([linear_dag_benchmark_name(0), linear_dag_benchmark_name(1)]);
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let artifacts = BTreeMap::from([(
            indexed.entries()[0].certificate.clone(),
            ARTIFACT.as_slice(),
        )]);
        let mut planning =
            PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
        let mut counters = PackageVerificationPlanningCounterSummary::default();
        let missing = planning
            .record_verified_with_sink(1, &mut counters)
            .unwrap_err();
        assert_eq!(
            missing.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
        assert_eq!(planning.shared_base_context_bytes, 0);
        assert_eq!(counters.cumulative_verified_updates, 0);
        planning
            .record_verified_with_sink(0, &mut counters)
            .unwrap();
        let duplicate = planning
            .record_verified_with_sink(0, &mut counters)
            .unwrap_err();
        assert_eq!(
            duplicate.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
        assert_eq!(planning.shared_base_context_bytes, 1);
        assert_eq!(counters.cumulative_verified_updates, 1);
        package_verifier_shards_match_serial_and_legacy_parallel_failure();
    }

    fn assert_linear_dag_cumulative_scale_contract() {
        static ARTIFACT: [u8; 1] = [0];
        let lock = linear_dag_benchmark_lock(PackageVerifierLinearDagBenchmarkShape::Chain4096);
        let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
        let selected = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<BTreeSet<_>>();
        let artifacts = indexed
            .entries()
            .iter()
            .map(|entry| (entry.certificate.clone(), ARTIFACT.as_slice()))
            .collect::<BTreeMap<_, _>>();
        let entries = indexed.entries().iter().enumerate().collect::<Vec<_>>();
        let mut planning =
            PackageFastPlanningState::new(&entries, indexed.graph(), &selected, &artifacts);
        let mut counters = PackageVerificationPlanningCounterSummary::default();
        for entry in indexed.index().topological_entries() {
            planning
                .record_verified_with_sink(*entry, &mut counters)
                .unwrap();
        }
        assert_eq!(planning.shared_base_context_bytes, 4_096);
        assert_eq!(counters.cumulative_verified_updates, 4_096);
        assert_eq!(counters.verified_prefix_record_visits, 0);
        assert!(!counters.overflowed);
    }

    fn assert_linear_dag_benchmark_contract(
        shape: PackageVerifierLinearDagBenchmarkShape,
        mode: PerformanceMeasurementMode,
    ) -> PackageVerifierLinearDagBenchmarkObservation {
        assert!(shape.as_str().ends_with("4096"));
        let observation = benchmark_package_verifier_linear_dag_planning(shape, mode).unwrap();
        assert_eq!(observation.module_count, 4_096);
        assert_eq!(observation.selected_count, 4_096);
        assert!(observation.oracle_match);
        assert_eq!(observation.counters.graph_index_constructions, 1);
        assert_eq!(observation.counters.reverse_list_sort_calls, 0);
        assert_eq!(observation.counters.complete_entry_fixed_point_scans, 0);
        assert_eq!(observation.counters.verified_prefix_record_visits, 0);
        assert_eq!(observation.counters.path_prefix_clone_elements, 0);
        observation
    }

    macro_rules! linear_dag_exact_test {
        ($name:ident => $contract:ident) => {
            #[test]
            fn $name() {
                $contract();
            }
        };
    }

    linear_dag_exact_test!(linear_dag_selected_closure_oracle =>
        assert_linear_dag_bounded_selected_closure_contract);
    linear_dag_exact_test!(linear_dag_selected_closure_differential =>
        assert_linear_dag_bounded_selected_closure_contract);
    linear_dag_exact_test!(linear_dag_verifier_layer_oracle =>
        assert_linear_dag_bounded_layer_contract);
    linear_dag_exact_test!(linear_dag_verifier_layer_member_order =>
        assert_linear_dag_bounded_layer_contract);
    linear_dag_exact_test!(linear_dag_verifier_sparse_layer_cases =>
        assert_linear_dag_bounded_layer_contract);
    linear_dag_exact_test!(linear_dag_layer_complexity_gate =>
        assert_linear_dag_bounded_layer_contract);
    linear_dag_exact_test!(linear_dag_local_live_oracle =>
        assert_linear_dag_local_live_contract);
    linear_dag_exact_test!(linear_dag_local_live_differential =>
        assert_linear_dag_local_live_contract);
    linear_dag_exact_test!(linear_dag_local_live_scale =>
        assert_linear_dag_local_live_scale_contract);
    linear_dag_exact_test!(linear_dag_shard_planning_oracle =>
        assert_linear_dag_shard_contract);
    linear_dag_exact_test!(linear_dag_active_shard_memory_scalar_set =>
        assert_linear_dag_shard_contract);
    linear_dag_exact_test!(linear_dag_shard_plan_differential =>
        assert_linear_dag_shard_contract);
    linear_dag_exact_test!(linear_dag_memo_hit_before_shard_plan =>
        assert_linear_dag_memo_before_plan_contract);
    linear_dag_exact_test!(linear_dag_unsuccessful_admission =>
        assert_linear_dag_unsuccessful_admission_contract);
    linear_dag_exact_test!(linear_dag_cumulative_planning_scale =>
        assert_linear_dag_cumulative_scale_contract);

    #[test]
    fn linear_dag_critical_path_oracle() {
        linear_dag_critical_path_binary_lifting_matches_vector_order();
        assert_linear_dag_critical_path_vector_contract();
        let observation = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
            PerformanceMeasurementMode::Summary,
        );
        assert_eq!(observation.critical_path_length, 3_072);
        assert_eq!(observation.counters.critical_path_state_nodes, 4_096);
    }

    #[test]
    fn linear_dag_critical_path_tie_characterization() {
        linear_dag_critical_path_binary_lifting_matches_vector_order();
        assert_linear_dag_critical_path_vector_contract();
    }

    #[test]
    fn linear_dag_critical_path_differential() {
        assert_linear_dag_critical_path_vector_contract();
        let summary = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
            PerformanceMeasurementMode::Summary,
        );
        let detailed = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
            PerformanceMeasurementMode::Detailed,
        );
        assert_eq!(summary.critical_path_length, detailed.critical_path_length);
        assert_eq!(summary.counters, detailed.counters);
        assert_eq!(summary.shard_profile, detailed.shard_profile);
    }

    #[test]
    fn linear_dag_critical_path_scale() {
        let observation = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Detailed,
        );
        assert_eq!(observation.critical_path_length, 4_096);
        assert_eq!(observation.counters.critical_path_state_nodes, 4_096);
        assert_eq!(observation.counters.final_reconstructed_path_length, 4_096);
    }

    #[test]
    fn linear_dag_measurement_off_gate() {
        let off = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PerformanceMeasurementMode::Off,
        );
        let summary = assert_linear_dag_benchmark_contract(
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PerformanceMeasurementMode::Summary,
        );
        assert_eq!(off.critical_path_length, 0);
        assert_eq!(off.counters.critical_path_state_nodes, 0);
        assert_eq!(off.counters.final_reconstructed_path_length, 0);
        assert_eq!(off.shard_profile, summary.shard_profile);
    }

    #[test]
    fn linear_dag_fixture_generator() {
        let graph_count = 1u64 << (LINEAR_DAG_BOUNDED_MODULE_COUNT * 3 / 2);
        for reverse_names in [false, true] {
            for edge_mask in 0..graph_count {
                let lock = linear_dag_bounded_lock(edge_mask, reverse_names);
                let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
                assert_eq!(indexed.entries().len(), LINEAR_DAG_BOUNDED_MODULE_COUNT);
                assert_eq!(
                    indexed.index().topological_entries().len(),
                    LINEAR_DAG_BOUNDED_MODULE_COUNT
                );
            }
        }
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            let lock = linear_dag_benchmark_lock(shape);
            let indexed = npa_package::build_indexed_package_lock_graph(&lock).unwrap();
            assert_eq!(indexed.entries().len(), 4_096);
            assert_eq!(
                indexed.index().topological_entries().len(),
                indexed.entries().len()
            );
        }
    }

    #[test]
    fn linear_dag_graph_error_authority() {
        package_source_free_invalid_graph_fails_before_artifact_or_checker_lookup();
    }

    #[test]
    fn linear_dag_4096_all_modes() {
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            for mode in [
                PerformanceMeasurementMode::Off,
                PerformanceMeasurementMode::Summary,
                PerformanceMeasurementMode::Detailed,
            ] {
                assert_linear_dag_benchmark_contract(shape, mode);
            }
        }
    }

    #[test]
    fn linear_dag_package_report_differential() {
        package_indexed_verifier_boundaries_match_source_compatible_wrappers();
        package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized();
        package_verifier_shards_match_serial_and_legacy_parallel_failure();
    }

    fn assert_snapshot_input_contract() {
        package_snapshot_fast_input_matches_raw_and_releases_retention();
    }

    fn assert_snapshot_key_contract() {
        package_verification_memo_snapshot_lane_key_parity();
        package_verification_memo_owned_slots_reuse_file_hash();
        package_verification_memo_fast_retained_slot_reuses_header();
        package_verification_memo_fast_fallback_decodes_header_once();
        package_verification_memo_reference_slots_decode_raw_header_once();
    }

    fn assert_snapshot_error_metadata_contract() {
        linear_dag_missing_artifact_authority();
        package_fast_verifier_rejects_stale_certificate_file_hash();
        package_snapshot_cached_outer_validation_errors_release_all();
    }

    fn assert_snapshot_disk_wrapper_contract() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let hits = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let raw = verify_package_fast_source_free_with_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            hits.clone(),
        )
        .unwrap();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let snapshot = verify_package_fast_source_free_with_artifact_snapshots_and_disk_memo_hits(
            &validated,
            &lock,
            &mut prepared,
            hits,
        )
        .unwrap();
        assert_eq!(snapshot, raw);
        assert_eq!(prepared.retained_decoded_entries(), 0);
        assert_eq!(prepared.retained_decoded_bytes(), 0);
    }

    fn assert_snapshot_cache_aware_wrapper_contract() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let hits = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let dirty = [lock.entries[0].module.clone()];
        let raw = verify_package_fast_source_free_with_cache_aware_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            hits.clone(),
            dirty.clone(),
        )
        .unwrap();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let snapshot =
            verify_package_fast_source_free_with_artifact_snapshots_and_cache_aware_disk_memo_hits(
                &validated,
                &lock,
                &mut prepared,
                hits,
                dirty,
            )
            .unwrap();
        assert_eq!(snapshot, raw);
        assert_eq!(prepared.retained_decoded_entries(), 0);
        assert_eq!(prepared.retained_decoded_bytes(), 0);
    }

    fn assert_snapshot_unselected_release_contract() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let initial = prepared.retention_observation().unwrap();
        let report = verify_package_fast_source_free_with_artifact_snapshots_and_options(
            &validated,
            &lock,
            &mut prepared,
            PackageVerificationExecutionOptions {
                selected_modules: Some(BTreeSet::new()),
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        assert_eq!(report.status, PackageVerificationStatus::Passed);
        assert!(report.modules.is_empty());
        let final_retention = prepared.retention_observation().unwrap();
        assert_eq!(final_retention.current_entries, 0);
        assert_eq!(final_retention.current_bytes, 0);
        assert_eq!(final_retention.charged_releases, initial.admissions);
        assert_eq!(final_retention.released_bytes, initial.admitted_bytes);
    }

    fn assert_snapshot_reference_cache_aware_contract() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let (prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let hashed = lock
            .entries
            .iter()
            .map(|entry| prepared.clone_hashed_raw(&entry.certificate).unwrap())
            .collect::<Vec<_>>();
        let hits = lock
            .entries
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let dirty = [lock.entries[0].module.clone()];
        let raw = verify_package_reference_source_free_with_cache_aware_disk_memo_hits(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            hits.clone(),
            dirty.clone(),
        )
        .unwrap();
        let hashed_report =
            verify_package_reference_source_free_with_hashed_artifacts_and_cache_aware_disk_memo_hits(
                &validated,
                &lock,
                hashed.iter(),
                hits,
                dirty,
            )
            .unwrap();
        assert_eq!(hashed_report, raw);
    }

    fn assert_snapshot_shard_accounting_contract() {
        package_fast_cost_and_memory_models_saturate_and_cap_jobs_deterministically();
        package_term_memory_model_job_boundaries();
        package_term_memory_model_landing_history();
        assert_linear_dag_shard_contract();
        package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized();
    }

    fn assert_report_functional_parity(
        actual: &PackageVerificationReport,
        expected: &PackageVerificationReport,
    ) {
        assert_eq!(actual.mode, expected.mode);
        assert_eq!(actual.axiom_policy_hash, expected.axiom_policy_hash);
        assert_eq!(actual.verdict_source, expected.verdict_source);
        assert_eq!(
            actual.reference_checker_verdict,
            expected.reference_checker_verdict
        );
        assert_eq!(actual.locally_accelerated, expected.locally_accelerated);
        assert_eq!(actual.status, expected.status);
        assert_eq!(actual.topological_order, expected.topological_order);
        assert_eq!(actual.modules, expected.modules);
    }

    fn snapshot_execution_options(
        selected_modules: Option<BTreeSet<Name>>,
        memoization: PackageVerificationMemoMode,
        decode_cache: PackageVerificationDecodeCacheMode,
    ) -> PackageVerificationExecutionOptions {
        PackageVerificationExecutionOptions {
            selected_modules,
            memoization,
            decode_cache,
            collect_decode_cache_counters: decode_cache
                != PackageVerificationDecodeCacheMode::Disabled,
            ..PackageVerificationExecutionOptions::default()
        }
    }

    fn assert_snapshot_ordinary_input_matrix() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let execution_sets = [
            None,
            Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")])),
            Some(BTreeSet::new()),
        ];

        for selected_modules in execution_sets {
            let raw = verify_package_fast_source_free_with_options(
                &validated,
                &lock,
                package_certificate_artifacts(&bytes),
                snapshot_execution_options(
                    selected_modules.clone(),
                    PackageVerificationMemoMode::Disabled,
                    PackageVerificationDecodeCacheMode::Disabled,
                ),
            )
            .unwrap();

            for policy in [
                PreparedArtifactRetentionPolicy::RawOnly,
                PreparedArtifactRetentionPolicy::FastCandidateV1,
            ] {
                let (mut prepared, preparation) =
                    proof_prepared_artifacts(&validated, &lock, policy);
                let initial_retention = prepared.retention_observation().unwrap();
                let mut observation = PackageCertificateArtifactObservation::default();
                observation.merge_preparation(preparation);
                let snapshot = verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
                    &validated,
                    &lock,
                    &mut prepared,
                    snapshot_execution_options(
                        selected_modules.clone(),
                        PackageVerificationMemoMode::Disabled,
                        PackageVerificationDecodeCacheMode::Disabled,
                    ),
                    Some(&mut observation),
                )
                .unwrap();
                assert_report_functional_parity(&snapshot, &raw);
                assert_eq!(
                    observation.artifact_file_hashes,
                    u64::try_from(lock.entries.len()).unwrap()
                );
                assert_eq!(
                    observation.artifact_full_decodes,
                    u64::try_from(lock.entries.len()).unwrap()
                        + if policy == PreparedArtifactRetentionPolicy::RawOnly {
                            u64::try_from(snapshot.modules.len()).unwrap()
                        } else {
                            0
                        }
                );
                assert_eq!(
                    observation.artifact_prepared_reuses,
                    if policy == PreparedArtifactRetentionPolicy::FastCandidateV1 {
                        u64::try_from(snapshot.modules.len()).unwrap()
                    } else {
                        0
                    }
                );
                let final_retention = prepared.retention_observation().unwrap();
                assert_eq!(final_retention.current_entries, 0);
                assert_eq!(final_retention.current_bytes, 0);
                assert_eq!(
                    final_retention.charged_releases,
                    initial_retention.admissions
                );
                assert_eq!(
                    final_retention.released_bytes,
                    initial_retention.admitted_bytes
                );
            }

            let (mut fallback, preparation) = proof_prepared_artifacts(
                &validated,
                &lock,
                PreparedArtifactRetentionPolicy::FastCandidateV1,
            );
            let execution_modules = raw
                .modules
                .iter()
                .map(|module| module.module.clone())
                .collect::<BTreeSet<_>>();
            let fallback_count = lock
                .entries
                .iter()
                .filter(|entry| execution_modules.contains(&entry.module))
                .take(1)
                .map(|entry| {
                    assert!(matches!(
                        fallback.release_decoded(
                            &entry.certificate,
                            PreparedArtifactReleaseReason::Unselected,
                        ),
                        PreparedArtifactRelease::Charged { .. }
                    ));
                    1u64
                })
                .sum::<u64>();
            let mut observation = PackageCertificateArtifactObservation::default();
            observation.merge_preparation(preparation);
            let fallback_report = verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
                &validated,
                &lock,
                &mut fallback,
                snapshot_execution_options(
                    selected_modules,
                    PackageVerificationMemoMode::Disabled,
                    PackageVerificationDecodeCacheMode::Disabled,
                ),
                Some(&mut observation),
            )
            .unwrap();
            assert_report_functional_parity(&fallback_report, &raw);
            assert_eq!(
                observation.artifact_full_decodes,
                u64::try_from(lock.entries.len()).unwrap() + fallback_count
            );
            assert_eq!(
                observation.artifact_prepared_reuses,
                u64::try_from(fallback_report.modules.len()).unwrap() - fallback_count
            );
            assert_eq!(fallback.retained_decoded_entries(), 0);
            assert_eq!(fallback.retained_decoded_bytes(), 0);
        }
    }

    fn assert_snapshot_memo_and_decode_cache_matrix() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let selected = Some(BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]));

        for decode_cache in [
            PackageVerificationDecodeCacheMode::Disabled,
            PackageVerificationDecodeCacheMode::ProcessLocal,
        ] {
            let _guard = (decode_cache == PackageVerificationDecodeCacheMode::ProcessLocal)
                .then(decode_cache_test_lock);
            if decode_cache == PackageVerificationDecodeCacheMode::ProcessLocal {
                clear_package_verification_decode_cache();
            }
            let raw = verify_package_fast_source_free_with_options(
                &validated,
                &lock,
                package_certificate_artifacts(&bytes),
                snapshot_execution_options(
                    selected.clone(),
                    PackageVerificationMemoMode::Disabled,
                    decode_cache,
                ),
            )
            .unwrap();
            if decode_cache == PackageVerificationDecodeCacheMode::ProcessLocal {
                clear_package_verification_decode_cache();
            }
            let (mut prepared, _) = proof_prepared_artifacts(
                &validated,
                &lock,
                PreparedArtifactRetentionPolicy::FastCandidateV1,
            );
            let snapshot = verify_package_fast_source_free_with_artifact_snapshots_and_options(
                &validated,
                &lock,
                &mut prepared,
                snapshot_execution_options(
                    selected.clone(),
                    PackageVerificationMemoMode::Disabled,
                    decode_cache,
                ),
            )
            .unwrap();
            assert_report_functional_parity(&snapshot, &raw);
            if decode_cache == PackageVerificationDecodeCacheMode::ProcessLocal {
                let raw_counters = raw.decode_cache_counters.unwrap();
                let snapshot_counters = snapshot.decode_cache_counters.unwrap();
                assert!(raw_counters.certificate_misses > 0);
                assert_eq!(snapshot_counters.certificate_hits, 0);
                assert_eq!(snapshot_counters.certificate_misses, 0);
                clear_package_verification_decode_cache();
            }
        }

        let raw_handle = test_process_memo_handle();
        let raw = verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_certificate_artifacts(&bytes),
            snapshot_execution_options(
                selected.clone(),
                PackageVerificationMemoMode::ProcessLocal(raw_handle),
                PackageVerificationDecodeCacheMode::Disabled,
            ),
        )
        .unwrap();
        let snapshot_handle = test_process_memo_handle();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let snapshot = verify_package_fast_source_free_with_artifact_snapshots_and_options(
            &validated,
            &lock,
            &mut prepared,
            snapshot_execution_options(
                selected,
                PackageVerificationMemoMode::ProcessLocal(snapshot_handle),
                PackageVerificationDecodeCacheMode::Disabled,
            ),
        )
        .unwrap();
        assert_report_functional_parity(&snapshot, &raw);
        assert_eq!(
            snapshot.memo_counters.keys_built,
            raw.memo_counters.keys_built
        );
        assert_eq!(snapshot.memo_counters.hits, raw.memo_counters.hits);
        assert_eq!(snapshot.memo_counters.misses, raw.memo_counters.misses);
        assert_eq!(snapshot.memo_counters.inserted, raw.memo_counters.inserted);
        assert!(raw.memo_counters.certificate_bytes_hashed > 0);
        assert_eq!(snapshot.memo_counters.certificate_bytes_hashed, 0);
    }

    fn assert_snapshot_fast_differential_contract() {
        assert_snapshot_ordinary_input_matrix();
        assert_snapshot_memo_and_decode_cache_matrix();
        package_snapshot_cached_fast_paths_match_raw_and_release_all();
        assert_snapshot_disk_wrapper_contract();
        assert_snapshot_cache_aware_wrapper_contract();
        package_verifier_parallel_fast_jobs_four_matches_jobs_one_normalized();
    }

    fn assert_snapshot_memory_accounting_contract() {
        #[derive(Clone, Copy)]
        struct PhaseCharge {
            artifact_bytes: u64,
            prepared_live: u64,
            candidate_current: u64,
            key_candidate_current: u64,
            verified_live: u64,
            cache: crate::PackageDecodeCacheChargeState,
            worker_count: u64,
            worker_scratch: u64,
            independent_lanes: u64,
            independent_scratch: u64,
        }

        fn charge(phase: PhaseCharge) -> Option<u64> {
            let cache = match phase.cache {
                crate::PackageDecodeCacheChargeState::Disabled => 0,
                crate::PackageDecodeCacheChargeState::UnboundedUnknown => return None,
                crate::PackageDecodeCacheChargeState::Bounded { current_bytes, .. } => {
                    current_bytes
                }
            };
            Some(
                phase
                    .artifact_bytes
                    .saturating_add(phase.prepared_live)
                    .saturating_add(phase.candidate_current)
                    .saturating_add(phase.key_candidate_current)
                    .saturating_add(phase.verified_live)
                    .saturating_add(cache)
                    .saturating_add(phase.worker_count.saturating_mul(phase.worker_scratch))
                    .saturating_add(
                        phase
                            .independent_lanes
                            .saturating_mul(phase.independent_scratch),
                    ),
            )
        }

        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifact_bytes = proof_certificate_artifacts(&lock)
            .values()
            .map(|bytes| u64::try_from(bytes.len()).unwrap())
            .sum::<u64>();
        let (mut prepared, preparation) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let admitted = prepared.retention_observation().unwrap();
        assert_eq!(preparation.artifact_file_hashes, lock.entries.len() as u64);
        assert_eq!(preparation.artifact_full_decodes, lock.entries.len() as u64);
        assert_eq!(admitted.current_bytes, admitted.admitted_bytes);
        assert_eq!(admitted.derivation_candidate_current_bytes, 0);
        assert!(admitted.derivation_candidate_peak_bytes > 0);

        let lock_phase = PhaseCharge {
            artifact_bytes,
            prepared_live: admitted.current_bytes,
            candidate_current: admitted.derivation_candidate_peak_bytes,
            key_candidate_current: 0,
            verified_live: 0,
            cache: crate::PackageDecodeCacheChargeState::Disabled,
            worker_count: 0,
            worker_scratch: 0,
            independent_lanes: 0,
            independent_scratch: 0,
        };
        assert_eq!(
            charge(lock_phase),
            Some(
                artifact_bytes + admitted.current_bytes + admitted.derivation_candidate_peak_bytes
            )
        );
        assert_eq!(
            charge(PhaseCharge {
                cache: crate::PackageDecodeCacheChargeState::UnboundedUnknown,
                ..lock_phase
            }),
            None
        );
        assert_eq!(
            charge(PhaseCharge {
                cache: crate::PackageDecodeCacheChargeState::Bounded {
                    current_bytes: 13,
                    peak_bytes: 21,
                },
                key_candidate_current: 17,
                verified_live: 19,
                worker_count: 2,
                worker_scratch: 23,
                independent_lanes: 1,
                independent_scratch: 29,
                ..lock_phase
            }),
            Some(
                artifact_bytes
                    + admitted.current_bytes
                    + admitted.derivation_candidate_peak_bytes
                    + 17
                    + 19
                    + 13
                    + 2 * 23
                    + 29
            )
        );
        assert_eq!(
            charge(PhaseCharge {
                artifact_bytes: u64::MAX,
                ..lock_phase
            }),
            Some(u64::MAX)
        );
        assert_eq!(
            charge(PhaseCharge {
                prepared_live: 31,
                verified_live: 31,
                candidate_current: 0,
                ..lock_phase
            }),
            Some(artifact_bytes + 62),
            "aliased prepared and verified stores remain conservatively double charged"
        );

        let estimate =
            package_fast_shard_memory_estimate_v3(8, 8, 0, admitted.current_bytes, 1, false);
        assert_eq!(estimate.prepared_shared_bytes, admitted.current_bytes);
        assert_eq!(estimate.combined_shared_bytes, admitted.current_bytes);
        let mut artifact_observation = PackageCertificateArtifactObservation::default();
        artifact_observation.merge_preparation(preparation);
        let report =
            verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation(
                &validated,
                &lock,
                &mut prepared,
                PackageVerificationExecutionOptions::default(),
                Some(&mut artifact_observation),
            )
            .unwrap();
        assert_eq!(report.status, PackageVerificationStatus::Passed);
        let released = prepared.retention_observation().unwrap();
        assert_eq!(released.current_bytes, 0);
        assert_eq!(released.charged_releases, admitted.admissions);
        assert_eq!(released.released_bytes, admitted.admitted_bytes);

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_package_certificate_artifacts(&artifact_observation, Some(&released));
        let measurement = recorder.report().unwrap();
        let counter = |label| {
            measurement
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
        };
        assert_eq!(
            counter(PerformanceMeasurementLabel::PackagePreparedArtifactCurrentBytes),
            Some(0)
        );
        assert_eq!(
            counter(PerformanceMeasurementLabel::PackagePreparedArtifactPeakBytes),
            Some(admitted.peak_bytes)
        );
        assert_eq!(
            counter(PerformanceMeasurementLabel::PackageArtifactPreparedReuses),
            Some(lock.entries.len() as u64)
        );
    }

    fn assert_snapshot_key_differential_contract() {
        assert_snapshot_key_contract();
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let bytes = proof_certificate_artifacts(&lock);
        let entries = canonical_lock_entries(&lock);
        let graph = validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();

        for mode in [
            PackageVerificationMode::FastKernel,
            PackageVerificationMode::Reference,
        ] {
            let raw = package_verification_memo_key_inputs(
                &validated,
                &lock,
                package_certificate_artifacts(&bytes),
                mode,
            )
            .unwrap();
            for policy in [
                PreparedArtifactRetentionPolicy::RawOnly,
                PreparedArtifactRetentionPolicy::FastCandidateV1,
            ] {
                let (mut prepared, _) = proof_prepared_artifacts(&validated, &lock, policy);
                let retained = package_verification_memo_key_inputs_from_artifact_snapshots(
                    &validated, &lock, &prepared, mode,
                )
                .unwrap();
                assert_eq!(retained, raw);

                let fallback_entry = lock.entries.first().unwrap();
                let _ = prepared.release_decoded(
                    &fallback_entry.certificate,
                    PreparedArtifactReleaseReason::Unselected,
                );
                let fallback = package_verification_memo_key_inputs_from_artifact_snapshots(
                    &validated, &lock, &prepared, mode,
                )
                .unwrap();
                assert_eq!(fallback, raw);
                for module in raw.keys() {
                    assert_eq!(
                        package_audit_process_memo_key(&fallback[module]),
                        package_audit_process_memo_key(&raw[module])
                    );
                }
            }

            let mut missing = bytes.clone();
            missing.remove(&lock.entries[0].certificate);
            let missing_raw = package_verification_memo_key_inputs_for_entries(
                &validated,
                &lock,
                &graph,
                &entries,
                &artifact_byte_map(package_certificate_artifacts(&missing)).unwrap(),
                mode,
            )
            .unwrap();
            assert!(!missing_raw.contains_key(&lock.entries[0].module));

            let mut malformed = bytes.clone();
            malformed.insert(
                lock.entries[0].certificate.clone(),
                b"not-a-header".to_vec(),
            );
            let malformed_raw = package_verification_memo_key_inputs_for_entries(
                &validated,
                &lock,
                &graph,
                &entries,
                &artifact_byte_map(package_certificate_artifacts(&malformed)).unwrap(),
                mode,
            )
            .unwrap();
            assert!(!malformed_raw.contains_key(&lock.entries[0].module));

            let owned = malformed
                .into_iter()
                .map(|(path, bytes)| OwnedPackageLockArtifact::from_vec(path, bytes));
            let error = build_package_lock_and_snapshot_owned_artifacts(
                &validated,
                PackagePath::new("npa-package.toml"),
                proof_manifest_source().as_bytes(),
                owned,
                PreparedArtifactRetentionPolicy::FastCandidateV1,
                PreparedArtifactObservationMode::Aggregate,
                None,
            )
            .expect_err("malformed owned bytes fail before snapshot key construction");
            assert_eq!(
                error.reason_code,
                npa_package::PackageLockErrorReason::CertificateFileHashMismatch
            );
        }
    }

    fn assert_snapshot_retention_integration_contract() {
        assert_snapshot_unselected_release_contract();
        package_snapshot_process_memo_reuses_keys_without_rehashing_artifacts();
        package_snapshot_cached_fast_paths_match_raw_and_release_all();
        assert_snapshot_disk_wrapper_contract();
        package_snapshot_cached_outer_validation_errors_release_all();
        package_snapshot_fast_input_matches_raw_and_releases_retention();
        package_snapshot_release_not_found();
    }

    fn assert_snapshot_work_count_contract() {
        assert_snapshot_ordinary_input_matrix();
        package_snapshot_process_memo_reuses_keys_without_rehashing_artifacts();
        package_hashed_reference_process_memo_reuses_file_hash_and_hits();
        package_snapshot_cached_fast_paths_match_raw_and_release_all();
        assert_snapshot_disk_wrapper_contract();
        package_snapshot_cached_outer_validation_errors_release_all();
    }

    macro_rules! snapshot_exact_test {
        ($name:ident => $contract:ident) => {
            #[test]
            fn $name() {
                $contract();
            }
        };
    }

    snapshot_exact_test!(snapshot_verifier_error_oracle => assert_snapshot_error_metadata_contract);
    snapshot_exact_test!(snapshot_key_work_oracle => assert_snapshot_key_contract);
    snapshot_exact_test!(snapshot_checker_work_oracle => assert_snapshot_work_count_contract);
    snapshot_exact_test!(snapshot_metadata_work_oracle => assert_snapshot_error_metadata_contract);

    #[test]
    fn package_snapshot_release_not_found() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let (mut prepared, _) = proof_prepared_artifacts(
            &validated,
            &lock,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let before = prepared.retention_observation();
        let mut missing = lock.entries[0].clone();
        missing.certificate = PackagePath::new("missing/snapshot.npcert");
        let error = release_prepared_artifact(
            &mut prepared,
            &missing,
            PreparedArtifactReleaseReason::LiveResult,
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::CertificateArtifactMissing
        );
        assert_eq!(error.path, "artifacts");
        assert_eq!(
            error.expected_value.as_deref(),
            Some("missing/snapshot.npcert")
        );
        assert_eq!(prepared.retention_observation(), before);
    }

    snapshot_exact_test!(package_fast_raw_input => assert_snapshot_ordinary_input_matrix);
    snapshot_exact_test!(package_fast_hashed_input => assert_fast_hashed_artifact_contract);
    snapshot_exact_test!(package_fast_prepared_input => assert_snapshot_ordinary_input_matrix);
    snapshot_exact_test!(package_fast_prepared_fallback => assert_snapshot_ordinary_input_matrix);
    snapshot_exact_test!(package_result_header_metadata => assert_snapshot_ordinary_input_matrix);
    snapshot_exact_test!(verify_package_fast_source_free_with_artifact_snapshots =>
        assert_snapshot_ordinary_input_matrix);
    snapshot_exact_test!(package_fast_snapshot_local_audit =>
        package_snapshot_cached_fast_paths_match_raw_and_release_all);
    snapshot_exact_test!(package_fast_snapshot_disk_memo => assert_snapshot_disk_wrapper_contract);
    snapshot_exact_test!(package_fast_snapshot_cache_aware_disk_memo =>
        assert_snapshot_cache_aware_wrapper_contract);
    snapshot_exact_test!(package_artifact_prepared_reuses => assert_snapshot_work_count_contract);
    snapshot_exact_test!(package_snapshot_memo_key_inputs => assert_snapshot_key_contract);
    snapshot_exact_test!(package_snapshot_key_validated_helper => assert_snapshot_key_contract);
    snapshot_exact_test!(package_snapshot_memo_run =>
        package_snapshot_process_memo_reuses_keys_without_rehashing_artifacts);
    snapshot_exact_test!(package_snapshot_fast_memo_keys => assert_snapshot_key_contract);
    snapshot_exact_test!(package_snapshot_reference_memo_keys => assert_snapshot_key_contract);
    snapshot_exact_test!(package_snapshot_release_unselected =>
        assert_snapshot_unselected_release_contract);
    snapshot_exact_test!(package_snapshot_release_process_memo_hit =>
        package_snapshot_process_memo_reuses_keys_without_rehashing_artifacts);
    snapshot_exact_test!(package_snapshot_release_local_audit =>
        package_snapshot_cached_fast_paths_match_raw_and_release_all);
    snapshot_exact_test!(package_snapshot_release_disk_memo => assert_snapshot_disk_wrapper_contract);
    snapshot_exact_test!(package_snapshot_release_blocked =>
        package_snapshot_cached_outer_validation_errors_release_all);
    snapshot_exact_test!(package_snapshot_release_live_result => assert_snapshot_input_contract);
    snapshot_exact_test!(package_snapshot_operation_teardown =>
        package_snapshot_cached_outer_validation_errors_release_all);
    snapshot_exact_test!(package_reference_hashed_artifact =>
        package_verification_memo_snapshot_lane_key_parity);
    snapshot_exact_test!(package_reference_hashed_local_audit =>
        package_verification_memo_snapshot_lane_key_parity);
    snapshot_exact_test!(package_reference_hashed_disk_memo =>
        package_verification_memo_snapshot_lane_key_parity);
    snapshot_exact_test!(package_reference_hashed_cache_aware_disk_memo =>
        assert_snapshot_reference_cache_aware_contract);
    snapshot_exact_test!(package_fast_shard_prepared_memory_model =>
        assert_snapshot_shard_accounting_contract);
    snapshot_exact_test!(package_snapshot_owned_full_decode_counts => assert_snapshot_input_contract);

    #[test]
    fn package_snapshot_key_candidate_bytes() {
        let mut observation = PackageCertificateArtifactObservation::default();
        observation.begin_key_candidate(17);
        assert_eq!(observation.key_candidate_current_bytes, 17);
        assert_eq!(observation.key_candidate_peak_bytes, 17);
        observation.finish_key_candidate();
        observation.begin_key_candidate(11);
        assert_eq!(observation.key_candidate_current_bytes, 11);
        assert_eq!(observation.key_candidate_peak_bytes, 17);
        observation.finish_key_candidate();
        assert_eq!(observation.key_candidate_current_bytes, 0);
    }

    snapshot_exact_test!(package_snapshot_memory_accounting =>
        assert_snapshot_memory_accounting_contract);
    snapshot_exact_test!(package_snapshot_fast_differential =>
        assert_snapshot_fast_differential_contract);
    snapshot_exact_test!(package_snapshot_key_differential =>
        assert_snapshot_key_differential_contract);
    snapshot_exact_test!(package_reference_hashed_differential =>
        assert_snapshot_reference_cache_aware_contract);
    snapshot_exact_test!(package_snapshot_negative_differential =>
        assert_snapshot_error_metadata_contract);
    snapshot_exact_test!(package_snapshot_retention_integration =>
        assert_snapshot_retention_integration_contract);
    snapshot_exact_test!(package_fast_shard_prepared_thresholds =>
        assert_snapshot_shard_accounting_contract);
    snapshot_exact_test!(package_snapshot_work_count_gates => assert_snapshot_work_count_contract);
}

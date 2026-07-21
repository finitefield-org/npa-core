use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
    sync::{Mutex, OnceLock},
    thread,
    time::Instant,
};

use npa_cert::{
    decode_module_cert, verify_decoded_module_cert, verify_decoded_module_cert_with_import_refs,
    AxiomPolicy, CertError, CoreFeature, DeclCert, DeclPayload, ModuleCert, Name, TermNode,
    VerifiedModule, VerifierSession,
};
use npa_checker_ref::{
    check_certificate, check_certificate_with_observation, ReferenceCertificateSection,
    ReferenceCheckError, ReferenceCheckErrorKind, ReferenceCheckObservation, ReferenceCheckReason,
    ReferenceCheckResult, ReferenceCheckedModule, ReferenceCheckerPolicy, ReferenceCoreFeature,
    ReferenceImportStore, ReferenceModuleName, ReferenceTrustMode,
};
use npa_package::{
    build_package_lock_graph, format_package_hash, package_audit_process_memo_key,
    package_file_hash, package_import_context_export_cache_entry_json,
    package_import_context_export_cache_key, parse_package_import_context_export_cache_entry_json,
    validate_observed_package_lock_against_manifest_graph,
    validate_package_lock_against_manifest_graph, PackageArtifactErrorReason,
    PackageAuditCacheKeyInput, PackageAuditCheckerIdentity, PackageAuditImportIdentity,
    PackageHash, PackageImportContextExportCacheEntry, PackageImportContextExportCacheKeyInput,
    PackageImportContextExportData, PackageLockEntry, PackageLockEntryOrigin, PackageLockGraph,
    PackageLockManifest, PackageLockResolvedImport, PackagePath, ValidatedPackageManifest,
    CHECKER_PROFILE_REFERENCE_V0_1, PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA,
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
    PerformanceDeclarationMeasurement, PerformanceMeasurementLabel, PerformanceMeasurementMode,
    PerformanceMeasurementRecorder, PerformanceMeasurementReport, PerformanceModuleMeasurement,
    PerformancePackageLayerMeasurement, PerformancePackageModuleShardingMeasurement,
    PerformancePackageShardCostModel, PerformancePackageShardMeasurement,
    PerformancePackageShardMemoryModel, PerformancePackageShardReductionReason,
    PerformancePackageShardingMeasurement, PerformanceWorkerMeasurement,
    PERFORMANCE_DECLARATION_DETAIL_LIMIT, PERFORMANCE_MODULE_DETAIL_LIMIT,
    PERFORMANCE_WORKER_DETAIL_LIMIT,
};

const PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;
const PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1: u64 = 4_096;
const PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1: u64 = 1024 * 1024 * 1024;
const PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1: u64 = 8 * 1024 * 1024;
const PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1: u64 = 4;
static NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP: AtomicUsize = AtomicUsize::new(0);

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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageVerificationMemoMode {
    /// Do not read or write the process-local verifier memo.
    Disabled,
    /// Reuse exact verifier results within this process only.
    ProcessLocal,
}

impl PackageVerificationMemoMode {
    /// Return whether process-local memoization is enabled.
    pub const fn is_enabled(self) -> bool {
        match self {
            Self::Disabled => false,
            Self::ProcessLocal => true,
        }
    }
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
    /// Import context cache hits in this verifier run.
    pub import_context_hits: usize,
    /// Import context cache misses in this verifier run.
    pub import_context_misses: usize,
    /// Import context entries inserted in this verifier run.
    pub import_context_inserted: usize,
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
            || self.import_context_hits > 0
            || self.import_context_misses > 0
            || self.import_context_inserted > 0
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
        self.import_context_hits = self
            .import_context_hits
            .saturating_add(other.import_context_hits);
        self.import_context_misses = self
            .import_context_misses
            .saturating_add(other.import_context_misses);
        self.import_context_inserted = self
            .import_context_inserted
            .saturating_add(other.import_context_inserted);
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
        self.hits > 0 || self.misses > 0 || self.inserted > 0
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

#[derive(Debug, Default)]
struct PackageVerificationProcessMemo {
    entries: BTreeMap<String, PackageVerificationMemoEntry>,
}

static PACKAGE_VERIFICATION_PROCESS_MEMO: OnceLock<Mutex<PackageVerificationProcessMemo>> =
    OnceLock::new();

#[derive(Debug, Default)]
struct PackageVerificationDecodeCache {
    fast_certificates: BTreeMap<String, ModuleCert>,
    reference_import_contexts: BTreeMap<String, ReferenceImportStore>,
}

static PACKAGE_VERIFICATION_DECODE_CACHE: OnceLock<Mutex<PackageVerificationDecodeCache>> =
    OnceLock::new();

/// Clear the process-local package verification memo.
///
/// This is intended for tests and deterministic package-gate orchestration. It
/// does not touch disk-backed audit cache entries.
pub fn clear_package_verification_process_memo() {
    package_verification_process_memo()
        .lock()
        .expect("package verification process memo mutex should not be poisoned")
        .entries
        .clear();
}

/// Return the current process-local package verification memo entry count.
pub fn package_verification_process_memo_entry_count() -> usize {
    package_verification_process_memo()
        .lock()
        .expect("package verification process memo mutex should not be poisoned")
        .entries
        .len()
}

/// Clear the process-local package verification decode/import cache.
///
/// This cache stores decoded certificate structures and materialized import
/// contexts only. It does not store checker acceptance verdicts and does not
/// touch disk-backed audit cache or verifier memo entries.
pub fn clear_package_verification_decode_cache() {
    *package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned") =
        PackageVerificationDecodeCache::default();
}

/// Clear the disk-backed import-context export-data cache rooted at the current
/// working directory.
///
/// This cache stores local acceleration metadata only. Removing it must not
/// change verifier acceptance.
pub fn clear_package_import_context_export_disk_cache() {
    let _ = fs::remove_dir_all(package_import_context_export_cache_dir());
}

/// Return the current disk-backed import-context export-data cache file count.
pub fn package_import_context_export_disk_cache_entry_count() -> usize {
    let cache_dir = package_import_context_export_cache_dir();
    match fs::read_dir(cache_dir) {
        Ok(entries) => entries
            .filter_map(Result::ok)
            .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
            .count(),
        Err(error) if error.kind() == io::ErrorKind::NotFound => 0,
        Err(_) => 0,
    }
}

/// Return the current process-local package verification decode/import cache size.
pub fn package_verification_decode_cache_entry_count() -> usize {
    let cache = package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned");
    cache.fast_certificates.len() + cache.reference_import_contexts.len()
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
    if options.jobs == 1
        && options.selected_modules.is_none()
        && !options.memoization.is_enabled()
        && options.decode_cache == PackageVerificationDecodeCacheMode::Disabled
        && !options.collect_decode_cache_counters
        && options.measurement_mode == PerformanceMeasurementMode::Off
    {
        return verify_package_fast_source_free_report(validated, lock, artifacts);
    }
    Ok(verify_package_fast_source_free_execution(validated, lock, artifacts, options)?.report)
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
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
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
        topological_order: graph.topological_order,
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
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::FastKernel,
            ));
            continue;
        }

        let bytes = match read_certificate_artifact_from_root(package_root, *entry_index, entry) {
            Ok(bytes) => bytes,
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
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
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
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
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    package_verification_memo_key_inputs_for_entries(
        validated,
        lock,
        &graph,
        &entries,
        &artifact_bytes,
        mode,
    )
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
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_options(&entries, &graph, &options)?;
    let execution_layers = execution_layers_for_modules(&entries, &graph, &execution_modules);
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
    let mut memo_run = PackageVerificationMemoRun::for_run(
        &options,
        validated,
        lock,
        &graph,
        &entries,
        &artifact_bytes,
        PackageVerificationMode::FastKernel,
    )?;
    let mut session = VerifierSession::new();
    let mut blocked_modules = BTreeSet::<Name>::new();
    let mut results_by_module = BTreeMap::<Name, PackageModuleVerificationResult>::new();
    let mut verified_modules_by_module = BTreeMap::<Name, PackageVerifiedModuleRecord>::new();
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();
    let mut measurement_state = PackageVerifierMeasurementState::new(options.measurement_mode);
    if let Some(measurements) = measurement_state.as_mut() {
        if let Some(observation) = package_fast_execution_cost_observation(
            &entries,
            &graph,
            &execution_modules,
            &execution_layers,
            &artifact_bytes,
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
                blocked_direct_import(&graph, *entry_index, &blocked_modules)
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
                    ),
                );
                blocked_modules.insert(entry.module.clone());
                continue;
            }
            match memo_run.lookup(&entry.module) {
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
                    results_by_module.insert(entry.module.clone(), result);
                    verified_modules_by_module.insert(entry.module.clone(), *record);
                    continue;
                }
                Some(PackageVerificationMemoEntry::Failed { result }) => {
                    blocked_modules.insert(entry.module.clone());
                    results_by_module.insert(entry.module.clone(), result);
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
                graph: &graph,
                verified_modules_by_module: &verified_modules_by_module,
                artifact_bytes: &artifact_bytes,
                session: &session,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
                measurement_mode: options.measurement_mode,
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
                    entry_index: _,
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
                    memo_run.insert(
                        &entry.module,
                        PackageVerificationMemoEntry::FastPassed {
                            result: result.clone(),
                            record: record.clone(),
                        },
                    );
                    results_by_module.insert(entry.module.clone(), result);
                    verified_modules_by_module.insert(entry.module.clone(), *record);
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
    session: &'a VerifierSession,
    policy: &'a AxiomPolicy,
    decode_cache_config: &'a PackageVerificationDecodeCacheConfig,
    measurement_mode: PerformanceMeasurementMode,
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
fn verify_fast_layer_legacy<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
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
struct PackageFastShardMemoryEstimateV1 {
    effective_jobs: usize,
    shared_base_context_bytes: u64,
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
    let context_modules = context
        .verified_modules_by_module
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let Some(plan) = plan_fast_verifier_shards(
        runnable,
        context.graph,
        &context_modules,
        context.verified_modules_by_module,
        context.artifact_bytes,
        jobs,
    ) else {
        return Ok(PackageFastShardedLayerExecution {
            results: verify_fast_layer_independent_serial(
                runnable,
                context.artifact_bytes,
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

fn plan_fast_verifier_shards(
    runnable: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    context_modules: &BTreeSet<Name>,
    verified_modules_by_module: &BTreeMap<Name, PackageVerifiedModuleRecord>,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    jobs: usize,
) -> Option<PackageFastShardPlan> {
    if runnable.is_empty() {
        return Some(PackageFastShardPlan {
            requested_jobs: jobs,
            effective_jobs: 0,
            reduction_reason: PackageFastShardReductionReason::RunnableWidth,
            shared_base_context_bytes: 0,
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
    for record in verified_modules_by_module.values() {
        let bytes = artifact_bytes
            .get(&record.certificate)
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

    let memory = package_fast_shard_memory_estimate_v1(
        jobs,
        runnable.len(),
        shared_base_context_bytes,
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
        per_worker_bytes: memory.per_worker_bytes,
        estimated_total_cost,
        overflowed,
        module_costs,
        shards,
    })
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

fn package_fast_shard_memory_estimate_v1(
    requested_jobs: usize,
    runnable_width: usize,
    shared_base_context_bytes: u64,
    largest_runnable_artifact_bytes: u64,
    prior_overflowed: bool,
) -> PackageFastShardMemoryEstimateV1 {
    let (scratch_bytes, scratch_overflowed) = saturating_mul_u64(
        largest_runnable_artifact_bytes,
        PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1,
    );
    let worker_stack_bytes =
        u64::try_from(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES).unwrap_or(u64::MAX);
    let (stack_and_fixed, fixed_overflowed) =
        saturating_add_u64(worker_stack_bytes, PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1);
    let (per_worker_bytes, worker_overflowed) = saturating_add_u64(stack_and_fixed, scratch_bytes);
    let overflowed =
        prior_overflowed || scratch_overflowed || fixed_overflowed || worker_overflowed;
    let available_for_workers =
        PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1.saturating_sub(shared_base_context_bytes);
    let memory_jobs_u64 = if overflowed {
        1
    } else {
        (available_for_workers / per_worker_bytes.max(1)).max(1)
    };
    let memory_jobs = usize::try_from(memory_jobs_u64).unwrap_or(usize::MAX);
    let requested_jobs = requested_jobs.max(1);
    let runnable_width = runnable_width.max(1);
    let effective_jobs = requested_jobs.min(runnable_width).min(memory_jobs).max(1);
    let memory_limited = shared_base_context_bytes >= PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1
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
    PackageFastShardMemoryEstimateV1 {
        effective_jobs,
        shared_base_context_bytes,
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

fn verify_fast_worker<'a>(
    entry_index: usize,
    entry: &'a PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    import_context: PackageFastWorkerImportContext<'_>,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    observation: PackageFastWorkerObservation,
) -> PackageFastLayerWorkerResult<'a> {
    let checker_started = observation.measurement_mode.is_enabled().then(Instant::now);
    let mut measurement_observation =
        PackageEntryCheckObservation::new(observation.measurement_mode);
    let verification = match import_context {
        PackageFastWorkerImportContext::Session(session) => verify_lock_entry_observed(
            entry_index,
            entry,
            artifact_bytes,
            session,
            policy,
            decode_cache_config,
            &mut measurement_observation,
        ),
        PackageFastWorkerImportContext::Borrowed {
            resolved_imports,
            verified_modules_by_module,
        } => verify_lock_entry_with_context_observed(
            entry_index,
            entry,
            artifact_bytes,
            PackageFastWorkerImportContext::Borrowed {
                resolved_imports,
                verified_modules_by_module,
            },
            policy,
            decode_cache_config,
            &mut measurement_observation,
        ),
    };
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
                result: module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
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
                result: module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
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

fn verify_package_fast_source_free_with_cached_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let live_modules = local_audit_cache_live_modules(&entries, &graph, cache_hits, dirty_modules)?;
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
            ));
            continue;
        }

        if !live_modules.contains(module) {
            locally_accelerated = true;
            results.push(cached_module_result(
                entry,
                PackageVerificationMode::FastKernel,
                cache_evidence,
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
                ));
            }
            Err(error) => {
                failed_module = Some(entry.module.clone());
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Failed,
                    Some(error),
                    PackageVerificationMode::FastKernel,
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
        topological_order: graph.topological_order,
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
    let graph = match input_validation {
        PackageVerificationInputValidationMode::RequireManifestPins => {
            validate_package_lock_against_manifest_graph(validated, lock)
        }
        PackageVerificationInputValidationMode::ObserveLocalArtifacts => {
            validate_observed_package_lock_against_manifest_graph(validated, lock)
        }
    }
    .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let execution_modules = execution_modules_for_options(&entries, &graph, &options)?;
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
    let mut memo_run = PackageVerificationMemoRun::for_run(
        &options,
        validated,
        lock,
        &graph,
        &entries,
        &artifact_bytes,
        PackageVerificationMode::Reference,
    )?;
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses =
        reference_import_use_counts(&entries, &graph, &execution_modules);
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
            ));
            continue;
        }

        match memo_run.lookup(&entry.module) {
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
                    *checked,
                );
                retire_reference_imports_after_module(
                    *entry_index,
                    &graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(result);
                continue;
            }
            Some(PackageVerificationMemoEntry::Failed { result }) => {
                failed_module = Some(entry.module.clone());
                checked_by_module.clear();
                remaining_import_uses.clear();
                results.push(result);
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
        if let Some(failed) = &failed_module {
            results.push(module_result(
                entry,
                PackageModuleVerificationStatus::Skipped,
                Some(PackageVerificationError::earlier_module_failed(
                    format!("entries[{entry_index}].module"),
                    failed.as_dotted(),
                )),
                PackageVerificationMode::Reference,
            ));
            continue;
        }

        let bytes = match read_certificate_artifact_from_root(package_root, *entry_index, entry) {
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

fn verify_package_reference_source_free_with_cached_hits<'a>(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    artifacts: impl IntoIterator<Item = PackageCertificateArtifact<'a>>,
    cache_hits: impl IntoIterator<Item = Name>,
    cache_evidence: PackageModuleVerificationEvidence,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<PackageVerificationReport> {
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
        .map_err(|error| PackageVerificationError::lock_graph_invalid(format!("{error:?}")))?;
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let entries = canonical_lock_entries(lock);
    let entries_by_module = entries
        .iter()
        .map(|(index, entry)| (entry.module.clone(), (*index, *entry)))
        .collect::<BTreeMap<_, _>>();
    let live_modules = local_audit_cache_live_modules(&entries, &graph, cache_hits, dirty_modules)?;
    let policy = package_reference_checker_policy(validated);
    let decode_cache_config = PackageVerificationDecodeCacheConfig::for_mode(
        validated,
        PackageVerificationMode::Reference,
    );
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses = reference_import_use_counts(&entries, &graph, &live_modules);
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
            ));
            continue;
        }

        if !live_modules.contains(module) {
            locally_accelerated = true;
            results.push(cached_module_result(
                entry,
                PackageVerificationMode::Reference,
                cache_evidence,
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
                    &graph,
                    &mut checked_by_module,
                    &mut remaining_import_uses,
                );
                results.push(module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::Reference,
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
        topological_order: graph.topological_order,
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
}

impl PackageEntryCheckObservation {
    fn new(measurement_mode: PerformanceMeasurementMode) -> Self {
        Self {
            measurement_mode,
            ..Self::default()
        }
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
            &certificate.name_table,
            &certificate.term_table,
            &certificate.declarations,
        );
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

#[derive(Clone)]
struct PackageFastCriticalPathState {
    cost: u64,
    modules: Vec<Name>,
    overflowed: bool,
}

fn package_fast_execution_cost_observation(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    execution_modules: &BTreeSet<Name>,
    execution_layers: &[Vec<Name>],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
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
    let mut paths = BTreeMap::<Name, PackageFastCriticalPathState>::new();
    let mut overflowed = false;
    for module in graph
        .topological_order
        .iter()
        .filter(|module| execution_modules.contains(*module))
    {
        let (entry_index, entry) = entries_by_module.get(module).copied()?;
        let bytes = artifact_bytes.get(&entry.certificate).copied()?;
        let artifact_bytes = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
        let direct_import_count =
            u64::try_from(graph.resolved_entry_imports[entry_index].len()).unwrap_or(u64::MAX);
        let estimate = package_module_cost_estimate_v1(artifact_bytes, direct_import_count);
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
            .unwrap_or(PackageFastCriticalPathState {
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
        .unwrap_or(PackageFastCriticalPathState {
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
}

impl PackageVerifierMeasurementState {
    fn new(mode: PerformanceMeasurementMode) -> Option<Self> {
        mode.is_enabled().then(|| Self {
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
        })
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
            memory_model: PerformancePackageShardMemoryModel::FastShardMemoryV1,
            import_weight: PACKAGE_FAST_SHARD_IMPORT_WEIGHT_V1,
            memory_budget_bytes: PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
            fixed_worker_bytes: PACKAGE_FAST_SHARD_FIXED_WORKER_BYTES_V1,
            scratch_multiplier: PACKAGE_FAST_SHARD_SCRATCH_MULTIPLIER_V1,
            requested_jobs: u64::try_from(requested_jobs).unwrap_or(u64::MAX),
            effective_jobs: 0,
            reduction_reason: PerformancePackageShardReductionReason::None,
            shared_base_context_bytes: 0,
            per_worker_bytes: 0,
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
                    per_worker_bytes: plan.per_worker_bytes,
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
            TermNode::Let { ty, value, body } => {
                pending.push(*ty);
                pending.push(*value);
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

fn read_certificate_artifact_from_root(
    package_root: &Path,
    entry_index: usize,
    entry: &PackageLockEntry,
) -> PackageVerificationResult<Vec<u8>> {
    fs::read(package_root.join(entry.certificate.as_str())).map_err(|_| {
        PackageVerificationError::certificate_artifact_missing(
            format!("entries[{entry_index}].certificate"),
            entry.certificate.as_str(),
        )
    })
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

fn package_verification_process_memo() -> &'static Mutex<PackageVerificationProcessMemo> {
    PACKAGE_VERIFICATION_PROCESS_MEMO
        .get_or_init(|| Mutex::new(PackageVerificationProcessMemo::default()))
}

fn package_verification_decode_cache() -> &'static Mutex<PackageVerificationDecodeCache> {
    PACKAGE_VERIFICATION_DECODE_CACHE
        .get_or_init(|| Mutex::new(PackageVerificationDecodeCache::default()))
}

#[derive(Clone, Debug)]
struct PackageVerificationDecodeCacheConfig {
    checker_mode: PackageVerificationMode,
    certificate_format: String,
    core_spec: String,
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
            certificate_format: manifest.certificate_format.clone(),
            core_spec: manifest.core_spec.clone(),
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
        let cert = decode_module_cert(bytes).map_err(|source| {
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

    let key = package_decode_cache_certificate_key(entry, actual_file_hash, config);
    if let Some(cert) = package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned")
        .fast_certificates
        .get(&key)
        .cloned()
    {
        observation.decode_cache_counters.certificate_hits = observation
            .decode_cache_counters
            .certificate_hits
            .saturating_add(1);
        return Ok(cert);
    }

    observation.decode_cache_counters.certificate_misses = observation
        .decode_cache_counters
        .certificate_misses
        .saturating_add(1);
    let cert = decode_module_cert(bytes).map_err(|source| {
        PackageVerificationError::certificate_decode_failed(
            format!("entries[{entry_index}].certificate"),
            format!("{source:?}"),
        )
    })?;
    if observation.measurement_mode.is_enabled() {
        observation.physical_certificate_decodes =
            observation.physical_certificate_decodes.saturating_add(1);
    }
    package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned")
        .fast_certificates
        .insert(key, cert.clone());
    observation.decode_cache_counters.certificate_inserted = observation
        .decode_cache_counters
        .certificate_inserted
        .saturating_add(1);
    Ok(cert)
}

#[cfg(test)]
fn reference_import_store_with_cache(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<PackageDecodeCacheLookup<ReferenceImportStore>> {
    let mut counters = PackageVerificationDecodeCacheCounters::default();
    let value = reference_import_store_with_cache_observed(
        entry_index,
        entry,
        resolved_imports,
        PackageReferenceImportContext {
            lock,
            entries,
            checked_by_module,
            config,
        },
        &mut counters,
    )?;
    Ok(PackageDecodeCacheLookup { value, counters })
}

fn reference_import_store_with_cache_observed(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    context: PackageReferenceImportContext<'_>,
    counters: &mut PackageVerificationDecodeCacheCounters,
) -> PackageVerificationResult<ReferenceImportStore> {
    let PackageReferenceImportContext {
        lock,
        entries,
        checked_by_module,
        config,
    } = context;
    let key = config
        .process_local_cache
        .then(|| package_decode_cache_import_context_key(resolved_imports, config));
    if let Some(key) = &key {
        if let Some(imports) = package_verification_decode_cache()
            .lock()
            .expect("package verification decode cache mutex should not be poisoned")
            .reference_import_contexts
            .get(key)
            .cloned()
        {
            counters.import_context_hits = counters.import_context_hits.saturating_add(1);
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
            config,
        )?;
        let disk_cache_dir = package_import_context_export_cache_dir();
        match read_import_context_export_cache_lookup(&disk_cache_dir, entry, &expected_disk_entry)
        {
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
                    Some((disk_cache_dir, expected_disk_entry));
            }
            ImportContextExportCacheLookup::Stale => {
                counters.import_context_disk_stale =
                    counters.import_context_disk_stale.saturating_add(1);
                pending_import_context_export_cache_write =
                    Some((disk_cache_dir, expected_disk_entry));
            }
            ImportContextExportCacheLookup::SchemaMiss => {
                counters.import_context_disk_schema_misses =
                    counters.import_context_disk_schema_misses.saturating_add(1);
                pending_import_context_export_cache_write =
                    Some((disk_cache_dir, expected_disk_entry));
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
    if let Some((disk_cache_dir, expected_disk_entry)) = pending_import_context_export_cache_write {
        if write_import_context_export_cache_entry(&disk_cache_dir, entry, &expected_disk_entry) {
            counters.import_context_disk_inserted =
                counters.import_context_disk_inserted.saturating_add(1);
        }
    }
    if let Some(key) = key {
        package_verification_decode_cache()
            .lock()
            .expect("package verification decode cache mutex should not be poisoned")
            .reference_import_contexts
            .insert(key, imports.clone());
        counters.import_context_inserted = counters.import_context_inserted.saturating_add(1);
    }
    Ok(imports)
}

enum ImportContextExportCacheLookup {
    Hit,
    Missing,
    Stale,
    SchemaMiss,
}

fn import_context_export_cache_entry_for_context(
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
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
            Ok(PackageImportContextExportData {
                module: dependency.module.clone(),
                origin: dependency.origin,
                package: dependency.package.clone(),
                version: dependency.version.clone(),
                export_hash: dependency.export_hash,
                certificate_hash: dependency.certificate_hash,
                axiom_report_hash: dependency.axiom_report_hash,
                certificate_format: config.certificate_format.clone(),
            })
        })
        .collect::<PackageVerificationResult<Vec<_>>>()?;
    let key_input = PackageImportContextExportCacheKeyInput {
        schema: PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA.to_owned(),
        package_id: lock.package.clone(),
        package_version: lock.version.clone(),
        package_lock_schema: lock.schema.clone(),
        core_spec: config.core_spec.clone(),
        certificate_format: config.certificate_format.clone(),
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
    cache_dir: &Path,
    entry: &PackageLockEntry,
    expected: &PackageImportContextExportCacheEntry,
) -> ImportContextExportCacheLookup {
    let path = import_context_export_cache_entry_path(cache_dir, entry, &expected.key_input);
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
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
    cache_dir: &Path,
    owner: &PackageLockEntry,
    entry: &PackageImportContextExportCacheEntry,
) -> bool {
    if fs::create_dir_all(cache_dir).is_err() {
        return false;
    }
    let path = import_context_export_cache_entry_path(cache_dir, owner, &entry.key_input);
    let temp_index = NEXT_IMPORT_CONTEXT_EXPORT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
    let temp_path = cache_dir.join(format!(
        "{}.{}.{}.tmp",
        import_context_export_cache_slot_key(owner, &entry.key_input),
        std::process::id(),
        temp_index
    ));
    if fs::write(
        &temp_path,
        package_import_context_export_cache_entry_json(entry),
    )
    .is_err()
    {
        let _ = fs::remove_file(&temp_path);
        return false;
    }
    match fs::rename(&temp_path, path) {
        Ok(()) => true,
        Err(_) => {
            let _ = fs::remove_file(&temp_path);
            false
        }
    }
}

fn package_import_context_export_cache_dir() -> PathBuf {
    std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."))
        .join(PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR)
}

fn import_context_export_cache_entry_path(
    cache_dir: &Path,
    owner: &PackageLockEntry,
    input: &PackageImportContextExportCacheKeyInput,
) -> PathBuf {
    cache_dir.join(format!(
        "{}.json",
        import_context_export_cache_slot_key(owner, input)
    ))
}

fn import_context_export_cache_slot_key(
    owner: &PackageLockEntry,
    input: &PackageImportContextExportCacheKeyInput,
) -> String {
    let material = format!(
        "schema=npa.package.import_context_export_cache_slot.v0.1\npackage_id={}\npackage_version={}\npackage_lock_schema={}\ncore_spec={}\ncertificate_format={}\nchecker_policy_hash={}\nowner_module={}\n",
        input.package_id.as_str(),
        input.package_version.as_str(),
        input.package_lock_schema,
        input.core_spec,
        input.certificate_format,
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
    config: &PackageVerificationDecodeCacheConfig,
) -> String {
    let mut material = format!(
        "schema=npa.package.decode_cache.certificate.v0.1\nmode={}\ncertificate_format={}\ncore_spec={}\ncertificate_file_hash={}\ncertificate_hash={}\nenabled_core_features={}\n",
        config.checker_mode.as_str(),
        config.certificate_format,
        config.core_spec,
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
    config: &PackageVerificationDecodeCacheConfig,
) -> String {
    let mut material = format!(
        "schema=npa.package.decode_cache.import_context.v0.1\nmode={}\nchecker_policy_hash={}\ndirect_imports={}\n",
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
        material.push('\n');
    }
    format_package_hash(&package_file_hash(material.as_bytes()))
}

struct PackageVerificationMemoRun {
    mode: PackageVerificationMemoMode,
    keys_by_module: BTreeMap<Name, String>,
    counters: PackageVerificationMemoCounters,
}

impl PackageVerificationMemoRun {
    fn disabled() -> Self {
        Self {
            mode: PackageVerificationMemoMode::Disabled,
            keys_by_module: BTreeMap::new(),
            counters: PackageVerificationMemoCounters::default(),
        }
    }

    fn for_run(
        options: &PackageVerificationExecutionOptions,
        validated: &ValidatedPackageManifest,
        lock: &PackageLockManifest,
        graph: &PackageLockGraph,
        entries: &[(usize, &PackageLockEntry)],
        artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
        mode: PackageVerificationMode,
    ) -> PackageVerificationResult<Self> {
        if !options.memoization.is_enabled() {
            return Ok(Self::disabled());
        }
        Ok(Self {
            mode: options.memoization,
            keys_by_module: package_verification_memo_keys(
                validated,
                lock,
                graph,
                entries,
                artifact_bytes,
                mode,
            )?,
            counters: PackageVerificationMemoCounters::default(),
        })
    }

    fn lookup(&mut self, module: &Name) -> Option<PackageVerificationMemoEntry> {
        if !self.mode.is_enabled() {
            return None;
        }
        let key = self.keys_by_module.get(module)?;
        let hit = package_verification_process_memo()
            .lock()
            .expect("package verification process memo mutex should not be poisoned")
            .entries
            .get(key)
            .cloned();
        if hit.is_some() {
            self.counters.hits = self.counters.hits.saturating_add(1);
        } else {
            self.counters.misses = self.counters.misses.saturating_add(1);
        }
        hit
    }

    fn insert(&mut self, module: &Name, entry: PackageVerificationMemoEntry) {
        if !self.mode.is_enabled() {
            return;
        }
        let Some(key) = self.keys_by_module.get(module).cloned() else {
            return;
        };
        package_verification_process_memo()
            .lock()
            .expect("package verification process memo mutex should not be poisoned")
            .entries
            .insert(key, entry);
        self.counters.inserted = self.counters.inserted.saturating_add(1);
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
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, String>> {
    let inputs = package_verification_memo_key_inputs_for_entries(
        validated,
        lock,
        graph,
        entries,
        artifact_bytes,
        mode,
    )?;
    Ok(inputs
        .into_iter()
        .map(|(module, input)| (module, package_audit_process_memo_key(&input)))
        .collect())
}

fn package_verification_memo_key_inputs_for_entries(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
    entries: &[(usize, &PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mode: PackageVerificationMode,
) -> PackageVerificationResult<BTreeMap<Name, PackageAuditCacheKeyInput>> {
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
        let Some(bytes) = artifact_bytes.get(&entry.certificate).copied() else {
            continue;
        };
        let key_input = PackageAuditCacheKeyInput {
            schema: PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA.to_owned(),
            package_id: lock.package.clone(),
            package_version: lock.version.clone(),
            package_lock_schema: lock.schema.clone(),
            core_spec: manifest.core_spec.clone(),
            certificate_format: manifest.certificate_format.clone(),
            package_lock_hash,
            package_policy_hash,
            checker: checker.clone(),
            module: entry.module.clone(),
            origin: entry.origin,
            certificate: entry.certificate.clone(),
            certificate_file_hash: package_file_hash(bytes),
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
        inputs.insert(entry.module.clone(), key_input);
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
        "schema=npa.package.reference_verification_axiom_policy.v0.1\nmode={}\ntrust_mode={trust_mode}\ndeny_sorry={}\ndeny_custom_axioms={}\nallowed_axioms={}\nenabled_core_features={}\n",
        mode.as_str(),
        policy.deny_sorry,
        policy.deny_custom_axioms,
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

fn execution_layers_for_modules(
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
    let entry_path = format!("entries[{entry_index}]");
    observation.observe_certificate_bytes(bytes);
    let actual_file_hash = package_file_hash(bytes);
    if entry.certificate_file_hash != actual_file_hash {
        return Err(PackageVerificationError::certificate_file_hash_mismatch(
            format!("{entry_path}.certificate_file_hash"),
            entry.certificate_file_hash,
            actual_file_hash,
        ));
    }

    let decoded = decode_fast_certificate_with_cache(
        entry_index,
        entry,
        bytes,
        actual_file_hash,
        decode_cache_config,
        observation,
    )?;
    let cert = decoded;
    observation.observe_fast_certificate(&entry.module, &cert);
    if cert.header.module != entry.module {
        return Err(PackageVerificationError::certificate_module_mismatch(
            format!("{entry_path}.certificate"),
            entry.module.as_dotted(),
            cert.header.module.as_dotted(),
        ));
    }
    check_entry_hashes(entry_index, entry, &cert)?;

    let verified = match import_context {
        PackageFastWorkerImportContext::Session(session) => {
            verify_decoded_module_cert(&cert, bytes, session, policy)
        }
        PackageFastWorkerImportContext::Borrowed {
            resolved_imports,
            verified_modules_by_module,
        } => {
            let imports = exact_fast_import_refs(resolved_imports, verified_modules_by_module);
            verify_decoded_module_cert_with_import_refs(&cert, bytes, &imports, policy)
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
    context: PackageReferenceEntryBytesContext<'_>,
    observation: &mut PackageEntryCheckObservation,
) -> PackageVerificationResult<ReferenceCheckedModule> {
    let entry_path = format!("entries[{entry_index}]");
    observation.observe_certificate_bytes(bytes);
    let actual_file_hash = package_file_hash(bytes);
    if entry.certificate_file_hash != actual_file_hash {
        return Err(PackageVerificationError::certificate_file_hash_mismatch(
            format!("{entry_path}.certificate_file_hash"),
            entry.certificate_file_hash,
            actual_file_hash,
        ));
    }

    let imports = reference_import_store_with_cache_observed(
        entry_index,
        entry,
        resolved_imports,
        PackageReferenceImportContext {
            lock: context.lock,
            entries: context.entries,
            checked_by_module: context.checked_by_module,
            config: context.decode_cache_config,
        },
        &mut observation.decode_cache_counters,
    )?;
    let check_result = if observation.measurement_mode.is_enabled() {
        let declaration_detail_limit = if observation.measurement_mode.is_detailed() {
            PERFORMANCE_DECLARATION_DETAIL_LIMIT
        } else {
            0
        };
        let (result, check_observation) = check_certificate_with_observation(
            bytes,
            &imports,
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
        check_certificate(bytes, &imports, context.policy)
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
    let entry_path = format!("entries[{entry_index}]");
    let actual_export_hash = PackageHash::from(cert.hashes.export_hash);
    if entry.export_hash != actual_export_hash {
        return Err(PackageVerificationError::export_hash_mismatch(
            format!("{entry_path}.export_hash"),
            entry.export_hash,
            actual_export_hash,
        ));
    }
    let actual_axiom_report_hash = PackageHash::from(cert.hashes.axiom_report_hash);
    if entry.axiom_report_hash != actual_axiom_report_hash {
        return Err(PackageVerificationError::axiom_report_hash_mismatch(
            format!("{entry_path}.axiom_report_hash"),
            entry.axiom_report_hash,
            actual_axiom_report_hash,
        ));
    }
    let actual_certificate_hash = PackageHash::from(cert.hashes.certificate_hash);
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
) -> PackageModuleVerificationResult {
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status,
        evidence: PackageModuleVerificationEvidence::LiveChecker,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        error,
    }
}

fn cached_module_result(
    entry: &PackageLockEntry,
    checker_mode: PackageVerificationMode,
    evidence: PackageModuleVerificationEvidence,
) -> PackageModuleVerificationResult {
    PackageModuleVerificationResult {
        module: entry.module.clone(),
        checker_mode,
        status: PackageModuleVerificationStatus::Passed,
        evidence,
        export_hash: entry.export_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate_hash: entry.certificate_hash,
        error: None,
    }
}

fn local_audit_cache_live_modules(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    local_cache_hits: impl IntoIterator<Item = Name>,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageVerificationResult<BTreeSet<Name>> {
    let local_cache_hits = local_cache_hits.into_iter().collect::<BTreeSet<_>>();
    let known_modules = entries
        .iter()
        .map(|(_, entry)| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let dirty_modules = dirty_modules.into_iter().collect::<BTreeSet<_>>();
    for module in &dirty_modules {
        if !known_modules.contains(module) {
            return Err(PackageVerificationError::selected_module_missing(module));
        }
    }
    let mut live_modules = entries
        .iter()
        .filter(|(_, entry)| !local_cache_hits.contains(&entry.module))
        .map(|(_, entry)| entry.module.clone())
        .collect::<BTreeSet<_>>();
    live_modules.extend(dirty_modules.iter().cloned());
    let reverse = package_lock_reverse_dependencies_from_graph(entries, graph);
    for dirty in &dirty_modules {
        live_modules.extend(reverse_dependency_closure(&reverse, dirty));
    }

    loop {
        let mut changed = false;
        for (entry_index, entry) in entries {
            if !live_modules.contains(&entry.module) {
                continue;
            }
            for import in &graph.resolved_entry_imports[*entry_index] {
                changed |= live_modules.insert(import.module.clone());
            }
        }
        if !changed {
            return Ok(live_modules);
        }
    }
}

fn package_lock_reverse_dependencies_from_graph(
    entries: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
) -> BTreeMap<Name, Vec<Name>> {
    let order = graph
        .topological_order
        .iter()
        .enumerate()
        .map(|(index, module)| (module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut reverse = entries
        .iter()
        .map(|(_, entry)| (entry.module.clone(), Vec::<Name>::new()))
        .collect::<BTreeMap<_, _>>();
    for (entry_index, entry) in entries {
        for import in &graph.resolved_entry_imports[*entry_index] {
            reverse
                .entry(import.module.clone())
                .or_default()
                .push(entry.module.clone());
        }
    }
    for dependents in reverse.values_mut() {
        dependents.sort_by_key(|module| order.get(module).copied().unwrap_or(usize::MAX));
        dependents.dedup();
    }
    reverse
}

fn reverse_dependency_closure(
    reverse: &BTreeMap<Name, Vec<Name>>,
    module: &Name,
) -> BTreeSet<Name> {
    let mut closure = BTreeSet::<Name>::new();
    let mut stack = reverse.get(module).cloned().unwrap_or_default();
    while let Some(dependent) = stack.pop() {
        if !closure.insert(dependent.clone()) {
            continue;
        }
        if let Some(next) = reverse.get(&dependent) {
            stack.extend(next.iter().cloned());
        }
    }
    closure
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
        build_package_lock_from_artifacts, package_audit_disk_memo_key,
        package_audit_disk_memo_key_input, package_audit_process_memo_key,
        package_reference_summary_cache_key, package_reference_summary_cache_key_input,
        parse_manifest_str, parse_package_lock_json, validate_manifest, PackageId,
        PackageLockArtifact, PackageLockManifest, PackageManifest, PackageModule, PackagePath,
        PackagePolicy, PackageVersion, ValidatedPackageManifest, CERTIFICATE_FORMAT_CANONICAL_V0_1,
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

    fn recompute_unchecked_import_module_hash(cert: &mut ModuleCert) {
        let encoded = encode_module_cert(cert).unwrap();
        let payload = &encoded[..encoded.len() - 32];
        cert.hashes.certificate_hash =
            unchecked_import_hash_with_domain(b"NPA-MODULE-CERT-0.2.0", payload);
    }

    fn semantically_invalid_unchecked_import_provider(mut cert: ModuleCert) -> ModuleCert {
        let bvar_zero = cert
            .term_table
            .iter()
            .position(|term| matches!(term, TermNode::BVar(0)))
            .expect("identity certificate contains bvar 0");
        let bvar_one = cert
            .term_table
            .iter()
            .position(|term| matches!(term, TermNode::BVar(1)))
            .expect("identity certificate contains bvar 1");
        let inner_lambda = cert
            .term_table
            .iter()
            .position(|term| {
                matches!(
                    term,
                    TermNode::Lam { ty, body } if *ty == bvar_zero && *body == bvar_zero
                )
            })
            .expect("identity certificate contains its inner lambda");
        match &mut cert.term_table[inner_lambda] {
            TermNode::Lam { body, .. } => *body = bvar_one,
            term => panic!("expected inner identity lambda, got {term:?}"),
        }
        let proof = match cert.declarations[0].decl {
            DeclPayload::Theorem { proof, .. } => proof,
            ref decl => panic!("expected identity theorem, got {decl:?}"),
        };
        let mut payload = Vec::new();
        payload.extend(cert.declarations[0].hashes.decl_interface_hash);
        payload.extend(term_hash(&cert, proof).unwrap());
        payload.push(0); // Empty dependency vector.
        cert.declarations[0].hashes.decl_certificate_hash =
            unchecked_import_hash_with_domain(b"NPA-DECL-CERT-0.1", &payload);
        recompute_unchecked_import_module_hash(&mut cert);
        cert
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
            expected_export_hash: PackageHash::new(cert.hashes.export_hash),
            expected_axiom_report_hash: PackageHash::new(cert.hashes.axiom_report_hash),
            expected_certificate_hash: PackageHash::new(cert.hashes.certificate_hash),
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

    fn process_memo_test_lock() -> MutexGuard<'static, ()> {
        static LOCK: Mutex<()> = Mutex::new(());
        LOCK.lock().unwrap()
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
    }

    #[test]
    fn package_fast_verifier_rejects_missing_certificate_artifact() {
        let validated = validated_proof_manifest();
        let lock = proof_lock();
        let artifacts = BTreeMap::new();

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
            PackageVerificationErrorReason::CertificateArtifactMissing
        );
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
    fn package_fast_cost_and_memory_models_saturate_and_cap_jobs_deterministically() {
        let ordinary = package_module_cost_estimate_v1(10, 2);
        assert_eq!(ordinary.artifact_bytes, 10);
        assert_eq!(ordinary.direct_import_count, 2);
        assert_eq!(ordinary.estimated_cost, 10 + 2 * 4_096);
        assert!(!ordinary.overflowed);

        let overflowed = package_module_cost_estimate_v1(u64::MAX, u64::MAX);
        assert_eq!(overflowed.estimated_cost, u64::MAX);
        assert!(overflowed.overflowed);

        let width_limited = package_fast_shard_memory_estimate_v1(8, 3, 0, 1, false);
        assert_eq!(width_limited.effective_jobs, 3);
        assert_eq!(
            width_limited.reduction_reason,
            PackageFastShardReductionReason::RunnableWidth
        );

        let memory_limited = package_fast_shard_memory_estimate_v1(16, 16, 0, 1, false);
        assert!(memory_limited.effective_jobs < 16);
        assert_eq!(
            memory_limited.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let context_over_budget = package_fast_shard_memory_estimate_v1(
            4,
            4,
            PACKAGE_FAST_SHARD_MEMORY_BUDGET_BYTES_V1,
            1,
            false,
        );
        assert_eq!(context_over_budget.effective_jobs, 1);
        assert_eq!(
            context_over_budget.reduction_reason,
            PackageFastShardReductionReason::MemoryBudget
        );

        let estimate_overflow = package_fast_shard_memory_estimate_v1(4, 4, 0, u64::MAX, false);
        assert_eq!(estimate_overflow.effective_jobs, 1);
        assert_eq!(
            estimate_overflow.reduction_reason,
            PackageFastShardReductionReason::EstimateOverflow
        );
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
            PerformancePackageShardMemoryModel::FastShardMemoryV1
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
        let _guard = process_memo_test_lock();
        clear_package_verification_process_memo();
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
            }
        );
        assert_eq!(
            second.memo_counters,
            PackageVerificationMemoCounters {
                hits: 1,
                misses: 0,
                inserted: 0,
            }
        );
        assert_eq!(package_verification_process_memo_entry_count(), 1);
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
    fn package_verifier_memo_keeps_fast_and_reference_namespaces_separate() {
        let _guard = process_memo_test_lock();
        clear_package_verification_process_memo();
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
            package_verification_process_memo_entry_count(),
            fast_verified_count + reference_verified_count
        );
        assert_eq!(reference.status, PackageVerificationStatus::Passed);
    }

    #[test]
    fn package_verifier_memo_failure_hit_still_skips_dependent_deterministically() {
        let _guard = process_memo_test_lock();
        clear_package_verification_process_memo();
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
                memoization: PackageVerificationMemoMode::ProcessLocal,
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
        let changed_input = changed_inputs
            .get(&Name::from_dotted("Proofs.Ai.Basic"))
            .expect("proof fixture contains Proofs.Ai.Basic");
        assert_ne!(disk_key, package_audit_disk_memo_key(changed_input));
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
        let first = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &checked_by_module,
            &config,
        )
        .unwrap();
        let second = reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &checked_by_module,
            &config,
        )
        .unwrap();
        let unverified_hit = match reference_import_store_with_cache(
            *target_index,
            target_entry,
            direct_imports,
            &lock,
            &entries,
            &BTreeMap::new(),
            &config,
        ) {
            Ok(_) => panic!("cached import context hit must require verified imports in this run"),
            Err(error) => error,
        };
        let mut reordered_imports = direct_imports.to_vec();
        reordered_imports.swap(0, 1);
        let changed = reference_import_store_with_cache(
            *target_index,
            target_entry,
            &reordered_imports,
            &lock,
            &entries,
            &checked_by_module,
            &config,
        )
        .unwrap();

        assert_eq!(
            first.counters.import_context_hits + first.counters.import_context_misses,
            1
        );
        assert_eq!(
            first.counters.import_context_inserted,
            first.counters.import_context_misses
        );
        assert_eq!(second.counters.import_context_hits, 1);
        assert_eq!(
            unverified_hit.reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
        assert_eq!(changed.counters.import_context_misses, 1);
    }

    #[test]
    fn package_import_context_export_cache_reuses_disk_entry_without_changing_report() {
        let _guard = decode_cache_test_lock();
        clear_package_verification_process_memo();
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
        let policy = package_reference_checker_policy(&validated);
        let mut config = PackageVerificationDecodeCacheConfig::for_mode(
            &validated,
            PackageVerificationMode::Reference,
        )
        .with_persistent_import_context_export_cache(true);
        config.checker_policy_hash = PackageHash::new(test_hash(0xd1));
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
        let failed = reference_import_store_with_cache_observed(
            *target_index,
            target_entry,
            direct_imports,
            PackageReferenceImportContext {
                lock: &lock,
                entries: &entries,
                checked_by_module: &BTreeMap::new(),
                config: &config,
            },
            &mut failed_counters,
        )
        .expect_err("disk hit still requires verified imports in this run");
        assert_eq!(
            failed.reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
        assert_eq!(failed_counters.import_context_disk_hits, 1);
    }

    #[test]
    fn package_import_context_export_cache_reports_stale_dependency_identity() {
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
        let policy = package_reference_checker_policy(&validated);
        let config = PackageVerificationDecodeCacheConfig::for_mode(
            &validated,
            PackageVerificationMode::Reference,
        )
        .with_persistent_import_context_export_cache(true);
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
            &config,
        )
        .unwrap();

        assert_eq!(stale.counters.import_context_disk_hits, 0);
        assert_eq!(stale.counters.import_context_disk_stale, 1);
        assert_eq!(stale.counters.import_context_disk_inserted, 1);
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
        let mut leaf =
            build_module_cert(unchecked_import_consumer(), &[verified_provider]).unwrap();
        leaf.imports[0].certificate_hash = Some(bad_provider.hashes.certificate_hash);
        recompute_unchecked_import_module_hash(&mut leaf);
        let leaf_bytes = encode_module_cert(&leaf).unwrap();

        assert_eq!(
            good_provider.hashes.export_hash,
            bad_provider.hashes.export_hash
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
    fn package_reference_dag_rejects_inductive_universe_violation_before_leaf() {
        let provider_bytes = read(repo_root().join(
            "testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert",
        ));
        let provider = decode_module_cert(&provider_bytes).unwrap();
        let mut leaf = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Audit.Leaf"),
                declarations: Vec::new(),
            },
            &[],
        )
        .unwrap();
        leaf.imports.push(npa_cert::ImportEntry {
            module: provider.header.module.clone(),
            export_hash: provider.hashes.export_hash,
            certificate_hash: Some(provider.hashes.certificate_hash),
        });
        recompute_unchecked_import_module_hash(&mut leaf);
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
                unchecked_import_package_module(
                    "Audit.Universe",
                    "Audit/Universe/source.npa",
                    provider_path.as_str(),
                    Vec::new(),
                    &provider,
                    &provider_bytes,
                ),
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
        let lock = build_package_lock_from_artifacts(
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
        .unwrap();
        let artifacts = BTreeMap::from([(provider_path, provider_bytes), (leaf_path, leaf_bytes)]);

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
            .find(|result| result.module.as_dotted() == "Audit.Universe")
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
        assert_eq!(
            checker_error.reason_code.as_deref(),
            Some("constructor_universe_bound_violation")
        );

        let leaf_result = report
            .modules
            .iter()
            .find(|result| result.module.as_dotted() == "Audit.Leaf")
            .unwrap();
        assert_eq!(leaf_result.status, PackageModuleVerificationStatus::Skipped);
        assert_eq!(
            leaf_result.error.as_ref().unwrap().reason_code,
            PackageVerificationErrorReason::EarlierModuleFailed
        );
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
}

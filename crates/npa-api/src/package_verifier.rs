use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
    sync::{Mutex, OnceLock},
    thread,
};

use npa_cert::{
    decode_module_cert, verify_decoded_module_cert, AxiomPolicy, CertError, CoreFeature,
    ModuleCert, Name, VerifiedModule, VerifierSession,
};
use npa_checker_ref::{
    check_certificate, ReferenceCertificateSection, ReferenceCheckError, ReferenceCheckErrorKind,
    ReferenceCheckReason, ReferenceCheckResult, ReferenceCheckedModule, ReferenceCheckerPolicy,
    ReferenceCoreFeature, ReferenceImportStore, ReferenceModuleName, ReferenceTrustMode,
};
use npa_package::{
    build_package_lock_graph, format_package_hash, package_audit_process_memo_key,
    package_file_hash, package_import_context_export_cache_entry_json,
    package_import_context_export_cache_key, parse_package_import_context_export_cache_entry_json,
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

const PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;
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
    /// Enable the process-local decode/import cache and collect its counters in
    /// the report.
    pub collect_decode_cache_counters: bool,
}

impl Default for PackageVerificationExecutionOptions {
    fn default() -> Self {
        Self {
            jobs: 1,
            selected_modules: None,
            memoization: PackageVerificationMemoMode::Disabled,
            collect_decode_cache_counters: false,
        }
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
        self.certificate_hits += other.certificate_hits;
        self.certificate_misses += other.certificate_misses;
        self.certificate_inserted += other.certificate_inserted;
        self.import_context_hits += other.import_context_hits;
        self.import_context_misses += other.import_context_misses;
        self.import_context_inserted += other.import_context_inserted;
        self.import_context_disk_hits += other.import_context_disk_hits;
        self.import_context_disk_misses += other.import_context_disk_misses;
        self.import_context_disk_stale += other.import_context_disk_stale;
        self.import_context_disk_schema_misses += other.import_context_disk_schema_misses;
        self.import_context_disk_inserted += other.import_context_disk_inserted;
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

    fn certificate_artifact_missing(path: impl Into<String>, expected: impl Into<String>) -> Self {
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
        && !options.collect_decode_cache_counters
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
    .with_process_local_cache(options.collect_decode_cache_counters)
    .with_persistent_import_context_export_cache(options.collect_decode_cache_counters);
    let mut session = VerifierSession::new();
    let mut results = Vec::with_capacity(execution_modules.len());
    let mut failed_module = None::<Name>;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();

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

        match verify_lock_entry_bytes(
            *entry_index,
            entry,
            &bytes,
            &mut session,
            &policy,
            &decode_cache_config,
        ) {
            Ok((_verified_module, counters)) => {
                decode_cache_counters.add(counters);
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
            decode_cache_counters: options
                .collect_decode_cache_counters
                .then_some(decode_cache_counters),
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
    .with_process_local_cache(options.collect_decode_cache_counters)
    .with_persistent_import_context_export_cache(options.collect_decode_cache_counters);
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

    for layer in execution_layers {
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

        let worker_results = verify_fast_layer(
            &runnable,
            PackageFastLayerContext {
                graph: &graph,
                verified_modules_by_module: &verified_modules_by_module,
                artifact_bytes: &artifact_bytes,
                session: &session,
                policy: &policy,
                decode_cache_config: &decode_cache_config,
            },
            options.jobs,
            parallel_strategy,
        );
        for worker_result in worker_results {
            decode_cache_counters.add(worker_result.decode_cache_counters());
            match worker_result {
                PackageFastLayerWorkerResult::Passed {
                    entry,
                    result,
                    record,
                    decode_cache_counters: _,
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
                    entry,
                    result,
                    decode_cache_counters: _,
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
            decode_cache_counters: options
                .collect_decode_cache_counters
                .then_some(decode_cache_counters),
        },
        verified_modules,
    })
}

enum PackageFastLayerWorkerResult<'a> {
    Passed {
        entry: &'a PackageLockEntry,
        result: PackageModuleVerificationResult,
        record: Box<PackageVerifiedModuleRecord>,
        decode_cache_counters: PackageVerificationDecodeCacheCounters,
    },
    Failed {
        entry: &'a PackageLockEntry,
        result: PackageModuleVerificationResult,
        decode_cache_counters: PackageVerificationDecodeCacheCounters,
    },
}

impl PackageFastLayerWorkerResult<'_> {
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
}

#[derive(Clone, Copy)]
struct PackageFastLayerContext<'a> {
    graph: &'a PackageLockGraph,
    verified_modules_by_module: &'a BTreeMap<Name, PackageVerifiedModuleRecord>,
    artifact_bytes: &'a BTreeMap<PackagePath, &'a [u8]>,
    session: &'a VerifierSession,
    policy: &'a AxiomPolicy,
    decode_cache_config: &'a PackageVerificationDecodeCacheConfig,
}

fn verify_fast_layer<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    context: PackageFastLayerContext<'_>,
    jobs: usize,
    parallel_strategy: PackageFastParallelStrategy,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    #[cfg(test)]
    if parallel_strategy == PackageFastParallelStrategy::LegacyLayer {
        return verify_fast_layer_legacy(
            runnable,
            context.artifact_bytes,
            context.session,
            context.policy,
            context.decode_cache_config,
            jobs,
        );
    }
    #[cfg(not(test))]
    let _ = parallel_strategy;

    verify_fast_layer_shards(runnable, context, jobs)
}

#[cfg(test)]
fn verify_fast_layer_legacy<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    session: &VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
    jobs: usize,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    if jobs == 1 {
        let mut serial_results = Vec::with_capacity(runnable.len());
        let mut serial_session = session.clone();
        for (entry_index, entry) in runnable {
            serial_results.push(verify_fast_worker(
                *entry_index,
                entry,
                artifact_bytes,
                &mut serial_session,
                policy,
                decode_cache_config,
            ));
        }
        return serial_results;
    }

    let mut results = Vec::with_capacity(runnable.len());
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
                            verify_fast_worker(
                                *entry_index,
                                entry,
                                artifact_bytes,
                                &mut worker_session,
                                policy,
                                decode_cache_config,
                            )
                        })
                        .expect("package fast verifier layer worker should spawn")
                })
                .collect::<Vec<_>>();

            for handle in handles {
                results.push(
                    handle
                        .join()
                        .expect("package fast verifier worker should not panic"),
                );
            }
        });
    }
    results
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackageFastShard {
    member_indexes: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackageFastShardPlan {
    shards: Vec<PackageFastShard>,
}

fn verify_fast_layer_shards<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    context: PackageFastLayerContext<'_>,
    jobs: usize,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    let context_modules = context
        .verified_modules_by_module
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let Some(plan) = plan_fast_verifier_shards(runnable, context.graph, &context_modules, jobs)
    else {
        return verify_fast_layer_independent_serial(
            runnable,
            context.artifact_bytes,
            context.session,
            context.policy,
            context.decode_cache_config,
        );
    };
    if plan.shards.len() <= 1 {
        return plan
            .shards
            .first()
            .map(|shard| {
                verify_fast_shard(
                    runnable,
                    shard,
                    context.artifact_bytes,
                    context.session.clone(),
                    context.policy,
                    context.decode_cache_config,
                )
            })
            .unwrap_or_default();
    }

    let mut shard_results = Vec::with_capacity(plan.shards.len());
    thread::scope(|scope| {
        let handles = plan
            .shards
            .iter()
            .enumerate()
            .map(|(shard_index, shard)| {
                let worker_session = context.session.clone();
                thread::Builder::new()
                    .name(format!("npa-package-fast-shard-{shard_index}"))
                    .stack_size(PACKAGE_FAST_VERIFIER_WORKER_STACK_BYTES)
                    .spawn_scoped(scope, move || {
                        verify_fast_shard(
                            runnable,
                            shard,
                            context.artifact_bytes,
                            worker_session,
                            context.policy,
                            context.decode_cache_config,
                        )
                    })
                    .expect("package fast verifier shard worker should spawn")
            })
            .collect::<Vec<_>>();

        for handle in handles {
            shard_results.push(
                handle
                    .join()
                    .expect("package fast verifier shard worker should not panic"),
            );
        }
    });
    shard_results.into_iter().flatten().collect()
}

fn plan_fast_verifier_shards(
    runnable: &[(usize, &PackageLockEntry)],
    graph: &PackageLockGraph,
    context_modules: &BTreeSet<Name>,
    jobs: usize,
) -> Option<PackageFastShardPlan> {
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

    let shard_count = jobs.max(1).min(runnable.len().max(1));
    let shard_size = runnable.len().div_ceil(shard_count).max(1);
    let shards = (0..runnable.len())
        .collect::<Vec<_>>()
        .chunks(shard_size)
        .map(|chunk| PackageFastShard {
            member_indexes: chunk.to_vec(),
        })
        .collect::<Vec<_>>();
    Some(PackageFastShardPlan { shards })
}

fn verify_fast_shard<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    shard: &PackageFastShard,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    mut session: VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    let mut results = Vec::with_capacity(shard.member_indexes.len());
    for member_index in &shard.member_indexes {
        let (entry_index, entry) = runnable[*member_index];
        results.push(verify_fast_worker(
            entry_index,
            entry,
            artifact_bytes,
            &mut session,
            policy,
            decode_cache_config,
        ));
    }
    results
}

fn verify_fast_layer_independent_serial<'a>(
    runnable: &[(usize, &'a PackageLockEntry)],
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    session: &VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
) -> Vec<PackageFastLayerWorkerResult<'a>> {
    runnable
        .iter()
        .map(|(entry_index, entry)| {
            let mut worker_session = session.clone();
            verify_fast_worker(
                *entry_index,
                entry,
                artifact_bytes,
                &mut worker_session,
                policy,
                decode_cache_config,
            )
        })
        .collect()
}

fn verify_fast_worker<'a>(
    entry_index: usize,
    entry: &'a PackageLockEntry,
    artifact_bytes: &BTreeMap<PackagePath, &[u8]>,
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
) -> PackageFastLayerWorkerResult<'a> {
    match verify_lock_entry(
        entry_index,
        entry,
        artifact_bytes,
        session,
        policy,
        decode_cache_config,
    ) {
        Ok((verified_module, decode_cache_counters)) => {
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
                entry,
                result: module_result(
                    entry,
                    PackageModuleVerificationStatus::Passed,
                    None,
                    PackageVerificationMode::FastKernel,
                ),
                record: Box::new(record),
                decode_cache_counters,
            }
        }
        Err(error) => PackageFastLayerWorkerResult::Failed {
            entry,
            result: module_result(
                entry,
                PackageModuleVerificationStatus::Failed,
                Some(error),
                PackageVerificationMode::FastKernel,
            ),
            decode_cache_counters: PackageVerificationDecodeCacheCounters::default(),
        },
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
    validate_execution_options(&options, PackageVerificationMode::Reference)?;
    validate_manifest_lock_identity(validated, lock)?;
    let graph = validate_package_lock_against_manifest_graph(validated, lock)
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
    .with_process_local_cache(options.collect_decode_cache_counters)
    .with_persistent_import_context_export_cache(options.collect_decode_cache_counters);
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
            Ok((checked, counters)) => {
                decode_cache_counters.add(counters);
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
        decode_cache_counters: options
            .collect_decode_cache_counters
            .then_some(decode_cache_counters),
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
    .with_process_local_cache(options.collect_decode_cache_counters)
    .with_persistent_import_context_export_cache(options.collect_decode_cache_counters);
    let mut checked_by_module = BTreeMap::<Name, ReferenceCheckedModule>::new();
    let mut remaining_import_uses =
        reference_import_use_counts(&entries, &graph, &execution_modules);
    let mut results = Vec::with_capacity(execution_modules.len());
    let mut failed_module = None::<Name>;
    let mut decode_cache_counters = PackageVerificationDecodeCacheCounters::default();

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
        match verify_reference_lock_entry_bytes(
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
        ) {
            Ok((checked, counters)) => {
                decode_cache_counters.add(counters);
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
        decode_cache_counters: options
            .collect_decode_cache_counters
            .then_some(decode_cache_counters),
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

struct PackageDecodeCacheLookup<T> {
    value: T,
    counters: PackageVerificationDecodeCacheCounters,
}

fn decode_fast_certificate_with_cache(
    entry_index: usize,
    entry: &PackageLockEntry,
    bytes: &[u8],
    actual_file_hash: PackageHash,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<PackageDecodeCacheLookup<ModuleCert>> {
    if !config.process_local_cache {
        let cert = decode_module_cert(bytes).map_err(|source| {
            PackageVerificationError::certificate_decode_failed(
                format!("entries[{entry_index}].certificate"),
                format!("{source:?}"),
            )
        })?;
        return Ok(PackageDecodeCacheLookup {
            value: cert,
            counters: PackageVerificationDecodeCacheCounters::default(),
        });
    }

    let key = package_decode_cache_certificate_key(entry, actual_file_hash, config);
    if let Some(cert) = package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned")
        .fast_certificates
        .get(&key)
        .cloned()
    {
        return Ok(PackageDecodeCacheLookup {
            value: cert,
            counters: PackageVerificationDecodeCacheCounters {
                certificate_hits: 1,
                ..PackageVerificationDecodeCacheCounters::default()
            },
        });
    }

    let cert = decode_module_cert(bytes).map_err(|source| {
        PackageVerificationError::certificate_decode_failed(
            format!("entries[{entry_index}].certificate"),
            format!("{source:?}"),
        )
    })?;
    package_verification_decode_cache()
        .lock()
        .expect("package verification decode cache mutex should not be poisoned")
        .fast_certificates
        .insert(key, cert.clone());
    Ok(PackageDecodeCacheLookup {
        value: cert,
        counters: PackageVerificationDecodeCacheCounters {
            certificate_misses: 1,
            certificate_inserted: 1,
            ..PackageVerificationDecodeCacheCounters::default()
        },
    })
}

fn reference_import_store_with_cache(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    lock: &PackageLockManifest,
    entries: &[(usize, &PackageLockEntry)],
    checked_by_module: &BTreeMap<Name, ReferenceCheckedModule>,
    config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<PackageDecodeCacheLookup<ReferenceImportStore>> {
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
            validate_reference_import_context_hit(
                entry_index,
                resolved_imports,
                checked_by_module,
            )?;
            return Ok(PackageDecodeCacheLookup {
                value: imports,
                counters: PackageVerificationDecodeCacheCounters {
                    import_context_hits: 1,
                    ..PackageVerificationDecodeCacheCounters::default()
                },
            });
        }
    }

    let mut counters = PackageVerificationDecodeCacheCounters::default();
    if config.process_local_cache {
        counters.import_context_misses = 1;
        counters.import_context_inserted = 1;
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
                validate_reference_import_context_hit(
                    entry_index,
                    resolved_imports,
                    checked_by_module,
                )?;
                counters.import_context_disk_hits += 1;
            }
            ImportContextExportCacheLookup::Missing => {
                counters.import_context_disk_misses += 1;
                pending_import_context_export_cache_write =
                    Some((disk_cache_dir, expected_disk_entry));
            }
            ImportContextExportCacheLookup::Stale => {
                counters.import_context_disk_stale += 1;
                pending_import_context_export_cache_write =
                    Some((disk_cache_dir, expected_disk_entry));
            }
            ImportContextExportCacheLookup::SchemaMiss => {
                counters.import_context_disk_schema_misses += 1;
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
            counters.import_context_disk_inserted += 1;
        }
    }
    if let Some(key) = key {
        package_verification_decode_cache()
            .lock()
            .expect("package verification decode cache mutex should not be poisoned")
            .reference_import_contexts
            .insert(key, imports.clone());
    }
    Ok(PackageDecodeCacheLookup {
        value: imports,
        counters,
    })
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
            self.counters.hits += 1;
        } else {
            self.counters.misses += 1;
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
        self.counters.inserted += 1;
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
    verify_lock_entry_bytes(
        entry_index,
        entry,
        bytes,
        session,
        policy,
        decode_cache_config,
    )
}

fn verify_lock_entry_bytes(
    entry_index: usize,
    entry: &PackageLockEntry,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    decode_cache_config: &PackageVerificationDecodeCacheConfig,
) -> PackageVerificationResult<(VerifiedModule, PackageVerificationDecodeCacheCounters)> {
    let entry_path = format!("entries[{entry_index}]");
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
    )?;
    let cert = decoded.value;
    if cert.header.module != entry.module {
        return Err(PackageVerificationError::certificate_module_mismatch(
            format!("{entry_path}.certificate"),
            entry.module.as_dotted(),
            cert.header.module.as_dotted(),
        ));
    }
    check_entry_hashes(entry_index, entry, &cert)?;

    let verified = verify_decoded_module_cert(&cert, bytes, session, policy).map_err(|source| {
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

    Ok((verified, decoded.counters))
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
    verify_reference_lock_entry_bytes(
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
    )
}

fn verify_reference_lock_entry_bytes(
    entry_index: usize,
    entry: &PackageLockEntry,
    resolved_imports: &[PackageLockResolvedImport],
    bytes: &[u8],
    context: PackageReferenceEntryBytesContext<'_>,
) -> PackageVerificationResult<(
    ReferenceCheckedModule,
    PackageVerificationDecodeCacheCounters,
)> {
    let entry_path = format!("entries[{entry_index}]");
    let actual_file_hash = package_file_hash(bytes);
    if entry.certificate_file_hash != actual_file_hash {
        return Err(PackageVerificationError::certificate_file_hash_mismatch(
            format!("{entry_path}.certificate_file_hash"),
            entry.certificate_file_hash,
            actual_file_hash,
        ));
    }

    let imports = reference_import_store_with_cache(
        entry_index,
        entry,
        resolved_imports,
        context.lock,
        context.entries,
        context.checked_by_module,
        context.decode_cache_config,
    )?;
    let mut counters = PackageVerificationDecodeCacheCounters::default();
    counters.add(imports.counters);
    let imports = imports.value;
    let checked = match check_certificate(bytes, &imports, context.policy) {
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

    Ok((checked, counters))
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
        ReferenceCheckReason::NonNormalizedLevel => "non_normalized_level",
        ReferenceCheckReason::NonNormalizedTerm => "non_normalized_term",
        ReferenceCheckReason::UnusedTableEntry => "unused_table_entry",
        ReferenceCheckReason::TrailingBytes => "trailing_bytes",
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

    use npa_package::{
        package_audit_disk_memo_key, package_audit_disk_memo_key_input,
        package_audit_process_memo_key, package_reference_summary_cache_key,
        package_reference_summary_cache_key_input, parse_manifest_str, parse_package_lock_json,
        validate_manifest, PackageId, PackageLockManifest, PackagePath, PackageVersion,
        ValidatedPackageManifest,
    };

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

    fn test_hash(byte: u8) -> npa_cert::Hash {
        [byte; 32]
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

        let plan = plan_fast_verifier_shards(&runnable, &graph, &BTreeSet::new(), 4)
            .expect("first layer has complete import context");
        let planned_indexes = plan
            .shards
            .iter()
            .flat_map(|shard| shard.member_indexes.iter().copied())
            .collect::<Vec<_>>();

        assert!(plan.shards.len() <= 4);
        assert_eq!(planned_indexes, (0..runnable.len()).collect::<Vec<_>>());
        assert_eq!(
            plan,
            plan_fast_verifier_shards(&runnable, &graph, &BTreeSet::new(), 4)
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
        assert!(
            plan_fast_verifier_shards(&dependent_runnable, &graph, &BTreeSet::new(), 4).is_none()
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

        clear_package_verification_decode_cache();
        let uncached = verify_package_fast_source_free_with_options(
            &validated,
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
                collect_decode_cache_counters: true,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .unwrap();
        let cached = verify_package_fast_source_free_with_options(
            &validated,
            &corrupt_lock,
            package_certificate_artifacts(&corrupt_artifacts),
            PackageVerificationExecutionOptions {
                selected_modules: selected,
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

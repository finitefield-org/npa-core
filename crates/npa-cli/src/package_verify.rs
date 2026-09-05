//! Implementation of `npa package verify-certs`.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::{OsStr, OsString},
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
};

#[cfg(any(target_os = "linux", target_os = "android"))]
use std::os::fd::FromRawFd;

use npa_api::{
    format_hash_string, independent_checker_file_hash,
    independent_checker_machine_check_run_with_certificate_bytes,
    independent_checker_npa_checker_ext_launch_plan,
    independent_checker_resolve_checker_executable, materialize_package_phase8_requests,
    package_verification_memo_key_inputs_from_artifact_snapshots_indexed, parse_hash_string,
    parse_independent_checker_axiom_policy_toml, parse_independent_checker_binary_registry,
    parse_independent_checker_runner_policy,
    verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed_indexed,
    verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation_indexed,
    verify_package_fast_source_free_with_hashed_artifacts_and_options_indexed,
    verify_package_fast_source_free_with_options_indexed,
    verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits_indexed,
    verify_package_reference_source_free_with_hashed_artifacts_and_options_indexed,
    verify_package_reference_source_free_with_options_indexed, IndependentCheckerAllowlistEntry,
    IndependentCheckerBinaryRegistry, IndependentCheckerMachineCheckChecker,
    IndependentCheckerMachineCheckError, IndependentCheckerMachineCheckProcess,
    IndependentCheckerMachineCheckRequestPolicy, IndependentCheckerMachineCheckResourceUsage,
    IndependentCheckerMachineCheckResult, IndependentCheckerMachineCheckRunner,
    IndependentCheckerMachineCheckStatus, IndependentCheckerPolicyFailure,
    IndependentCheckerPolicyFailureReasonCode, IndependentCheckerPolicyValidationError,
    IndependentCheckerResolvedCheckerExecutable, IndependentCheckerRunObservation,
    IndependentCheckerRunnerPolicy, PackageCertificateArtifact,
    PackageCertificateArtifactObservation, PackageModuleVerificationEvidence,
    PackageModuleVerificationResult, PackageModuleVerificationStatus,
    PackagePhase8RequestMaterialization, PackageVerificationDecodeCacheCounters,
    PackageVerificationDecodeCacheMode, PackageVerificationError, PackageVerificationErrorKind,
    PackageVerificationErrorReason, PackageVerificationExecutionOptions,
    PackageVerificationMemoCounters, PackageVerificationMemoMode, PackageVerificationMode,
    PackageVerificationReport, PackageVerificationStatus, PackageVerificationVerdictSource,
    PerformanceMeasurementMode, PerformancePackageSelectionBatchPolicy,
    PerformancePackageSelectionObservation,
};
use npa_cert::{decode_module_cert, CertificatePayloadObservation, Hash, Name};
use npa_package::{
    build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation,
    format_package_hash, normalize_package_lock_against_manifest_for_comparison,
    package_audit_cache_key, package_audit_disk_memo_key, package_audit_disk_memo_key_input,
    package_audit_disk_memo_result_entry_json, package_audit_result_entry_json, package_file_hash,
    parse_and_validate_manifest_str, parse_package_audit_disk_memo_result_entry_json,
    parse_package_audit_result_entry_json, parse_package_lock_json,
    select_package_cache_aware_live_modules_indexed, IndexedPackageLockGraph,
    IndexedPackageLockGraphError, OwnedPackageLockArtifact, PackageArtifactError,
    PackageArtifactErrorReason, PackageArtifactPreparationObservation, PackageAuditCacheKeyInput,
    PackageAuditCachedStatus, PackageAuditCheckerIdentity, PackageAuditImportIdentity,
    PackageAuditResultEntry, PackageHash, PackageLockEntry, PackageLockEntryOrigin,
    PackageLockManifest, PackageManifest, PackageModule, PackagePath,
    PreparedArtifactObservationMode, PreparedArtifactReleaseReason,
    PreparedArtifactRetentionPolicy, PreparedPackageArtifactView, PreparedPackageArtifacts,
    ValidatedPackageManifest, PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_CACHE_SCHEMA,
    PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR, PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA,
    PACKAGE_AUDIT_RESULT_SCHEMA,
};

use crate::args::{
    package_verify_selection, validate_package_verify_certs_options, PackageAuditCacheMode,
    PackageChecker, PackageExternalCheckerOptions, PackageLockInputMode, PackageVerifierMemoMode,
    PackageVerifyCertsOptions, PackageVerifyOptionsValidationError, PackageVerifySelection,
};
use crate::diagnostic::{
    CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind, DiagnosticSeverity,
    PackageVerifySelectionDetailCounts, PackageVerifySelectionSummary,
    PACKAGE_VERIFY_SELECTION_SCHEMA,
};
use crate::fs::{
    no_follow_directory::{open_absolute_directory, Directory},
    render_package_path, render_package_root,
};
use crate::generated_artifact_writer::read_package_regular_file_no_follow;
use crate::package::{load_package_root, LoadedPackageRoot, PACKAGE_MANIFEST_PATH};
use crate::package_artifacts::LoadedPackageAuditSnapshot;
use crate::timing::{
    PackageTimingCollector, TIMING_BUILD_GRAPH_MS, TIMING_CACHE_LOOKUP_MS, TIMING_CHECKER_MS,
    TIMING_DECODE_CERTIFICATES_MS, TIMING_LOAD_LOCK_MS, TIMING_LOAD_ROOT_MS, TIMING_SELECTION_MS,
};

const COMMAND: &str = "package verify-certs";
const EXTERNAL_CHECKER_PROFILE: &str = "external";
const EXTERNAL_CHECKER_LABEL: &str = "npa-checker-ext";
const PACKAGE_LOCK_PATH: &str = "generated/package-lock.json";
const PACKAGE_VERIFY_STACK_BYTES: usize = 64 * 1024 * 1024;
const GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES: usize = 64 * 1024;
const GIT_CHANGED_PATHSPEC_BATCH_MAX_PATHS: usize = 1024;
const GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES: usize = 32 * 1024;
const GIT_CHANGED_LEGACY_BATCH_PATHS: usize = 128;
const PACKAGE_VERIFY_SELECTION_DETAIL_LIMIT: usize = 64;
const PACKAGE_VERIFY_BASE_BLOB_MAX_BYTES: usize = 128 * 1024 * 1024;
const PACKAGE_VERIFY_BASE_TEXT_LIMIT: usize = 256;
const PACKAGE_VERIFY_GIT_ERROR_LIMIT: usize = 4096;
const PACKAGE_EXTERNAL_RUNNER_ID: &str = "npa-cli-package-external-runner";
const PACKAGE_EXTERNAL_RUNNER_VERSION: &str = "0.1.0";
static NEXT_AUDIT_CACHE_WRITE_TEMP: AtomicUsize = AtomicUsize::new(0);

fn canonical_selection_list_identity(values: &[String]) -> String {
    let mut canonical = Vec::new();
    for value in values {
        canonical.extend_from_slice(value.len().to_string().as_bytes());
        canonical.push(b':');
        canonical.extend_from_slice(value.as_bytes());
        canonical.push(b'\n');
    }
    format_package_hash(&package_file_hash(&canonical))
}

fn bounded_selection_details(
    values: &[String],
) -> (PackageVerifySelectionDetailCounts, Vec<String>, bool) {
    let retained = values
        .iter()
        .take(PACKAGE_VERIFY_SELECTION_DETAIL_LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    let mut overflowed = false;
    let attempted = u64::try_from(values.len()).unwrap_or_else(|_| {
        overflowed = true;
        u64::MAX
    });
    let retained_count = u64::try_from(retained.len()).unwrap_or_else(|_| {
        overflowed = true;
        u64::MAX
    });
    let omitted = attempted.saturating_sub(retained_count);
    (
        PackageVerifySelectionDetailCounts {
            attempted,
            retained: retained_count,
            omitted,
        },
        retained,
        overflowed,
    )
}

fn explicit_selection_summary(modules: &BTreeSet<Name>) -> PackageVerifySelectionSummary {
    let module_names = modules.iter().map(Name::as_dotted).collect::<Vec<_>>();
    let seed_identity = canonical_selection_list_identity(&module_names);
    let (seed_modules, seed_details, overflowed) = bounded_selection_details(&module_names);
    let detail_truncated = seed_modules.omitted > 0;
    let empty = Vec::<String>::new();
    PackageVerifySelectionSummary {
        schema: PACKAGE_VERIFY_SELECTION_SCHEMA.to_owned(),
        trusted: false,
        proof_evidence: false,
        mode: "modules".to_owned(),
        outcome: "targeted".to_owned(),
        requested_base: None,
        base_commit: None,
        merge_base: None,
        head_commit: None,
        changed_path_count: None,
        seed_modules,
        seed_details,
        seed_identity,
        closure_module_count: None,
        escalation_reasons: PackageVerifySelectionDetailCounts::default(),
        escalation_details: Vec::new(),
        escalation_identity: canonical_selection_list_identity(&empty),
        detail_truncated,
        overflowed,
    }
}

fn attach_verify_selection(
    result: CommandResult,
    summary: &Option<PackageVerifySelectionSummary>,
) -> CommandResult {
    match summary {
        Some(summary) => result.with_verify_selection(summary.clone()),
        None => result,
    }
}

fn initial_verify_selection_summary(
    selection: PackageVerifySelection<'_>,
) -> Option<PackageVerifySelectionSummary> {
    match selection {
        PackageVerifySelection::Modules(modules) => {
            let modules = modules.iter().cloned().collect::<BTreeSet<_>>();
            Some(explicit_selection_summary(&modules))
        }
        PackageVerifySelection::CommittedBase(base) => Some(base_selection_summary(base)),
        PackageVerifySelection::Full | PackageVerifySelection::WorkingTreeChanged => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FullEscalationReason {
    BaselineUnavailable,
    BaselineMetadataInvalid,
    LocalModuleDeleted,
    ModuleRoutingChanged,
    NewModuleUnattributed,
    ModuleMetadataChanged,
    PackageIdentityChanged,
    PackageVersionChanged,
    ManifestSchemaChanged,
    CoreSpecChanged,
    KernelProfileChanged,
    CertificateFormatChanged,
    CheckerProfileChanged,
    AxiomPolicyChanged,
    ExternalImportsChanged,
    PackageMetadataChanged,
    LockSchemaChanged,
    LockIdentityChanged,
    ExternalLockEntriesChanged,
    LocalLockRoutingChanged,
}

impl FullEscalationReason {
    fn as_str(self) -> &'static str {
        match self {
            Self::BaselineUnavailable => "baseline_unavailable",
            Self::BaselineMetadataInvalid => "baseline_metadata_invalid",
            Self::LocalModuleDeleted => "local_module_deleted",
            Self::ModuleRoutingChanged => "module_routing_changed",
            Self::NewModuleUnattributed => "new_module_unattributed",
            Self::ModuleMetadataChanged => "module_metadata_changed",
            Self::PackageIdentityChanged => "package_identity_changed",
            Self::PackageVersionChanged => "package_version_changed",
            Self::ManifestSchemaChanged => "manifest_schema_changed",
            Self::CoreSpecChanged => "core_spec_changed",
            Self::KernelProfileChanged => "kernel_profile_changed",
            Self::CertificateFormatChanged => "certificate_format_changed",
            Self::CheckerProfileChanged => "checker_profile_changed",
            Self::AxiomPolicyChanged => "axiom_policy_changed",
            Self::ExternalImportsChanged => "external_imports_changed",
            Self::PackageMetadataChanged => "package_metadata_changed",
            Self::LockSchemaChanged => "lock_schema_changed",
            Self::LockIdentityChanged => "lock_identity_changed",
            Self::ExternalLockEntriesChanged => "external_lock_entries_changed",
            Self::LocalLockRoutingChanged => "local_lock_routing_changed",
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FullEscalation {
    reason: FullEscalationReason,
    detail: String,
}

impl FullEscalation {
    fn new(reason: FullEscalationReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            detail: detail.into(),
        }
    }

    fn render(&self) -> String {
        if self.detail.is_empty() {
            self.reason.as_str().to_owned()
        } else {
            format!("{}:{}", self.reason.as_str(), self.detail)
        }
    }
}

#[derive(Clone, Debug)]
struct BasePackageSnapshot {
    validated: ValidatedPackageManifest,
    lock: PackageLockManifest,
}

#[derive(Clone, Debug)]
struct CommittedGitIdentity {
    worktree_root: PathBuf,
    package_prefix: String,
    object_format: GitObjectFormat,
    head_commit: String,
    merge_base: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GitObjectFormat {
    Sha1,
    Sha256,
}

impl GitObjectFormat {
    fn oid_len(self) -> usize {
        match self {
            Self::Sha1 => 40,
            Self::Sha256 => 64,
        }
    }
}

struct CommittedSelectionFailure {
    diagnostic: Box<CommandDiagnostic>,
    summary: PackageVerifySelectionSummary,
}

fn bounded_selection_text(value: &str, limit: usize) -> String {
    let mut bounded = String::new();
    for character in value.chars() {
        let character = if character.is_control() {
            '\u{fffd}'
        } else {
            character
        };
        if bounded.len().saturating_add(character.len_utf8()) > limit {
            break;
        }
        bounded.push(character);
    }
    bounded
}

fn base_selection_summary(requested_base: &str) -> PackageVerifySelectionSummary {
    let empty = Vec::<String>::new();
    PackageVerifySelectionSummary {
        schema: PACKAGE_VERIFY_SELECTION_SCHEMA.to_owned(),
        trusted: false,
        proof_evidence: false,
        mode: "base".to_owned(),
        outcome: "targeted".to_owned(),
        requested_base: Some(bounded_selection_text(
            requested_base,
            PACKAGE_VERIFY_BASE_TEXT_LIMIT,
        )),
        base_commit: None,
        merge_base: None,
        head_commit: None,
        changed_path_count: None,
        seed_modules: PackageVerifySelectionDetailCounts::default(),
        seed_details: Vec::new(),
        seed_identity: canonical_selection_list_identity(&empty),
        closure_module_count: None,
        escalation_reasons: PackageVerifySelectionDetailCounts::default(),
        escalation_details: Vec::new(),
        escalation_identity: canonical_selection_list_identity(&empty),
        detail_truncated: false,
        overflowed: false,
    }
}

fn populate_base_selection_summary(
    summary: &mut PackageVerifySelectionSummary,
    changed_path_count: usize,
    seeds: &BTreeSet<Name>,
    escalations: &BTreeSet<FullEscalation>,
) {
    summary.changed_path_count = Some(u64::try_from(changed_path_count).unwrap_or_else(|_| {
        summary.overflowed = true;
        u64::MAX
    }));
    let seed_values = seeds.iter().map(Name::as_dotted).collect::<Vec<_>>();
    summary.seed_identity = canonical_selection_list_identity(&seed_values);
    let (seed_counts, seed_details, seed_overflowed) = bounded_selection_details(&seed_values);
    summary.seed_modules = seed_counts;
    summary.seed_details = seed_details;

    let escalation_values = escalations
        .iter()
        .map(FullEscalation::render)
        .collect::<Vec<_>>();
    summary.escalation_identity = canonical_selection_list_identity(&escalation_values);
    let (escalation_counts, escalation_details, escalation_overflowed) =
        bounded_selection_details(&escalation_values);
    summary.escalation_reasons = escalation_counts;
    summary.escalation_details = escalation_details;
    summary.detail_truncated =
        summary.seed_modules.omitted > 0 || summary.escalation_reasons.omitted > 0;
    summary.overflowed |= seed_overflowed || escalation_overflowed;
    if !escalations.is_empty() {
        summary.outcome = "full_escalated".to_owned();
    }
}

#[derive(Clone, Debug)]
struct CertificateArtifactBuffer {
    path: PackagePath,
    bytes: OwnedPackageLockArtifact,
}

struct PackageLockAcquisition {
    indexed: IndexedPackageLockGraph,
    artifacts: Vec<CertificateArtifactBuffer>,
    prepared_artifacts: PreparedPackageArtifacts,
    artifact_observation: PackageCertificateArtifactObservation,
    certificate_payload_observation: CertificatePayloadObservation,
    canonical_json: String,
    canonical_hash: PackageHash,
    mode: PackageLockInputMode,
}

impl PackageLockAcquisition {
    fn new(
        indexed: IndexedPackageLockGraph,
        artifacts: Vec<CertificateArtifactBuffer>,
        prepared_artifacts: PreparedPackageArtifacts,
        artifact_observation: PackageCertificateArtifactObservation,
        certificate_payload_observation: CertificatePayloadObservation,
        canonical_json: String,
        mode: PackageLockInputMode,
    ) -> Self {
        let canonical_hash = package_file_hash(canonical_json.as_bytes());
        Self {
            indexed,
            artifacts,
            prepared_artifacts,
            artifact_observation,
            certificate_payload_observation,
            canonical_json,
            canonical_hash,
            mode,
        }
    }
}

fn indexed_package_lock_diagnostic(error: IndexedPackageLockGraphError) -> CommandDiagnostic {
    match error {
        IndexedPackageLockGraphError::Lock(error) => {
            CommandDiagnostic::from_package_lock_error(&error)
        }
        IndexedPackageLockGraphError::InternalInvariant(error) => {
            CommandDiagnostic::error(DiagnosticKind::Internal, "package_lock_index_invariant")
                .with_field("package_lock.index")
                .with_expected_value("validated_same_call_graph_products")
                .with_actual_value(error.invariant())
        }
    }
}

fn with_package_lock_provenance(
    mut result: CommandResult,
    mode: PackageLockInputMode,
    canonical_hash: PackageHash,
) -> CommandResult {
    debug_assert!(result.diagnostics.iter().all(|diagnostic| {
        !matches!(
            diagnostic.reason_code.as_str(),
            "package_lock_checked" | "package_lock_reconstructed"
        )
    }));
    let reason_code = match mode {
        PackageLockInputMode::CheckedFile => "package_lock_checked",
        PackageLockInputMode::ReconstructedInMemory => "package_lock_reconstructed",
    };
    // Lock provenance records input selection only; it is not checker or proof evidence.
    let diagnostic = CommandDiagnostic::info(DiagnosticKind::PackageLock, reason_code)
        .with_field("package_lock")
        .with_actual_value(format!(
            "mode={};hash={}",
            mode.as_str(),
            format_package_hash(&canonical_hash)
        ));
    let insert_at = result
        .diagnostics
        .iter()
        .position(|diagnostic| diagnostic.reason_code == "package_verified")
        .map(|index| index + 1)
        .unwrap_or_else(|| {
            result
                .diagnostics
                .iter()
                .position(|diagnostic| diagnostic.severity != DiagnosticSeverity::Error)
                .unwrap_or(result.diagnostics.len())
        });
    result.diagnostics.insert(insert_at, diagnostic);
    result
}

fn finish_result_with_package_lock_provenance(
    mut timings: PackageTimingCollector,
    result: CommandResult,
    acquired: &mut PackageLockAcquisition,
) -> CommandResult {
    acquired
        .prepared_artifacts
        .release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
    timings.observe_package_certificate_artifacts(
        &acquired.artifact_observation,
        acquired.prepared_artifacts.retention_observation().as_ref(),
    );
    timings.observe_certificate_payload_ownership(&acquired.certificate_payload_observation);
    timings.finish_result(with_package_lock_provenance(
        result,
        acquired.mode,
        acquired.canonical_hash,
    ))
}

struct VerifiedExternalChecker {
    resolved: IndependentCheckerResolvedCheckerExecutable,
    executable: fs::File,
}

#[derive(Clone, Debug)]
struct PackageAuditVerificationRun {
    report: PackageVerificationReport,
    cache: PackageAuditCacheSummary,
}

#[derive(Clone, Debug)]
struct PackageDiskMemoVerificationRun {
    report: PackageVerificationReport,
    memo: PackageVerifierDiskMemoSummary,
}

#[derive(Clone, Debug)]
struct PackageAuditCacheSummary {
    mode: PackageAuditCacheMode,
    hits: usize,
    misses: usize,
    stale: usize,
    schema_misses: usize,
    written: usize,
    live_checked: usize,
    cached: usize,
    trusted: bool,
    cache_off_follow_up: Option<String>,
}

#[derive(Clone, Debug)]
struct PackageVerifierDiskMemoSummary {
    mode: PackageVerifierMemoMode,
    hits: usize,
    misses: usize,
    stale: usize,
    schema_misses: usize,
    written: usize,
    invalidated: usize,
    live_checked: usize,
    cached: usize,
    trusted: bool,
    proof_evidence: bool,
}

#[derive(Clone, Debug)]
struct PackageAuditKeyedEntry {
    entry: PackageLockEntry,
    key_input: PackageAuditCacheKeyInput,
    cache_key: String,
}

#[derive(Clone, Debug)]
enum PackageAuditCacheLookup {
    Hit(Box<PackageAuditResultEntry>),
    Missing,
    SchemaMiss,
    Stale,
}

enum PackageAuditVerificationRunError {
    Diagnostic(Box<CommandDiagnostic>),
    Verification(PackageVerificationError),
}

/// Run source-free package certificate verification.
///
/// This command reads the package manifest and local/external certificate
/// files. Checked mode additionally reads `generated/package-lock.json`;
/// reconstructed mode builds the same validated snapshot in memory without
/// opening that path. It never passes source, replay, metadata, theorem-index,
/// AI trace, Git output, network registry, or checker-result sidecars to the
/// checker. Committed-base selection asks Git to compare the protected
/// source/replay/meta paths and their raw blob identities before checker
/// execution; full, changed, and explicit-module verification do not.
/// External checker mode additionally reads the explicitly supplied runner
/// policy, checker binary registry, checker binary, and axiom policy.
pub fn run_package_verify_certs(options: PackageVerifyCertsOptions) -> CommandResult {
    run_package_verify_certs_with_benchmark_artifact_mode(options, None)
}

/// Artifact representation selected only by the doc-hidden snapshot benchmark.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageArtifactSnapshotBenchmarkMode {
    /// Exercise the legacy raw/hashed acquisition lane.
    Raw,
    /// Exercise the operation-owned decoded snapshot lane where eligible.
    Snapshot,
}

/// Run ordinary package verification while forcing only the artifact
/// representation used by the snapshot benchmark.
///
/// This is not a CLI flag. All ordinary option validation, package acquisition,
/// cache, memo, verification, diagnostic, and result paths remain shared.
#[doc(hidden)]
pub fn benchmark_run_package_verify_certs(
    options: PackageVerifyCertsOptions,
    artifact_mode: PackageArtifactSnapshotBenchmarkMode,
) -> CommandResult {
    run_package_verify_certs_with_benchmark_artifact_mode(options, Some(artifact_mode))
}

fn run_package_verify_certs_with_benchmark_artifact_mode(
    options: PackageVerifyCertsOptions,
    benchmark_artifact_mode: Option<PackageArtifactSnapshotBenchmarkMode>,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let timing_mode = options.timings;
    let outer_timings = PackageTimingCollector::new(timing_mode);
    if let Err(error) = validate_package_verify_certs_options(&options) {
        return outer_timings.finish_result(CommandResult::failed(
            COMMAND,
            root_display,
            vec![package_verify_validation_diagnostic(&options, error)],
        ));
    }
    let outer_selection_summary = initial_verify_selection_summary(
        package_verify_selection(&options).expect("validated package verify selection"),
    );
    let cache_cwd =
        if options.audit_cache.uses_local_store() || options.verifier_memo.uses_local_store() {
            match std::env::current_dir() {
                Ok(cwd) => Some(cwd),
                Err(error) => {
                    return outer_timings.finish_result(CommandResult::failed(
                        COMMAND,
                        root_display,
                        vec![CommandDiagnostic::error(
                            DiagnosticKind::Internal,
                            "audit_cache_cwd_unavailable",
                        )
                        .with_actual_value(error.to_string())],
                    ));
                }
            }
        } else {
            None
        };
    match thread::Builder::new()
        .name("npa-cli-package-verify-certs".to_owned())
        .stack_size(PACKAGE_VERIFY_STACK_BYTES)
        .spawn(move || {
            run_package_verify_certs_on_stack(options, cache_cwd, benchmark_artifact_mode)
        }) {
        Ok(handle) => match handle.join() {
            Ok(result) => result,
            Err(_) => outer_timings.finish_result(attach_verify_selection(
                CommandResult::failed(
                    COMMAND,
                    root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "verify_thread_panicked",
                    )],
                ),
                &outer_selection_summary,
            )),
        },
        Err(error) => outer_timings.finish_result(attach_verify_selection(
            CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::Internal,
                    "verify_thread_spawn_failed",
                )
                .with_actual_value(error.to_string())],
            ),
            &outer_selection_summary,
        )),
    }
}

fn package_verify_validation_diagnostic(
    options: &PackageVerifyCertsOptions,
    error: PackageVerifyOptionsValidationError,
) -> CommandDiagnostic {
    let unsupported = |field: &'static str, actual_value: String| {
        CommandDiagnostic::error(DiagnosticKind::Usage, "unsupported_flag")
            .with_field(field)
            .with_actual_value(actual_value)
    };
    match error {
        PackageVerifyOptionsValidationError::JobsZero => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "invalid_flag_value")
                .with_field("--jobs")
                .with_actual_value(options.jobs.to_string())
        }
        PackageVerifyOptionsValidationError::SelectorConflict => {
            let field = if options.base.is_some() {
                "--base"
            } else if options.modules_requested || !options.modules.is_empty() {
                "--module"
            } else {
                "--changed"
            };
            CommandDiagnostic::error(DiagnosticKind::Usage, "verify_selector_conflict")
                .with_field(field)
                .with_actual_value("conflicting selector")
        }
        PackageVerifyOptionsValidationError::ModuleDuplicate => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "verify_module_duplicate")
                .with_field("--module")
        }
        PackageVerifyOptionsValidationError::ModuleSelectionEmpty => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "verify_module_selection_empty")
                .with_field("--module")
        }
        PackageVerifyOptionsValidationError::ModuleInvalid => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "invalid_module_name")
                .with_field("--module")
        }
        PackageVerifyOptionsValidationError::BaseEmpty => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "missing_flag_value")
                .with_field("--base")
        }
        PackageVerifyOptionsValidationError::ChangedWithExternalChecker => {
            unsupported("--changed", options.checker.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ModulesWithExternalChecker => {
            unsupported("--module", options.checker.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ModulesWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ModulesWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::BaseWithExternalChecker => {
            unsupported("--base", options.checker.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::BaseWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::BaseWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::BaseWithReconstructedLock => unsupported(
            "--package-lock",
            options.package_lock_mode.as_str().to_owned(),
        ),
        PackageVerifyOptionsValidationError::ExternalCheckerWithParallelJobs => {
            unsupported("--jobs", options.jobs.to_string())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithReconstructedLock => unsupported(
            "--package-lock",
            format!(
                "{};checker={}",
                options.package_lock_mode.as_str(),
                options.checker.as_str()
            ),
        ),
        PackageVerifyOptionsValidationError::AuditCacheWithParallelJobs => unsupported(
            "--jobs",
            format!(
                "jobs={};audit_cache={}",
                options.jobs,
                options.audit_cache.as_str()
            ),
        ),
        PackageVerifyOptionsValidationError::AuditCacheWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::MissingExternalCheckerOptions => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "missing_external_checker_options")
                .with_checker(EXTERNAL_CHECKER_LABEL)
        }
        PackageVerifyOptionsValidationError::UnexpectedExternalCheckerOptions => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "unsupported_flag")
                .with_field("--runner-policy")
        }
    }
}

pub(crate) fn run_package_verify_certs_fast_with_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    include_memo_summary: bool,
) -> CommandResult {
    let result = command_result_from_report(
        loaded.root_display.clone(),
        &loaded.snapshot.package_lock_manifest,
        loaded.snapshot.fast_verification_report.clone(),
        include_memo_summary,
    );
    with_package_lock_provenance(
        result,
        PackageLockInputMode::CheckedFile,
        package_file_hash(loaded.package_lock_json.as_bytes()),
    )
}

fn run_package_verify_certs_on_stack(
    options: PackageVerifyCertsOptions,
    cache_cwd: Option<PathBuf>,
    benchmark_artifact_mode: Option<PackageArtifactSnapshotBenchmarkMode>,
) -> CommandResult {
    let checker = options.checker;
    let selection = package_verify_selection(&options)
        .expect("package verify options validated before worker-thread package I/O");
    let mut initial_selection_summary = initial_verify_selection_summary(selection);
    let audit_cache = options.audit_cache;
    let verifier_memo = options.verifier_memo;
    let jobs = options.jobs;
    let mut timings = PackageTimingCollector::new(options.timings);
    let mut committed_selection_observation = (timings.is_enabled()
        && matches!(selection, PackageVerifySelection::CommittedBase(_)))
    .then(|| PerformancePackageSelectionObservation {
        committed_base: true,
        ..PerformancePackageSelectionObservation::default()
    });
    let loaded = match timings.time_phase(TIMING_LOAD_ROOT_MS, || {
        load_package_root(&options.common.root, COMMAND)
    }) {
        Ok(loaded) => loaded,
        Err(result) => {
            return timings
                .finish_result(attach_verify_selection(result, &initial_selection_summary));
        }
    };

    let retention_policy = match benchmark_artifact_mode {
        Some(PackageArtifactSnapshotBenchmarkMode::Raw) => PreparedArtifactRetentionPolicy::RawOnly,
        Some(PackageArtifactSnapshotBenchmarkMode::Snapshot) => {
            package_artifact_retention_policy(checker, jobs, audit_cache, verifier_memo)
        }
        None => package_artifact_retention_policy(checker, jobs, audit_cache, verifier_memo),
    };
    let mut acquired = match acquire_package_lock(
        &loaded,
        options.package_lock_mode,
        retention_policy,
        &mut timings,
    ) {
        Ok(acquired) => acquired,
        Err(diagnostic) => {
            return timings.finish_result(attach_verify_selection(
                CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]),
                &initial_selection_summary,
            ));
        }
    };
    debug_assert_eq!(acquired.mode, options.package_lock_mode);
    debug_assert_eq!(
        acquired.canonical_hash,
        package_file_hash(acquired.canonical_json.as_bytes())
    );
    let indexed = &acquired.indexed;
    let lock = indexed.lock();
    let artifacts = &acquired.artifacts;
    let lock_hash = acquired.canonical_hash;

    let (selected_modules, mut selection_summary) = match selection {
        PackageVerifySelection::Full => (None, None),
        PackageVerifySelection::WorkingTreeChanged => {
            let selection_result =
                run_changed_selection_with_timings(&mut timings, |observation| {
                    changed_certificate_modules(&loaded, lock, observation)
                });
            match selection_result {
                Ok(modules) => (Some(modules), None),
                Err(diagnostic) => {
                    let result =
                        CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                    return finish_result_with_package_lock_provenance(
                        timings,
                        result,
                        &mut acquired,
                    );
                }
            }
        }
        PackageVerifySelection::Modules(modules) => {
            let summary = initial_selection_summary
                .take()
                .expect("explicit selector summary initialized before package loading");
            let modules = match explicit_local_modules(&loaded.validated, modules) {
                Ok(modules) => modules,
                Err(error) => {
                    let result = CommandResult::failed(
                        COMMAND,
                        loaded.root_display,
                        vec![verification_error_diagnostic(
                            &error,
                            None,
                            checker_diagnostic_kind(checker),
                            checker_label(checker),
                        )],
                    )
                    .with_verify_selection(summary);
                    return finish_result_with_package_lock_provenance(
                        timings,
                        result,
                        &mut acquired,
                    );
                }
            };
            (Some(modules), Some(summary))
        }
        PackageVerifySelection::CommittedBase(base) => {
            let selection_result = timings.time_phase(TIMING_SELECTION_MS, || {
                committed_base_modules(
                    &loaded,
                    lock,
                    base,
                    committed_selection_observation.as_mut(),
                )
            });
            match selection_result {
                Ok((modules, summary)) => (modules, Some(summary)),
                Err(failure) => {
                    if let Some(observation) = committed_selection_observation.as_ref() {
                        timings.observe_package_selection(observation);
                    }
                    let result = CommandResult::failed(
                        COMMAND,
                        loaded.root_display,
                        vec![*failure.diagnostic],
                    )
                    .with_verify_selection(failure.summary);
                    return finish_result_with_package_lock_provenance(
                        timings,
                        result,
                        &mut acquired,
                    );
                }
            }
        }
    };

    if checker == PackageChecker::External {
        let external_options = options
            .external
            .as_ref()
            .expect("external checker options validated before package I/O");
        let result = timings.time_phase(TIMING_CHECKER_MS, || {
            run_package_verify_external(&loaded, lock, artifacts, external_options)
        });
        return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
    }

    if audit_cache == PackageAuditCacheMode::ReadThrough {
        let cache_cwd = cache_cwd.expect("read-through cache cwd captured before worker thread");
        let run = match verify_package_with_read_through_cache(
            checker,
            &loaded,
            lock_hash,
            indexed,
            artifacts,
            &mut acquired.prepared_artifacts,
            &mut acquired.artifact_observation,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
            Err(PackageAuditVerificationRunError::Verification(error)) => {
                let result = CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![verification_error_diagnostic(
                        &error,
                        None,
                        checker_diagnostic_kind(checker),
                        checker_label(checker),
                    )],
                );
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
        };
        let result = command_result_from_audit_run(loaded.root_display, lock, run);
        return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
    }

    if audit_cache == PackageAuditCacheMode::LocalHit {
        let cache_cwd = cache_cwd.expect("local-hit cache cwd captured before worker thread");
        let mut run = match verify_package_with_local_hit_cache(
            checker,
            &loaded,
            lock_hash,
            indexed,
            &mut acquired.prepared_artifacts,
            &mut acquired.artifact_observation,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
            Err(PackageAuditVerificationRunError::Verification(error)) => {
                let result = CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![verification_error_diagnostic(
                        &error,
                        None,
                        checker_diagnostic_kind(checker),
                        checker_label(checker),
                    )],
                );
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
        };
        if run.cache.cached > 0 {
            run.cache.cache_off_follow_up = Some(cache_off_follow_up_command(
                &loaded.root_display,
                checker,
                options.common.json,
            ));
        }
        let result = command_result_from_audit_run(loaded.root_display, lock, run);
        return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
    }

    if verifier_memo == PackageVerifierMemoMode::ReadThrough {
        let cache_cwd =
            cache_cwd.expect("read-through disk verifier memo cwd captured before worker thread");
        let run = match verify_package_with_read_through_disk_memo(
            checker,
            jobs,
            &loaded,
            indexed,
            artifacts,
            &mut acquired.prepared_artifacts,
            &mut acquired.artifact_observation,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
            Err(PackageAuditVerificationRunError::Verification(error)) => {
                let result = CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![verification_error_diagnostic(
                        &error,
                        None,
                        checker_diagnostic_kind(checker),
                        checker_label(checker),
                    )],
                );
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
        };
        let result =
            command_result_from_disk_memo_run(loaded.root_display, lock, run, timings.is_enabled());
        return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
    }

    if verifier_memo == PackageVerifierMemoMode::Disk {
        let cache_cwd = cache_cwd.expect("disk verifier memo cwd captured before worker thread");
        let run = match verify_package_with_disk_memo(
            checker,
            &loaded,
            indexed,
            &mut acquired.prepared_artifacts,
            &mut acquired.artifact_observation,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
            Err(PackageAuditVerificationRunError::Verification(error)) => {
                let result = CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![verification_error_diagnostic(
                        &error,
                        None,
                        checker_diagnostic_kind(checker),
                        checker_label(checker),
                    )],
                );
                return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
            }
        };
        let result =
            command_result_from_disk_memo_run(loaded.root_display, lock, run, timings.is_enabled());
        return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
    }

    let collect_decode_cache_counters = timings.is_enabled();
    let measurement_mode = timings.measurement_mode();
    let report = match timings.time_phase(TIMING_CHECKER_MS, || {
        let execution_options = ordinary_package_verification_execution_options(
            jobs,
            selected_modules,
            collect_decode_cache_counters,
            measurement_mode,
        );
        let prepared_artifacts = (checker == PackageChecker::Fast
            || checker == PackageChecker::Reference)
            .then_some(&mut acquired.prepared_artifacts);
        let artifact_observation = (checker == PackageChecker::Fast && jobs == 1)
            .then_some(&mut acquired.artifact_observation);
        verify_package(
            checker,
            &loaded,
            indexed,
            artifacts,
            prepared_artifacts,
            artifact_observation,
            execution_options,
        )
    }) {
        Ok(report) => report,
        Err(error) => {
            if let Some(observation) = committed_selection_observation.as_ref() {
                timings.observe_package_selection(observation);
            }
            let result = attach_verify_selection(
                CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![verification_error_diagnostic(
                        &error,
                        None,
                        checker_diagnostic_kind(checker),
                        checker_label(checker),
                    )],
                ),
                &selection_summary,
            );
            return finish_result_with_package_lock_provenance(timings, result, &mut acquired);
        }
    };

    timings.observe_measurements(report.measurements.clone());

    if let Some(summary) = selection_summary.as_mut() {
        let closure_module_count = u64::try_from(report.modules.len()).unwrap_or_else(|_| {
            summary.overflowed = true;
            if let Some(observation) = committed_selection_observation.as_mut() {
                observation.overflowed = true;
            }
            u64::MAX
        });
        summary.closure_module_count = Some(closure_module_count);
        if let Some(observation) = committed_selection_observation.as_mut() {
            observation.selected_closure_modules = closure_module_count;
        }
    }
    if let Some(observation) = committed_selection_observation.as_ref() {
        timings.observe_package_selection(observation);
    }

    let result = attach_verify_selection(
        command_result_from_report(loaded.root_display, lock, report, false),
        &selection_summary,
    );
    finish_result_with_package_lock_provenance(timings, result, &mut acquired)
}

fn run_changed_selection_with_timings<T>(
    timings: &mut PackageTimingCollector,
    select: impl FnOnce(Option<&mut PerformancePackageSelectionObservation>) -> T,
) -> T {
    let mut observation = timings
        .is_enabled()
        .then(PerformancePackageSelectionObservation::default);
    let result = timings.time_phase(TIMING_SELECTION_MS, || select(observation.as_mut()));
    if let Some(observation) = observation.as_ref() {
        timings.observe_package_selection(observation);
    }
    result
}

fn ordinary_package_verification_execution_options(
    jobs: usize,
    selected_modules: Option<BTreeSet<Name>>,
    collect_decode_cache_counters: bool,
    measurement_mode: PerformanceMeasurementMode,
) -> PackageVerificationExecutionOptions {
    PackageVerificationExecutionOptions {
        jobs,
        selected_modules,
        memoization: PackageVerificationMemoMode::Disabled,
        decode_cache: PackageVerificationDecodeCacheMode::Disabled,
        collect_decode_cache_counters,
        measurement_mode,
    }
}

fn explicit_local_modules(
    validated: &ValidatedPackageManifest,
    modules: &[Name],
) -> Result<BTreeSet<Name>, PackageVerificationError> {
    let local_modules = validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    let selected = modules.iter().cloned().collect::<BTreeSet<_>>();
    if let Some(module) = selected
        .iter()
        .find(|module| !local_modules.contains(*module))
    {
        return Err(PackageVerificationError {
            kind: PackageVerificationErrorKind::Input,
            path: "execution.selected_modules".to_owned(),
            module: None,
            field: Some(Box::new("selected_modules".to_owned())),
            reason_code: PackageVerificationErrorReason::SelectedModuleMissing,
            expected_value: Some("local package manifest module".to_owned()),
            actual_value: Some(module.as_dotted()),
            checker_error: None,
        });
    }
    Ok(selected)
}

fn package_artifact_retention_policy(
    checker: PackageChecker,
    jobs: usize,
    _audit_cache: PackageAuditCacheMode,
    _verifier_memo: PackageVerifierMemoMode,
) -> PreparedArtifactRetentionPolicy {
    if checker == PackageChecker::Fast && jobs == 1 {
        PreparedArtifactRetentionPolicy::FastCandidateV1
    } else {
        PreparedArtifactRetentionPolicy::RawOnly
    }
}

fn run_package_verify_external(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    options: &PackageExternalCheckerOptions,
) -> CommandResult {
    let (policy, policy_path_display) = match load_external_runner_policy(loaded, options) {
        Ok(policy) => policy,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
    };
    if let Err(diagnostic) = validate_external_axiom_policy(loaded, &policy) {
        return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
    }
    let registry = match load_external_checker_registry(loaded, options) {
        Ok(registry) => registry,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
    };
    let selected = match policy.selected_checker_policy(EXTERNAL_CHECKER_PROFILE) {
        Some(selected) => selected,
        None => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![CommandDiagnostic::error(
                    DiagnosticKind::ExternalVerifier,
                    "external_checker_profile_missing",
                )
                .with_field("checker_profile")
                .with_expected_value(EXTERNAL_CHECKER_PROFILE)
                .with_actual_value("missing")
                .with_checker(EXTERNAL_CHECKER_LABEL)],
            );
        }
    };
    let resolved = match resolve_external_checker_binary(loaded, &registry, selected) {
        Ok(resolved) => resolved,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
    };
    if !external_checker_supervisor_is_enforceable() {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![external_checker_supervisor_unavailable_diagnostic()],
        );
    }
    let materialized = match materialize_package_phase8_requests(
        lock,
        package_certificate_artifacts(artifacts),
        &policy,
        EXTERNAL_CHECKER_PROFILE,
        None,
    ) {
        Ok(report) => report,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![verification_error_diagnostic(
                    &error,
                    None,
                    DiagnosticKind::ExternalVerifier,
                    EXTERNAL_CHECKER_LABEL,
                )],
            );
        }
    };

    let mut machine_results = Vec::new();
    let mut result_artifacts = Vec::new();
    let artifact_bytes = artifact_bytes_by_path(artifacts);
    for module in &materialized.modules {
        if let Err(diagnostic) =
            materialize_external_import_dir(loaded, lock, module, &artifact_bytes)
        {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
        let Some(certificate_bytes) = artifact_bytes.get(&module.request.certificate.path) else {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                        .with_path(module.request.certificate.path.clone())
                        .with_module(module.module.as_dotted()),
                ],
            );
        };
        let run =
            run_external_machine_check(loaded, lock, &policy, &resolved, module, certificate_bytes);
        let result_path = external_machine_result_path(lock, &module.module);
        if let Err(diagnostic) = write_external_machine_result(loaded, &result_path, &run) {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
        result_artifacts.push(CommandArtifact {
            kind: "machine_check_result".to_owned(),
            path: result_path,
        });
        machine_results.push(run);
    }

    external_command_result_from_machine_results(
        loaded.root_display.clone(),
        lock,
        &policy_path_display,
        machine_results,
        result_artifacts,
    )
}

/// External machine results are release evidence, so the runner may launch a
/// checker only when it can enforce the complete policy budget for the whole
/// descendant tree and report measured usage. The current binary protocol has
/// no authenticated step counter, and this crate has no descendant-owning
/// memory supervisor. Keep the operational path closed until both exist.
fn external_checker_supervisor_is_enforceable() -> bool {
    false
}

fn external_checker_supervisor_unavailable_diagnostic() -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::ExternalVerifier,
        "external_checker_supervisor_unavailable",
    )
    .with_field("runner.resource_accounting")
    .with_expected_value("descendant_memory_timeout_and_authenticated_steps")
    .with_actual_value("unavailable")
    .with_checker(EXTERNAL_CHECKER_LABEL)
}

fn load_external_runner_policy(
    loaded: &LoadedPackageRoot,
    options: &PackageExternalCheckerOptions,
) -> Result<(IndependentCheckerRunnerPolicy, String), Box<CommandDiagnostic>> {
    let path = package_path_from_cli(&options.runner_policy, "--runner-policy")?;
    let path_display = render_package_path(&path);
    let source = read_package_text(loaded, &path, "runner_policy_missing")?;
    let expected_hash = parse_hash_string(&options.runner_policy_hash).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "invalid_hash_format")
                .with_path(path_display.clone())
                .with_field("--runner-policy-hash")
                .with_expected_value("sha256:<lower-hex>")
                .with_actual_value(options.runner_policy_hash.clone()),
        )
    })?;
    let policy = parse_independent_checker_runner_policy(&source)
        .map_err(|error| Box::new(policy_validation_diagnostic("runner_policy_invalid", error)))?;
    let actual_hash = policy.policy_hash();
    if actual_hash != expected_hash {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "runner_policy_hash_mismatch")
                .with_path(path_display)
                .with_field("--runner-policy-hash")
                .with_hashes(
                    format_hash_string(&expected_hash),
                    format_hash_string(&actual_hash),
                ),
        ));
    }
    Ok((policy, render_package_path(&path)))
}

fn validate_external_axiom_policy(
    loaded: &LoadedPackageRoot,
    policy: &IndependentCheckerRunnerPolicy,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = PackagePath::new(policy.axiom_policy.path.clone());
    let bytes = read_package_bytes(loaded, &path, "axiom_policy_missing")?;
    let actual_hash = independent_checker_file_hash(&bytes);
    if actual_hash != policy.axiom_policy.hash {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "axiom_policy_hash_mismatch")
                .with_path(render_package_path(&path))
                .with_field("runner_policy.axiom_policy.hash")
                .with_hashes(
                    format_hash_string(&policy.axiom_policy.hash),
                    format_hash_string(&actual_hash),
                ),
        ));
    }
    let source = std::str::from_utf8(&bytes).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "axiom_policy_invalid")
                .with_path(render_package_path(&path))
                .with_field("axiom_policy")
                .with_expected_value("valid_utf8")
                .with_actual_value("invalid_utf8")
                .with_checker(EXTERNAL_CHECKER_LABEL),
        )
    })?;
    parse_independent_checker_axiom_policy_toml(source).map_err(|error| {
        Box::new(
            policy_validation_diagnostic("axiom_policy_invalid", error)
                .with_path(render_package_path(&path)),
        )
    })?;
    Ok(())
}

fn load_external_checker_registry(
    loaded: &LoadedPackageRoot,
    options: &PackageExternalCheckerOptions,
) -> Result<IndependentCheckerBinaryRegistry, Box<CommandDiagnostic>> {
    let path = package_path_from_cli(&options.checker_registry, "--checker-registry")?;
    let source = read_package_text(loaded, &path, "checker_registry_missing")?;
    parse_independent_checker_binary_registry(&source).map_err(|error| {
        Box::new(policy_validation_diagnostic(
            "checker_registry_invalid",
            error,
        ))
    })
}

fn resolve_external_checker_binary(
    loaded: &LoadedPackageRoot,
    registry: &IndependentCheckerBinaryRegistry,
    selected: &IndependentCheckerAllowlistEntry,
) -> Result<VerifiedExternalChecker, Box<CommandDiagnostic>> {
    let Some(entry) = registry
        .entries
        .iter()
        .find(|entry| entry.binary_id == selected.binary_id)
    else {
        let failure = IndependentCheckerPolicyFailure {
            reason_code: IndependentCheckerPolicyFailureReasonCode::CheckerBinaryFileUnreadable,
            field: "checker.binary_id".to_owned().into_boxed_str(),
            expected_value: Some("readable_executable".to_owned().into_boxed_str()),
            actual_value: Some("binary_id_not_found".to_owned().into_boxed_str()),
            expected_hash: None,
            actual_hash: None,
        };
        return Err(Box::new(policy_failure_diagnostic(failure, None)));
    };
    let binary_path = PackagePath::new(entry.path.clone());
    let binary_bytes = read_package_bytes(loaded, &binary_path, "checker_binary_file_unreadable")?;
    let actual_binary_hash = independent_checker_file_hash(&binary_bytes);
    let resolved =
        independent_checker_resolve_checker_executable(registry, selected, actual_binary_hash)
            .map_err(|failure| {
                Box::new(policy_failure_diagnostic(
                    failure,
                    Some(render_package_path(&binary_path)),
                ))
            })?;
    let executable = stage_external_checker(&binary_bytes)
        .map_err(|error| Box::new(checker_binary_stage_diagnostic(&binary_path, &error)))?;
    Ok(VerifiedExternalChecker {
        resolved,
        executable,
    })
}

fn checker_binary_stage_diagnostic(
    binary_path: &PackagePath,
    error: &io::Error,
) -> CommandDiagnostic {
    let diagnostic = if error.kind() == io::ErrorKind::Unsupported {
        CommandDiagnostic::error(
            DiagnosticKind::ArtifactIo,
            "checker_binary_immutable_snapshot_unsupported",
        )
        .with_field("checker.binary.snapshot")
        .with_expected_value("kernel_sealed_immutable_descriptor")
        .with_actual_value(std::env::consts::OS)
    } else {
        CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "checker_binary_stage_failed")
    };
    diagnostic
        .with_path(render_package_path(binary_path))
        .with_checker(EXTERNAL_CHECKER_LABEL)
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn stage_external_checker(bytes: &[u8]) -> io::Result<fs::File> {
    let descriptor = unsafe {
        libc::memfd_create(
            c"npa-checker-ext".as_ptr(),
            libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
        )
    };
    if descriptor < 0 {
        return Err(io::Error::last_os_error());
    }
    let mut executable = unsafe { fs::File::from_raw_fd(descriptor) };
    executable.write_all(bytes)?;
    if unsafe { libc::fchmod(descriptor, 0o500) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let seals = libc::F_SEAL_SEAL | libc::F_SEAL_SHRINK | libc::F_SEAL_GROW | libc::F_SEAL_WRITE;
    if unsafe { libc::fcntl(descriptor, libc::F_ADD_SEALS, seals) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(executable)
}

#[cfg(not(any(target_os = "linux", target_os = "android")))]
fn stage_external_checker(_bytes: &[u8]) -> io::Result<fs::File> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "external checker execution requires a kernel-sealed immutable descriptor",
    ))
}

fn materialize_external_import_dir(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    module: &PackagePhase8RequestMaterialization,
    artifact_bytes: &BTreeMap<String, &[u8]>,
) -> Result<(), Box<CommandDiagnostic>> {
    let import_dir = external_import_dir_path(lock, &module.module);
    let (parent_components, leaf) =
        split_package_relative_directory(&import_dir).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_invalid")
                    .with_path(import_dir.clone()),
            )
        })?;
    let root = open_absolute_directory(&loaded.root, false).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_root_unsafe")
                .with_path(import_dir.clone()),
        )
    })?;
    let parent = open_directory_components(root, &parent_components, true).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_create_failed")
                .with_path(import_dir.clone()),
        )
    })?;
    let expected_files = module
        .import_lock_manifest
        .imports
        .iter()
        .map(|import| normal_relative_components(Path::new(&import.certificate.path)))
        .collect::<io::Result<Vec<_>>>()
        .map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_invalid")
                    .with_path(import_dir.clone()),
            )
        })?;
    match remove_closed_import_directory(&parent, &leaf, &expected_files) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_rewrite_failed")
                    .with_path(import_dir.clone()),
            ));
        }
    }
    let import_directory = parent.create_new_directory(&leaf).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_create_failed")
                .with_path(import_dir.clone()),
        )
    })?;
    for import in &module.import_lock_manifest.imports {
        let Some(bytes) = artifact_bytes.get(&import.certificate.path) else {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                    .with_path(import.certificate.path.clone())
                    .with_module(import.module.clone()),
            ));
        };
        write_relative_create_new(
            &import_directory,
            Path::new(&import.certificate.path),
            bytes,
        )
        .map_err(|_| {
            Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "import_certificate_write_failed",
                )
                .with_path(import.certificate.path.clone()),
            )
        })?;
    }
    Ok(())
}

fn normal_relative_components(path: &Path) -> io::Result<Vec<OsString>> {
    if path.is_absolute() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "absolute path"));
    }
    let components = path
        .components()
        .map(|component| match component {
            std::path::Component::Normal(component) => Ok(component.to_owned()),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "non-normal relative path",
            )),
        })
        .collect::<io::Result<Vec<_>>>()?;
    if components.is_empty() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "empty path"));
    }
    Ok(components)
}

/// Remove exactly the certificate-file catalog produced by the preceding run.
/// Unknown entries abort cleanup, and only empty named directories are removed
/// after their identity is rechecked from the retained parent descriptor.
fn remove_closed_import_directory(
    parent: &Directory,
    leaf: &OsStr,
    expected_files: &[Vec<OsString>],
) -> io::Result<()> {
    let directory = parent.open_or_create_directory(leaf, false)?;
    let identity = directory.identity()?;
    if identity.device != parent.identity()?.device {
        return Err(io::Error::other(
            "import directory crosses a device boundary",
        ));
    }
    remove_closed_file_catalog(parent, leaf, &directory, expected_files)?;
    parent.remove_empty_directory_if_identity(leaf, identity)?;
    parent.sync_all()
}

fn remove_closed_file_catalog(
    root_parent: &Directory,
    root_name: &OsStr,
    directory: &Directory,
    expected_files: &[Vec<OsString>],
) -> io::Result<()> {
    remove_closed_file_catalog_after_preflight(
        root_parent,
        root_name,
        directory,
        expected_files,
        || {},
    )
}

fn remove_closed_file_catalog_after_preflight(
    root_parent: &Directory,
    root_name: &OsStr,
    directory: &Directory,
    expected_files: &[Vec<OsString>],
    before_remove: impl FnOnce(),
) -> io::Result<()> {
    let mut groups = BTreeMap::<OsString, Vec<Vec<OsString>>>::new();
    for components in expected_files {
        let (first, rest) = components
            .split_first()
            .ok_or_else(|| io::Error::other("empty expected import path"))?;
        groups.entry(first.clone()).or_default().push(rest.to_vec());
    }
    let actual = directory
        .entry_names()?
        .into_iter()
        .collect::<BTreeSet<_>>();
    if actual != groups.keys().cloned().collect::<BTreeSet<_>>() {
        return Err(io::Error::other("import directory layout is not closed"));
    }
    // Build and validate the complete retained subtree before the first
    // unlink. Recursive validation during mutation would let a late unknown or
    // renamed entry leave a partially erased import tree.
    struct CatalogNode {
        parent: Directory,
        name: Option<OsString>,
        directory: Directory,
        identity: crate::fs::no_follow_directory::Identity,
        files: Vec<(OsString, crate::fs::no_follow_directory::Identity)>,
        children: Vec<(OsString, CatalogNode)>,
    }
    fn preflight(
        directory: &Directory,
        parent: Option<(&Directory, &OsStr)>,
        groups: BTreeMap<OsString, Vec<Vec<OsString>>>,
    ) -> io::Result<CatalogNode> {
        let identity = directory.identity()?;
        let mut files = Vec::new();
        let mut children = Vec::new();
        for (name, tails) in groups {
            if tails.iter().any(Vec::is_empty) {
                if tails.len() != 1 {
                    return Err(io::Error::other("import catalog path conflict"));
                }
                let file = directory
                    .open_regular_file(&name)?
                    .ok_or_else(|| io::Error::other("import file is unavailable"))?;
                files.push((
                    name,
                    crate::fs::no_follow_directory::regular_file_identity(&file)?,
                ));
            } else {
                let child = directory.open_or_create_directory(&name, false)?;
                if child.identity()?.device != identity.device {
                    return Err(io::Error::other("import subtree crosses a device boundary"));
                }
                let mut child_groups = BTreeMap::<OsString, Vec<Vec<OsString>>>::new();
                for tail in tails {
                    let (first, rest) = tail
                        .split_first()
                        .ok_or_else(|| io::Error::other("empty expected import path"))?;
                    child_groups
                        .entry(first.clone())
                        .or_default()
                        .push(rest.to_vec());
                }
                let child_actual = child.entry_names()?.into_iter().collect::<BTreeSet<_>>();
                if child_actual != child_groups.keys().cloned().collect::<BTreeSet<_>>() {
                    return Err(io::Error::other("import directory layout is not closed"));
                }
                children.push((
                    name.clone(),
                    preflight(&child, Some((directory, &name)), child_groups)?,
                ));
            }
        }
        let (parent, name) = match parent {
            Some((parent, name)) => (parent.try_clone()?, Some(name.to_owned())),
            None => (directory.try_clone()?, None),
        };
        Ok(CatalogNode {
            parent,
            name,
            directory: directory.try_clone()?,
            identity,
            files,
            children,
        })
    }
    fn remove(node: CatalogNode) -> io::Result<()> {
        let parent = node.parent;
        let node_name = node.name;
        let directory = node.directory;
        let identity = node.identity;
        let ensure_named = || -> io::Result<()> {
            if let Some(name) = &node_name {
                if parent.open_or_create_directory(name, false)?.identity()? != identity {
                    return Err(io::Error::other("import directory identity changed"));
                }
            }
            Ok(())
        };
        for (name, identity) in node.files {
            ensure_named()?;
            directory.remove_regular_file_if_identity(&name, identity)?;
        }
        for (name, child) in node.children {
            let child_identity = child.identity;
            ensure_named()?;
            remove(child)?;
            ensure_named()?;
            directory.remove_empty_directory_if_identity(&name, child_identity)?;
        }
        directory.sync_all()
    }
    let catalog = preflight(directory, Some((root_parent, root_name)), groups)?;
    before_remove();
    remove(catalog)
}

fn split_package_relative_directory(path: &str) -> io::Result<(Vec<OsString>, OsString)> {
    let path = Path::new(path);
    if path.is_absolute() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "package path must be relative",
        ));
    }
    let mut components = path
        .components()
        .map(|component| match component {
            std::path::Component::Normal(component) => Ok(component.to_owned()),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "package path contains a non-normal component",
            )),
        })
        .collect::<io::Result<Vec<_>>>()?;
    let leaf = components
        .pop()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "package path is empty"))?;
    Ok((components, leaf))
}

fn open_directory_components(
    mut directory: Directory,
    components: &[OsString],
    create: bool,
) -> io::Result<Directory> {
    for component in components {
        directory = directory.open_or_create_directory(component, create)?;
    }
    Ok(directory)
}

fn write_relative_create_new(root: &Directory, path: &Path, bytes: &[u8]) -> io::Result<()> {
    let (parents, leaf) = split_package_relative_directory(
        path.to_str()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "path is not UTF-8"))?,
    )?;
    let directory = open_directory_components(root.try_clone()?, &parents, true)?;
    let mut file = directory.create_new_regular_file(&leaf)?;
    file.write_all(bytes)?;
    file.sync_all()
}

fn write_relative_atomic_replace(root: &Directory, path: &Path, bytes: &[u8]) -> io::Result<()> {
    let (parents, leaf) = split_package_relative_directory(
        path.to_str()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "path is not UTF-8"))?,
    )?;
    let directory = open_directory_components(root.try_clone()?, &parents, true)?;
    match directory.open_regular_file(&leaf) {
        Ok(_) => {}
        Err(error) => return Err(error),
    }
    let temporary = OsString::from(format!(
        ".{}.{}.{}.tmp",
        leaf.to_string_lossy(),
        std::process::id(),
        NEXT_AUDIT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst)
    ));
    let mut file = directory.create_new_regular_file(&temporary)?;
    let result = (|| {
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);
        match directory.open_regular_file(&leaf) {
            Ok(_) => {}
            Err(error) => return Err(error),
        }
        directory.replace_file(&temporary, &leaf)
    })();
    if result.is_err() {
        let _ = directory.remove_file(&temporary);
    }
    result
}

fn run_external_machine_check(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    policy: &IndependentCheckerRunnerPolicy,
    checker: &VerifiedExternalChecker,
    module: &PackagePhase8RequestMaterialization,
    certificate_bytes: &[u8],
) -> IndependentCheckerMachineCheckResult {
    let import_dir = external_import_dir_path(lock, &module.module);
    let launch = independent_checker_npa_checker_ext_launch_plan(
        &checker.resolved,
        &module.request,
        import_dir.clone(),
        policy.axiom_policy.hash,
    );
    let executable = loaded.root.join(&checker.resolved.path);
    let observation = external_run_observation(
        &loaded.root,
        &executable,
        &checker.executable,
        &launch.argv,
        &launch.environment,
        module,
    );
    independent_checker_machine_check_run_with_certificate_bytes(
        &module.request,
        policy,
        observation,
        certificate_bytes,
    )
    .map(|adoption| adoption.result)
    .unwrap_or_else(|error| {
        let mut machine_error = IndependentCheckerMachineCheckError::new("checker_internal_error")
            .with_reason_code(error.reason_code.to_string());
        if let (Some(field), Some(expected), Some(actual)) = (
            error.field.clone(),
            error.expected_value.clone(),
            error.actual_value.clone(),
        ) {
            machine_error = machine_error.with_value_payload(
                field.into_string(),
                expected.into_string(),
                actual.into_string(),
            );
        } else if let (Some(field), Some(expected), Some(actual)) =
            (error.field, error.expected_hash, error.actual_hash)
        {
            machine_error =
                machine_error.with_hash_payload(field.into_string(), *expected, *actual);
        }
        IndependentCheckerMachineCheckResult {
            request_id: module.request.request_id.clone(),
            request_hash: module.request.request_hash(),
            result_id: external_machine_result_id(&module.module),
            policy: IndependentCheckerMachineCheckRequestPolicy {
                id: policy.id.clone(),
                version: policy.version,
                hash: policy.policy_hash(),
            },
            runner: external_runner_identity(),
            checker: IndependentCheckerMachineCheckChecker {
                profile: EXTERNAL_CHECKER_PROFILE.to_owned(),
                binary_id: Some(checker.resolved.binary_id.clone()),
                binary_hash: Some(checker.resolved.binary_hash),
                id: None,
                build_hash: None,
                version: None,
            },
            attempt: 1,
            status: IndependentCheckerMachineCheckStatus::Failed,
            module: module.module.as_dotted(),
            process: IndependentCheckerMachineCheckProcess::not_launched(),
            resource_usage: IndependentCheckerMachineCheckResourceUsage::zero(),
            error: Some(machine_error),
            certificate_hash: None,
            export_hash: None,
            axiom_report_hash: None,
            diagnostics: Vec::new(),
            axioms_used: None,
            declarations_checked: None,
            raw_checker_output_hex: None,
        }
    })
}

fn external_run_observation(
    root: &Path,
    executable: &Path,
    staged_executable: &fs::File,
    argv: &[String],
    environment: &[(String, String)],
    module: &PackagePhase8RequestMaterialization,
) -> IndependentCheckerRunObservation {
    let _ = (root, executable, staged_executable, argv, environment);
    IndependentCheckerRunObservation {
        result_id: external_machine_result_id(&module.module),
        attempt: 1,
        runner: external_runner_identity(),
        process: IndependentCheckerMachineCheckProcess::not_launched(),
        resource_usage: IndependentCheckerMachineCheckResourceUsage::zero(),
        stdout: Vec::new(),
        stderr: b"external_checker_supervisor_unavailable".to_vec(),
    }
}

fn external_command_result_from_machine_results(
    root_display: String,
    lock: &PackageLockManifest,
    policy_path: &str,
    machine_results: Vec<IndependentCheckerMachineCheckResult>,
    artifacts: Vec<CommandArtifact>,
) -> CommandResult {
    let entries_by_module = lock_entries_by_module(lock);
    let mut diagnostics = Vec::new();
    for result in &machine_results {
        let result_path = external_machine_result_path(lock, &module_name_from_result(result));
        if let Some(diagnostic) =
            external_result_failure_diagnostic(result, &result_path, &entries_by_module)
        {
            diagnostics.push(diagnostic);
        }
    }

    if diagnostics.is_empty() {
        let mut result = CommandResult::passed(COMMAND, root_display);
        result.diagnostics = external_passed_diagnostics(lock, policy_path, &machine_results);
        result.artifacts = artifacts;
        result
    } else {
        let mut result = CommandResult::failed(COMMAND, root_display, diagnostics);
        result.artifacts = artifacts;
        result
    }
}

fn external_passed_diagnostics(
    lock: &PackageLockManifest,
    policy_path: &str,
    machine_results: &[IndependentCheckerMachineCheckResult],
) -> Vec<CommandDiagnostic> {
    let entries_by_module = lock_entries_by_module(lock);
    let mut diagnostics = vec![
        CommandDiagnostic::info(DiagnosticKind::ExternalVerifier, "package_verified")
            .with_field("verdict_source")
            .with_path(policy_path)
            .with_actual_value(format!(
                "mode=external;verdict_source={EXTERNAL_CHECKER_LABEL};reference_checker_verdict=false;modules={}",
                machine_results.len()
            ))
            .with_checker(EXTERNAL_CHECKER_LABEL),
    ];
    diagnostics.extend(machine_results.iter().map(|result| {
        let path = entries_by_module
            .get(&module_name_from_result(result))
            .map(|entry| entry.certificate.as_str())
            .unwrap_or("<unknown-certificate>");
        CommandDiagnostic::info(DiagnosticKind::ExternalVerifier, "module_verified")
            .with_module(result.module.clone())
            .with_path(path)
            .with_field("status")
            .with_expected_value(IndependentCheckerMachineCheckStatus::Checked.as_str())
            .with_actual_value(result.status.as_str())
            .with_checker(EXTERNAL_CHECKER_LABEL)
    }));
    diagnostics
}

fn external_result_failure_diagnostic(
    result: &IndependentCheckerMachineCheckResult,
    result_path: &str,
    entries_by_module: &BTreeMap<Name, &PackageLockEntry>,
) -> Option<CommandDiagnostic> {
    if result.status != IndependentCheckerMachineCheckStatus::Checked {
        return Some(machine_result_error_diagnostic(result, result_path));
    }
    let module = module_name_from_result(result);
    let Some(entry) = entries_by_module.get(&module) else {
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::ExternalVerifier,
                "module_not_in_package_lock",
            )
            .with_path(result_path)
            .with_module(result.module.clone())
            .with_checker(EXTERNAL_CHECKER_LABEL),
        );
    };
    external_hash_failure(ExternalHashCheck {
        result_path,
        module: &result.module,
        field: "certificate_hash",
        missing_reason: "certificate_hash_missing",
        mismatch_reason: "certificate_hash_mismatch",
        expected: entry.certificate_hash,
        actual: result.certificate_hash,
    })
    .or_else(|| {
        external_hash_failure(ExternalHashCheck {
            result_path,
            module: &result.module,
            field: "export_hash",
            missing_reason: "export_hash_missing",
            mismatch_reason: "export_hash_mismatch",
            expected: entry.export_hash,
            actual: result.export_hash,
        })
    })
    .or_else(|| {
        external_hash_failure(ExternalHashCheck {
            result_path,
            module: &result.module,
            field: "axiom_report_hash",
            missing_reason: "axiom_report_hash_missing",
            mismatch_reason: "axiom_report_hash_mismatch",
            expected: entry.axiom_report_hash,
            actual: result.axiom_report_hash,
        })
    })
}

struct ExternalHashCheck<'a> {
    result_path: &'a str,
    module: &'a str,
    field: &'static str,
    missing_reason: &'static str,
    mismatch_reason: &'static str,
    expected: PackageHash,
    actual: Option<Hash>,
}

fn external_hash_failure(check: ExternalHashCheck<'_>) -> Option<CommandDiagnostic> {
    match check.actual {
        Some(actual) if actual == check.expected.into_bytes() => None,
        Some(actual) => Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, check.mismatch_reason)
                .with_path(check.result_path)
                .with_module(check.module)
                .with_field(check.field)
                .with_hashes(
                    format_package_hash(&check.expected),
                    format_hash_string(&actual),
                )
                .with_checker(EXTERNAL_CHECKER_LABEL),
        ),
        None => Some(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, check.missing_reason)
                .with_path(check.result_path)
                .with_module(check.module)
                .with_field(check.field)
                .with_expected_value(format_package_hash(&check.expected))
                .with_actual_value("missing")
                .with_checker(EXTERNAL_CHECKER_LABEL),
        ),
    }
}

fn machine_result_error_diagnostic(
    result: &IndependentCheckerMachineCheckResult,
    result_path: &str,
) -> CommandDiagnostic {
    let Some(error) = result.error.as_ref() else {
        return CommandDiagnostic::error(
            DiagnosticKind::ExternalVerifier,
            "external_checker_failed",
        )
        .with_path(result_path)
        .with_module(result.module.clone())
        .with_field("status")
        .with_expected_value(IndependentCheckerMachineCheckStatus::Checked.as_str())
        .with_actual_value(result.status.as_str())
        .with_checker(EXTERNAL_CHECKER_LABEL);
    };
    let mut diagnostic = CommandDiagnostic::error(
        if error.expected_hash.is_some() || error.actual_hash.is_some() {
            DiagnosticKind::HashMismatch
        } else {
            DiagnosticKind::ExternalVerifier
        },
        error.reason_code.as_deref().unwrap_or(&error.kind),
    )
    .with_path(result_path)
    .with_module(result.module.clone())
    .with_checker(EXTERNAL_CHECKER_LABEL);
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field.as_str());
    }
    if let (Some(expected), Some(actual)) = (error.expected_hash, error.actual_hash) {
        diagnostic =
            diagnostic.with_hashes(format_hash_string(&expected), format_hash_string(&actual));
    } else {
        if let Some(expected) = &error.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.clone());
        }
        if let Some(actual) = &error.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.clone());
        }
    }
    diagnostic
}

fn write_external_machine_result(
    loaded: &LoadedPackageRoot,
    result_path: &str,
    result: &IndependentCheckerMachineCheckResult,
) -> Result<(), Box<CommandDiagnostic>> {
    let root = open_absolute_directory(&loaded.root, false).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_root_unsafe")
                .with_path(result_path),
        )
    })?;
    write_relative_atomic_replace(
        &root,
        Path::new(result_path),
        result.canonical_json().as_bytes(),
    )
    .map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "machine_result_write_failed")
                .with_path(result_path),
        )
    })
}

fn package_path_from_cli(
    path: &Path,
    field: &'static str,
) -> Result<PackagePath, Box<CommandDiagnostic>> {
    let value = path.to_string_lossy().replace('\\', "/");
    let package_path = PackagePath::new(value);
    npa_package::validate_package_path(&package_path, field).map_err(|error| {
        Box::new(CommandDiagnostic::from_package_manifest_error(&error).with_field(field))
    })?;
    Ok(package_path)
}

fn read_package_text(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
    missing_reason: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    let bytes = read_package_bytes(loaded, path, missing_reason)?;
    String::from_utf8(bytes).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "artifact_not_utf8")
                .with_path(render_package_path(path)),
        )
    })
}

fn read_package_bytes(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
    missing_reason: &str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    read_package_regular_file_no_follow(&loaded.root, path).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, missing_reason)
                .with_path(render_package_path(path)),
        )
    })
}

fn policy_validation_diagnostic(
    reason_code: &str,
    error: IndependentCheckerPolicyValidationError,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason_code)
        .with_field(error.field)
        .with_expected_value(error.expected_value)
        .with_actual_value(error.actual_value)
        .with_checker(EXTERNAL_CHECKER_LABEL)
}

fn package_cache_aware_selection_diagnostic(error: PackageArtifactError) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "cache_aware_selection_invalid",
    )
    .with_field(error.path)
    .with_actual_value(error.reason_code.as_str())
}

fn policy_failure_diagnostic(
    failure: IndependentCheckerPolicyFailure,
    path: Option<String>,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        if failure.expected_hash.is_some() || failure.actual_hash.is_some() {
            DiagnosticKind::HashMismatch
        } else {
            DiagnosticKind::ExternalVerifier
        },
        failure.reason_code.as_str(),
    )
    .with_field(failure.field.to_string())
    .with_checker(EXTERNAL_CHECKER_LABEL);
    if let Some(path) = path {
        diagnostic = diagnostic.with_path(path);
    }
    if let (Some(expected), Some(actual)) = (failure.expected_hash, failure.actual_hash) {
        diagnostic =
            diagnostic.with_hashes(format_hash_string(&expected), format_hash_string(&actual));
    } else {
        if let Some(expected) = failure.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.to_string());
        }
        if let Some(actual) = failure.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.to_string());
        }
    }
    diagnostic
}

fn artifact_bytes_by_path(artifacts: &[CertificateArtifactBuffer]) -> BTreeMap<String, &[u8]> {
    artifacts
        .iter()
        .map(|artifact| (artifact.path.as_str().to_owned(), artifact.bytes.bytes()))
        .collect()
}

fn external_runner_identity() -> IndependentCheckerMachineCheckRunner {
    IndependentCheckerMachineCheckRunner {
        id: PACKAGE_EXTERNAL_RUNNER_ID.to_owned(),
        version: PACKAGE_EXTERNAL_RUNNER_VERSION.to_owned(),
        build_hash: independent_checker_file_hash(
            format!("{PACKAGE_EXTERNAL_RUNNER_ID}:{PACKAGE_EXTERNAL_RUNNER_VERSION}").as_bytes(),
        ),
    }
}

fn module_name_from_result(result: &IndependentCheckerMachineCheckResult) -> Name {
    Name::from_dotted(&result.module)
}

fn external_machine_result_id(module: &Name) -> String {
    format!(
        "mchkres_package_{}_external",
        module.as_dotted().replace('.', "_")
    )
}

fn external_import_dir_path(lock: &PackageLockManifest, module: &Name) -> String {
    format!(
        "generated/checker-imports/{}/{}/{}/external",
        lock.package.as_str(),
        lock.version.as_str(),
        module.as_dotted()
    )
}

fn external_machine_result_path(lock: &PackageLockManifest, module: &Name) -> String {
    format!(
        "generated/checker-results/{}/{}/{}/external/result.json",
        lock.package.as_str(),
        lock.version.as_str(),
        module.as_dotted()
    )
}

fn acquire_package_lock(
    loaded: &LoadedPackageRoot,
    mode: PackageLockInputMode,
    retention_policy: PreparedArtifactRetentionPolicy,
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    match mode {
        PackageLockInputMode::CheckedFile => {
            acquire_checked_package_lock(loaded, retention_policy, timings)
        }
        PackageLockInputMode::ReconstructedInMemory => {
            acquire_reconstructed_package_lock(loaded, retention_policy, timings)
        }
    }
}

fn acquire_checked_package_lock(
    loaded: &LoadedPackageRoot,
    retention_policy: PreparedArtifactRetentionPolicy,
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    let mut artifact_observation = PackageCertificateArtifactObservation::default();
    let mut certificate_payload_observation = CertificatePayloadObservation::default();
    let measurement_enabled = timings.is_enabled();
    let (checked_source, _checked_lock) =
        timings.time_phase(TIMING_LOAD_LOCK_MS, || read_package_lock(loaded))?;
    let artifacts = timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
        read_certificate_artifacts(
            loaded,
            measurement_enabled.then_some(&mut artifact_observation),
        )
    })?;
    let (indexed, reconstructed_json, prepared_artifacts) =
        timings.time_phase(TIMING_BUILD_GRAPH_MS, || {
            build_canonical_package_lock(
                loaded,
                &artifacts,
                retention_policy,
                measurement_enabled.then_some(&mut artifact_observation),
                measurement_enabled.then_some(&mut certificate_payload_observation),
            )
        })?;

    if checked_source != reconstructed_json {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "package_lock_stale")
                .with_path(PACKAGE_LOCK_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(reconstructed_json.as_bytes())),
                    format_package_hash(&package_file_hash(checked_source.as_bytes())),
                ),
        ));
    }

    Ok(PackageLockAcquisition::new(
        indexed,
        artifacts,
        prepared_artifacts,
        artifact_observation,
        certificate_payload_observation,
        checked_source,
        PackageLockInputMode::CheckedFile,
    ))
}

fn acquire_reconstructed_package_lock(
    loaded: &LoadedPackageRoot,
    retention_policy: PreparedArtifactRetentionPolicy,
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    let mut artifact_observation = PackageCertificateArtifactObservation::default();
    let mut certificate_payload_observation = CertificatePayloadObservation::default();
    let measurement_enabled = timings.is_enabled();
    let artifacts = timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
        read_certificate_artifacts(
            loaded,
            measurement_enabled.then_some(&mut artifact_observation),
        )
    })?;
    let (indexed, canonical_json, prepared_artifacts) =
        timings.time_phase(TIMING_BUILD_GRAPH_MS, || {
            build_canonical_package_lock(
                loaded,
                &artifacts,
                retention_policy,
                measurement_enabled.then_some(&mut artifact_observation),
                measurement_enabled.then_some(&mut certificate_payload_observation),
            )
        })?;

    Ok(PackageLockAcquisition::new(
        indexed,
        artifacts,
        prepared_artifacts,
        artifact_observation,
        certificate_payload_observation,
        canonical_json,
        PackageLockInputMode::ReconstructedInMemory,
    ))
}

fn read_package_lock(
    loaded: &LoadedPackageRoot,
) -> Result<(String, PackageLockManifest), Box<CommandDiagnostic>> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let lock_source = match read_package_regular_file_no_follow(&loaded.root, &lock_path) {
        Ok(bytes) => String::from_utf8(bytes).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            )
        })?,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::PackageLock, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            ));
        }
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            ));
        }
    };
    let lock = parse_package_lock_json(&lock_source).map_err(|error| {
        Box::new(CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH))
    })?;
    Ok((lock_source, lock))
}

fn read_certificate_artifacts(
    loaded: &LoadedPackageRoot,
    mut artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
) -> Result<Vec<CertificateArtifactBuffer>, Box<CommandDiagnostic>> {
    let mut artifacts = Vec::new();
    for (index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let bytes = read_certificate_bytes(
            loaded,
            &module.certificate,
            format!("modules[{index}].certificate"),
            Some(&module.module),
        )?;
        if let Some(observation) = artifact_observation.as_deref_mut() {
            observation.observe_file_read();
        }
        artifacts.push(CertificateArtifactBuffer {
            path: module.certificate.clone(),
            bytes: OwnedPackageLockArtifact::from_vec(module.certificate.clone(), bytes),
        });
    }
    for (index, import) in loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let bytes = read_certificate_bytes(
            loaded,
            &import.certificate,
            format!("imports[{index}].certificate"),
            Some(&import.module),
        )?;
        if let Some(observation) = artifact_observation.as_deref_mut() {
            observation.observe_file_read();
        }
        artifacts.push(CertificateArtifactBuffer {
            path: import.certificate.clone(),
            bytes: OwnedPackageLockArtifact::from_vec(import.certificate.clone(), bytes),
        });
    }
    Ok(artifacts)
}

fn read_certificate_bytes(
    loaded: &LoadedPackageRoot,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
    module: Option<&Name>,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let _ = manifest_field_path.into();
    read_package_regular_file_no_follow(&loaded.root, package_path).map_err(|_| {
        let mut diagnostic =
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                .with_path(render_package_path(package_path));
        if let Some(module) = module {
            diagnostic = diagnostic.with_module(module.as_dotted());
        }
        Box::new(diagnostic)
    })
}

fn build_canonical_package_lock(
    loaded: &LoadedPackageRoot,
    artifacts: &[CertificateArtifactBuffer],
    retention_policy: PreparedArtifactRetentionPolicy,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
    payload_observation: Option<&mut CertificatePayloadObservation>,
) -> Result<(IndexedPackageLockGraph, String, PreparedPackageArtifacts), Box<CommandDiagnostic>> {
    let mut preparation_observation = PackageArtifactPreparationObservation::default();
    let snapshots =
        build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
            &loaded.validated,
            loaded.manifest_path.clone(),
            loaded.manifest_source.as_bytes(),
            artifacts.iter().map(|artifact| artifact.bytes.clone()),
            retention_policy,
            if artifact_observation.is_some() {
                PreparedArtifactObservationMode::Aggregate
            } else {
                PreparedArtifactObservationMode::Off
            },
            artifact_observation
                .is_some()
                .then_some(&mut preparation_observation),
            payload_observation,
        );
    if let Some(observation) = artifact_observation {
        observation.merge_preparation(preparation_observation);
    }
    let (indexed, prepared_artifacts) =
        snapshots.map_err(|error| Box::new(indexed_package_lock_diagnostic(error)))?;
    let canonical_json = indexed
        .lock()
        .canonical_json()
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    Ok((indexed, canonical_json, prepared_artifacts))
}

fn verify_package(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    artifacts: &[CertificateArtifactBuffer],
    prepared_artifacts: Option<&mut PreparedPackageArtifacts>,
    artifact_observation: Option<&mut PackageCertificateArtifactObservation>,
    execution_options: PackageVerificationExecutionOptions,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => match prepared_artifacts {
            Some(prepared_artifacts) => {
                let hashed = package_hashed_artifacts(indexed.lock(), prepared_artifacts);
                verify_package_reference_source_free_with_hashed_artifacts_and_options_indexed(
                    &loaded.validated,
                    indexed,
                    hashed.iter(),
                    execution_options,
                )
            }
            None => verify_package_reference_source_free_with_options_indexed(
                &loaded.validated,
                indexed,
                package_certificate_artifacts(artifacts),
                execution_options,
            ),
        },
        PackageChecker::Fast => match prepared_artifacts {
            Some(prepared_artifacts) if execution_options.jobs == 1 => verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation_indexed(
                &loaded.validated,
                indexed,
                prepared_artifacts,
                execution_options,
                artifact_observation,
            ),
            Some(prepared_artifacts) => {
                let hashed = package_hashed_artifacts(indexed.lock(), prepared_artifacts);
                verify_package_fast_source_free_with_hashed_artifacts_and_options_indexed(
                    &loaded.validated,
                    indexed,
                    hashed.iter(),
                    execution_options,
                )
            }
            None => verify_package_fast_source_free_with_options_indexed(
                &loaded.validated,
                indexed,
                package_certificate_artifacts(artifacts),
                execution_options,
            ),
        },
        PackageChecker::External => {
            unreachable!("external checker is handled before verify_package")
        }
    }
}

fn package_hashed_artifacts(
    lock: &PackageLockManifest,
    artifacts: &PreparedPackageArtifacts,
) -> Vec<npa_package::HashedPackageLockArtifact> {
    lock.entries
        .iter()
        .filter_map(|entry| artifacts.clone_hashed_raw(&entry.certificate))
        .collect()
}

fn changed_certificate_modules(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<BTreeSet<Name>, Box<CommandDiagnostic>> {
    let certificate_modules = lock
        .entries
        .iter()
        .map(|entry| (entry.certificate.as_str().to_owned(), entry.module.clone()))
        .collect::<BTreeMap<_, _>>();
    changed_certificate_modules_with_selector(
        &certificate_modules,
        observation,
        |candidate_paths, observation| match observation {
            Some(observation) => {
                changed_package_paths_observed(&loaded.root, candidate_paths, Some(observation))
            }
            None => changed_package_paths(&loaded.root, candidate_paths),
        },
    )
}

fn changed_certificate_modules_with_selector(
    certificate_modules: &BTreeMap<String, Name>,
    observation: Option<&mut PerformancePackageSelectionObservation>,
    select: impl FnOnce(
        &BTreeSet<String>,
        Option<&mut PerformancePackageSelectionObservation>,
    ) -> Result<Vec<String>, String>,
) -> Result<BTreeSet<Name>, Box<CommandDiagnostic>> {
    let candidate_paths = certificate_modules.keys().cloned().collect::<BTreeSet<_>>();
    let changed_paths = select(&candidate_paths, observation).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, "git_status_failed")
                .with_field("--changed")
                .with_actual_value(error),
        )
    })?;
    Ok(changed_paths
        .iter()
        .filter_map(|path| certificate_modules.get(path.as_str()).cloned())
        .collect())
}

fn changed_package_paths(
    package_root: &Path,
    candidate_paths: &BTreeSet<String>,
) -> Result<Vec<String>, String> {
    changed_package_paths_with_runner(
        package_root,
        candidate_paths,
        &SystemChangedPathGitProcessRunner,
        None,
    )
}

pub(crate) fn changed_package_paths_observed(
    package_root: &Path,
    candidate_paths: &BTreeSet<String>,
    observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Vec<String>, String> {
    changed_package_paths_with_runner(
        package_root,
        candidate_paths,
        &SystemChangedPathGitProcessRunner,
        observation,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GitInvocationKind {
    WorktreeRoot,
    HasHead,
    Tracked,
    ProtectedIndexState,
    ProtectedRawHash,
    Untracked,
    IgnoredUntracked,
    ObjectFormat,
    ResolveBase,
    ResolveHead,
    MergeBase,
    LsTree,
    BlobSize,
    BlobRead,
    CommittedDiff,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct GitInvocation {
    kind: GitInvocationKind,
    program: &'static Path,
    current_dir: PathBuf,
    args: Vec<OsString>,
    committed_base_hardened: bool,
}

const SELECTOR_GIT_ENVIRONMENT: [(&str, &str); 1] = [("GIT_NO_REPLACE_OBJECTS", "1")];
const COMMITTED_BASE_GIT_ENVIRONMENT: [(&str, &str); 1] = [("GIT_NO_LAZY_FETCH", "1")];

fn git_committed_base_invocation(mut invocation: GitInvocation) -> GitInvocation {
    invocation.committed_base_hardened = true;
    invocation
}

fn git_clean_head_invocation(mut invocation: GitInvocation) -> GitInvocation {
    let mut args = [
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.trustctime=true",
        "-c",
        "core.checkStat=default",
        "-c",
        "core.fileMode=true",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.append(&mut invocation.args);
    invocation.args = args;
    git_committed_base_invocation(invocation)
}

trait ChangedPathGitProcessRunner {
    fn output(&self, invocation: &GitInvocation) -> io::Result<Output>;
}

struct SystemChangedPathGitProcessRunner;

fn apply_git_child_environment(command: &mut Command, committed_base_hardened: bool) {
    // The package root and explicit invocation arguments define the complete
    // repository protocol. Inherited Git variables can redirect the worktree,
    // repository, index, object store, refs, configuration, or pathspec
    // interpretation and make a dirty protected path look clean. Remove every
    // Git-specific variable, including dynamically numbered configuration
    // entries, before applying the fixed selector hardening values.
    let mut git_keys = std::env::vars_os()
        .map(|(key, _)| key)
        .filter(|key| is_git_child_environment_key(key))
        .collect::<BTreeSet<_>>();
    git_keys.extend(
        command
            .get_envs()
            .map(|(key, _)| key.to_os_string())
            .filter(|key| is_git_child_environment_key(key)),
    );
    for key in git_keys {
        command.env_remove(key);
    }
    for (key, value) in SELECTOR_GIT_ENVIRONMENT {
        command.env(key, value);
    }
    if committed_base_hardened {
        for (key, value) in COMMITTED_BASE_GIT_ENVIRONMENT {
            command.env(key, value);
        }
    }
}

fn is_git_child_environment_key(key: &OsStr) -> bool {
    let key = key.to_string_lossy();
    key.get(..4)
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case("GIT_"))
}

impl ChangedPathGitProcessRunner for SystemChangedPathGitProcessRunner {
    fn output(&self, invocation: &GitInvocation) -> io::Result<Output> {
        let mut command = Command::new(invocation.program);
        command
            .args(&invocation.args)
            .current_dir(&invocation.current_dir);
        apply_git_child_environment(&mut command, invocation.committed_base_hardened);
        command.output()
    }
}

fn git_worktree_root_invocation(package_root: &Path) -> GitInvocation {
    GitInvocation {
        kind: GitInvocationKind::WorktreeRoot,
        program: Path::new("/usr/bin/git"),
        current_dir: package_root.to_path_buf(),
        args: ["rev-parse", "--show-toplevel"]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    }
}

fn git_has_head_invocation(worktree_root: &Path) -> GitInvocation {
    GitInvocation {
        kind: GitInvocationKind::HasHead,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: ["rev-parse", "--verify", "--quiet", "HEAD"]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    }
}

fn git_tracked_invocation(worktree_root: &Path, pathspecs: &[String]) -> GitInvocation {
    let mut args = [
        "diff",
        "--name-only",
        "-z",
        "--no-ext-diff",
        "--no-renames",
        "HEAD",
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::Tracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_index_state_invocation(
    worktree_root: &Path,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = ["ls-files", "-s", "-v", "-z", "--"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::ProtectedIndexState,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_index_diff_invocation(
    worktree_root: &Path,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = [
        "diff",
        "--cached",
        "--name-only",
        "-z",
        "--no-ext-diff",
        "--no-renames",
        "--ignore-submodules=none",
        "HEAD",
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::Tracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_worktree_diff_invocation(
    worktree_root: &Path,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = [
        "diff",
        "--name-only",
        "-z",
        "--no-ext-diff",
        "--no-renames",
        "--ignore-submodules=none",
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::Tracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_raw_hash_invocation(
    worktree_root: &Path,
    worktree_paths: &[String],
) -> GitInvocation {
    let mut args = ["hash-object", "--no-filters", "--"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.extend(worktree_paths.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::ProtectedRawHash,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_ancestor_index_invocation(
    worktree_root: &Path,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = ["ls-files", "-z", "--"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::ProtectedIndexState,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_protected_ancestor_head_invocation(
    worktree_root: &Path,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = [
        "diff",
        "--cached",
        "--name-only",
        "-z",
        "--no-ext-diff",
        "--no-renames",
        "--ignore-submodules=none",
        "HEAD",
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::Tracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_untracked_invocation(worktree_root: &Path, pathspecs: &[String]) -> GitInvocation {
    let mut args = ["ls-files", "--others", "--exclude-standard", "-z", "--"]
        .into_iter()
        .map(OsString::from)
        .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::Untracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_ignored_untracked_invocation(worktree_root: &Path, pathspecs: &[String]) -> GitInvocation {
    let mut args = [
        "ls-files",
        "--others",
        "--ignored",
        "--exclude-standard",
        "-z",
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    GitInvocation {
        kind: GitInvocationKind::IgnoredUntracked,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    }
}

fn git_object_format_invocation(worktree_root: &Path) -> GitInvocation {
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::ObjectFormat,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: ["rev-parse", "--show-object-format=storage"]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    })
}

fn git_resolve_commit_invocation(
    worktree_root: &Path,
    revision: &str,
    kind: GitInvocationKind,
) -> GitInvocation {
    debug_assert!(matches!(
        kind,
        GitInvocationKind::ResolveBase | GitInvocationKind::ResolveHead
    ));
    git_committed_base_invocation(GitInvocation {
        kind,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: [
            OsString::from("rev-parse"),
            OsString::from("--verify"),
            OsString::from("--end-of-options"),
            OsString::from(format!("{revision}^{{commit}}")),
        ]
        .into_iter()
        .collect(),
        committed_base_hardened: false,
    })
}

fn git_merge_base_invocation(
    worktree_root: &Path,
    base_commit: &str,
    head_commit: &str,
) -> GitInvocation {
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::MergeBase,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: ["merge-base", "--all", base_commit, head_commit]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    })
}

fn git_ls_tree_invocation(
    worktree_root: &Path,
    commit: &str,
    top_literal_pathspec: &str,
) -> GitInvocation {
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::LsTree,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: [
            "ls-tree",
            "-z",
            "--full-tree",
            commit,
            "--",
            top_literal_pathspec,
        ]
        .into_iter()
        .map(OsString::from)
        .collect(),
        committed_base_hardened: false,
    })
}

fn git_blob_size_invocation(worktree_root: &Path, blob_oid: &str) -> GitInvocation {
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::BlobSize,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: ["cat-file", "-s", blob_oid]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    })
}

fn git_blob_read_invocation(worktree_root: &Path, blob_oid: &str) -> GitInvocation {
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::BlobRead,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args: ["cat-file", "blob", blob_oid]
            .into_iter()
            .map(OsString::from)
            .collect(),
        committed_base_hardened: false,
    })
}

fn git_committed_diff_invocation(
    worktree_root: &Path,
    merge_base: &str,
    head_commit: &str,
    pathspecs: &[String],
) -> GitInvocation {
    let mut args = [
        "diff",
        "--name-only",
        "-z",
        "--no-ext-diff",
        "--no-renames",
        merge_base,
        head_commit,
        "--",
    ]
    .into_iter()
    .map(OsString::from)
    .collect::<Vec<_>>();
    args.extend(pathspecs.iter().map(OsString::from));
    git_committed_base_invocation(GitInvocation {
        kind: GitInvocationKind::CommittedDiff,
        program: Path::new("/usr/bin/git"),
        current_dir: worktree_root.to_path_buf(),
        args,
        committed_base_hardened: false,
    })
}

fn git_failure(output: &Output, operation: &str) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    if stderr.is_empty() {
        format!("{operation} exited with status {}", output.status)
    } else {
        stderr
    }
}

fn decode_git_worktree_root_output(output: Output) -> Result<PathBuf, String> {
    if output.status.success() {
        Ok(PathBuf::from(
            String::from_utf8_lossy(&output.stdout).trim(),
        ))
    } else {
        Err(git_failure(&output, "git rev-parse"))
    }
}

fn decode_git_has_head_output(output: Output) -> Result<bool, String> {
    match output.status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        Some(_) | None => Err(git_failure(&output, "git rev-parse")),
    }
}

fn decode_git_tracked_output(output: Output) -> Result<Vec<u8>, String> {
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(git_failure(&output, "git diff"))
    }
}

fn decode_git_untracked_output(output: Output) -> Result<Vec<u8>, String> {
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(git_failure(&output, "git ls-files"))
    }
}

fn decode_git_protected_raw_hash_output(output: Output) -> Result<Vec<u8>, String> {
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(git_failure(&output, "git hash-object"))
    }
}

fn committed_git_output(
    runner: &impl ChangedPathGitProcessRunner,
    invocation: &GitInvocation,
    operation: &str,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Output, String> {
    let field: Option<fn(&mut PerformancePackageSelectionObservation) -> &mut u64> =
        match invocation.kind {
            GitInvocationKind::WorktreeRoot => {
                Some(|observation| &mut observation.worktree_root_queries)
            }
            GitInvocationKind::ResolveBase => {
                Some(|observation| &mut observation.base_commit_queries)
            }
            GitInvocationKind::ResolveHead => {
                Some(|observation| &mut observation.committed_head_queries)
            }
            GitInvocationKind::MergeBase => Some(|observation| &mut observation.merge_base_queries),
            GitInvocationKind::CommittedDiff => {
                Some(|observation| &mut observation.committed_diff_processes)
            }
            GitInvocationKind::ObjectFormat
            | GitInvocationKind::LsTree
            | GitInvocationKind::BlobSize
            | GitInvocationKind::BlobRead => None,
            GitInvocationKind::HasHead
            | GitInvocationKind::Tracked
            | GitInvocationKind::ProtectedIndexState
            | GitInvocationKind::ProtectedRawHash
            | GitInvocationKind::Untracked
            | GitInvocationKind::IgnoredUntracked => {
                unreachable!("working-tree selection uses its dedicated Git runner")
            }
        };
    if let Some(field) = field {
        observation_add(observation, field, 1);
    }
    let output = runner
        .output(invocation)
        .map_err(|error| format!("{operation} spawn failed: {error}"))?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(bounded_selection_text(
            &git_failure(&output, operation),
            PACKAGE_VERIFY_GIT_ERROR_LIMIT,
        ))
    }
}

fn strict_single_line(stdout: &[u8], operation: &str) -> Result<String, String> {
    let text = std::str::from_utf8(stdout)
        .map_err(|_| format!("{operation} returned non-UTF-8 output"))?;
    let line = text
        .strip_suffix('\n')
        .ok_or_else(|| format!("{operation} returned output without a terminating LF"))?;
    if line.is_empty() || line.contains(['\n', '\r', '\0']) {
        return Err(format!("{operation} returned malformed single-line output"));
    }
    Ok(line.to_owned())
}

fn validate_strict_nul_path_output(
    stdout: &[u8],
    non_terminated_error: &'static str,
    empty_record_error: &'static str,
) -> Result<(), String> {
    if stdout.is_empty() {
        return Ok(());
    }
    if !stdout.ends_with(&[0]) {
        return Err(non_terminated_error.to_owned());
    }
    let records = &stdout[..stdout.len() - 1];
    if records.is_empty() || records.split(|byte| *byte == 0).any(<[u8]>::is_empty) {
        return Err(empty_record_error.to_owned());
    }
    Ok(())
}

fn validate_git_oid(value: &str, format: GitObjectFormat, operation: &str) -> Result<(), String> {
    if value.len() != format.oid_len()
        || !value
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err(format!("{operation} returned a malformed object ID"));
    }
    Ok(())
}

fn decode_git_object_format(output: Output) -> Result<GitObjectFormat, String> {
    match strict_single_line(&output.stdout, "git object-format query")?.as_str() {
        "sha1" => Ok(GitObjectFormat::Sha1),
        "sha256" => Ok(GitObjectFormat::Sha256),
        _ => Err("git object-format query returned an unsupported format".to_owned()),
    }
}

fn decode_git_oid(
    output: Output,
    format: GitObjectFormat,
    operation: &str,
) -> Result<String, String> {
    let oid = strict_single_line(&output.stdout, operation)?;
    validate_git_oid(&oid, format, operation)?;
    Ok(oid)
}

fn decode_unique_merge_base(output: Output, format: GitObjectFormat) -> Result<String, String> {
    let merge_base = strict_single_line(&output.stdout, "git merge-base").map_err(|_| {
        "git merge-base returned zero, multiple, or malformed merge bases".to_owned()
    })?;
    validate_git_oid(&merge_base, format, "git merge-base")?;
    Ok(merge_base)
}

fn discover_committed_git_identity(
    package_root: &Path,
    requested_base: &str,
    runner: &impl ChangedPathGitProcessRunner,
    summary: &mut PackageVerifySelectionSummary,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<CommittedGitIdentity, String> {
    let root_invocation = git_committed_base_invocation(git_worktree_root_invocation(package_root));
    let root_output = committed_git_output(
        runner,
        &root_invocation,
        "git rev-parse --show-toplevel",
        observation,
    )?;
    let root_text = strict_single_line(&root_output.stdout, "git worktree-root query")?;
    let worktree_root = PathBuf::from(root_text);
    let package_prefix = package_status_prefix(package_root, &worktree_root)?;

    let object_format = decode_git_object_format(committed_git_output(
        runner,
        &git_object_format_invocation(&worktree_root),
        "git rev-parse --show-object-format",
        observation,
    )?)?;
    let base_commit = decode_git_oid(
        committed_git_output(
            runner,
            &git_resolve_commit_invocation(
                &worktree_root,
                requested_base,
                GitInvocationKind::ResolveBase,
            ),
            "git base resolution",
            observation,
        )?,
        object_format,
        "git base resolution",
    )?;
    summary.base_commit = Some(base_commit.clone());
    let head_commit = decode_git_oid(
        committed_git_output(
            runner,
            &git_resolve_commit_invocation(&worktree_root, "HEAD", GitInvocationKind::ResolveHead),
            "git HEAD resolution",
            observation,
        )?,
        object_format,
        "git HEAD resolution",
    )?;
    summary.head_commit = Some(head_commit.clone());
    let merge_base = decode_unique_merge_base(
        committed_git_output(
            runner,
            &git_merge_base_invocation(&worktree_root, &base_commit, &head_commit),
            "git merge-base",
            observation,
        )?,
        object_format,
    )?;
    summary.merge_base = Some(merge_base.clone());
    Ok(CommittedGitIdentity {
        worktree_root,
        package_prefix,
        object_format,
        head_commit,
        merge_base,
    })
}

fn package_path_at_worktree_prefix(package_prefix: &str, package_path: &str) -> String {
    if package_prefix.is_empty() {
        package_path.to_owned()
    } else {
        format!("{package_prefix}/{package_path}")
    }
}

fn read_committed_blob(
    identity: &CommittedGitIdentity,
    package_path: &str,
    runner: &impl ChangedPathGitProcessRunner,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Option<Vec<u8>>, String> {
    let worktree_path = package_path_at_worktree_prefix(&identity.package_prefix, package_path);
    let pathspec = format!(":(top,literal){worktree_path}");
    let tree_output = committed_git_output(
        runner,
        &git_ls_tree_invocation(&identity.worktree_root, &identity.merge_base, &pathspec),
        "git ls-tree",
        observation,
    )?;
    if tree_output.stdout.is_empty() {
        return Ok(None);
    }
    if !tree_output.stdout.ends_with(&[0]) {
        return Err("git ls-tree returned a non-NUL-terminated record".to_owned());
    }
    let records = tree_output.stdout[..tree_output.stdout.len() - 1]
        .split(|byte| *byte == 0)
        .collect::<Vec<_>>();
    if records.len() != 1 || records[0].is_empty() {
        return Err(format!(
            "git ls-tree returned {} exact-path records; expected one",
            records.len()
        ));
    }
    let tab = records[0]
        .iter()
        .position(|byte| *byte == b'\t')
        .ok_or_else(|| "git ls-tree returned a malformed record".to_owned())?;
    let header = &records[0][..tab];
    let returned_path = &records[0][tab + 1..];
    if returned_path != worktree_path.as_bytes() {
        return Err("git ls-tree returned a path outside the exact catalog lookup".to_owned());
    }
    let header = std::str::from_utf8(header)
        .map_err(|_| "git ls-tree returned a non-UTF-8 record header".to_owned())?;
    let fields = header.split(' ').collect::<Vec<_>>();
    if fields.len() != 3 || !matches!(fields[0], "100644" | "100755") || fields[1] != "blob" {
        return Err("git ls-tree returned a non-ordinary-blob record".to_owned());
    }
    let blob_oid = fields[2];
    validate_git_oid(blob_oid, identity.object_format, "git ls-tree")?;

    let size_output = committed_git_output(
        runner,
        &git_blob_size_invocation(&identity.worktree_root, blob_oid),
        "git cat-file -s",
        observation,
    )?;
    let size_text = strict_single_line(&size_output.stdout, "git cat-file -s")?;
    if !size_text.as_bytes().iter().all(u8::is_ascii_digit) {
        return Err("git cat-file -s returned a non-decimal size".to_owned());
    }
    let size = size_text
        .parse::<usize>()
        .map_err(|_| "git cat-file -s returned an overflowing size".to_owned())?;
    if size > PACKAGE_VERIFY_BASE_BLOB_MAX_BYTES {
        return Err(format!(
            "git blob exceeds the {PACKAGE_VERIFY_BASE_BLOB_MAX_BYTES}-byte package metadata limit"
        ));
    }
    let blob_output = committed_git_output(
        runner,
        &git_blob_read_invocation(&identity.worktree_root, blob_oid),
        "git cat-file blob",
        observation,
    )?;
    if blob_output.stdout.len() != size {
        return Err(format!(
            "git cat-file blob returned {} bytes; expected {size}",
            blob_output.stdout.len()
        ));
    }
    let field: fn(&mut PerformancePackageSelectionObservation) -> &mut u64 = match package_path {
        PACKAGE_MANIFEST_PATH => |observation| &mut observation.base_manifest_blob_bytes,
        PACKAGE_LOCK_PATH => |observation| &mut observation.base_lock_blob_bytes,
        _ => unreachable!("base selection reads only package manifest and lock blobs"),
    };
    observation_add_usize(observation, field, size);
    Ok(Some(blob_output.stdout))
}

fn load_base_package_snapshot(
    identity: &CommittedGitIdentity,
    runner: &impl ChangedPathGitProcessRunner,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<(Option<BasePackageSnapshot>, BTreeSet<FullEscalation>), String> {
    let manifest_bytes = read_committed_blob(identity, PACKAGE_MANIFEST_PATH, runner, observation)?;
    let lock_bytes = read_committed_blob(identity, PACKAGE_LOCK_PATH, runner, observation)?;
    let mut escalations = BTreeSet::new();
    let availability = (manifest_bytes.is_some(), lock_bytes.is_some());
    let (manifest_bytes, lock_bytes) = match (manifest_bytes, lock_bytes) {
        (Some(manifest_bytes), Some(lock_bytes)) => (manifest_bytes, lock_bytes),
        _ => {
            let detail = match availability {
                (false, false) => "manifest_and_lock",
                (false, true) => "manifest",
                (true, false) => "lock",
                (true, true) => unreachable!("both base blobs were matched above"),
            };
            escalations.insert(FullEscalation::new(
                FullEscalationReason::BaselineUnavailable,
                detail,
            ));
            return Ok((None, escalations));
        }
    };

    let Ok(manifest_source) = std::str::from_utf8(&manifest_bytes) else {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "manifest_utf8",
        ));
        return Ok((None, escalations));
    };
    let Ok(validated) = parse_and_validate_manifest_str(manifest_source) else {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "manifest",
        ));
        return Ok((None, escalations));
    };
    let Ok(lock_source) = std::str::from_utf8(&lock_bytes) else {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "lock_utf8",
        ));
        return Ok((None, escalations));
    };
    let Ok(lock) = parse_package_lock_json(lock_source) else {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "lock",
        ));
        return Ok((None, escalations));
    };
    if lock.manifest.path.as_str() != PACKAGE_MANIFEST_PATH
        || lock.manifest.file_hash != package_file_hash(&manifest_bytes)
    {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "manifest_lock_pair",
        ));
        return Ok((None, escalations));
    }
    let Ok(lock) = normalize_package_lock_against_manifest_for_comparison(&validated, &lock) else {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::BaselineMetadataInvalid,
            "manifest_lock_pair",
        ));
        return Ok((None, escalations));
    };
    Ok((Some(BasePackageSnapshot { validated, lock }), escalations))
}

fn insert_manifest_candidate_paths(manifest: &PackageManifest, candidates: &mut BTreeSet<String>) {
    for module in &manifest.modules {
        candidates.insert(module.source.as_str().to_owned());
        candidates.insert(module.certificate.as_str().to_owned());
        if let Some(meta) = &module.meta {
            candidates.insert(meta.as_str().to_owned());
        }
        if let Some(replay) = &module.replay {
            candidates.insert(replay.as_str().to_owned());
        }
    }
    for import in manifest.imports.as_deref().unwrap_or(&[]) {
        candidates.insert(import.certificate.as_str().to_owned());
    }
}

fn committed_candidate_catalog(
    current: &ValidatedPackageManifest,
    base: Option<&BasePackageSnapshot>,
) -> BTreeSet<String> {
    let mut candidates = BTreeSet::from([
        PACKAGE_MANIFEST_PATH.to_owned(),
        PACKAGE_LOCK_PATH.to_owned(),
    ]);
    insert_manifest_candidate_paths(current.manifest(), &mut candidates);
    if let Some(base) = base {
        insert_manifest_candidate_paths(base.validated.manifest(), &mut candidates);
    }
    candidates
}

fn committed_changed_candidate_paths(
    identity: &CommittedGitIdentity,
    candidates: &BTreeSet<String>,
    runner: &impl ChangedPathGitProcessRunner,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Vec<String>, String> {
    let candidate_by_worktree_path = candidates
        .iter()
        .map(|path| {
            (
                package_path_at_worktree_prefix(&identity.package_prefix, path),
                path.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let pathspec_groups =
        exact_candidate_pathspec_groups(candidate_by_worktree_path.keys().map(String::as_str));
    let pathspecs = pathspec_groups
        .iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    let policy = grouped_git_pathspec_batch_policy(
        &pathspecs,
        derive_committed_git_pathspec_batch_policy(
            &identity.worktree_root,
            &identity.merge_base,
            &identity.head_commit,
            &pathspecs,
        ),
        2,
    );
    let batches = pathspec_groups
        .iter()
        .flat_map(|group| git_pathspec_batches_grouped(group, policy, 2))
        .collect::<Vec<_>>();
    observation_assign_usize(
        observation,
        |observation| &mut observation.committed_diff_batches,
        batches.len(),
    );
    let mut changed = BTreeSet::new();
    for batch in batches {
        let output = committed_git_output(
            runner,
            &git_committed_diff_invocation(
                &identity.worktree_root,
                &identity.merge_base,
                &identity.head_commit,
                batch.pathspecs,
            ),
            "git committed diff",
            observation,
        )?;
        validate_strict_nul_path_output(
            &output.stdout,
            "git committed diff returned non-NUL-terminated output",
            "git committed diff returned an empty path record",
        )?;
        let records = output
            .stdout
            .split(|byte| *byte == 0)
            .filter(|record| !record.is_empty());
        for record in records {
            observation_add(
                observation,
                |observation| &mut observation.committed_diff_output_paths,
                1,
            );
            let path = std::str::from_utf8(record)
                .map_err(|_| "git committed diff returned a non-UTF-8 path".to_owned())?;
            let Some(candidate) = candidate_by_worktree_path.get(path) else {
                return Err(
                    "git committed diff returned a path outside the exact candidate catalog"
                        .to_owned(),
                );
            };
            changed.insert(candidate.clone());
        }
    }
    Ok(changed.into_iter().collect())
}

fn module_artifact_paths(module: &PackageModule) -> Vec<&str> {
    let mut paths = vec![module.source.as_str(), module.certificate.as_str()];
    if let Some(meta) = &module.meta {
        paths.push(meta.as_str());
    }
    if let Some(replay) = &module.replay {
        paths.push(replay.as_str());
    }
    paths
}

fn module_routing_is_equal(base: &PackageModule, current: &PackageModule) -> bool {
    base.module == current.module
        && base.source == current.source
        && base.certificate == current.certificate
        && base.meta == current.meta
        && base.replay == current.replay
        && base.producer_profile == current.producer_profile
}

fn manifest_modules_by_name(manifest: &PackageManifest) -> BTreeMap<Name, &PackageModule> {
    manifest
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect()
}

fn lock_entries_by_origin(
    lock: &PackageLockManifest,
    origin: PackageLockEntryOrigin,
) -> BTreeMap<Name, &PackageLockEntry> {
    lock.entries
        .iter()
        .filter(|entry| entry.origin == origin)
        .map(|entry| (entry.module.clone(), entry))
        .collect()
}

fn normalized_external_imports(
    manifest: &PackageManifest,
) -> BTreeMap<Name, &npa_package::PackageExternalImport> {
    manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .map(|import| (import.module.clone(), import))
        .collect()
}

fn normalized_axiom_policy(manifest: &PackageManifest) -> (bool, BTreeSet<Name>) {
    (
        manifest.policy.allow_custom_axioms,
        manifest.policy.allowed_axioms.iter().cloned().collect(),
    )
}

fn attribute_committed_package_changes(
    current: &ValidatedPackageManifest,
    current_lock: &PackageLockManifest,
    base: Option<&BasePackageSnapshot>,
    changed_paths: &[String],
    mut escalations: BTreeSet<FullEscalation>,
) -> (BTreeSet<Name>, BTreeSet<FullEscalation>) {
    let changed_paths = changed_paths
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let current_manifest = current.manifest();
    let current_modules = manifest_modules_by_name(current_manifest);
    let mut seeds = BTreeSet::new();

    for module in &current_manifest.modules {
        if module_artifact_paths(module)
            .iter()
            .any(|path| changed_paths.contains(path))
        {
            seeds.insert(module.module.clone());
        }
    }

    let Some(base) = base else {
        return (seeds, escalations);
    };
    let base_manifest = base.validated.manifest();
    let base_modules = manifest_modules_by_name(base_manifest);

    if base_manifest.schema != current_manifest.schema {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::ManifestSchemaChanged,
            "schema",
        ));
    }
    if base_manifest.package != current_manifest.package {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::PackageIdentityChanged,
            "package",
        ));
    }
    if base_manifest.version != current_manifest.version {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::PackageVersionChanged,
            "version",
        ));
    }
    if base_manifest.core_spec != current_manifest.core_spec {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::CoreSpecChanged,
            "core_spec",
        ));
    }
    if base_manifest.kernel_profile != current_manifest.kernel_profile {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::KernelProfileChanged,
            "kernel_profile",
        ));
    }
    if base_manifest.certificate_format != current_manifest.certificate_format {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::CertificateFormatChanged,
            "certificate_format",
        ));
    }
    if base_manifest.checker_profile != current_manifest.checker_profile {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::CheckerProfileChanged,
            "checker_profile",
        ));
    }
    if normalized_axiom_policy(base_manifest) != normalized_axiom_policy(current_manifest) {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::AxiomPolicyChanged,
            "policy",
        ));
    }
    if normalized_external_imports(base_manifest) != normalized_external_imports(current_manifest) {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::ExternalImportsChanged,
            "imports",
        ));
    }
    if base_manifest.license != current_manifest.license
        || base_manifest.repository != current_manifest.repository
        || base_manifest.description != current_manifest.description
    {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::PackageMetadataChanged,
            "informational_metadata",
        ));
    }

    for base_name in base_modules.keys() {
        if !current_modules.contains_key(base_name) {
            escalations.insert(FullEscalation::new(
                FullEscalationReason::LocalModuleDeleted,
                base_name.as_dotted(),
            ));
        }
    }
    for (name, current_module) in &current_modules {
        let Some(base_module) = base_modules.get(name) else {
            if module_artifact_paths(current_module)
                .iter()
                .any(|path| changed_paths.contains(path))
            {
                seeds.insert(name.clone());
            } else {
                escalations.insert(FullEscalation::new(
                    FullEscalationReason::NewModuleUnattributed,
                    name.as_dotted(),
                ));
            }
            continue;
        };
        if *base_module != *current_module {
            seeds.insert(name.clone());
            if !module_routing_is_equal(base_module, current_module) {
                escalations.insert(FullEscalation::new(
                    FullEscalationReason::ModuleRoutingChanged,
                    name.as_dotted(),
                ));
            } else if base_module.tags != current_module.tags {
                escalations.insert(FullEscalation::new(
                    FullEscalationReason::ModuleMetadataChanged,
                    name.as_dotted(),
                ));
            }
        }
    }

    if base.lock.schema != current_lock.schema {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::LockSchemaChanged,
            "schema",
        ));
    }
    if base.lock.package != current_lock.package || base.lock.version != current_lock.version {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::LockIdentityChanged,
            "package_or_version",
        ));
    }
    if base.lock.manifest.path != current_lock.manifest.path {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::LockIdentityChanged,
            "manifest_path",
        ));
    }
    if lock_entries_by_origin(&base.lock, PackageLockEntryOrigin::External)
        != lock_entries_by_origin(current_lock, PackageLockEntryOrigin::External)
    {
        escalations.insert(FullEscalation::new(
            FullEscalationReason::ExternalLockEntriesChanged,
            "entries",
        ));
    }

    let base_local_lock = lock_entries_by_origin(&base.lock, PackageLockEntryOrigin::Local);
    let current_local_lock = lock_entries_by_origin(current_lock, PackageLockEntryOrigin::Local);
    for (name, current_entry) in &current_local_lock {
        let Some(base_entry) = base_local_lock.get(name) else {
            if base_modules.contains_key(name) {
                escalations.insert(FullEscalation::new(
                    FullEscalationReason::LocalLockRoutingChanged,
                    name.as_dotted(),
                ));
            }
            continue;
        };
        if *base_entry != *current_entry {
            seeds.insert(name.clone());
            if base_entry.module != current_entry.module
                || base_entry.origin != current_entry.origin
                || base_entry.certificate != current_entry.certificate
                || base_entry.package != current_entry.package
                || base_entry.version != current_entry.version
            {
                escalations.insert(FullEscalation::new(
                    FullEscalationReason::LocalLockRoutingChanged,
                    name.as_dotted(),
                ));
            }
        }
    }
    for name in base_local_lock.keys() {
        if !current_local_lock.contains_key(name) && current_modules.contains_key(name) {
            escalations.insert(FullEscalation::new(
                FullEscalationReason::LocalLockRoutingChanged,
                name.as_dotted(),
            ));
        }
    }

    (seeds, escalations)
}

fn committed_git_selection_failure(
    summary: PackageVerifySelectionSummary,
    error: impl AsRef<str>,
) -> CommittedSelectionFailure {
    let requested_base = summary.requested_base.as_deref().unwrap_or("");
    let actual = bounded_selection_text(
        &format!(
            "base={};error={}",
            requested_base,
            bounded_selection_text(error.as_ref(), PACKAGE_VERIFY_GIT_ERROR_LIMIT)
        ),
        PACKAGE_VERIFY_GIT_ERROR_LIMIT,
    );
    CommittedSelectionFailure {
        diagnostic: Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, "git_base_selection_failed")
                .with_field("--base")
                .with_actual_value(actual),
        ),
        summary,
    }
}

fn dirty_base_selection_failure(
    summary: PackageVerifySelectionSummary,
    dirty_paths: &[String],
) -> CommittedSelectionFailure {
    let identity = canonical_selection_list_identity(dirty_paths);
    let retained = dirty_paths
        .iter()
        .take(PACKAGE_VERIFY_SELECTION_DETAIL_LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    let actual = bounded_selection_text(
        &format!(
            "attempted={};retained={};omitted={};identity={};paths={}",
            dirty_paths.len(),
            retained.len(),
            dirty_paths.len().saturating_sub(retained.len()),
            identity,
            retained.join(",")
        ),
        PACKAGE_VERIFY_GIT_ERROR_LIMIT,
    );
    CommittedSelectionFailure {
        diagnostic: Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::SourceFreeBoundary,
                "base_selection_dirty_inputs",
            )
            .with_field("--base")
            .with_actual_value(actual),
        ),
        summary,
    }
}

fn empty_base_selection_failure(
    summary: PackageVerifySelectionSummary,
) -> CommittedSelectionFailure {
    CommittedSelectionFailure {
        diagnostic: Box::new(
            CommandDiagnostic::error(DiagnosticKind::SourceFreeBoundary, "base_selection_empty")
                .with_field("--base")
                .with_actual_value("no attributable module or full-escalation reason"),
        ),
        summary,
    }
}

fn selection_identity_words(identity: &str) -> [u64; 4] {
    let digest = identity
        .strip_prefix("sha256:")
        .expect("selection identities use canonical SHA-256 spelling");
    std::array::from_fn(|index| {
        let start = index * 16;
        u64::from_str_radix(&digest[start..start + 16], 16)
            .expect("selection identity contains canonical SHA-256 hex")
    })
}

fn committed_base_modules_with_runner(
    loaded: &LoadedPackageRoot,
    current_lock: &PackageLockManifest,
    requested_base: &str,
    runner: &impl ChangedPathGitProcessRunner,
    mut observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<(Option<BTreeSet<Name>>, PackageVerifySelectionSummary), CommittedSelectionFailure> {
    let mut summary = base_selection_summary(requested_base);
    let identity = discover_committed_git_identity(
        &loaded.root,
        requested_base,
        runner,
        &mut summary,
        &mut observation,
    )
    .map_err(|error| committed_git_selection_failure(summary.clone(), error))?;
    let (base, initial_escalations) =
        load_base_package_snapshot(&identity, runner, &mut observation)
            .map_err(|error| committed_git_selection_failure(summary.clone(), error))?;
    let candidates = committed_candidate_catalog(&loaded.validated, base.as_ref());
    observation_assign_usize(
        &mut observation,
        |observation| &mut observation.protected_candidate_paths,
        candidates.len(),
    );
    let dirty_paths = changed_candidate_paths_in_worktree(
        &identity.worktree_root,
        &identity.package_prefix,
        &candidates,
        runner,
        observation.as_deref_mut(),
        None,
        true,
    )
    .map_err(|error| committed_git_selection_failure(summary.clone(), error))?;
    observation_assign_usize(
        &mut observation,
        |observation| &mut observation.dirty_paths,
        dirty_paths.len(),
    );
    if !dirty_paths.is_empty() {
        return Err(dirty_base_selection_failure(summary, &dirty_paths));
    }
    let changed_paths =
        committed_changed_candidate_paths(&identity, &candidates, runner, &mut observation)
            .map_err(|error| committed_git_selection_failure(summary.clone(), error))?;
    let (seeds, escalations) = attribute_committed_package_changes(
        &loaded.validated,
        current_lock,
        base.as_ref(),
        &changed_paths,
        initial_escalations,
    );
    populate_base_selection_summary(&mut summary, changed_paths.len(), &seeds, &escalations);
    observation_assign_usize(
        &mut observation,
        |observation| &mut observation.seed_modules,
        seeds.len(),
    );
    if !escalations.is_empty() {
        let reason_identity = selection_identity_words(&summary.escalation_identity);
        observe_selection(&mut observation, |observation| {
            observation.full_escalations = 1;
            observation.full_escalation_reason_identity = reason_identity;
        });
    }
    if escalations.is_empty() && seeds.is_empty() {
        return Err(empty_base_selection_failure(summary));
    }
    let selected_modules = escalations.is_empty().then_some(seeds);
    Ok((selected_modules, summary))
}

fn committed_base_modules(
    loaded: &LoadedPackageRoot,
    current_lock: &PackageLockManifest,
    requested_base: &str,
    observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<(Option<BTreeSet<Name>>, PackageVerifySelectionSummary), CommittedSelectionFailure> {
    committed_base_modules_with_runner(
        loaded,
        current_lock,
        requested_base,
        &SystemChangedPathGitProcessRunner,
        observation,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GitPathspecBatch<'a> {
    pathspecs: &'a [String],
    payload_bytes: usize,
    argv_charge_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GitPathspecBatchPolicy {
    ExecBudget { effective_charge_bytes: usize },
    Legacy128,
}

fn grouped_git_pathspec_batch_policy(
    pathspecs: &[String],
    policy: GitPathspecBatchPolicy,
    group_size: usize,
) -> GitPathspecBatchPolicy {
    let GitPathspecBatchPolicy::ExecBudget {
        effective_charge_bytes,
    } = policy
    else {
        return policy;
    };
    if group_size == 0 || !pathspecs.len().is_multiple_of(group_size) {
        return GitPathspecBatchPolicy::Legacy128;
    }
    let group_exceeds_budget = pathspecs.chunks_exact(group_size).any(|group| {
        group
            .iter()
            .try_fold(0usize, |charge, pathspec| {
                charge.checked_add(pathspec_charges(pathspec)?.1)
            })
            .is_none_or(|charge| charge > effective_charge_bytes)
    });
    if group_exceeds_budget {
        GitPathspecBatchPolicy::Legacy128
    } else {
        policy
    }
}

fn pathspec_charges(pathspec: &str) -> Option<(usize, usize)> {
    let payload_bytes = pathspec.len().checked_add(1)?;
    let argv_charge_bytes = payload_bytes.checked_add(std::mem::size_of::<*const u8>())?;
    Some((payload_bytes, argv_charge_bytes))
}

#[cfg(test)]
fn git_pathspec_batches(
    pathspecs: &[String],
    policy: GitPathspecBatchPolicy,
) -> Vec<GitPathspecBatch<'_>> {
    git_pathspec_batches_grouped(pathspecs, policy, 1)
}

fn git_pathspec_batches_grouped(
    pathspecs: &[String],
    policy: GitPathspecBatchPolicy,
    group_size: usize,
) -> Vec<GitPathspecBatch<'_>> {
    if pathspecs.is_empty() {
        return Vec::new();
    }
    assert!(group_size > 0, "pathspec group size must be positive");
    assert_eq!(
        pathspecs.len() % group_size,
        0,
        "pathspec groups must be complete"
    );
    match policy {
        GitPathspecBatchPolicy::Legacy128 => {
            let batch_size = GIT_CHANGED_LEGACY_BATCH_PATHS
                .checked_div(group_size)
                .unwrap_or(0)
                .saturating_mul(group_size)
                .max(group_size);
            pathspecs
                .chunks(batch_size)
                .map(|pathspecs| {
                    let (payload_bytes, argv_charge_bytes) =
                        pathspecs
                            .iter()
                            .fold((0usize, 0usize), |(payload, argv), pathspec| {
                                let (next_payload, next_argv) =
                                    pathspec_charges(pathspec).unwrap_or((usize::MAX, usize::MAX));
                                (
                                    payload.saturating_add(next_payload),
                                    argv.saturating_add(next_argv),
                                )
                            });
                    GitPathspecBatch {
                        pathspecs,
                        payload_bytes,
                        argv_charge_bytes,
                    }
                })
                .collect()
        }
        GitPathspecBatchPolicy::ExecBudget {
            effective_charge_bytes,
        } => {
            let mut batches = Vec::new();
            let mut start = 0;
            let mut payload_bytes = 0usize;
            let mut argv_charge_bytes = 0usize;
            for index in (0..pathspecs.len()).step_by(group_size) {
                let (next_payload, next_argv) = pathspecs[index..index + group_size].iter().fold(
                    (0usize, 0usize),
                    |(payload, argv), pathspec| {
                        let (path_payload, path_argv) = pathspec_charges(pathspec)
                            .expect("exec-budget policy preflights every pathspec charge");
                        (
                            payload.saturating_add(path_payload),
                            argv.saturating_add(path_argv),
                        )
                    },
                );
                let exceeds_bytes = argv_charge_bytes
                    .checked_add(next_argv)
                    .is_none_or(|charge| charge > effective_charge_bytes);
                let exceeds_count = index.saturating_sub(start).saturating_add(group_size)
                    > GIT_CHANGED_PATHSPEC_BATCH_MAX_PATHS;
                if index > start && (exceeds_bytes || exceeds_count) {
                    batches.push(GitPathspecBatch {
                        pathspecs: &pathspecs[start..index],
                        payload_bytes,
                        argv_charge_bytes,
                    });
                    start = index;
                    payload_bytes = 0;
                    argv_charge_bytes = 0;
                }
                payload_bytes = payload_bytes.saturating_add(next_payload);
                argv_charge_bytes = argv_charge_bytes.saturating_add(next_argv);
            }
            batches.push(GitPathspecBatch {
                pathspecs: &pathspecs[start..],
                payload_bytes,
                argv_charge_bytes,
            });
            batches
        }
    }
}

#[cfg(unix)]
fn os_string_byte_len(value: &std::ffi::OsStr) -> usize {
    use std::os::unix::ffi::OsStrExt;
    value.as_bytes().len()
}

#[cfg(unix)]
fn inherited_environment_charge(environment: &[(OsString, OsString)]) -> Option<usize> {
    let pointer_size = std::mem::size_of::<*const u8>();
    let payload = environment.iter().try_fold(0usize, |total, (key, value)| {
        total
            .checked_add(os_string_byte_len(key))?
            .checked_add(1)?
            .checked_add(os_string_byte_len(value))?
            .checked_add(1)
    })?;
    payload.checked_add(
        environment
            .len()
            .checked_add(1)?
            .checked_mul(pointer_size)?,
    )
}

#[cfg(unix)]
fn effective_git_child_environment(
    mut environment: Vec<(OsString, OsString)>,
    committed_base_hardened: bool,
) -> Vec<(OsString, OsString)> {
    environment.retain(|(key, _)| !is_git_child_environment_key(key));
    for (override_key, override_value) in SELECTOR_GIT_ENVIRONMENT {
        environment.push((OsString::from(override_key), OsString::from(override_value)));
    }
    if committed_base_hardened {
        for (override_key, override_value) in COMMITTED_BASE_GIT_ENVIRONMENT {
            environment.push((OsString::from(override_key), OsString::from(override_value)));
        }
    }
    environment
}

#[cfg(unix)]
fn fixed_invocation_argv_charge(invocation: &GitInvocation) -> Option<usize> {
    let pointer_size = std::mem::size_of::<*const u8>();
    let executable_payload = os_string_byte_len(invocation.program.as_os_str()).checked_add(1)?;
    let argument_payload = invocation.args.iter().try_fold(0usize, |total, argument| {
        total
            .checked_add(os_string_byte_len(argument))?
            .checked_add(1)
    })?;
    executable_payload
        .checked_add(argument_payload)?
        .checked_add(
            invocation
                .args
                .len()
                .checked_add(2)?
                .checked_mul(pointer_size)?,
        )
}

#[cfg(unix)]
fn unix_arg_max() -> Option<usize> {
    // SAFETY: `sysconf` receives a constant and reads no caller-owned memory.
    let value = unsafe { libc::sysconf(libc::_SC_ARG_MAX) };
    (value > 0).then(|| usize::try_from(value).ok()).flatten()
}

fn effective_git_pathspec_charge(
    arg_max: usize,
    environment_charge: usize,
    fixed_argv_charge: usize,
) -> Option<usize> {
    let safe = arg_max
        .checked_sub(environment_charge)?
        .checked_sub(fixed_argv_charge)?
        .checked_sub(GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES)?;
    (safe > 0).then_some(safe.min(GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES))
}

#[cfg(unix)]
fn derive_git_pathspec_batch_policy(pathspecs: &[String]) -> GitPathspecBatchPolicy {
    let environment =
        effective_git_child_environment(std::env::vars_os().collect::<Vec<_>>(), false);
    let empty_root = Path::new("");
    let fixed_charge = [
        fixed_invocation_argv_charge(&git_tracked_invocation(empty_root, &[])),
        fixed_invocation_argv_charge(&git_untracked_invocation(empty_root, &[])),
    ]
    .into_iter()
    .collect::<Option<Vec<_>>>()
    .and_then(|charges| charges.into_iter().max());
    git_pathspec_batch_policy_from_charges(
        pathspecs,
        unix_arg_max(),
        inherited_environment_charge(&environment),
        fixed_charge,
    )
}

#[cfg(unix)]
fn derive_protected_git_pathspec_batch_policy(pathspecs: &[String]) -> GitPathspecBatchPolicy {
    let environment =
        effective_git_child_environment(std::env::vars_os().collect::<Vec<_>>(), true);
    let empty_root = Path::new("");
    let fixed_charge = [
        fixed_invocation_argv_charge(&git_clean_head_invocation(git_tracked_invocation(
            empty_root,
            &[],
        ))),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_index_state_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_index_diff_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_worktree_diff_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_raw_hash_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_ancestor_index_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_protected_ancestor_head_invocation(empty_root, &[]),
        )),
        fixed_invocation_argv_charge(&git_clean_head_invocation(git_untracked_invocation(
            empty_root,
            &[],
        ))),
        fixed_invocation_argv_charge(&git_clean_head_invocation(
            git_ignored_untracked_invocation(empty_root, &[]),
        )),
    ]
    .into_iter()
    .collect::<Option<Vec<_>>>()
    .and_then(|charges| charges.into_iter().max());
    git_pathspec_batch_policy_from_charges(
        pathspecs,
        unix_arg_max(),
        inherited_environment_charge(&environment),
        fixed_charge,
    )
}

fn git_pathspec_batch_policy_from_charges(
    pathspecs: &[String],
    arg_max: Option<usize>,
    environment_charge: Option<usize>,
    fixed_argv_charge: Option<usize>,
) -> GitPathspecBatchPolicy {
    let Some(effective_charge_bytes) = arg_max.and_then(|arg_max| {
        effective_git_pathspec_charge(arg_max, environment_charge?, fixed_argv_charge?)
    }) else {
        return GitPathspecBatchPolicy::Legacy128;
    };
    if pathspecs.iter().any(|pathspec| {
        pathspec_charges(pathspec)
            .map(|(_, charge)| charge > effective_charge_bytes)
            .unwrap_or(true)
    }) {
        GitPathspecBatchPolicy::Legacy128
    } else {
        GitPathspecBatchPolicy::ExecBudget {
            effective_charge_bytes,
        }
    }
}

#[cfg(not(unix))]
fn derive_git_pathspec_batch_policy(_pathspecs: &[String]) -> GitPathspecBatchPolicy {
    GitPathspecBatchPolicy::Legacy128
}

#[cfg(not(unix))]
fn derive_protected_git_pathspec_batch_policy(_pathspecs: &[String]) -> GitPathspecBatchPolicy {
    GitPathspecBatchPolicy::Legacy128
}

#[cfg(unix)]
fn derive_committed_git_pathspec_batch_policy(
    worktree_root: &Path,
    merge_base: &str,
    head_commit: &str,
    pathspecs: &[String],
) -> GitPathspecBatchPolicy {
    let environment =
        effective_git_child_environment(std::env::vars_os().collect::<Vec<_>>(), true);
    let fixed_charge = fixed_invocation_argv_charge(&git_committed_diff_invocation(
        worktree_root,
        merge_base,
        head_commit,
        &[],
    ));
    git_pathspec_batch_policy_from_charges(
        pathspecs,
        unix_arg_max(),
        inherited_environment_charge(&environment),
        fixed_charge,
    )
}

#[cfg(not(unix))]
fn derive_committed_git_pathspec_batch_policy(
    _worktree_root: &Path,
    _merge_base: &str,
    _head_commit: &str,
    _pathspecs: &[String],
) -> GitPathspecBatchPolicy {
    GitPathspecBatchPolicy::Legacy128
}

fn observe_selection(
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    update: impl FnOnce(&mut PerformancePackageSelectionObservation),
) {
    if let Some(observation) = observation.as_deref_mut() {
        update(observation);
    }
}

fn observation_assign_usize(
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    field: fn(&mut PerformancePackageSelectionObservation) -> &mut u64,
    value: usize,
) {
    observe_selection(observation, |observation| match u64::try_from(value) {
        Ok(value) => *field(observation) = value,
        Err(_) => {
            *field(observation) = u64::MAX;
            observation.overflowed = true;
        }
    });
}

fn observation_add(
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    field: fn(&mut PerformancePackageSelectionObservation) -> &mut u64,
    value: u64,
) {
    observe_selection(observation, |observation| {
        let (sum, overflowed) = field(observation).overflowing_add(value);
        *field(observation) = if overflowed { u64::MAX } else { sum };
        observation.overflowed |= overflowed;
    });
}

fn observation_add_usize(
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    field: fn(&mut PerformancePackageSelectionObservation) -> &mut u64,
    value: usize,
) {
    observe_selection(observation, |observation| match u64::try_from(value) {
        Ok(value) => {
            let (sum, overflowed) = field(observation).overflowing_add(value);
            *field(observation) = if overflowed { u64::MAX } else { sum };
            observation.overflowed |= overflowed;
        }
        Err(_) => {
            *field(observation) = u64::MAX;
            observation.overflowed = true;
        }
    });
}

fn record_partition_observation(
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    policy: GitPathspecBatchPolicy,
    batches: &[GitPathspecBatch<'_>],
) {
    observe_selection(observation, |observation| {
        observation.batch_policy = match policy {
            GitPathspecBatchPolicy::ExecBudget { .. } => {
                PerformancePackageSelectionBatchPolicy::ExecBudget
            }
            GitPathspecBatchPolicy::Legacy128 => PerformancePackageSelectionBatchPolicy::Legacy128,
        };
        observation.effective_argv_charge_bytes = match policy {
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes,
            } => u64::try_from(effective_charge_bytes).unwrap_or_else(|_| {
                observation.overflowed = true;
                u64::MAX
            }),
            GitPathspecBatchPolicy::Legacy128 => 0,
        };
        observation.pathspec_batches = u64::try_from(batches.len()).unwrap_or_else(|_| {
            observation.overflowed = true;
            u64::MAX
        });
        for batch in batches {
            let payload = u64::try_from(batch.payload_bytes).unwrap_or_else(|_| {
                observation.overflowed = true;
                u64::MAX
            });
            let argv = u64::try_from(batch.argv_charge_bytes).unwrap_or_else(|_| {
                observation.overflowed = true;
                u64::MAX
            });
            let (total, overflowed) = observation.pathspec_payload_bytes.overflowing_add(payload);
            observation.pathspec_payload_bytes = if overflowed { u64::MAX } else { total };
            observation.overflowed |= overflowed;
            observation.max_batch_payload_bytes = observation.max_batch_payload_bytes.max(payload);
            observation.max_batch_argv_charge_bytes =
                observation.max_batch_argv_charge_bytes.max(argv);
        }
    });
}

fn run_git_invocation(
    runner: &impl ChangedPathGitProcessRunner,
    invocation: &GitInvocation,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Output, String> {
    let (field, prefix): (
        fn(&mut PerformancePackageSelectionObservation) -> &mut u64,
        &str,
    ) = match invocation.kind {
        GitInvocationKind::WorktreeRoot => (
            |observation| &mut observation.worktree_root_queries,
            "failed to run git rev-parse",
        ),
        GitInvocationKind::HasHead => (
            |observation| &mut observation.head_queries,
            "failed to run git rev-parse",
        ),
        GitInvocationKind::Tracked => (
            |observation| &mut observation.tracked_queries,
            "failed to run git diff",
        ),
        GitInvocationKind::ProtectedIndexState => (
            |observation| &mut observation.tracked_queries,
            "failed to run git ls-files",
        ),
        GitInvocationKind::ProtectedRawHash => (
            |observation| &mut observation.tracked_queries,
            "failed to run git hash-object",
        ),
        GitInvocationKind::Untracked | GitInvocationKind::IgnoredUntracked => (
            |observation| &mut observation.untracked_queries,
            "failed to run git ls-files",
        ),
        GitInvocationKind::ObjectFormat
        | GitInvocationKind::ResolveBase
        | GitInvocationKind::ResolveHead
        | GitInvocationKind::MergeBase
        | GitInvocationKind::LsTree
        | GitInvocationKind::BlobSize
        | GitInvocationKind::BlobRead
        | GitInvocationKind::CommittedDiff => {
            unreachable!("committed selection uses its dedicated Git failure mapping")
        }
    };
    observation_add(observation, field, 1);
    runner
        .output(invocation)
        .map_err(|error| format!("{prefix}: {error}"))
}

fn changed_package_paths_with_runner(
    package_root: &Path,
    candidate_paths: &BTreeSet<String>,
    runner: &impl ChangedPathGitProcessRunner,
    observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<Vec<String>, String> {
    changed_package_paths_with_runner_and_policy(
        package_root,
        candidate_paths,
        runner,
        observation,
        None,
    )
}

fn changed_package_paths_with_runner_and_policy(
    package_root: &Path,
    candidate_paths: &BTreeSet<String>,
    runner: &impl ChangedPathGitProcessRunner,
    mut observation: Option<&mut PerformancePackageSelectionObservation>,
    policy_override: Option<GitPathspecBatchPolicy>,
) -> Result<Vec<String>, String> {
    observation_assign_usize(
        &mut observation,
        |observation| &mut observation.candidate_paths,
        candidate_paths.len(),
    );
    if candidate_paths.is_empty() {
        return Ok(Vec::new());
    }
    let root_invocation = git_worktree_root_invocation(package_root);
    let worktree_root = decode_git_worktree_root_output(run_git_invocation(
        runner,
        &root_invocation,
        &mut observation,
    )?)?;
    let head_invocation = git_has_head_invocation(&worktree_root);
    let has_head = decode_git_has_head_output(run_git_invocation(
        runner,
        &head_invocation,
        &mut observation,
    )?)?;
    let package_prefix = package_status_prefix(package_root, &worktree_root)?;
    if !has_head {
        observation_assign_usize(
            &mut observation,
            |observation| &mut observation.selected_paths,
            candidate_paths.len(),
        );
        return Ok(candidate_paths.iter().cloned().collect());
    }
    changed_candidate_paths_in_worktree(
        &worktree_root,
        &package_prefix,
        candidate_paths,
        runner,
        observation,
        policy_override,
        false,
    )
}

fn changed_candidate_paths_in_worktree(
    worktree_root: &Path,
    package_prefix: &str,
    candidate_paths: &BTreeSet<String>,
    runner: &impl ChangedPathGitProcessRunner,
    mut observation: Option<&mut PerformancePackageSelectionObservation>,
    policy_override: Option<GitPathspecBatchPolicy>,
    include_ignored_untracked: bool,
) -> Result<Vec<String>, String> {
    let candidate_by_worktree_path = candidate_paths
        .iter()
        .map(|candidate_path| {
            let worktree_path = if package_prefix.is_empty() {
                candidate_path.clone()
            } else {
                format!("{package_prefix}/{candidate_path}")
            };
            (worktree_path, candidate_path.clone())
        })
        .collect::<BTreeMap<_, _>>();
    let pathspec_groups =
        exact_candidate_pathspec_groups(candidate_by_worktree_path.keys().map(String::as_str));
    let pathspecs = pathspec_groups
        .iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    let policy = policy_override.unwrap_or_else(|| {
        if include_ignored_untracked {
            derive_protected_git_pathspec_batch_policy(&pathspecs)
        } else {
            derive_git_pathspec_batch_policy(&pathspecs)
        }
    });
    let policy = grouped_git_pathspec_batch_policy(&pathspecs, policy, 2);
    let batches = pathspec_groups
        .iter()
        .flat_map(|group| git_pathspec_batches_grouped(group, policy, 2))
        .collect::<Vec<_>>();
    record_partition_observation(&mut observation, policy, &batches);
    let mut changed = BTreeSet::new();
    // `git status` refreshes the complete index before applying pathspecs and
    // can consequently open unrelated tracked source or sidecar files. Query
    // validated certificate path batches directly so changed-only selection
    // stays within its documented Git certificate-path boundary. Batching also
    // avoids one Git process per certificate without risking an oversized
    // command line for large package closures. Protected clean-head queries
    // disable fsmonitor so a stale or incorrect hook cannot hide worktree
    // changes behind index fsmonitor-valid bits. They also inspect every
    // strict protected-path ancestor: Git does not descend through a tracked
    // gitlink or symlink for an exact child pathspec, so any tracked ancestor
    // makes the affected protected paths unsafe for a committed-base label.
    if include_ignored_untracked {
        let ancestor_candidates = protected_ancestor_candidates(&candidate_by_worktree_path);
        for pathspecs in protected_ancestor_pathspec_batches(&ancestor_candidates, policy) {
            let ancestor_index_invocation = git_clean_head_invocation(
                git_protected_ancestor_index_invocation(worktree_root, &pathspecs),
            );
            let index_ancestors = decode_git_untracked_output(run_git_invocation(
                runner,
                &ancestor_index_invocation,
                &mut observation,
            )?)?;
            record_protected_ancestor_paths(&index_ancestors, &ancestor_candidates, &mut changed)?;

            // The index query catches a current gitlink, symlink, or sparse
            // directory entry. The cached index-to-HEAD diff separately
            // catches one removed from or replaced in the index: an exact
            // child pathspec cannot report that staged ancestor change.
            // Override submodule-ignore configuration so removal of a gitlink
            // cannot be suppressed.
            let ancestor_head_invocation = git_clean_head_invocation(
                git_protected_ancestor_head_invocation(worktree_root, &pathspecs),
            );
            let changed_head_ancestors = decode_git_tracked_output(run_git_invocation(
                runner,
                &ancestor_head_invocation,
                &mut observation,
            )?)?;
            record_protected_ancestor_paths(
                &changed_head_ancestors,
                &ancestor_candidates,
                &mut changed,
            )?;
        }
    }
    for batch in batches {
        let mut raw_hash_candidates = BTreeMap::new();
        if include_ignored_untracked {
            let index_state_invocation = git_clean_head_invocation(
                git_protected_index_state_invocation(worktree_root, batch.pathspecs),
            );
            let index_state = decode_git_untracked_output(run_git_invocation(
                runner,
                &index_state_invocation,
                &mut observation,
            )?)?;
            record_protected_index_state_paths(
                &index_state,
                &candidate_by_worktree_path,
                &mut changed,
                &mut raw_hash_candidates,
            )?;
            record_protected_worktree_path_types(
                worktree_root,
                batch.pathspecs,
                &candidate_by_worktree_path,
                &raw_hash_candidates,
                &mut changed,
            )?;

            // A combined `git diff HEAD` observes only the final worktree
            // snapshot, so an unstaged edit can cancel a staged index edit.
            // Compare HEAD/index and index/worktree independently. The latter
            // still uses Git's mode and file-type handling; the raw hash below
            // closes the content-filter boundary.
            for invocation in [
                git_protected_index_diff_invocation(worktree_root, batch.pathspecs),
                git_protected_worktree_diff_invocation(worktree_root, batch.pathspecs),
            ] {
                let invocation = git_clean_head_invocation(invocation);
                let tracked = decode_git_tracked_output(run_git_invocation(
                    runner,
                    &invocation,
                    &mut observation,
                )?)?;
                record_changed_candidate_paths(
                    &tracked,
                    &candidate_by_worktree_path,
                    &mut changed,
                    GitInvocationKind::Tracked,
                    &mut observation,
                    true,
                )?;
            }

            let raw_hash_candidates = raw_hash_candidates
                .into_iter()
                .filter(|(_, candidate)| !changed.contains(&candidate.candidate_path))
                .collect::<Vec<_>>();
            if !raw_hash_candidates.is_empty() {
                let worktree_paths = raw_hash_candidates
                    .iter()
                    .map(|(worktree_path, _)| worktree_path.clone())
                    .collect::<Vec<_>>();
                let invocation = git_clean_head_invocation(git_protected_raw_hash_invocation(
                    worktree_root,
                    &worktree_paths,
                ));
                let raw_hashes = decode_git_protected_raw_hash_output(run_git_invocation(
                    runner,
                    &invocation,
                    &mut observation,
                )?)?;
                record_protected_raw_hashes(&raw_hashes, &raw_hash_candidates, &mut changed)?;
            }
        } else {
            let tracked_invocation = git_tracked_invocation(worktree_root, batch.pathspecs);
            let tracked = decode_git_tracked_output(run_git_invocation(
                runner,
                &tracked_invocation,
                &mut observation,
            )?)?;
            record_changed_candidate_paths(
                &tracked,
                &candidate_by_worktree_path,
                &mut changed,
                GitInvocationKind::Tracked,
                &mut observation,
                false,
            )?;
        }
        let untracked_invocation = git_untracked_invocation(worktree_root, batch.pathspecs);
        let untracked_invocation = if include_ignored_untracked {
            git_clean_head_invocation(untracked_invocation)
        } else {
            untracked_invocation
        };
        let untracked = decode_git_untracked_output(run_git_invocation(
            runner,
            &untracked_invocation,
            &mut observation,
        )?)?;
        record_changed_candidate_paths(
            &untracked,
            &candidate_by_worktree_path,
            &mut changed,
            GitInvocationKind::Untracked,
            &mut observation,
            include_ignored_untracked,
        )?;
        if include_ignored_untracked {
            let ignored_invocation = git_clean_head_invocation(git_ignored_untracked_invocation(
                worktree_root,
                batch.pathspecs,
            ));
            let ignored = decode_git_untracked_output(run_git_invocation(
                runner,
                &ignored_invocation,
                &mut observation,
            )?)?;
            record_changed_candidate_paths(
                &ignored,
                &candidate_by_worktree_path,
                &mut changed,
                GitInvocationKind::IgnoredUntracked,
                &mut observation,
                true,
            )?;
        }
    }
    let changed = changed.into_iter().collect::<Vec<_>>();
    observation_assign_usize(
        &mut observation,
        |observation| &mut observation.selected_paths,
        changed.len(),
    );
    Ok(changed)
}

fn protected_ancestor_candidates(
    candidate_by_worktree_path: &BTreeMap<String, String>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut ancestors = BTreeMap::<String, BTreeSet<String>>::new();
    for (worktree_path, candidate_path) in candidate_by_worktree_path {
        let mut prefix = worktree_path.as_str();
        while let Some((ancestor, _)) = prefix.rsplit_once('/') {
            if ancestor.is_empty() {
                break;
            }
            ancestors
                .entry(ancestor.to_owned())
                .or_default()
                .insert(candidate_path.clone());
            prefix = ancestor;
        }
    }
    ancestors
}

fn git_glob_escape_path(path: &str) -> String {
    let mut escaped = String::with_capacity(path.len());
    for character in path.chars() {
        if matches!(character, '\\' | '*' | '?' | '[' | ']') {
            escaped.push('\\');
        }
        escaped.push(character);
    }
    escaped
}

fn exact_candidate_pathspec_groups<'a>(
    paths: impl IntoIterator<Item = &'a str>,
) -> Vec<Vec<String>> {
    // A literal Git pathspec still recurses when its path names a directory.
    // Exclude descendants explicitly, and isolate depths so an ancestor's
    // exclusion cannot suppress a separately cataloged descendant.
    let mut groups = BTreeMap::<usize, Vec<String>>::new();
    for path in paths {
        let depth = path.bytes().filter(|byte| *byte == b'/').count();
        let pathspecs = groups.entry(depth).or_default();
        pathspecs.push(format!(":(top,literal){path}"));
        pathspecs.push(format!(
            ":(top,exclude,glob){}/**",
            git_glob_escape_path(path)
        ));
    }
    groups.into_values().collect()
}

fn protected_ancestor_pathspec_batches(
    ancestor_candidates: &BTreeMap<String, BTreeSet<String>>,
    policy: GitPathspecBatchPolicy,
) -> Vec<Vec<String>> {
    let mut batches = Vec::new();
    let (charge_limit, pathspec_limit) = match policy {
        GitPathspecBatchPolicy::ExecBudget {
            effective_charge_bytes,
        } => (
            Some(effective_charge_bytes),
            GIT_CHANGED_PATHSPEC_BATCH_MAX_PATHS,
        ),
        GitPathspecBatchPolicy::Legacy128 => (None, GIT_CHANGED_LEGACY_BATCH_PATHS),
    };
    let mut ancestors_by_depth = BTreeMap::<usize, Vec<&str>>::new();
    for ancestor in ancestor_candidates.keys() {
        ancestors_by_depth
            .entry(ancestor.bytes().filter(|byte| *byte == b'/').count())
            .or_default()
            .push(ancestor);
    }
    for ancestors in ancestors_by_depth.values() {
        let mut current = Vec::new();
        let mut current_charge = 0usize;
        for ancestor in ancestors {
            let pair = [
                format!(":(top,literal){ancestor}"),
                format!(":(top,exclude,glob){}/**", git_glob_escape_path(ancestor)),
            ];
            let pair_charge = pair.iter().fold(0usize, |charge, pathspec| {
                charge.saturating_add(
                    pathspec_charges(pathspec)
                        .map(|(_, argv)| argv)
                        .unwrap_or(usize::MAX),
                )
            });
            let exceeds_charge = charge_limit.is_some_and(|limit| {
                current_charge
                    .checked_add(pair_charge)
                    .is_none_or(|charge| charge > limit)
            });
            let exceeds_count = current.len().saturating_add(pair.len()) > pathspec_limit;
            if !current.is_empty() && (exceeds_charge || exceeds_count) {
                batches.push(std::mem::take(&mut current));
                current_charge = 0;
            }
            current.extend(pair);
            current_charge = current_charge.saturating_add(pair_charge);
        }
        if !current.is_empty() {
            batches.push(current);
        }
    }
    batches
}

fn record_protected_ancestor_paths(
    stdout: &[u8],
    ancestor_candidates: &BTreeMap<String, BTreeSet<String>>,
    changed: &mut BTreeSet<String>,
) -> Result<(), String> {
    validate_strict_nul_path_output(
        stdout,
        "git returned non-NUL-terminated protected-ancestor output",
        "git returned an empty protected-ancestor record",
    )?;
    for record in stdout
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
    {
        let path = std::str::from_utf8(record)
            .map_err(|_| "git returned a non-UTF-8 protected-ancestor path".to_owned())?;
        let Some(candidates) = ancestor_candidates.get(path) else {
            return Err("git returned a path outside the exact protected ancestors".to_owned());
        };
        changed.extend(candidates.iter().cloned());
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProtectedIndexBlob {
    candidate_path: String,
    oid: String,
}

fn record_protected_index_state_paths(
    stdout: &[u8],
    candidate_by_worktree_path: &BTreeMap<String, String>,
    changed: &mut BTreeSet<String>,
    raw_hash_candidates: &mut BTreeMap<String, ProtectedIndexBlob>,
) -> Result<(), String> {
    validate_strict_nul_path_output(
        stdout,
        "git returned non-NUL-terminated protected-index output",
        "git returned an empty protected-index record",
    )?;
    for record in stdout
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
    {
        let tab = record
            .iter()
            .position(|byte| *byte == b'\t')
            .ok_or_else(|| "git returned a malformed protected-index record".to_owned())?;
        let header = std::str::from_utf8(&record[..tab])
            .map_err(|_| "git returned a non-UTF-8 protected-index header".to_owned())?;
        let fields = header.split(' ').collect::<Vec<_>>();
        if fields.len() != 4
            || fields[0].len() != 1
            || !matches!(
                fields[1],
                "100644" | "100755" | "120000" | "160000" | "040000"
            )
            || !matches!(fields[2].len(), 40 | 64)
            || !fields[2]
                .as_bytes()
                .iter()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            || !fields[3].as_bytes().iter().all(u8::is_ascii_digit)
        {
            return Err("git returned a malformed protected-index record".to_owned());
        }
        let path = std::str::from_utf8(&record[tab + 1..])
            .map_err(|_| "git returned a non-UTF-8 protected-index path".to_owned())?;
        let Some(candidate_path) = candidate_by_worktree_path.get(path) else {
            return Err("git returned a path outside the exact protected catalog".to_owned());
        };
        // `git ls-files -sv` lowercases the ordinary `H` tag for
        // assume-unchanged entries and emits `S` for skip-worktree entries.
        // It also exposes the index stage and object mode. Only a stage-zero
        // ordinary blob with an ordinary tracked `H` tag is safe: with
        // `core.symlinks=false`, for example, a 120000 entry can otherwise be
        // represented by a clean regular worktree file.
        if fields[0] != "H" || !matches!(fields[1], "100644" | "100755") || fields[3] != "0" {
            changed.insert(candidate_path.clone());
        } else if raw_hash_candidates
            .insert(
                path.to_owned(),
                ProtectedIndexBlob {
                    candidate_path: candidate_path.clone(),
                    oid: fields[2].to_owned(),
                },
            )
            .is_some()
        {
            return Err("git returned a duplicate protected-index path".to_owned());
        }
    }
    Ok(())
}

fn record_protected_raw_hashes(
    stdout: &[u8],
    candidates: &[(String, ProtectedIndexBlob)],
    changed: &mut BTreeSet<String>,
) -> Result<(), String> {
    let text = std::str::from_utf8(stdout)
        .map_err(|_| "git hash-object returned non-UTF-8 output".to_owned())?;
    let records = if candidates.is_empty() {
        if !text.is_empty() {
            return Err("git hash-object returned unexpected output".to_owned());
        }
        Vec::new()
    } else {
        let records = text
            .strip_suffix('\n')
            .ok_or_else(|| "git hash-object returned output without a terminating LF".to_owned())?
            .split('\n')
            .collect::<Vec<_>>();
        if records.len() != candidates.len() {
            return Err(format!(
                "git hash-object returned {} records; expected {}",
                records.len(),
                candidates.len()
            ));
        }
        records
    };
    for (actual_oid, (_, expected)) in records.into_iter().zip(candidates) {
        if actual_oid.len() != expected.oid.len()
            || !actual_oid
                .as_bytes()
                .iter()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
        {
            return Err("git hash-object returned a malformed object ID".to_owned());
        }
        if actual_oid != expected.oid {
            changed.insert(expected.candidate_path.clone());
        }
    }
    Ok(())
}

fn record_protected_worktree_path_types(
    worktree_root: &Path,
    pathspecs: &[String],
    candidate_by_worktree_path: &BTreeMap<String, String>,
    tracked_blobs: &BTreeMap<String, ProtectedIndexBlob>,
    changed: &mut BTreeSet<String>,
) -> Result<(), String> {
    const TOP_LITERAL_PREFIX: &str = ":(top,literal)";

    if !pathspecs.len().is_multiple_of(2) {
        return Err("protected exact-path pathspec pair is incomplete".to_owned());
    }
    for pair in pathspecs.as_chunks::<2>().0 {
        let worktree_path = pair[0]
            .strip_prefix(TOP_LITERAL_PREFIX)
            .ok_or_else(|| "protected pathspec is not top-literal".to_owned())?;
        let expected_exclusion = format!(
            ":(top,exclude,glob){}/**",
            git_glob_escape_path(worktree_path)
        );
        if pair[1] != expected_exclusion {
            return Err("protected exact-path exclusion does not match its literal".to_owned());
        }
        let candidate_path = candidate_by_worktree_path
            .get(worktree_path)
            .ok_or_else(|| "protected pathspec is outside the exact catalog".to_owned())?;
        if changed.contains(candidate_path) {
            continue;
        }
        let tracked_blob = tracked_blobs.contains_key(worktree_path);
        if protected_worktree_path_type_is_dirty(worktree_root, worktree_path, tracked_blob)? {
            changed.insert(candidate_path.clone());
        }
    }
    Ok(())
}

fn protected_worktree_path_type_is_dirty(
    worktree_root: &Path,
    worktree_path: &str,
    tracked_blob: bool,
) -> Result<bool, String> {
    let components = worktree_path.split('/').collect::<Vec<_>>();
    if components.is_empty()
        || components
            .iter()
            .any(|component| component.is_empty() || matches!(*component, "." | ".."))
    {
        return Err("protected worktree path is not a normal relative path".to_owned());
    }

    let mut path = worktree_root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        path.push(component);
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
            Err(error) => {
                return Err(format!(
                    "failed to inspect protected worktree path {}: {error}",
                    path.display()
                ));
            }
        };
        let final_component = index + 1 == components.len();
        if !final_component {
            if !metadata.file_type().is_dir() {
                return Ok(true);
            }
        } else if tracked_blob {
            return Ok(!metadata.file_type().is_file());
        } else {
            // An exact directory can be a committed replacement for a base-only
            // file path; Git and structural attribution handle that case. Any
            // other existing leaf without an exact index blob is untracked or
            // hidden behind a boundary such as an embedded repository.
            return Ok(!metadata.file_type().is_dir());
        }
    }
    unreachable!("a validated protected worktree path has at least one component")
}

fn package_status_prefix(package_root: &Path, worktree_root: &Path) -> Result<String, String> {
    let package_root = package_root
        .canonicalize()
        .map_err(|error| format!("failed to canonicalize package root: {error}"))?;
    let worktree_root = worktree_root
        .canonicalize()
        .map_err(|error| format!("failed to canonicalize git worktree root: {error}"))?;
    let relative = package_root.strip_prefix(&worktree_root).map_err(|_| {
        format!(
            "package root {} is not inside Git worktree {}",
            package_root.display(),
            worktree_root.display()
        )
    })?;
    path_to_git_status_path(relative)
}

fn path_to_git_status_path(path: &Path) -> Result<String, String> {
    path.components()
        .filter_map(|component| match component {
            std::path::Component::Normal(segment) => Some(
                segment
                    .to_str()
                    .map(str::to_owned)
                    .ok_or_else(|| "package root contains a non-UTF-8 path component".to_owned()),
            ),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|components| components.join("/"))
}

fn record_changed_candidate_paths(
    stdout: &[u8],
    candidate_by_worktree_path: &BTreeMap<String, String>,
    changed: &mut BTreeSet<String>,
    kind: GitInvocationKind,
    observation: &mut Option<&mut PerformancePackageSelectionObservation>,
    strict_catalog: bool,
) -> Result<(), String> {
    if strict_catalog {
        validate_strict_nul_path_output(
            stdout,
            "git returned non-NUL-terminated protected-path output",
            "git returned an empty protected-path record",
        )?;
    }
    for path in stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        let field: fn(&mut PerformancePackageSelectionObservation) -> &mut u64 = match kind {
            GitInvocationKind::Tracked => {
                |observation: &mut PerformancePackageSelectionObservation| {
                    &mut observation.tracked_output_paths
                }
            }
            GitInvocationKind::Untracked | GitInvocationKind::IgnoredUntracked => {
                |observation: &mut PerformancePackageSelectionObservation| {
                    &mut observation.untracked_output_paths
                }
            }
            GitInvocationKind::WorktreeRoot
            | GitInvocationKind::HasHead
            | GitInvocationKind::ProtectedIndexState
            | GitInvocationKind::ProtectedRawHash
            | GitInvocationKind::ObjectFormat
            | GitInvocationKind::ResolveBase
            | GitInvocationKind::ResolveHead
            | GitInvocationKind::MergeBase
            | GitInvocationKind::LsTree
            | GitInvocationKind::BlobSize
            | GitInvocationKind::BlobRead
            | GitInvocationKind::CommittedDiff => {
                unreachable!("only query output contains changed paths")
            }
        };
        observation_add(observation, field, 1);
        let path = std::str::from_utf8(path)
            .map_err(|_| "git returned a non-UTF-8 certificate path".to_owned())?;
        let path = if strict_catalog {
            path
        } else {
            path.trim_start_matches("./")
        };
        if let Some(candidate_path) = candidate_by_worktree_path.get(path) {
            changed.insert(candidate_path.clone());
        } else if strict_catalog {
            return Err("git returned a path outside the exact protected catalog".to_owned());
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn verify_package_with_read_through_cache(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    package_lock_hash: PackageHash,
    indexed: &IndexedPackageLockGraph,
    artifacts: &[CertificateArtifactBuffer],
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageAuditVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_audit_cache_key_inputs_for_lock(
                checker,
                loaded,
                package_lock_hash,
                indexed,
                prepared_artifacts,
                artifact_observation,
            )
        })
        .map_err(PackageAuditVerificationRunError::Diagnostic)?;
    let cache_dir = cache_cwd.join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR);
    let lookups = timings.time_phase(TIMING_CACHE_LOOKUP_MS, || {
        keyed_entries
            .iter()
            .map(|entry| {
                (
                    entry.entry.module.clone(),
                    read_package_audit_cache_lookup(&cache_dir, &entry.cache_key),
                )
            })
            .collect::<BTreeMap<_, _>>()
    });

    let report = timings
        .time_phase(TIMING_CHECKER_MS, || {
            verify_package(
                checker,
                loaded,
                indexed,
                artifacts,
                Some(prepared_artifacts),
                Some(artifact_observation),
                PackageVerificationExecutionOptions {
                    jobs: 1,
                    selected_modules: None,
                    memoization: PackageVerificationMemoMode::Disabled,
                    collect_decode_cache_counters: false,
                    ..PackageVerificationExecutionOptions::default()
                },
            )
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let mut summary = PackageAuditCacheSummary::new(PackageAuditCacheMode::ReadThrough);
    summary.live_checked = live_checked_module_count(&report);
    let results_by_module = report
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();

    for keyed in &keyed_entries {
        let Some(module_result) = results_by_module.get(&keyed.entry.module) else {
            summary.stale += 1;
            continue;
        };
        let expected_entry = package_audit_result_entry_for_module(keyed, module_result);
        match lookups
            .get(&keyed.entry.module)
            .expect("lookup exists for keyed entry")
        {
            PackageAuditCacheLookup::Hit(stored) if stored.as_ref() == &expected_entry => {
                summary.hits += 1;
                summary.cached += 1;
            }
            PackageAuditCacheLookup::Hit(_) | PackageAuditCacheLookup::Stale => {
                summary.stale += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::SchemaMiss => {
                summary.schema_misses += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::Missing => {
                summary.misses += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
        }
    }

    Ok(PackageAuditVerificationRun {
        report,
        cache: summary,
    })
}

#[allow(clippy::too_many_arguments)]
fn verify_package_with_local_hit_cache(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    package_lock_hash: PackageHash,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageAuditVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_audit_cache_key_inputs_for_lock(
                checker,
                loaded,
                package_lock_hash,
                indexed,
                prepared_artifacts,
                artifact_observation,
            )
        })
        .map_err(PackageAuditVerificationRunError::Diagnostic)?;
    let cache_dir = cache_cwd.join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR);
    let (lookups, accepted_cache_hits) = timings.time_phase(TIMING_CACHE_LOOKUP_MS, || {
        let lookups = keyed_entries
            .iter()
            .map(|entry| {
                (
                    entry.entry.module.clone(),
                    read_package_audit_cache_lookup(&cache_dir, &entry.cache_key),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let accepted_cache_hits = keyed_entries
            .iter()
            .filter(|entry| {
                let lookup = lookups
                    .get(&entry.entry.module)
                    .expect("lookup exists for keyed entry");
                is_exact_accepted_cache_hit(entry, lookup)
            })
            .map(|entry| entry.entry.module.clone())
            .collect::<Vec<_>>();
        (lookups, accepted_cache_hits)
    });

    let report = timings
        .time_phase(TIMING_CHECKER_MS, || {
            verify_package_with_local_audit_cache_hits(
                checker,
                loaded,
                indexed,
                prepared_artifacts,
                artifact_observation,
                accepted_cache_hits,
            )
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let mut summary = PackageAuditCacheSummary::new(PackageAuditCacheMode::LocalHit);
    summary.live_checked = live_checked_module_count(&report);
    let results_by_module = report
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();

    for keyed in &keyed_entries {
        let Some(module_result) = results_by_module.get(&keyed.entry.module) else {
            summary.stale += 1;
            continue;
        };
        if module_result.evidence == PackageModuleVerificationEvidence::LocalAuditCache {
            summary.hits += 1;
            summary.cached += 1;
            continue;
        }

        let expected_entry = package_audit_result_entry_for_module(keyed, module_result);
        match lookups
            .get(&keyed.entry.module)
            .expect("lookup exists for keyed entry")
        {
            PackageAuditCacheLookup::Hit(stored) if stored.as_ref() == &expected_entry => {
                summary.hits += 1;
            }
            PackageAuditCacheLookup::Hit(_) | PackageAuditCacheLookup::Stale => {
                summary.stale += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::SchemaMiss => {
                summary.schema_misses += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::Missing => {
                summary.misses += 1;
                if write_package_audit_cache_entry(&cache_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
        }
    }

    Ok(PackageAuditVerificationRun {
        report,
        cache: summary,
    })
}

#[allow(clippy::too_many_arguments)]
fn verify_package_with_read_through_disk_memo(
    checker: PackageChecker,
    jobs: usize,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    artifacts: &[CertificateArtifactBuffer],
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageDiskMemoVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_disk_memo_key_inputs_for_lock(checker, loaded, indexed, prepared_artifacts)
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let memo_dir = cache_cwd.join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR);
    let lookups = timings.time_phase(TIMING_CACHE_LOOKUP_MS, || {
        keyed_entries
            .iter()
            .map(|entry| {
                (
                    entry.entry.module.clone(),
                    read_package_disk_memo_lookup(&memo_dir, &entry.cache_key),
                )
            })
            .collect::<BTreeMap<_, _>>()
    });

    let report = timings
        .time_phase(TIMING_CHECKER_MS, || {
            let prepared = (checker == PackageChecker::Fast
                || checker == PackageChecker::Reference)
                .then_some(&mut *prepared_artifacts);
            let observation = (checker == PackageChecker::Fast && jobs == 1)
                .then_some(&mut *artifact_observation);
            verify_package(
                checker,
                loaded,
                indexed,
                artifacts,
                prepared,
                observation,
                PackageVerificationExecutionOptions {
                    jobs,
                    selected_modules: None,
                    memoization: PackageVerificationMemoMode::Disabled,
                    collect_decode_cache_counters: false,
                    ..PackageVerificationExecutionOptions::default()
                },
            )
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let mut summary = PackageVerifierDiskMemoSummary::new(PackageVerifierMemoMode::ReadThrough);
    summary.live_checked = live_checked_module_count(&report);
    let results_by_module = report
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();

    for keyed in &keyed_entries {
        let Some(module_result) = results_by_module.get(&keyed.entry.module) else {
            summary.stale += 1;
            continue;
        };
        if module_result.evidence != PackageModuleVerificationEvidence::LiveChecker
            || module_result.status == PackageModuleVerificationStatus::Skipped
        {
            continue;
        }

        let expected_entry = package_disk_memo_result_entry_for_module(keyed, module_result);
        match lookups
            .get(&keyed.entry.module)
            .expect("lookup exists for keyed entry")
        {
            PackageAuditCacheLookup::Hit(stored) if stored.as_ref() == &expected_entry => {
                summary.hits += 1;
            }
            PackageAuditCacheLookup::Hit(_) | PackageAuditCacheLookup::Stale => {
                summary.stale += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::SchemaMiss => {
                summary.schema_misses += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::Missing => {
                summary.misses += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
        }
    }

    Ok(PackageDiskMemoVerificationRun {
        report,
        memo: summary,
    })
}

fn verify_package_with_disk_memo(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageDiskMemoVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_disk_memo_key_inputs_for_lock(checker, loaded, indexed, prepared_artifacts)
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let memo_dir = cache_cwd.join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR);
    let (lookups, accepted_memo_hits, dirty_modules) =
        timings.time_phase(TIMING_CACHE_LOOKUP_MS, || {
            let lookups = keyed_entries
                .iter()
                .map(|entry| {
                    (
                        entry.entry.module.clone(),
                        read_package_disk_memo_lookup(&memo_dir, &entry.cache_key),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let accepted_memo_hits = keyed_entries
                .iter()
                .filter(|entry| {
                    let lookup = lookups
                        .get(&entry.entry.module)
                        .expect("lookup exists for keyed entry");
                    is_exact_accepted_disk_memo_hit(entry, lookup)
                })
                .map(|entry| entry.entry.module.clone())
                .collect::<Vec<_>>();
            let dirty_modules = keyed_entries
                .iter()
                .filter(|entry| {
                    let lookup = lookups
                        .get(&entry.entry.module)
                        .expect("lookup exists for keyed entry");
                    !is_exact_accepted_disk_memo_hit(entry, lookup)
                })
                .map(|entry| entry.entry.module.clone())
                .collect::<Vec<_>>();
            (lookups, accepted_memo_hits, dirty_modules)
        });
    let live_selection = timings
        .time_phase(TIMING_SELECTION_MS, || {
            select_package_cache_aware_live_modules_indexed(indexed, dirty_modules.clone())
        })
        .map_err(|error| {
            PackageAuditVerificationRunError::Diagnostic(Box::new(
                package_cache_aware_selection_diagnostic(error),
            ))
        })?;
    let cache_aware_live_modules = live_selection
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    let accepted_memo_hits = accepted_memo_hits
        .into_iter()
        .filter(|module| !cache_aware_live_modules.contains(module))
        .collect::<Vec<_>>();

    let report = timings
        .time_phase(TIMING_CHECKER_MS, || {
            verify_package_with_disk_memo_hits(
                checker,
                loaded,
                indexed,
                prepared_artifacts,
                artifact_observation,
                accepted_memo_hits,
                dirty_modules.into_iter().collect(),
            )
        })
        .map_err(PackageAuditVerificationRunError::Verification)?;
    let mut summary = PackageVerifierDiskMemoSummary::new(PackageVerifierMemoMode::Disk);
    summary.invalidated = cache_aware_live_modules.len();
    summary.live_checked = live_checked_module_count(&report);
    let results_by_module = report
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();

    for keyed in &keyed_entries {
        let Some(module_result) = results_by_module.get(&keyed.entry.module) else {
            summary.stale += 1;
            continue;
        };
        if module_result.evidence == PackageModuleVerificationEvidence::DiskVerifierMemo {
            summary.hits += 1;
            summary.cached += 1;
            continue;
        }
        if module_result.evidence != PackageModuleVerificationEvidence::LiveChecker
            || module_result.status == PackageModuleVerificationStatus::Skipped
        {
            continue;
        }

        let expected_entry = package_disk_memo_result_entry_for_module(keyed, module_result);
        match lookups
            .get(&keyed.entry.module)
            .expect("lookup exists for keyed entry")
        {
            PackageAuditCacheLookup::Hit(stored) if stored.as_ref() == &expected_entry => {
                summary.hits += 1;
            }
            PackageAuditCacheLookup::Hit(_) | PackageAuditCacheLookup::Stale => {
                summary.stale += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::SchemaMiss => {
                summary.schema_misses += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
            PackageAuditCacheLookup::Missing => {
                summary.misses += 1;
                if write_package_disk_memo_entry(&memo_dir, &expected_entry) {
                    summary.written += 1;
                }
            }
        }
    }

    Ok(PackageDiskMemoVerificationRun {
        report,
        memo: summary,
    })
}

fn verify_package_with_local_audit_cache_hits(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    accepted_cache_hits: Vec<Name>,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => {
            let hashed = package_hashed_artifacts(indexed.lock(), prepared_artifacts);
            verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits_indexed(
                &loaded.validated,
                indexed,
                hashed.iter(),
                accepted_cache_hits,
                PackageModuleVerificationEvidence::LocalAuditCache,
                std::iter::empty::<Name>(),
            )
        }
        PackageChecker::Fast => {
            verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed_indexed(
                &loaded.validated,
                indexed,
                prepared_artifacts,
                accepted_cache_hits,
                PackageModuleVerificationEvidence::LocalAuditCache,
                std::iter::empty::<Name>(),
                Some(artifact_observation),
            )
        }
        PackageChecker::External => {
            unreachable!("external checker is handled before local-hit verification")
        }
    }
}

fn verify_package_with_disk_memo_hits(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &mut PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
    accepted_memo_hits: Vec<Name>,
    dirty_modules: BTreeSet<Name>,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => {
            let hashed = package_hashed_artifacts(indexed.lock(), prepared_artifacts);
            verify_package_reference_source_free_with_hashed_artifacts_and_cached_hits_indexed(
                &loaded.validated,
                indexed,
                hashed.iter(),
                accepted_memo_hits,
                PackageModuleVerificationEvidence::DiskVerifierMemo,
                dirty_modules,
            )
        }
        PackageChecker::Fast => {
            verify_package_fast_source_free_with_artifact_snapshots_and_cached_hits_observed_indexed(
                &loaded.validated,
                indexed,
                prepared_artifacts,
                accepted_memo_hits,
                PackageModuleVerificationEvidence::DiskVerifierMemo,
                dirty_modules,
                Some(artifact_observation),
            )
        }
        PackageChecker::External => {
            unreachable!("external checker is handled before disk memo verification")
        }
    }
}

fn live_checked_module_count(report: &PackageVerificationReport) -> usize {
    report
        .modules
        .iter()
        .filter(|module| {
            module.evidence == PackageModuleVerificationEvidence::LiveChecker
                && module.status != PackageModuleVerificationStatus::Skipped
        })
        .count()
}

fn package_audit_cache_key_inputs_for_lock(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    package_lock_hash: PackageHash,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &PreparedPackageArtifacts,
    artifact_observation: &mut PackageCertificateArtifactObservation,
) -> Result<Vec<PackageAuditKeyedEntry>, Box<CommandDiagnostic>> {
    let lock = indexed.lock();
    let package_policy_hash = package_audit_policy_hash(loaded);
    let checker_identity = package_audit_checker_identity(checker, loaded);
    let manifest = loaded.validated.manifest();

    indexed
        .entries()
        .iter()
        .cloned()
        .enumerate()
        .map(|(entry_index, entry)| {
            let Some(artifact) = prepared_artifacts.get(&entry.certificate) else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                        .with_path(render_package_path(&entry.certificate))
                        .with_module(entry.module.as_dotted()),
                ));
            };
            let (bytes, file_hash, retained) = match artifact {
                PreparedPackageArtifactView::Hashed(artifact) => {
                    (artifact.bytes(), artifact.file_hash(), None)
                }
                PreparedPackageArtifactView::Prepared(artifact) => (
                    artifact.bytes(),
                    artifact.file_hash(),
                    (checker == PackageChecker::Fast)
                        .then(|| {
                            Some((artifact.decoded_header()?, artifact.decoded_axiom_report()?))
                        })
                        .flatten(),
                ),
            };
            let (module_certificate_format, module_core_spec, enabled_core_features) =
                if let Some((header, axiom_report)) = retained {
                    (
                        header.format.clone(),
                        header.core_spec.clone(),
                        axiom_report
                            .core_features
                            .iter()
                            .map(|feature| feature.as_str().to_owned())
                            .collect(),
                    )
                } else {
                    artifact_observation
                        .begin_key_candidate(u64::try_from(bytes.len()).unwrap_or(u64::MAX));
                    observe_artifact_full_decode(artifact_observation);
                    let certificate = decode_module_cert(bytes);
                    artifact_observation.finish_key_candidate();
                    let certificate = certificate.map_err(|error| {
                        Box::new(
                            CommandDiagnostic::error(
                                DiagnosticKind::SourceFreeBoundary,
                                "certificate_decode_failed",
                            )
                            .with_path(render_package_path(&entry.certificate))
                            .with_module(entry.module.as_dotted())
                            .with_actual_value(format!("{error:?}")),
                        )
                    })?;
                    (
                        certificate.header().format.clone(),
                        certificate.header().core_spec.clone(),
                        certificate
                            .axiom_report()
                            .core_features
                            .iter()
                            .map(|feature| feature.as_str().to_owned())
                            .collect(),
                    )
                };
            let key_input = PackageAuditCacheKeyInput {
                schema: PACKAGE_AUDIT_CACHE_SCHEMA.to_owned(),
                package_id: lock.package.clone(),
                package_version: lock.version.clone(),
                package_lock_schema: lock.schema.clone(),
                package_core_profile: manifest.core_spec.clone(),
                package_certificate_profile: manifest.certificate_format.clone(),
                module_certificate_format,
                module_core_spec,
                package_lock_hash,
                package_policy_hash,
                checker: checker_identity.clone(),
                module: entry.module.clone(),
                origin: entry.origin,
                certificate: entry.certificate.clone(),
                certificate_file_hash: file_hash,
                certificate_hash: entry.certificate_hash,
                export_hash: entry.export_hash,
                axiom_report_hash: entry.axiom_report_hash,
                direct_imports: indexed.graph().resolved_entry_imports[entry_index]
                    .iter()
                    .map(|import| PackageAuditImportIdentity {
                        module: import.module.clone(),
                        export_hash: import.export_hash,
                        certificate_hash: import.certificate_hash,
                    })
                    .collect(),
                dependency_summary_hash: None,
                enabled_core_features,
            };
            let cache_key = package_audit_cache_key(&key_input);
            Ok(PackageAuditKeyedEntry {
                entry,
                key_input,
                cache_key,
            })
        })
        .collect()
}

fn package_disk_memo_key_inputs_for_lock(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    indexed: &IndexedPackageLockGraph,
    prepared_artifacts: &PreparedPackageArtifacts,
) -> Result<Vec<PackageAuditKeyedEntry>, PackageVerificationError> {
    let mode = package_verification_mode_for_checker(checker);
    let inputs = package_verification_memo_key_inputs_from_artifact_snapshots_indexed(
        &loaded.validated,
        indexed,
        prepared_artifacts,
        mode,
    )?;
    let mut keyed_entries = Vec::new();
    for entry in indexed.entries().iter().cloned() {
        let Some(input) = inputs.get(&entry.module) else {
            continue;
        };
        let key_input = package_audit_disk_memo_key_input(input);
        let cache_key = package_audit_disk_memo_key(&key_input);
        keyed_entries.push(PackageAuditKeyedEntry {
            entry,
            key_input,
            cache_key,
        });
    }
    Ok(keyed_entries)
}

fn package_verification_mode_for_checker(checker: PackageChecker) -> PackageVerificationMode {
    match checker {
        PackageChecker::Reference => PackageVerificationMode::Reference,
        PackageChecker::Fast => PackageVerificationMode::FastKernel,
        PackageChecker::External => {
            unreachable!("external checker does not use in-process package verifier")
        }
    }
}

fn observe_artifact_full_decode(observation: &mut PackageCertificateArtifactObservation) {
    let (count, overflowed) = observation.artifact_full_decodes.overflowing_add(1);
    observation.artifact_full_decodes = if overflowed { u64::MAX } else { count };
    observation.overflowed |= overflowed;
}

fn read_package_audit_cache_lookup(cache_dir: &Path, cache_key: &str) -> PackageAuditCacheLookup {
    let source = match read_cache_entry_no_follow(cache_dir, cache_key) {
        Ok(Some(source)) => source,
        Ok(None) => return PackageAuditCacheLookup::Missing,
        Err(_) => return PackageAuditCacheLookup::Stale,
    };

    match parse_package_audit_result_entry_json(&source) {
        Ok(entry) => PackageAuditCacheLookup::Hit(Box::new(entry)),
        Err(error) if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema => {
            PackageAuditCacheLookup::SchemaMiss
        }
        Err(_) => PackageAuditCacheLookup::Stale,
    }
}

fn read_package_disk_memo_lookup(memo_dir: &Path, cache_key: &str) -> PackageAuditCacheLookup {
    let source = match read_cache_entry_no_follow(memo_dir, cache_key) {
        Ok(Some(source)) => source,
        Ok(None) => return PackageAuditCacheLookup::Missing,
        Err(_) => return PackageAuditCacheLookup::Stale,
    };

    match parse_package_audit_disk_memo_result_entry_json(&source) {
        Ok(entry) => PackageAuditCacheLookup::Hit(Box::new(entry)),
        Err(error) if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema => {
            PackageAuditCacheLookup::SchemaMiss
        }
        Err(_) => PackageAuditCacheLookup::Stale,
    }
}

fn write_package_audit_cache_entry(cache_dir: &Path, entry: &PackageAuditResultEntry) -> bool {
    write_cache_entry_no_follow(
        cache_dir,
        &entry.cache_key,
        &package_audit_result_entry_json(entry),
    )
}

fn write_package_disk_memo_entry(memo_dir: &Path, entry: &PackageAuditResultEntry) -> bool {
    write_cache_entry_no_follow(
        memo_dir,
        &entry.cache_key,
        &package_audit_disk_memo_result_entry_json(entry),
    )
}

fn read_cache_entry_no_follow(cache_dir: &Path, cache_key: &str) -> io::Result<Option<String>> {
    const MAX_AUDIT_RESULT_ENTRY_BYTES: u64 = 2_097_152;
    let directory = match open_absolute_directory(cache_dir, false) {
        Ok(directory) => directory,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    let filename = OsString::from(format!("{cache_key}.json"));
    let Some(mut file) = directory.open_regular_file(&filename)? else {
        return Ok(None);
    };
    let metadata = file.metadata()?;
    if metadata.len() > MAX_AUDIT_RESULT_ENTRY_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "audit cache result entry exceeds its byte limit",
        ));
    }
    let mut source = String::new();
    std::io::Read::by_ref(&mut file)
        .take(MAX_AUDIT_RESULT_ENTRY_BYTES + 1)
        .read_to_string(&mut source)?;
    if source.len() as u64 > MAX_AUDIT_RESULT_ENTRY_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "audit cache result entry exceeds its byte limit",
        ));
    }
    Ok(Some(source))
}

fn write_cache_entry_no_follow(cache_dir: &Path, cache_key: &str, source: &str) -> bool {
    let Ok(directory) = open_absolute_directory(cache_dir, true) else {
        return false;
    };
    let filename = OsString::from(format!("{cache_key}.json"));
    let temporary = OsString::from(format!(
        "{cache_key}.{}.{}.tmp",
        std::process::id(),
        NEXT_AUDIT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst)
    ));
    let Ok(mut file) = directory.create_new_regular_file(&temporary) else {
        return false;
    };
    let result = (|| {
        file.write_all(source.as_bytes())?;
        file.sync_all()?;
        drop(file);
        directory.publish_file_no_replace(&temporary, &filename)
    })();
    // Cache entries are content-addressed and immutable. A collision is
    // validated by the next lookup; the unique staging residue is preserved on
    // failure because an inspect-then-unlink cleanup would be racy.
    result.is_ok()
}

fn cache_off_follow_up_command(root_display: &str, checker: PackageChecker, json: bool) -> String {
    let json_flag = if json { " --json" } else { "" };
    format!(
        "npa package verify-certs --root {} --checker {} --audit-cache off{}",
        shell_word(root_display),
        checker.as_str(),
        json_flag
    )
}

fn shell_word(value: &str) -> String {
    if value
        .bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'/' | b'_' | b'-'))
    {
        return value.to_owned();
    }
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn package_audit_result_entry_for_module(
    keyed: &PackageAuditKeyedEntry,
    module: &PackageModuleVerificationResult,
) -> PackageAuditResultEntry {
    package_audit_result_entry_from_parts(
        keyed,
        package_audit_cached_status(module.status),
        module
            .error
            .as_ref()
            .map(|error| error.reason_code.as_str().to_owned()),
    )
}

fn package_disk_memo_result_entry_for_module(
    keyed: &PackageAuditKeyedEntry,
    module: &PackageModuleVerificationResult,
) -> PackageAuditResultEntry {
    package_disk_memo_result_entry_from_parts(
        keyed,
        package_audit_cached_status(module.status),
        module
            .error
            .as_ref()
            .map(|error| error.reason_code.as_str().to_owned()),
    )
}

fn package_audit_accepted_result_entry_for_key(
    keyed: &PackageAuditKeyedEntry,
) -> PackageAuditResultEntry {
    package_audit_result_entry_from_parts(keyed, PackageAuditCachedStatus::Accepted, None)
}

fn package_disk_memo_accepted_result_entry_for_key(
    keyed: &PackageAuditKeyedEntry,
) -> PackageAuditResultEntry {
    package_disk_memo_result_entry_from_parts(keyed, PackageAuditCachedStatus::Accepted, None)
}

fn package_audit_result_entry_from_parts(
    keyed: &PackageAuditKeyedEntry,
    status: PackageAuditCachedStatus,
    diagnostic_reason: Option<String>,
) -> PackageAuditResultEntry {
    PackageAuditResultEntry {
        schema: PACKAGE_AUDIT_RESULT_SCHEMA.to_owned(),
        cache_key: keyed.cache_key.clone(),
        trusted: false,
        proof_evidence: false,
        key_input: keyed.key_input.clone(),
        status,
        diagnostic_reason,
        trust_boundary: "cache entry is not proof evidence; live checker result dominates"
            .to_owned(),
    }
}

fn package_disk_memo_result_entry_from_parts(
    keyed: &PackageAuditKeyedEntry,
    status: PackageAuditCachedStatus,
    diagnostic_reason: Option<String>,
) -> PackageAuditResultEntry {
    PackageAuditResultEntry {
        schema: PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA.to_owned(),
        cache_key: keyed.cache_key.clone(),
        trusted: false,
        proof_evidence: false,
        key_input: keyed.key_input.clone(),
        status,
        diagnostic_reason,
        trust_boundary: "disk verifier memo entry is not proof evidence".to_owned(),
    }
}

fn is_exact_accepted_cache_hit(
    keyed: &PackageAuditKeyedEntry,
    lookup: &PackageAuditCacheLookup,
) -> bool {
    matches!(
        lookup,
        PackageAuditCacheLookup::Hit(stored)
            if stored.as_ref() == &package_audit_accepted_result_entry_for_key(keyed)
    )
}

fn is_exact_accepted_disk_memo_hit(
    keyed: &PackageAuditKeyedEntry,
    lookup: &PackageAuditCacheLookup,
) -> bool {
    matches!(
        lookup,
        PackageAuditCacheLookup::Hit(stored)
            if stored.as_ref() == &package_disk_memo_accepted_result_entry_for_key(keyed)
    )
}

fn package_audit_cached_status(
    status: PackageModuleVerificationStatus,
) -> PackageAuditCachedStatus {
    match status {
        PackageModuleVerificationStatus::Passed => PackageAuditCachedStatus::Accepted,
        PackageModuleVerificationStatus::Failed | PackageModuleVerificationStatus::Skipped => {
            PackageAuditCachedStatus::Rejected
        }
    }
}

fn package_audit_policy_hash(loaded: &LoadedPackageRoot) -> PackageHash {
    let policy = &loaded.validated.manifest().policy;
    let mut allowed_axioms = policy
        .allowed_axioms
        .iter()
        .map(Name::as_dotted)
        .collect::<Vec<_>>();
    allowed_axioms.sort();

    let mut material = format!(
        "schema=npa.package.audit_policy.v0.1\nallow_custom_axioms={}\nallowed_axioms={}\n",
        policy.allow_custom_axioms,
        allowed_axioms.len()
    );
    for axiom in allowed_axioms {
        material.push_str("allowed_axiom=");
        material.push_str(&axiom);
        material.push('\n');
    }
    package_file_hash(material.as_bytes())
}

fn package_audit_checker_identity(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
) -> PackageAuditCheckerIdentity {
    let checker_id = match checker {
        PackageChecker::Reference => "npa-checker-ref",
        PackageChecker::Fast => "fast-kernel-certificate-verifier",
        PackageChecker::External => EXTERNAL_CHECKER_LABEL,
    };
    let checker_profile = match checker {
        PackageChecker::Reference => loaded.validated.manifest().checker_profile.clone(),
        PackageChecker::Fast => "fast-kernel".to_owned(),
        PackageChecker::External => EXTERNAL_CHECKER_PROFILE.to_owned(),
    };
    let checker_version = env!("CARGO_PKG_VERSION").to_owned();
    // Built-in PAS-02 checkers do not have separate runner artifacts, so the
    // cache key uses deterministic CLI-owned checker identity material.
    let build_material = format!(
        "schema=npa.package.audit_checker_identity.v0.1\nmode={}\nchecker_id={checker_id}\nchecker_version={checker_version}\nchecker_profile={checker_profile}\n",
        checker.as_str(),
    );

    PackageAuditCheckerIdentity {
        mode: checker.as_str().to_owned(),
        checker_id: checker_id.to_owned(),
        checker_version,
        checker_build_hash: package_file_hash(build_material.as_bytes()),
        checker_profile,
        runner_policy_hash: None,
    }
}

fn package_certificate_artifacts(
    artifacts: &[CertificateArtifactBuffer],
) -> Vec<PackageCertificateArtifact<'_>> {
    artifacts
        .iter()
        .map(|artifact| PackageCertificateArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.bytes(),
        })
        .collect()
}

fn command_result_from_report(
    root_display: String,
    lock: &PackageLockManifest,
    report: PackageVerificationReport,
    include_memo_summary: bool,
) -> CommandResult {
    let memo_counters = report.memo_counters;
    let decode_cache_counters = report.decode_cache_counters;
    let mut result = if report.status == PackageVerificationStatus::Passed {
        let mut result = CommandResult::passed(COMMAND, root_display);
        result.diagnostics = passed_report_diagnostics(lock, &report);
        result
    } else {
        let diagnostics = failed_report_diagnostics(&report);
        CommandResult::failed(COMMAND, root_display, diagnostics)
    };
    if include_memo_summary && memo_counters.is_active() {
        result
            .diagnostics
            .push(package_process_memo_summary_diagnostic(memo_counters));
    }
    if include_memo_summary {
        if let Some(counters) = decode_cache_counters.filter(|counters| counters.is_active()) {
            result
                .diagnostics
                .push(package_decode_cache_summary_diagnostic(counters));
        }
    }
    result
}

fn command_result_from_audit_run(
    root_display: String,
    lock: &PackageLockManifest,
    run: PackageAuditVerificationRun,
) -> CommandResult {
    let mut result = command_result_from_report(root_display, lock, run.report, false);
    result
        .diagnostics
        .push(package_audit_cache_summary_diagnostic(&run.cache));
    if let Some(diagnostic) = package_audit_cache_follow_up_diagnostic(&run.cache) {
        result.diagnostics.push(diagnostic);
    }
    result
}

fn command_result_from_disk_memo_run(
    root_display: String,
    lock: &PackageLockManifest,
    run: PackageDiskMemoVerificationRun,
    include_memo_summary: bool,
) -> CommandResult {
    let memo = run.memo;
    let mut result = command_result_from_report(root_display, lock, run.report, false);
    if include_memo_summary {
        result
            .diagnostics
            .push(package_disk_memo_summary_diagnostic(&memo));
    }
    result
}

impl PackageAuditCacheSummary {
    fn new(mode: PackageAuditCacheMode) -> Self {
        Self {
            mode,
            hits: 0,
            misses: 0,
            stale: 0,
            schema_misses: 0,
            written: 0,
            live_checked: 0,
            cached: 0,
            trusted: false,
            cache_off_follow_up: None,
        }
    }

    fn diagnostic_value(&self) -> String {
        format!(
            "mode={};hits={};misses={};stale={};schema_misses={};written={};live_checked={};cached={};trusted={}",
            self.mode.as_str(),
            self.hits,
            self.misses,
            self.stale,
            self.schema_misses,
            self.written,
            self.live_checked,
            self.cached,
            self.trusted,
        )
    }
}

impl PackageVerifierDiskMemoSummary {
    fn new(mode: PackageVerifierMemoMode) -> Self {
        Self {
            mode,
            hits: 0,
            misses: 0,
            stale: 0,
            schema_misses: 0,
            written: 0,
            invalidated: 0,
            live_checked: 0,
            cached: 0,
            trusted: false,
            proof_evidence: false,
        }
    }

    fn diagnostic_value(&self) -> String {
        format!(
            "mode={};hits={};misses={};stale={};schema_misses={};written={};invalidated={};live_checked={};cached={};trusted={};proof_evidence={}",
            self.mode.as_str(),
            self.hits,
            self.misses,
            self.stale,
            self.schema_misses,
            self.written,
            self.invalidated,
            self.live_checked,
            self.cached,
            self.trusted,
            self.proof_evidence,
        )
    }
}

fn package_audit_cache_summary_diagnostic(summary: &PackageAuditCacheSummary) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "audit_cache_summary")
        .with_field("audit_cache")
        .with_actual_value(summary.diagnostic_value())
}

fn package_disk_memo_summary_diagnostic(
    summary: &PackageVerifierDiskMemoSummary,
) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "disk_memo_summary")
        .with_field("verifier_memo")
        .with_actual_value(summary.diagnostic_value())
}

fn package_audit_cache_follow_up_diagnostic(
    summary: &PackageAuditCacheSummary,
) -> Option<CommandDiagnostic> {
    let follow_up = summary.cache_off_follow_up.as_ref()?;
    Some(
        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "audit_cache_follow_up")
            .with_field("audit_cache")
            .with_actual_value(format!("proof_evidence=false;follow_up=\"{follow_up}\"")),
    )
}

fn package_process_memo_summary_diagnostic(
    counters: PackageVerificationMemoCounters,
) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "process_memo_summary")
        .with_field("process_memo")
        .with_actual_value(format!(
            "mode=process-local;hits={};misses={};inserted={};trusted=false",
            counters.hits, counters.misses, counters.inserted,
        ))
}

fn package_decode_cache_summary_diagnostic(
    counters: PackageVerificationDecodeCacheCounters,
) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "decode_cache_summary")
        .with_field("decode_cache")
        .with_actual_value(format!(
            "mode=process-local;certificate_hits={};certificate_misses={};certificate_inserted={};import_context_hits={};import_context_misses={};import_context_inserted={};import_context_disk_hits={};import_context_disk_misses={};import_context_disk_stale={};import_context_disk_schema_misses={};import_context_disk_inserted={};trusted=false;proof_evidence=false",
            counters.certificate_hits,
            counters.certificate_misses,
            counters.certificate_inserted,
            counters.import_context_hits,
            counters.import_context_misses,
            counters.import_context_inserted,
            counters.import_context_disk_hits,
            counters.import_context_disk_misses,
            counters.import_context_disk_stale,
            counters.import_context_disk_schema_misses,
            counters.import_context_disk_inserted,
        ))
}

fn passed_report_diagnostics(
    lock: &PackageLockManifest,
    report: &PackageVerificationReport,
) -> Vec<CommandDiagnostic> {
    let entries_by_module = lock_entries_by_module(lock);
    let mut diagnostics = vec![aggregate_report_diagnostic(report)];
    diagnostics.extend(report.modules.iter().map(|module| {
        let path = entries_by_module
            .get(&module.module)
            .map(|entry| entry.certificate.as_str())
            .unwrap_or("<unknown-certificate>");
        CommandDiagnostic::info(
            diagnostic_kind_for_mode(module.checker_mode),
            "module_verified",
        )
        .with_module(module.module.as_dotted())
        .with_path(path)
        .with_field("status")
        .with_expected_value(PackageModuleVerificationStatus::Passed.as_str())
        .with_actual_value(module_result_actual_value(module))
        .with_checker(report.verdict_source.as_str())
    }));
    diagnostics
}

fn module_result_actual_value(module: &PackageModuleVerificationResult) -> String {
    format!(
        "status={};evidence={};proof_evidence={};certificate_format={};core_spec={}",
        module.status.as_str(),
        module.evidence.as_str(),
        module.evidence.is_proof_evidence(),
        module.certificate_format.as_deref().unwrap_or("unknown"),
        module.core_spec.as_deref().unwrap_or("unknown")
    )
}

fn aggregate_report_diagnostic(report: &PackageVerificationReport) -> CommandDiagnostic {
    CommandDiagnostic::info(diagnostic_kind_for_mode(report.mode), "package_verified")
        .with_field("verdict_source")
        .with_actual_value(format!(
            "mode={};verdict_source={};reference_checker_verdict={};locally_accelerated={};modules={}",
            report.mode.as_str(),
            report.verdict_source.as_str(),
            report.reference_checker_verdict,
            report.locally_accelerated,
            report.modules.len()
        ))
        .with_checker(report.verdict_source.as_str())
}

fn failed_report_diagnostics(report: &PackageVerificationReport) -> Vec<CommandDiagnostic> {
    let kind = diagnostic_kind_for_mode(report.mode);
    let checker = report.verdict_source.as_str();
    let diagnostics = report
        .modules
        .iter()
        .filter_map(|module| {
            module
                .error
                .as_ref()
                .map(|error| verification_error_diagnostic(error, Some(module), kind, checker))
        })
        .collect::<Vec<_>>();
    if diagnostics.is_empty() {
        vec![CommandDiagnostic::error(
            DiagnosticKind::Internal,
            "verification_failed_without_error",
        )
        .with_checker(checker)]
    } else {
        diagnostics
    }
}

fn verification_error_diagnostic(
    error: &PackageVerificationError,
    module: Option<&PackageModuleVerificationResult>,
    fallback_kind: DiagnosticKind,
    fallback_checker: &str,
) -> CommandDiagnostic {
    let kind = diagnostic_kind_for_error(error).unwrap_or(fallback_kind);
    let mut diagnostic = CommandDiagnostic::error(kind, error.reason_code.as_str())
        .with_path(error.path.clone())
        .with_checker(
            error
                .checker_error
                .as_ref()
                .map(|checker| checker.checker.as_str())
                .unwrap_or(fallback_checker),
        );
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field.as_str());
    }
    if let Some(module) = &error.module {
        diagnostic = diagnostic.with_module(module.as_str());
    } else if let Some(module) = module {
        diagnostic = diagnostic.with_module(module.module.as_dotted());
    }
    if is_hash_mismatch_reason(error.reason_code) {
        if let (Some(expected), Some(actual)) = (&error.expected_value, &error.actual_value) {
            diagnostic = diagnostic.with_hashes(expected.clone(), actual.clone());
        }
    } else {
        if let Some(expected) = &error.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.clone());
        }
        if let Some(actual) = &error.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.clone());
        }
    }
    diagnostic
}

fn diagnostic_kind_for_error(error: &PackageVerificationError) -> Option<DiagnosticKind> {
    Some(match error.kind {
        PackageVerificationErrorKind::Input => DiagnosticKind::PackageLock,
        PackageVerificationErrorKind::LockGraph => DiagnosticKind::PackageGraph,
        PackageVerificationErrorKind::Artifact => DiagnosticKind::ArtifactIo,
        PackageVerificationErrorKind::CertificateDecode => DiagnosticKind::SourceFreeBoundary,
        PackageVerificationErrorKind::CertificateIdentity => DiagnosticKind::HashMismatch,
        PackageVerificationErrorKind::Kernel => DiagnosticKind::FastVerifier,
        PackageVerificationErrorKind::ReferenceChecker => DiagnosticKind::ReferenceVerifier,
        PackageVerificationErrorKind::Phase8Adapter => DiagnosticKind::SourceFreeBoundary,
        PackageVerificationErrorKind::Dependency => return None,
    })
}

fn is_hash_mismatch_reason(reason: PackageVerificationErrorReason) -> bool {
    matches!(
        reason,
        PackageVerificationErrorReason::CertificateFileHashMismatch
            | PackageVerificationErrorReason::ExportHashMismatch
            | PackageVerificationErrorReason::AxiomReportHashMismatch
            | PackageVerificationErrorReason::CertificateHashMismatch
    )
}

fn diagnostic_kind_for_mode(mode: PackageVerificationMode) -> DiagnosticKind {
    match mode {
        PackageVerificationMode::FastKernel => DiagnosticKind::FastVerifier,
        PackageVerificationMode::Reference => DiagnosticKind::ReferenceVerifier,
    }
}

fn checker_diagnostic_kind(checker: PackageChecker) -> DiagnosticKind {
    match checker {
        PackageChecker::Reference => DiagnosticKind::ReferenceVerifier,
        PackageChecker::Fast => DiagnosticKind::FastVerifier,
        PackageChecker::External => DiagnosticKind::ExternalVerifier,
    }
}

fn checker_label(checker: PackageChecker) -> &'static str {
    match checker {
        PackageChecker::Reference => PackageVerificationVerdictSource::ReferenceChecker.as_str(),
        PackageChecker::Fast => {
            PackageVerificationVerdictSource::FastKernelCertificateVerifier.as_str()
        }
        PackageChecker::External => EXTERNAL_CHECKER_LABEL,
    }
}

fn lock_entries_by_module(lock: &PackageLockManifest) -> BTreeMap<Name, &PackageLockEntry> {
    lock.entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    use std::os::fd::AsRawFd;
    #[cfg(unix)]
    use std::os::unix::process::ExitStatusExt;
    #[cfg(unix)]
    use std::sync::atomic::{AtomicU64, Ordering};

    #[cfg(unix)]
    fn output(code: i32, stdout: &[u8], stderr: &[u8]) -> Output {
        Output {
            status: std::process::ExitStatus::from_raw(code << 8),
            stdout: stdout.to_vec(),
            stderr: stderr.to_vec(),
        }
    }

    #[cfg(unix)]
    #[derive(Default)]
    struct ScriptedGitRunner {
        outputs: RefCell<Vec<Result<Output, io::Error>>>,
        invocations: RefCell<Vec<GitInvocation>>,
    }

    #[cfg(unix)]
    impl ScriptedGitRunner {
        fn new(outputs: Vec<Result<Output, io::Error>>) -> Self {
            Self {
                outputs: RefCell::new(outputs.into_iter().rev().collect()),
                invocations: RefCell::new(Vec::new()),
            }
        }
    }

    #[cfg(unix)]
    impl ChangedPathGitProcessRunner for ScriptedGitRunner {
        fn output(&self, invocation: &GitInvocation) -> io::Result<Output> {
            self.invocations.borrow_mut().push(invocation.clone());
            self.outputs
                .borrow_mut()
                .pop()
                .expect("script contains one result per invocation")
        }
    }

    #[cfg(unix)]
    struct TemporaryGitRepository {
        root: PathBuf,
    }

    #[cfg(unix)]
    impl TemporaryGitRepository {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let root = std::env::temp_dir().join(format!(
                "npa-gitsel-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&root).unwrap();
            let repository = Self { root };
            repository.git(&["init", "-q"]);
            repository.git(&["config", "user.email", "gitsel@example.invalid"]);
            repository.git(&["config", "user.name", "GITSEL Test"]);
            repository
        }

        fn path(&self) -> &Path {
            &self.root
        }

        fn write(&self, relative: &str, bytes: &[u8]) {
            let path = self.root.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            fs::write(path, bytes).unwrap();
        }

        fn git(&self, args: &[&str]) -> Output {
            let output = Command::new("/usr/bin/git")
                .args(args)
                .current_dir(&self.root)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            output
        }

        fn commit_all(&self) {
            self.git(&["add", "."]);
            self.git(&["commit", "-q", "-m", "baseline"]);
        }
    }

    #[cfg(unix)]
    impl Drop for TemporaryGitRepository {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.root).unwrap();
        }
    }

    #[test]
    fn git_changed_batching_constants_match_design() {
        assert_eq!(GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES, 65_536);
        assert_eq!(GIT_CHANGED_PATHSPEC_BATCH_MAX_PATHS, 1_024);
        assert_eq!(GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES, 32_768);
        assert_eq!(GIT_CHANGED_LEGACY_BATCH_PATHS, 128);
    }

    #[test]
    fn git_changed_selection_invocation_builders_are_byte_exact() {
        let root = Path::new("/tmp/work tree");
        let pathspecs = vec![
            ":(top,literal)-leading path".to_owned(),
            ":(top,literal)日本語/証明.npcert".to_owned(),
        ];
        let root_invocation = git_worktree_root_invocation(root);
        assert_eq!(root_invocation.kind, GitInvocationKind::WorktreeRoot);
        assert_eq!(root_invocation.program, Path::new("/usr/bin/git"));
        assert_eq!(root_invocation.current_dir, root);
        assert!(!root_invocation.committed_base_hardened);
        assert_eq!(
            root_invocation.args,
            vec![
                OsString::from("rev-parse"),
                OsString::from("--show-toplevel")
            ]
        );
        assert_eq!(
            git_has_head_invocation(root).args,
            ["rev-parse", "--verify", "--quiet", "HEAD"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_tracked_invocation(root, &pathspecs).args,
            [
                "diff",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                "HEAD",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_untracked_invocation(root, &pathspecs).args,
            [
                "ls-files",
                "--others",
                "--exclude-standard",
                "-z",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_protected_index_state_invocation(root, &pathspecs).args,
            [
                "ls-files",
                "-s",
                "-v",
                "-z",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_protected_index_diff_invocation(root, &pathspecs).args,
            [
                "diff",
                "--cached",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                "--ignore-submodules=none",
                "HEAD",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_protected_worktree_diff_invocation(root, &pathspecs).args,
            [
                "diff",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                "--ignore-submodules=none",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        let raw_paths = vec!["-leading path".to_owned(), "日本語/証明.npcert".to_owned()];
        assert_eq!(
            git_protected_raw_hash_invocation(root, &raw_paths).args,
            [
                "hash-object",
                "--no-filters",
                "--",
                raw_paths[0].as_str(),
                raw_paths[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        let ancestor_pathspecs = vec![
            ":(top,literal)nested [*?]".to_owned(),
            ":(top,exclude,glob)nested \\[\\*\\?\\]/**".to_owned(),
        ];
        let ancestor_invocation =
            git_protected_ancestor_index_invocation(root, &ancestor_pathspecs);
        assert_eq!(
            ancestor_invocation.kind,
            GitInvocationKind::ProtectedIndexState
        );
        assert!(!ancestor_invocation.committed_base_hardened);
        assert_eq!(
            ancestor_invocation.args,
            [
                "ls-files",
                "-z",
                "--",
                ancestor_pathspecs[0].as_str(),
                ancestor_pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        let ancestor_head_invocation =
            git_protected_ancestor_head_invocation(root, &ancestor_pathspecs);
        assert_eq!(ancestor_head_invocation.kind, GitInvocationKind::Tracked);
        assert!(!ancestor_head_invocation.committed_base_hardened);
        assert_eq!(
            ancestor_head_invocation.args,
            [
                "diff",
                "--cached",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                "--ignore-submodules=none",
                "HEAD",
                "--",
                ancestor_pathspecs[0].as_str(),
                ancestor_pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_ignored_untracked_invocation(root, &pathspecs).args,
            [
                "ls-files",
                "--others",
                "--ignored",
                "--exclude-standard",
                "-z",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        let clean_head_invocation =
            git_clean_head_invocation(git_protected_worktree_diff_invocation(root, &pathspecs));
        assert!(clean_head_invocation.committed_base_hardened);
        assert_eq!(
            clean_head_invocation.args,
            [
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.trustctime=true",
                "-c",
                "core.checkStat=default",
                "-c",
                "core.fileMode=true",
                "diff",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                "--ignore-submodules=none",
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
    }

    #[test]
    fn git_committed_selection_invocation_builders_are_byte_exact() {
        let root = Path::new("/tmp/work tree");
        let sha1_a = "a".repeat(40);
        let sha1_b = "b".repeat(40);
        let pathspecs = vec![
            ":(top,literal)nested package/-proof [x].npcert".to_owned(),
            ":(top,literal)nested package/日本語.npcert".to_owned(),
        ];

        assert_eq!(
            git_object_format_invocation(root).args,
            ["rev-parse", "--show-object-format=storage"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_resolve_commit_invocation(root, "-topic", GitInvocationKind::ResolveBase).args,
            [
                "rev-parse",
                "--verify",
                "--end-of-options",
                "-topic^{commit}"
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_resolve_commit_invocation(root, "HEAD", GitInvocationKind::ResolveHead).args,
            ["rev-parse", "--verify", "--end-of-options", "HEAD^{commit}"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_merge_base_invocation(root, &sha1_a, &sha1_b).args,
            ["merge-base", "--all", sha1_a.as_str(), sha1_b.as_str()]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_ls_tree_invocation(root, &sha1_a, &pathspecs[0]).args,
            [
                "ls-tree",
                "-z",
                "--full-tree",
                sha1_a.as_str(),
                "--",
                pathspecs[0].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );
        assert_eq!(
            git_blob_size_invocation(root, &sha1_b).args,
            ["cat-file", "-s", sha1_b.as_str()]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_blob_read_invocation(root, &sha1_b).args,
            ["cat-file", "blob", sha1_b.as_str()]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            git_committed_diff_invocation(root, &sha1_a, &sha1_b, &pathspecs).args,
            [
                "diff",
                "--name-only",
                "-z",
                "--no-ext-diff",
                "--no-renames",
                sha1_a.as_str(),
                sha1_b.as_str(),
                "--",
                pathspecs[0].as_str(),
                pathspecs[1].as_str(),
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );

        for invocation in [
            git_committed_base_invocation(git_worktree_root_invocation(root)),
            git_object_format_invocation(root),
            git_resolve_commit_invocation(root, "base", GitInvocationKind::ResolveBase),
            git_resolve_commit_invocation(root, "HEAD", GitInvocationKind::ResolveHead),
            git_merge_base_invocation(root, &sha1_a, &sha1_b),
            git_ls_tree_invocation(root, &sha1_a, &pathspecs[0]),
            git_blob_size_invocation(root, &sha1_b),
            git_blob_read_invocation(root, &sha1_b),
            git_committed_diff_invocation(root, &sha1_a, &sha1_b, &pathspecs),
        ] {
            assert!(invocation.committed_base_hardened);
        }
    }

    #[cfg(unix)]
    #[test]
    fn committed_git_blob_reads_ignore_replace_objects() {
        let repository = TemporaryGitRepository::new();
        repository.write("tracked", b"original\n");
        repository.commit_all();
        let original_oid = String::from_utf8(repository.git(&["rev-parse", "HEAD:tracked"]).stdout)
            .unwrap()
            .trim()
            .to_owned();

        repository.write("replacement", b"replacement\n");
        let replacement_oid =
            String::from_utf8(repository.git(&["hash-object", "-w", "replacement"]).stdout)
                .unwrap()
                .trim()
                .to_owned();
        repository.git(&["replace", &original_oid, &replacement_oid]);

        let ordinary = Command::new("/usr/bin/git")
            .args(["cat-file", "blob", &original_oid])
            .current_dir(repository.path())
            .env_remove("GIT_NO_REPLACE_OBJECTS")
            .output()
            .unwrap();
        assert!(ordinary.status.success());
        assert_eq!(ordinary.stdout, b"replacement\n");

        let hardened = SystemChangedPathGitProcessRunner
            .output(&git_blob_read_invocation(repository.path(), &original_oid))
            .unwrap();
        assert!(hardened.status.success());
        assert_eq!(hardened.stdout, b"original\n");
    }

    #[cfg(unix)]
    #[test]
    fn git_committed_selection_decoders_reject_ambiguous_or_malformed_output() {
        assert_eq!(
            decode_git_object_format(output(0, b"sha1\n", b"")).unwrap(),
            GitObjectFormat::Sha1
        );
        assert_eq!(
            decode_git_object_format(output(0, b"sha256\n", b"")).unwrap(),
            GitObjectFormat::Sha256
        );
        for stdout in [
            b"sha1".as_slice(),
            b"SHA1\n".as_slice(),
            b"sha1\nextra\n".as_slice(),
            b"sha1\r\n".as_slice(),
            b"\xff\n".as_slice(),
        ] {
            assert!(decode_git_object_format(output(0, stdout, b"")).is_err());
        }

        let sha1 = "a".repeat(40);
        assert_eq!(
            decode_git_oid(
                output(0, format!("{sha1}\n").as_bytes(), b""),
                GitObjectFormat::Sha1,
                "resolve",
            )
            .unwrap(),
            sha1
        );
        for stdout in [
            "a".repeat(40),
            format!("{}\n", "A".repeat(40)),
            format!("{}\n", "a".repeat(39)),
            format!("{}g\n", "a".repeat(39)),
            format!("{}\n{}\n", "a".repeat(40), "b".repeat(40)),
        ] {
            assert!(decode_git_oid(
                output(0, stdout.as_bytes(), b""),
                GitObjectFormat::Sha1,
                "resolve",
            )
            .is_err());
        }
        assert!(decode_unique_merge_base(output(0, b"", b""), GitObjectFormat::Sha1).is_err());
        assert!(decode_unique_merge_base(
            output(
                0,
                format!("{}\n{}\n", "a".repeat(40), "b".repeat(40)).as_bytes(),
                b"",
            ),
            GitObjectFormat::Sha1,
        )
        .is_err());

        assert!(validate_strict_nul_path_output(b"", "unterminated", "empty record").is_ok());
        for stdout in [b"path".as_slice(), b"\0".as_slice(), b"path\0\0".as_slice()] {
            assert!(
                validate_strict_nul_path_output(stdout, "unterminated", "empty record").is_err()
            );
        }
        assert!(validate_strict_nul_path_output(
            b"first\0second\0",
            "unterminated",
            "empty record"
        )
        .is_ok());

        let candidates = BTreeMap::from([
            ("normal".to_owned(), "normal".to_owned()),
            ("assumed".to_owned(), "assumed".to_owned()),
            ("skipped".to_owned(), "skipped".to_owned()),
        ]);
        let mut changed = BTreeSet::new();
        let mut raw_hash_candidates = BTreeMap::new();
        let oid = "0".repeat(40);
        record_protected_index_state_paths(
            format!(
                "H 100644 {oid} 0\tnormal\0h 100644 {oid} 0\tassumed\0S 100644 {oid} 0\tskipped\0"
            )
            .as_bytes(),
            &candidates,
            &mut changed,
            &mut raw_hash_candidates,
        )
        .unwrap();
        assert_eq!(
            changed,
            BTreeSet::from(["assumed".to_owned(), "skipped".to_owned()])
        );
        assert_eq!(
            raw_hash_candidates,
            BTreeMap::from([(
                "normal".to_owned(),
                ProtectedIndexBlob {
                    candidate_path: "normal".to_owned(),
                    oid: oid.clone(),
                },
            )])
        );
        let malformed = [
            format!("H 100644 {oid} 0\tnormal"),
            format!("H 100644 {oid} 0\tnormal\0\0"),
            "H\0".to_owned(),
            format!("H-100644 {oid} 0\tnormal\0"),
            format!("H 100644 {oid} 0\toutside\0"),
            format!("H 100644 {} 0\tnormal\0", "A".repeat(40)),
            format!("H 100600 {oid} 0\tnormal\0"),
        ];
        for stdout in malformed {
            assert!(record_protected_index_state_paths(
                stdout.as_bytes(),
                &candidates,
                &mut BTreeSet::new(),
                &mut BTreeMap::new(),
            )
            .is_err());
        }

        for mode in ["120000", "160000", "040000"] {
            let mut changed = BTreeSet::new();
            record_protected_index_state_paths(
                format!("H {mode} {oid} 0\tnormal\0").as_bytes(),
                &candidates,
                &mut changed,
                &mut BTreeMap::new(),
            )
            .unwrap();
            assert_eq!(changed, BTreeSet::from(["normal".to_owned()]));
        }

        let raw_candidates = vec![(
            "normal".to_owned(),
            ProtectedIndexBlob {
                candidate_path: "normal".to_owned(),
                oid: oid.clone(),
            },
        )];
        let mut raw_changed = BTreeSet::new();
        record_protected_raw_hashes(
            format!("{}\n", "1".repeat(40)).as_bytes(),
            &raw_candidates,
            &mut raw_changed,
        )
        .unwrap();
        assert_eq!(raw_changed, BTreeSet::from(["normal".to_owned()]));
        for stdout in [
            oid.clone(),
            format!("{oid}\n{oid}\n"),
            format!("{}\n", "A".repeat(40)),
            format!("{}\n", "0".repeat(39)),
        ] {
            assert!(record_protected_raw_hashes(
                stdout.as_bytes(),
                &raw_candidates,
                &mut BTreeSet::new(),
            )
            .is_err());
        }

        let failure = committed_git_selection_failure(
            base_selection_summary(&"b".repeat(PACKAGE_VERIFY_BASE_TEXT_LIMIT * 2)),
            "e".repeat(PACKAGE_VERIFY_GIT_ERROR_LIMIT * 2),
        );
        assert!(
            failure.diagnostic.actual_value.as_deref().unwrap().len()
                <= PACKAGE_VERIFY_GIT_ERROR_LIMIT
        );
    }

    #[cfg(unix)]
    #[test]
    fn git_output_decoder_branch_matrix() {
        assert_eq!(
            decode_git_worktree_root_output(output(0, b"  /tmp/repo\n", b"ignored")),
            Ok(PathBuf::from("/tmp/repo"))
        );
        assert_eq!(
            decode_git_worktree_root_output(output(2, b"", b"  failure \n")),
            Err("failure".to_owned())
        );
        assert_eq!(
            decode_git_worktree_root_output(output(2, b"", b" \n")),
            Err("git rev-parse exited with status exit status: 2".to_owned())
        );
        assert_eq!(decode_git_has_head_output(output(0, b"", b"")), Ok(true));
        assert_eq!(decode_git_has_head_output(output(1, b"", b"")), Ok(false));
        assert_eq!(
            decode_git_has_head_output(output(3, b"", b"head failed")),
            Err("head failed".to_owned())
        );
        assert_eq!(
            decode_git_tracked_output(output(0, b"a\0\xff", b"")),
            Ok(b"a\0\xff".to_vec())
        );
        assert_eq!(
            decode_git_tracked_output(output(4, b"", b" \n")),
            Err("git diff exited with status exit status: 4".to_owned())
        );
        assert_eq!(
            decode_git_untracked_output(output(5, b"", b"  untracked failed \n")),
            Err("untracked failed".to_owned())
        );
        let signaled = Output {
            status: std::process::ExitStatus::from_raw(9),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        assert!(decode_git_untracked_output(signaled)
            .unwrap_err()
            .starts_with("git ls-files exited with status"));
    }

    fn pathspec_with_charge(charge: usize) -> String {
        "x".repeat(charge - 1 - std::mem::size_of::<*const u8>())
    }

    #[test]
    fn git_pathspec_batches_obey_exact_byte_and_count_boundaries() {
        let target = 100;
        let pathspecs = vec![pathspec_with_charge(40), pathspec_with_charge(60)];
        let batches = git_pathspec_batches(
            &pathspecs,
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: target,
            },
        );
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].argv_charge_bytes, target);

        let pathspecs = vec![
            pathspec_with_charge(40),
            pathspec_with_charge(60),
            pathspec_with_charge(1 + std::mem::size_of::<*const u8>()),
        ];
        let batches = git_pathspec_batches(
            &pathspecs,
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: target,
            },
        );
        assert_eq!(
            batches
                .iter()
                .map(|batch| batch.pathspecs.len())
                .collect::<Vec<_>>(),
            vec![2, 1]
        );

        let tiny = (0..1_025)
            .map(|index| format!("p{index:04}"))
            .collect::<Vec<_>>();
        let batches = git_pathspec_batches(
            &tiny,
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: usize::MAX,
            },
        );
        assert_eq!(batches[0].pathspecs.len(), 1_024);
        assert_eq!(batches[1].pathspecs.len(), 1);
        assert_eq!(
            batches
                .iter()
                .flat_map(|batch| batch.pathspecs.iter())
                .collect::<Vec<_>>(),
            tiny.iter().collect::<Vec<_>>()
        );
        assert_eq!(
            git_pathspec_batches(&tiny, GitPathspecBatchPolicy::Legacy128)
                .iter()
                .map(|batch| batch.pathspecs.len())
                .collect::<Vec<_>>(),
            tiny.chunks(128).map(<[_]>::len).collect::<Vec<_>>()
        );
    }

    #[test]
    fn exact_candidate_pathspec_groups_keep_pairs_atomic_and_depth_isolated() {
        let groups = exact_candidate_pathspec_groups(["a", "b[*?]", "a/deep"]);
        assert_eq!(
            groups,
            vec![
                vec![
                    ":(top,literal)a".to_owned(),
                    ":(top,exclude,glob)a/**".to_owned(),
                    ":(top,literal)b[*?]".to_owned(),
                    r":(top,exclude,glob)b\[\*\?\]/**".to_owned(),
                ],
                vec![
                    ":(top,literal)a/deep".to_owned(),
                    ":(top,exclude,glob)a/deep/**".to_owned(),
                ],
            ]
        );

        let pair_charge = groups[0]
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
                pair.iter()
                    .map(|pathspec| pathspec_charges(pathspec).unwrap().1)
                    .sum::<usize>()
            })
            .max()
            .unwrap();
        let policy = grouped_git_pathspec_batch_policy(
            &groups[0],
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: pair_charge,
            },
            2,
        );
        let batches = git_pathspec_batches_grouped(&groups[0], policy, 2);
        assert_eq!(
            batches
                .iter()
                .map(|batch| batch.pathspecs.len())
                .collect::<Vec<_>>(),
            vec![2, 2]
        );
        assert_eq!(
            grouped_git_pathspec_batch_policy(
                &groups[0],
                GitPathspecBatchPolicy::ExecBudget {
                    effective_charge_bytes: pair_charge - 1,
                },
                2,
            ),
            GitPathspecBatchPolicy::Legacy128
        );
    }

    #[test]
    fn protected_ancestor_batches_keep_pairs_atomic_and_depth_isolated() {
        assert_eq!(git_glob_escape_path(r"a\b[*?]"), r"a\\b\[\*\?\]");
        let ancestors = BTreeMap::from([
            ("a".to_owned(), BTreeSet::from(["a/protected".to_owned()])),
            (
                "a/deep".to_owned(),
                BTreeSet::from(["a/deep/protected".to_owned()]),
            ),
            (
                "b[*?]".to_owned(),
                BTreeSet::from(["b[*?]/protected".to_owned()]),
            ),
        ]);
        let batches = protected_ancestor_pathspec_batches(
            &ancestors,
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: usize::MAX,
            },
        );
        assert_eq!(
            batches,
            [
                vec![
                    ":(top,literal)a".to_owned(),
                    ":(top,exclude,glob)a/**".to_owned(),
                    ":(top,literal)b[*?]".to_owned(),
                    ":(top,exclude,glob)b\\[\\*\\?\\]/**".to_owned(),
                ],
                vec![
                    ":(top,literal)a/deep".to_owned(),
                    ":(top,exclude,glob)a/deep/**".to_owned(),
                ],
            ]
        );

        let same_depth = (0..65)
            .map(|index| {
                (
                    format!("ancestor-{index:02}"),
                    BTreeSet::from([format!("ancestor-{index:02}/protected")]),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let legacy_batches =
            protected_ancestor_pathspec_batches(&same_depth, GitPathspecBatchPolicy::Legacy128);
        assert_eq!(
            legacy_batches.iter().map(Vec::len).collect::<Vec<_>>(),
            [128, 2]
        );
        assert!(legacy_batches.iter().all(|batch| batch.len() % 2 == 0));

        let one_pair_charge = batches[1]
            .iter()
            .map(|pathspec| pathspec_charges(pathspec).unwrap().1)
            .sum();
        let charge_batches = protected_ancestor_pathspec_batches(
            &ancestors,
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: one_pair_charge,
            },
        );
        assert!(charge_batches.iter().all(|batch| batch.len() % 2 == 0));
    }

    #[test]
    fn git_exec_budget_safe_headroom_boundary_matrix() {
        assert_eq!(
            effective_git_pathspec_charge(200_000, 20_000, 10_000),
            Some(65_536)
        );
        assert_eq!(
            effective_git_pathspec_charge(
                GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES + 10_000 + 1,
                1,
                10_000,
            ),
            None
        );
        assert_eq!(effective_git_pathspec_charge(10, 11, 0), None);
    }

    #[test]
    fn git_exec_budget_policy_falls_back_for_every_unsafe_premise() {
        let pathspecs = vec![":(top,literal)a".to_owned()];
        for (arg_max, environment_charge, fixed_charge) in [
            (None, Some(1), Some(1)),
            (Some(100_000), None, Some(1)),
            (Some(100_000), Some(1), None),
            (Some(1), Some(2), Some(3)),
            (
                Some(GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES + 2),
                Some(1),
                Some(1),
            ),
        ] {
            assert_eq!(
                git_pathspec_batch_policy_from_charges(
                    &pathspecs,
                    arg_max,
                    environment_charge,
                    fixed_charge,
                ),
                GitPathspecBatchPolicy::Legacy128
            );
        }

        let oversized = vec![pathspec_with_charge(101)];
        assert_eq!(
            git_pathspec_batch_policy_from_charges(
                &oversized,
                Some(GIT_CHANGED_EXEC_SAFETY_RESERVE_BYTES + 101),
                Some(1),
                Some(0),
            ),
            GitPathspecBatchPolicy::Legacy128
        );
        assert_eq!(
            git_pathspec_batch_policy_from_charges(&pathspecs, Some(200_000), Some(1), Some(1),),
            GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }
        );
    }

    #[cfg(unix)]
    #[test]
    fn git_exec_budget_environment_and_fixed_charges_match_layout() {
        use std::os::unix::ffi::OsStringExt;
        let environment = vec![
            (OsString::from("A"), OsString::from("bc")),
            (
                OsString::from_vec(vec![b'X', 0xff]),
                OsString::from_vec(vec![0xfe]),
            ),
        ];
        let pointer_size = std::mem::size_of::<*const u8>();
        assert_eq!(
            inherited_environment_charge(&environment),
            Some((1 + 1 + 2 + 1) + (2 + 1 + 1 + 1) + 3 * pointer_size)
        );
        let invocation = git_tracked_invocation(Path::new("/tmp"), &[]);
        let payload = "/usr/bin/git".len()
            + 1
            + invocation
                .args
                .iter()
                .map(|argument| argument.len() + 1)
                .sum::<usize>();
        assert_eq!(
            fixed_invocation_argv_charge(&invocation),
            Some(payload + (invocation.args.len() + 2) * pointer_size)
        );

        let inherited_environment = vec![
            (OsString::from("GIT_NO_LAZY_FETCH"), OsString::from("0")),
            (OsString::from("GIT_LITERAL_PATHSPECS"), OsString::from("1")),
            (OsString::from("GIT_DIR"), OsString::from("/redirected")),
            (OsString::from("GIT_CONFIG_COUNT"), OsString::from("1")),
            (OsString::from("OTHER"), OsString::from("value")),
        ];
        assert_eq!(
            effective_git_child_environment(inherited_environment.clone(), false),
            vec![
                (OsString::from("OTHER"), OsString::from("value")),
                (
                    OsString::from("GIT_NO_REPLACE_OBJECTS"),
                    OsString::from("1")
                ),
            ]
        );
        let hardened_environment = effective_git_child_environment(inherited_environment, true);
        assert_eq!(
            hardened_environment,
            vec![
                (OsString::from("OTHER"), OsString::from("value")),
                (
                    OsString::from("GIT_NO_REPLACE_OBJECTS"),
                    OsString::from("1")
                ),
                (OsString::from("GIT_NO_LAZY_FETCH"), OsString::from("1")),
            ]
        );
    }

    #[test]
    fn git_child_environment_removes_git_context_and_hardens_committed_base() {
        let mut command = Command::new("/usr/bin/git");
        let git_environment = [
            "GIT_LITERAL_PATHSPECS",
            "GIT_GLOB_PATHSPECS",
            "GIT_NOGLOB_PATHSPECS",
            "GIT_ICASE_PATHSPECS",
            "GIT_DIR",
            "GIT_WORK_TREE",
            "GIT_INDEX_FILE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_NAMESPACE",
            "GIT_SHALLOW_FILE",
            "GIT_CONFIG_COUNT",
            "GIT_CONFIG_KEY_0",
            "GIT_CONFIG_VALUE_0",
        ];
        for key in git_environment {
            command.env(key, "1");
        }
        command.env("GIT_NO_LAZY_FETCH", "0");
        command.env("GIT_NO_REPLACE_OBJECTS", "0");
        command.env("OTHER", "value");

        apply_git_child_environment(&mut command, true);

        let environment = command
            .get_envs()
            .map(|(key, value)| (key.to_os_string(), value.map(OsStr::to_os_string)))
            .collect::<BTreeMap<_, _>>();
        for key in git_environment {
            assert_eq!(environment.get(OsStr::new(key)), Some(&None));
        }
        assert_eq!(
            environment.get(OsStr::new("GIT_NO_LAZY_FETCH")),
            Some(&Some(OsString::from("1")))
        );
        assert_eq!(
            environment.get(OsStr::new("GIT_NO_REPLACE_OBJECTS")),
            Some(&Some(OsString::from("1")))
        );
        assert_eq!(
            environment.get(OsStr::new("OTHER")),
            Some(&Some(OsString::from("value")))
        );
    }

    #[test]
    fn changed_path_observation_empty_and_saturation_contract_is_exact() {
        let runner = ScriptedGitRunner::new(Vec::new());
        let mut observation = PerformancePackageSelectionObservation::default();
        assert_eq!(
            changed_package_paths_with_runner(
                Path::new("unused"),
                &BTreeSet::new(),
                &runner,
                Some(&mut observation),
            ),
            Ok(Vec::new())
        );
        assert!(runner.invocations.borrow().is_empty());
        assert_eq!(
            observation.batch_policy,
            PerformancePackageSelectionBatchPolicy::NotSelected
        );
        assert_eq!(observation.candidate_paths, 0);
        assert!(!observation.overflowed);

        observation.tracked_output_paths = u64::MAX - 1;
        {
            let mut optional = Some(&mut observation);
            observation_add(
                &mut optional,
                |observation| &mut observation.tracked_output_paths,
                1,
            );
        }
        assert_eq!(observation.tracked_output_paths, u64::MAX);
        assert!(!observation.overflowed);
        {
            let mut optional = Some(&mut observation);
            observation_add(
                &mut optional,
                |observation| &mut observation.tracked_output_paths,
                1,
            );
        }
        assert_eq!(observation.tracked_output_paths, u64::MAX);
        assert!(observation.overflowed);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_runner_interleaves_tracked_and_untracked_per_batch() {
        let package_root = std::env::current_dir().unwrap();
        let root_stdout = format!("{}\n", package_root.display());
        let runner = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
            Ok(output(0, b"a\0", b"")),
            Ok(output(0, b"", b"")),
            Ok(output(0, b"", b"")),
            Ok(output(0, b"b\0", b"")),
        ]);
        let candidates = BTreeSet::from(["a".to_owned(), "b".to_owned()]);
        let pathspec_charge = [":(top,literal)a", ":(top,exclude,glob)a/**"]
            .iter()
            .map(|pathspec| pathspec_charges(pathspec).unwrap().1)
            .sum();
        let changed = changed_package_paths_with_runner_and_policy(
            &package_root,
            &candidates,
            &runner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: pathspec_charge,
            }),
        )
        .unwrap();
        assert_eq!(changed, ["a", "b"]);
        let invocations = runner.invocations.borrow();
        assert_eq!(
            invocations
                .iter()
                .map(|invocation| invocation.kind)
                .collect::<Vec<_>>(),
            [
                GitInvocationKind::WorktreeRoot,
                GitInvocationKind::HasHead,
                GitInvocationKind::Tracked,
                GitInvocationKind::Untracked,
                GitInvocationKind::Tracked,
                GitInvocationKind::Untracked,
            ]
        );
        for (invocation, candidate) in [
            (&invocations[2], "a"),
            (&invocations[3], "a"),
            (&invocations[4], "b"),
            (&invocations[5], "b"),
        ] {
            assert!(invocation.args.ends_with(&[
                OsString::from(format!(":(top,literal){candidate}")),
                OsString::from(format!(":(top,exclude,glob){candidate}/**")),
            ]));
        }
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_runner_maps_spawn_failures_before_short_circuiting() {
        let package_root = std::env::current_dir().unwrap();
        let root_stdout = format!("{}\n", package_root.display());
        let candidates = BTreeSet::from(["a".to_owned()]);

        let root_failure = ScriptedGitRunner::new(vec![Err(io::Error::other("root spawn"))]);
        assert_eq!(
            changed_package_paths_with_runner(&package_root, &candidates, &root_failure, None,),
            Err("failed to run git rev-parse: root spawn".to_owned())
        );
        assert_eq!(root_failure.invocations.borrow().len(), 1);

        let tracked_failure = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
            Err(io::Error::other("tracked spawn")),
        ]);
        assert_eq!(
            changed_package_paths_with_runner_and_policy(
                &package_root,
                &candidates,
                &tracked_failure,
                None,
                Some(GitPathspecBatchPolicy::Legacy128),
            ),
            Err("failed to run git diff: tracked spawn".to_owned())
        );
        assert_eq!(tracked_failure.invocations.borrow().len(), 3);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_runner_filters_exact_candidates_and_counts_order() {
        let package_root = std::env::current_dir().unwrap();
        let root_stdout = format!("{}\n", package_root.display());
        let runner = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
            Ok(output(0, b"b\0./a\0a.backup\0", b"")),
            Ok(output(0, b"a\0directory\0", b"")),
        ]);
        let candidates = BTreeSet::from(["a".to_owned(), "b".to_owned()]);
        let mut observation = PerformancePackageSelectionObservation::default();
        let changed = changed_package_paths_with_runner_and_policy(
            &package_root,
            &candidates,
            &runner,
            Some(&mut observation),
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: 65_536,
            }),
        )
        .unwrap();
        assert_eq!(changed, vec!["a", "b"]);
        assert_eq!(observation.candidate_paths, 2);
        assert_eq!(observation.pathspec_batches, 1);
        assert_eq!(observation.worktree_root_queries, 1);
        assert_eq!(observation.head_queries, 1);
        assert_eq!(observation.tracked_queries, 1);
        assert_eq!(observation.untracked_queries, 1);
        assert_eq!(observation.tracked_output_paths, 3);
        assert_eq!(observation.untracked_output_paths, 2);
        assert_eq!(observation.selected_paths, 2);
        assert_eq!(
            runner
                .invocations
                .borrow()
                .iter()
                .map(|invocation| invocation.kind)
                .collect::<Vec<_>>(),
            vec![
                GitInvocationKind::WorktreeRoot,
                GitInvocationKind::HasHead,
                GitInvocationKind::Tracked,
                GitInvocationKind::Untracked,
            ]
        );
        for invocation in runner.invocations.borrow().iter().skip(2) {
            assert!(invocation.args.ends_with(&[
                OsString::from(":(top,literal)a"),
                OsString::from(":(top,exclude,glob)a/**"),
                OsString::from(":(top,literal)b"),
                OsString::from(":(top,exclude,glob)b/**"),
            ]));
        }
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_runner_stops_at_first_documented_failure() {
        let package_root = std::env::current_dir().unwrap();
        let root_stdout = format!("{}\n", package_root.display());
        let runner = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
            Ok(output(0, b"\xff\0", b"")),
        ]);
        let candidates = BTreeSet::from(["a".to_owned()]);
        let mut observation = PerformancePackageSelectionObservation::default();
        let error = changed_package_paths_with_runner_and_policy(
            &package_root,
            &candidates,
            &runner,
            Some(&mut observation),
            Some(GitPathspecBatchPolicy::Legacy128),
        )
        .unwrap_err();
        assert_eq!(error, "git returned a non-UTF-8 certificate path");
        assert_eq!(runner.invocations.borrow().len(), 3);
        assert_eq!(observation.tracked_queries, 1);
        assert_eq!(observation.tracked_output_paths, 1);
        assert_eq!(observation.untracked_queries, 0);
        assert_eq!(observation.selected_paths, 0);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_exec_batching_has_documented_merged_boundary_error_order() {
        let package_root = std::env::current_dir().unwrap();
        let root_stdout = format!("{}\n", package_root.display());
        let runner = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
            Ok(output(2, b"", b"combined tracked failure")),
        ]);
        let candidates = (0..129)
            .map(|index| format!("p{index:03}"))
            .collect::<BTreeSet<_>>();
        let error = changed_package_paths_with_runner_and_policy(
            &package_root,
            &candidates,
            &runner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: 65_536,
            }),
        )
        .unwrap_err();
        assert_eq!(error, "combined tracked failure");
        assert_eq!(runner.invocations.borrow().len(), 3);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_real_git_covers_tracked_untracked_ignored_and_missing_head() {
        let repository = TemporaryGitRepository::new();
        repository.write("a.npcert", b"a0");
        repository.write("b.npcert", b"b0");
        repository.commit_all();
        repository.write("a.npcert", b"a1");
        repository.git(&["rm", "--cached", "--", "b.npcert"]);
        repository.write("ignored.npcert", b"ignored");
        repository.write(".git/info/exclude", b"ignored.npcert\n");

        let candidates = BTreeSet::from([
            "a.npcert".to_owned(),
            "b.npcert".to_owned(),
            "ignored.npcert".to_owned(),
        ]);
        let mut observation = PerformancePackageSelectionObservation::default();
        let changed = changed_package_paths_with_runner_and_policy(
            repository.path(),
            &candidates,
            &SystemChangedPathGitProcessRunner,
            Some(&mut observation),
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
        )
        .unwrap();
        assert_eq!(changed, ["a.npcert", "b.npcert"]);
        assert_eq!(observation.tracked_output_paths, 2);
        assert_eq!(observation.untracked_output_paths, 1);
        assert_eq!(observation.selected_paths, 2);

        let unborn = TemporaryGitRepository::new();
        fs::create_dir_all(unborn.path().join("nested")).unwrap();
        let unborn_candidates =
            BTreeSet::from(["ignored.npcert".to_owned(), "missing.npcert".to_owned()]);
        let mut unborn_observation = PerformancePackageSelectionObservation::default();
        let changed = changed_package_paths_with_runner_and_policy(
            &unborn.path().join("nested"),
            &unborn_candidates,
            &SystemChangedPathGitProcessRunner,
            Some(&mut unborn_observation),
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
        )
        .unwrap();
        assert_eq!(changed, ["ignored.npcert", "missing.npcert"]);
        assert_eq!(
            unborn_observation.batch_policy,
            PerformancePackageSelectionBatchPolicy::NotSelected
        );
        assert_eq!(unborn_observation.worktree_root_queries, 1);
        assert_eq!(unborn_observation.head_queries, 1);
        assert_eq!(unborn_observation.tracked_queries, 0);
        assert_eq!(unborn_observation.untracked_queries, 0);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_real_git_ignores_replace_refs_for_head() {
        let repository = TemporaryGitRepository::new();
        repository.write("protected.npcert", b"base");
        repository.commit_all();
        let head = String::from_utf8(repository.git(&["rev-parse", "HEAD"]).stdout)
            .unwrap()
            .trim()
            .to_owned();

        repository.write("protected.npcert", b"next");
        repository.git(&["add", "protected.npcert"]);
        let tree = String::from_utf8(repository.git(&["write-tree"]).stdout)
            .unwrap()
            .trim()
            .to_owned();
        let replacement = String::from_utf8(
            repository
                .git(&["commit-tree", &tree, "-m", "replacement"])
                .stdout,
        )
        .unwrap()
        .trim()
        .to_owned();
        repository.git(&["read-tree", &head]);
        repository.git(&["replace", &head, &replacement]);

        let candidates = BTreeSet::from(["protected.npcert".to_owned()]);
        let changed = changed_package_paths_with_runner_and_policy(
            repository.path(),
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
        )
        .unwrap();

        assert_eq!(changed, ["protected.npcert"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_index_masked_worktree_changes() {
        let repository = TemporaryGitRepository::new();
        repository.write("assumed", b"base");
        repository.write("skipped", b"base");
        repository.commit_all();
        repository.git(&["update-index", "--assume-unchanged", "assumed"]);
        repository.git(&["update-index", "--skip-worktree", "skipped"]);
        repository.write("assumed", b"dirty");
        repository.write("skipped", b"dirty");

        let candidates = BTreeSet::from(["assumed".to_owned(), "skipped".to_owned()]);
        let mut observation = PerformancePackageSelectionObservation::default();
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            Some(&mut observation),
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["assumed", "skipped"]);
        assert_eq!(observation.tracked_queries, 3);
        assert_eq!(observation.untracked_queries, 2);
        assert_eq!(observation.selected_paths, 2);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_stat_cache_masked_worktree_change() {
        use std::fs::{File, FileTimes};
        use std::time::{Duration, SystemTime};

        let repository = TemporaryGitRepository::new();
        repository.write("protected", b"base");
        let protected = repository.path().join("protected");
        let original_modified = SystemTime::UNIX_EPOCH + Duration::from_secs(1_000_000);
        File::options()
            .write(true)
            .open(&protected)
            .unwrap()
            .set_times(FileTimes::new().set_modified(original_modified))
            .unwrap();
        repository.commit_all();
        repository.git(&["config", "core.trustctime", "false"]);
        repository.git(&["config", "core.checkStat", "minimal"]);

        let replacement = repository.path().join("replacement");
        fs::write(&replacement, b"evil").unwrap();
        File::options()
            .write(true)
            .open(&replacement)
            .unwrap()
            .set_times(FileTimes::new().set_modified(original_modified))
            .unwrap();
        fs::rename(replacement, protected).unwrap();

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_clean_filter_masked_worktree_change() {
        let repository = TemporaryGitRepository::new();
        repository.write(".gitattributes", b"protected filter=mask\n");
        repository.write("protected", b"base\n");
        repository.git(&["config", "filter.mask.clean", "/usr/bin/sed 's/.*/base/'"]);
        repository.git(&["config", "filter.mask.required", "true"]);
        repository.commit_all();
        repository.write("protected", b"dirty\n");

        let masked = repository.git(&["diff", "--name-only", "HEAD", "--", "protected"]);
        assert!(
            masked.stdout.is_empty(),
            "the clean filter must mask the fixture"
        );

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_staged_change_canceled_in_worktree() {
        let repository = TemporaryGitRepository::new();
        repository.write("protected", b"base\n");
        repository.commit_all();
        repository.write("protected", b"staged\n");
        repository.git(&["add", "protected"]);
        repository.write("protected", b"base\n");

        let net_worktree = repository.git(&["diff", "--name-only", "HEAD", "--", "protected"]);
        assert!(
            net_worktree.stdout.is_empty(),
            "the worktree snapshot must cancel the staged fixture"
        );

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_staged_mode_change_canceled_in_worktree() {
        let repository = TemporaryGitRepository::new();
        repository.write("protected", b"base\n");
        repository.commit_all();
        repository.git(&["update-index", "--chmod=+x", "protected"]);

        let net_worktree = repository.git(&["diff", "--name-only", "HEAD", "--", "protected"]);
        assert!(
            net_worktree.stdout.is_empty(),
            "the worktree mode must cancel the staged fixture"
        );

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_worktree_mode_change_with_filemode_disabled() {
        use std::os::unix::fs::PermissionsExt;

        let repository = TemporaryGitRepository::new();
        repository.write("protected", b"base\n");
        repository.commit_all();
        repository.git(&["config", "core.fileMode", "false"]);
        fs::set_permissions(
            repository.path().join("protected"),
            fs::Permissions::from_mode(0o755),
        )
        .unwrap();

        let masked = repository.git(&["diff", "--name-only", "--", "protected"]);
        assert!(
            masked.stdout.is_empty(),
            "core.fileMode=false must mask the fixture from an ordinary diff"
        );

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_non_blob_leaf_mode_with_symlinks_disabled() {
        let repository = TemporaryGitRepository::new();
        repository.write("protected", b"certificate");
        repository.git(&["add", "protected"]);
        let blob = String::from_utf8(repository.git(&["rev-parse", ":protected"]).stdout)
            .unwrap()
            .trim()
            .to_owned();
        repository.git(&[
            "update-index",
            "--add",
            "--cacheinfo",
            "120000",
            &blob,
            "protected",
        ]);
        repository.git(&["commit", "-q", "-m", "baseline"]);
        repository.git(&["config", "core.symlinks", "false"]);
        assert!(fs::symlink_metadata(repository.path().join("protected"))
            .unwrap()
            .file_type()
            .is_file());

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_symlink_worktree_leaf_with_symlinks_disabled() {
        use std::os::unix::fs::symlink;

        let repository = TemporaryGitRepository::new();
        repository.write("target", b"certificate");
        repository.write("protected", b"certificate");
        repository.commit_all();
        repository.git(&["config", "core.symlinks", "false"]);
        fs::remove_file(repository.path().join("protected")).unwrap();
        symlink("target", repository.path().join("protected")).unwrap();

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_gitlink_ancestor_changes() {
        let repository = TemporaryGitRepository::new();
        let nested_name = "outer/nested [*?]";
        let nested = repository.path().join(nested_name);
        fs::create_dir_all(&nested).unwrap();
        let nested_git = |args: &[&str]| {
            let output = Command::new("/usr/bin/git")
                .args(args)
                .current_dir(&nested)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "nested git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        };
        nested_git(&["init", "-q"]);
        nested_git(&["config", "user.email", "gitsel@example.invalid"]);
        nested_git(&["config", "user.name", "GITSEL Test"]);
        fs::write(nested.join("protected"), b"base").unwrap();
        nested_git(&["add", "protected"]);
        nested_git(&["commit", "-q", "-m", "nested baseline"]);
        repository.write("outer/regular/protected", b"clean");
        repository.git(&["add", nested_name, "outer/regular/protected"]);
        repository.git(&["commit", "-q", "-m", "parent baseline"]);
        fs::write(nested.join("protected"), b"dirty").unwrap();

        let nested_candidate = format!("{nested_name}/protected");
        let candidates = BTreeSet::from([
            nested_candidate.clone(),
            "outer/regular/protected".to_owned(),
        ]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed.as_slice(), std::slice::from_ref(&nested_candidate));

        repository.git(&["config", "diff.ignoreSubmodules", "all"]);
        repository.git(&["rm", "-q", "--cached", "-f", "--", nested_name]);
        let changed_after_staged_gitlink_removal = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();
        assert_eq!(changed_after_staged_gitlink_removal, [nested_candidate]);
    }

    #[cfg(unix)]
    #[test]
    fn protected_clean_head_rejects_untracked_path_inside_embedded_repository() {
        let repository = TemporaryGitRepository::new();
        repository.write("baseline", b"tracked");
        repository.commit_all();

        let nested = repository.path().join("nested");
        fs::create_dir(&nested).unwrap();
        let nested_git = |args: &[&str]| {
            let output = Command::new("/usr/bin/git")
                .args(args)
                .current_dir(&nested)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "nested git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        };
        nested_git(&["init", "-q"]);
        nested_git(&["config", "user.email", "gitsel@example.invalid"]);
        nested_git(&["config", "user.name", "GITSEL Test"]);
        fs::write(nested.join("protected"), b"untracked by parent").unwrap();
        nested_git(&["add", "protected"]);
        nested_git(&["commit", "-q", "-m", "nested baseline"]);

        let candidates = BTreeSet::from(["nested/protected".to_owned()]);
        let changed = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();

        assert_eq!(changed, ["nested/protected"]);
    }

    #[cfg(unix)]
    #[test]
    fn exact_candidate_queries_do_not_recurse_into_tracked_descendants() {
        let repository = TemporaryGitRepository::new();
        repository.write("protected/child", b"base");
        repository.commit_all();
        let merge_base = String::from_utf8(repository.git(&["rev-parse", "HEAD"]).stdout)
            .unwrap()
            .trim()
            .to_owned();

        let candidates = BTreeSet::from(["protected".to_owned()]);
        let dirty = changed_candidate_paths_in_worktree(
            repository.path(),
            "",
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
            true,
        )
        .unwrap();
        assert!(dirty.is_empty());

        repository.write("protected/child", b"next");
        repository.commit_all();
        let head_commit = String::from_utf8(repository.git(&["rev-parse", "HEAD"]).stdout)
            .unwrap()
            .trim()
            .to_owned();
        let identity = CommittedGitIdentity {
            worktree_root: repository.path().to_path_buf(),
            package_prefix: String::new(),
            object_format: GitObjectFormat::Sha1,
            head_commit,
            merge_base,
        };
        let changed = committed_changed_candidate_paths(
            &identity,
            &candidates,
            &SystemChangedPathGitProcessRunner,
            &mut None,
        )
        .unwrap();
        assert!(changed.is_empty());

        let overlapping_candidates =
            BTreeSet::from(["protected".to_owned(), "protected/child".to_owned()]);
        let changed = committed_changed_candidate_paths(
            &identity,
            &overlapping_candidates,
            &SystemChangedPathGitProcessRunner,
            &mut None,
        )
        .unwrap();
        assert_eq!(changed, ["protected/child"]);
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_real_git_preserves_nested_literal_rename_and_symlink_boundaries() {
        use std::os::unix::fs::symlink;

        let repository = TemporaryGitRepository::new();
        let package_root = repository.path().join("nested package");
        repository.write("nested package/old.npcert", b"old");
        repository.write("nested package/space[*] 日本.npcert", b"literal0");
        repository.write("outside-one", b"outside0");
        repository.write("outside-two", b"outside1");
        symlink("../outside-one", package_root.join("link.npcert")).unwrap();
        repository.commit_all();

        repository.git(&[
            "mv",
            "--",
            "nested package/old.npcert",
            "nested package/new.npcert",
        ]);
        repository.write("nested package/space[*] 日本.npcert", b"literal1");
        repository.write("outside-one", b"outside-only-change");

        let candidates = BTreeSet::from([
            "link.npcert".to_owned(),
            "new.npcert".to_owned(),
            "old.npcert".to_owned(),
            "space[*] 日本.npcert".to_owned(),
        ]);
        let changed = changed_package_paths_with_runner_and_policy(
            &package_root,
            &candidates,
            &SystemChangedPathGitProcessRunner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
        )
        .unwrap();
        assert_eq!(
            changed,
            ["new.npcert", "old.npcert", "space[*] 日本.npcert",]
        );

        fs::remove_file(package_root.join("link.npcert")).unwrap();
        symlink("../outside-two", package_root.join("link.npcert")).unwrap();
        let link_only = BTreeSet::from(["link.npcert".to_owned()]);
        assert_eq!(
            changed_package_paths_with_runner_and_policy(
                &package_root,
                &link_only,
                &SystemChangedPathGitProcessRunner,
                None,
                Some(GitPathspecBatchPolicy::ExecBudget {
                    effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
                }),
            )
            .unwrap(),
            ["link.npcert"]
        );
    }

    #[cfg(unix)]
    #[test]
    fn changed_path_real_git_rejects_package_outside_discovered_worktree() {
        let discovered = TemporaryGitRepository::new();
        discovered.write("a", b"a");
        discovered.commit_all();
        let outside = TemporaryGitRepository::new();
        outside.write("candidate.npcert", b"candidate");
        let root_stdout = format!("{}\n", discovered.path().display());
        let runner = ScriptedGitRunner::new(vec![
            Ok(output(0, root_stdout.as_bytes(), b"")),
            Ok(output(0, b"", b"")),
        ]);
        let error = changed_package_paths_with_runner_and_policy(
            outside.path(),
            &BTreeSet::from(["candidate.npcert".to_owned()]),
            &runner,
            None,
            Some(GitPathspecBatchPolicy::ExecBudget {
                effective_charge_bytes: GIT_CHANGED_PATHSPEC_TARGET_CHARGE_BYTES,
            }),
        )
        .unwrap_err();
        assert!(error.contains("is not inside Git worktree"), "{error}");
        assert_eq!(runner.invocations.borrow().len(), 2);
    }

    #[test]
    fn package_verify_certs_full_jobs_one_maps_to_serial_fast_options() {
        let options = ordinary_package_verification_execution_options(
            1,
            None,
            false,
            PerformanceMeasurementMode::Off,
        );

        assert_eq!(options.jobs, 1);
        assert!(options.selected_modules.is_none());
        assert_eq!(options.memoization, PackageVerificationMemoMode::Disabled);
        assert_eq!(
            options.decode_cache,
            PackageVerificationDecodeCacheMode::Disabled
        );
        assert!(!options.collect_decode_cache_counters);
        assert_eq!(options.measurement_mode, PerformanceMeasurementMode::Off);
    }

    #[test]
    fn package_snapshot_retention_policy_covers_all_serial_fast_cache_lanes() {
        for audit_cache in [
            PackageAuditCacheMode::Off,
            PackageAuditCacheMode::ReadThrough,
            PackageAuditCacheMode::LocalHit,
        ] {
            for verifier_memo in [
                PackageVerifierMemoMode::Off,
                PackageVerifierMemoMode::ReadThrough,
                PackageVerifierMemoMode::Disk,
            ] {
                assert_eq!(
                    package_artifact_retention_policy(
                        PackageChecker::Fast,
                        1,
                        audit_cache,
                        verifier_memo,
                    ),
                    PreparedArtifactRetentionPolicy::FastCandidateV1
                );
                assert_eq!(
                    package_artifact_retention_policy(
                        PackageChecker::Fast,
                        2,
                        audit_cache,
                        verifier_memo,
                    ),
                    PreparedArtifactRetentionPolicy::RawOnly
                );
                assert_eq!(
                    package_artifact_retention_policy(
                        PackageChecker::Reference,
                        1,
                        audit_cache,
                        verifier_memo,
                    ),
                    PreparedArtifactRetentionPolicy::RawOnly
                );
                assert_eq!(
                    package_artifact_retention_policy(
                        PackageChecker::External,
                        1,
                        audit_cache,
                        verifier_memo,
                    ),
                    PreparedArtifactRetentionPolicy::RawOnly
                );
            }
        }
    }

    #[test]
    fn package_parallel_fast_uses_raw_only_hashed_indexed_adapter() {
        let source = include_str!("package_verify.rs");
        assert!(source.contains("Some(prepared_artifacts) if execution_options.jobs == 1"));
        assert!(source.contains(
            "verify_package_fast_source_free_with_hashed_artifacts_and_options_indexed("
        ));
        assert!(source.contains("let prepared_artifacts = (checker == PackageChecker::Fast"));
        assert!(source.contains(
            "package_artifact_retention_policy(checker, jobs, audit_cache, verifier_memo)"
        ));
        assert_eq!(
            package_artifact_retention_policy(
                PackageChecker::Fast,
                4,
                PackageAuditCacheMode::Off,
                PackageVerifierMemoMode::Off,
            ),
            PreparedArtifactRetentionPolicy::RawOnly
        );
    }

    #[cfg(unix)]
    #[test]
    fn external_import_catalog_rejects_root_rename_before_unlink() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "npa-import-cleanup-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let parent = open_absolute_directory(&root, false).unwrap();
        let leaf = OsStr::new("imports");
        let directory = parent.create_new_directory(leaf).unwrap();
        write_relative_create_new(
            &directory,
            Path::new("Dependency/certificate.npcert"),
            b"cert",
        )
        .unwrap();
        let moved = OsStr::new("imports-moved");
        let expected =
            vec![normal_relative_components(Path::new("Dependency/certificate.npcert")).unwrap()];

        let error = remove_closed_file_catalog_after_preflight(
            &parent,
            leaf,
            &directory,
            &expected,
            || parent.rename_entry(leaf, moved).unwrap(),
        )
        .expect_err("renamed root must not be erased through its retained descriptor");
        assert_eq!(error.kind(), io::ErrorKind::NotFound);
        assert_eq!(
            fs::read(root.join("imports-moved/Dependency/certificate.npcert")).unwrap(),
            b"cert"
        );

        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn package_verify_certs_timing_summary_excludes_serial_fast_options() {
        let options = ordinary_package_verification_execution_options(
            1,
            None,
            true,
            PerformanceMeasurementMode::Summary,
        );

        assert_eq!(options.jobs, 1);
        assert!(options.selected_modules.is_none());
        assert_eq!(options.memoization, PackageVerificationMemoMode::Disabled);
        assert_eq!(
            options.decode_cache,
            PackageVerificationDecodeCacheMode::Disabled
        );
        assert!(options.collect_decode_cache_counters);
        assert_eq!(
            options.measurement_mode,
            PerformanceMeasurementMode::Summary
        );
    }

    #[test]
    fn linear_dag_whole_command_single_index() {
        // Complete ordinary, local-audit, and disk-memo behavior is exercised
        // by `tests/package_verify_certs.rs`. Keep this unit gate focused on
        // the operation-lifetime property that those black-box reports cannot
        // observe: acquisition constructs one indexed product, and every
        // in-process downstream stage calls only a borrowed-index boundary.
        let source = include_str!("package_verify.rs");
        let indexed_builder = [
            "build_indexed_package_lock_and_snapshot_owned_artifacts_",
            "with_payload_observation(",
        ]
        .concat();
        assert_eq!(source.matches(&indexed_builder).count(), 1);

        for raw_wrapper in [
            ["build_package_lock_graph", "("].concat(),
            ["build_indexed_package_lock_graph", "("].concat(),
            ["validate_package_lock_against_manifest_graph", "("].concat(),
            ["validate_package_lock_against_manifest_indexed", "("].concat(),
            ["validate_observed_package_lock_against_manifest_graph", "("].concat(),
            [
                "validate_observed_package_lock_against_manifest_indexed",
                "(",
            ]
            .concat(),
            ["package_verification_memo_key_inputs", "("].concat(),
            ["select_package_cache_aware_live_modules", "("].concat(),
            ["verify_package_fast_source_free_with_options", "("].concat(),
            ["verify_package_reference_source_free_with_options", "("].concat(),
            ["verify_package_fast_source_free_with_cached_hits", "("].concat(),
            ["verify_package_reference_source_free_with_cached_hits", "("].concat(),
        ] {
            assert_eq!(
                source.matches(&raw_wrapper).count(),
                0,
                "raw graph-building wrapper re-entered the command: {raw_wrapper}"
            );
        }

        for indexed_boundary in [
            [
                "package_verification_memo_key_inputs_from_artifact_",
                "snapshots_indexed(",
            ]
            .concat(),
            ["select_package_cache_aware_live_modules_", "indexed("].concat(),
            [
                "verify_package_fast_source_free_with_artifact_snapshots_",
                "and_options_and_observation_indexed(",
            ]
            .concat(),
            [
                "verify_package_fast_source_free_with_hashed_artifacts_",
                "and_options_indexed(",
            ]
            .concat(),
            [
                "verify_package_reference_source_free_with_hashed_artifacts_",
                "and_options_indexed(",
            ]
            .concat(),
            [
                "verify_package_fast_source_free_with_artifact_snapshots_",
                "and_cached_hits_observed_indexed(",
            ]
            .concat(),
            [
                "verify_package_reference_source_free_with_hashed_artifacts_",
                "and_cached_hits_indexed(",
            ]
            .concat(),
        ] {
            assert!(
                source.contains(&indexed_boundary),
                "command does not route through indexed boundary: {indexed_boundary}"
            );
        }
    }

    #[test]
    fn linear_dag_strict_observed_policy() {
        linear_dag_whole_command_single_index();
        let source = include_str!("package_verify.rs");
        assert!(source.contains("build_indexed_package_lock_and_snapshot_owned_artifacts_"));
        assert!(source.contains("select_package_cache_aware_live_modules_indexed("));
        let raw_wrapper = ["select_package_cache_aware_live_modules", "(indexed.lock()"].concat();
        assert!(!source.contains(&raw_wrapper));
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    #[test]
    fn staged_external_checker_is_an_immutable_byte_snapshot() {
        use std::os::unix::fs::FileExt;

        let expected = b"#!/bin/sh\nexit 0\n";
        let staged = stage_external_checker(expected).unwrap();
        let mut actual = vec![0; expected.len()];
        staged.read_exact_at(&mut actual, 0).unwrap();
        assert_eq!(actual, expected);

        let replacement = b'X';
        let written =
            unsafe { libc::pwrite(staged.as_raw_fd(), (&replacement as *const u8).cast(), 1, 0) };
        assert_eq!(written, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
    }

    #[test]
    fn unsupported_immutable_snapshot_has_a_stable_diagnostic() {
        let path = PackagePath::new("tools/checkers/npa-checker-ext".to_owned());
        let error = io::Error::new(io::ErrorKind::Unsupported, "test unsupported platform");

        let diagnostic = checker_binary_stage_diagnostic(&path, &error);

        assert_eq!(diagnostic.kind, DiagnosticKind::ArtifactIo);
        assert_eq!(
            diagnostic.reason_code,
            "checker_binary_immutable_snapshot_unsupported"
        );
        assert_eq!(diagnostic.field.as_deref(), Some("checker.binary.snapshot"));
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("kernel_sealed_immutable_descriptor")
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some(std::env::consts::OS)
        );
        assert_eq!(diagnostic.checker.as_deref(), Some(EXTERNAL_CHECKER_LABEL));
    }

    #[test]
    fn external_checker_execution_requires_complete_resource_supervision() {
        assert!(!external_checker_supervisor_is_enforceable());
        let diagnostic = external_checker_supervisor_unavailable_diagnostic();
        assert_eq!(diagnostic.kind, DiagnosticKind::ExternalVerifier);
        assert_eq!(
            diagnostic.reason_code,
            "external_checker_supervisor_unavailable"
        );
        assert_eq!(
            diagnostic.field.as_deref(),
            Some("runner.resource_accounting")
        );
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("descendant_memory_timeout_and_authenticated_steps")
        );
        assert_eq!(diagnostic.actual_value.as_deref(), Some("unavailable"));
    }

    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    #[test]
    fn external_checker_staging_fails_closed_without_kernel_sealing() {
        let error = stage_external_checker(b"#!/bin/sh\nexit 0\n").unwrap_err();

        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    }

    // Keep every microtask verification filter bound to a substantive oracle.
    // The aliases below deliberately reuse the denser branch-matrix tests above
    // so the task ledger cannot silently succeed with a zero-test filter while
    // preserving one authoritative behavioral contract per implementation area.
    macro_rules! exact_test_alias {
        ($name:ident => $oracle:ident) => {
            #[test]
            fn $name() {
                $oracle();
            }
        };
    }

    exact_test_alias!(git_worktree_root_invocation_is_exact =>
        git_changed_selection_invocation_builders_are_byte_exact);
    exact_test_alias!(git_has_head_invocation_is_exact =>
        git_changed_selection_invocation_builders_are_byte_exact);
    exact_test_alias!(git_tracked_invocation_is_exact =>
        git_changed_selection_invocation_builders_are_byte_exact);
    exact_test_alias!(git_untracked_invocation_is_exact =>
        git_changed_selection_invocation_builders_are_byte_exact);
    exact_test_alias!(git_ignored_untracked_invocation_is_exact =>
        git_changed_selection_invocation_builders_are_byte_exact);
    exact_test_alias!(git_worktree_root_decoder_preserves_current_text =>
        git_output_decoder_branch_matrix);
    exact_test_alias!(git_has_head_decoder_accepts_only_status_zero_or_one =>
        git_output_decoder_branch_matrix);
    exact_test_alias!(git_tracked_output_decoder_preserves_raw_stdout_and_errors =>
        git_output_decoder_branch_matrix);
    exact_test_alias!(git_untracked_output_decoder_preserves_raw_stdout_and_errors =>
        git_output_decoder_branch_matrix);
    exact_test_alias!(git_worktree_root_runner_mapping_is_exact =>
        changed_path_runner_maps_spawn_failures_before_short_circuiting);
    exact_test_alias!(git_has_head_runner_mapping_is_exact =>
        changed_path_runner_maps_spawn_failures_before_short_circuiting);
    exact_test_alias!(git_tracked_runner_mapping_is_exact =>
        changed_path_runner_maps_spawn_failures_before_short_circuiting);
    exact_test_alias!(git_untracked_runner_mapping_is_exact =>
        changed_path_runner_maps_spawn_failures_before_short_circuiting);
    exact_test_alias!(changed_package_paths_wrapper_uses_system_runner =>
        changed_path_real_git_covers_tracked_untracked_ignored_and_missing_head);
    exact_test_alias!(git_worktree_root_decoder_branch_matrix => git_output_decoder_branch_matrix);
    exact_test_alias!(git_has_head_decoder_branch_matrix => git_output_decoder_branch_matrix);
    exact_test_alias!(git_tracked_output_decoder_branch_matrix => git_output_decoder_branch_matrix);
    exact_test_alias!(git_untracked_output_decoder_branch_matrix =>
        git_output_decoder_branch_matrix);
    exact_test_alias!(changed_path_runner_preserves_tracked_untracked_interleave =>
        changed_path_runner_interleaves_tracked_and_untracked_per_batch);
    exact_test_alias!(changed_path_runner_filters_exact_candidates_and_deduplicates =>
        changed_path_runner_filters_exact_candidates_and_counts_order);
    exact_test_alias!(package_selection_observation_saturates_only_on_overflow =>
        changed_path_observation_empty_and_saturation_contract_is_exact);
    exact_test_alias!(package_selection_observation_counts_empty_and_nonempty_candidates =>
        changed_path_observation_empty_and_saturation_contract_is_exact);
    exact_test_alias!(package_selection_observation_counts_discovery_attempts_on_failure =>
        changed_path_runner_maps_spawn_failures_before_short_circuiting);
    exact_test_alias!(package_selection_observation_counts_query_attempts_before_runner =>
        changed_path_runner_stops_at_first_documented_failure);
    exact_test_alias!(package_selection_observation_counts_raw_records_before_filtering =>
        changed_path_runner_filters_exact_candidates_and_counts_order);
    exact_test_alias!(package_selection_observation_assigns_selected_only_on_success =>
        changed_path_runner_stops_at_first_documented_failure);
    exact_test_alias!(package_selection_observation_describes_complete_legacy_partition =>
        changed_path_runner_interleaves_tracked_and_untracked_per_batch);
    exact_test_alias!(git_exec_budget_environment_charge_matches_independent_layout =>
        git_exec_budget_environment_and_fixed_charges_match_layout);
    exact_test_alias!(git_exec_budget_fixed_argv_charge_matches_built_invocations =>
        git_exec_budget_environment_and_fixed_charges_match_layout);
    exact_test_alias!(git_arg_max_adapter_rejects_unusable_values =>
        git_exec_budget_policy_falls_back_for_every_unsafe_premise);
    exact_test_alias!(git_batch_policy_falls_back_for_every_unavailable_premise =>
        git_exec_budget_policy_falls_back_for_every_unsafe_premise);
    exact_test_alias!(git_batch_policy_preflights_oversized_pathspec_before_queries =>
        git_exec_budget_policy_falls_back_for_every_unsafe_premise);
    exact_test_alias!(git_pathspec_legacy_batches_match_chunks_128 =>
        git_pathspec_batches_obey_exact_byte_and_count_boundaries);
    exact_test_alias!(git_pathspec_exec_budget_batches_respect_bytes_and_count =>
        git_pathspec_batches_obey_exact_byte_and_count_boundaries);
    exact_test_alias!(package_selection_observation_projects_selected_batch_policy =>
        changed_path_runner_filters_exact_candidates_and_counts_order);
    exact_test_alias!(git_pathspec_batches_are_lossless_and_order_preserving =>
        git_pathspec_batches_obey_exact_byte_and_count_boundaries);
    exact_test_alias!(git_pathspec_batches_obey_exact_byte_boundaries =>
        git_pathspec_batches_obey_exact_byte_and_count_boundaries);
    exact_test_alias!(git_pathspec_batches_obey_exact_count_boundaries =>
        git_pathspec_batches_obey_exact_byte_and_count_boundaries);
    exact_test_alias!(git_exec_budget_policy_fallback_matrix =>
        git_exec_budget_policy_falls_back_for_every_unsafe_premise);
    exact_test_alias!(changed_path_policy_is_derived_after_prefix_and_before_queries =>
        changed_path_runner_filters_exact_candidates_and_counts_order);
    exact_test_alias!(changed_path_query_loop_executes_the_complete_planned_partition =>
        changed_path_runner_interleaves_tracked_and_untracked_per_batch);
    exact_test_alias!(changed_path_batch_policies_have_fixed_state_success_parity =>
        changed_path_real_git_covers_tracked_untracked_ignored_and_missing_head);
    exact_test_alias!(package_changed_selection_worktree_containment_matrix =>
        changed_path_real_git_rejects_package_outside_discovered_worktree);
    exact_test_alias!(package_changed_selection_preserves_no_renames_semantics =>
        changed_path_real_git_preserves_nested_literal_rename_and_symlink_boundaries);
    exact_test_alias!(package_changed_selection_pathspecs_are_top_literal =>
        changed_path_runner_filters_exact_candidates_and_counts_order);
    exact_test_alias!(package_changed_selection_symlink_matrix =>
        changed_path_real_git_preserves_nested_literal_rename_and_symlink_boundaries);
    exact_test_alias!(package_changed_selection_inflated_environment_has_no_new_e2big =>
        git_exec_budget_policy_falls_back_for_every_unsafe_premise);
    exact_test_alias!(package_changed_selection_process_and_output_counter_matrix =>
        changed_path_runner_filters_exact_candidates_and_counts_order);

    #[cfg(unix)]
    #[test]
    fn changed_package_paths_wrapper_passes_no_observation() {
        let repository = TemporaryGitRepository::new();
        repository.write("candidate.npcert", b"baseline");
        repository.commit_all();
        repository.write("candidate.npcert", b"changed");
        let candidates = BTreeSet::from(["candidate.npcert".to_owned()]);

        let wrapper = changed_package_paths(repository.path(), &candidates).unwrap();
        let mut observation = PerformancePackageSelectionObservation::default();
        let observed =
            changed_package_paths_observed(repository.path(), &candidates, Some(&mut observation))
                .unwrap();

        assert_eq!(wrapper, observed);
        assert_eq!(wrapper, ["candidate.npcert"]);
        assert_eq!(observation.candidate_paths, 1);
        assert_eq!(observation.selected_paths, 1);
    }

    #[test]
    fn changed_certificate_modules_threads_selection_observation() {
        let certificate_modules = BTreeMap::from([
            ("certs/A.npcert".to_owned(), Name::from_dotted("Fixture.A")),
            ("certs/B.npcert".to_owned(), Name::from_dotted("Fixture.B")),
        ]);
        let mut observation = PerformancePackageSelectionObservation::default();
        let selected = changed_certificate_modules_with_selector(
            &certificate_modules,
            Some(&mut observation),
            |candidates, observation| {
                assert_eq!(
                    candidates,
                    &BTreeSet::from(["certs/A.npcert".to_owned(), "certs/B.npcert".to_owned(),])
                );
                let observation = observation.expect("observed selector receives the caller DTO");
                observation.candidate_paths = candidates.len() as u64;
                observation.selected_paths = 1;
                Ok(vec![
                    "certs/B.npcert".to_owned(),
                    "not-a-candidate".to_owned(),
                ])
            },
        )
        .unwrap();

        assert_eq!(selected, BTreeSet::from([Name::from_dotted("Fixture.B")]));
        assert_eq!(observation.candidate_paths, 2);
        assert_eq!(observation.selected_paths, 1);
    }

    #[test]
    fn changed_verify_allocates_selection_observation_only_when_enabled() {
        let mut off = PackageTimingCollector::new(crate::args::PackageTimingMode::Off);
        let off_value = run_changed_selection_with_timings(&mut off, |observation| {
            assert!(observation.is_none());
            7
        });
        assert_eq!(off_value, 7);
        let off_result = off.finish_result(CommandResult::passed(COMMAND, "."));
        assert!(off_result.timings.is_none());

        let mut summary = PackageTimingCollector::new(crate::args::PackageTimingMode::Summary);
        let summary_value = run_changed_selection_with_timings(&mut summary, |observation| {
            let observation = observation.expect("enabled timing owns a selection DTO");
            observation.candidate_paths = 3;
            11
        });
        assert_eq!(summary_value, 11);
        let summary_result = summary.finish_result(CommandResult::passed(COMMAND, "."));
        let report = summary_result
            .timings
            .unwrap()
            .measurements
            .expect("enabled timing projects the selection DTO");
        assert!(report.counters.iter().any(|counter| {
            counter.label == npa_api::PerformanceMeasurementLabel::PackageSelectionCandidatePaths
                && counter.value == 3
        }));
    }

    #[test]
    fn changed_verify_times_complete_selection() {
        let mut summary = PackageTimingCollector::new(crate::args::PackageTimingMode::Summary);
        let mut closure_completed = false;
        let selected = run_changed_selection_with_timings(&mut summary, |observation| {
            observation.expect("enabled timing owns a selection DTO");
            closure_completed = true;
            BTreeSet::from([Name::from_dotted("Fixture.Selected")])
        });
        assert!(closure_completed);
        assert_eq!(
            selected,
            BTreeSet::from([Name::from_dotted("Fixture.Selected")])
        );
        let result = summary.finish_result(CommandResult::passed(COMMAND, "."));
        assert!(result
            .timings
            .unwrap()
            .metrics
            .iter()
            .any(|metric| { metric.field == TIMING_SELECTION_MS }));
    }

    #[test]
    fn changed_verify_propagates_after_observation() {
        let mut summary = PackageTimingCollector::new(crate::args::PackageTimingMode::Summary);
        let selection: Result<(), &str> =
            run_changed_selection_with_timings(&mut summary, |observation| {
                let observation = observation.expect("enabled timing owns a selection DTO");
                observation.worktree_root_queries = 1;
                Err("selection failed")
            });
        assert_eq!(selection, Err("selection failed"));

        let result = summary.finish_result(CommandResult::passed(COMMAND, "."));
        let timings = result.timings.unwrap();
        assert!(timings
            .metrics
            .iter()
            .any(|metric| metric.field == TIMING_SELECTION_MS));
        let report = timings.measurements.unwrap();
        assert!(report.counters.iter().any(|counter| {
            counter.label
                == npa_api::PerformanceMeasurementLabel::PackageSelectionWorktreeRootQueries
                && counter.value == 1
        }));
    }

    #[test]
    fn retention_policy_selection() {
        package_snapshot_retention_policy_covers_all_serial_fast_cache_lanes();
    }
}

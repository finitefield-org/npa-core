//! Implementation of `npa package verify-certs`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
    time::{Duration, Instant},
};

#[cfg(any(target_os = "linux", target_os = "android"))]
use std::io::Write;
#[cfg(unix)]
use std::os::fd::AsRawFd;
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::os::fd::FromRawFd;
#[cfg(unix)]
use std::os::unix::process::CommandExt;

use npa_api::{
    format_hash_string, independent_checker_file_hash, independent_checker_machine_check_run,
    independent_checker_npa_checker_ext_launch_plan,
    independent_checker_resolve_checker_executable, materialize_package_phase8_requests,
    package_verification_memo_key_inputs, parse_hash_string,
    parse_independent_checker_axiom_policy_toml, parse_independent_checker_binary_registry,
    parse_independent_checker_runner_policy,
    verify_package_fast_source_free_with_cache_aware_disk_memo_hits,
    verify_package_fast_source_free_with_local_audit_cache_hits,
    verify_package_fast_source_free_with_options,
    verify_package_reference_source_free_with_cache_aware_disk_memo_hits,
    verify_package_reference_source_free_with_local_audit_cache_hits,
    verify_package_reference_source_free_with_options, IndependentCheckerAllowlistEntry,
    IndependentCheckerBinaryRegistry, IndependentCheckerMachineCheckChecker,
    IndependentCheckerMachineCheckError, IndependentCheckerMachineCheckProcess,
    IndependentCheckerMachineCheckRequestPolicy, IndependentCheckerMachineCheckResourceUsage,
    IndependentCheckerMachineCheckResult, IndependentCheckerMachineCheckRunner,
    IndependentCheckerMachineCheckStatus, IndependentCheckerPolicyFailure,
    IndependentCheckerPolicyFailureReasonCode, IndependentCheckerPolicyValidationError,
    IndependentCheckerResolvedCheckerExecutable, IndependentCheckerRunObservation,
    IndependentCheckerRunnerPolicy, PackageCertificateArtifact, PackageModuleVerificationEvidence,
    PackageModuleVerificationResult, PackageModuleVerificationStatus,
    PackagePhase8RequestMaterialization, PackageVerificationDecodeCacheCounters,
    PackageVerificationError, PackageVerificationErrorKind, PackageVerificationErrorReason,
    PackageVerificationExecutionOptions, PackageVerificationMemoCounters,
    PackageVerificationMemoMode, PackageVerificationMode, PackageVerificationReport,
    PackageVerificationStatus, PackageVerificationVerdictSource,
};
use npa_cert::{decode_module_cert, Hash, Name};
use npa_package::{
    build_package_lock_from_artifacts, build_package_lock_graph, format_package_hash,
    package_audit_cache_key, package_audit_disk_memo_key, package_audit_disk_memo_key_input,
    package_audit_disk_memo_result_entry_json, package_audit_result_entry_json, package_file_hash,
    parse_package_audit_disk_memo_result_entry_json, parse_package_audit_result_entry_json,
    parse_package_lock_json, select_package_cache_aware_live_modules, PackageArtifactError,
    PackageArtifactErrorReason, PackageAuditCacheKeyInput, PackageAuditCachedStatus,
    PackageAuditCheckerIdentity, PackageAuditImportIdentity, PackageAuditResultEntry, PackageHash,
    PackageLockArtifact, PackageLockEntry, PackageLockManifest, PackagePath,
    PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_CACHE_SCHEMA, PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR,
    PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA, PACKAGE_AUDIT_RESULT_SCHEMA,
};

use crate::args::{
    validate_package_verify_certs_options, PackageAuditCacheMode, PackageChecker,
    PackageExternalCheckerOptions, PackageLockInputMode, PackageVerifierMemoMode,
    PackageVerifyCertsOptions, PackageVerifyOptionsValidationError,
};
use crate::diagnostic::{
    CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind, DiagnosticSeverity,
};
use crate::fs::{join_package_path, render_package_path, render_package_root};
use crate::package::{load_package_root, LoadedPackageRoot};
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
const PACKAGE_EXTERNAL_RUNNER_ID: &str = "npa-cli-package-external-runner";
const PACKAGE_EXTERNAL_RUNNER_VERSION: &str = "0.1.0";
static NEXT_AUDIT_CACHE_WRITE_TEMP: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug)]
struct CertificateArtifactBuffer {
    path: PackagePath,
    bytes: Vec<u8>,
}

struct PackageLockAcquisition {
    lock: PackageLockManifest,
    artifacts: Vec<CertificateArtifactBuffer>,
    canonical_json: String,
    canonical_hash: PackageHash,
    mode: PackageLockInputMode,
}

impl PackageLockAcquisition {
    fn new(
        lock: PackageLockManifest,
        artifacts: Vec<CertificateArtifactBuffer>,
        canonical_json: String,
        mode: PackageLockInputMode,
    ) -> Self {
        let canonical_hash = package_file_hash(canonical_json.as_bytes());
        Self {
            lock,
            artifacts,
            canonical_json,
            canonical_hash,
            mode,
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
    timings: PackageTimingCollector,
    result: CommandResult,
    acquired: &PackageLockAcquisition,
) -> CommandResult {
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
/// opening that path. It intentionally does not read source, replay, metadata,
/// theorem-index, AI trace, network registry, or checker-result sidecars.
/// External checker mode additionally reads the explicitly supplied runner
/// policy, checker binary registry, checker binary, and axiom policy.
pub fn run_package_verify_certs(options: PackageVerifyCertsOptions) -> CommandResult {
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
        .spawn(move || run_package_verify_certs_on_stack(options, cache_cwd))
    {
        Ok(handle) => match handle.join() {
            Ok(result) => result,
            Err(_) => outer_timings.finish_result(CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::Internal,
                    "verify_thread_panicked",
                )],
            )),
        },
        Err(error) => outer_timings.finish_result(CommandResult::failed(
            COMMAND,
            root_display,
            vec![
                CommandDiagnostic::error(DiagnosticKind::Internal, "verify_thread_spawn_failed")
                    .with_actual_value(error.to_string()),
            ],
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
        PackageVerifyOptionsValidationError::ChangedWithExternalChecker => {
            unsupported("--changed", options.checker.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
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
) -> CommandResult {
    let checker = options.checker;
    let changed = options.changed;
    let audit_cache = options.audit_cache;
    let verifier_memo = options.verifier_memo;
    let jobs = options.jobs;
    let mut timings = PackageTimingCollector::new(options.timings);
    let loaded = match timings.time_phase(TIMING_LOAD_ROOT_MS, || {
        load_package_root(&options.common.root, COMMAND)
    }) {
        Ok(loaded) => loaded,
        Err(result) => return timings.finish_result(result),
    };

    let acquired = match acquire_package_lock(&loaded, options.package_lock_mode, &mut timings) {
        Ok(acquired) => acquired,
        Err(diagnostic) => {
            return timings.finish_result(CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };
    debug_assert_eq!(acquired.mode, options.package_lock_mode);
    debug_assert_eq!(
        acquired.canonical_hash,
        package_file_hash(acquired.canonical_json.as_bytes())
    );
    let lock = &acquired.lock;
    let artifacts = &acquired.artifacts;
    let lock_hash = acquired.canonical_hash;

    let selected_modules = if changed {
        match timings.time_phase(TIMING_SELECTION_MS, || {
            changed_certificate_modules(&loaded, lock)
        }) {
            Ok(modules) => Some(modules),
            Err(diagnostic) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
            }
        }
    } else {
        None
    };

    if checker == PackageChecker::External {
        let external_options = options
            .external
            .as_ref()
            .expect("external checker options validated before package I/O");
        let result = timings.time_phase(TIMING_CHECKER_MS, || {
            run_package_verify_external(&loaded, lock, artifacts, external_options)
        });
        return finish_result_with_package_lock_provenance(timings, result, &acquired);
    }

    if audit_cache == PackageAuditCacheMode::ReadThrough {
        let cache_cwd = cache_cwd.expect("read-through cache cwd captured before worker thread");
        let run = match verify_package_with_read_through_cache(
            checker,
            &loaded,
            lock_hash,
            lock,
            artifacts,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
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
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
            }
        };
        let result = command_result_from_audit_run(loaded.root_display, lock, run);
        return finish_result_with_package_lock_provenance(timings, result, &acquired);
    }

    if audit_cache == PackageAuditCacheMode::LocalHit {
        let cache_cwd = cache_cwd.expect("local-hit cache cwd captured before worker thread");
        let mut run = match verify_package_with_local_hit_cache(
            checker,
            &loaded,
            lock_hash,
            lock,
            artifacts,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
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
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
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
        return finish_result_with_package_lock_provenance(timings, result, &acquired);
    }

    if verifier_memo == PackageVerifierMemoMode::ReadThrough {
        let cache_cwd =
            cache_cwd.expect("read-through disk verifier memo cwd captured before worker thread");
        let run = match verify_package_with_read_through_disk_memo(
            checker,
            jobs,
            &loaded,
            lock,
            artifacts,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
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
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
            }
        };
        let result =
            command_result_from_disk_memo_run(loaded.root_display, lock, run, timings.is_enabled());
        return finish_result_with_package_lock_provenance(timings, result, &acquired);
    }

    if verifier_memo == PackageVerifierMemoMode::Disk {
        let cache_cwd = cache_cwd.expect("disk verifier memo cwd captured before worker thread");
        let run = match verify_package_with_disk_memo(
            checker,
            &loaded,
            lock,
            artifacts,
            &cache_cwd,
            &mut timings,
        ) {
            Ok(run) => run,
            Err(PackageAuditVerificationRunError::Diagnostic(diagnostic)) => {
                let result = CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
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
                return finish_result_with_package_lock_provenance(timings, result, &acquired);
            }
        };
        let result =
            command_result_from_disk_memo_run(loaded.root_display, lock, run, timings.is_enabled());
        return finish_result_with_package_lock_provenance(timings, result, &acquired);
    }

    let collect_decode_cache_counters = timings.is_enabled();
    let report = match timings.time_phase(TIMING_CHECKER_MS, || {
        let execution_options = PackageVerificationExecutionOptions {
            jobs,
            selected_modules,
            memoization: PackageVerificationMemoMode::ProcessLocal,
            collect_decode_cache_counters,
        };
        verify_package(checker, &loaded, lock, artifacts, execution_options)
    }) {
        Ok(report) => report,
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
            );
            return finish_result_with_package_lock_provenance(timings, result, &acquired);
        }
    };

    let result =
        command_result_from_report(loaded.root_display, lock, report, timings.is_enabled());
    finish_result_with_package_lock_provenance(timings, result, &acquired)
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
        let run = run_external_machine_check(loaded, lock, &policy, &resolved, module);
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
    let full_import_dir = loaded.root.join(&import_dir);
    if full_import_dir.exists() {
        fs::remove_dir_all(&full_import_dir).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "import_dir_rewrite_failed")
                    .with_path(import_dir.clone()),
            )
        })?;
    }
    fs::create_dir_all(&full_import_dir).map_err(|_| {
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
        let target = full_import_dir.join(&import.certificate.path);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|_| {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::ArtifactIo,
                        "import_certificate_dir_create_failed",
                    )
                    .with_path(import.certificate.path.clone()),
                )
            })?;
        }
        fs::write(&target, bytes).map_err(|_| {
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

fn run_external_machine_check(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    policy: &IndependentCheckerRunnerPolicy,
    checker: &VerifiedExternalChecker,
    module: &PackagePhase8RequestMaterialization,
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
    independent_checker_machine_check_run(&module.request, policy, observation).unwrap_or_else(
        |error| {
            let mut machine_error =
                IndependentCheckerMachineCheckError::new("checker_internal_error")
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
        },
    )
}

fn external_run_observation(
    root: &Path,
    _executable: &Path,
    staged_executable: &fs::File,
    argv: &[String],
    environment: &[(String, String)],
    module: &PackagePhase8RequestMaterialization,
) -> IndependentCheckerRunObservation {
    let started = Instant::now();
    #[cfg(unix)]
    let mut command = {
        let descriptor = staged_executable.as_raw_fd();
        #[cfg(any(target_os = "linux", target_os = "android"))]
        let descriptor_path = format!("/proc/self/fd/{descriptor}");
        #[cfg(not(any(target_os = "linux", target_os = "android")))]
        let descriptor_path = format!("/dev/fd/{descriptor}");
        let mut command = Command::new(descriptor_path);
        unsafe {
            command.pre_exec(move || {
                let flags = libc::fcntl(descriptor, libc::F_GETFD);
                if flags < 0
                    || libc::fcntl(descriptor, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        command
    };
    #[cfg(not(unix))]
    let mut command = Command::new(_executable);
    command
        .args(argv.iter().skip(1))
        .current_dir(root)
        .env_clear()
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (key, value) in environment {
        command.env(key, value);
    }

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            return IndependentCheckerRunObservation {
                result_id: external_machine_result_id(&module.module),
                attempt: 1,
                runner: external_runner_identity(),
                process: IndependentCheckerMachineCheckProcess::not_launched(),
                resource_usage: IndependentCheckerMachineCheckResourceUsage {
                    steps: 0,
                    memory_peak_mb: 0,
                    elapsed_ms: elapsed_ms(started),
                },
                stdout: Vec::new(),
                stderr: error.to_string().into_bytes(),
            };
        }
    };

    let timeout = Duration::from_millis(module.request.budget.timeout_ms);
    loop {
        match child.try_wait() {
            Ok(Some(_)) => {
                return match child.wait_with_output() {
                    Ok(output) => IndependentCheckerRunObservation {
                        result_id: external_machine_result_id(&module.module),
                        attempt: 1,
                        runner: external_runner_identity(),
                        process: process_from_exit_status(output.status.code()),
                        resource_usage: IndependentCheckerMachineCheckResourceUsage {
                            steps: 0,
                            memory_peak_mb: 0,
                            elapsed_ms: elapsed_ms(started),
                        },
                        stdout: output.stdout,
                        stderr: output.stderr,
                    },
                    Err(error) => IndependentCheckerRunObservation {
                        result_id: external_machine_result_id(&module.module),
                        attempt: 1,
                        runner: external_runner_identity(),
                        process: IndependentCheckerMachineCheckProcess::terminated(
                            "killed_without_exit_status",
                        ),
                        resource_usage: IndependentCheckerMachineCheckResourceUsage {
                            steps: 0,
                            memory_peak_mb: 0,
                            elapsed_ms: elapsed_ms(started),
                        },
                        stdout: Vec::new(),
                        stderr: error.to_string().into_bytes(),
                    },
                };
            }
            Ok(None) if started.elapsed() >= timeout => {
                let _ = child.kill();
                let output = child.wait_with_output();
                let (stdout, stderr) = output
                    .map(|output| (output.stdout, output.stderr))
                    .unwrap_or_else(|error| (Vec::new(), error.to_string().into_bytes()));
                return IndependentCheckerRunObservation {
                    result_id: external_machine_result_id(&module.module),
                    attempt: 1,
                    runner: external_runner_identity(),
                    process: IndependentCheckerMachineCheckProcess::terminated("timeout"),
                    resource_usage: IndependentCheckerMachineCheckResourceUsage {
                        steps: 0,
                        memory_peak_mb: 0,
                        elapsed_ms: elapsed_ms(started),
                    },
                    stdout,
                    stderr,
                };
            }
            Ok(None) => thread::sleep(Duration::from_millis(5)),
            Err(error) => {
                return IndependentCheckerRunObservation {
                    result_id: external_machine_result_id(&module.module),
                    attempt: 1,
                    runner: external_runner_identity(),
                    process: IndependentCheckerMachineCheckProcess::terminated(
                        "killed_without_exit_status",
                    ),
                    resource_usage: IndependentCheckerMachineCheckResourceUsage {
                        steps: 0,
                        memory_peak_mb: 0,
                        elapsed_ms: elapsed_ms(started),
                    },
                    stdout: Vec::new(),
                    stderr: error.to_string().into_bytes(),
                };
            }
        }
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
    let full_path = loaded.root.join(result_path);
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "machine_result_dir_create_failed",
                )
                .with_path(result_path),
            )
        })?;
    }
    fs::write(&full_path, result.canonical_json()).map_err(|_| {
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
    let full_path = join_package_path(&loaded.root, path, "external_checker.path")?;
    fs::read(full_path).map_err(|_| {
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
        .map(|artifact| (artifact.path.as_str().to_owned(), artifact.bytes.as_slice()))
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

fn process_from_exit_status(code: Option<i32>) -> IndependentCheckerMachineCheckProcess {
    code.and_then(|code| u8::try_from(code).ok())
        .map(IndependentCheckerMachineCheckProcess::exited)
        .unwrap_or_else(|| {
            IndependentCheckerMachineCheckProcess::terminated("killed_without_exit_status")
        })
}

fn elapsed_ms(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
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
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    match mode {
        PackageLockInputMode::CheckedFile => acquire_checked_package_lock(loaded, timings),
        PackageLockInputMode::ReconstructedInMemory => {
            acquire_reconstructed_package_lock(loaded, timings)
        }
    }
}

fn acquire_checked_package_lock(
    loaded: &LoadedPackageRoot,
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    let (checked_source, checked_lock) =
        timings.time_phase(TIMING_LOAD_LOCK_MS, || read_package_lock(loaded))?;
    let artifacts = timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
        read_certificate_artifacts(loaded)
    })?;
    let (_, reconstructed_json) = timings.time_phase(TIMING_BUILD_GRAPH_MS, || {
        build_canonical_package_lock(loaded, &artifacts)
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
        checked_lock,
        artifacts,
        checked_source,
        PackageLockInputMode::CheckedFile,
    ))
}

fn acquire_reconstructed_package_lock(
    loaded: &LoadedPackageRoot,
    timings: &mut PackageTimingCollector,
) -> Result<PackageLockAcquisition, Box<CommandDiagnostic>> {
    let artifacts = timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
        read_certificate_artifacts(loaded)
    })?;
    let (lock, canonical_json) = timings.time_phase(TIMING_BUILD_GRAPH_MS, || {
        build_canonical_package_lock(loaded, &artifacts)
    })?;

    Ok(PackageLockAcquisition::new(
        lock,
        artifacts,
        canonical_json,
        PackageLockInputMode::ReconstructedInMemory,
    ))
}

fn read_package_lock(
    loaded: &LoadedPackageRoot,
) -> Result<(String, PackageLockManifest), Box<CommandDiagnostic>> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let full_lock_path = join_package_path(&loaded.root, &lock_path, "package_lock.path")?;
    let lock_source = match fs::read_to_string(&full_lock_path) {
        Ok(source) => source,
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
) -> Result<Vec<CertificateArtifactBuffer>, Box<CommandDiagnostic>> {
    let mut artifacts = Vec::new();
    for (index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let bytes = read_certificate_bytes(
            loaded,
            &module.certificate,
            format!("modules[{index}].certificate"),
            Some(&module.module),
        )?;
        artifacts.push(CertificateArtifactBuffer {
            path: module.certificate.clone(),
            bytes,
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
        artifacts.push(CertificateArtifactBuffer {
            path: import.certificate.clone(),
            bytes,
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
    let full_path = join_package_path(&loaded.root, package_path, manifest_field_path)?;
    fs::read(full_path).map_err(|_| {
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
) -> Result<(PackageLockManifest, String), Box<CommandDiagnostic>> {
    let lock = build_package_lock_from_artifacts(
        &loaded.validated,
        loaded.manifest_path.clone(),
        loaded.manifest_source.as_bytes(),
        artifacts.iter().map(|artifact| PackageLockArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.as_slice(),
        }),
    )
    .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    let canonical_json = lock
        .canonical_json()
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    Ok((lock, canonical_json))
}

fn verify_package(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    execution_options: PackageVerificationExecutionOptions,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => verify_package_reference_source_free_with_options(
            &loaded.validated,
            lock,
            package_certificate_artifacts(artifacts),
            execution_options,
        ),
        PackageChecker::Fast => verify_package_fast_source_free_with_options(
            &loaded.validated,
            lock,
            package_certificate_artifacts(artifacts),
            execution_options,
        ),
        PackageChecker::External => {
            unreachable!("external checker is handled before verify_package")
        }
    }
}

fn changed_certificate_modules(
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
) -> Result<BTreeSet<Name>, Box<CommandDiagnostic>> {
    let certificate_modules = lock
        .entries
        .iter()
        .map(|entry| (entry.certificate.as_str().to_owned(), entry.module.clone()))
        .collect::<BTreeMap<_, _>>();
    let certificate_paths = certificate_modules.keys().cloned().collect::<BTreeSet<_>>();
    let changed_paths =
        changed_package_paths(&loaded.root, &certificate_paths).map_err(|error| {
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

pub(crate) fn changed_package_paths(
    package_root: &Path,
    certificate_paths: &BTreeSet<String>,
) -> Result<Vec<String>, String> {
    if certificate_paths.is_empty() {
        return Ok(Vec::new());
    }
    let worktree_root = git_worktree_root(package_root)?;
    let has_head = git_worktree_has_head(&worktree_root)?;
    let package_prefix = package_status_prefix(package_root, &worktree_root)?;
    if !has_head {
        return Ok(certificate_paths.iter().cloned().collect());
    }
    let certificate_by_worktree_path = certificate_paths
        .iter()
        .map(|certificate_path| {
            let worktree_path = if package_prefix.is_empty() {
                certificate_path.clone()
            } else {
                format!("{package_prefix}/{certificate_path}")
            };
            (worktree_path, certificate_path.clone())
        })
        .collect::<BTreeMap<_, _>>();
    let pathspecs = certificate_by_worktree_path
        .keys()
        .map(|path| format!(":(top,literal){path}"))
        .collect::<Vec<_>>();
    let mut changed = BTreeSet::new();
    // `git status` refreshes the complete index before applying pathspecs and
    // can consequently open unrelated tracked source or sidecar files. Query
    // validated certificate path batches directly so changed-only selection
    // stays within its documented Git certificate-path boundary. Batching also
    // avoids one Git process per certificate without risking an oversized
    // command line for large package closures.
    for pathspec_batch in pathspecs.chunks(128) {
        let tracked = git_changed_tracked_paths(&worktree_root, pathspec_batch)?;
        record_changed_certificate_paths(&tracked, &certificate_by_worktree_path, &mut changed)?;
        let untracked = git_untracked_paths(&worktree_root, pathspec_batch)?;
        record_changed_certificate_paths(&untracked, &certificate_by_worktree_path, &mut changed)?;
    }
    Ok(changed.into_iter().collect())
}

fn git_worktree_root(package_root: &Path) -> Result<PathBuf, String> {
    let output = Command::new("/usr/bin/git")
        .args(["rev-parse", "--show-toplevel"])
        .current_dir(package_root)
        .output()
        .map_err(|error| format!("failed to run git rev-parse: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            return Err(format!(
                "git rev-parse exited with status {}",
                output.status
            ));
        }
        return Err(stderr);
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

fn git_worktree_has_head(worktree_root: &Path) -> Result<bool, String> {
    let output = Command::new("/usr/bin/git")
        .args(["rev-parse", "--verify", "--quiet", "HEAD"])
        .current_dir(worktree_root)
        .output()
        .map_err(|error| format!("failed to run git rev-parse: {error}"))?;
    match output.status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        Some(_) | None => {
            let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
            if stderr.is_empty() {
                Err(format!(
                    "git rev-parse exited with status {}",
                    output.status
                ))
            } else {
                Err(stderr)
            }
        }
    }
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
    Ok(path_to_git_status_path(relative))
}

fn path_to_git_status_path(path: &Path) -> String {
    path.components()
        .filter_map(|component| match component {
            std::path::Component::Normal(segment) => Some(segment.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("/")
}

fn git_changed_tracked_paths(
    worktree_root: &Path,
    pathspecs: &[String],
) -> Result<Vec<u8>, String> {
    let output = Command::new("/usr/bin/git")
        .args([
            "diff",
            "--name-only",
            "-z",
            "--no-ext-diff",
            "--no-renames",
            "HEAD",
            "--",
        ])
        .args(pathspecs)
        .current_dir(worktree_root)
        .output()
        .map_err(|error| format!("failed to run git diff: {error}"))?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            Err(format!("git diff exited with status {}", output.status))
        } else {
            Err(stderr)
        }
    }
}

fn git_untracked_paths(worktree_root: &Path, pathspecs: &[String]) -> Result<Vec<u8>, String> {
    let output = Command::new("/usr/bin/git")
        .args(["ls-files", "--others", "--exclude-standard", "-z", "--"])
        .args(pathspecs)
        .current_dir(worktree_root)
        .output()
        .map_err(|error| format!("failed to run git ls-files: {error}"))?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            Err(format!("git ls-files exited with status {}", output.status))
        } else {
            Err(stderr)
        }
    }
}

fn record_changed_certificate_paths(
    stdout: &[u8],
    certificate_by_worktree_path: &BTreeMap<String, String>,
    changed: &mut BTreeSet<String>,
) -> Result<(), String> {
    for path in stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        let path = std::str::from_utf8(path)
            .map_err(|_| "git returned a non-UTF-8 certificate path".to_owned())?
            .trim_start_matches("./");
        if let Some(certificate_path) = certificate_by_worktree_path.get(path) {
            changed.insert(certificate_path.clone());
        }
    }
    Ok(())
}

fn verify_package_with_read_through_cache(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    package_lock_hash: PackageHash,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageAuditVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_audit_cache_key_inputs_for_lock(
                checker,
                loaded,
                package_lock_hash,
                lock,
                artifacts,
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
                lock,
                artifacts,
                PackageVerificationExecutionOptions {
                    jobs: 1,
                    selected_modules: None,
                    memoization: PackageVerificationMemoMode::Disabled,
                    collect_decode_cache_counters: false,
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

fn verify_package_with_local_hit_cache(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    package_lock_hash: PackageHash,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageAuditVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_audit_cache_key_inputs_for_lock(
                checker,
                loaded,
                package_lock_hash,
                lock,
                artifacts,
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
                lock,
                artifacts,
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

fn verify_package_with_read_through_disk_memo(
    checker: PackageChecker,
    jobs: usize,
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageDiskMemoVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_disk_memo_key_inputs_for_lock(checker, loaded, lock, artifacts)
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
            verify_package(
                checker,
                loaded,
                lock,
                artifacts,
                PackageVerificationExecutionOptions {
                    jobs,
                    selected_modules: None,
                    memoization: PackageVerificationMemoMode::Disabled,
                    collect_decode_cache_counters: false,
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
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    cache_cwd: &Path,
    timings: &mut PackageTimingCollector,
) -> Result<PackageDiskMemoVerificationRun, PackageAuditVerificationRunError> {
    let keyed_entries = timings
        .time_phase(TIMING_SELECTION_MS, || {
            package_disk_memo_key_inputs_for_lock(checker, loaded, lock, artifacts)
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
            select_package_cache_aware_live_modules(lock, dirty_modules.clone())
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
                lock,
                artifacts,
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
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    accepted_cache_hits: Vec<Name>,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => {
            verify_package_reference_source_free_with_local_audit_cache_hits(
                &loaded.validated,
                lock,
                package_certificate_artifacts(artifacts),
                accepted_cache_hits,
            )
        }
        PackageChecker::Fast => verify_package_fast_source_free_with_local_audit_cache_hits(
            &loaded.validated,
            lock,
            package_certificate_artifacts(artifacts),
            accepted_cache_hits,
        ),
        PackageChecker::External => {
            unreachable!("external checker is handled before local-hit verification")
        }
    }
}

fn verify_package_with_disk_memo_hits(
    checker: PackageChecker,
    loaded: &LoadedPackageRoot,
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
    accepted_memo_hits: Vec<Name>,
    dirty_modules: BTreeSet<Name>,
) -> Result<PackageVerificationReport, PackageVerificationError> {
    match checker {
        PackageChecker::Reference => {
            verify_package_reference_source_free_with_cache_aware_disk_memo_hits(
                &loaded.validated,
                lock,
                package_certificate_artifacts(artifacts),
                accepted_memo_hits,
                dirty_modules,
            )
        }
        PackageChecker::Fast => verify_package_fast_source_free_with_cache_aware_disk_memo_hits(
            &loaded.validated,
            lock,
            package_certificate_artifacts(artifacts),
            accepted_memo_hits,
            dirty_modules,
        ),
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
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
) -> Result<Vec<PackageAuditKeyedEntry>, Box<CommandDiagnostic>> {
    let graph = build_package_lock_graph(lock)
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    let mut entries = lock.entries.clone();
    entries.sort_by(|left, right| left.module.cmp(&right.module));
    let artifact_bytes = artifact_bytes_by_path(artifacts);
    let package_policy_hash = package_audit_policy_hash(loaded);
    let checker_identity = package_audit_checker_identity(checker, loaded);
    let manifest = loaded.validated.manifest();

    entries
        .into_iter()
        .enumerate()
        .map(|(entry_index, entry)| {
            let Some(bytes) = artifact_bytes.get(entry.certificate.as_str()).copied() else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                        .with_path(render_package_path(&entry.certificate))
                        .with_module(entry.module.as_dotted()),
                ));
            };
            let certificate = decode_module_cert(bytes).map_err(|error| {
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
            let key_input = PackageAuditCacheKeyInput {
                schema: PACKAGE_AUDIT_CACHE_SCHEMA.to_owned(),
                package_id: lock.package.clone(),
                package_version: lock.version.clone(),
                package_lock_schema: lock.schema.clone(),
                core_spec: manifest.core_spec.clone(),
                certificate_format: manifest.certificate_format.clone(),
                package_lock_hash,
                package_policy_hash,
                checker: checker_identity.clone(),
                module: entry.module.clone(),
                origin: entry.origin,
                certificate: entry.certificate.clone(),
                certificate_file_hash: package_file_hash(bytes),
                certificate_hash: entry.certificate_hash,
                export_hash: entry.export_hash,
                axiom_report_hash: entry.axiom_report_hash,
                direct_imports: graph.resolved_entry_imports[entry_index]
                    .iter()
                    .map(|import| PackageAuditImportIdentity {
                        module: import.module.clone(),
                        export_hash: import.export_hash,
                        certificate_hash: import.certificate_hash,
                    })
                    .collect(),
                dependency_summary_hash: None,
                enabled_core_features: certificate
                    .axiom_report
                    .core_features
                    .iter()
                    .map(|feature| feature.as_str().to_owned())
                    .collect(),
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
    lock: &PackageLockManifest,
    artifacts: &[CertificateArtifactBuffer],
) -> Result<Vec<PackageAuditKeyedEntry>, PackageVerificationError> {
    let mode = package_verification_mode_for_checker(checker);
    let inputs = package_verification_memo_key_inputs(
        &loaded.validated,
        lock,
        package_certificate_artifacts(artifacts),
        mode,
    )?;
    let mut entries = lock.entries.clone();
    entries.sort_by(|left, right| left.module.cmp(&right.module));
    let mut keyed_entries = Vec::new();
    for entry in entries {
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

fn read_package_audit_cache_lookup(cache_dir: &Path, cache_key: &str) -> PackageAuditCacheLookup {
    let path = package_audit_cache_entry_path(cache_dir, cache_key);
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return PackageAuditCacheLookup::Missing;
        }
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
    let path = package_audit_cache_entry_path(memo_dir, cache_key);
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return PackageAuditCacheLookup::Missing;
        }
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
    if fs::create_dir_all(cache_dir).is_err() {
        return false;
    }
    let path = package_audit_cache_entry_path(cache_dir, &entry.cache_key);
    let temp_index = NEXT_AUDIT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
    let temp_path = cache_dir.join(format!(
        "{}.{}.{}.tmp",
        entry.cache_key,
        std::process::id(),
        temp_index
    ));
    if fs::write(&temp_path, package_audit_result_entry_json(entry)).is_err() {
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

fn write_package_disk_memo_entry(memo_dir: &Path, entry: &PackageAuditResultEntry) -> bool {
    if fs::create_dir_all(memo_dir).is_err() {
        return false;
    }
    let path = package_audit_cache_entry_path(memo_dir, &entry.cache_key);
    let temp_index = NEXT_AUDIT_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
    let temp_path = memo_dir.join(format!(
        "{}.{}.{}.tmp",
        entry.cache_key,
        std::process::id(),
        temp_index
    ));
    if fs::write(&temp_path, package_audit_disk_memo_result_entry_json(entry)).is_err() {
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

fn package_audit_cache_entry_path(cache_dir: &Path, cache_key: &str) -> PathBuf {
    cache_dir.join(format!("{cache_key}.json"))
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
            bytes: artifact.bytes.as_slice(),
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
        "status={};evidence={};proof_evidence={}",
        module.status.as_str(),
        module.evidence.as_str(),
        module.evidence.is_proof_evidence()
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

    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    #[test]
    fn external_checker_staging_fails_closed_without_kernel_sealing() {
        let error = stage_external_checker(b"#!/bin/sh\nexit 0\n").unwrap_err();

        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    }
}

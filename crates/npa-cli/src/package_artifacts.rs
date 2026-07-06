//! Source-free package artifact extraction loading for CLR-05 commands.

use std::{fs, io, path::Path};

use npa_api::{
    build_package_audit_snapshot_source_free, extract_package_artifacts_source_free,
    PackageArtifactExtraction, PackageArtifactExtractionInput, PackageArtifactReferenceSummaryMode,
    PackageAuditCertificateInput, PackageAuditSnapshot, PackageAuditSnapshotBuildError,
    PackageAuditSnapshotInput, PackageCertificateArtifact, PackageVerificationError,
    PackageVerificationErrorKind, PackageVerificationErrorReason, PackageVerificationVerdictSource,
};
use npa_cert::Name;
use npa_package::{
    package_file_hash, parse_package_lock_json, PackageArtifactError, PackageArtifactFileReference,
    PackageLockManifest, PackagePath, ValidatedPackageManifest, PACKAGE_PUBLISH_PLAN_PATH,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

use crate::args::{PackageCheckGeneratedOptions, PackageCommonOptions, PackageTimingMode};
use crate::diagnostic::{
    CommandArtifact, CommandDiagnostic, CommandResult, CommandStatus, DiagnosticKind,
};
use crate::fs::{join_package_path, render_package_path};
use crate::package::{load_package_root, LoadedPackageRoot};
use crate::package_axiom_report::run_package_axiom_report_check_with_snapshot;
use crate::package_export_summary::run_package_export_summary_check_with_snapshot;
use crate::package_index::run_package_index_check_with_snapshot;
use crate::package_publish::run_package_publish_plan_check_with_snapshot;
use crate::package_verify::run_package_verify_certs_fast_with_snapshot;
use crate::timing::{
    PackageTimingCollector, TIMING_ARTIFACT_COMPARE_MS, TIMING_CHECKER_MS,
    TIMING_DECODE_CERTIFICATES_MS, TIMING_LOAD_LOCK_MS, TIMING_LOAD_ROOT_MS,
};

/// Package-relative path to the generated package lock.
pub const PACKAGE_LOCK_PATH: &str = "generated/package-lock.json";
/// Package-relative path to the generated package axiom report.
pub const PACKAGE_AXIOM_REPORT_PATH: &str = "generated/axiom-report.json";
/// Package-relative path to the generated package theorem index.
pub const PACKAGE_THEOREM_INDEX_PATH: &str = "generated/theorem-index.json";
/// Internal command label for PAS-17 shared snapshot check groups.
pub const PACKAGE_SHARED_SNAPSHOT_CHECK_GROUP_COMMAND: &str = "package shared-snapshot check-group";
/// Public command label for PAS-26 unified generated package checks.
pub const PACKAGE_CHECK_GENERATED_COMMAND: &str = "package check-generated";

const SHARED_SNAPSHOT_COMMAND_COUNT: usize = 5;
const PACKAGE_GENERATED_CHECK_SUBRESULTS: [PackageGeneratedCheckSubresult; 5] = [
    PackageGeneratedCheckSubresult {
        artifact: "axiom_report",
        path: PACKAGE_AXIOM_REPORT_PATH,
        command: "package axiom-report",
    },
    PackageGeneratedCheckSubresult {
        artifact: "theorem_index",
        path: PACKAGE_THEOREM_INDEX_PATH,
        command: "package index",
    },
    PackageGeneratedCheckSubresult {
        artifact: "verified_export_summary",
        path: PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
        command: "package export-summary",
    },
    PackageGeneratedCheckSubresult {
        artifact: "publish_plan",
        path: PACKAGE_PUBLISH_PLAN_PATH,
        command: "package publish-plan",
    },
    PackageGeneratedCheckSubresult {
        artifact: "fast_certificate_verification",
        path: PACKAGE_LOCK_PATH,
        command: "package verify-certs",
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PackageGeneratedCheckSubresult {
    artifact: &'static str,
    path: &'static str,
    command: &'static str,
}

#[derive(Clone, Debug)]
struct CertificateArtifactBuffer {
    path: PackagePath,
    bytes: Vec<u8>,
}

/// Which checked generated CLR-05 artifacts should be read from disk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackageGeneratedArtifactReadMode {
    /// Read `generated/axiom-report.json`.
    pub axiom_report: bool,
    /// Read `generated/theorem-index.json`.
    pub theorem_index: bool,
}

impl PackageGeneratedArtifactReadMode {
    /// Do not read checked generated CLR-05 artifacts.
    pub const fn none() -> Self {
        Self {
            axiom_report: false,
            theorem_index: false,
        }
    }

    /// Read both checked generated CLR-05 artifacts.
    pub const fn all() -> Self {
        Self {
            axiom_report: true,
            theorem_index: true,
        }
    }
}

/// Checked generated artifacts loaded only for check-mode comparisons.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedGeneratedPackageArtifacts {
    /// Checked-in axiom report JSON, when requested.
    pub axiom_report_json: Option<String>,
    /// Checked-in theorem index JSON, when requested.
    pub theorem_index_json: Option<String>,
}

/// Loaded source-free extraction output and optional checked generated artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedPackageArtifactExtraction {
    /// Sanitized package root display string for diagnostics.
    pub root_display: String,
    /// Validated package manifest used for extraction.
    pub validated: ValidatedPackageManifest,
    /// Checked package-lock JSON bytes loaded from disk.
    pub package_lock_json: String,
    /// Parsed checked package-lock manifest loaded from disk.
    pub package_lock_manifest: PackageLockManifest,
    /// Exact package-lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Source-free extraction output for later artifact projection.
    pub extraction: PackageArtifactExtraction,
    /// Checked generated artifacts requested by check mode.
    pub checked_generated: CheckedGeneratedPackageArtifacts,
}

/// Loaded process-local package audit snapshot and optional checked generated artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedPackageAuditSnapshot {
    /// Sanitized package root display string for diagnostics.
    pub root_display: String,
    /// Checked package-lock JSON bytes loaded from disk.
    pub package_lock_json: String,
    /// Source-free package audit snapshot for later artifact projection.
    pub snapshot: PackageAuditSnapshot,
    /// Checked generated artifacts requested by check mode.
    pub checked_generated: CheckedGeneratedPackageArtifacts,
}

/// Options for running a PAS-17 in-process shared package snapshot check group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageSharedSnapshotCheckGroupOptions {
    /// Common package root and output-shape options shared by every command in the group.
    pub common: PackageCommonOptions,
    /// Optional group timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Result of a PAS-17 in-process shared package snapshot check group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageSharedSnapshotCheckGroupResult {
    /// Group-level summary and optional timing telemetry.
    pub summary: CommandResult,
    /// Per-command results produced from the shared snapshot.
    pub command_results: Vec<CommandResult>,
}

/// Load and verify source-free inputs for CLR-05 package artifact commands.
///
/// This reads `npa-package.toml`, `generated/package-lock.json`, local and
/// external certificate artifacts, and optionally the checked generated CLR-05
/// artifacts. It does not read source, replay, metadata, AI trace, registry, or
/// theorem-search sidecars.
pub fn load_package_artifact_extraction(
    root: impl AsRef<Path>,
    command: impl Into<String>,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
) -> Result<LoadedPackageArtifactExtraction, CommandResult> {
    let command = command.into();
    load_package_artifact_extraction_impl(
        root.as_ref(),
        command,
        generated_read_mode,
        reference_summaries,
        None,
    )
}

pub(crate) fn load_package_artifact_extraction_with_timings(
    root: impl AsRef<Path>,
    command: impl Into<String>,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
    timings: &mut PackageTimingCollector,
) -> Result<LoadedPackageArtifactExtraction, CommandResult> {
    let command = command.into();
    load_package_artifact_extraction_impl(
        root.as_ref(),
        command,
        generated_read_mode,
        reference_summaries,
        Some(timings),
    )
}

/// Load a reusable package audit snapshot for combined in-process projections.
pub fn load_package_audit_snapshot(
    root: impl AsRef<Path>,
    command: impl Into<String>,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    let command = command.into();
    load_package_audit_snapshot_impl(
        root.as_ref(),
        command,
        generated_read_mode,
        reference_summaries,
        None,
    )
}

pub(crate) fn load_package_audit_snapshot_with_timings(
    root: impl AsRef<Path>,
    command: impl Into<String>,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
    timings: &mut PackageTimingCollector,
) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    let command = command.into();
    load_package_audit_snapshot_impl(
        root.as_ref(),
        command,
        generated_read_mode,
        reference_summaries,
        Some(timings),
    )
}

/// Run projection/check-mode commands through one process-local package audit snapshot.
///
/// This is local orchestration only. The snapshot is built from checked-in
/// source-free package artifacts, is never serialized, and is not proof
/// evidence. Standalone CLI command output remains unchanged.
pub fn run_package_shared_snapshot_check_group(
    options: PackageSharedSnapshotCheckGroupOptions,
) -> PackageSharedSnapshotCheckGroupResult {
    let mut timings = PackageTimingCollector::new(options.timings);
    let loaded = match load_package_audit_snapshot_with_timings(
        &options.common.root,
        PACKAGE_SHARED_SNAPSHOT_CHECK_GROUP_COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
        &mut timings,
    ) {
        Ok(loaded) => loaded,
        Err(result) => {
            return PackageSharedSnapshotCheckGroupResult {
                summary: timings.finish_result(result),
                command_results: Vec::new(),
            };
        }
    };

    let command_results = vec![
        run_package_axiom_report_check_with_snapshot(&loaded, &mut timings),
        run_package_index_check_with_snapshot(&loaded, &mut timings),
        run_package_export_summary_check_with_snapshot(
            &options.common,
            None,
            &loaded,
            &mut timings,
        ),
        run_package_publish_plan_check_with_snapshot(&options.common, &loaded, &mut timings),
        timings.time_phase(TIMING_CHECKER_MS, || {
            run_package_verify_certs_fast_with_snapshot(&loaded, false)
        }),
    ];

    let mut summary = if command_results
        .iter()
        .all(|result| result.status == crate::diagnostic::CommandStatus::Passed)
    {
        CommandResult::passed(
            PACKAGE_SHARED_SNAPSHOT_CHECK_GROUP_COMMAND,
            loaded.root_display.clone(),
        )
    } else {
        CommandResult::failed(
            PACKAGE_SHARED_SNAPSHOT_CHECK_GROUP_COMMAND,
            loaded.root_display.clone(),
            shared_snapshot_failure_diagnostics(&command_results),
        )
    };
    summary
        .diagnostics
        .extend(shared_snapshot_diagnostics(&loaded));

    PackageSharedSnapshotCheckGroupResult {
        summary: timings.finish_result(summary),
        command_results,
    }
}

/// Run `package check-generated` through one source-free package audit snapshot.
///
/// The command is local orchestration only. It reports deterministic aggregate
/// and per-artifact sub-results, preserves failing sub-command diagnostics, and
/// is not proof evidence.
pub fn run_package_check_generated(options: PackageCheckGeneratedOptions) -> CommandResult {
    let group = run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
        common: options.common,
        timings: options.timings,
    });
    package_check_generated_result_from_group(group)
}

fn package_check_generated_result_from_group(
    group: PackageSharedSnapshotCheckGroupResult,
) -> CommandResult {
    let PackageSharedSnapshotCheckGroupResult {
        mut summary,
        command_results,
    } = group;
    let root = summary.root.clone();
    let status = summary.status;
    let timings = summary.timings.take();
    let mut diagnostics =
        package_generated_check_diagnostics(status, &command_results, &summary.diagnostics);
    diagnostics.append(&mut summary.diagnostics);
    if status != CommandStatus::Passed {
        diagnostics.extend(package_generated_check_failure_diagnostics(
            &command_results,
        ));
    }

    let mut result = if status == CommandStatus::Passed {
        CommandResult::passed(PACKAGE_CHECK_GENERATED_COMMAND, root)
    } else {
        CommandResult::failed(PACKAGE_CHECK_GENERATED_COMMAND, root, Vec::new())
    };
    result.status = status;
    result.diagnostics = diagnostics;
    result.artifacts = package_generated_check_artifacts();
    result.timings = timings;
    result
}

fn package_generated_check_diagnostics(
    status: CommandStatus,
    command_results: &[CommandResult],
    summary_diagnostics: &[CommandDiagnostic],
) -> Vec<CommandDiagnostic> {
    let failed = command_results
        .iter()
        .filter(|result| result.status != CommandStatus::Passed)
        .count();
    let passed = command_results.len().saturating_sub(failed);
    let mut diagnostics = vec![package_generated_check_summary_diagnostic(
        status, passed, failed,
    )];
    diagnostics.extend(package_generated_check_subresult_diagnostics(
        command_results,
    ));
    if command_results.is_empty() && status != CommandStatus::Passed {
        diagnostics.push(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "package_generated_check_snapshot_failed",
            )
            .with_field("snapshot")
            .with_actual_value(format!(
                "status={};diagnostics={};proof_evidence=false",
                status.as_str(),
                summary_diagnostics.len()
            )),
        );
    }
    diagnostics
}

fn package_generated_check_summary_diagnostic(
    status: CommandStatus,
    passed: usize,
    failed: usize,
) -> CommandDiagnostic {
    let diagnostic = match status {
        CommandStatus::Passed => CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "package_generated_check_summary",
        ),
        CommandStatus::Failed => CommandDiagnostic::error(
            DiagnosticKind::GeneratedArtifact,
            "package_generated_check_summary",
        ),
    };
    diagnostic
        .with_field("aggregate")
        .with_actual_value(format!(
            "status={};artifacts={};passed={};failed={};proof_evidence=false;build_evidence=false",
            status.as_str(),
            PACKAGE_GENERATED_CHECK_SUBRESULTS.len(),
            passed,
            failed
        ))
}

fn package_generated_check_subresult_diagnostics(
    command_results: &[CommandResult],
) -> Vec<CommandDiagnostic> {
    PACKAGE_GENERATED_CHECK_SUBRESULTS
        .iter()
        .zip(command_results.iter())
        .map(|(subresult, result)| {
            let diagnostic = match result.status {
                CommandStatus::Passed => CommandDiagnostic::info(
                    DiagnosticKind::GeneratedArtifact,
                    "package_generated_check_subresult",
                ),
                CommandStatus::Failed => CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "package_generated_check_subresult",
                ),
            };
            diagnostic
                .with_path(subresult.path)
                .with_field(subresult.artifact)
                .with_actual_value(format!(
                    "command={};status={};proof_evidence=false",
                    subresult.command,
                    result.status.as_str()
                ))
        })
        .collect()
}

fn package_generated_check_failure_diagnostics(
    command_results: &[CommandResult],
) -> Vec<CommandDiagnostic> {
    command_results
        .iter()
        .filter(|result| result.status != CommandStatus::Passed)
        .flat_map(|result| result.diagnostics.iter().cloned())
        .collect()
}

fn package_generated_check_artifacts() -> Vec<CommandArtifact> {
    PACKAGE_GENERATED_CHECK_SUBRESULTS
        .iter()
        .map(|subresult| CommandArtifact {
            kind: format!("package_generated_check_{}", subresult.artifact),
            path: subresult.path.to_owned(),
        })
        .collect()
}

fn load_package_artifact_extraction_impl(
    root: &Path,
    command: String,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
    mut timings: Option<&mut PackageTimingCollector>,
) -> Result<LoadedPackageArtifactExtraction, CommandResult> {
    let loaded = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_LOAD_ROOT_MS, || {
            load_package_root(root, command.clone())
        }),
        None => load_package_root(root, command.clone()),
    }?;
    let lock_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_LOAD_LOCK_MS, || read_package_lock(&loaded)),
        None => read_package_lock(&loaded),
    };
    let (lock_source, lock) = match lock_result {
        Ok(lock) => lock,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };
    let package_lock = PackageArtifactFileReference {
        path: PackagePath::new(PACKAGE_LOCK_PATH),
        file_hash: package_file_hash(lock_source.as_bytes()),
    };
    let certificates_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
            read_certificate_artifacts(&loaded)
        }),
        None => read_certificate_artifacts(&loaded),
    };
    let certificates = match certificates_result {
        Ok(certificates) => certificates,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };
    let certificate_artifacts = package_certificate_artifacts(&certificates);
    let extraction_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_CHECKER_MS, || {
            extract_package_artifacts_source_free(PackageArtifactExtractionInput {
                validated: &loaded.validated,
                manifest_path: loaded.manifest_path.clone(),
                manifest_bytes: loaded.manifest_source.as_bytes(),
                package_lock: &lock,
                certificates: certificate_artifacts,
                reference_summaries,
            })
        }),
        None => extract_package_artifacts_source_free(PackageArtifactExtractionInput {
            validated: &loaded.validated,
            manifest_path: loaded.manifest_path.clone(),
            manifest_bytes: loaded.manifest_source.as_bytes(),
            package_lock: &lock,
            certificates: certificate_artifacts,
            reference_summaries,
        }),
    };
    let extraction = match extraction_result {
        Ok(extraction) => extraction,
        Err(error) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![extraction_error_diagnostic(&error)],
            ));
        }
    };
    let checked_generated_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
            read_checked_generated_artifacts(&loaded, generated_read_mode)
        }),
        None => read_checked_generated_artifacts(&loaded, generated_read_mode),
    };
    let checked_generated = match checked_generated_result {
        Ok(artifacts) => artifacts,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };

    Ok(LoadedPackageArtifactExtraction {
        root_display: loaded.root_display,
        validated: loaded.validated,
        package_lock_json: lock_source,
        package_lock_manifest: lock,
        package_lock,
        extraction,
        checked_generated,
    })
}

fn load_package_audit_snapshot_impl(
    root: &Path,
    command: String,
    generated_read_mode: PackageGeneratedArtifactReadMode,
    reference_summaries: PackageArtifactReferenceSummaryMode,
    mut timings: Option<&mut PackageTimingCollector>,
) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    let loaded = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_LOAD_ROOT_MS, || {
            load_package_root(root, command.clone())
        }),
        None => load_package_root(root, command.clone()),
    }?;
    let lock_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_LOAD_LOCK_MS, || read_package_lock(&loaded)),
        None => read_package_lock(&loaded),
    };
    let (lock_source, lock) = match lock_result {
        Ok(lock) => lock,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };
    let package_lock = PackageArtifactFileReference {
        path: PackagePath::new(PACKAGE_LOCK_PATH),
        file_hash: package_file_hash(lock_source.as_bytes()),
    };
    let certificates_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_DECODE_CERTIFICATES_MS, || {
            read_certificate_artifacts(&loaded)
        }),
        None => read_certificate_artifacts(&loaded),
    };
    let certificates = match certificates_result {
        Ok(certificates) => certificates,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };
    let certificate_inputs = package_audit_certificate_inputs(certificates);
    let snapshot_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_CHECKER_MS, || {
            build_package_audit_snapshot_source_free(PackageAuditSnapshotInput {
                validated: &loaded.validated,
                manifest_path: loaded.manifest_path.clone(),
                manifest_bytes: loaded.manifest_source.as_bytes(),
                package_lock_manifest: &lock,
                package_lock: package_lock.clone(),
                certificates: certificate_inputs,
                reference_summaries,
            })
        }),
        None => build_package_audit_snapshot_source_free(PackageAuditSnapshotInput {
            validated: &loaded.validated,
            manifest_path: loaded.manifest_path.clone(),
            manifest_bytes: loaded.manifest_source.as_bytes(),
            package_lock_manifest: &lock,
            package_lock: package_lock.clone(),
            certificates: certificate_inputs,
            reference_summaries,
        }),
    };
    let snapshot = match snapshot_result {
        Ok(snapshot) => snapshot,
        Err(error) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![snapshot_build_error_diagnostic(&error)],
            ));
        }
    };
    let checked_generated_result = match timings.as_mut() {
        Some(timings) => timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
            read_checked_generated_artifacts(&loaded, generated_read_mode)
        }),
        None => read_checked_generated_artifacts(&loaded, generated_read_mode),
    };
    let checked_generated = match checked_generated_result {
        Ok(artifacts) => artifacts,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display,
                vec![*diagnostic],
            ));
        }
    };

    Ok(LoadedPackageAuditSnapshot {
        root_display: loaded.root_display,
        package_lock_json: lock_source,
        snapshot,
        checked_generated,
    })
}

fn shared_snapshot_diagnostics(loaded: &LoadedPackageAuditSnapshot) -> Vec<CommandDiagnostic> {
    vec![
        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "shared_snapshot_summary")
            .with_field("shared_snapshot")
            .with_actual_value(format!(
                "commands={};snapshot_builds=1;standalone_load_root_equivalent={};shared_load_root=1;standalone_decode_equivalent={};shared_decode=1;proof_evidence=false;build_evidence=false",
                SHARED_SNAPSHOT_COMMAND_COUNT,
                SHARED_SNAPSHOT_COMMAND_COUNT,
                SHARED_SNAPSHOT_COMMAND_COUNT,
            )),
        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "shared_snapshot_root_identity")
            .with_field("root")
            .with_actual_value(loaded.root_display.clone()),
        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "shared_snapshot_commands")
            .with_field("commands")
            .with_actual_value(
                [
                    "package axiom-report",
                    "package index",
                    "package export-summary",
                    "package publish-plan",
                    "package verify-certs",
                ]
                .join(";"),
            ),
        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "shared_snapshot_boundary")
            .with_field("source_free")
            .with_actual_value(
                "source_text=false;replay=false;ai_trace=false;hidden_cache=false;network=false",
            ),
    ]
}

fn shared_snapshot_failure_diagnostics(results: &[CommandResult]) -> Vec<CommandDiagnostic> {
    let mut diagnostics = results
        .iter()
        .filter(|result| result.status != crate::diagnostic::CommandStatus::Passed)
        .map(|result| {
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "shared_snapshot_command_failed",
            )
            .with_field("command")
            .with_actual_value(result.command.clone())
        })
        .collect::<Vec<_>>();
    if diagnostics.is_empty() {
        diagnostics.push(CommandDiagnostic::error(
            DiagnosticKind::Internal,
            "shared_snapshot_failed_without_command_failure",
        ));
    }
    diagnostics
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

fn package_audit_certificate_inputs(
    artifacts: Vec<CertificateArtifactBuffer>,
) -> Vec<PackageAuditCertificateInput> {
    artifacts
        .into_iter()
        .map(|artifact| PackageAuditCertificateInput {
            path: artifact.path,
            bytes: artifact.bytes,
        })
        .collect()
}

fn read_checked_generated_artifacts(
    loaded: &LoadedPackageRoot,
    mode: PackageGeneratedArtifactReadMode,
) -> Result<CheckedGeneratedPackageArtifacts, Box<CommandDiagnostic>> {
    Ok(CheckedGeneratedPackageArtifacts {
        axiom_report_json: if mode.axiom_report {
            Some(read_generated_artifact(
                loaded,
                PACKAGE_AXIOM_REPORT_PATH,
                DiagnosticKind::AxiomReport,
                "axiom_report_missing",
            )?)
        } else {
            None
        },
        theorem_index_json: if mode.theorem_index {
            Some(read_generated_artifact(
                loaded,
                PACKAGE_THEOREM_INDEX_PATH,
                DiagnosticKind::TheoremIndex,
                "theorem_index_missing",
            )?)
        } else {
            None
        },
    })
}

fn read_generated_artifact(
    loaded: &LoadedPackageRoot,
    package_path: &str,
    kind: DiagnosticKind,
    missing_reason: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    let package_path = PackagePath::new(package_path);
    let full_path = join_package_path(&loaded.root, &package_path, "generated_artifact.path")?;
    fs::read_to_string(full_path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            missing_reason
        } else {
            "generated_artifact_read_failed"
        };
        Box::new(CommandDiagnostic::error(kind, reason).with_path(package_path.as_str()))
    })
}

fn snapshot_build_error_diagnostic(error: &PackageAuditSnapshotBuildError) -> CommandDiagnostic {
    match error {
        PackageAuditSnapshotBuildError::Verification(error) => extraction_error_diagnostic(error),
        PackageAuditSnapshotBuildError::Artifact(error) => {
            snapshot_artifact_error_diagnostic(error)
        }
    }
}

fn snapshot_artifact_error_diagnostic(error: &PackageArtifactError) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        error.reason_code.as_str(),
    )
    .with_path(error.path.clone());
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field.as_str());
    }
    if let Some(expected) = &error.expected_value {
        diagnostic = diagnostic.with_expected_value(expected.clone());
    }
    if let Some(actual) = &error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual.clone());
    }
    diagnostic
}

fn extraction_error_diagnostic(error: &PackageVerificationError) -> CommandDiagnostic {
    let reason_code = if error.reason_code == PackageVerificationErrorReason::AxiomPolicyRejected {
        "axiom_report_policy_violation"
    } else {
        error.reason_code.as_str()
    };
    let mut diagnostic = CommandDiagnostic::error(diagnostic_kind_for_error(error), reason_code)
        .with_path(error.path.clone());
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field.as_str());
    }
    if let Some(module) = &error.module {
        diagnostic = diagnostic.with_module(module.as_str());
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
    diagnostic.with_checker(
        error
            .checker_error
            .as_ref()
            .map(|checker| checker.checker.as_str())
            .unwrap_or_else(|| fallback_checker(error).as_str()),
    )
}

fn diagnostic_kind_for_error(error: &PackageVerificationError) -> DiagnosticKind {
    if error.reason_code == PackageVerificationErrorReason::AxiomPolicyRejected {
        return DiagnosticKind::PackagePolicy;
    }
    match error.kind {
        PackageVerificationErrorKind::Input => DiagnosticKind::PackageLock,
        PackageVerificationErrorKind::LockGraph => DiagnosticKind::PackageGraph,
        PackageVerificationErrorKind::Artifact => DiagnosticKind::ArtifactIo,
        PackageVerificationErrorKind::CertificateDecode => DiagnosticKind::SourceFreeBoundary,
        PackageVerificationErrorKind::CertificateIdentity => DiagnosticKind::HashMismatch,
        PackageVerificationErrorKind::Kernel => DiagnosticKind::FastVerifier,
        PackageVerificationErrorKind::ReferenceChecker => DiagnosticKind::ReferenceVerifier,
        PackageVerificationErrorKind::Phase8Adapter => DiagnosticKind::SourceFreeBoundary,
        PackageVerificationErrorKind::Dependency => DiagnosticKind::SourceFreeBoundary,
    }
}

fn is_hash_mismatch_reason(reason: PackageVerificationErrorReason) -> bool {
    matches!(
        reason,
        PackageVerificationErrorReason::PackageLockStale
            | PackageVerificationErrorReason::CertificateFileHashMismatch
            | PackageVerificationErrorReason::ExportHashMismatch
            | PackageVerificationErrorReason::AxiomReportHashMismatch
            | PackageVerificationErrorReason::CertificateHashMismatch
    )
}

fn fallback_checker(error: &PackageVerificationError) -> PackageVerificationVerdictSource {
    match error.kind {
        PackageVerificationErrorKind::ReferenceChecker => {
            PackageVerificationVerdictSource::ReferenceChecker
        }
        _ => PackageVerificationVerdictSource::FastKernelCertificateVerifier,
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicUsize, Ordering},
    };

    use npa_api::{
        project_package_axiom_report_from_extraction,
        project_package_theorem_index_from_extraction,
        project_package_verified_export_summary_from_extraction,
        PackageArtifactReferenceSummaryMode,
    };
    use npa_cert::Name;
    use npa_package::{
        build_package_lock_from_artifacts, package_axiom_report_summary,
        parse_and_validate_manifest_str, parse_package_axiom_report_json,
        parse_package_publish_plan_json, parse_package_theorem_index_json,
        parse_package_verified_export_summary_json, PackageAxiomReference, PackageHash,
        PackageLockArtifact, PackagePath, PACKAGE_PUBLISH_PLAN_PATH,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
    };

    use super::*;
    use crate::args::{
        PackageAxiomReportOptions, PackageCheckGeneratedOptions, PackageExportSummaryOptions,
        PackageIndexOptions, PackagePublishPlanOptions,
    };
    use crate::package::PACKAGE_MANIFEST_PATH;
    use crate::package_axiom_report::run_package_axiom_report;
    use crate::package_export_summary::run_package_export_summary;
    use crate::package_index::run_package_index;
    use crate::package_publish::run_package_publish_plan;

    const PROOF_CORPUS_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

    static TEST_DIR_COUNTER: AtomicUsize = AtomicUsize::new(0);

    struct TestDir {
        path: PathBuf,
    }

    impl TestDir {
        fn new(label: &str) -> Self {
            let index = TEST_DIR_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "npa-cli-package-artifact-boundary-{}-{label}-{index}",
                std::process::id()
            ));
            if path.exists() {
                fs::remove_dir_all(&path).unwrap();
            }
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }

        fn path(&self) -> &Path {
            &self.path
        }

        fn artifact_path(&self, relative: &str) -> PathBuf {
            self.path.join(relative)
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    type ProjectionFailureCase = (&'static str, fn(&TestDir), usize, &'static str);

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("npa-cli crate lives under crates/")
            .to_path_buf()
    }

    fn source_free_fixture(label: &str) -> TestDir {
        let dir = TestDir::new(label);
        let manifest_source = basic_manifest_source();
        write_file(dir.artifact_path(PACKAGE_MANIFEST_PATH), &manifest_source);
        let certificate_bytes =
            fs::read(repo_root().join("proofs").join(BASIC_CERTIFICATE_PATH)).unwrap();
        write_bytes(
            dir.artifact_path(BASIC_CERTIFICATE_PATH),
            certificate_bytes.as_slice(),
        );
        let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let lock = build_package_lock_from_artifacts(
            &validated,
            PackagePath::new(PACKAGE_MANIFEST_PATH),
            manifest_source.as_bytes(),
            [PackageLockArtifact {
                path: PackagePath::new(BASIC_CERTIFICATE_PATH),
                bytes: certificate_bytes.as_slice(),
            }],
        )
        .unwrap();
        write_file(
            dir.artifact_path(PACKAGE_LOCK_PATH),
            &lock.canonical_json().unwrap(),
        );
        dir
    }

    const BASIC_CERTIFICATE_PATH: &str = "Proofs/Ai/Basic/certificate.npcert";

    fn basic_manifest_source() -> String {
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[modules]]
module = "Proofs.Ai.Basic"
source = "missing/source/Proofs/Ai/Basic.npa"
certificate = "Proofs/Ai/Basic/certificate.npcert"
meta = "missing/meta/Proofs/Ai/Basic.json"
replay = "missing/replay/Proofs/Ai/Basic.json"
producer_profile = "human-surface-explicit-term"
expected_source_hash = "sha256:2176be7570deae66754789868aa373ab01434512b4f50b992089886d2c655387"
expected_certificate_file_hash = "sha256:448a3de71485d4f38e45ac7bf3b637b0e9e38d7ce215dd4847a2a2188099ee21"
expected_export_hash = "sha256:6cbf881b56f61d413c2584eb9b1cdd6fb09e504f6ff6c855fa73ee55d763b839"
expected_axiom_report_hash = "sha256:fed11e73accfbfb0dfc28b4f510e151fa33d8af82d58fdb23b92567e04e59e40"
expected_certificate_hash = "sha256:7a50b381af353fe15c0b602fad60f4b9d5f70613dfe6f47832da2d8c11b391dd"
imports = []
definitions = []
theorems = ["id"]
axioms = []
"#
        .to_owned()
    }

    fn write_file(path: PathBuf, contents: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, contents).unwrap();
    }

    fn write_bytes(path: PathBuf, contents: &[u8]) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, contents).unwrap();
    }

    #[test]
    fn package_projection_snapshot_reuses_one_snapshot_for_all_projection_artifacts() {
        let fixture = source_free_fixture("projection-snapshot");
        let standalone = load_package_artifact_extraction(
            fixture.path(),
            "package projection snapshot standalone",
            PackageGeneratedArtifactReadMode::none(),
            PackageArtifactReferenceSummaryMode::Omit,
        )
        .unwrap();
        let standalone_axiom_report_json = project_package_axiom_report_from_extraction(
            &standalone.validated,
            &standalone.extraction,
            standalone.package_lock.clone(),
        )
        .and_then(|report| report.canonical_json())
        .unwrap();
        let standalone_theorem_index_json = project_package_theorem_index_from_extraction(
            &standalone.validated,
            &standalone.extraction,
            standalone.package_lock.clone(),
        )
        .and_then(|index| index.canonical_json())
        .unwrap();
        let standalone_export_summary_json =
            project_package_verified_export_summary_from_extraction(
                &standalone.validated,
                &standalone.package_lock_manifest,
                standalone.package_lock.clone(),
                &standalone.extraction,
            )
            .and_then(|summary| summary.canonical_json())
            .unwrap();

        write_file(
            fixture.artifact_path(PACKAGE_AXIOM_REPORT_PATH),
            &standalone_axiom_report_json,
        );
        write_file(
            fixture.artifact_path(PACKAGE_THEOREM_INDEX_PATH),
            &standalone_theorem_index_json,
        );

        let shared = load_package_audit_snapshot(
            fixture.path(),
            "package projection snapshot shared",
            PackageGeneratedArtifactReadMode::all(),
            PackageArtifactReferenceSummaryMode::Include,
        )
        .unwrap();
        assert_eq!(shared.snapshot.certificate_artifacts.len(), 1);
        assert!(shared.snapshot.reference_verification_report.is_some());
        assert_eq!(
            shared
                .snapshot
                .projection_input_hashes
                .package_lock_file_hash,
            shared.snapshot.package_lock.file_hash
        );

        let shared_axiom_report_json = shared
            .snapshot
            .project_axiom_report()
            .and_then(|report| report.canonical_json())
            .unwrap();
        let shared_theorem_index_json = shared
            .snapshot
            .project_theorem_index()
            .and_then(|index| index.canonical_json())
            .unwrap();
        let shared_export_summary_json = shared
            .snapshot
            .project_verified_export_summary()
            .and_then(|summary| summary.canonical_json())
            .unwrap();
        assert_eq!(shared_axiom_report_json, standalone_axiom_report_json);
        assert_eq!(shared_theorem_index_json, standalone_theorem_index_json);
        assert_eq!(shared_export_summary_json, standalone_export_summary_json);

        let shared_publish_inputs =
            crate::package_publish::load_package_publish_inputs_from_snapshot(shared).unwrap();
        let shared_publish_plan_json =
            crate::package_publish::project_package_publish_plan_from_inputs(
                &shared_publish_inputs,
            )
            .unwrap()
            .canonical_json()
            .unwrap();

        let standalone_publish_inputs =
            crate::package_publish::load_package_publish_inputs(fixture.path()).unwrap();
        let standalone_publish_plan_json =
            crate::package_publish::project_package_publish_plan_from_inputs(
                &standalone_publish_inputs,
            )
            .unwrap()
            .canonical_json()
            .unwrap();
        assert_eq!(shared_publish_plan_json, standalone_publish_plan_json);
    }

    #[test]
    fn package_shared_snapshot_check_group_matches_standalone_projection_checks() {
        let fixture = source_free_fixture("shared-snapshot-group");
        write_checked_projection_artifacts(&fixture);

        let standalone = standalone_projection_check_results(&fixture);
        let shared =
            run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                timings: PackageTimingMode::Off,
            });

        assert_eq!(
            shared.summary.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(shared.command_results.len(), SHARED_SNAPSHOT_COMMAND_COUNT);
        for (index, expected) in standalone.iter().enumerate() {
            assert_eq!(
                shared.command_results[index].render_json(),
                expected.render_json()
            );
        }
        assert!(shared
            .command_results
            .iter()
            .all(|result| !result.render_json().contains("\"timings\"")));
        let summary_json = shared.summary.render_json();
        assert!(summary_json.contains("\"reason_code\":\"shared_snapshot_summary\""));
        assert!(summary_json.contains("snapshot_builds=1"));
        assert!(summary_json.contains("standalone_load_root_equivalent=5;shared_load_root=1"));
        assert!(summary_json.contains("proof_evidence=false"));

        let cache_root = repo_root().join("target/npa-package-audit-cache");
        let _ = fs::remove_dir_all(cache_root);
        let after_cache_delete =
            run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                timings: PackageTimingMode::Off,
            });
        assert_eq!(
            after_cache_delete.summary.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        for (index, expected) in standalone.iter().enumerate() {
            assert_eq!(
                after_cache_delete.command_results[index].render_json(),
                expected.render_json()
            );
        }
    }

    #[test]
    fn package_shared_snapshot_check_group_matches_standalone_projection_failures() {
        let cases: [ProjectionFailureCase; 4] = [
            (
                "shared-snapshot-failure-axiom",
                tamper_axiom_report_payload,
                0,
                "axiom_report_stale",
            ),
            (
                "shared-snapshot-failure-index",
                tamper_theorem_index_payload,
                1,
                "theorem_index_stale",
            ),
            (
                "shared-snapshot-failure-export",
                tamper_export_summary_payload,
                2,
                "verified_export_summary_stale",
            ),
            (
                "shared-snapshot-failure-publish",
                tamper_publish_plan_payload,
                3,
                "publish_plan_stale",
            ),
        ];

        for (label, tamper, failed_index, reason_code) in cases {
            let fixture = source_free_fixture(label);
            write_checked_projection_artifacts(&fixture);
            tamper(&fixture);

            let standalone = standalone_projection_check_results(&fixture);
            assert_projection_failure(standalone[failed_index].clone(), reason_code);

            let shared =
                run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
                    common: PackageCommonOptions {
                        root: fixture.path().to_path_buf(),
                        json: true,
                    },
                    timings: PackageTimingMode::Off,
                });

            assert_eq!(
                shared.summary.exit_code(),
                crate::diagnostic::CommandExitCode::PackageFailure
            );
            assert_eq!(shared.command_results.len(), SHARED_SNAPSHOT_COMMAND_COUNT);
            assert_eq!(
                shared.command_results[failed_index].render_json(),
                standalone[failed_index].render_json()
            );
            let summary_json = shared.summary.render_json();
            assert!(summary_json.contains("\"reason_code\":\"shared_snapshot_command_failed\""));
            assert!(summary_json.contains(&standalone[failed_index].command));
        }
    }

    #[test]
    fn package_shared_snapshot_timing_reports_one_load_and_decode_for_command_group() {
        let fixture = source_free_fixture("shared-snapshot-timings");
        write_checked_projection_artifacts(&fixture);

        let shared =
            run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                timings: PackageTimingMode::Summary,
            });

        assert_eq!(
            shared.summary.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        let summary_json = shared.summary.render_json();
        assert!(summary_json.contains("\"timings\""));
        assert!(summary_json.contains("\"load_root_ms\":"));
        assert!(summary_json.contains("\"load_lock_ms\":"));
        assert!(summary_json.contains("\"decode_certificates_ms\":"));
        assert!(summary_json.contains("\"checker_ms\":"));
        assert!(summary_json.contains("standalone_decode_equivalent=5;shared_decode=1"));
        assert!(summary_json.contains("source_text=false;replay=false;ai_trace=false"));
    }

    #[test]
    fn package_shared_snapshot_proof_corpus_check_group_succeeds_with_checked_in_artifacts() {
        let root = repo_root().join("proofs");
        let generated_paths = [
            PACKAGE_AXIOM_REPORT_PATH,
            PACKAGE_THEOREM_INDEX_PATH,
            PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
            PACKAGE_PUBLISH_PLAN_PATH,
        ];
        let before = generated_paths
            .iter()
            .map(|path| (*path, fs::read(root.join(path)).unwrap()))
            .collect::<Vec<_>>();

        let root_for_run = root.clone();
        let shared = run_with_proof_corpus_stack(move || {
            run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
                common: PackageCommonOptions {
                    root: root_for_run,
                    json: true,
                },
                timings: PackageTimingMode::Summary,
            })
        });

        assert_eq!(
            shared.summary.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(shared.command_results.len(), SHARED_SNAPSHOT_COMMAND_COUNT);
        assert!(shared
            .command_results
            .iter()
            .all(|result| result.exit_code() == crate::diagnostic::CommandExitCode::Success));
        let summary_json = shared.summary.render_json();
        assert!(summary_json.contains("\"reason_code\":\"shared_snapshot_summary\""));
        assert!(summary_json.contains("\"proof_evidence\":false"));
        assert!(summary_json.contains("\"timings\""));
        assert!(summary_json.contains("\"load_root_ms\":"));
        assert!(summary_json.contains("\"load_lock_ms\":"));
        assert!(summary_json.contains("\"decode_certificates_ms\":"));
        assert!(summary_json.contains("\"checker_ms\":"));
        assert!(summary_json.contains("standalone_load_root_equivalent=5;shared_load_root=1"));

        for (path, expected) in before {
            assert_eq!(fs::read(root.join(path)).unwrap(), expected);
        }
    }

    #[test]
    fn package_generated_check_command_reports_aggregate_and_subresults() {
        let fixture = source_free_fixture("check-generated-success");
        write_checked_projection_artifacts(&fixture);

        let result = run_package_check_generated(PackageCheckGeneratedOptions {
            common: PackageCommonOptions {
                root: fixture.path().to_path_buf(),
                json: true,
            },
            timings: PackageTimingMode::Off,
        });

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(result.command, PACKAGE_CHECK_GENERATED_COMMAND);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.reason_code == "package_generated_check_subresult")
                .count(),
            SHARED_SNAPSHOT_COMMAND_COUNT
        );
        let json = result.render_json();
        assert!(json.contains("\"reason_code\":\"package_generated_check_summary\""));
        assert!(json.contains("status=passed;artifacts=5;passed=5;failed=0"));
        assert!(json.contains("\"path\":\"generated/axiom-report.json\""));
        assert!(json.contains("\"path\":\"generated/theorem-index.json\""));
        assert!(json.contains("\"path\":\"generated/verified-export-summary.json\""));
        assert!(json.contains("\"path\":\"generated/publish-plan.json\""));
        assert!(json.contains("\"path\":\"generated/package-lock.json\""));
        assert!(json.contains("proof_evidence=false"));
        assert!(json.contains("\"reason_code\":\"shared_snapshot_summary\""));
    }

    #[test]
    fn package_generated_check_command_preserves_original_failure_diagnostic() {
        let fixture = source_free_fixture("check-generated-failure");
        write_checked_projection_artifacts(&fixture);
        tamper_publish_plan_payload(&fixture);

        let standalone = standalone_projection_check_results(&fixture);
        assert_projection_failure(standalone[3].clone(), "publish_plan_stale");

        let result = run_package_check_generated(PackageCheckGeneratedOptions {
            common: PackageCommonOptions {
                root: fixture.path().to_path_buf(),
                json: true,
            },
            timings: PackageTimingMode::Off,
        });

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::PackageFailure
        );
        let json = result.render_json();
        assert!(json.contains("\"reason_code\":\"package_generated_check_summary\""));
        assert!(json.contains("status=failed;artifacts=5;passed=4;failed=1"));
        assert!(json.contains("\"reason_code\":\"package_generated_check_subresult\""));
        assert!(json.contains("command=package publish-plan;status=failed"));
        assert!(json.contains("\"reason_code\":\"publish_plan_stale\""));
        assert!(json.contains("\"path\":\"generated/publish-plan.json\""));
    }

    #[test]
    fn package_generated_check_command_timing_reports_one_snapshot_pipeline() {
        let fixture = source_free_fixture("check-generated-timings");
        write_checked_projection_artifacts(&fixture);

        let result = run_package_check_generated(PackageCheckGeneratedOptions {
            common: PackageCommonOptions {
                root: fixture.path().to_path_buf(),
                json: true,
            },
            timings: PackageTimingMode::Summary,
        });

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        let json = result.render_json();
        assert!(json.contains("\"command\":\"package check-generated\""));
        assert!(json.contains("\"timings\""));
        assert!(json.contains("\"load_root_ms\":"));
        assert!(json.contains("\"load_lock_ms\":"));
        assert!(json.contains("\"decode_certificates_ms\":"));
        assert!(json.contains("\"checker_ms\":"));
        assert!(json.contains("standalone_load_root_equivalent=5;shared_load_root=1"));
        assert!(json.contains("standalone_decode_equivalent=5;shared_decode=1"));
    }

    #[test]
    fn package_projection_incremental_check_reuses_checked_artifact_json() {
        let fixture = source_free_fixture("projection-incremental");
        write_checked_projection_artifacts(&fixture);

        let results = [
            run_package_axiom_report(PackageAxiomReportOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            run_package_index(PackageIndexOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            run_package_export_summary(PackageExportSummaryOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                out: None,
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
        ];

        for result in results {
            assert_eq!(
                result.exit_code(),
                crate::diagnostic::CommandExitCode::Success
            );
            let json = result.render_json();
            assert!(json.contains("\"timings\""));
            assert!(json.contains("\"projection_ms\":"));
            assert!(json.contains("\"proof_evidence\":false"));
        }
    }

    #[test]
    fn package_projection_incremental_check_rejects_canonical_payload_tamper() {
        let axiom = source_free_fixture("projection-incremental-tamper-axiom");
        write_checked_projection_artifacts(&axiom);
        tamper_axiom_report_payload(&axiom);
        assert_projection_failure(
            run_package_axiom_report(PackageAxiomReportOptions {
                common: PackageCommonOptions {
                    root: axiom.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "axiom_report_stale",
        );

        let index = source_free_fixture("projection-incremental-tamper-index");
        write_checked_projection_artifacts(&index);
        tamper_theorem_index_payload(&index);
        assert_projection_failure(
            run_package_index(PackageIndexOptions {
                common: PackageCommonOptions {
                    root: index.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "theorem_index_stale",
        );

        let export_summary = source_free_fixture("projection-incremental-tamper-export");
        write_checked_projection_artifacts(&export_summary);
        tamper_export_summary_payload(&export_summary);
        assert_projection_failure(
            run_package_export_summary(PackageExportSummaryOptions {
                common: PackageCommonOptions {
                    root: export_summary.path().to_path_buf(),
                    json: true,
                },
                out: None,
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "verified_export_summary_stale",
        );

        let publish = source_free_fixture("projection-incremental-tamper-publish");
        write_checked_projection_artifacts(&publish);
        tamper_publish_plan_payload(&publish);
        assert_projection_failure(
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: publish.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "publish_plan_stale",
        );

        let publish_axiom_input = source_free_fixture("projection-incremental-publish-axiom-input");
        write_checked_projection_artifacts(&publish_axiom_input);
        tamper_axiom_report_payload(&publish_axiom_input);
        assert_projection_failure(
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: publish_axiom_input.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "axiom_report_stale",
        );

        let publish_index_input = source_free_fixture("projection-incremental-publish-index-input");
        write_checked_projection_artifacts(&publish_index_input);
        tamper_theorem_index_payload(&publish_index_input);
        assert_projection_failure(
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: publish_index_input.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Summary,
            }),
            "theorem_index_stale",
        );
    }

    #[test]
    fn package_artifact_source_free_boundary_ignores_source_replay_meta_and_unrequested_generated()
    {
        let fixture = source_free_fixture("no-source-sidecars");
        assert!(!fixture
            .artifact_path("missing/source/Proofs/Ai/Basic.npa")
            .exists());
        assert!(!fixture
            .artifact_path("missing/meta/Proofs/Ai/Basic.json")
            .exists());
        assert!(!fixture
            .artifact_path("missing/replay/Proofs/Ai/Basic.json")
            .exists());
        assert!(!fixture.artifact_path(PACKAGE_AXIOM_REPORT_PATH).exists());
        assert!(!fixture.artifact_path(PACKAGE_THEOREM_INDEX_PATH).exists());

        let loaded = load_package_artifact_extraction(
            fixture.path(),
            "package axiom-report",
            PackageGeneratedArtifactReadMode::none(),
            PackageArtifactReferenceSummaryMode::Omit,
        )
        .unwrap();

        assert_eq!(loaded.extraction.verified_modules.len(), 1);
        assert!(loaded.checked_generated.axiom_report_json.is_none());
        assert!(loaded.checked_generated.theorem_index_json.is_none());
    }

    fn write_checked_projection_artifacts(fixture: &TestDir) {
        assert_eq!(
            run_package_axiom_report(PackageAxiomReportOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: false,
                timings: PackageTimingMode::Off,
            })
            .exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(
            run_package_index(PackageIndexOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: false,
                timings: PackageTimingMode::Off,
            })
            .exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(
            run_package_export_summary(PackageExportSummaryOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                out: None,
                check: false,
                timings: PackageTimingMode::Off,
            })
            .exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: false,
                timings: PackageTimingMode::Off,
            })
            .exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert!(fixture.artifact_path(PACKAGE_AXIOM_REPORT_PATH).exists());
        assert!(fixture.artifact_path(PACKAGE_THEOREM_INDEX_PATH).exists());
        assert!(fixture
            .artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)
            .exists());
        assert!(fixture.artifact_path(PACKAGE_PUBLISH_PLAN_PATH).exists());
    }

    fn tamper_axiom_report_payload(fixture: &TestDir) {
        let path = fixture.artifact_path(PACKAGE_AXIOM_REPORT_PATH);
        let mut report =
            parse_package_axiom_report_json(&fs::read_to_string(&path).unwrap()).unwrap();
        let module = &mut report.modules[0];
        module.direct_axioms.push(PackageAxiomReference {
            module: module.module.clone(),
            name: Name::from_dotted("tampered_axiom"),
            export_hash: module.export_hash,
            decl_interface_hash: PackageHash::new([0x7a; 32]),
        });
        report.summary = package_axiom_report_summary(&report.modules);
        let report = report.with_computed_hash().unwrap();
        write_file(path, &report.canonical_json().unwrap());
    }

    fn tamper_theorem_index_payload(fixture: &TestDir) {
        let path = fixture.artifact_path(PACKAGE_THEOREM_INDEX_PATH);
        let mut index =
            parse_package_theorem_index_json(&fs::read_to_string(&path).unwrap()).unwrap();
        index.entries[0].tags.push("tampered".to_owned());
        let index = index.with_computed_hash().unwrap();
        write_file(path, &index.canonical_json().unwrap());
    }

    fn tamper_export_summary_payload(fixture: &TestDir) {
        let path = fixture.artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH);
        let mut summary =
            parse_package_verified_export_summary_json(&fs::read_to_string(&path).unwrap())
                .unwrap();
        summary.modules[0]
            .core_features
            .push("tampered_feature".to_owned());
        let summary = summary.with_computed_hash().unwrap();
        write_file(path, &summary.canonical_json().unwrap());
    }

    fn tamper_publish_plan_payload(fixture: &TestDir) {
        let path = fixture.artifact_path(PACKAGE_PUBLISH_PLAN_PATH);
        let mut plan =
            parse_package_publish_plan_json(&fs::read_to_string(&path).unwrap()).unwrap();
        plan.downstream_import_bundle.modules[0]
            .exported_declarations
            .push(Name::from_dotted("tampered_decl"));
        let plan = plan.with_computed_hash().unwrap();
        write_file(path, &plan.canonical_json().unwrap());
    }

    fn assert_projection_failure(result: CommandResult, reason_code: &str) {
        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::PackageFailure
        );
        assert_eq!(result.diagnostics[0].reason_code, reason_code);
    }

    fn standalone_projection_check_results(fixture: &TestDir) -> Vec<CommandResult> {
        [
            run_package_axiom_report(PackageAxiomReportOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Off,
            }),
            run_package_index(PackageIndexOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Off,
            }),
            run_package_export_summary(PackageExportSummaryOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                out: None,
                check: true,
                timings: PackageTimingMode::Off,
            }),
            run_package_publish_plan(PackagePublishPlanOptions {
                common: PackageCommonOptions {
                    root: fixture.path().to_path_buf(),
                    json: true,
                },
                check: true,
                timings: PackageTimingMode::Off,
            }),
        ]
        .into_iter()
        .collect()
    }

    fn run_with_proof_corpus_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(PROOF_CORPUS_TEST_STACK_SIZE)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn package_artifact_source_free_boundary_reads_generated_only_when_check_mode_requests_it() {
        let fixture = source_free_fixture("checked-generated");
        write_file(
            fixture.artifact_path(PACKAGE_AXIOM_REPORT_PATH),
            "{\"schema\":\"npa.package.axiom_report.v0.1\"}",
        );
        write_file(
            fixture.artifact_path(PACKAGE_THEOREM_INDEX_PATH),
            "{\"schema\":\"npa.package.theorem_index.v0.1\"}",
        );

        let loaded = load_package_artifact_extraction(
            fixture.path(),
            "package index",
            PackageGeneratedArtifactReadMode::all(),
            PackageArtifactReferenceSummaryMode::Omit,
        )
        .unwrap();

        assert_eq!(
            loaded.checked_generated.axiom_report_json.as_deref(),
            Some("{\"schema\":\"npa.package.axiom_report.v0.1\"}")
        );
        assert_eq!(
            loaded.checked_generated.theorem_index_json.as_deref(),
            Some("{\"schema\":\"npa.package.theorem_index.v0.1\"}")
        );

        let missing = source_free_fixture("missing-generated");
        let result = load_package_artifact_extraction(
            missing.path(),
            "package index",
            PackageGeneratedArtifactReadMode::all(),
            PackageArtifactReferenceSummaryMode::Omit,
        )
        .unwrap_err();
        assert_eq!(result.diagnostics[0].reason_code, "axiom_report_missing");
        assert_eq!(result.diagnostics[0].kind, DiagnosticKind::AxiomReport);
    }
}

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
use crate::generated_artifact_writer::read_regular_file_no_follow;
use crate::package::{load_package_root, LoadedPackageRoot};
use crate::package_axiom_report::run_package_axiom_report_check_with_snapshot;
use crate::package_export_summary::run_package_export_summary_check_with_snapshot;
use crate::package_index::run_package_index_check_with_snapshot;
use crate::package_publish::run_package_publish_plan_check_with_snapshot;
use crate::package_theorem_premise_report::run_package_theorem_premise_report_check_with_snapshot;
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
/// Package-relative path to the generated package theorem-premise report.
pub const PACKAGE_THEOREM_PREMISE_REPORT_PATH: &str = "generated/theorem-premise-report.json";
/// Internal command label for PAS-17 shared snapshot check groups.
pub const PACKAGE_SHARED_SNAPSHOT_CHECK_GROUP_COMMAND: &str = "package shared-snapshot check-group";
/// Public command label for PAS-26 unified generated package checks.
pub const PACKAGE_CHECK_GENERATED_COMMAND: &str = "package check-generated";

const SHARED_SNAPSHOT_COMMAND_COUNT: usize = 6;
const PACKAGE_GENERATED_CHECK_SUBRESULTS: [PackageGeneratedCheckSubresult; 6] = [
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
        artifact: "theorem_premise_report",
        path: PACKAGE_THEOREM_PREMISE_REPORT_PATH,
        command: "package theorem-premise-report",
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
    /// Read `generated/theorem-premise-report.json`.
    pub theorem_premise_report: bool,
}

impl PackageGeneratedArtifactReadMode {
    /// Do not read checked generated CLR-05 artifacts.
    pub const fn none() -> Self {
        Self {
            axiom_report: false,
            theorem_index: false,
            theorem_premise_report: false,
        }
    }

    /// Read all checked generated source-free audit artifacts.
    pub const fn all() -> Self {
        Self {
            axiom_report: true,
            theorem_index: true,
            theorem_premise_report: true,
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
    /// Checked-in theorem-premise report JSON, when requested.
    pub theorem_premise_report_json: Option<String>,
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
        run_package_theorem_premise_report_check_with_snapshot(&loaded, &mut timings),
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
                    "package theorem-premise-report",
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
        theorem_premise_report_json: if mode.theorem_premise_report {
            Some(read_checked_theorem_premise_report(loaded)?)
        } else {
            None
        },
    })
}

fn read_checked_theorem_premise_report(
    loaded: &LoadedPackageRoot,
) -> Result<String, Box<CommandDiagnostic>> {
    let failure = |reason| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                .with_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        )
    };
    let generated = loaded.root.join("generated");
    let parent = match fs::symlink_metadata(&generated) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(failure("theorem_premise_report_missing"));
        }
        Err(_) => return Err(failure("generated_artifact_read_failed")),
    };
    let parent_type = parent.file_type();
    if !parent_type.is_dir() || parent_type.is_symlink() {
        return Err(failure("generated_artifact_read_failed"));
    }

    let target = generated.join("theorem-premise-report.json");
    let metadata = match fs::symlink_metadata(&target) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(failure("theorem_premise_report_missing"));
        }
        Err(_) => return Err(failure("generated_artifact_read_failed")),
    };
    let file_type = metadata.file_type();
    if !file_type.is_file() || file_type.is_symlink() {
        return Err(failure("generated_artifact_read_failed"));
    }
    let bytes = read_regular_file_no_follow(&target)
        .map_err(|_| failure("generated_artifact_read_failed"))?;
    String::from_utf8(bytes).map_err(|_| failure("generated_artifact_read_failed"))
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

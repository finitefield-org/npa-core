//! Implementation of `npa package axiom-report`.

use std::{fs, io};

use npa_api::{project_package_axiom_report_from_extraction, PackageArtifactReferenceSummaryMode};
use npa_package::{
    format_package_hash, package_axiom_report_incremental_projection_plan, package_file_hash,
    parse_package_axiom_report_json, PackageArtifactError, PackageArtifactErrorReason,
    PackageArtifactFileReference, PackageAxiomReport, PackageAxiomReportIncrementalProjectionInput,
    PackagePath,
};

use crate::args::{PackageAxiomReportOptions, PackageCommonOptions};
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::join_package_path;
use crate::package_artifacts::{
    load_package_artifact_extraction_with_timings, LoadedPackageArtifactExtraction,
    LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
};
use crate::timing::{
    PackageTimingCollector, TIMING_ARTIFACT_COMPARE_MS, TIMING_JSON_WRITE_MS, TIMING_PROJECTION_MS,
};

const COMMAND: &str = "package axiom-report";

/// Run `package axiom-report`.
pub fn run_package_axiom_report(options: PackageAxiomReportOptions) -> CommandResult {
    let mut timings = PackageTimingCollector::new(options.timings);
    let result = if options.check {
        run_package_axiom_report_check(options.common, &mut timings)
    } else {
        run_package_axiom_report_write(options.common, &mut timings)
    };
    timings.finish_result(result)
}

fn run_package_axiom_report_check(
    options: PackageCommonOptions,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let loaded = match load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        PackageGeneratedArtifactReadMode {
            axiom_report: true,
            theorem_index: false,
        },
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    ) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let checked_json = loaded
        .checked_generated
        .axiom_report_json
        .as_deref()
        .expect("axiom report check mode reads the checked artifact");
    let checked_report = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_axiom_report_json(checked_json)
    }) {
        Ok(report) => report,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    let checked_policy_violations = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        policy_violation_diagnostics(&checked_report)
    });
    if !checked_policy_violations.is_empty() {
        return CommandResult::failed(COMMAND, loaded.root_display, checked_policy_violations);
    }
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        axiom_report_incremental_plan_for_loaded(&loaded, &checked_report)
    }) {
        Ok(plan) => plan,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    if incremental_plan.is_incremental_unchanged() {
        let report = match project_axiom_report_from_loaded(&loaded, timings) {
            Ok(report) => report,
            Err(result) => return result,
        };
        let report_stale =
            timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_report != report);
        if report_stale {
            let report_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json()) {
                    Ok(json) => json,
                    Err(error) => {
                        return CommandResult::failed(
                            COMMAND,
                            loaded.root_display,
                            vec![metadata_extraction_diagnostic(error)],
                        );
                    }
                };
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![stale_report_diagnostic(checked_json, &report_json)],
            );
        }
        record_incremental_reuse_json(timings, checked_json);
        return passed_result(loaded.root_display);
    }
    let (report, report_json) = match generate_axiom_report_from_loaded(&loaded, timings) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let generated_policy_violations = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        policy_violation_diagnostics(&report)
    });
    if !generated_policy_violations.is_empty() {
        return CommandResult::failed(COMMAND, loaded.root_display, generated_policy_violations);
    }
    let report_stale =
        timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != report_json);
    if report_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![stale_report_diagnostic(checked_json, &report_json)],
        );
    }

    passed_result(loaded.root_display)
}

pub(crate) fn run_package_axiom_report_check_with_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let checked_json = loaded
        .checked_generated
        .axiom_report_json
        .as_deref()
        .expect("shared snapshot axiom-report check reads the checked artifact");
    let checked_report = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_axiom_report_json(checked_json)
    }) {
        Ok(report) => report,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    let checked_policy_violations = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        policy_violation_diagnostics(&checked_report)
    });
    if !checked_policy_violations.is_empty() {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            checked_policy_violations,
        );
    }
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        axiom_report_incremental_plan_for_snapshot(loaded, &checked_report)
    }) {
        Ok(plan) => plan,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    if incremental_plan.is_incremental_unchanged() {
        let report = match timings.time_phase(TIMING_PROJECTION_MS, || {
            loaded.snapshot.project_axiom_report()
        }) {
            Ok(report) => report,
            Err(error) => {
                return CommandResult::failed(
                    COMMAND,
                    loaded.root_display.clone(),
                    vec![metadata_extraction_diagnostic(error)],
                );
            }
        };
        let report_stale =
            timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_report != report);
        if report_stale {
            let report_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json()) {
                    Ok(json) => json,
                    Err(error) => {
                        return CommandResult::failed(
                            COMMAND,
                            loaded.root_display.clone(),
                            vec![metadata_extraction_diagnostic(error)],
                        );
                    }
                };
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![stale_report_diagnostic(checked_json, &report_json)],
            );
        }
        record_incremental_reuse_json(timings, checked_json);
        return passed_result(loaded.root_display.clone());
    }
    let report = match timings.time_phase(TIMING_PROJECTION_MS, || {
        loaded.snapshot.project_axiom_report()
    }) {
        Ok(report) => report,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let report_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let generated_policy_violations = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        policy_violation_diagnostics(&report)
    });
    if !generated_policy_violations.is_empty() {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            generated_policy_violations,
        );
    }
    let report_stale =
        timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != report_json);
    if report_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![stale_report_diagnostic(checked_json, &report_json)],
        );
    }

    passed_result(loaded.root_display.clone())
}

fn run_package_axiom_report_write(
    options: PackageCommonOptions,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let (loaded, report, report_json) =
        match generate_axiom_report(&options, PackageGeneratedArtifactReadMode::none(), timings) {
            Ok(generated) => generated,
            Err(result) => return result,
        };
    let policy_violations = policy_violation_diagnostics(&report);
    if !policy_violations.is_empty() {
        return CommandResult::failed(COMMAND, loaded.root_display, policy_violations);
    }
    let write_result = timings.time_phase(TIMING_JSON_WRITE_MS, || {
        write_axiom_report(&options, report_json.as_bytes())
    });
    if let Err(diagnostic) = write_result {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
    }

    passed_result(loaded.root_display)
}

fn generate_axiom_report(
    options: &PackageCommonOptions,
    read_mode: PackageGeneratedArtifactReadMode,
    timings: &mut PackageTimingCollector,
) -> Result<(LoadedPackageArtifactExtraction, PackageAxiomReport, String), CommandResult> {
    let loaded = load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        read_mode,
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    )?;
    let (report, report_json) = generate_axiom_report_from_loaded(&loaded, timings)?;
    Ok((loaded, report, report_json))
}

fn generate_axiom_report_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<(PackageAxiomReport, String), CommandResult> {
    let report = project_axiom_report_from_loaded(loaded, timings)?;
    let report_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            ));
        }
    };
    Ok((report, report_json))
}

fn project_axiom_report_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<PackageAxiomReport, CommandResult> {
    match timings.time_phase(TIMING_PROJECTION_MS, || {
        project_package_axiom_report_from_extraction(
            &loaded.validated,
            &loaded.extraction,
            loaded.package_lock.clone(),
        )
    }) {
        Ok(report) => Ok(report),
        Err(error) => Err(CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![metadata_extraction_diagnostic(error)],
        )),
    }
}

fn axiom_report_incremental_plan_for_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    checked_report: &PackageAxiomReport,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.validated.manifest();
    let manifest_ref = PackageArtifactFileReference {
        path: loaded.extraction.manifest.path.clone(),
        file_hash: loaded.extraction.manifest.file_hash,
    };
    let policy = npa_package::PackageArtifactPolicy {
        allow_custom_axioms: manifest.policy.allow_custom_axioms,
        allowed_axioms: manifest.policy.allowed_axioms.clone(),
    };
    package_axiom_report_incremental_projection_plan(PackageAxiomReportIncrementalProjectionInput {
        report: checked_report,
        package: &manifest.package,
        version: &manifest.version,
        manifest: &manifest_ref,
        package_lock: &loaded.package_lock,
        policy: &policy,
        checker_summaries: &loaded.extraction.checker_summaries,
        current_lock: &loaded.package_lock_manifest,
    })
}

fn axiom_report_incremental_plan_for_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    checked_report: &PackageAxiomReport,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.snapshot.validated.manifest();
    let extraction = loaded.snapshot.fast_projection_extraction();
    let manifest_ref = PackageArtifactFileReference {
        path: loaded.snapshot.manifest.path.clone(),
        file_hash: loaded.snapshot.manifest.file_hash,
    };
    package_axiom_report_incremental_projection_plan(PackageAxiomReportIncrementalProjectionInput {
        report: checked_report,
        package: &manifest.package,
        version: &manifest.version,
        manifest: &manifest_ref,
        package_lock: &loaded.snapshot.package_lock,
        policy: &loaded.snapshot.policy,
        checker_summaries: &extraction.checker_summaries,
        current_lock: &loaded.snapshot.package_lock_manifest,
    })
}

fn record_incremental_reuse_json(timings: &mut PackageTimingCollector, checked_json: &str) {
    timings.time_phase(TIMING_JSON_WRITE_MS, || checked_json.len());
}

fn write_axiom_report(
    options: &PackageCommonOptions,
    report_json: &[u8],
) -> Result<(), Box<CommandDiagnostic>> {
    let package_path = PackagePath::new(PACKAGE_AXIOM_REPORT_PATH);
    let full_path = join_package_path(&options.root, &package_path, "generated.axiom_report.path")?;
    match fs::read(&full_path) {
        Ok(existing) if existing == report_json => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(Box::new(write_failed_diagnostic())),
    }
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).map_err(|_| Box::new(write_failed_diagnostic()))?;
    }
    fs::write(full_path, report_json).map_err(|_| Box::new(write_failed_diagnostic()))
}

fn passed_result(root_display: String) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "package_axiom_report".to_owned(),
        path: PACKAGE_AXIOM_REPORT_PATH.to_owned(),
    });
    result
}

fn artifact_error_diagnostic(error: &PackageArtifactError) -> CommandDiagnostic {
    let reason_code = match error.reason_code {
        PackageArtifactErrorReason::NonCanonicalOrder => "axiom_report_non_canonical_order",
        PackageArtifactErrorReason::SelfHashMismatch => "axiom_report_hash_mismatch",
        _ => error.reason_code.as_str(),
    };
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::AxiomReport, reason_code)
        .with_path(PACKAGE_AXIOM_REPORT_PATH);
    if let Some(field) = error.field.clone().or_else(|| {
        if error.path == "$" {
            None
        } else {
            Some(error.path.clone())
        }
    }) {
        diagnostic = diagnostic.with_field(field);
    }
    if error.reason_code == PackageArtifactErrorReason::SelfHashMismatch {
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

fn metadata_extraction_diagnostic(error: PackageArtifactError) -> CommandDiagnostic {
    let message = error.to_string();
    CommandDiagnostic::error(DiagnosticKind::AxiomReport, "metadata_extraction_failed")
        .with_path(PACKAGE_AXIOM_REPORT_PATH)
        .with_field(error.path)
        .with_actual_value(message)
}

fn stale_report_diagnostic(checked_json: &str, generated_json: &str) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::AxiomReport, "axiom_report_stale")
        .with_path(PACKAGE_AXIOM_REPORT_PATH)
        .with_hashes(
            format_package_hash(&package_file_hash(generated_json.as_bytes())),
            format_package_hash(&package_file_hash(checked_json.as_bytes())),
        )
}

fn write_failed_diagnostic() -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "generated_artifact_write_failed",
    )
    .with_path(PACKAGE_AXIOM_REPORT_PATH)
}

fn policy_violation_diagnostics(report: &PackageAxiomReport) -> Vec<CommandDiagnostic> {
    report
        .modules
        .iter()
        .flat_map(|module| {
            module
                .policy_status
                .violations
                .iter()
                .map(|violation| {
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "axiom_report_policy_violation",
                    )
                    .with_path(PACKAGE_AXIOM_REPORT_PATH)
                    .with_module(module.module.as_dotted())
                    .with_field("policy_status.violations")
                    .with_expected_value("package axiom policy satisfied")
                    .with_actual_value(format!(
                        "{} {}.{} export_hash={} decl_interface_hash={}",
                        violation.reason_code.as_str(),
                        violation.axiom.module.as_dotted(),
                        violation.axiom.name.as_dotted(),
                        format_package_hash(&violation.axiom.export_hash),
                        format_package_hash(&violation.axiom.decl_interface_hash)
                    ))
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

//! Implementation of `npa package export-summary`.

use std::{fs, io, path::Path};

use npa_api::{
    project_package_verified_export_summary_from_extraction, PackageArtifactReferenceSummaryMode,
};
use npa_package::{
    format_package_hash, package_file_hash,
    package_verified_export_summary_incremental_projection_plan,
    parse_package_verified_export_summary_json,
    validate_package_verified_export_summary_against_lock, PackageArtifactError,
    PackageArtifactErrorReason, PackagePath, PackageVerifiedExportSummary,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

use crate::args::{PackageCommonOptions, PackageExportSummaryOptions};
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{join_package_path, render_package_root};
use crate::package_artifacts::{
    load_package_artifact_extraction_with_timings, LoadedPackageArtifactExtraction,
    LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode,
};
use crate::timing::{
    PackageTimingCollector, TIMING_ARTIFACT_COMPARE_MS, TIMING_JSON_WRITE_MS, TIMING_PROJECTION_MS,
    TIMING_SELECTION_MS,
};

const COMMAND: &str = "package export-summary";

/// Run `package export-summary`.
pub fn run_package_export_summary(options: PackageExportSummaryOptions) -> CommandResult {
    let mut timings = PackageTimingCollector::new(options.timings);
    let result = if options.check {
        run_package_export_summary_check(options.common, options.out.as_deref(), &mut timings)
    } else {
        run_package_export_summary_write(options.common, options.out.as_deref(), &mut timings)
    };
    timings.finish_result(result)
}

fn run_package_export_summary_check(
    options: PackageCommonOptions,
    out: Option<&Path>,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let target = match timings.time_phase(TIMING_SELECTION_MS, || output_path(out)) {
        Ok(path) => path,
        Err(diagnostic) => {
            return CommandResult::failed(
                COMMAND,
                render_package_root(&options.root),
                vec![*diagnostic],
            );
        }
    };
    let loaded = match load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        PackageGeneratedArtifactReadMode::none(),
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    ) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let checked_json = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        read_export_summary(&options, &target)
    }) {
        Ok(json) => json,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };
    let checked_summary = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_verified_export_summary_json(&checked_json)
    }) {
        Ok(summary) => summary,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![artifact_error_diagnostic(&target, &error)],
            );
        }
    };
    if let Err(error) = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        validate_package_verified_export_summary_against_lock(
            &checked_summary,
            &loaded.package_lock_manifest,
            loaded.package_lock.file_hash,
        )
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![artifact_error_diagnostic(&target, &error)],
        );
    }
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        export_summary_incremental_plan_for_loaded(&loaded, &checked_summary)
    }) {
        Ok(plan) => plan,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![artifact_error_diagnostic(&target, &error)],
            );
        }
    };
    if incremental_plan.is_incremental_unchanged() {
        let summary = match project_export_summary_from_loaded(&loaded, timings) {
            Ok(summary) => summary,
            Err(result) => return result,
        };
        let summary_stale =
            timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_summary != summary);
        if summary_stale {
            let summary_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || summary.canonical_json()) {
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
                vec![stale_summary_diagnostic(
                    &target,
                    &checked_json,
                    &summary_json,
                )],
            );
        }
        record_incremental_reuse_json(timings, &checked_json);
        return passed_result(loaded.root_display, &target);
    }
    let (_summary, summary_json) = match generate_export_summary_from_loaded(&loaded, timings) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let summary_stale =
        timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != summary_json);
    if summary_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![stale_summary_diagnostic(
                &target,
                &checked_json,
                &summary_json,
            )],
        );
    }

    passed_result(loaded.root_display, &target)
}

pub(crate) fn run_package_export_summary_check_with_snapshot(
    options: &PackageCommonOptions,
    out: Option<&Path>,
    loaded: &LoadedPackageAuditSnapshot,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let target = match timings.time_phase(TIMING_SELECTION_MS, || output_path(out)) {
        Ok(path) => path,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
    };
    let checked_json = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        read_export_summary(options, &target)
    }) {
        Ok(json) => json,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic]);
        }
    };
    let checked_summary = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_verified_export_summary_json(&checked_json)
    }) {
        Ok(summary) => summary,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![artifact_error_diagnostic(&target, &error)],
            );
        }
    };
    if let Err(error) = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        validate_package_verified_export_summary_against_lock(
            &checked_summary,
            &loaded.snapshot.package_lock_manifest,
            loaded.snapshot.package_lock.file_hash,
        )
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![artifact_error_diagnostic(&target, &error)],
        );
    }
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        export_summary_incremental_plan_for_snapshot(loaded, &checked_summary)
    }) {
        Ok(plan) => plan,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![artifact_error_diagnostic(&target, &error)],
            );
        }
    };
    if incremental_plan.is_incremental_unchanged() {
        let summary = match timings.time_phase(TIMING_PROJECTION_MS, || {
            loaded.snapshot.project_verified_export_summary()
        }) {
            Ok(summary) => summary,
            Err(error) => {
                return CommandResult::failed(
                    COMMAND,
                    loaded.root_display.clone(),
                    vec![metadata_extraction_diagnostic(error)],
                );
            }
        };
        let summary_stale =
            timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_summary != summary);
        if summary_stale {
            let summary_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || summary.canonical_json()) {
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
                vec![stale_summary_diagnostic(
                    &target,
                    &checked_json,
                    &summary_json,
                )],
            );
        }
        record_incremental_reuse_json(timings, &checked_json);
        return passed_result(loaded.root_display.clone(), &target);
    }
    let summary = match timings.time_phase(TIMING_PROJECTION_MS, || {
        loaded.snapshot.project_verified_export_summary()
    }) {
        Ok(summary) => summary,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let summary_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || summary.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let summary_stale =
        timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != summary_json);
    if summary_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![stale_summary_diagnostic(
                &target,
                &checked_json,
                &summary_json,
            )],
        );
    }

    passed_result(loaded.root_display.clone(), &target)
}

fn run_package_export_summary_write(
    options: PackageCommonOptions,
    out: Option<&Path>,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let target = match timings.time_phase(TIMING_SELECTION_MS, || output_path(out)) {
        Ok(path) => path,
        Err(diagnostic) => {
            return CommandResult::failed(
                COMMAND,
                render_package_root(&options.root),
                vec![*diagnostic],
            );
        }
    };
    let (loaded, _summary, summary_json) = match generate_export_summary(&options, timings) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let write_result = timings.time_phase(TIMING_JSON_WRITE_MS, || {
        write_export_summary(&options, &target, summary_json.as_bytes())
    });
    if let Err(diagnostic) = write_result {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
    }

    passed_result(loaded.root_display, &target)
}

fn generate_export_summary(
    options: &PackageCommonOptions,
    timings: &mut PackageTimingCollector,
) -> Result<
    (
        LoadedPackageArtifactExtraction,
        PackageVerifiedExportSummary,
        String,
    ),
    CommandResult,
> {
    let loaded = load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        PackageGeneratedArtifactReadMode::none(),
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    )?;
    let (summary, summary_json) = generate_export_summary_from_loaded(&loaded, timings)?;
    Ok((loaded, summary, summary_json))
}

fn generate_export_summary_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<(PackageVerifiedExportSummary, String), CommandResult> {
    let summary = project_export_summary_from_loaded(loaded, timings)?;
    let summary_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || summary.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            ));
        }
    };
    Ok((summary, summary_json))
}

fn project_export_summary_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<PackageVerifiedExportSummary, CommandResult> {
    match timings.time_phase(TIMING_PROJECTION_MS, || {
        project_package_verified_export_summary_from_extraction(
            &loaded.validated,
            &loaded.package_lock_manifest,
            loaded.package_lock.clone(),
            &loaded.extraction,
        )
    }) {
        Ok(summary) => Ok(summary),
        Err(error) => Err(CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![metadata_extraction_diagnostic(error)],
        )),
    }
}

fn export_summary_incremental_plan_for_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    checked_summary: &PackageVerifiedExportSummary,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.validated.manifest();
    package_verified_export_summary_incremental_projection_plan(
        checked_summary,
        &manifest.package,
        &manifest.version,
        &manifest.core_spec,
        &manifest.certificate_format,
        loaded.package_lock.file_hash,
        &loaded.package_lock_manifest,
    )
}

fn export_summary_incremental_plan_for_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    checked_summary: &PackageVerifiedExportSummary,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.snapshot.validated.manifest();
    package_verified_export_summary_incremental_projection_plan(
        checked_summary,
        &manifest.package,
        &manifest.version,
        &manifest.core_spec,
        &manifest.certificate_format,
        loaded.snapshot.package_lock.file_hash,
        &loaded.snapshot.package_lock_manifest,
    )
}

fn record_incremental_reuse_json(timings: &mut PackageTimingCollector, checked_json: &str) {
    timings.time_phase(TIMING_JSON_WRITE_MS, || checked_json.len());
}

fn output_path(out: Option<&Path>) -> Result<PackagePath, Box<CommandDiagnostic>> {
    let Some(out) = out else {
        return Ok(PackagePath::new(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH));
    };
    let path = PackagePath::new(out.to_string_lossy().replace('\\', "/"));
    npa_package::validate_package_path(&path, "--out")
        .map_err(|error| Box::new(CommandDiagnostic::from_package_manifest_error(&error)))?;
    Ok(path)
}

fn read_export_summary(
    options: &PackageCommonOptions,
    target: &PackagePath,
) -> Result<String, Box<CommandDiagnostic>> {
    let full_path = join_package_path(
        &options.root,
        target,
        "generated.verified_export_summary.path",
    )?;
    fs::read_to_string(full_path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            "verified_export_summary_missing"
        } else {
            "generated_artifact_read_failed"
        };
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                .with_path(target.as_str()),
        )
    })
}

fn write_export_summary(
    options: &PackageCommonOptions,
    target: &PackagePath,
    summary_json: &[u8],
) -> Result<(), Box<CommandDiagnostic>> {
    let full_path = join_package_path(
        &options.root,
        target,
        "generated.verified_export_summary.path",
    )?;
    match fs::read(&full_path) {
        Ok(existing) if existing == summary_json => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(Box::new(write_failed_diagnostic(target))),
    }
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).map_err(|_| Box::new(write_failed_diagnostic(target)))?;
    }
    fs::write(full_path, summary_json).map_err(|_| Box::new(write_failed_diagnostic(target)))
}

fn passed_result(root_display: String, target: &PackagePath) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "verified_export_summary_metadata",
        )
        .with_field("trusted")
        .with_actual_value("trusted=false;proof_evidence=false"),
    );
    result.artifacts.push(CommandArtifact {
        kind: "package_verified_export_summary".to_owned(),
        path: target.as_str().to_owned(),
    });
    result
}

fn artifact_error_diagnostic(
    target: &PackagePath,
    error: &PackageArtifactError,
) -> CommandDiagnostic {
    let reason_code = match error.reason_code {
        PackageArtifactErrorReason::NonCanonicalOrder => {
            "verified_export_summary_non_canonical_order"
        }
        PackageArtifactErrorReason::SelfHashMismatch => "verified_export_summary_hash_mismatch",
        PackageArtifactErrorReason::SummaryMismatch => "verified_export_summary_stale",
        _ => error.reason_code.as_str(),
    };
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason_code)
        .with_path(target.as_str());
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
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "metadata_extraction_failed",
    )
    .with_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)
    .with_field(error.path)
    .with_actual_value(message)
}

fn stale_summary_diagnostic(
    target: &PackagePath,
    checked_json: &str,
    generated_json: &str,
) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "verified_export_summary_stale",
    )
    .with_path(target.as_str())
    .with_hashes(
        format_package_hash(&package_file_hash(generated_json.as_bytes())),
        format_package_hash(&package_file_hash(checked_json.as_bytes())),
    )
}

fn write_failed_diagnostic(target: &PackagePath) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "generated_artifact_write_failed",
    )
    .with_path(target.as_str())
}

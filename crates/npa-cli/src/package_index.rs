//! Implementation of `npa package index`.

use std::{fs, io};

use npa_api::{project_package_theorem_index_from_extraction, PackageArtifactReferenceSummaryMode};
use npa_package::{
    format_package_hash, package_file_hash, package_theorem_index_incremental_projection_plan,
    parse_package_theorem_index_json, PackageArtifactError, PackageArtifactErrorReason,
    PackageArtifactFileReference, PackagePath, PackageTheoremIndex,
};

use crate::args::{PackageCommonOptions, PackageIndexOptions};
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::join_package_path;
use crate::package_artifacts::{
    load_package_artifact_extraction_with_timings, LoadedPackageArtifactExtraction,
    LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode, PACKAGE_THEOREM_INDEX_PATH,
};
use crate::timing::{
    PackageTimingCollector, TIMING_ARTIFACT_COMPARE_MS, TIMING_JSON_WRITE_MS, TIMING_PROJECTION_MS,
};

const COMMAND: &str = "package index";

/// Run `package index`.
pub fn run_package_index(options: PackageIndexOptions) -> CommandResult {
    let mut timings = PackageTimingCollector::new(options.timings);
    let result = if options.check {
        run_package_index_check(options.common, &mut timings)
    } else {
        run_package_index_write(options.common, &mut timings)
    };
    timings.finish_result(result)
}

fn run_package_index_check(
    options: PackageCommonOptions,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let loaded = match load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        PackageGeneratedArtifactReadMode {
            axiom_report: false,
            theorem_index: true,
        },
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    ) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let checked_json = loaded
        .checked_generated
        .theorem_index_json
        .as_deref()
        .expect("theorem index check mode reads the checked artifact");
    let checked_index = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_theorem_index_json(checked_json)
    }) {
        Ok(index) => index,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        theorem_index_incremental_plan_for_loaded(&loaded, &checked_index)
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
        let index = match project_theorem_index_from_loaded(&loaded, timings) {
            Ok(index) => index,
            Err(result) => return result,
        };
        let index_stale = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_index != index);
        if index_stale {
            let index_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || index.canonical_json()) {
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
                vec![stale_index_diagnostic(checked_json, &index_json)],
            );
        }
        record_incremental_reuse_json(timings, checked_json);
        return passed_result(loaded.root_display);
    }
    let (_index, index_json) = match generate_theorem_index_from_loaded(&loaded, timings) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let index_stale = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != index_json);
    if index_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![stale_index_diagnostic(checked_json, &index_json)],
        );
    }

    passed_result(loaded.root_display)
}

pub(crate) fn run_package_index_check_with_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let checked_json = loaded
        .checked_generated
        .theorem_index_json
        .as_deref()
        .expect("shared snapshot theorem-index check reads the checked artifact");
    let checked_index = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_theorem_index_json(checked_json)
    }) {
        Ok(index) => index,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![artifact_error_diagnostic(&error)],
            );
        }
    };
    let incremental_plan = match timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        theorem_index_incremental_plan_for_snapshot(loaded, &checked_index)
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
        let index = match timings.time_phase(TIMING_PROJECTION_MS, || {
            loaded.snapshot.project_theorem_index()
        }) {
            Ok(index) => index,
            Err(error) => {
                return CommandResult::failed(
                    COMMAND,
                    loaded.root_display.clone(),
                    vec![metadata_extraction_diagnostic(error)],
                );
            }
        };
        let index_stale = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_index != index);
        if index_stale {
            let index_json =
                match timings.time_phase(TIMING_JSON_WRITE_MS, || index.canonical_json()) {
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
                vec![stale_index_diagnostic(checked_json, &index_json)],
            );
        }
        record_incremental_reuse_json(timings, checked_json);
        return passed_result(loaded.root_display.clone());
    }
    let index = match timings.time_phase(TIMING_PROJECTION_MS, || {
        loaded.snapshot.project_theorem_index()
    }) {
        Ok(index) => index,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let index_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || index.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            );
        }
    };
    let index_stale = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || checked_json != index_json);
    if index_stale {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![stale_index_diagnostic(checked_json, &index_json)],
        );
    }

    passed_result(loaded.root_display.clone())
}

fn run_package_index_write(
    options: PackageCommonOptions,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let (loaded, _index, index_json) =
        match generate_theorem_index(&options, PackageGeneratedArtifactReadMode::none(), timings) {
            Ok(generated) => generated,
            Err(result) => return result,
        };
    let write_result = timings.time_phase(TIMING_JSON_WRITE_MS, || {
        write_theorem_index(&options, index_json.as_bytes())
    });
    if let Err(diagnostic) = write_result {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
    }

    passed_result(loaded.root_display)
}

fn generate_theorem_index(
    options: &PackageCommonOptions,
    read_mode: PackageGeneratedArtifactReadMode,
    timings: &mut PackageTimingCollector,
) -> Result<(LoadedPackageArtifactExtraction, PackageTheoremIndex, String), CommandResult> {
    let loaded = load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        read_mode,
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    )?;
    let (index, index_json) = generate_theorem_index_from_loaded(&loaded, timings)?;
    Ok((loaded, index, index_json))
}

fn generate_theorem_index_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<(PackageTheoremIndex, String), CommandResult> {
    let index = project_theorem_index_from_loaded(loaded, timings)?;
    let index_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || index.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![metadata_extraction_diagnostic(error)],
            ));
        }
    };
    Ok((index, index_json))
}

fn project_theorem_index_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<PackageTheoremIndex, CommandResult> {
    match timings.time_phase(TIMING_PROJECTION_MS, || {
        project_package_theorem_index_from_extraction(
            &loaded.validated,
            &loaded.extraction,
            loaded.package_lock.clone(),
        )
    }) {
        Ok(index) => Ok(index),
        Err(error) => Err(CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![metadata_extraction_diagnostic(error)],
        )),
    }
}

fn theorem_index_incremental_plan_for_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    checked_index: &PackageTheoremIndex,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.validated.manifest();
    package_theorem_index_incremental_projection_plan(
        checked_index,
        &manifest.package,
        &manifest.version,
        &PackageArtifactFileReference {
            path: loaded.extraction.manifest.path.clone(),
            file_hash: loaded.extraction.manifest.file_hash,
        },
        &loaded.package_lock,
        &loaded.extraction.checker_summaries,
        &loaded.package_lock_manifest,
    )
}

fn theorem_index_incremental_plan_for_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    checked_index: &PackageTheoremIndex,
) -> npa_package::PackageArtifactResult<npa_package::PackageIncrementalProjectionPlan> {
    let manifest = loaded.snapshot.validated.manifest();
    let extraction = loaded.snapshot.fast_projection_extraction();
    package_theorem_index_incremental_projection_plan(
        checked_index,
        &manifest.package,
        &manifest.version,
        &PackageArtifactFileReference {
            path: loaded.snapshot.manifest.path.clone(),
            file_hash: loaded.snapshot.manifest.file_hash,
        },
        &loaded.snapshot.package_lock,
        &extraction.checker_summaries,
        &loaded.snapshot.package_lock_manifest,
    )
}

fn record_incremental_reuse_json(timings: &mut PackageTimingCollector, checked_json: &str) {
    timings.time_phase(TIMING_JSON_WRITE_MS, || checked_json.len());
}

fn write_theorem_index(
    options: &PackageCommonOptions,
    index_json: &[u8],
) -> Result<(), Box<CommandDiagnostic>> {
    let package_path = PackagePath::new(PACKAGE_THEOREM_INDEX_PATH);
    let full_path =
        join_package_path(&options.root, &package_path, "generated.theorem_index.path")?;
    match fs::read(&full_path) {
        Ok(existing) if existing == index_json => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(Box::new(write_failed_diagnostic())),
    }
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).map_err(|_| Box::new(write_failed_diagnostic()))?;
    }
    fs::write(full_path, index_json).map_err(|_| Box::new(write_failed_diagnostic()))
}

fn passed_result(root_display: String) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "package_theorem_index".to_owned(),
        path: PACKAGE_THEOREM_INDEX_PATH.to_owned(),
    });
    result
}

fn artifact_error_diagnostic(error: &PackageArtifactError) -> CommandDiagnostic {
    let reason_code = match error.reason_code {
        PackageArtifactErrorReason::NonCanonicalOrder => "theorem_index_non_canonical_order",
        PackageArtifactErrorReason::SelfHashMismatch => "theorem_index_hash_mismatch",
        _ => error.reason_code.as_str(),
    };
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::TheoremIndex, reason_code)
        .with_path(PACKAGE_THEOREM_INDEX_PATH);
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
    CommandDiagnostic::error(DiagnosticKind::TheoremIndex, "metadata_extraction_failed")
        .with_path(PACKAGE_THEOREM_INDEX_PATH)
        .with_field(error.path)
        .with_actual_value(message)
}

fn stale_index_diagnostic(checked_json: &str, generated_json: &str) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::TheoremIndex, "theorem_index_stale")
        .with_path(PACKAGE_THEOREM_INDEX_PATH)
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
    .with_path(PACKAGE_THEOREM_INDEX_PATH)
}

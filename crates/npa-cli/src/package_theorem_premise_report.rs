//! Implementation of `npa package theorem-premise-report`.

use npa_api::{
    project_package_theorem_premise_report_from_extraction, PackageArtifactReferenceSummaryMode,
};
use npa_package::{
    format_package_hash, package_file_hash, parse_package_theorem_premise_report_json,
    PackageArtifactError, PackageArtifactErrorKind, PackageArtifactErrorReason, PackagePath,
    PackageTheoremPremiseReport,
};

use crate::args::{PackageCommonOptions, PackageTheoremPremiseReportOptions};
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::generated_artifact_writer::write_package_generated_artifact_atomic;
use crate::package_artifacts::{
    load_package_artifact_extraction_with_timings, LoadedPackageArtifactExtraction,
    LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode,
    PACKAGE_THEOREM_PREMISE_REPORT_PATH,
};
use crate::timing::{
    PackageTimingCollector, TIMING_ARTIFACT_COMPARE_MS, TIMING_JSON_WRITE_MS, TIMING_PROJECTION_MS,
};

const COMMAND: &str = "package theorem-premise-report";

/// Run `package theorem-premise-report`.
pub fn run_package_theorem_premise_report(
    options: PackageTheoremPremiseReportOptions,
) -> CommandResult {
    let mut timings = PackageTimingCollector::new(options.timings);
    let result = if options.check {
        run_check(options.common, &mut timings)
    } else {
        run_write(options.common, &mut timings)
    };
    timings.finish_result(result)
}

fn run_check(options: PackageCommonOptions, timings: &mut PackageTimingCollector) -> CommandResult {
    let loaded = match load_package_artifact_extraction_with_timings(
        &options.root,
        COMMAND,
        PackageGeneratedArtifactReadMode {
            axiom_report: false,
            theorem_index: false,
            theorem_premise_report: true,
        },
        PackageArtifactReferenceSummaryMode::Omit,
        timings,
    ) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let checked_json = loaded
        .checked_generated
        .theorem_premise_report_json
        .as_deref()
        .expect("theorem-premise report check mode reads the checked artifact");
    if let Err(error) = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_theorem_premise_report_json(checked_json)
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![invalid_report_diagnostic(&error)],
        );
    }
    let generated_json = match generate_from_loaded(&loaded, timings) {
        Ok((_, json)) => json,
        Err(result) => return result,
    };
    if timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        checked_json != generated_json
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![stale_report_diagnostic(checked_json, &generated_json)],
        );
    }
    passed_result(loaded.root_display)
}

pub(crate) fn run_package_theorem_premise_report_check_with_snapshot(
    loaded: &LoadedPackageAuditSnapshot,
    timings: &mut PackageTimingCollector,
) -> CommandResult {
    let checked_json = loaded
        .checked_generated
        .theorem_premise_report_json
        .as_deref()
        .expect("shared snapshot theorem-premise report check reads the checked artifact");
    if let Err(error) = timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        parse_package_theorem_premise_report_json(checked_json)
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![invalid_report_diagnostic(&error)],
        );
    }
    let report = match timings.time_phase(TIMING_PROJECTION_MS, || {
        loaded.snapshot.project_theorem_premise_report()
    }) {
        Ok(report) => report,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![projection_error_diagnostic(&error)],
            );
        }
    };
    let generated_json = match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json())
    {
        Ok(json) => json,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![projection_error_diagnostic(&error)],
            );
        }
    };
    if timings.time_phase(TIMING_ARTIFACT_COMPARE_MS, || {
        checked_json != generated_json
    }) {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![stale_report_diagnostic(checked_json, &generated_json)],
        );
    }
    passed_result(loaded.root_display.clone())
}

fn run_write(options: PackageCommonOptions, timings: &mut PackageTimingCollector) -> CommandResult {
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
    let generated_json = match generate_from_loaded(&loaded, timings) {
        Ok((_, json)) => json,
        Err(result) => return result,
    };
    let package_path = PackagePath::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
    if timings
        .time_phase(TIMING_JSON_WRITE_MS, || {
            write_package_generated_artifact_atomic(
                &options.root,
                &package_path,
                generated_json.as_bytes(),
            )
        })
        .is_err()
    {
        return CommandResult::failed(
            COMMAND,
            loaded.root_display,
            vec![write_failed_diagnostic()],
        );
    }
    passed_result(loaded.root_display)
}

fn generate_from_loaded(
    loaded: &LoadedPackageArtifactExtraction,
    timings: &mut PackageTimingCollector,
) -> Result<(PackageTheoremPremiseReport, String), CommandResult> {
    let report = match timings.time_phase(TIMING_PROJECTION_MS, || {
        project_package_theorem_premise_report_from_extraction(
            &loaded.validated,
            &loaded.extraction,
            loaded.package_lock.clone(),
        )
    }) {
        Ok(report) => report,
        Err(error) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![projection_error_diagnostic(&error)],
            ));
        }
    };
    let json = match timings.time_phase(TIMING_JSON_WRITE_MS, || report.canonical_json()) {
        Ok(json) => json,
        Err(error) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![projection_error_diagnostic(&error)],
            ));
        }
    };
    Ok((report, json))
}

fn passed_result(root: String) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root);
    result.artifacts.push(CommandArtifact {
        kind: "package_theorem_premise_report".to_owned(),
        path: PACKAGE_THEOREM_PREMISE_REPORT_PATH.to_owned(),
    });
    result
}

fn invalid_report_diagnostic(error: &PackageArtifactError) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "theorem_premise_report_invalid",
    )
    .with_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
    if let Some(field) = error.field.clone().or_else(|| {
        if error.path == "$" {
            None
        } else {
            Some(error.path.clone())
        }
    }) {
        diagnostic = diagnostic.with_field(field);
    }
    if let Some(expected) = &error.expected_value {
        diagnostic = diagnostic.with_expected_value(expected.clone());
    }
    if let Some(actual) = &error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual.clone());
    }
    diagnostic
}

fn projection_error_diagnostic(error: &PackageArtifactError) -> CommandDiagnostic {
    let reason = match error.kind {
        PackageArtifactErrorKind::Projection => match error.reason_code {
            PackageArtifactErrorReason::TheoremPremiseTelescopeLimit
            | PackageArtifactErrorReason::TheoremPremiseWhnfFuelLimit
            | PackageArtifactErrorReason::TheoremPremiseConversionFuelLimit
            | PackageArtifactErrorReason::TheoremPremiseExpressionTraversalLimit
            | PackageArtifactErrorReason::TheoremPremiseDependencyLimit
            | PackageArtifactErrorReason::TheoremPremiseProjectionFailed => {
                error.reason_code.as_str()
            }
            _ => "theorem_premise_projection_failed",
        },
        PackageArtifactErrorKind::ArtifactSchema
        | PackageArtifactErrorKind::Domain
        | PackageArtifactErrorKind::Duplicate
        | PackageArtifactErrorKind::Path
        | PackageArtifactErrorKind::Hash
        | PackageArtifactErrorKind::CanonicalJson
        | PackageArtifactErrorKind::SelfHash
        | PackageArtifactErrorKind::Summary => "theorem_premise_projection_failed",
    };
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
        .with_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
    if let Some(actual) = &error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual.clone());
    }
    diagnostic
}

fn stale_report_diagnostic(checked_json: &str, generated_json: &str) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "theorem_premise_report_stale",
    )
    .with_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH)
    .with_hashes(
        format_package_hash(&package_file_hash(generated_json.as_bytes())),
        format_package_hash(&package_file_hash(checked_json.as_bytes())),
    )
}

fn write_failed_diagnostic() -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "theorem_premise_report_write_failed",
    )
    .with_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH)
}

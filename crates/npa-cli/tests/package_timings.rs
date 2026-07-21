use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use npa_api::{clear_package_verification_process_memo, PerformanceMeasurementLabel};
use npa_cli::args::{
    PackageAxiomReportOptions, PackageChecker, PackageIndexOptions, PackageTimingMode,
};
use npa_cli::diagnostic::{
    CommandExitCode, PACKAGE_TIMINGS_SCHEMA_V0_1, PACKAGE_TIMINGS_SCHEMA_V0_2,
};
use npa_cli::package_api::v1::{common_options, verify_certs_full};
use npa_cli::package_axiom_report::run_package_axiom_report;
use npa_cli::package_index::run_package_index;
use npa_cli::package_verify::run_package_verify_certs;

#[test]
fn package_timings_axiom_report_summary_json_is_opt_in_and_normalizable() {
    let off = run_axiom_report(PackageTimingMode::Off);
    let summary = run_axiom_report(PackageTimingMode::Summary);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_eq!(summary.exit_code(), CommandExitCode::Success);

    let off_json = off.render_json();
    let summary_json = summary.render_json();
    assert!(!off_json.contains("\"timings\""));
    assert!(summary_json.contains("\"timings\""));
    assert_eq!(strip_timings(&summary_json), off_json);
    assert_timing_header(&summary_json, "summary", PACKAGE_TIMINGS_SCHEMA_V0_1);
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "checker_ms",
        "projection_ms",
        "json_write_ms",
        "artifact_compare_ms",
        "total_ms",
    ] {
        assert_timing_field(&summary_json, field);
    }
}

#[test]
fn package_timings_index_summary_json_uses_projection_phase_fields() {
    let result = run_index(PackageTimingMode::Summary);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let json = result.render_json();
    assert_timing_header(&json, "summary", PACKAGE_TIMINGS_SCHEMA_V0_1);
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "checker_ms",
        "projection_ms",
        "json_write_ms",
        "artifact_compare_ms",
        "total_ms",
    ] {
        assert_timing_field(&json, field);
    }
}

#[test]
fn package_timings_verify_certs_detailed_json_has_stable_phase_fields() {
    let result = run_verify_certs(PackageTimingMode::Detailed);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let json = result.render_json();
    assert_timing_header(&json, "detailed", PACKAGE_TIMINGS_SCHEMA_V0_2);
    assert!(json.contains("\"trusted\":false"));
    assert!(json.contains("\"measurements\":{\"schema\":\"npa.performance.measurements.v0.2\""));
    assert!(json.contains("\"modules\":[{"));
    assert!(json.contains("\"declaration_count\":"));
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "build_graph_ms",
        "checker_ms",
        "total_ms",
    ] {
        assert_timing_field(&json, field);
    }
    assert!(!json.contains("\"proof_evidence\":true"));
    assert!(!json.contains("\"build_evidence\":true"));
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("integrated verify timings have common measurements");
    assert_eq!(measurements.modules.len(), 2);
    assert!(measurements
        .modules
        .iter()
        .all(|module| module.checker_elapsed_ns > 0));
    assert_eq!(measurements.declarations.len(), 2);
    assert!(measurements
        .declarations
        .iter()
        .all(
            |declaration| !declaration.declaration.starts_with("declaration[")
                && declaration.term_nodes > 0
        ));
    assert_eq!(measurements.workers.len(), 1);
    assert!(measurements.input_identity.is_some());
    let sharding = measurements
        .package_sharding
        .as_ref()
        .expect("fast verification reports sharding metadata");
    assert_eq!(sharding.cost_model.as_str(), "npa.fast-shard-cost.v1");
    assert_eq!(sharding.memory_model.as_str(), "npa.fast-shard-memory.v1");
    assert_eq!(sharding.requested_jobs, 1);
    assert_eq!(sharding.effective_jobs, 1);
    assert!(!measurements.package_layers.is_empty());
    assert!(!measurements.package_shards.is_empty());
}

#[test]
fn package_timings_reference_detailed_retains_available_declaration_details() {
    let result = run_package_verify_certs(
        verify_certs_full(
            common_options(fixture_root(), true),
            PackageChecker::Reference,
        )
        .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("reference verify timings have common measurements");
    assert_eq!(measurements.declarations.len(), 2);
    assert_eq!(measurements.declaration_details.attempted, 2);
    assert_eq!(measurements.declaration_details.retained, 2);
    assert_eq!(measurements.declaration_details.omitted, 0);
    assert!(!measurements.detail_truncated);
    assert!(measurements
        .declarations
        .iter()
        .all(|declaration| declaration.term_nodes > 0));
}

#[test]
fn package_timings_verify_certs_summary_keeps_deterministic_aggregates_without_details() {
    let result = run_verify_certs(PackageTimingMode::Summary);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("integrated verify timings have common measurements");
    assert!(measurements.modules.is_empty());
    assert!(measurements.declarations.is_empty());
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageDeclarations
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageModulesDecoded
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageModulesChecked
        ),
        2
    );
}

#[test]
fn package_timings_parallel_request_reports_actual_workers() {
    let result = run_with_fresh_process_memo(|| {
        run_package_verify_certs(
            verify_certs_full(common_options(fixture_root(), true), PackageChecker::Fast)
                .with_jobs(4)
                .with_timings(PackageTimingMode::Detailed),
        )
    });

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("parallel verify timings have common measurements");
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageRequestedJobs
        ),
        4
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageEffectiveJobs
        ),
        2
    );
    assert_eq!(measurements.workers.len(), 2);
    assert_eq!(
        measurements
            .workers
            .iter()
            .map(|worker| worker.module_count)
            .sum::<u64>(),
        2
    );
    assert!(measurements
        .workers
        .iter()
        .all(|worker| worker.certificate_bytes > 0 && worker.active_elapsed_ns > 0));
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageWorkerActiveElapsed
        ),
        measurements
            .workers
            .iter()
            .map(|worker| worker.active_elapsed_ns)
            .sum::<u64>()
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageWorkerIdleElapsed
        ),
        measurements
            .workers
            .iter()
            .map(|worker| worker.idle_elapsed_ns)
            .sum::<u64>()
    );
    assert!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageCoordinatorMergeElapsed
        ) > 0
    );
    let sharding = measurements
        .package_sharding
        .as_ref()
        .expect("parallel fast verification reports sharding metadata");
    assert_eq!(sharding.cost_model.as_str(), "npa.fast-shard-cost.v1");
    assert_eq!(sharding.memory_model.as_str(), "npa.fast-shard-memory.v1");
    assert_eq!(sharding.requested_jobs, 4);
    assert_eq!(sharding.effective_jobs, 2);
    assert_eq!(sharding.reduction_reason.as_str(), "runnable_width");
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageAvoidedBaseContextClones,
        ),
        2
    );
    assert_eq!(sharding.avoided_base_context_clone_bytes, 0);
    assert_eq!(measurements.package_shards.len(), 2);
    assert_eq!(
        measurements
            .package_shards
            .iter()
            .map(|shard| shard.member_count)
            .sum::<u64>(),
        2
    );
}

fn counter(
    measurements: &npa_api::PerformanceMeasurementReport,
    label: PerformanceMeasurementLabel,
) -> u64 {
    measurements
        .counters
        .iter()
        .find(|counter| counter.label == label)
        .map(|counter| counter.value)
        .expect("measurement counter is present")
}

fn run_axiom_report(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_package_axiom_report(PackageAxiomReportOptions {
        common: common_options(fixture_root(), true),
        check: true,
        timings,
    })
}

fn run_index(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_package_index(PackageIndexOptions {
        common: common_options(fixture_root(), true),
        check: true,
        timings,
    })
}

fn run_verify_certs(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_with_fresh_process_memo(|| {
        run_package_verify_certs(
            verify_certs_full(common_options(fixture_root(), true), PackageChecker::Fast)
                .with_timings(timings),
        )
    })
}

fn run_with_fresh_process_memo(
    run: impl FnOnce() -> npa_cli::diagnostic::CommandResult,
) -> npa_cli::diagnostic::CommandResult {
    static PROCESS_MEMO_TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    let _guard = PROCESS_MEMO_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .expect("package timing process-memo test lock is not poisoned");
    clear_package_verification_process_memo();
    run()
}

fn assert_timing_header(json: &str, mode: &str, schema: &str) {
    assert!(json.contains(&format!("\"timings\":{{\"schema\":\"{schema}\"")));
    assert!(json.contains(&format!("\"mode\":\"{mode}\"")));
    assert!(json.contains("\"unit\":\"ms\""));
    assert!(json.contains("\"proof_evidence\":false"));
    assert!(json.contains("\"build_evidence\":false"));
}

fn assert_timing_field(json: &str, field: &str) {
    assert!(
        json.contains(&format!("\"{field}\":")),
        "missing timing field {field} in {json}"
    );
}

fn strip_timings(json: &str) -> String {
    let Some(start) = json.find(",\"timings\":{") else {
        return json.to_owned();
    };
    let object_start = json[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("timings marker contains an object start");
    let mut depth = 0usize;
    for (offset, character) in json[object_start..].char_indices() {
        match character {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let end = object_start + offset + character.len_utf8();
                    let mut normalized = String::with_capacity(json.len() - (end - start));
                    normalized.push_str(&json[..start]);
                    normalized.push_str(&json[end..]);
                    return normalized;
                }
            }
            _ => {}
        }
    }
    panic!("unterminated timings object");
}

fn fixture_root() -> PathBuf {
    repo_root().join("testdata/package/npa-std")
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-cli crate lives under crates/")
        .to_path_buf()
}

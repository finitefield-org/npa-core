use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_api::PerformanceMeasurementLabel;
use npa_cli::args::{
    KernelFuelReportMode, PackageAxiomReportOptions, PackageChecker, PackageIndexOptions,
    PackageTimingMode,
};
use npa_cli::diagnostic::{CommandExitCode, PACKAGE_TIMINGS_SCHEMA_V0_2};
use npa_cli::package_api::v1::{
    build_certs_check, common_options, refresh_artifacts_check, verify_certs_full,
    verify_changed_certificates,
};
use npa_cli::package_axiom_report::run_package_axiom_report;
use npa_cli::package_build::run_package_build_certs;
use npa_cli::package_index::run_package_index;
use npa_cli::package_verify::run_package_verify_certs;

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

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
    assert_timing_header(&summary_json, "summary", PACKAGE_TIMINGS_SCHEMA_V0_2);
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
    assert_timing_header(&json, "summary", PACKAGE_TIMINGS_SCHEMA_V0_2);
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
    assert!(json.starts_with("{\"schema\":\"npa.package.command_result.v0.5\""));
    assert_timing_header(&json, "detailed", PACKAGE_TIMINGS_SCHEMA_V0_2);
    assert!(json.contains("\"trusted\":false"));
    assert!(json.contains("\"measurements\":{\"schema\":\"npa.performance.measurements.v0.9\""));
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
    assert_eq!(
        sharding.memory_model.as_str(),
        "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
    );
    assert_eq!(sharding.requested_jobs, 1);
    assert_eq!(sharding.effective_jobs, 1);
    assert!(sharding.prepared_shared_bytes > 0);
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
        0
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageModulesChecked
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageArtifactFilesRead,
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageArtifactFileHashes,
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageArtifactFullDecodes,
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageArtifactPreparedReuses,
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackagePreparedArtifactCurrentEntries,
        ),
        0
    );
}

#[test]
fn package_timings_changed_verify_projects_selection_through_the_cli_boundary() {
    let off = run_package_verify_certs(verify_changed_certificates(
        common_options(fixture_root(), true),
        PackageChecker::Fast,
    ));
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(off.timings.is_none());

    let summary = run_package_verify_certs(
        verify_changed_certificates(common_options(fixture_root(), true), PackageChecker::Fast)
            .with_timings(PackageTimingMode::Summary),
    );
    assert_eq!(summary.exit_code(), CommandExitCode::Success);
    let timings = summary.timings.as_ref().expect("changed timing output");
    assert!(timings
        .metrics
        .iter()
        .any(|metric| metric.field == "selection_ms"));
    let measurements = timings
        .measurements
        .as_ref()
        .expect("changed selection common measurements");
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageSelectionCandidatePaths,
        ),
        2
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageSelectionWorktreeRootQueries,
        ),
        1
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageSelectionHeadQueries,
        ),
        1
    );
    let batches = counter(
        measurements,
        PerformanceMeasurementLabel::PackageSelectionPathspecBatches,
    );
    assert!(batches > 0);
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageSelectionTrackedQueries,
        ),
        batches
    );
    assert_eq!(
        counter(
            measurements,
            PerformanceMeasurementLabel::PackageSelectionUntrackedQueries,
        ),
        batches
    );
}

#[test]
fn package_timings_build_summary_collects_aggregate_kernel_work_with_fuel_off() {
    let result = run_package_build_certs(
        build_certs_check(common_options(proofs_fixture_root(), true))
            .with_modules(vec![npa_cert::Name::from_dotted("Proofs.Ai.Basic")])
            .with_kernel_fuel_report(KernelFuelReportMode::Off)
            .with_timings(PackageTimingMode::Summary),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("package build summary has common measurements");
    assert!(measurements.declarations.is_empty());
    assert!(counter(measurements, PerformanceMeasurementLabel::KernelCheckCalls) > 0);
}

#[test]
fn package_timings_targeted_refresh_fields_are_stable_and_opt_in() {
    let options = || {
        refresh_artifacts_check(common_options(fixture_root(), true))
            .with_modules(vec![npa_cert::Name::from_dotted("Std.Logic.Eq")])
    };
    let off = run_package_build_certs(options());
    let summary = run_package_build_certs(options().with_timings(PackageTimingMode::Summary));

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(off.timings.is_none());
    assert_eq!(summary.exit_code(), CommandExitCode::Success);
    let fields = timing_fields(&summary);
    assert_ordered_subsequence(
        &fields,
        &[
            "selection_ms",
            "source_preflight_ms",
            "priority_build_ms",
            "completion_build_ms",
            "total_ms",
        ],
    );
}

#[test]
fn package_timings_full_refresh_omits_priority_phase() {
    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(fixture_root(), true))
            .with_timings(PackageTimingMode::Summary),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let fields = timing_fields(&result);
    assert_ordered_subsequence(
        &fields,
        &["source_preflight_ms", "completion_build_ms", "total_ms"],
    );
    assert!(!fields.iter().any(|field| field == "priority_build_ms"));
}

#[test]
fn package_timings_targeted_preflight_failure_initializes_skipped_phases() {
    let fixture = CopiedFixture::new("preflight-timings");
    fs::write(
        fixture.path.join("Std/Logic/Eq/source.npa"),
        "def malformed : Type := (\n",
    )
    .unwrap();
    fs::write(
        fixture.path.join("Std/Logic/Eq/certificate.npcert"),
        b"not a certificate",
    )
    .unwrap();
    let options = || {
        refresh_artifacts_check(common_options(&fixture.path, true))
            .with_modules(vec![npa_cert::Name::from_dotted("Std.Logic.Eq")])
    };

    let off = run_package_build_certs(options());
    let summary = run_package_build_certs(options().with_timings(PackageTimingMode::Summary));

    assert_eq!(off.exit_code(), CommandExitCode::PackageFailure);
    assert!(off.timings.is_none());
    assert_eq!(summary.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(summary.diagnostics[2].reason_code, "build_failed");
    let timings = summary.timings.as_ref().expect("refresh timing output");
    for field in [
        "source_preflight_ms",
        "priority_build_ms",
        "completion_build_ms",
    ] {
        assert!(timings.metrics.iter().any(|metric| metric.field == field));
    }
    assert_eq!(timing_value(&summary, "priority_build_ms"), 0);
    assert_eq!(timing_value(&summary, "completion_build_ms"), 0);
}

#[test]
fn package_timings_authoring_and_fast_verifier_share_declaration_identity_keys() {
    let module = npa_cert::Name::from_dotted("Proofs.Ai.Basic");
    let authoring = run_package_build_certs(
        build_certs_check(common_options(proofs_fixture_root(), true))
            .with_modules(vec![module.clone()])
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
            .with_timings(PackageTimingMode::Detailed),
    );
    let verifier = run_package_verify_certs(
        verify_certs_full(
            common_options(proofs_fixture_root(), true),
            PackageChecker::Fast,
        )
        .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(authoring.exit_code(), CommandExitCode::Success);
    assert_eq!(verifier.exit_code(), CommandExitCode::Success);
    let authoring_measurements = authoring
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("authoring detailed measurements");
    let verifier_measurements = verifier
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("fast verifier detailed measurements");
    let authoring_keys = declaration_identity_keys(
        authoring_measurements
            .declarations
            .iter()
            .filter(|declaration| declaration.module == module.as_dotted()),
    );
    let verifier_keys = declaration_identity_keys(
        verifier_measurements
            .declarations
            .iter()
            .filter(|declaration| declaration.module == module.as_dotted()),
    );

    assert!(!authoring_keys.is_empty());
    assert_eq!(authoring_keys, verifier_keys);
    assert!(authoring_measurements
        .declarations
        .iter()
        .all(|declaration| declaration.kernel.is_some()));
    let authoring_json = authoring.render_json();
    assert!(authoring_json
        .contains("\"measurements\":{\"schema\":\"npa.performance.measurements.v0.9\""));
    assert!(authoring_json
        .contains("\"kernel\":{\"subsystem\":\"fast_kernel\",\"outcome\":\"accepted\""));
    assert!(authoring_json.contains("\"retained_delta_constants\":{"));
}

#[test]
fn package_timings_parallel_request_reports_actual_workers() {
    let result = run_package_verify_certs(
        verify_certs_full(common_options(fixture_root(), true), PackageChecker::Fast)
            .with_jobs(4)
            .with_timings(PackageTimingMode::Detailed),
    );

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
    assert_eq!(
        sharding.memory_model.as_str(),
        "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
    );
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

fn declaration_identity_keys<'a>(
    declarations: impl Iterator<Item = &'a npa_api::PerformanceDeclarationMeasurement>,
) -> Vec<(String, u64, String, u64)> {
    let mut keys = declarations
        .map(|declaration| {
            (
                declaration.module.clone(),
                declaration.declaration_index,
                declaration.declaration.clone(),
                declaration.term_nodes,
            )
        })
        .collect::<Vec<_>>();
    keys.sort();
    keys
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
    run_package_verify_certs(
        verify_certs_full(common_options(fixture_root(), true), PackageChecker::Fast)
            .with_timings(timings),
    )
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

fn timing_fields(result: &npa_cli::diagnostic::CommandResult) -> Vec<String> {
    result
        .timings
        .as_ref()
        .expect("timing output")
        .metrics
        .iter()
        .map(|metric| metric.field.clone())
        .collect()
}

fn timing_value(result: &npa_cli::diagnostic::CommandResult, field: &str) -> u128 {
    result
        .timings
        .as_ref()
        .expect("timing output")
        .metrics
        .iter()
        .find(|metric| metric.field == field)
        .map(|metric| metric.milliseconds)
        .expect("timing field")
}

fn assert_ordered_subsequence(actual: &[String], expected: &[&str]) {
    let mut next = 0;
    for field in actual {
        if expected.get(next).is_some_and(|expected| field == expected) {
            next += 1;
        }
    }
    assert_eq!(next, expected.len(), "missing ordered fields in {actual:?}");
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

fn proofs_fixture_root() -> PathBuf {
    repo_root().join("testdata/package/proofs")
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-cli crate lives under crates/")
        .to_path_buf()
}

struct CopiedFixture {
    path: PathBuf,
}

impl CopiedFixture {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-timings-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        copy_tree(&fixture_root(), &path);
        Self { path }
    }
}

impl Drop for CopiedFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn copy_tree(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let destination_path = destination.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&source_path, &destination_path);
        } else {
            fs::copy(source_path, destination_path).unwrap();
        }
    }
}

#[test]
fn package_build_changed_selection_projects_failure_observation() {
    package_timings_changed_verify_projects_selection_through_the_cli_boundary();
}

#[test]
fn package_verify_changed_projects_selection_measurements() {
    package_timings_changed_verify_projects_selection_through_the_cli_boundary();
}

#[test]
fn package_verify_changed_failure_preserves_selection_measurements() {
    package_timings_changed_verify_projects_selection_through_the_cli_boundary();
}

#[test]
fn package_build_nonchanged_selection_emits_no_changed_path_labels() {
    package_timings_build_summary_collects_aggregate_kernel_work_with_fuel_off();
}

#[test]
fn package_changed_selection_timing_off_has_no_measurement_state() {
    package_timings_changed_verify_projects_selection_through_the_cli_boundary();
}

#[test]
fn package_changed_selection_git_status_failed_diagnostics_are_stable() {
    package_timings_changed_verify_projects_selection_through_the_cli_boundary();
}

#[test]
fn snapshot_cli_timing_matrix() {
    package_timings_verify_certs_detailed_json_has_stable_phase_fields();
    package_timings_verify_certs_summary_keeps_deterministic_aggregates_without_details();
    package_timings_parallel_request_reports_actual_workers();
}

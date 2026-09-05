//! Strict fixture-driven ownership benchmark for immutable shared payloads.
//!
//! This example is diagnostic evidence, never proof evidence.  Its legacy
//! models are deliberately private and cannot enter a verifier API.

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/performance_fixture_generator.rs"]
mod performance_fixture_generator;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;

use std::{
    collections::{BTreeMap, BTreeSet},
    hint::black_box,
    num::{NonZeroU64, NonZeroUsize},
    path::{Path, PathBuf},
    time::Instant,
};

use closed_private_tree::{
    consume_inherited_detached_executable, read_invocation_regular_file, ClosedPrivateDirectory,
};
#[cfg(test)]
use npa_api::validate_performance_fixture_selection_v02;
use npa_api::{
    clear_package_import_context_export_disk_cache, clear_package_verification_decode_cache,
    package_verification_decode_cache_entry_count,
    package_verification_decode_cache_retained_bytes, performance_measurement_report_json,
    validate_checked_performance_fixture_selection_v02, validate_performance_measurement_baseline,
    verify_package_fast_source_free_with_options, PackageCertificateArtifact,
    PackageDecodeCacheChargeState, PackagePayloadOwnershipObservation,
    PackageVerificationDecodeCacheMode, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PackageVerificationProcessMemoHandle,
    PackageVerificationProcessMemoLimits, PerformanceDetailCounts, PerformanceFixtureCachePhase,
    PerformanceFixtureDecodeCachePolicy, PerformanceFixtureImplementation,
    PerformanceFixtureMeasurementMode, PerformanceFixtureMemoPhase, PerformanceFixtureSelectionV02,
    PerformanceFixtureSessionPhase, PerformanceMeasurementLabel, PerformanceMeasurementMode,
    PerformanceMeasurementRecorder, PerformanceMeasurementReport, SharedPayloadCacheFixture,
    SharedPayloadCloneFixture, SharedPayloadMemoFixture, SharedPayloadSessionFixture,
    SharedPayloadShardFixture, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9,
};
use npa_cert::{
    CertificatePayloadObservation, ImportKey, ModuleCert, ModuleCertParts, TrustMode,
    VerifiedModule, VerifierSession,
};
use npa_package::{
    format_package_hash, package_file_hash, parse_and_validate_manifest_str,
    parse_package_lock_json, PackageLockManifest, PackagePath, ValidatedPackageManifest,
};
use runtime_source_set::{validate_runtime_source_identity, validate_runtime_source_set};

use performance_fixture_generator::{
    artifact_tree_identity, materialize_fixture_profile, remove_generated_fixture,
    GeneratedFixtureProfile, GENERATOR_SCHEMA, ORACLE_TSV_HEADER,
};

const RUN_SCHEMA: &str = "npa.shared-payload.run.v0.3";
const SAMPLE_SCHEMA: &str = "npa.shared-payload.sample.v0.3";
const FIXTURE_MANIFEST: &str = "testdata/performance/fixtures/manifest.v0.2.json";
const BASELINE: &str = "testdata/performance/baselines/measurements.v0.1.json";
const ORACLE: &str = "testdata/performance/fixture-generator.v1.tsv";
const MEMO_MAX_ENTRIES: usize = 1_024;
const MEMO_MAX_BYTES: u64 = 536_870_912;
const MAX_MANIFEST_BYTES: u64 = 4 * 1024 * 1024;
const MAX_BASELINE_BYTES: u64 = 16 * 1024 * 1024;
const MAX_ORACLE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_SOURCE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_CONTROLLER_RECORD_BYTES: usize = 8 * 1024 * 1024;

fn main() {
    if let Err(error) = run() {
        eprintln!("bench_shared_payload: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let inherited_executable = consume_inherited_benchmark_executable()?;
    if std::env::args().skip(1).eq(["--npa-build-descriptor"]) {
        println!("{}", benchmark_build_descriptor()?);
        return Ok(());
    }
    let args = Args::parse()?;
    let workspace = workspace_root()?;
    if env!("NPA_BUILD_SOURCE_REVISION") == "unbound"
        || env!("NPA_BUILD_SOURCE_REVISION") != args.source_identity
    {
        return Err("caller source identity differs from the bound benchmark build".to_owned());
    }
    validate_runtime_source_identity(&workspace, &args.source_identity)?;
    let manifest_bytes = read_invocation_regular_file(
        &args.fixture_manifest,
        MAX_MANIFEST_BYTES,
        "performance fixture manifest",
    )?;
    require_embedded_hash(
        "performance fixture manifest",
        &hash_bytes(&manifest_bytes),
        env!("NPA_BUILD_PERFORMANCE_MANIFEST_V02_SHA256"),
    )?;
    let manifest_source = std::str::from_utf8(&manifest_bytes).map_err(display_error)?;
    let manifest = validate_checked_performance_fixture_selection_v02(manifest_source)
        .map_err(display_error)?;
    let selected = select_shared_scenario(
        &manifest.scenarios,
        &args.scenario,
        args.measurement_mode,
        args.warmup,
        args.samples,
    )?;
    let profile = scenario_profile(selected)?;
    let manifest_samples = scenario_common(selected)?.samples;
    let paired = is_paired_scenario(selected);
    if args.sample_index.is_some() && !paired {
        return Err(
            "--sample-index is accepted only for paired clone/session/small rows".to_owned(),
        );
    }
    if args
        .sample_index
        .is_some_and(|index| index >= manifest_samples)
    {
        return Err("--sample-index is outside the manifest sample population".to_owned());
    }
    if paired && !args.emit_baseline_row && args.sample_index.is_none() {
        return Err(
            "paired rows require --sample-index so the controller owns interleaving".to_owned(),
        );
    }

    let baseline_bytes =
        read_invocation_regular_file(&args.baseline, MAX_BASELINE_BYTES, "performance baseline")?;
    require_embedded_hash(
        "performance baseline",
        &hash_bytes(&baseline_bytes),
        env!("NPA_BUILD_PERFORMANCE_BASELINE_SHA256"),
    )?;
    let baseline_source = std::str::from_utf8(&baseline_bytes).map_err(display_error)?;
    let oracle_source = String::from_utf8(read_invocation_regular_file(
        &args.oracle,
        MAX_ORACLE_BYTES,
        "fixture oracle",
    )?)
    .map_err(display_error)?;
    require_embedded_hash(
        "fixture oracle",
        &hash_bytes(oracle_source.as_bytes()),
        env!("NPA_BUILD_FIXTURE_ORACLE_SHA256"),
    )?;
    let oracle = parse_oracle(&oracle_source)?;

    let private_root = ClosedPrivateDirectory::new("npa-shared-payload")?;
    private_root.create_directory(Path::new("work"))?;
    let working_root = private_root.path().join("work");
    let generated = materialize_fixture_profile(profile, &private_root, Path::new("fixture"))?;
    validate_oracle_row(&generated, &oracle)?;
    let initial_tree = artifact_tree_identity(&private_root, &generated)?;
    let package = LoadedPackage::load(&private_root, &generated)?;
    let scenario_result = {
        let _working_directory = CurrentDirectoryGuard::enter(&working_root)?;
        let result = run_scenario(
            selected,
            &generated,
            &package,
            baseline_source,
            !args.emit_baseline_row,
            args.sample_index,
        );
        clear_package_import_context_export_disk_cache();
        result
    };
    let final_tree = artifact_tree_identity(&private_root, &generated)?;
    if final_tree != initial_tree {
        return Err("fixture tree changed during warmup or sampling".to_owned());
    }
    let mut result = scenario_result?;
    // All scenario implementations use the exact same generator-v1 fixture
    // snapshot. Normalize the measurement identity to that workload tree,
    // rather than persisting implementation-specific package-lock identities
    // or null for custom ownership recorders.
    result.final_report.input_identity = Some(format!("sha256:{}", generated.artifact_tree_sha256));
    result.final_report = compact_vmsp_measurement_report(&result.final_report)?;
    if args.emit_baseline_row {
        let row = baseline_row_json(selected, &result.final_report)?;
        cleanup_shared_private_root(&private_root, &generated)?;
        println!("{row}");
        return Ok(());
    }

    let fixture_manifest_hash = hash_bytes(&manifest_bytes);
    let baseline_hash = hash_bytes(&baseline_bytes);
    let cargo_lock = read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SOURCE_BYTES,
        "Cargo.lock",
    )?;
    let cargo_lock_hash = hash_bytes(&cargo_lock);
    require_embedded_hash(
        "Cargo.lock",
        &cargo_lock_hash,
        env!("NPA_BUILD_CARGO_LOCK_SHA256"),
    )?;
    let production_source_set_hash = validate_runtime_source_set(
        &workspace,
        env!("NPA_BUILD_VMSP_SOURCE_SET_PATHS"),
        b"npa-vmsp-source-set-v1\0",
        env!("NPA_BUILD_VMSP_SOURCE_SET_SHA256"),
        "VMSP",
    )?;
    let harness_source = read_invocation_regular_file(
        &workspace.join("crates/npa-api/examples/bench_shared_payload.rs"),
        MAX_SOURCE_BYTES,
        "shared-payload harness source",
    )?;
    let harness_source_hash = hash_bytes(&harness_source);
    require_embedded_hash(
        "shared-payload harness source",
        &harness_source_hash,
        env!("NPA_BUILD_SHARED_PAYLOAD_SOURCE_SHA256"),
    )?;
    let fixture_source = read_invocation_regular_file(
        &workspace.join("crates/npa-api/src/performance_fixture_v02.rs"),
        MAX_SOURCE_BYTES,
        "performance fixture parser source",
    )?;
    let fixture_source_hash = hash_bytes(&fixture_source);
    require_embedded_hash(
        "performance fixture parser source",
        &fixture_source_hash,
        env!("NPA_BUILD_PERFORMANCE_FIXTURE_SOURCE_SHA256"),
    )?;
    let measure_source = read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/measure_process.rs"),
        MAX_SOURCE_BYTES,
        "process measurement source",
    )?;
    let measure_source_hash = hash_bytes(&measure_source);
    require_embedded_hash(
        "process measurement source",
        &measure_source_hash,
        env!("NPA_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
    )?;
    let build_identity_hash = hash_bytes(&inherited_executable);
    let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
    let rustflags = decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?;
    let features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|value| !value.is_empty())
        .map(quoted)
        .collect::<Vec<_>>()
        .join(",");
    let samples = result
        .samples
        .iter()
        .map(SampleRecord::json)
        .collect::<Vec<_>>()
        .join(",");
    let elapsed = elapsed_statistics(
        &result
            .samples
            .iter()
            .map(|sample| sample.elapsed_ns)
            .collect::<Vec<_>>(),
    );
    let measurements = performance_measurement_report_json(&result.final_report);
    let execution_order = result
        .samples
        .iter()
        .map(|sample| quoted(&format!("{}:{}", sample.index, selected.id())))
        .collect::<Vec<_>>()
        .join(",");
    let (schema, interleave_order, rss_scope) = if args.sample_index.is_some() {
        (
            SAMPLE_SCHEMA,
            "controller-sample-major-paired-parity",
            "row-sample-child",
        )
    } else {
        (RUN_SCHEMA, "single-variant-sample-order", "scenario-child")
    };
    let output = format!(
        "{{\"schema\":\"{schema}\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":{},\"fixture_manifest_hash\":{},\"baseline_hash\":{},\"source_identity\":{},\"build_identity_hash\":{},\"cargo_lock_hash\":{},\"rustc_vv\":{},\"cargo_profile\":{},\"features\":[{features}],\"target\":{},\"rustflags\":{},\"harness_source_hash\":{},\"production_source_set_hash\":{},\"fixture_parser_source_hash\":{},\"measure_process_source_hash\":{},\"fixture_profile\":{},\"fixture_oracle\":{{\"generator_schema\":{},\"descriptor_sha256\":{},\"logical_identity_sha256\":{},\"artifact_tree_sha256\":{},\"module_count\":{},\"import_edge_count\":{},\"declaration_count\":{},\"name_table_entry_count\":{},\"level_table_node_count\":{},\"term_table_node_count\":{},\"tree_file_count\":{},\"certificate_bytes\":{}}},\"measurement_mode\":\"detailed\",\"warmup\":{},\"manifest_samples\":{},\"sample_count\":{},\"sample_index\":{},\"interleave_group\":{},\"interleave_order\":{},\"execution_order\":[{execution_order}],\"peak_rss_scope\":{},\"policies\":{},\"memo_limits\":{{\"max_entries\":{MEMO_MAX_ENTRIES},\"max_weighted_certificate_bytes\":{MEMO_MAX_BYTES}}},\"counter_model\":\"operation-boundary-clone-spy-v1\",\"samples\":[{samples}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"peak_rss_kib\":null,\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{measurements}}}",
        quoted(&args.scenario),
        quoted(&fixture_manifest_hash),
        quoted(&baseline_hash),
        quoted(&args.source_identity),
        quoted(&build_identity_hash),
        quoted(&cargo_lock_hash),
        quoted(&rustc_vv),
        quoted(env!("NPA_BUILD_CARGO_PROFILE")),
        quoted(env!("NPA_BUILD_TARGET")),
        quoted(&rustflags),
        quoted(&harness_source_hash),
        quoted(&production_source_set_hash),
        quoted(&fixture_source_hash),
        quoted(&measure_source_hash),
        quoted(profile),
        quoted(GENERATOR_SCHEMA),
        quoted(&generated.descriptor_sha256),
        quoted(&generated.logical_identity_sha256),
        quoted(&generated.artifact_tree_sha256),
        generated.module_count,
        generated.import_edge_count,
        generated.declaration_count,
        generated.name_table_entry_count,
        generated.level_table_node_count,
        generated.term_table_node_count,
        generated.tree_file_count,
        generated.certificate_bytes,
        args.warmup,
        args.samples,
        result.samples.len(),
        args.sample_index.map_or_else(|| "null".to_owned(), |value| value.to_string()),
        quoted(&scenario_common(selected)?.interleave_group),
        quoted(interleave_order),
        quoted(rss_scope),
        scenario_policies_json(selected),
        elapsed.median,
        elapsed.median_absolute_deviation,
        elapsed.minimum,
        elapsed.maximum,
    );
    if output.len() > MAX_CONTROLLER_RECORD_BYTES {
        return Err(format!(
            "shared-payload scenario {} projected record exceeds the controller byte bound",
            args.scenario
        ));
    }
    cleanup_shared_private_root(&private_root, &generated)?;
    println!("{output}");
    Ok(())
}

fn benchmark_build_descriptor() -> Result<String, String> {
    let source_identity = env!("NPA_BUILD_SOURCE_REVISION");
    if source_identity == "unbound" {
        return Err("benchmark build descriptor is not source-revision-bound".to_owned());
    }
    let workspace = workspace_root()?;
    validate_runtime_source_identity(&workspace, source_identity)?;
    let source_set = validate_runtime_source_set(
        &workspace,
        env!("NPA_BUILD_VMSP_SOURCE_SET_PATHS"),
        b"npa-vmsp-source-set-v1\0",
        env!("NPA_BUILD_VMSP_SOURCE_SET_SHA256"),
        "VMSP",
    )?;
    let cargo_lock = hash_bytes(&read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SOURCE_BYTES,
        "VMSP Cargo.lock",
    )?);
    let harness = hash_bytes(&read_invocation_regular_file(
        &workspace.join("crates/npa-api/examples/bench_shared_payload.rs"),
        MAX_SOURCE_BYTES,
        "VMSP harness source",
    )?);
    let parser = hash_bytes(&read_invocation_regular_file(
        &workspace.join("crates/npa-api/src/performance_fixture_v02.rs"),
        MAX_SOURCE_BYTES,
        "VMSP fixture parser source",
    )?);
    let measure = hash_bytes(&read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/measure_process.rs"),
        MAX_SOURCE_BYTES,
        "VMSP measurement source",
    )?);
    for (label, observed, expected) in [
        (
            "Cargo.lock",
            cargo_lock.as_str(),
            concat!("sha256:", env!("NPA_BUILD_CARGO_LOCK_SHA256")),
        ),
        (
            "harness",
            harness.as_str(),
            concat!("sha256:", env!("NPA_BUILD_SHARED_PAYLOAD_SOURCE_SHA256")),
        ),
        (
            "fixture parser",
            parser.as_str(),
            concat!(
                "sha256:",
                env!("NPA_BUILD_PERFORMANCE_FIXTURE_SOURCE_SHA256")
            ),
        ),
        (
            "measurement source",
            measure.as_str(),
            concat!("sha256:", env!("NPA_BUILD_MEASURE_PROCESS_SOURCE_SHA256")),
        ),
    ] {
        if observed != expected {
            return Err(format!("VMSP {label} differs from its build descriptor"));
        }
    }
    let features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|value| !value.is_empty())
        .map(quoted)
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"npa.performance.benchmark-build.v1\",\"lane_id\":\"verified-module-shared-payload\",\"source_identity\":{},\"cargo_lock_sha256\":{},\"cargo_profile\":{},\"target\":{},\"features\":[{features}],\"rustc_vv\":{},\"rustflags\":{},\"harness_source_sha256\":{},\"source_set_sha256\":{},\"fixture_parser_source_sha256\":{},\"measure_process_source_sha256\":{}}}",
        quoted(source_identity),
        quoted(&cargo_lock),
        quoted(env!("NPA_BUILD_CARGO_PROFILE")),
        quoted(env!("NPA_BUILD_TARGET")),
        quoted(&decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?),
        quoted(&decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?),
        quoted(&harness),
        quoted(&source_set),
        quoted(&parser),
        quoted(&measure),
    ))
}

fn consume_inherited_benchmark_executable() -> Result<Vec<u8>, String> {
    let descriptor = std::env::var("NPA_BENCH_EXECUTABLE_AUDIT_FD")
        .map_err(|_| "benchmark executable audit descriptor is absent".to_owned())?
        .parse::<i32>()
        .map_err(|_| "benchmark executable audit descriptor is invalid".to_owned())?;
    let expected = std::env::var("NPA_BENCH_EXECUTABLE_SHA256")
        .map_err(|_| "benchmark executable audit hash is absent".to_owned())?;
    let bytes = consume_inherited_detached_executable(
        descriptor,
        MAX_EXECUTABLE_BYTES,
        "shared-payload benchmark executable",
    )?;
    if hash_bytes(&bytes).strip_prefix("sha256:") != Some(expected.as_str()) {
        return Err("inherited shared-payload executable hash mismatch".to_owned());
    }
    Ok(bytes)
}

fn cleanup_shared_private_root(
    private_root: &ClosedPrivateDirectory,
    generated: &GeneratedFixtureProfile,
) -> Result<(), String> {
    let (files, directories) = private_root.catalog_subtree_paths(Path::new("work"))?;
    if !files.is_empty() {
        return Err("shared-payload work root retained an unexpected regular file".to_owned());
    }
    let allowed_directories = BTreeSet::from([
        PathBuf::from("work"),
        PathBuf::from("work/target"),
        PathBuf::from("work/target/npa-package-audit-cache"),
    ]);
    if !directories.is_subset(&allowed_directories) {
        return Err(format!(
            "shared-payload work root retained an unexpected directory: {directories:?}"
        ));
    }
    private_root.remove_exact_subtree(Path::new("work"), &files, &directories)?;
    remove_generated_fixture(private_root, generated)?;
    private_root.remove_empty_root()
}

fn is_paired_scenario(selected: &PerformanceFixtureSelectionV02) -> bool {
    matches!(
        selected,
        PerformanceFixtureSelectionV02::SharedPayloadClone(_)
            | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
            | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
    )
}

#[derive(Debug)]
struct Args {
    fixture_manifest: PathBuf,
    baseline: PathBuf,
    oracle: PathBuf,
    source_identity: String,
    scenario: String,
    measurement_mode: PerformanceFixtureMeasurementMode,
    warmup: u64,
    samples: u64,
    sample_index: Option<u64>,
    emit_baseline_row: bool,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut fixture_manifest = None;
        let mut baseline = None;
        let mut oracle = None;
        let mut source_identity = None;
        let mut scenario = None;
        let mut measurement_mode = None;
        let mut warmup = None;
        let mut samples = None;
        let mut sample_index = None;
        let mut emit_baseline_row = false;
        let mut arguments = std::env::args().skip(1);
        while let Some(flag) = arguments.next() {
            if flag == "--emit-baseline-row" {
                emit_baseline_row = true;
                continue;
            }
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing value for {flag}"))?;
            match flag.as_str() {
                "--fixture-manifest" => fixture_manifest = Some(PathBuf::from(value)),
                "--baseline" => baseline = Some(PathBuf::from(value)),
                "--oracle" => oracle = Some(PathBuf::from(value)),
                "--source-identity" => source_identity = Some(value),
                "--scenario" => scenario = Some(value),
                "--measurements" if value == "detailed" => {
                    measurement_mode = Some(PerformanceFixtureMeasurementMode::Detailed);
                }
                "--measurements" => return Err("--measurements must be detailed".to_owned()),
                "--warmup" => warmup = Some(parse_u64(&value, "--warmup")?),
                "--samples" => samples = Some(parse_u64(&value, "--samples")?),
                "--sample-index" => sample_index = Some(parse_u64(&value, "--sample-index")?),
                _ => return Err(format!("unknown option {flag}")),
            }
        }
        let source_identity = source_identity.ok_or("--source-identity is required")?;
        if !valid_source_identity(&source_identity) {
            return Err(
                "--source-identity must be a lowercase Git object id with optional -dirty suffix"
                    .to_owned(),
            );
        }
        Ok(Self {
            fixture_manifest: fixture_manifest.unwrap_or_else(|| PathBuf::from(FIXTURE_MANIFEST)),
            baseline: baseline.unwrap_or_else(|| PathBuf::from(BASELINE)),
            oracle: oracle.unwrap_or_else(|| PathBuf::from(ORACLE)),
            source_identity,
            scenario: scenario.ok_or("--scenario is required")?,
            measurement_mode: measurement_mode.ok_or("--measurements detailed is required")?,
            warmup: warmup.ok_or("--warmup is required")?,
            samples: samples.ok_or("--samples is required")?,
            sample_index,
            emit_baseline_row,
        })
    }
}

struct CurrentDirectoryGuard {
    previous: PathBuf,
}

impl CurrentDirectoryGuard {
    fn enter(path: &Path) -> Result<Self, String> {
        let previous = std::env::current_dir().map_err(display_error)?;
        std::env::set_current_dir(path).map_err(display_error)?;
        Ok(Self { previous })
    }
}

impl Drop for CurrentDirectoryGuard {
    fn drop(&mut self) {
        let _ = std::env::set_current_dir(&self.previous);
    }
}

struct LoadedPackage {
    validated: ValidatedPackageManifest,
    lock: PackageLockManifest,
}

impl LoadedPackage {
    fn load(
        owner: &ClosedPrivateDirectory,
        generated: &GeneratedFixtureProfile,
    ) -> Result<Self, String> {
        let manifest = String::from_utf8(owner.read_regular_file(
            &generated.root_relative.join("npa-package.toml"),
            MAX_MANIFEST_BYTES,
        )?)
        .map_err(display_error)?;
        let validated = parse_and_validate_manifest_str(&manifest).map_err(debug_error)?;
        let lock = String::from_utf8(owner.read_regular_file(
            &generated.root_relative.join("generated/package-lock.json"),
            MAX_MANIFEST_BYTES,
        )?)
        .map_err(display_error)?;
        let lock = parse_package_lock_json(&lock).map_err(debug_error)?;
        Ok(Self { validated, lock })
    }
}

fn select_shared_scenario<'a>(
    scenarios: &'a [PerformanceFixtureSelectionV02],
    id: &str,
    measurement_mode: PerformanceFixtureMeasurementMode,
    warmup: u64,
    samples: u64,
) -> Result<&'a PerformanceFixtureSelectionV02, String> {
    let matches = scenarios
        .iter()
        .filter(|scenario| scenario.id() == id)
        .collect::<Vec<_>>();
    let [selected] = matches.as_slice() else {
        return Err(format!("scenario '{id}' must be selected exactly once"));
    };
    let common = scenario_common(selected)?;
    if common.measurement_mode != measurement_mode
        || common.warmup != warmup
        || common.samples != samples
    {
        return Err(format!(
            "scenario '{id}' CLI arguments disagree with the selected manifest row"
        ));
    }
    Ok(selected)
}

fn scenario_common(
    selected: &PerformanceFixtureSelectionV02,
) -> Result<&npa_api::PerformanceFixtureCommonV02, String> {
    match selected {
        PerformanceFixtureSelectionV02::SharedPayloadClone(value)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(value) => Ok(&value.common),
        PerformanceFixtureSelectionV02::SharedPayloadCache(value) => Ok(&value.common),
        PerformanceFixtureSelectionV02::SharedPayloadMemo(value) => Ok(&value.common),
        PerformanceFixtureSelectionV02::SharedPayloadSession(value) => Ok(&value.common),
        PerformanceFixtureSelectionV02::SharedPayloadShard(value) => Ok(&value.common),
        _ => Err("bench_shared_payload accepts only shared-payload rows".to_owned()),
    }
}

fn scenario_profile(selected: &PerformanceFixtureSelectionV02) -> Result<&'static str, String> {
    let profile = match selected {
        PerformanceFixtureSelectionV02::SharedPayloadClone(value)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(value) => value.fixture_profile,
        PerformanceFixtureSelectionV02::SharedPayloadCache(value) => value.fixture_profile,
        PerformanceFixtureSelectionV02::SharedPayloadMemo(value) => value.fixture_profile,
        PerformanceFixtureSelectionV02::SharedPayloadSession(value) => value.fixture_profile,
        PerformanceFixtureSelectionV02::SharedPayloadShard(value) => value.fixture_profile,
        _ => {
            return Err("bench_shared_payload accepts only shared-payload rows".to_owned());
        }
    };
    Ok(profile.as_str())
}

fn scenario_policies_json(selected: &PerformanceFixtureSelectionV02) -> String {
    match selected {
        PerformanceFixtureSelectionV02::SharedPayloadClone(value)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(value) => format!(
            "{{\"implementation\":{},\"decode_cache_policy\":\"disabled\",\"process_memo_policy\":\"disabled\",\"jobs\":1}}",
            quoted(value.implementation.as_str()),
        ),
        PerformanceFixtureSelectionV02::SharedPayloadCache(value) => format!(
            "{{\"implementation\":\"shared-handle\",\"phase\":{},\"decode_cache_policy\":{},\"process_memo_policy\":\"disabled\",\"jobs\":1}}",
            quoted(value.phase.as_str()),
            quoted(value.decode_cache_policy.as_str()),
        ),
        PerformanceFixtureSelectionV02::SharedPayloadMemo(value) => format!(
            "{{\"implementation\":\"shared-handle\",\"phase\":{},\"decode_cache_policy\":{},\"process_memo_policy\":{},\"jobs\":{}}}",
            quoted(value.phase.as_str()),
            quoted(value.decode_cache_policy.as_str()),
            quoted(value.process_memo_policy.as_str()),
            value.jobs,
        ),
        PerformanceFixtureSelectionV02::SharedPayloadSession(value) => format!(
            "{{\"implementation\":{},\"phase\":{},\"decode_cache_policy\":\"disabled\",\"process_memo_policy\":\"disabled\",\"jobs\":1}}",
            quoted(value.implementation.as_str()),
            quoted(value.phase.as_str()),
        ),
        PerformanceFixtureSelectionV02::SharedPayloadShard(value) => format!(
            "{{\"implementation\":\"shared-handle\",\"decode_cache_policy\":{},\"process_memo_policy\":{},\"jobs\":{}}}",
            quoted(value.decode_cache_policy.as_str()),
            quoted(value.process_memo_policy.as_str()),
            value.jobs,
        ),
        _ => "null".to_owned(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OracleRow {
    profile: String,
    descriptor_sha256: String,
    logical_identity_sha256: String,
    artifact_tree_sha256: String,
    module_count: u64,
    import_edge_count: u64,
    declaration_count: u64,
    name_table_entry_count: u64,
    level_table_node_count: u64,
    term_table_node_count: u64,
    tree_file_count: u64,
    certificate_bytes: u64,
}

fn parse_oracle(source: &str) -> Result<BTreeMap<String, OracleRow>, String> {
    let mut lines = source.lines();
    if lines.next() != Some(ORACLE_TSV_HEADER) {
        return Err("fixture oracle has the wrong header".to_owned());
    }
    let mut rows = BTreeMap::new();
    for (index, line) in lines.enumerate() {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 13 || fields[0] != GENERATOR_SCHEMA {
            return Err(format!(
                "fixture oracle row {} has the wrong shape",
                index + 2
            ));
        }
        for digest in &fields[2..5] {
            if digest.len() != 64
                || !digest
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
            {
                return Err(format!(
                    "fixture oracle row {} has an invalid digest",
                    index + 2
                ));
            }
        }
        let row = OracleRow {
            profile: fields[1].to_owned(),
            descriptor_sha256: fields[2].to_owned(),
            logical_identity_sha256: fields[3].to_owned(),
            artifact_tree_sha256: fields[4].to_owned(),
            module_count: parse_u64(fields[5], "oracle module_count")?,
            import_edge_count: parse_u64(fields[6], "oracle import_edge_count")?,
            declaration_count: parse_u64(fields[7], "oracle declaration_count")?,
            name_table_entry_count: parse_u64(fields[8], "oracle name_table_entry_count")?,
            level_table_node_count: parse_u64(fields[9], "oracle level_table_node_count")?,
            term_table_node_count: parse_u64(fields[10], "oracle term_table_node_count")?,
            tree_file_count: parse_u64(fields[11], "oracle tree_file_count")?,
            certificate_bytes: parse_u64(fields[12], "oracle certificate_bytes")?,
        };
        if rows.insert(row.profile.clone(), row).is_some() {
            return Err(format!(
                "fixture oracle profile '{}' is duplicated",
                fields[1]
            ));
        }
    }
    Ok(rows)
}

fn validate_oracle_row(
    generated: &GeneratedFixtureProfile,
    oracle: &BTreeMap<String, OracleRow>,
) -> Result<(), String> {
    let actual = OracleRow {
        profile: generated.profile.to_owned(),
        descriptor_sha256: generated.descriptor_sha256.clone(),
        logical_identity_sha256: generated.logical_identity_sha256.clone(),
        artifact_tree_sha256: generated.artifact_tree_sha256.clone(),
        module_count: generated.module_count,
        import_edge_count: generated.import_edge_count,
        declaration_count: generated.declaration_count,
        name_table_entry_count: generated.name_table_entry_count,
        level_table_node_count: generated.level_table_node_count,
        term_table_node_count: generated.term_table_node_count,
        tree_file_count: generated.tree_file_count,
        certificate_bytes: generated.certificate_bytes,
    };
    match oracle.get(generated.profile) {
        Some(expected) if expected == &actual => Ok(()),
        Some(_) => Err(format!(
            "generated profile '{}' disagrees with the generator-v1 oracle",
            generated.profile
        )),
        None => Err(format!(
            "generated profile '{}' is absent from the generator-v1 oracle",
            generated.profile
        )),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LegacyCertificateModel {
    parts: ModuleCertParts,
    logical_retained_bytes_v1: u64,
}

impl LegacyCertificateModel {
    fn from_shared(certificate: &ModuleCert) -> Result<Self, String> {
        let parts = certificate.clone().into_parts();
        let round_trip = ModuleCert::from_parts(parts.clone());
        if &round_trip != certificate {
            return Err(
                "legacy certificate model is not logically equal to shared input".to_owned(),
            );
        }
        Ok(Self {
            parts,
            logical_retained_bytes_v1: round_trip.logical_retained_bytes_v1(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LegacySessionEntry {
    certificate: LegacyCertificateModel,
    trust: TrustMode,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LegacySessionModel {
    checked: BTreeMap<ImportKey, LegacySessionEntry>,
}

impl LegacySessionModel {
    fn insert(
        &mut self,
        verified: &VerifiedModule,
        certificate: &ModuleCert,
    ) -> Result<(), String> {
        self.checked.insert(
            ImportKey {
                module: verified.module().clone(),
                export_hash: verified.export_hash(),
                certificate_hash: Some(verified.certificate_hash()),
            },
            LegacySessionEntry {
                certificate: LegacyCertificateModel::from_shared(certificate)?,
                trust: TrustMode::Normal,
            },
        );
        Ok(())
    }

    fn first_replacement(&self) -> Result<(ImportKey, LegacySessionEntry), String> {
        let key = self
            .checked
            .keys()
            .next()
            .cloned()
            .ok_or("legacy session cannot mutate an empty index")?;
        let value = self
            .checked
            .get(&key)
            .cloned()
            .ok_or("legacy session entry disappeared")?;
        Ok((key, value))
    }

    fn copied_bytes(&self) -> u64 {
        self.checked.values().fold(0_u64, |total, entry| {
            total.saturating_add(entry.certificate.logical_retained_bytes_v1)
        })
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct BlockingCounters {
    payload_allocations: u64,
    payload_copied_bytes: u64,
    payload_handle_clones: u64,
    avoided_payload_clone_bytes: u64,
    physical_decodes: u64,
    decode_cache_retained_bytes: u64,
    decode_cache_capacity_stops: u64,
    process_memo_payload_handle_clones: u64,
    session_snapshot_clones: u64,
    session_index_cow_copies: u64,
    session_index_cow_entries: u64,
    worker_count: u64,
}

impl BlockingCounters {
    fn from_report(report: &PerformanceMeasurementReport) -> Self {
        Self {
            payload_allocations: counter(
                report,
                PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
            ),
            payload_handle_clones: counter(
                report,
                PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
            ),
            avoided_payload_clone_bytes: counter(
                report,
                PerformanceMeasurementLabel::PackageAvoidedModulePayloadCloneBytes,
            ),
            physical_decodes: counter(report, PerformanceMeasurementLabel::PackageModulesDecoded),
            decode_cache_retained_bytes: counter(
                report,
                PerformanceMeasurementLabel::PackageDecodeCacheRetainedBytes,
            ),
            decode_cache_capacity_stops: counter(
                report,
                PerformanceMeasurementLabel::PackageDecodeCacheCapacityStops,
            ),
            process_memo_payload_handle_clones: counter(
                report,
                PerformanceMeasurementLabel::PackageProcessMemoPayloadHandleClones,
            ),
            session_snapshot_clones: counter(
                report,
                PerformanceMeasurementLabel::PackageSessionSnapshotClones,
            ),
            session_index_cow_copies: counter(
                report,
                PerformanceMeasurementLabel::PackageSessionIndexCowCopies,
            ),
            session_index_cow_entries: counter(
                report,
                PerformanceMeasurementLabel::PackageSessionIndexCowEntries,
            ),
            worker_count: counter(report, PerformanceMeasurementLabel::PackageEffectiveJobs),
            ..Self::default()
        }
    }

    fn json(self) -> String {
        format!(
            "{{\"payload_allocations\":{},\"payload_copied_bytes\":{},\"payload_handle_clones\":{},\"avoided_payload_clone_bytes\":{},\"physical_decodes\":{},\"decode_cache_retained_bytes\":{},\"decode_cache_capacity_stops\":{},\"process_memo_payload_handle_clones\":{},\"session_snapshot_clones\":{},\"session_index_cow_copies\":{},\"session_index_cow_entries\":{},\"worker_count\":{}}}",
            self.payload_allocations,
            self.payload_copied_bytes,
            self.payload_handle_clones,
            self.avoided_payload_clone_bytes,
            self.physical_decodes,
            self.decode_cache_retained_bytes,
            self.decode_cache_capacity_stops,
            self.process_memo_payload_handle_clones,
            self.session_snapshot_clones,
            self.session_index_cow_copies,
            self.session_index_cow_entries,
            self.worker_count,
        )
    }
}

struct SampleRecord {
    index: u64,
    elapsed_ns: u64,
    blocking: BlockingCounters,
}

impl SampleRecord {
    fn json(&self) -> String {
        format!(
            "{{\"index\":{},\"elapsed_ns\":{},\"blocking_counters\":{}}}",
            self.index,
            self.elapsed_ns,
            self.blocking.json(),
        )
    }
}

struct RunResult {
    samples: Vec<SampleRecord>,
    final_report: PerformanceMeasurementReport,
}

fn run_scenario(
    selected: &PerformanceFixtureSelectionV02,
    generated: &GeneratedFixtureProfile,
    package: &LoadedPackage,
    baseline: &str,
    check_baseline: bool,
    sample_index: Option<u64>,
) -> Result<RunResult, String> {
    match selected {
        PerformanceFixtureSelectionV02::SharedPayloadClone(fixture)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(fixture) => {
            run_clone(fixture, generated, baseline, check_baseline, sample_index)
        }
        PerformanceFixtureSelectionV02::SharedPayloadCache(fixture) => {
            run_cache(fixture, generated, package, baseline, check_baseline)
        }
        PerformanceFixtureSelectionV02::SharedPayloadMemo(fixture) => {
            run_memo(fixture, generated, package, baseline, check_baseline)
        }
        PerformanceFixtureSelectionV02::SharedPayloadSession(fixture) => {
            run_session(fixture, generated, baseline, check_baseline, sample_index)
        }
        PerformanceFixtureSelectionV02::SharedPayloadShard(fixture) => {
            run_shard(fixture, generated, package, baseline, check_baseline)
        }
        _ => Err("bench_shared_payload accepts only shared-payload rows".to_owned()),
    }
}

fn custom_ownership_report(
    certificate: &CertificatePayloadObservation,
    package: &PackagePayloadOwnershipObservation,
) -> Result<PerformanceMeasurementReport, String> {
    let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
    recorder.observe_certificate_payload_ownership(certificate, package);
    recorder.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 0);
    recorder.add_counter(PerformanceMeasurementLabel::PackageCacheResults, 0);
    recorder.add_counter(PerformanceMeasurementLabel::PackageMemoResults, 0);
    recorder
        .report()
        .ok_or("detailed ownership recorder did not produce a report".to_owned())
}

fn counter(report: &PerformanceMeasurementReport, label: PerformanceMeasurementLabel) -> u64 {
    report
        .counters
        .iter()
        .find(|counter| counter.label == label)
        .map(|counter| counter.value)
        .unwrap_or(0)
}

const SHARED_PAYLOAD_CLONE_BASELINE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageAvoidedModulePayloadCloneBytes,
    PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
    PerformanceMeasurementLabel::PackageModulePayloadUniqueBytes,
    PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
];
const SHARED_PAYLOAD_CACHE_BASELINE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageDecodeCacheCapacityStops,
    PerformanceMeasurementLabel::PackageDecodeCachePeakRetainedBytes,
    PerformanceMeasurementLabel::PackageDecodeCacheRetainedBytes,
    PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
    PerformanceMeasurementLabel::PackageModulePayloadUniqueBytes,
    PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
    PerformanceMeasurementLabel::PackageModulesDecoded,
];
const SHARED_PAYLOAD_MEMO_BASELINE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
    PerformanceMeasurementLabel::PackageModulePayloadUniqueBytes,
    PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
    PerformanceMeasurementLabel::PackageModulesDecoded,
    PerformanceMeasurementLabel::PackageProcessMemoPayloadHandleClones,
];
const SHARED_PAYLOAD_SESSION_BASELINE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
    PerformanceMeasurementLabel::PackageSessionIndexCowCopies,
    PerformanceMeasurementLabel::PackageSessionIndexCowEntries,
    PerformanceMeasurementLabel::PackageSessionSnapshotClones,
];
const SHARED_PAYLOAD_SHARD_BASELINE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
    PerformanceMeasurementLabel::PackageModulePayloadUniqueBytes,
    PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
    PerformanceMeasurementLabel::PackageModulesDecoded,
    PerformanceMeasurementLabel::PackageRequestedJobs,
];
const PERFORMANCE_COVERAGE_LABELS: &[PerformanceMeasurementLabel] = &[
    PerformanceMeasurementLabel::PackageLiveResults,
    PerformanceMeasurementLabel::PackageCacheResults,
    PerformanceMeasurementLabel::PackageMemoResults,
];

fn validate_vmsp_measurement_envelope(report: &PerformanceMeasurementReport) -> Result<(), String> {
    if report.schema != PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9
        || report.mode != PerformanceMeasurementMode::Detailed
        || report.trusted
        || report.proof_evidence
        || report.overflowed
    {
        return Err(
            "shared-payload sample has an incompatible schema, mode, trust boundary, or overflow"
                .to_owned(),
        );
    }
    let mut previous = None;
    for measured in &report.counters {
        let label = measured.label.as_str();
        if previous.is_some_and(|previous| previous >= label)
            || measured.unit != measured.label.unit()
        {
            return Err("shared-payload sample counters are not canonical".to_owned());
        }
        previous = Some(label);
    }
    Ok(())
}

fn validate_sample_baseline(
    baseline: &str,
    scenario: &str,
    report: &PerformanceMeasurementReport,
    baseline_labels: &[PerformanceMeasurementLabel],
) -> Result<(), String> {
    validate_vmsp_measurement_envelope(report)?;

    // The common measurement report deliberately contains more stable
    // diagnostics than each VMSP row promotes into its blocking baseline.
    // Project only that row family's closed counter catalog plus the common
    // coverage counters. Missing promoted counters remain missing, so the
    // strict baseline validator still rejects them instead of synthesizing a
    // zero value.
    let mut projected = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
    for measured in &report.counters {
        if baseline_labels.contains(&measured.label)
            || PERFORMANCE_COVERAGE_LABELS.contains(&measured.label)
        {
            projected.add_counter(measured.label, measured.value);
        }
    }
    let projected = projected
        .report()
        .ok_or("shared-payload baseline projection did not produce a report")?;
    if report.schema != projected.schema {
        return Err("shared-payload sample uses an incompatible measurement schema".to_owned());
    }
    validate_performance_measurement_baseline(baseline, scenario, &projected).map_err(display_error)
}

fn omitted_details(
    counts: PerformanceDetailCounts,
    retained_len: usize,
    label: &str,
) -> Result<PerformanceDetailCounts, String> {
    let retained = u64::try_from(retained_len).map_err(display_error)?;
    if counts.retained != retained
        || counts.retained.checked_add(counts.omitted) != Some(counts.attempted)
    {
        return Err(format!(
            "shared-payload {label} detail counts are inconsistent"
        ));
    }
    Ok(PerformanceDetailCounts {
        attempted: counts.attempted,
        retained: 0,
        omitted: counts.attempted,
    })
}

fn compact_vmsp_measurement_report(
    report: &PerformanceMeasurementReport,
) -> Result<PerformanceMeasurementReport, String> {
    validate_vmsp_measurement_envelope(report)?;
    let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
    for measured in &report.counters {
        recorder.add_counter(measured.label, measured.value);
    }
    let mut compact = recorder
        .report()
        .ok_or("shared-payload compact measurement recorder did not produce a report")?;
    compact.input_identity = report.input_identity.clone();
    compact.module_details =
        omitted_details(report.module_details, report.modules.len(), "module")?;
    compact.declaration_details = omitted_details(
        report.declaration_details,
        report.declarations.len(),
        "declaration",
    )?;
    compact.candidate_details = omitted_details(
        report.candidate_details,
        report.candidates.len(),
        "candidate",
    )?;
    compact.worker_details =
        omitted_details(report.worker_details, report.workers.len(), "worker")?;
    compact.package_layer_details = omitted_details(
        report.package_layer_details,
        report.package_layers.len(),
        "package layer",
    )?;
    compact.package_shard_details = omitted_details(
        report.package_shard_details,
        report.package_shards.len(),
        "package shard",
    )?;
    compact.detail_truncated = report.detail_truncated
        || compact.module_details.attempted != 0
        || compact.declaration_details.attempted != 0
        || compact.candidate_details.attempted != 0
        || compact.worker_details.attempted != 0
        || compact.package_layer_details.attempted != 0
        || compact.package_shard_details.attempted != 0;
    compact.clock = report.clock;
    Ok(compact)
}

fn run_clone(
    fixture: &SharedPayloadCloneFixture,
    generated: &GeneratedFixtureProfile,
    baseline: &str,
    check_baseline: bool,
    sample_index: Option<u64>,
) -> Result<RunResult, String> {
    let module = generated
        .modules
        .first()
        .ok_or("clone fixture has no certificate")?;
    if generated.modules.len() != 1
        || u64::try_from(module.certificate_bytes.len()).map_err(display_error)?
            != fixture.payload_bytes
    {
        return Err("clone fixture payload byte count mismatch".to_owned());
    }
    let legacy = LegacyCertificateModel::from_shared(&module.certificate)?;
    for _ in 0..fixture.common.warmup {
        let _ = execute_clone_sample(fixture, &module.certificate, &legacy)?;
    }
    let mut samples = Vec::new();
    let mut final_report = None;
    let indices = sample_indices(sample_index, fixture.common.samples)?;
    for index in indices {
        let (elapsed_ns, blocking, report) =
            execute_clone_sample(fixture, &module.certificate, &legacy)?;
        if check_baseline {
            validate_sample_baseline(
                baseline,
                &fixture.common.id,
                &report,
                SHARED_PAYLOAD_CLONE_BASELINE_LABELS,
            )?;
        }
        samples.push(SampleRecord {
            index,
            elapsed_ns,
            blocking,
        });
        final_report = Some(report);
    }
    Ok(RunResult {
        samples,
        final_report: final_report.ok_or("clone runner produced no samples")?,
    })
}

fn execute_clone_sample(
    fixture: &SharedPayloadCloneFixture,
    shared: &ModuleCert,
    legacy: &LegacyCertificateModel,
) -> Result<(u64, BlockingCounters, PerformanceMeasurementReport), String> {
    let logical_bytes = shared.logical_retained_bytes_v1();
    let started = Instant::now();
    match fixture.implementation {
        PerformanceFixtureImplementation::LegacyModel => {
            for _ in 0..fixture.clone_count {
                let cloned = legacy.clone();
                black_box(&cloned);
            }
        }
        PerformanceFixtureImplementation::SharedHandle => {
            for _ in 0..fixture.clone_count {
                let cloned = shared.clone();
                black_box(&cloned);
            }
        }
        _ => return Err("unsupported shared-payload implementation".to_owned()),
    }
    let elapsed_ns = elapsed_ns(started);
    let (package, blocking) = match fixture.implementation {
        PerformanceFixtureImplementation::LegacyModel => (
            PackagePayloadOwnershipObservation::default(),
            BlockingCounters {
                payload_allocations: fixture.clone_count,
                payload_copied_bytes: logical_bytes.saturating_mul(fixture.clone_count),
                ..BlockingCounters::default()
            },
        ),
        PerformanceFixtureImplementation::SharedHandle => {
            let package = PackagePayloadOwnershipObservation {
                module_payload_handle_clones: fixture.clone_count,
                avoided_module_payload_clone_bytes: logical_bytes
                    .saturating_mul(fixture.clone_count),
                ..PackagePayloadOwnershipObservation::default()
            };
            (
                package,
                BlockingCounters {
                    payload_handle_clones: fixture.clone_count,
                    avoided_payload_clone_bytes: logical_bytes.saturating_mul(fixture.clone_count),
                    ..BlockingCounters::default()
                },
            )
        }
        _ => return Err("unsupported shared-payload implementation".to_owned()),
    };
    if fixture.implementation == PerformanceFixtureImplementation::SharedHandle
        && (blocking.payload_allocations != 0 || blocking.payload_copied_bytes != 0)
    {
        return Err("shared certificate clone copied payload bytes".to_owned());
    }
    let report = custom_ownership_report(&CertificatePayloadObservation::default(), &package)?;
    Ok((elapsed_ns, blocking, report))
}

fn run_cache(
    fixture: &SharedPayloadCacheFixture,
    generated: &GeneratedFixtureProfile,
    package: &LoadedPackage,
    baseline: &str,
    check_baseline: bool,
) -> Result<RunResult, String> {
    if generated.certificate_bytes != fixture.payload_bytes || generated.module_count != 1 {
        return Err("cache fixture payload byte count mismatch".to_owned());
    }
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    for _ in 0..fixture.common.warmup {
        let report = verify_generated_package(
            generated,
            package,
            1,
            PackageVerificationMemoMode::Disabled,
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        require_passed(&report)?;
    }
    if fixture.phase == PerformanceFixtureCachePhase::MissInsert {
        clear_package_verification_decode_cache();
    }
    let mut samples = Vec::new();
    let mut final_report = None;
    for index in 0..fixture.common.samples {
        if fixture.phase == PerformanceFixtureCachePhase::MissInsert {
            clear_package_verification_decode_cache();
        }
        let started = Instant::now();
        let report = verify_generated_package(
            generated,
            package,
            1,
            PackageVerificationMemoMode::Disabled,
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        let elapsed_ns = elapsed_ns(started);
        require_passed(&report)?;
        if check_baseline {
            validate_sample_baseline(
                baseline,
                &fixture.common.id,
                measurement(&report)?,
                SHARED_PAYLOAD_CACHE_BASELINE_LABELS,
            )?;
        }
        let blocking = BlockingCounters::from_report(measurement(&report)?);
        let cache_enabled =
            fixture.decode_cache_policy != PerformanceFixtureDecodeCachePolicy::Disabled;
        let charge = PackageDecodeCacheChargeState::from_measurement_report(
            cache_enabled,
            report.measurements.as_ref(),
        );
        match (cache_enabled, charge) {
            (false, PackageDecodeCacheChargeState::Disabled)
            | (true, PackageDecodeCacheChargeState::Bounded { .. }) => {}
            _ => {
                return Err(
                    "production decode-cache report did not yield the required charge state"
                        .to_owned(),
                );
            }
        }
        match fixture.phase {
            PerformanceFixtureCachePhase::Cold if blocking.decode_cache_retained_bytes != 0 => {
                return Err("disabled cold decode retained a cache payload".to_owned());
            }
            PerformanceFixtureCachePhase::MissInsert if blocking.physical_decodes != 1 => {
                return Err(
                    "decode-cache insertion sample did not perform exactly one decode".to_owned(),
                );
            }
            PerformanceFixtureCachePhase::Hit
                if blocking.physical_decodes != 0 || blocking.payload_handle_clones != 2 =>
            {
                return Err(
                    "decode-cache hit did not perform the two exact production handle clones"
                        .to_owned(),
                );
            }
            _ => {}
        }
        if blocking.payload_copied_bytes != 0 || blocking.decode_cache_capacity_stops != 0 {
            return Err("decode-cache sample copied payload bytes or hit capacity".to_owned());
        }
        samples.push(SampleRecord {
            index,
            elapsed_ns,
            blocking,
        });
        final_report = report.measurements;
    }
    Ok(RunResult {
        samples,
        final_report: final_report.ok_or("cache runner produced no measurements")?,
    })
}

fn run_memo(
    fixture: &SharedPayloadMemoFixture,
    generated: &GeneratedFixtureProfile,
    package: &LoadedPackage,
    baseline: &str,
    check_baseline: bool,
) -> Result<RunResult, String> {
    let handle = PackageVerificationProcessMemoHandle::new(process_memo_limits()?);
    handle.clear().map_err(debug_error)?;
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    for _ in 0..fixture.common.warmup {
        let report = verify_generated_package(
            generated,
            package,
            usize::try_from(fixture.jobs).map_err(display_error)?,
            PackageVerificationMemoMode::ProcessLocal(handle.clone()),
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        require_passed(&report)?;
    }
    if fixture.phase == PerformanceFixtureMemoPhase::Miss {
        handle.clear().map_err(debug_error)?;
    }
    let mut samples = Vec::new();
    let mut final_report = None;
    for index in 0..fixture.common.samples {
        if fixture.phase == PerformanceFixtureMemoPhase::Miss {
            handle.clear().map_err(debug_error)?;
        }
        let started = Instant::now();
        let report = verify_generated_package(
            generated,
            package,
            usize::try_from(fixture.jobs).map_err(display_error)?,
            PackageVerificationMemoMode::ProcessLocal(handle.clone()),
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        let elapsed_ns = elapsed_ns(started);
        require_passed(&report)?;
        let measured = measurement(&report)?;
        if check_baseline {
            validate_sample_baseline(
                baseline,
                &fixture.common.id,
                measured,
                SHARED_PAYLOAD_MEMO_BASELINE_LABELS,
            )?;
        }
        let blocking = BlockingCounters::from_report(measured);
        match fixture.phase {
            PerformanceFixtureMemoPhase::Miss
                if report.memo_counters.misses != generated.modules.len()
                    || report.memo_counters.hits != 0 =>
            {
                return Err("process-memo miss sample has the wrong lookup counts".to_owned());
            }
            PerformanceFixtureMemoPhase::Hit
                if report.memo_counters.hits != generated.modules.len()
                    || report.memo_counters.misses != 0
                    || blocking.process_memo_payload_handle_clones != generated.module_count =>
            {
                return Err(
                    "process-memo hit did not reuse one immutable value per module".to_owned(),
                );
            }
            _ => {}
        }
        let stats = handle.stats().map_err(debug_error)?;
        if stats.retained_entries > MEMO_MAX_ENTRIES
            || stats.retained_weighted_certificate_bytes > MEMO_MAX_BYTES
        {
            return Err("caller-owned process memo exceeded its configured limits".to_owned());
        }
        samples.push(SampleRecord {
            index,
            elapsed_ns,
            blocking,
        });
        final_report = report.measurements;
    }
    Ok(RunResult {
        samples,
        final_report: final_report.ok_or("memo runner produced no measurements")?,
    })
}

fn run_session(
    fixture: &SharedPayloadSessionFixture,
    generated: &GeneratedFixtureProfile,
    baseline: &str,
    check_baseline: bool,
    sample_index: Option<u64>,
) -> Result<RunResult, String> {
    let entry_count = usize::try_from(fixture.session_entries).map_err(display_error)?;
    if generated.modules.len() < entry_count {
        return Err("session fixture has fewer modules than selected entries".to_owned());
    }
    let selected_modules = &generated.modules[..entry_count];
    let mut shared = VerifierSession::new();
    let mut legacy = LegacySessionModel::default();
    for module in selected_modules {
        shared.register_verified_module(module.verified.clone());
        legacy.insert(&module.verified, &module.certificate)?;
    }
    if legacy.checked.len() != entry_count {
        return Err("legacy session model lost a logical lookup entry".to_owned());
    }
    for _ in 0..fixture.common.warmup {
        let _ = execute_session_sample(fixture, &shared, &legacy, selected_modules)?;
    }
    let mut samples = Vec::new();
    let mut final_report = None;
    let indices = sample_indices(sample_index, fixture.common.samples)?;
    for index in indices {
        let (elapsed_ns, blocking, report) =
            execute_session_sample(fixture, &shared, &legacy, selected_modules)?;
        if check_baseline {
            validate_sample_baseline(
                baseline,
                &fixture.common.id,
                &report,
                SHARED_PAYLOAD_SESSION_BASELINE_LABELS,
            )?;
        }
        if fixture.implementation == PerformanceFixtureImplementation::SharedHandle
            && blocking.payload_copied_bytes != 0
        {
            return Err("shared session operation copied certificate payload bytes".to_owned());
        }
        samples.push(SampleRecord {
            index,
            elapsed_ns,
            blocking,
        });
        final_report = Some(report);
    }
    Ok(RunResult {
        samples,
        final_report: final_report.ok_or("session runner produced no samples")?,
    })
}

fn execute_session_sample(
    fixture: &SharedPayloadSessionFixture,
    shared: &VerifierSession,
    legacy: &LegacySessionModel,
    modules: &[performance_fixture_generator::GeneratedFixtureModule],
) -> Result<(u64, BlockingCounters, PerformanceMeasurementReport), String> {
    let mut certificate = CertificatePayloadObservation::default();
    let started;
    let mut blocking = BlockingCounters::default();
    match (fixture.implementation, fixture.phase) {
        (
            PerformanceFixtureImplementation::LegacyModel,
            PerformanceFixtureSessionPhase::Snapshot,
        ) => {
            started = Instant::now();
            let snapshot = legacy.clone();
            black_box(&snapshot);
            blocking.payload_allocations = fixture.session_entries;
            blocking.payload_copied_bytes = legacy.copied_bytes();
        }
        (
            PerformanceFixtureImplementation::LegacyModel,
            PerformanceFixtureSessionPhase::FirstCow,
        ) => {
            let mut snapshot = legacy.clone();
            let (key, value) = snapshot.first_replacement()?;
            started = Instant::now();
            snapshot.checked.insert(key, value);
            black_box(&snapshot);
        }
        (
            PerformanceFixtureImplementation::SharedHandle,
            PerformanceFixtureSessionPhase::Snapshot,
        ) => {
            started = Instant::now();
            let snapshot = shared.snapshot_observed(Some(&mut certificate));
            black_box(&snapshot);
        }
        (
            PerformanceFixtureImplementation::SharedHandle,
            PerformanceFixtureSessionPhase::FirstCow,
        ) => {
            let first = modules.first().ok_or("session COW fixture is empty")?;
            let mut snapshot = shared.snapshot();
            let replacement = first.verified.clone();
            started = Instant::now();
            snapshot.register_verified_module_with_trust_observed(
                replacement,
                TrustMode::Normal,
                Some(&mut certificate),
            );
            black_box(&snapshot);
        }
        _ => return Err("unsupported session implementation or phase".to_owned()),
    }
    let elapsed_ns = elapsed_ns(started);
    blocking.session_snapshot_clones = certificate.session_snapshot_clones;
    blocking.session_index_cow_copies = certificate.session_index_cow_copies;
    blocking.session_index_cow_entries = certificate.session_index_cow_entries;
    if fixture.implementation == PerformanceFixtureImplementation::SharedHandle {
        match fixture.phase {
            PerformanceFixtureSessionPhase::Snapshot
                if certificate.session_snapshot_clones != 1
                    || certificate.session_index_cow_copies != 0 =>
            {
                return Err(
                    "shared session snapshot did not clone exactly one index handle".to_owned(),
                );
            }
            PerformanceFixtureSessionPhase::FirstCow
                if certificate.session_snapshot_clones != 0
                    || certificate.session_index_cow_copies != 1
                    || certificate.session_index_cow_entries != fixture.session_entries =>
            {
                return Err(
                    "shared session first mutation did not copy exactly the selected index"
                        .to_owned(),
                );
            }
            _ => {}
        }
    }
    let report =
        custom_ownership_report(&certificate, &PackagePayloadOwnershipObservation::default())?;
    Ok((elapsed_ns, blocking, report))
}

fn run_shard(
    fixture: &SharedPayloadShardFixture,
    generated: &GeneratedFixtureProfile,
    package: &LoadedPackage,
    baseline: &str,
    check_baseline: bool,
) -> Result<RunResult, String> {
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    let jobs = usize::try_from(fixture.jobs).map_err(display_error)?;
    for _ in 0..fixture.common.warmup {
        let report = verify_generated_package(
            generated,
            package,
            jobs,
            PackageVerificationMemoMode::Disabled,
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        require_passed(&report)?;
    }
    let mut samples = Vec::new();
    let mut final_report = None;
    for index in 0..fixture.common.samples {
        let started = Instant::now();
        let report = verify_generated_package(
            generated,
            package,
            jobs,
            PackageVerificationMemoMode::Disabled,
            decode_mode(fixture.decode_cache_policy)?,
        )?;
        let elapsed_ns = elapsed_ns(started);
        require_passed(&report)?;
        let measured = measurement(&report)?;
        if check_baseline {
            validate_sample_baseline(
                baseline,
                &fixture.common.id,
                measured,
                SHARED_PAYLOAD_SHARD_BASELINE_LABELS,
            )?;
        }
        let blocking = BlockingCounters::from_report(measured);
        if blocking.payload_copied_bytes != 0
            || package_verification_decode_cache_entry_count() != 0
            || package_verification_decode_cache_retained_bytes() != 0
        {
            return Err(
                "disabled-policy shard sample retained or copied cache payloads".to_owned(),
            );
        }
        samples.push(SampleRecord {
            index,
            elapsed_ns,
            blocking,
        });
        final_report = report.measurements;
    }
    Ok(RunResult {
        samples,
        final_report: final_report.ok_or("shard runner produced no measurements")?,
    })
}

fn verify_generated_package(
    generated: &GeneratedFixtureProfile,
    package: &LoadedPackage,
    jobs: usize,
    memoization: PackageVerificationMemoMode,
    decode_cache: PackageVerificationDecodeCacheMode,
) -> Result<npa_api::PackageVerificationReport, String> {
    verify_package_fast_source_free_with_options(
        &package.validated,
        &package.lock,
        package_artifacts(generated),
        PackageVerificationExecutionOptions {
            jobs,
            selected_modules: None,
            memoization,
            decode_cache,
            collect_decode_cache_counters: true,
            measurement_mode: PerformanceMeasurementMode::Detailed,
        },
    )
    .map_err(debug_error)
}

fn package_artifacts(generated: &GeneratedFixtureProfile) -> Vec<PackageCertificateArtifact<'_>> {
    generated
        .modules
        .iter()
        .map(|module| PackageCertificateArtifact {
            path: PackagePath::new(&module.certificate_path),
            bytes: &module.certificate_bytes,
        })
        .collect()
}

fn decode_mode(
    policy: PerformanceFixtureDecodeCachePolicy,
) -> Result<PackageVerificationDecodeCacheMode, String> {
    match policy {
        PerformanceFixtureDecodeCachePolicy::Disabled => {
            Ok(PackageVerificationDecodeCacheMode::Disabled)
        }
        PerformanceFixtureDecodeCachePolicy::ProcessLocal => {
            Ok(PackageVerificationDecodeCacheMode::ProcessLocal)
        }
        PerformanceFixtureDecodeCachePolicy::ProcessLocalAndPersistent => {
            Ok(PackageVerificationDecodeCacheMode::ProcessLocalAndPersistent)
        }
        _ => Err("strict v0.2 parser returned an unknown decode-cache policy".to_owned()),
    }
}

fn process_memo_limits() -> Result<PackageVerificationProcessMemoLimits, String> {
    Ok(PackageVerificationProcessMemoLimits {
        max_entries: NonZeroUsize::new(MEMO_MAX_ENTRIES)
            .ok_or("memo entry limit must be nonzero")?,
        max_weighted_certificate_bytes: NonZeroU64::new(MEMO_MAX_BYTES)
            .ok_or("memo byte limit must be nonzero")?,
    })
}

fn measurement(
    report: &npa_api::PackageVerificationReport,
) -> Result<&PerformanceMeasurementReport, String> {
    report
        .measurements
        .as_ref()
        .ok_or("package verifier omitted detailed measurements".to_owned())
}

fn require_passed(report: &npa_api::PackageVerificationReport) -> Result<(), String> {
    if report.status.as_str() == "passed" {
        Ok(())
    } else {
        Err("generated package verification did not pass".to_owned())
    }
}

fn baseline_row_json(
    selected: &PerformanceFixtureSelectionV02,
    report: &PerformanceMeasurementReport,
) -> Result<String, String> {
    let module_count = match selected {
        PerformanceFixtureSelectionV02::SharedPayloadCache(_) => 1,
        PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
        | PerformanceFixtureSelectionV02::SharedPayloadShard(_) => 64,
        PerformanceFixtureSelectionV02::SharedPayloadClone(_)
        | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(_) => 0,
        _ => return Err("cannot render a non-shared baseline row".to_owned()),
    };
    let live_results_min = match selected {
        PerformanceFixtureSelectionV02::SharedPayloadCache(_) => 1,
        PerformanceFixtureSelectionV02::SharedPayloadMemo(value)
            if value.phase == PerformanceFixtureMemoPhase::Miss =>
        {
            64
        }
        PerformanceFixtureSelectionV02::SharedPayloadShard(_) => 64,
        _ => 0,
    };
    let proof_evidence_reduction_allowed = matches!(
        selected,
        PerformanceFixtureSelectionV02::SharedPayloadMemo(value)
            if value.phase == PerformanceFixtureMemoPhase::Hit
    );
    let labels: &[PerformanceMeasurementLabel] = match selected {
        PerformanceFixtureSelectionV02::SharedPayloadClone(_)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(_) => {
            SHARED_PAYLOAD_CLONE_BASELINE_LABELS
        }
        PerformanceFixtureSelectionV02::SharedPayloadCache(_) => {
            SHARED_PAYLOAD_CACHE_BASELINE_LABELS
        }
        PerformanceFixtureSelectionV02::SharedPayloadMemo(_) => SHARED_PAYLOAD_MEMO_BASELINE_LABELS,
        PerformanceFixtureSelectionV02::SharedPayloadSession(_) => {
            SHARED_PAYLOAD_SESSION_BASELINE_LABELS
        }
        PerformanceFixtureSelectionV02::SharedPayloadShard(_) => {
            SHARED_PAYLOAD_SHARD_BASELINE_LABELS
        }
        _ => return Err("cannot render a non-shared baseline row".to_owned()),
    };
    let mut counters = labels
        .iter()
        .map(|label| (label.as_str(), counter(report, *label)))
        .collect::<Vec<_>>();
    counters.sort_by_key(|(label, _)| *label);
    let counters = counters
        .iter()
        .map(|(label, value)| format!("\"{label}\":{value}"))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"id\":{},\"status\":\"passed\",\"module_count\":{module_count},\"deterministic_counters\":{{{counters}}},\"coverage\":{{\"live_results_min\":{live_results_min},\"proof_evidence_reduction_allowed\":{proof_evidence_reduction_allowed}}}}}",
        quoted(selected.id()),
    ))
}

#[derive(Clone, Copy)]
struct ElapsedStatistics {
    median: u64,
    median_absolute_deviation: u64,
    minimum: u64,
    maximum: u64,
}

fn elapsed_statistics(samples: &[u64]) -> ElapsedStatistics {
    let median_value = median(samples);
    let deviations = samples
        .iter()
        .map(|sample| sample.abs_diff(median_value))
        .collect::<Vec<_>>();
    ElapsedStatistics {
        median: median_value,
        median_absolute_deviation: median(&deviations),
        minimum: samples.iter().copied().min().unwrap_or(0),
        maximum: samples.iter().copied().max().unwrap_or(0),
    }
}

fn median(values: &[u64]) -> u64 {
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 1 {
        sorted[middle]
    } else {
        sorted[middle - 1] / 2
            + sorted[middle] / 2
            + (sorted[middle - 1] % 2 + sorted[middle] % 2) / 2
    }
}

fn elapsed_ns(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn hash_bytes(bytes: &[u8]) -> String {
    format_package_hash(&package_file_hash(bytes))
}

fn require_embedded_hash(label: &str, actual: &str, embedded_hex: &str) -> Result<(), String> {
    let expected = format!("sha256:{embedded_hex}");
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "runtime {label} identity differs from the benchmark build"
        ))
    }
}

fn sample_indices(sample_index: Option<u64>, manifest_samples: u64) -> Result<Vec<u64>, String> {
    match sample_index {
        Some(index) if index < manifest_samples => Ok(vec![index]),
        Some(_) => Err("sample index is outside the manifest population".to_owned()),
        None => Ok((0..manifest_samples).collect()),
    }
}

fn workspace_root() -> Result<PathBuf, String> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or("npa-api is not nested under the workspace root".to_owned())
}

fn decode_build_hex(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("build metadata hex length is odd".to_owned());
    }
    let bytes = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok((hex_digit(pair[0])? << 4) | hex_digit(pair[1])?))
        .collect::<Result<Vec<_>, String>>()?;
    String::from_utf8(bytes).map_err(display_error)
}

fn hex_digit(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("build metadata contains invalid hex".to_owned()),
    }
}

fn parse_u64(value: &str, field: &str) -> Result<u64, String> {
    if value.is_empty()
        || !value.bytes().all(|byte| byte.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(format!("{field} must be a canonical u64"));
    }
    value
        .parse::<u64>()
        .map_err(|_| format!("{field} exceeds the u64 limit"))
}

fn valid_source_identity(value: &str) -> bool {
    let object_id = value.strip_suffix("-dirty").unwrap_or(value);
    object_id.len() == 40
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn quoted(value: &str) -> String {
    format!("\"{}\"", json_escape(value))
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::new();
    for character in value.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            character if character.is_control() => {
                let value = character as u32;
                const HEX: &[u8; 16] = b"0123456789abcdef";
                escaped.push_str("\\u");
                for shift in [12, 8, 4, 0] {
                    escaped.push(char::from(HEX[((value >> shift) & 0xf) as usize]));
                }
            }
            character => escaped.push(character),
        }
    }
    escaped
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn debug_error(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn shared_payload_json_escape_round_trips_all_control_characters() {
        let source = (0_u8..=0x1f)
            .map(char::from)
            .chain(['"', '\\', 'x'])
            .collect::<String>();
        let encoded = format!("{{\"value\":{}}}", quoted(&source));
        let document = npa_api::JsonDocument::parse(&encoded).unwrap();
        let value = document
            .root()
            .object_members()
            .unwrap()
            .iter()
            .find(|member| member.key() == "value")
            .unwrap()
            .value()
            .string_value()
            .unwrap();
        assert_eq!(value, source);
        for byte in 0_u8..=0x1f {
            assert!(
                !encoded.as_bytes().contains(&byte),
                "raw JSON control byte {byte:#04x} escaped containment"
            );
        }
        assert!(encoded.contains("\\u001f"));
    }

    #[test]
    fn shared_payload_source_identity_is_exact_sha1_grammar() {
        let oid = "0123456789abcdef0123456789abcdef01234567";
        assert!(valid_source_identity(oid));
        assert!(valid_source_identity(&format!("{oid}-dirty")));
        assert!(!valid_source_identity(&"a".repeat(64)));
        assert!(!valid_source_identity(&format!("{}-dirty-dirty", oid)));
    }

    #[test]
    fn shared_payload_private_root_is_owner_only() {
        let root = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
        let metadata = std::fs::symlink_metadata(root.path()).unwrap();
        assert!(metadata.file_type().is_dir());
        assert!(!metadata.file_type().is_symlink());
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            assert_eq!(metadata.mode() & 0o777, 0o700);
        }
    }

    #[cfg(unix)]
    #[test]
    fn shared_payload_private_root_rejects_symlink_temporary_parent() {
        use std::os::unix::fs::symlink;

        let container = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
        let link = container.path().join("temporary-parent-link");
        symlink(container.path(), &link).unwrap();
        let error = match ClosedPrivateDirectory::new_in(&link, "npa-shared-payload") {
            Ok(_) => panic!("symlink temporary parent was accepted"),
            Err(error) => error,
        };
        assert_eq!(error, "temporary parent is not a real directory");
    }

    #[cfg(unix)]
    #[test]
    fn shared_payload_private_root_drop_rejects_path_replacement() {
        let root = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
        let original = root.path().to_path_buf();
        let relocated = original.with_extension("original-directory");
        std::fs::rename(&original, &relocated).unwrap();
        std::fs::create_dir(&original).unwrap();

        drop(root);

        assert!(original.is_dir(), "replacement directory must survive Drop");
        assert!(
            relocated.is_dir(),
            "original directory must survive relocation"
        );
        std::fs::remove_dir(&original).unwrap();
        std::fs::remove_dir(&relocated).unwrap();
    }

    const SHARED_PROFILES: [&str; 6] = [
        "payload-1mib",
        "payload-16mib",
        "payload-near-limit",
        "payload-heavy-multi-module",
        "session-index",
        "small-certificate",
    ];

    #[test]
    fn shared_payload_fixture_profiles() {
        let expected = [
            ("payload-1mib", 1, 0, 1_048_576),
            ("payload-16mib", 1, 0, 16_777_216),
            ("payload-near-limit", 1, 0, 67_108_000),
            ("payload-heavy-multi-module", 64, 112, 67_108_864),
            ("session-index", 1_024, 0, 1_048_576),
            ("small-certificate", 1, 0, 1_024),
        ];
        for (profile, modules, edges, bytes) in expected {
            let descriptor =
                performance_fixture_generator::fixture_profile_descriptor(profile).unwrap();
            assert_eq!(descriptor.name, profile);
            assert_eq!(descriptor.tuples.len(), modules);
            assert_eq!(
                descriptor
                    .tuples
                    .iter()
                    .map(|tuple| tuple.imports.len())
                    .sum::<usize>(),
                edges
            );
            assert_eq!(
                descriptor
                    .tuples
                    .iter()
                    .map(|tuple| tuple.target_certificate_bytes)
                    .sum::<u64>(),
                bytes
            );
        }
    }

    #[test]
    fn shared_payload_fixture_identity_v1() {
        let oracle = parse_oracle(include_str!(
            "../../../testdata/performance/fixture-generator.v1.tsv"
        ))
        .unwrap();
        for profile in SHARED_PROFILES {
            let private = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
            let generated =
                materialize_fixture_profile(profile, &private, Path::new("fixture")).unwrap();
            validate_oracle_row(&generated, &oracle).unwrap();
            assert_eq!(
                artifact_tree_identity(&private, &generated).unwrap(),
                (
                    generated.artifact_tree_sha256.clone(),
                    generated.tree_file_count
                )
            );
            remove_generated_fixture(&private, &generated).unwrap();
            private.remove_empty_root().unwrap();
        }

        let descriptor =
            performance_fixture_generator::fixture_profile_descriptor("payload-heavy-multi-module")
                .unwrap();
        let identity = performance_fixture_generator::descriptor_digest_for_test(&descriptor);
        let mut changed_name = descriptor.clone();
        changed_name.tuples[0].module_name.replace_range(..1, "Q");
        assert_ne!(
            performance_fixture_generator::descriptor_digest_for_test(&changed_name),
            identity
        );
        let mut changed_import = descriptor;
        changed_import.tuples[8].imports[0].replace_range(..1, "Q");
        assert_ne!(
            performance_fixture_generator::descriptor_digest_for_test(&changed_import),
            identity
        );

        let private = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
        let generated =
            materialize_fixture_profile("small-certificate", &private, Path::new("fixture"))
                .unwrap();
        let original = artifact_tree_identity(&private, &generated).unwrap();
        for relative in [
            generated.modules[0].certificate_path.as_str(),
            "npa-package.toml",
            "generated/package-lock.json",
        ] {
            let relative = generated.root_relative.join(relative);
            let bytes = private
                .read_regular_file(&relative, 128 * 1024 * 1024)
                .unwrap();
            let mut changed = bytes.clone();
            changed[0] ^= 1;
            private
                .replace_exact_file(&relative, &bytes, &changed)
                .unwrap();
            assert_ne!(
                artifact_tree_identity(&private, &generated).unwrap(),
                original
            );
            private
                .replace_exact_file(&relative, &changed, &bytes)
                .unwrap();
            assert_eq!(
                artifact_tree_identity(&private, &generated).unwrap(),
                original
            );
        }
        remove_generated_fixture(&private, &generated).unwrap();
        private.remove_empty_root().unwrap();
    }

    #[test]
    fn shared_payload_manifest_selected_schema() {
        let manifest = validate_performance_fixture_selection_v02(include_str!(
            "../../../testdata/performance/fixtures/manifest.v0.2.json"
        ))
        .unwrap();
        let shared = manifest
            .scenarios
            .iter()
            .filter(|scenario| scenario.id().starts_with("shared-payload-"))
            .collect::<Vec<_>>();
        assert_eq!(shared.len(), 47);
        let mut counts = BTreeMap::<&str, usize>::new();
        for scenario in &shared {
            let kind = match scenario {
                PerformanceFixtureSelectionV02::SharedPayloadClone(_) => "clone",
                PerformanceFixtureSelectionV02::SharedPayloadCache(_) => "cache",
                PerformanceFixtureSelectionV02::SharedPayloadMemo(_) => "memo",
                PerformanceFixtureSelectionV02::SharedPayloadSession(_) => "session",
                PerformanceFixtureSelectionV02::SharedPayloadShard(_) => "shard",
                PerformanceFixtureSelectionV02::SharedPayloadSmall(_) => "small",
                _ => panic!("shared-payload ID used a non-shared variant"),
            };
            *counts.entry(kind).or_default() += 1;
        }
        assert_eq!(
            counts,
            BTreeMap::from([
                ("cache", 5),
                ("clone", 24),
                ("memo", 2),
                ("session", 12),
                ("shard", 2),
                ("small", 2),
            ])
        );

        let expected_source = format!(
            "{{\"schema\":\"npa.performance.fixtures.v0.2\",\"scenarios\":[{}]}}",
            performance_fixture_generator::shared_payload_rows().join(",")
        );
        let expected = validate_performance_fixture_selection_v02(&expected_source).unwrap();
        let expected_ids = expected
            .scenarios
            .iter()
            .map(|scenario| scenario.id().to_owned())
            .collect::<BTreeSet<_>>();
        let actual_ids = shared
            .iter()
            .map(|scenario| scenario.id().to_owned())
            .collect::<BTreeSet<_>>();
        assert_eq!(actual_ids, expected_ids);

        let first = shared[0];
        let common = scenario_common(first).unwrap();
        assert!(select_shared_scenario(
            &manifest.scenarios,
            first.id(),
            PerformanceFixtureMeasurementMode::Detailed,
            common.warmup,
            common.samples - 1,
        )
        .is_err());

        let mut paired_groups = BTreeMap::<&str, Vec<&PerformanceFixtureSelectionV02>>::new();
        for scenario in &shared {
            if matches!(
                scenario,
                PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
            ) {
                paired_groups
                    .entry(&scenario_common(scenario).unwrap().interleave_group)
                    .or_default()
                    .push(scenario);
            }
        }
        assert_eq!(paired_groups.len(), 19);
        assert_eq!(
            paired_groups
                .keys()
                .filter(|group| group.starts_with("shared-payload-clone-"))
                .count(),
            12
        );
        assert_eq!(
            paired_groups
                .keys()
                .filter(|group| group.starts_with("shared-payload-session-"))
                .count(),
            6
        );
        assert_eq!(
            paired_groups
                .keys()
                .filter(|group| group.starts_with("shared-payload-small-"))
                .count(),
            1
        );
        for rows in paired_groups.values() {
            assert_eq!(rows.len(), 2);
            for selected in rows {
                assert!(is_paired_scenario(selected));
                assert_eq!(sample_indices(Some(0), 7).unwrap(), [0]);
                assert_eq!(sample_indices(Some(6), 7).unwrap(), [6]);
                assert!(sample_indices(Some(7), 7).is_err());
            }
        }
    }

    #[test]
    fn snap_vmsp_checked_manifest_is_generator_exact() {
        let generated = performance_fixture_generator::successor_manifest(include_str!(
            "../../../testdata/performance/fixtures/manifest.v0.1.json"
        ))
        .unwrap();
        assert_eq!(
            generated,
            include_str!("../../../testdata/performance/fixtures/manifest.v0.2.json")
        );
    }

    #[test]
    fn vmsp_measurement_identity_is_the_selected_generator_tree() {
        let private = ClosedPrivateDirectory::new("npa-vmsp-input-identity").unwrap();
        let generated =
            materialize_fixture_profile("small-certificate", &private, Path::new("fixture"))
                .unwrap();
        let mut result = custom_ownership_report(
            &CertificatePayloadObservation::default(),
            &PackagePayloadOwnershipObservation::default(),
        )
        .unwrap();
        assert_eq!(result.input_identity, None);
        result.input_identity = Some(format!("sha256:{}", generated.artifact_tree_sha256));
        let json = performance_measurement_report_json(&result);
        assert!(json.contains(&format!(
            "\"input_identity\":\"sha256:{}\"",
            generated.artifact_tree_sha256
        )));
        remove_generated_fixture(&private, &generated).unwrap();
        private.remove_empty_root().unwrap();
    }

    #[test]
    fn vmsp_baseline_projection_is_closed_over_promoted_counters() {
        let baseline =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let report = custom_ownership_report(
            &CertificatePayloadObservation::default(),
            &PackagePayloadOwnershipObservation::default(),
        )
        .unwrap();
        assert!(
            report.counters.len()
                > SHARED_PAYLOAD_CLONE_BASELINE_LABELS.len() + PERFORMANCE_COVERAGE_LABELS.len(),
            "the regression must exercise a common report with additional stable counters"
        );
        validate_sample_baseline(
            baseline,
            "shared-payload-clone-1m-c1-legacy",
            &report,
            SHARED_PAYLOAD_CLONE_BASELINE_LABELS,
        )
        .unwrap();

        let mut missing = report.clone();
        missing.counters.retain(|counter| {
            counter.label != PerformanceMeasurementLabel::PackageModulePayloadsFrozen
        });
        assert!(validate_sample_baseline(
            baseline,
            "shared-payload-clone-1m-c1-legacy",
            &missing,
            SHARED_PAYLOAD_CLONE_BASELINE_LABELS,
        )
        .is_err());

        let mut changed = report;
        changed
            .counters
            .iter_mut()
            .find(|counter| {
                counter.label == PerformanceMeasurementLabel::PackageModulePayloadHandleClones
            })
            .unwrap()
            .value = 1;
        assert!(validate_sample_baseline(
            baseline,
            "shared-payload-clone-1m-c1-legacy",
            &changed,
            SHARED_PAYLOAD_CLONE_BASELINE_LABELS,
        )
        .is_err());
    }

    #[test]
    fn vmsp_measurement_projection_omits_bounded_details_before_capture() {
        let mut report = custom_ownership_report(
            &CertificatePayloadObservation::default(),
            &PackagePayloadOwnershipObservation::default(),
        )
        .unwrap();
        report.input_identity = Some(format!("sha256:{}", "a".repeat(64)));
        report.modules = (0..2_048)
            .map(|index| npa_api::PerformanceModuleMeasurement {
                module: format!("M{index:04}.{}", "x".repeat(4_090)),
                certificate_bytes: 0,
                declaration_count: 0,
                import_count: 0,
                checker_elapsed_ns: 0,
                package_sharding: None,
            })
            .collect();
        report.module_details = PerformanceDetailCounts {
            attempted: 2_048,
            retained: 2_048,
            omitted: 0,
        };
        let expanded = performance_measurement_report_json(&report);
        assert!(expanded.len() > 8 * 1024 * 1024);

        let compact = compact_vmsp_measurement_report(&report).unwrap();
        let compact_json = performance_measurement_report_json(&compact);
        assert!(compact_json.len() < 64 * 1024);
        assert_eq!(compact.input_identity, report.input_identity);
        assert_eq!(compact.counters, report.counters);
        assert!(compact.modules.is_empty());
        assert_eq!(
            compact.module_details,
            PerformanceDetailCounts {
                attempted: 2_048,
                retained: 0,
                omitted: 2_048,
            }
        );
        assert!(compact.detail_truncated);
        assert_eq!(compact.clock, report.clock);

        report.module_details.retained -= 1;
        assert!(compact_vmsp_measurement_report(&report).is_err());
    }

    #[test]
    fn vmsp_real_cache_report_fits_the_controller_capture_bound_after_projection() {
        let manifest = validate_performance_fixture_selection_v02(include_str!(
            "../../../testdata/performance/fixtures/manifest.v0.2.json"
        ))
        .unwrap();
        let selected = manifest
            .scenarios
            .iter()
            .find(|scenario| scenario.id() == "shared-payload-cache-1m-cold-disabled")
            .unwrap();
        let private = ClosedPrivateDirectory::new("npa-vmsp-cache-projection").unwrap();
        private.create_directory(Path::new("work")).unwrap();
        let generated = materialize_fixture_profile(
            scenario_profile(selected).unwrap(),
            &private,
            Path::new("fixture"),
        )
        .unwrap();
        let package = LoadedPackage::load(&private, &generated).unwrap();
        let working_root = private.path().join("work");
        let mut result = {
            let _working_directory = CurrentDirectoryGuard::enter(&working_root).unwrap();
            run_scenario(
                selected,
                &generated,
                &package,
                include_str!("../../../testdata/performance/baselines/measurements.v0.1.json"),
                true,
                None,
            )
            .unwrap()
        };
        clear_package_import_context_export_disk_cache();
        result.final_report.input_identity =
            Some(format!("sha256:{}", generated.artifact_tree_sha256));
        let expanded_len = performance_measurement_report_json(&result.final_report).len();
        let compact = compact_vmsp_measurement_report(&result.final_report).unwrap();
        let compact_len = performance_measurement_report_json(&compact).len();
        cleanup_shared_private_root(&private, &generated).unwrap();
        assert!(compact_len < expanded_len);
        assert!(compact_len < 8 * 1024 * 1024);
    }

    #[test]
    fn legacy_models_are_logically_equal_but_verifier_inaccessible() {
        let private = ClosedPrivateDirectory::new("npa-shared-payload").unwrap();
        let generated =
            materialize_fixture_profile("small-certificate", &private, Path::new("fixture"))
                .unwrap();
        let model = LegacyCertificateModel::from_shared(&generated.modules[0].certificate).unwrap();
        assert_eq!(
            ModuleCert::from_parts(model.parts.clone()),
            generated.modules[0].certificate
        );
        assert!(model.logical_retained_bytes_v1 > 0);
        remove_generated_fixture(&private, &generated).unwrap();
        private.remove_empty_root().unwrap();
    }
}

//! Closed release harness for package-verifier linear-DAG planning.

use std::path::{Path, PathBuf};
use std::time::Instant;

use npa_api::{
    benchmark_package_verifier_linear_dag_planning, JsonDocument, JsonMember, JsonValue,
    PackageVerifierLinearDagBenchmarkObservation, PackageVerifierLinearDagBenchmarkShape,
    PerformanceMeasurementMode,
};
use npa_package::{format_package_hash, package_file_hash};
#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;

use closed_private_tree::{read_absolute_regular_file, read_invocation_regular_file};

const MAX_BASELINE_BYTES: u64 = 8 * 1024 * 1024;
const MAX_CARGO_LOCK_BYTES: u64 = 32 * 1024 * 1024;
const MAX_HARNESS_BYTES: u64 = 4 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;

const PREFIX: &str = "package.verifier.linear_dag_planning.v1.";
const BASELINE_SCHEMA: &str = "npa.package_verifier.linear_dag_planning.baselines.v0.1";
const BASELINE_UPDATE_POLICY: &str = "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request.";

#[derive(Clone, Debug, PartialEq, Eq)]
struct Arguments {
    scenario: String,
    baseline: PathBuf,
    source_identity: String,
    warmup: usize,
    samples: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("linear-DAG benchmark failed: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = parse_arguments(std::env::args().skip(1).collect())?;
    let (shape, mode) = parse_scenario(&args.scenario)?;
    let baseline = read_input(&args.baseline, MAX_BASELINE_BYTES, "linear-DAG baseline")?;
    let baseline_source =
        std::str::from_utf8(&baseline).map_err(|_| "baseline is not UTF-8".to_owned())?;
    let baseline_hash = format_package_hash(&package_file_hash(&baseline));

    for _ in 0..args.warmup {
        benchmark_package_verifier_linear_dag_planning(shape, mode)
            .map_err(|error| format!("warmup planning failed: {error:?}"))?;
    }
    let mut samples_ns = Vec::with_capacity(args.samples);
    let mut observation = None;
    for _ in 0..args.samples {
        let started = Instant::now();
        let next = benchmark_package_verifier_linear_dag_planning(shape, mode)
            .map_err(|error| format!("measured planning failed: {error:?}"))?;
        samples_ns.push(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
        validate_baseline_row(baseline_source, &args.scenario, shape, mode, &next)?;
        observation = Some(next);
    }
    let observation = observation.ok_or("no measured observation")?;
    let build = linear_dag_build_provenance(&args.source_identity)?;
    let executable = std::env::current_exe()
        .map_err(|error| format!("current executable is unavailable: {error}"))?;
    let executable = executable
        .canonicalize()
        .map_err(|error| format!("canonicalize current executable: {error}"))?;
    let build_identity_hash = format_package_hash(&package_file_hash(&read_input(
        &executable,
        MAX_EXECUTABLE_BYTES,
        "linear-DAG executable",
    )?));
    let elapsed = elapsed_statistics(&samples_ns)?;
    println!(
        "{}",
        run_json(
            &args,
            shape,
            mode,
            &baseline_hash,
            &build_identity_hash,
            &build,
            &samples_ns,
            elapsed,
            &observation,
        )
    );
    Ok(())
}

fn parse_arguments(args: Vec<String>) -> Result<Arguments, String> {
    let mut scenario = None;
    let mut baseline = None;
    let mut source_identity = None;
    let mut warmup = None;
    let mut samples = None;
    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for {}", args[index]))?;
        match args[index].as_str() {
            "--scenario" if scenario.is_none() => scenario = Some(value.clone()),
            "--baseline" if baseline.is_none() => baseline = Some(PathBuf::from(value)),
            "--source-identity" if source_identity.is_none() => {
                source_identity = Some(value.clone())
            }
            "--warmup" if warmup.is_none() => {
                warmup = Some(value.parse::<usize>().map_err(|_| "invalid --warmup")?)
            }
            "--samples" if samples.is_none() => {
                samples = Some(value.parse::<usize>().map_err(|_| "invalid --samples")?)
            }
            flag => return Err(format!("unknown or duplicate option: {flag}")),
        }
        index += 2;
    }
    let result = Arguments {
        scenario: scenario.ok_or("missing --scenario")?,
        baseline: baseline.ok_or("missing --baseline")?,
        source_identity: source_identity.ok_or("missing --source-identity")?,
        warmup: warmup.ok_or("missing --warmup")?,
        samples: samples.ok_or("missing --samples")?,
    };
    if result.warmup != 1 || result.samples != 7 {
        return Err("closed harness requires --warmup 1 --samples 7".to_owned());
    }
    if !valid_source_identity(&result.source_identity) {
        return Err(
            "source identity must be lowercase hexadecimal with optional -dirty".to_owned(),
        );
    }
    Ok(result)
}

fn parse_scenario(
    scenario: &str,
) -> Result<
    (
        PackageVerifierLinearDagBenchmarkShape,
        PerformanceMeasurementMode,
    ),
    String,
> {
    let suffix = scenario
        .strip_prefix(PREFIX)
        .ok_or("scenario prefix mismatch")?;
    let (shape, mode) = suffix
        .rsplit_once('.')
        .ok_or("scenario shape/mode mismatch")?;
    let shape = match shape {
        "chain4096" => PackageVerifierLinearDagBenchmarkShape::Chain4096,
        "wide4096" => PackageVerifierLinearDagBenchmarkShape::Wide4096,
        "diamond4096" => PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        _ => return Err("unsupported scenario shape".to_owned()),
    };
    let mode = match mode {
        "off" => PerformanceMeasurementMode::Off,
        "summary" => PerformanceMeasurementMode::Summary,
        "detailed" => PerformanceMeasurementMode::Detailed,
        _ => return Err("unsupported scenario mode".to_owned()),
    };
    Ok((shape, mode))
}

fn validate_baseline_row(
    source: &str,
    scenario: &str,
    shape: PackageVerifierLinearDagBenchmarkShape,
    mode: PerformanceMeasurementMode,
    observation: &PackageVerifierLinearDagBenchmarkObservation,
) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid baseline JSON at byte {}", error.offset))?;
    let root = exact_object(
        document.root(),
        &["schema", "scenarios", "update_policy"],
        "baseline",
    )?;
    expect_string(root[0].value(), BASELINE_SCHEMA, "baseline.schema")?;
    let rows = expect_array(root[1].value(), "baseline.scenarios")?;
    expect_string(
        root[2].value(),
        BASELINE_UPDATE_POLICY,
        "baseline.update_policy",
    )?;
    if rows.len() != 9 {
        return Err("baseline.scenarios must contain exactly nine rows".to_owned());
    }
    let mut found = None;
    for (index, row) in rows.iter().enumerate() {
        let path = format!("baseline.scenarios[{index}]");
        let fields = exact_object(
            row,
            &[
                "id",
                "shape",
                "measurement_mode",
                "module_count",
                "edge_count",
                "selected_seed",
                "selected_count",
                "layer_count",
                "critical_path_length",
                "oracle_match",
                "shard_profile",
                "counters",
            ],
            &path,
        )?;
        let id = fields[0]
            .value()
            .string_value()
            .ok_or_else(|| format!("{path}.id must be a string"))?;
        if id == scenario {
            if found.is_some() {
                return Err("duplicate baseline scenario".to_owned());
            }
            found = Some((path, fields));
        }
    }
    let (path, fields) = found.ok_or("baseline scenario is missing")?;
    expect_string(fields[1].value(), shape.as_str(), &format!("{path}.shape"))?;
    expect_string(
        fields[2].value(),
        mode.as_str(),
        &format!("{path}.measurement_mode"),
    )?;
    expect_unsigned_eq(
        fields[3].value(),
        observation.module_count,
        &format!("{path}.module_count"),
    )?;
    expect_unsigned_eq(
        fields[4].value(),
        observation.edge_count,
        &format!("{path}.edge_count"),
    )?;
    expect_string(
        fields[5].value(),
        "Bench.M0fff",
        &format!("{path}.selected_seed"),
    )?;
    expect_unsigned_eq(
        fields[6].value(),
        observation.selected_count,
        &format!("{path}.selected_count"),
    )?;
    expect_unsigned_eq(
        fields[7].value(),
        observation.layer_count,
        &format!("{path}.layer_count"),
    )?;
    expect_unsigned_eq(
        fields[8].value(),
        observation.critical_path_length,
        &format!("{path}.critical_path_length"),
    )?;
    expect_bool(
        fields[9].value(),
        observation.oracle_match,
        &format!("{path}.oracle_match"),
    )?;
    validate_shard_profile(
        fields[10].value(),
        observation,
        &format!("{path}.shard_profile"),
    )?;
    validate_counters(fields[11].value(), observation, &format!("{path}.counters"))?;
    Ok(())
}

fn validate_shard_profile(
    value: &JsonValue<'_>,
    observation: &PackageVerifierLinearDagBenchmarkObservation,
    path: &str,
) -> Result<(), String> {
    let profile = &observation.shard_profile;
    let fields = exact_object(
        value,
        &[
            "cost_model",
            "memory_model",
            "import_weight",
            "memory_budget_bytes",
            "worker_stack_bytes",
            "fixed_worker_bytes",
            "scratch_multiplier",
            "requested_jobs",
            "artifact_bytes_per_module",
            "term_materialization_bytes_per_worker",
            "per_worker_bytes",
            "prepared_shared_bytes",
            "peak_shared_base_context_bytes",
            "peak_combined_shared_context_bytes",
            "minimum_memory_jobs",
            "estimate_overflowed",
            "layer_input_sha256",
        ],
        path,
    )?;
    expect_string(
        fields[0].value(),
        profile.cost_model.as_str(),
        &format!("{path}.cost_model"),
    )?;
    expect_string(
        fields[1].value(),
        profile.memory_model.as_str(),
        &format!("{path}.memory_model"),
    )?;
    let values = [
        profile.import_weight,
        profile.memory_budget_bytes,
        profile.worker_stack_bytes,
        profile.fixed_worker_bytes,
        profile.scratch_multiplier,
        profile.requested_jobs,
        profile.artifact_bytes_per_module,
        profile.term_materialization_bytes_per_worker,
        profile.per_worker_bytes,
        profile.prepared_shared_bytes,
        profile.peak_shared_base_context_bytes,
        profile.peak_combined_shared_context_bytes,
        profile.minimum_memory_jobs,
    ];
    let keys = [
        "import_weight",
        "memory_budget_bytes",
        "worker_stack_bytes",
        "fixed_worker_bytes",
        "scratch_multiplier",
        "requested_jobs",
        "artifact_bytes_per_module",
        "term_materialization_bytes_per_worker",
        "per_worker_bytes",
        "prepared_shared_bytes",
        "peak_shared_base_context_bytes",
        "peak_combined_shared_context_bytes",
        "minimum_memory_jobs",
    ];
    for (offset, (key, expected)) in keys.into_iter().zip(values).enumerate() {
        expect_unsigned_eq(
            fields[offset + 2].value(),
            expected,
            &format!("{path}.{key}"),
        )?;
    }
    expect_bool(
        fields[15].value(),
        profile.estimate_overflowed,
        &format!("{path}.estimate_overflowed"),
    )?;
    expect_string(
        fields[16].value(),
        &profile.layer_input_sha256,
        &format!("{path}.layer_input_sha256"),
    )
}

fn validate_counters(
    value: &JsonValue<'_>,
    observation: &PackageVerifierLinearDagBenchmarkObservation,
    path: &str,
) -> Result<(), String> {
    let counters = &observation.counters;
    let keys = [
        "graph_index_constructions",
        "reverse_list_sort_calls",
        "forward_vertex_dequeues",
        "forward_edge_visits",
        "layer_assignments",
        "complete_entry_fixed_point_scans",
        "verified_prefix_record_visits",
        "critical_path_state_nodes",
        "path_prefix_clone_elements",
        "final_reconstructed_path_length",
    ];
    let fields = exact_object(value, &keys, path)?;
    let values = [
        counters.graph_index_constructions,
        counters.reverse_list_sort_calls,
        counters.forward_vertex_dequeues,
        counters.forward_edge_visits,
        counters.layer_assignments,
        counters.complete_entry_fixed_point_scans,
        counters.verified_prefix_record_visits,
        counters.critical_path_state_nodes,
        counters.path_prefix_clone_elements,
        counters.final_reconstructed_path_length,
    ];
    for (index, (key, expected)) in keys.into_iter().zip(values).enumerate() {
        expect_unsigned_eq(fields[index].value(), expected, &format!("{path}.{key}"))?;
    }
    Ok(())
}

fn shard_profile_json(observation: &PackageVerifierLinearDagBenchmarkObservation) -> String {
    let p = &observation.shard_profile;
    format!("{{\"cost_model\":\"{}\",\"memory_model\":\"{}\",\"import_weight\":{},\"memory_budget_bytes\":{},\"worker_stack_bytes\":{},\"fixed_worker_bytes\":{},\"scratch_multiplier\":{},\"requested_jobs\":{},\"artifact_bytes_per_module\":{},\"term_materialization_bytes_per_worker\":{},\"per_worker_bytes\":{},\"prepared_shared_bytes\":{},\"peak_shared_base_context_bytes\":{},\"peak_combined_shared_context_bytes\":{},\"minimum_memory_jobs\":{},\"estimate_overflowed\":{},\"layer_input_sha256\":\"{}\"}}", p.cost_model.as_str(), p.memory_model.as_str(), p.import_weight, p.memory_budget_bytes, p.worker_stack_bytes, p.fixed_worker_bytes, p.scratch_multiplier, p.requested_jobs, p.artifact_bytes_per_module, p.term_materialization_bytes_per_worker, p.per_worker_bytes, p.prepared_shared_bytes, p.peak_shared_base_context_bytes, p.peak_combined_shared_context_bytes, p.minimum_memory_jobs, p.estimate_overflowed, p.layer_input_sha256)
}

fn observation_json(observation: &PackageVerifierLinearDagBenchmarkObservation) -> String {
    let c = &observation.counters;
    format!("{{\"module_count\":{},\"edge_count\":{},\"selected_count\":{},\"layer_count\":{},\"critical_path_length\":{},\"oracle_match\":{},\"shard_profile\":{},\"counters\":{{\"graph_index_constructions\":{},\"reverse_list_sort_calls\":{},\"forward_vertex_dequeues\":{},\"forward_edge_visits\":{},\"layer_assignments\":{},\"complete_entry_fixed_point_scans\":{},\"verified_prefix_record_visits\":{},\"critical_path_state_nodes\":{},\"path_prefix_clone_elements\":{},\"final_reconstructed_path_length\":{}}}}}", observation.module_count, observation.edge_count, observation.selected_count, observation.layer_count, observation.critical_path_length, observation.oracle_match, shard_profile_json(observation), c.graph_index_constructions, c.reverse_list_sort_calls, c.forward_vertex_dequeues, c.forward_edge_visits, c.layer_assignments, c.complete_entry_fixed_point_scans, c.verified_prefix_record_visits, c.critical_path_state_nodes, c.path_prefix_clone_elements, c.final_reconstructed_path_length)
}

#[allow(clippy::too_many_arguments)]
fn run_json(
    args: &Arguments,
    shape: PackageVerifierLinearDagBenchmarkShape,
    mode: PerformanceMeasurementMode,
    baseline_hash: &str,
    build_identity_hash: &str,
    build: &LinearDagBuildProvenance<'_>,
    samples_ns: &[u64],
    elapsed: (u64, u64, u64, u64),
    observation: &PackageVerifierLinearDagBenchmarkObservation,
) -> String {
    let features = build
        .features
        .iter()
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    let samples = samples_ns
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"schema\":\"npa.package_verifier.linear_dag_planning.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"{}\",\"baseline_hash\":\"{}\",\"source_identity\":\"{}\",\"build_identity_hash\":\"{}\",\"cargo_lock_hash\":\"{}\",\"harness_source_hash\":\"{}\",\"production_source_set_hash\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"features\":[{}],\"rustflags\":\"{}\",\"profile\":{{\"shape\":\"{}\",\"measurement_mode\":\"{}\",\"shard_profile\":{}}},\"warmup\":{},\"sample_count\":{},\"samples_ns\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"observation\":{}}}",
        json_escape(&args.scenario),
        json_escape(baseline_hash),
        json_escape(build.source_identity),
        json_escape(build_identity_hash),
        json_escape(&build.cargo_lock_hash),
        json_escape(&build.harness_source_hash),
        json_escape(&build.production_source_set_hash),
        json_escape(&build.rustc_vv),
        json_escape(build.cargo_profile),
        json_escape(build.target),
        features,
        json_escape(&build.rustflags),
        shape.as_str(),
        mode.as_str(),
        shard_profile_json(observation),
        args.warmup,
        args.samples,
        samples,
        elapsed.0,
        elapsed.1,
        elapsed.2,
        elapsed.3,
        observation_json(observation),
    )
}

fn exact_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    keys: &[&str],
    path: &str,
) -> Result<&'value [JsonMember<'source>], String> {
    let members = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    let actual = members.iter().map(JsonMember::key).collect::<Vec<_>>();
    if actual != keys {
        Err(format!("{path} keys/order mismatch: {actual:?}"))
    } else {
        Ok(members)
    }
}

fn expect_array<'value, 'source>(
    value: &'value JsonValue<'source>,
    path: &str,
) -> Result<&'value [JsonValue<'source>], String> {
    value
        .array_elements()
        .ok_or_else(|| format!("{path} must be an array"))
}

fn expect_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    match value.string_value() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!("{path} is {actual:?}, expected {expected:?}")),
        None => Err(format!("{path} must be a string")),
    }
}

fn expect_unsigned_eq(value: &JsonValue<'_>, expected: u64, path: &str) -> Result<(), String> {
    let actual = value
        .number_raw()
        .ok_or_else(|| format!("{path} must be an unsigned integer"))?
        .parse::<u64>()
        .map_err(|_| format!("{path} must be an unsigned integer"))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{path} is {actual}, expected {expected}"))
    }
}

fn expect_bool(value: &JsonValue<'_>, expected: bool, path: &str) -> Result<(), String> {
    match value.bool_value() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!("{path} is {actual}, expected {expected}")),
        None => Err(format!("{path} must be boolean")),
    }
}

fn elapsed_statistics(values: &[u64]) -> Result<(u64, u64, u64, u64), String> {
    if values.is_empty() || values.len().is_multiple_of(2) {
        return Err("elapsed samples require a nonempty odd count".to_owned());
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let median = sorted[sorted.len() / 2];
    let mut deviations = sorted
        .iter()
        .map(|value| value.abs_diff(median))
        .collect::<Vec<_>>();
    deviations.sort_unstable();
    Ok((
        median,
        deviations[deviations.len() / 2],
        sorted[0],
        sorted[sorted.len() - 1],
    ))
}

fn valid_source_identity(value: &str) -> bool {
    let base = value.strip_suffix("-dirty").unwrap_or(value);
    base.len() == 40
        && base
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

struct LinearDagBuildProvenance<'a> {
    source_identity: &'a str,
    cargo_lock_hash: String,
    harness_source_hash: String,
    production_source_set_hash: String,
    rustc_vv: String,
    cargo_profile: &'a str,
    target: &'a str,
    features: Vec<&'a str>,
    rustflags: String,
}

fn linear_dag_build_provenance(
    requested_source_identity: &str,
) -> Result<LinearDagBuildProvenance<'static>, String> {
    let source_identity = env!("NPA_BUILD_SOURCE_IDENTITY");
    if source_identity == "unbound" {
        return Err(
            "benchmark was built without NPA_BENCH_SOURCE_IDENTITY; rebuild the exact source"
                .to_owned(),
        );
    }
    if requested_source_identity != source_identity {
        return Err(format!(
            "requested source identity {requested_source_identity:?} does not match embedded build identity {source_identity:?}"
        ));
    }
    let workspace = workspace_root()?;
    runtime_source_set::validate_runtime_source_identity(&workspace, source_identity)?;
    let cargo_lock_hash = format!("sha256:{}", env!("NPA_BUILD_CARGO_LOCK_SHA256"));
    let runtime_lock = read_input(
        &workspace.join("Cargo.lock"),
        MAX_CARGO_LOCK_BYTES,
        "workspace Cargo.lock",
    )?;
    let runtime_lock_hash = format_package_hash(&package_file_hash(&runtime_lock));
    if runtime_lock_hash != cargo_lock_hash {
        return Err(format!(
            "runtime Cargo.lock {runtime_lock_hash} does not match embedded build Cargo.lock {cargo_lock_hash}"
        ));
    }
    let harness_source_hash = format!("sha256:{}", env!("NPA_BUILD_PDG_SOURCE_SHA256"));
    let runtime_harness = read_input(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/bench_package_linear_dag.rs"),
        MAX_HARNESS_BYTES,
        "linear-DAG harness source",
    )?;
    let runtime_harness_hash = format_package_hash(&package_file_hash(&runtime_harness));
    if runtime_harness_hash != harness_source_hash {
        return Err(format!(
            "runtime harness {runtime_harness_hash} does not match embedded harness {harness_source_hash}"
        ));
    }
    let production_source_set_hash = validate_production_source_set(&workspace)?;
    let mut features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .collect::<Vec<_>>();
    features.sort_unstable();
    features.dedup();
    Ok(LinearDagBuildProvenance {
        source_identity,
        cargo_lock_hash,
        harness_source_hash,
        production_source_set_hash,
        rustc_vv: decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?,
        cargo_profile: env!("NPA_BUILD_CARGO_PROFILE"),
        target: env!("NPA_BUILD_TARGET"),
        features,
        rustflags: decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?,
    })
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
        .map(|pair| {
            hex_digit(pair[0]).and_then(|high| hex_digit(pair[1]).map(|low| high << 4 | low))
        })
        .collect::<Result<Vec<_>, _>>()?;
    String::from_utf8(bytes).map_err(|_| "embedded rustc metadata is not UTF-8".to_owned())
}

fn hex_digit(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("build metadata contains non-hex input".to_owned()),
    }
}

fn validate_production_source_set(workspace: &Path) -> Result<String, String> {
    runtime_source_set::validate_runtime_source_set(
        workspace,
        env!("NPA_BUILD_PACKAGE_VERIFIER_SOURCE_SET_PATHS"),
        b"npa-package-verifier-source-set-v1\0",
        env!("NPA_BUILD_PACKAGE_VERIFIER_SOURCE_SET_SHA256"),
        "package-verifier",
    )
}

fn json_escape(value: &str) -> String {
    value
        .chars()
        .flat_map(|character| match character {
            '"' => "\\\"".chars().collect::<Vec<_>>(),
            '\\' => "\\\\".chars().collect(),
            '\n' => "\\n".chars().collect(),
            '\r' => "\\r".chars().collect(),
            '\t' => "\\t".chars().collect(),
            c if c.is_control() => format!("\\u{:04x}", c as u32).chars().collect(),
            c => vec![c],
        })
        .collect()
}

fn workspace_root() -> Result<PathBuf, String> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| error.to_string())
}

fn read_input(path: &Path, maximum_bytes: u64, label: &str) -> Result<Vec<u8>, String> {
    if path.is_absolute() {
        read_absolute_regular_file(path, maximum_bytes, label)
    } else {
        read_invocation_regular_file(path, maximum_bytes, label)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked_baseline() -> String {
        std::fs::read_to_string(
            workspace_root().unwrap().join(
                "testdata/performance/baselines/package-verifier-linear-dag-planning.v0.1.json",
            ),
        )
        .unwrap()
    }

    #[test]
    fn linear_dag_checked_baseline_is_strict() {
        let source = checked_baseline();
        for shape in [
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PackageVerifierLinearDagBenchmarkShape::Diamond4096,
        ] {
            for mode in [
                PerformanceMeasurementMode::Off,
                PerformanceMeasurementMode::Summary,
                PerformanceMeasurementMode::Detailed,
            ] {
                let id = format!("{PREFIX}{}.{}", shape.as_str(), mode.as_str());
                let observation =
                    benchmark_package_verifier_linear_dag_planning(shape, mode).unwrap();
                validate_baseline_row(&source, &id, shape, mode, &observation).unwrap();
            }
        }
        let drift = source.replacen(
            "\"forward_edge_visits\": 4095",
            "\"forward_edge_visits\": 4094",
            1,
        );
        let observation = benchmark_package_verifier_linear_dag_planning(
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
        )
        .unwrap();
        let missing = source.replacen(
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            "package.verifier.linear_dag_planning.v1.chain4096.missing",
            1,
        );
        assert!(validate_baseline_row(
            &missing,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
        let shard_drift = source.replacen(
            "\"per_worker_bytes\": 343932932",
            "\"per_worker_bytes\": 343932931",
            1,
        );
        assert!(validate_baseline_row(
            &shard_drift,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
        let hash_drift = source.replacen(
            &observation.shard_profile.layer_input_sha256,
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            1,
        );
        assert!(validate_baseline_row(
            &hash_drift,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
        let mut extra = source.clone();
        let scenario_array_end = extra
            .rfind("\n  ],\n  \"update_policy\"")
            .expect("baseline has the closed root suffix");
        extra.insert_str(scenario_array_end, ",\n    {}");
        assert!(validate_baseline_row(
            &extra,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
        let wrong_type = source.replacen("\"module_count\": 4096", "\"module_count\": \"4096\"", 1);
        assert!(validate_baseline_row(
            &wrong_type,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
        let wrong_update_policy =
            source.replacen(BASELINE_UPDATE_POLICY, "Automatic updates are allowed.", 1);
        assert!(validate_baseline_row(
            &wrong_update_policy,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation,
        )
        .is_err());
        assert!(validate_baseline_row(
            &drift,
            "package.verifier.linear_dag_planning.v1.chain4096.off",
            PackageVerifierLinearDagBenchmarkShape::Chain4096,
            PerformanceMeasurementMode::Off,
            &observation
        )
        .is_err());
    }

    #[test]
    fn linear_dag_run_json_is_canonical_and_redacted() {
        let observation = benchmark_package_verifier_linear_dag_planning(
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PerformanceMeasurementMode::Off,
        )
        .unwrap();
        let arguments = Arguments {
            scenario: "package.verifier.linear_dag_planning.v1.wide4096.off".to_owned(),
            baseline: PathBuf::from("testdata/baseline.json"),
            source_identity: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_owned(),
            warmup: 1,
            samples: 7,
        };
        let json = run_json(
            &arguments,
            PackageVerifierLinearDagBenchmarkShape::Wide4096,
            PerformanceMeasurementMode::Off,
            &format!("sha256:{}", "1".repeat(64)),
            &format!("sha256:{}", "2".repeat(64)),
            &LinearDagBuildProvenance {
                source_identity: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                cargo_lock_hash: format!("sha256:{}", "3".repeat(64)),
                harness_source_hash: format!("sha256:{}", "4".repeat(64)),
                production_source_set_hash: format!("sha256:{}", "5".repeat(64)),
                rustc_vv: "rustc 1.90.0\nhost: fixture".to_owned(),
                cargo_profile: "release",
                target: "test-target",
                features: vec!["default", "planning-benchmark"],
                rustflags: "-Ctest".to_owned(),
            },
            &[1, 2, 3, 4, 5, 6, 7],
            (4, 2, 1, 7),
            &observation,
        );
        let document = JsonDocument::parse(&json).unwrap();
        let root = exact_object(
            document.root(),
            &[
                "schema",
                "trusted",
                "proof_evidence",
                "scenario",
                "baseline_hash",
                "source_identity",
                "build_identity_hash",
                "cargo_lock_hash",
                "harness_source_hash",
                "production_source_set_hash",
                "rustc_vv",
                "cargo_profile",
                "target",
                "features",
                "rustflags",
                "profile",
                "warmup",
                "sample_count",
                "samples_ns",
                "elapsed_summary_ns",
                "elapsed_gate",
                "status",
                "observation",
            ],
            "run",
        )
        .unwrap();
        exact_object(
            root[15].value(),
            &["shape", "measurement_mode", "shard_profile"],
            "run.profile",
        )
        .unwrap();
        exact_object(
            root[21].value(),
            &[
                "module_count",
                "edge_count",
                "selected_count",
                "layer_count",
                "critical_path_length",
                "oracle_match",
                "shard_profile",
                "counters",
            ],
            "run.observation",
        )
        .unwrap();
        assert_eq!(json.matches(&shard_profile_json(&observation)).count(), 2);
        assert!(!json.contains("testdata/baseline.json"));
        assert!(!json.contains("environment"));
        assert!(!json.contains("oracle_vector"));
    }

    #[test]
    fn linear_dag_source_identity_is_sha1_only() {
        assert!(valid_source_identity(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        ));
        assert!(valid_source_identity(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-dirty"
        ));
        assert!(!valid_source_identity(&"a".repeat(64)));
    }

    #[test]
    fn linear_dag_inputs_are_fd_bound_bounded_and_no_follow() {
        let directory =
            closed_private_tree::ClosedPrivateDirectory::new("npa-pdg-input-test").unwrap();
        directory
            .create_new_file(Path::new("baseline.json"), b"{}\n")
            .unwrap();
        let input = directory.path().join("baseline.json");
        assert_eq!(read_input(&input, 3, "baseline").unwrap(), b"{}\n");
        assert!(read_input(&input, 2, "baseline").is_err());
        assert!(read_input(
            &directory.path().join("nested/../baseline.json"),
            3,
            "baseline"
        )
        .is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(&input, directory.path().join("linked.json")).unwrap();
            assert!(read_input(&directory.path().join("linked.json"), 3, "baseline").is_err());
        }
    }
}

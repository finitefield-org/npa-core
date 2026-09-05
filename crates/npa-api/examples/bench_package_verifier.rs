//! Explicit, fixture-driven source-free verifier performance harness.

use std::collections::{BTreeMap, BTreeSet};
use std::num::{NonZeroU64, NonZeroUsize};
use std::path::PathBuf;
use std::time::Instant;

const PROCESS_MEMO_IUT_STACK_BYTES: usize = 64 * 1024 * 1024;

use npa_api::{
    performance_measurement_report_json, validate_package_verifier_process_memo_scope_baseline,
    validate_performance_fixture_selection, validate_performance_measurement_baseline,
    verify_package_fast_source_free_with_options,
    verify_package_reference_source_free_with_options, PackageCertificateArtifact,
    PackageVerificationDecodeCacheMode, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PackageVerificationProcessMemoHandle,
    PackageVerificationProcessMemoLimits, PackageVerificationProcessMemoStats,
    PackageVerifierProcessMemoScopeBaselineObservation,
    PackageVerifierProcessMemoScopeStoreObservation, PerformanceFixtureSelection,
    PerformanceMeasurementMode,
};
use npa_cert::Name;
use npa_package::{
    build_package_lock_from_package_root, build_package_lock_graph, format_package_hash,
    package_file_hash, parse_and_validate_manifest_str, parse_package_lock_json,
    PackageLockEntryOrigin, PackagePath,
};
#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;

use closed_private_tree::{read_absolute_regular_file, read_invocation_regular_file};

const MAX_FIXTURE_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;
const MAX_PERFORMANCE_BASELINE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_BENCHMARK_EXECUTABLE_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_PACKAGE_MANIFEST_BYTES: u64 = 8 * 1024 * 1024;
const MAX_PACKAGE_LOCK_BYTES: u64 = 32 * 1024 * 1024;
const MAX_BENCHMARK_CERTIFICATES: usize = 4_096;
const MAX_BENCHMARK_CERTIFICATE_SET_BYTES: u64 = 512 * 1024 * 1024;

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("package-verifier benchmark failed: {error}");
            std::process::ExitCode::from(2)
        }
    }
}

fn run() -> Result<(), String> {
    let args = Args::parse()?;
    if !valid_source_identity(&args.source_identity) {
        return Err(
            "--source-identity must be a lowercase Git object id with optional -dirty suffix"
                .to_owned(),
        );
    }
    if let Some(path) = args.validate_legacy_report.as_deref() {
        let build = process_memo_build_provenance(&args.source_identity)?;
        let source = read_published_legacy_report(path)?;
        return validate_legacy_run_json(&source, &args, &build);
    }
    if let Some(profile) = LinearDagIutProfile::from_id(&args.scenario) {
        return run_linear_dag_iut(&args, profile);
    }
    if let Some(profile) = ProcessMemoScopeProfile::from_id(&args.scenario) {
        if profile.execution.package_token.starts_with("external/") {
            return std::thread::Builder::new()
                .name("npa-process-memo-iut".to_owned())
                .stack_size(PROCESS_MEMO_IUT_STACK_BYTES)
                .spawn(move || run_process_memo_scope(&args, profile))
                .map_err(|error| format!("cannot start process-memo IUT worker: {error}"))?
                .join()
                .map_err(|_| "process-memo IUT worker panicked".to_owned())?;
        }
        return run_process_memo_scope(&args, profile);
    }
    run_legacy(&args)
}

fn read_input(path: &std::path::Path, maximum_bytes: u64, label: &str) -> Result<Vec<u8>, String> {
    read_invocation_regular_file(path, maximum_bytes, label)
        .map_err(|error| format!("{label} is unavailable: {error}"))
}

fn read_utf8_input(
    path: &std::path::Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<String, String> {
    String::from_utf8(read_input(path, maximum_bytes, label)?)
        .map_err(|_| format!("{label} is not UTF-8"))
}

fn current_executable_hash() -> Result<String, String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("current executable path is unavailable: {error}"))?;
    Ok(format_package_hash(&package_file_hash(&read_input(
        &executable,
        MAX_BENCHMARK_EXECUTABLE_BYTES,
        "current executable",
    )?)))
}

fn read_package_artifacts(
    root: &std::path::Path,
    lock: &npa_package::PackageLockManifest,
    label: &str,
) -> Result<BTreeMap<PackagePath, Vec<u8>>, String> {
    if lock.entries.len() > MAX_BENCHMARK_CERTIFICATES {
        return Err(format!(
            "{label} has more than {MAX_BENCHMARK_CERTIFICATES} certificates"
        ));
    }
    let mut total_bytes = 0_u64;
    lock.entries
        .iter()
        .map(|entry| {
            let bytes = read_input(
                &root.join(entry.certificate.as_str()),
                npa_cert::MAX_CERTIFICATE_BYTES as u64,
                &format!("{label} certificate {}", entry.certificate.as_str()),
            )?;
            total_bytes = total_bytes
                .checked_add(
                    u64::try_from(bytes.len())
                        .map_err(|_| format!("{label} certificate byte count does not fit u64"))?,
                )
                .ok_or_else(|| format!("{label} certificate byte total overflowed"))?;
            if total_bytes > MAX_BENCHMARK_CERTIFICATE_SET_BYTES {
                return Err(format!(
                    "{label} certificate bytes exceed {MAX_BENCHMARK_CERTIFICATE_SET_BYTES}"
                ));
            }
            Ok((entry.certificate.clone(), bytes))
        })
        .collect()
}

fn run_legacy(args: &Args) -> Result<(), String> {
    let build = process_memo_build_provenance(&args.source_identity)?;
    let root = args.root.as_ref().ok_or("--root is required")?;
    let baseline_path = args.baseline.as_ref().ok_or("--baseline is required")?;
    let fixture_manifest = read_input(
        &args.fixture_manifest,
        MAX_FIXTURE_MANIFEST_BYTES,
        "fixture manifest",
    )?;
    let fixture_manifest_hash = format_package_hash(&package_file_hash(&fixture_manifest));
    let fixture_manifest_source = std::str::from_utf8(&fixture_manifest)
        .map_err(|_| "fixture manifest is not UTF-8".to_owned())?;
    let package_root = root.to_str().ok_or("package root is not valid UTF-8")?;
    validate_performance_fixture_selection(
        fixture_manifest_source,
        PerformanceFixtureSelection {
            scenario: &args.scenario,
            kind: "warmed-checked-artifact-verifier",
            package_root,
            verifier: &args.mode,
            cache_policy: "disabled",
            warmup: u64::try_from(args.warmup)
                .map_err(|_| "warmup does not fit the fixture schema")?,
            samples: u64::try_from(args.samples)
                .map_err(|_| "sample count does not fit the fixture schema")?,
        },
    )
    .map_err(|error| format!("fixture selection mismatch: {error}"))?;
    let baseline = read_input(
        baseline_path,
        MAX_PERFORMANCE_BASELINE_BYTES,
        "performance baseline",
    )?;
    let baseline_hash = format_package_hash(&package_file_hash(&baseline));
    let baseline_source = std::str::from_utf8(&baseline)
        .map_err(|_| "performance baseline is not UTF-8".to_owned())?;
    let build_identity_hash = current_executable_hash()?;
    let features = build
        .features
        .iter()
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    let manifest_source = read_utf8_input(
        &root.join("npa-package.toml"),
        MAX_PACKAGE_MANIFEST_BYTES,
        "package manifest",
    )?;
    let validated = parse_and_validate_manifest_str(&manifest_source)
        .map_err(|error| format!("package manifest is invalid: {error}"))?;
    let lock_source = read_utf8_input(
        &root.join("generated/package-lock.json"),
        MAX_PACKAGE_LOCK_BYTES,
        "package lock",
    )?;
    let lock = parse_package_lock_json(&lock_source)
        .map_err(|error| format!("package lock is invalid: {error}"))?;
    let artifacts = read_package_artifacts(root, &lock, "legacy package")?;

    for _ in 0..args.warmup {
        run_once(
            &args.mode,
            &validated,
            &lock,
            &artifacts,
            PerformanceMeasurementMode::Off,
        )?;
    }

    let mut samples_ns = Vec::with_capacity(args.samples);
    let mut final_report = None;
    for _ in 0..args.samples {
        let started = Instant::now();
        let report = run_once(&args.mode, &validated, &lock, &artifacts, args.measurements)?;
        samples_ns.push(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
        let measurements = report
            .measurements
            .as_ref()
            .ok_or("enabled legacy run omitted measurements")?;
        validate_performance_measurement_baseline(baseline_source, &args.scenario, measurements)
            .map_err(|error| format!("deterministic measurement baseline mismatch: {error}"))?;
        final_report = report.measurements;
        if report.status.as_str() != "passed" {
            return Err(format!(
                "source-free verification returned status {}",
                report.status.as_str()
            ));
        }
    }
    let measurements = final_report
        .as_ref()
        .map(performance_measurement_report_json)
        .unwrap_or_else(|| "null".to_owned());
    let samples = samples_ns
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let elapsed = elapsed_statistics(&samples_ns);
    let report_json = format!(
        "{{\"schema\":\"npa.performance.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"{}\",\"fixture_manifest_hash\":\"{}\",\"baseline_hash\":\"{}\",\"source_identity\":\"{}\",\"build_identity\":{{\"executable_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"harness_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"target\":\"{}\",\"cargo_profile\":\"{}\",\"features\":[{}],\"rustflags\":\"{}\"}},\"verifier\":\"{}\",\"cache_policy\":\"disabled\",\"warmup\":{},\"sample_count\":{},\"samples_ns\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{}}}",
        json_escape(&args.scenario),
        fixture_manifest_hash,
        baseline_hash,
        json_escape(build.source_identity),
        build_identity_hash,
        build.cargo_lock_hash,
        build.harness_source_hash,
        build.production_source_set_hash,
        json_escape(&build.rustc_vv),
        json_escape(build.target),
        json_escape(build.cargo_profile),
        features,
        json_escape(&build.rustflags),
        args.mode,
        args.warmup,
        args.samples,
        samples,
        elapsed.median,
        elapsed.median_absolute_deviation,
        elapsed.minimum,
        elapsed.maximum,
        measurements,
    );
    validate_legacy_run_json(&report_json, args, &build)?;
    println!("{report_json}");
    Ok(())
}

fn validate_legacy_run_json(
    source: &str,
    args: &Args,
    build: &ProcessMemoBuildProvenance<'_>,
) -> Result<(), String> {
    if has_unquoted_ascii_whitespace(source) {
        return Err("legacy run JSON must use compact canonical whitespace".to_owned());
    }
    let document = npa_api::JsonDocument::parse(source)
        .map_err(|error| format!("legacy run JSON is invalid at {}", error.offset))?;
    let root = document
        .root()
        .object_members()
        .ok_or("legacy run root must be an object")?;
    let expected = [
        "schema",
        "trusted",
        "proof_evidence",
        "scenario",
        "fixture_manifest_hash",
        "baseline_hash",
        "source_identity",
        "build_identity",
        "verifier",
        "cache_policy",
        "warmup",
        "sample_count",
        "samples_ns",
        "elapsed_summary_ns",
        "elapsed_profile",
        "elapsed_gate",
        "status",
        "measurements",
    ];
    if root.iter().map(|member| member.key()).collect::<Vec<_>>() != expected {
        return Err("legacy run root keys/order mismatch".to_owned());
    }
    let field = |index: usize| root[index].value();
    let fixture_manifest_hash = format_package_hash(&package_file_hash(&read_input(
        &args.fixture_manifest,
        MAX_FIXTURE_MANIFEST_BYTES,
        "fixture manifest",
    )?));
    let baseline_path = args.baseline.as_ref().ok_or("--baseline is required")?;
    let baseline_hash = format_package_hash(&package_file_hash(&read_input(
        baseline_path,
        MAX_PERFORMANCE_BASELINE_BYTES,
        "performance baseline",
    )?));
    if field(0).string_value() != Some("npa.performance.run.v0.2")
        || field(1).bool_value() != Some(false)
        || field(2).bool_value() != Some(false)
        || field(3).string_value() != Some(args.scenario.as_str())
        || field(4).string_value() != Some(fixture_manifest_hash.as_str())
        || field(5).string_value() != Some(baseline_hash.as_str())
        || field(6).string_value() != Some(build.source_identity)
        || field(8).string_value() != Some(args.mode.as_str())
        || field(9).string_value() != Some("disabled")
        || field(10).number_raw().and_then(|raw| raw.parse().ok()) != Some(args.warmup)
        || field(11).number_raw().and_then(|raw| raw.parse().ok()) != Some(args.samples)
        || field(15).string_value() != Some("advisory")
        || field(16).string_value() != Some("passed")
    {
        return Err("legacy run root value mismatch".to_owned());
    }
    let identity = field(7)
        .object_members()
        .ok_or("legacy build_identity must be an object")?;
    let identity_keys = [
        "executable_sha256",
        "cargo_lock_sha256",
        "harness_source_sha256",
        "production_source_set_sha256",
        "rustc_vv",
        "target",
        "cargo_profile",
        "features",
        "rustflags",
    ];
    let executable_hash = current_executable_hash()?;
    if identity
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>()
        != identity_keys
        || identity[0].value().string_value() != Some(executable_hash.as_str())
        || identity[1].value().string_value() != Some(build.cargo_lock_hash.as_str())
        || identity[2].value().string_value() != Some(build.harness_source_hash.as_str())
        || identity[3].value().string_value() != Some(build.production_source_set_hash.as_str())
        || identity[4].value().string_value() != Some(build.rustc_vv.as_str())
        || identity[5].value().string_value() != Some(build.target)
        || identity[6].value().string_value() != Some(build.cargo_profile)
        || identity[8].value().string_value() != Some(build.rustflags.as_str())
    {
        return Err("legacy build_identity mismatch".to_owned());
    }
    let features = identity[7]
        .value()
        .array_elements()
        .ok_or("legacy build features must be an array")?;
    if features.len() != build.features.len()
        || features
            .iter()
            .zip(&build.features)
            .any(|(actual, expected)| actual.string_value() != Some(*expected))
    {
        return Err("legacy build features mismatch".to_owned());
    }
    let samples = field(12)
        .array_elements()
        .ok_or("legacy samples_ns must be an array")?;
    let samples = samples
        .iter()
        .map(|sample| {
            sample
                .number_raw()
                .and_then(|raw| raw.parse::<u64>().ok())
                .ok_or_else(|| "legacy samples_ns must contain u64 values".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if samples.len() != args.samples {
        return Err("legacy samples_ns mismatch".to_owned());
    }
    let elapsed = field(13)
        .object_members()
        .ok_or("legacy elapsed summary must be an object")?;
    if elapsed
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>()
        != ["median", "median_absolute_deviation", "minimum", "maximum"]
        || field(14).kind() != npa_api::JsonValueKind::Null
    {
        return Err("legacy elapsed envelope mismatch".to_owned());
    }
    let expected_elapsed = elapsed_statistics(&samples);
    for (index, expected) in [
        expected_elapsed.median,
        expected_elapsed.median_absolute_deviation,
        expected_elapsed.minimum,
        expected_elapsed.maximum,
    ]
    .into_iter()
    .enumerate()
    {
        if elapsed[index]
            .value()
            .number_raw()
            .and_then(|raw| raw.parse::<u64>().ok())
            != Some(expected)
        {
            return Err("legacy elapsed summary does not match samples".to_owned());
        }
    }
    validate_legacy_measurements(field(17), args.measurements.as_str())?;
    Ok(())
}

fn read_published_legacy_report(path: &std::path::Path) -> Result<String, String> {
    let source = String::from_utf8(read_absolute_regular_file(
        path,
        64 * 1024 * 1024,
        "legacy run report",
    )?)
    .map_err(|_| "legacy run report is not UTF-8".to_owned())?;
    let body = source
        .strip_suffix('\n')
        .ok_or("legacy run report must end with exactly one LF")?;
    if body.ends_with(['\n', '\r']) {
        return Err("legacy run report must end with exactly one LF".to_owned());
    }
    Ok(body.to_owned())
}

fn validate_legacy_measurements(
    value: &npa_api::JsonValue<'_>,
    expected_mode: &str,
) -> Result<(), String> {
    let fields = value
        .object_members()
        .ok_or("legacy measurements must be an object")?;
    let keys = [
        "schema",
        "trusted",
        "proof_evidence",
        "mode",
        "input_identity",
        "counters",
        "modules",
        "module_details",
        "declarations",
        "declaration_details",
        "candidates",
        "candidate_details",
        "workers",
        "worker_details",
        "package_sharding",
        "package_layers",
        "package_layer_details",
        "package_shards",
        "package_shard_details",
        "detail_truncated",
        "overflowed",
        "clock",
    ];
    if fields.iter().map(|field| field.key()).collect::<Vec<_>>() != keys
        || fields[0].value().string_value() != Some(npa_api::PERFORMANCE_MEASUREMENTS_SCHEMA)
        || fields[1].value().bool_value() != Some(false)
        || fields[2].value().bool_value() != Some(false)
        || fields[3].value().string_value() != Some(expected_mode)
    {
        return Err("legacy measurements root mismatch".to_owned());
    }
    let input_identity = fields[4]
        .value()
        .string_value()
        .ok_or("legacy measurements input_identity must be a hash")?;
    if !is_sha256(input_identity) {
        return Err("legacy measurements input_identity must be sha256".to_owned());
    }
    let counters = fields[5]
        .value()
        .array_elements()
        .ok_or("legacy measurements counters must be an array")?;
    let mut previous = None;
    for counter in counters {
        let members = counter
            .object_members()
            .ok_or("legacy measurement counter must be an object")?;
        if members.iter().map(|field| field.key()).collect::<Vec<_>>() != ["label", "unit", "value"]
        {
            return Err("legacy measurement counter keys/order mismatch".to_owned());
        }
        let label = members[0]
            .value()
            .string_value()
            .ok_or("legacy measurement label must be a string")?;
        let known = npa_api::PerformanceMeasurementLabel::from_schema_identifier(
            npa_api::PERFORMANCE_MEASUREMENTS_SCHEMA,
            label,
        )
        .ok_or("legacy measurement label is unknown for the current schema")?;
        if previous.is_some_and(|previous| previous >= label) {
            return Err("legacy measurement counters must be strictly ordered".to_owned());
        }
        previous = Some(label);
        if members[1].value().string_value() != Some(known.unit().as_str())
            || members[2]
                .value()
                .number_raw()
                .and_then(|raw| raw.parse::<u64>().ok())
                .is_none()
        {
            return Err("legacy measurement counter unit/value mismatch".to_owned());
        }
    }
    for index in [6, 8, 10, 12, 15, 17] {
        let values = fields[index]
            .value()
            .array_elements()
            .ok_or("legacy measurement detail collection must be an array")?;
        if !values.is_empty() {
            return Err("Summary legacy measurement details must be empty".to_owned());
        }
    }
    for index in [7, 9, 11, 13, 16, 18] {
        let detail = fields[index]
            .value()
            .object_members()
            .ok_or("legacy detail counts must be an object")?;
        if detail.iter().map(|field| field.key()).collect::<Vec<_>>()
            != ["attempted", "retained", "omitted"]
            || detail.iter().any(|field| {
                field
                    .value()
                    .number_raw()
                    .and_then(|raw| raw.parse::<u64>().ok())
                    .is_none()
            })
        {
            return Err("legacy detail counts mismatch".to_owned());
        }
        if detail
            .iter()
            .any(|field| field.value().number_raw() != Some("0"))
        {
            return Err("Summary legacy detail counts must be zero".to_owned());
        }
    }
    validate_legacy_package_sharding(fields[14].value())?;
    if fields[19].value().bool_value().is_none() || fields[20].value().bool_value().is_none() {
        return Err("legacy measurement truncation/overflow flags must be booleans".to_owned());
    }
    let clock = fields[21]
        .value()
        .object_members()
        .ok_or("legacy measurement clock must be an object")?;
    if clock.iter().map(|field| field.key()).collect::<Vec<_>>()
        != ["source", "resolution_ns", "coarse_stage_reads"]
        || clock[0].value().string_value().is_none()
        || clock[1..].iter().any(|field| {
            field
                .value()
                .number_raw()
                .and_then(|raw| raw.parse::<u64>().ok())
                .is_none()
        })
    {
        return Err("legacy measurement clock mismatch".to_owned());
    }
    Ok(())
}

fn validate_legacy_package_sharding(value: &npa_api::JsonValue<'_>) -> Result<(), String> {
    let fields = value
        .object_members()
        .ok_or("legacy package_sharding must be an object")?;
    let keys = [
        "cost_model",
        "memory_model",
        "import_weight",
        "memory_budget_bytes",
        "fixed_worker_bytes",
        "scratch_multiplier",
        "requested_jobs",
        "effective_jobs",
        "reduction_reason",
        "shared_base_context_bytes",
        "prepared_shared_bytes",
        "combined_shared_bytes",
        "per_worker_bytes",
        "term_materialization_bytes_per_worker",
        "avoided_base_context_clone_bytes",
        "estimate_overflowed",
        "critical_path_cost",
        "critical_path_module_count",
        "critical_path_identity",
        "critical_path_checker_elapsed_ns",
        "barrier_elapsed_ns",
    ];
    if fields.iter().map(|field| field.key()).collect::<Vec<_>>() != keys
        || fields[0].value().string_value().is_none()
        || fields[1].value().string_value().is_none()
        || fields[8].value().string_value().is_none()
        || fields[18].value().string_value().is_none()
        || fields[15].value().bool_value().is_none()
    {
        return Err("legacy package_sharding shape mismatch".to_owned());
    }
    for index in [2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 16, 17, 19, 20] {
        if fields[index]
            .value()
            .number_raw()
            .and_then(|raw| raw.parse::<u64>().ok())
            .is_none()
        {
            return Err("legacy package_sharding counter must be u64".to_owned());
        }
    }
    Ok(())
}

fn has_unquoted_ascii_whitespace(source: &str) -> bool {
    let mut quoted = false;
    let mut escaped = false;
    for byte in source.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else if byte == b'"' {
            quoted = true;
        } else if byte.is_ascii_whitespace() {
            return true;
        }
    }
    false
}

fn is_sha256(value: &str) -> bool {
    value.len() == 71
        && value.starts_with("sha256:")
        && value[7..]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn decode_build_hex(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("embedded build metadata has odd hexadecimal length".to_owned());
    }
    let bytes = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok((hex_digit(pair[0])? << 4) | hex_digit(pair[1])?))
        .collect::<Result<Vec<_>, String>>()?;
    String::from_utf8(bytes).map_err(|_| "embedded build metadata is not UTF-8".to_owned())
}

fn hex_digit(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("embedded build metadata contains invalid hexadecimal".to_owned()),
    }
}

fn run_once(
    mode: &str,
    validated: &npa_package::ValidatedPackageManifest,
    lock: &npa_package::PackageLockManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    measurement_mode: PerformanceMeasurementMode,
) -> Result<npa_api::PackageVerificationReport, String> {
    let options = PackageVerificationExecutionOptions {
        jobs: 1,
        selected_modules: None,
        memoization: PackageVerificationMemoMode::Disabled,
        decode_cache: PackageVerificationDecodeCacheMode::Disabled,
        collect_decode_cache_counters: measurement_mode.is_enabled(),
        measurement_mode,
    };
    let report = match mode {
        "fast" => verify_package_fast_source_free_with_options(
            validated,
            lock,
            package_artifacts(artifacts),
            options,
        ),
        "reference" => verify_package_reference_source_free_with_options(
            validated,
            lock,
            package_artifacts(artifacts),
            options,
        ),
        other => return Err(format!("unsupported verifier mode {other}")),
    }
    .map_err(|error| format!("source-free verification failed: {error:?}"))?;
    if report.status.as_str() != "passed" {
        return Err(format!(
            "source-free verification returned status {}",
            report.status.as_str()
        ));
    }
    Ok(report)
}

fn package_artifacts(
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Vec<PackageCertificateArtifact<'_>> {
    artifacts
        .iter()
        .map(|(path, bytes)| PackageCertificateArtifact {
            path: path.clone(),
            bytes: bytes.as_slice(),
        })
        .collect()
}

const PROCESS_MEMO_SCOPE_PREFIX: &str = "package.verifier.process_memo_scope.v1.";
const LINEAR_DAG_IUT_PREFIX: &str = "package.verifier.linear_dag_planning.v1.iut992.empty.j4.";
const IUT_LEAF: &str =
    "Proofs.Ai.Iut.Foundation.ArithmeticGeometry.RationalPrimeAdicLegendreTateJIdentification";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProcessMemoSelection {
    Empty,
    Leaf(&'static str),
    Full,
}

impl ProcessMemoSelection {
    const fn kind(self) -> &'static str {
        match self {
            Self::Empty => "empty",
            Self::Leaf(_) => "leaf",
            Self::Full => "full",
        }
    }

    const fn module(self) -> Option<&'static str> {
        match self {
            Self::Leaf(module) => Some(module),
            Self::Empty | Self::Full => None,
        }
    }

    fn selected_modules(self) -> Option<BTreeSet<Name>> {
        match self {
            Self::Empty => Some(BTreeSet::new()),
            Self::Leaf(module) => Some(BTreeSet::from([Name::from_dotted(module)])),
            Self::Full => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProcessMemoOwner {
    Disabled,
    Warm { max_entries: u64, max_bytes: u64 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PackageVerifierBenchmarkLockInput {
    Checked,
    Reconstructed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LinearDagIutProfile {
    id: &'static str,
    measurement_mode: PerformanceMeasurementMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LinearDagIutIdentity<'a> {
    manifest_hash: &'a str,
    local_modules: u64,
    imported_modules: u64,
    certificate_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LinearDagIutSelectors<'a> {
    fixture_package_root: Option<&'a str>,
    package_lock: Option<&'a str>,
    selection: Option<&'a str>,
    jobs: Option<usize>,
    verifier: &'a str,
    measurements: PerformanceMeasurementMode,
    warmup: usize,
    samples: usize,
}

fn validate_linear_dag_iut_selectors(
    profile: LinearDagIutProfile,
    selectors: LinearDagIutSelectors<'_>,
) -> Result<(), &'static str> {
    if selectors.fixture_package_root != Some("external/npa-project-iut/proofs") {
        return Err("linear-DAG IUT fixture token mismatch");
    }
    if selectors.package_lock != Some("reconstructed") {
        return Err("linear-DAG IUT lock-input mismatch");
    }
    if selectors.selection != Some("empty") {
        return Err("linear-DAG IUT selection mismatch");
    }
    if selectors.jobs != Some(4) {
        return Err("linear-DAG IUT jobs mismatch");
    }
    if selectors.verifier != "fast" {
        return Err("linear-DAG IUT verifier mismatch");
    }
    if selectors.measurements != profile.measurement_mode {
        return Err("linear-DAG IUT measurement-mode mismatch");
    }
    if selectors.warmup != 1 {
        return Err("linear-DAG IUT warmup mismatch");
    }
    if selectors.samples != 7 {
        return Err("linear-DAG IUT sample-count mismatch");
    }
    Ok(())
}

fn validate_linear_dag_iut_identity(
    identity: LinearDagIutIdentity<'_>,
) -> Result<(), &'static str> {
    if identity.manifest_hash
        != "sha256:c8594c27e661f3fa5afb00b0a1039f9519c086741870efc4328860dc92365576"
    {
        return Err("linear-DAG IUT manifest hash mismatch");
    }
    if identity.local_modules != 992 {
        return Err("linear-DAG IUT local-module count mismatch");
    }
    if identity.imported_modules != 6 {
        return Err("linear-DAG IUT imported-module count mismatch");
    }
    if identity.certificate_bytes != 46_772_555 {
        return Err("linear-DAG IUT certificate-byte total mismatch");
    }
    Ok(())
}

const LINEAR_DAG_IUT_PROFILES: &[LinearDagIutProfile] = &[
    LinearDagIutProfile {
        id: "package.verifier.linear_dag_planning.v1.iut992.empty.j4.off",
        measurement_mode: PerformanceMeasurementMode::Off,
    },
    LinearDagIutProfile {
        id: "package.verifier.linear_dag_planning.v1.iut992.empty.j4.summary",
        measurement_mode: PerformanceMeasurementMode::Summary,
    },
    LinearDagIutProfile {
        id: "package.verifier.linear_dag_planning.v1.iut992.empty.j4.detailed",
        measurement_mode: PerformanceMeasurementMode::Detailed,
    },
];

impl LinearDagIutProfile {
    fn from_id(id: &str) -> Option<Self> {
        id.starts_with(LINEAR_DAG_IUT_PREFIX)
            .then(|| {
                LINEAR_DAG_IUT_PROFILES
                    .iter()
                    .copied()
                    .find(|profile| profile.id == id)
            })
            .flatten()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackageVerifierBenchmarkExecutionProfile {
    package_token: &'static str,
    lock_input: PackageVerifierBenchmarkLockInput,
    selection: ProcessMemoSelection,
    jobs: usize,
    measurement_mode: PerformanceMeasurementMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProcessMemoScopeProfile {
    id: &'static str,
    execution: PackageVerifierBenchmarkExecutionProfile,
    memo: ProcessMemoOwner,
    closure_modules: u64,
    closure_bytes: u64,
}

const PROCESS_MEMO_SCOPE_PROFILES: &[ProcessMemoScopeProfile] = &[
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "testdata/package/npa-std",
            lock_input: PackageVerifierBenchmarkLockInput::Checked,
            selection: ProcessMemoSelection::Empty,
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Disabled,
        closure_modules: 0,
        closure_bytes: 0,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.small.leaf.warm.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "testdata/package/npa-std",
            lock_input: PackageVerifierBenchmarkLockInput::Checked,
            selection: ProcessMemoSelection::Leaf("Std.Nat.Basic"),
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 1,
            max_bytes: 655,
        },
        closure_modules: 1,
        closure_bytes: 655,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.small.full.disabled.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "testdata/package/npa-std",
            lock_input: PackageVerifierBenchmarkLockInput::Checked,
            selection: ProcessMemoSelection::Full,
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Disabled,
        closure_modules: 2,
        closure_bytes: 1_106,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.small.full.disabled.j4.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "testdata/package/npa-std",
            lock_input: PackageVerifierBenchmarkLockInput::Checked,
            selection: ProcessMemoSelection::Full,
            jobs: 4,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Disabled,
        closure_modules: 2,
        closure_bytes: 1_106,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.small.full.warm.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "testdata/package/npa-std",
            lock_input: PackageVerifierBenchmarkLockInput::Checked,
            selection: ProcessMemoSelection::Full,
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 2,
            max_bytes: 1_106,
        },
        closure_modules: 2,
        closure_bytes: 1_106,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Empty,
            jobs: 4,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Disabled,
        closure_modules: 0,
        closure_bytes: 0,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.summary",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Empty,
            jobs: 4,
            measurement_mode: PerformanceMeasurementMode::Summary,
        },
        memo: ProcessMemoOwner::Disabled,
        closure_modules: 0,
        closure_bytes: 0,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.leaf.warm.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Leaf(IUT_LEAF),
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 611,
            max_bytes: 33_462_537,
        },
        closure_modules: 611,
        closure_bytes: 33_462_537,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.leaf.warm.j4.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Leaf(IUT_LEAF),
            jobs: 4,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 611,
            max_bytes: 33_462_537,
        },
        closure_modules: 611,
        closure_bytes: 33_462_537,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.full.warm.j1.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Full,
            jobs: 1,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 998,
            max_bytes: 46_772_555,
        },
        closure_modules: 998,
        closure_bytes: 46_772_555,
    },
    ProcessMemoScopeProfile {
        id: "package.verifier.process_memo_scope.v1.iut.full.warm.j4.off",
        execution: PackageVerifierBenchmarkExecutionProfile {
            package_token: "external/npa-project-iut/proofs",
            lock_input: PackageVerifierBenchmarkLockInput::Reconstructed,
            selection: ProcessMemoSelection::Full,
            jobs: 4,
            measurement_mode: PerformanceMeasurementMode::Off,
        },
        memo: ProcessMemoOwner::Warm {
            max_entries: 998,
            max_bytes: 46_772_555,
        },
        closure_modules: 998,
        closure_bytes: 46_772_555,
    },
];

impl ProcessMemoScopeProfile {
    fn from_id(id: &str) -> Option<Self> {
        if !id.starts_with(PROCESS_MEMO_SCOPE_PREFIX) {
            return None;
        }
        PROCESS_MEMO_SCOPE_PROFILES
            .iter()
            .copied()
            .find(|profile| profile.id == id)
    }

    const fn measurement_name(self) -> &'static str {
        match self.execution.measurement_mode {
            PerformanceMeasurementMode::Off => "off",
            PerformanceMeasurementMode::Summary => "summary",
            PerformanceMeasurementMode::Detailed => "detailed",
        }
    }

    const fn memo_name(self) -> &'static str {
        match self.memo {
            ProcessMemoOwner::Disabled => "disabled",
            ProcessMemoOwner::Warm { .. } => "warm",
        }
    }
}

fn run_linear_dag_iut(args: &Args, profile: LinearDagIutProfile) -> Result<(), String> {
    validate_linear_dag_iut_selectors(
        profile,
        LinearDagIutSelectors {
            fixture_package_root: args.fixture_package_root.as_deref(),
            package_lock: args.package_lock.as_deref(),
            selection: args.selection.as_deref(),
            jobs: args.jobs,
            verifier: &args.mode,
            measurements: args.measurements,
            warmup: args.warmup,
            samples: args.samples,
        },
    )
    .map_err(|error| format!("linear-DAG IUT selectors are invalid: {error}"))?;
    let package_root = args.root.as_ref().ok_or("--root is required")?;
    let fixture_package_root = args
        .fixture_package_root
        .as_deref()
        .ok_or("--fixture-package-root is required")?;
    let fixture = read_input(
        &args.fixture_manifest,
        MAX_FIXTURE_MANIFEST_BYTES,
        "fixture manifest",
    )?;
    let fixture_source =
        std::str::from_utf8(&fixture).map_err(|_| "fixture manifest is not UTF-8".to_owned())?;
    validate_performance_fixture_selection(
        fixture_source,
        PerformanceFixtureSelection {
            scenario: profile.id,
            kind: "warmed-checked-artifact-verifier",
            package_root: fixture_package_root,
            verifier: "fast",
            cache_policy: "disabled",
            warmup: 1,
            samples: 7,
        },
    )
    .map_err(|error| format!("linear-DAG IUT fixture selection is invalid: {error}"))?;
    let fixture_manifest_hash = format_package_hash(&package_file_hash(&fixture));
    let baseline = profile.measurement_mode.is_enabled().then(|| {
        read_input(
            args.baseline
                .as_ref()
                .ok_or("--baseline is required for enabled modes")?,
            MAX_PERFORMANCE_BASELINE_BYTES,
            "common baseline",
        )
    });
    let baseline = baseline.transpose()?;
    let baseline_hash = baseline
        .as_ref()
        .map(|bytes| format_package_hash(&package_file_hash(bytes)));
    let baseline_source = baseline
        .as_ref()
        .map(|bytes| {
            std::str::from_utf8(bytes).map_err(|_| "common baseline is not UTF-8".to_owned())
        })
        .transpose()?;
    let manifest_bytes = read_input(
        &package_root.join("npa-package.toml"),
        MAX_PACKAGE_MANIFEST_BYTES,
        "IUT manifest",
    )?;
    let manifest_hash = format_package_hash(&package_file_hash(&manifest_bytes));
    let validated = parse_and_validate_manifest_str(
        std::str::from_utf8(&manifest_bytes).map_err(|_| "IUT manifest is not UTF-8")?,
    )
    .map_err(|error| format!("IUT manifest is invalid: {error}"))?;
    let lock = build_package_lock_from_package_root(
        &validated,
        package_root,
        PackagePath::new("npa-package.toml"),
    )
    .map_err(|error| format!("IUT lock reconstruction failed: {error}"))?;
    let artifacts = read_package_artifacts(package_root, &lock, "linear-DAG IUT")?;
    let local_modules = lock
        .entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
        .count();
    let certificate_bytes = artifacts
        .values()
        .map(|bytes| u64_from_usize(bytes.len()))
        .fold(0u64, u64::saturating_add);
    validate_linear_dag_iut_identity(LinearDagIutIdentity {
        manifest_hash: &manifest_hash,
        local_modules: u64_from_usize(local_modules),
        imported_modules: u64_from_usize(lock.entries.len().saturating_sub(local_modules)),
        certificate_bytes,
    })
    .map_err(|error| format!("linear-DAG IUT identity is non-comparable: {error}"))?;
    let run_once = || {
        verify_package_fast_source_free_with_options(
            &validated,
            &lock,
            package_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 4,
                selected_modules: Some(BTreeSet::new()),
                memoization: PackageVerificationMemoMode::Disabled,
                decode_cache: PackageVerificationDecodeCacheMode::Disabled,
                collect_decode_cache_counters: profile.measurement_mode.is_enabled(),
                measurement_mode: profile.measurement_mode,
            },
        )
        .map_err(|error| format!("linear-DAG IUT verification failed: {error:?}"))
    };
    let warmup = run_once()?;
    if !warmup.modules.is_empty() {
        return Err("linear-DAG IUT warmup returned unexpected modules".to_owned());
    }
    let mut samples_ns = Vec::with_capacity(7);
    let mut final_measurements = None;
    for _ in 0..7 {
        let started = Instant::now();
        let report = run_once()?;
        samples_ns.push(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
        if !report.modules.is_empty() {
            return Err("linear-DAG IUT sample returned unexpected modules".to_owned());
        }
        if let Some(source) = baseline_source {
            let measurements = report
                .measurements
                .as_ref()
                .ok_or("linear-DAG IUT enabled mode omitted measurements")?;
            validate_performance_measurement_baseline(source, profile.id, measurements)
                .map_err(|error| format!("linear-DAG IUT common baseline mismatch: {error}"))?;
        } else if report.measurements.is_some() {
            return Err("linear-DAG IUT off mode returned measurements".to_owned());
        }
        final_measurements = report.measurements;
    }
    let build = process_memo_build_provenance(&args.source_identity)?;
    let build_identity_hash = current_executable_hash()?;
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
    let elapsed = elapsed_statistics(&samples_ns);
    let measurements = final_measurements
        .as_ref()
        .map(performance_measurement_report_json)
        .unwrap_or_else(|| "null".to_owned());
    let baseline_hash = baseline_hash
        .map(|hash| format!("\"{hash}\""))
        .unwrap_or_else(|| "null".to_owned());
    println!(
        "{{\"schema\":\"npa.package_verifier.linear_dag_planning.iut_run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"{}\",\"fixture_manifest_hash\":\"{}\",\"baseline_hash\":{},\"source_identity\":\"{}\",\"build_identity_hash\":\"{}\",\"cargo_lock_hash\":\"{}\",\"harness_source_hash\":\"{}\",\"production_source_set_hash\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"features\":[{}],\"rustflags\":\"{}\",\"verifier\":\"fast\",\"cache_policy\":\"disabled\",\"warmup\":1,\"sample_count\":7,\"samples_ns\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{}}}",
        profile.id,
        fixture_manifest_hash,
        baseline_hash,
        json_escape(build.source_identity),
        build_identity_hash,
        build.cargo_lock_hash,
        build.harness_source_hash,
        build.production_source_set_hash,
        json_escape(&build.rustc_vv),
        json_escape(build.cargo_profile),
        json_escape(build.target),
        features,
        json_escape(&build.rustflags),
        samples,
        elapsed.median,
        elapsed.median_absolute_deviation,
        elapsed.minimum,
        elapsed.maximum,
        measurements,
    );
    Ok(())
}

fn run_process_memo_scope(args: &Args, profile: ProcessMemoScopeProfile) -> Result<(), String> {
    let package_root = if profile.execution.package_token.starts_with("external/") {
        args.memo_scope_iut_root
            .as_ref()
            .ok_or("--memo-scope-iut-root is required for IUT profiles")?
            .clone()
    } else {
        workspace_root().join(profile.execution.package_token)
    };
    let fixture = read_input(
        &args.fixture_manifest,
        MAX_FIXTURE_MANIFEST_BYTES,
        "fixture manifest",
    )?;
    let fixture_source =
        std::str::from_utf8(&fixture).map_err(|_| "fixture manifest is not UTF-8".to_owned())?;
    validate_performance_fixture_selection(
        fixture_source,
        PerformanceFixtureSelection {
            scenario: profile.id,
            kind: "package-verifier-process-memo-scope",
            package_root: profile.execution.package_token,
            verifier: "fast",
            cache_policy: "disabled",
            warmup: 1,
            samples: 7,
        },
    )
    .map_err(|error| format!("process-memo fixture selection is invalid: {error}"))?;
    let fixture_manifest_hash = format_package_hash(&package_file_hash(&fixture));
    let memo_baseline_path = args
        .memo_scope_baseline
        .as_ref()
        .ok_or("--memo-scope-baseline is required")?;
    let memo_baseline = read_input(
        memo_baseline_path,
        MAX_PERFORMANCE_BASELINE_BYTES,
        "memo-scope baseline",
    )?;
    let memo_baseline_source = std::str::from_utf8(&memo_baseline)
        .map_err(|_| "memo-scope baseline is not UTF-8".to_owned())?;
    let memo_scope_baseline_hash = format_package_hash(&package_file_hash(&memo_baseline));
    let common_baseline = if profile.execution.measurement_mode.is_enabled() {
        let path = args
            .baseline
            .as_ref()
            .ok_or("--baseline is required for Summary profiles")?;
        Some(read_input(
            path,
            MAX_PERFORMANCE_BASELINE_BYTES,
            "common baseline",
        )?)
    } else {
        None
    };
    let common_baseline_hash = common_baseline
        .as_ref()
        .map(|source| format_package_hash(&package_file_hash(source)));
    let common_baseline_source = common_baseline
        .as_ref()
        .map(|source| {
            std::str::from_utf8(source).map_err(|_| "common baseline is not UTF-8".to_owned())
        })
        .transpose()?;

    let manifest_source = read_utf8_input(
        &package_root.join("npa-package.toml"),
        MAX_PACKAGE_MANIFEST_BYTES,
        "package manifest",
    )?;
    let validated = parse_and_validate_manifest_str(&manifest_source)
        .map_err(|error| format!("package manifest is invalid: {error}"))?;
    let lock = match profile.execution.lock_input {
        PackageVerifierBenchmarkLockInput::Checked => {
            let lock_source = read_utf8_input(
                &package_root.join("generated/package-lock.json"),
                MAX_PACKAGE_LOCK_BYTES,
                "package lock",
            )?;
            parse_package_lock_json(&lock_source)
                .map_err(|error| format!("package lock is invalid: {error}"))?
        }
        PackageVerifierBenchmarkLockInput::Reconstructed => build_package_lock_from_package_root(
            &validated,
            &package_root,
            PackagePath::new("npa-package.toml"),
        )
        .map_err(|error| format!("package lock reconstruction failed: {error}"))?,
    };
    let artifacts = read_package_artifacts(&package_root, &lock, "process-memo package")?;
    validate_process_memo_fixture_identity(profile.execution.package_token, &lock, &artifacts)?;
    let handle = match profile.memo {
        ProcessMemoOwner::Disabled => None,
        ProcessMemoOwner::Warm {
            max_entries,
            max_bytes,
        } => Some(PackageVerificationProcessMemoHandle::new(
            PackageVerificationProcessMemoLimits {
                max_entries: NonZeroUsize::new(
                    usize::try_from(max_entries)
                        .map_err(|_| "memo entry limit exceeds usize".to_owned())?,
                )
                .ok_or("memo entry limit must be nonzero")?,
                max_weighted_certificate_bytes: NonZeroU64::new(max_bytes)
                    .ok_or("memo byte limit must be nonzero")?,
            },
        )),
    };
    if let Some(handle) = &handle {
        handle
            .clear()
            .map_err(|error| format!("fresh memo handle cannot be cleared: {error:?}"))?;
    }

    let warmup =
        run_process_memo_scope_once(profile, handle.as_ref(), &validated, &lock, &artifacts)?;
    validate_process_memo_scope_identity(profile, &warmup, &lock, &artifacts)?;
    validate_process_memo_warmup(profile, &warmup)?;
    let post_warmup_store = handle
        .as_ref()
        .map(|handle| {
            handle
                .stats()
                .map_err(|error| format!("memo store stats are unavailable: {error:?}"))
        })
        .transpose()?;
    validate_process_memo_post_warmup_store(profile, post_warmup_store)?;

    let mut samples_ns = Vec::with_capacity(7);
    let mut sample_json = Vec::with_capacity(7);
    let mut final_measurements = None;
    for index in 0..7usize {
        let started = Instant::now();
        let report =
            run_process_memo_scope_once(profile, handle.as_ref(), &validated, &lock, &artifacts)?;
        let elapsed_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
        validate_process_memo_scope_identity(profile, &report, &lock, &artifacts)?;
        let store_stats = handle
            .as_ref()
            .map(|handle| {
                handle
                    .stats()
                    .map_err(|error| format!("memo store stats are unavailable: {error:?}"))
            })
            .transpose()?;
        validate_process_memo_measured_sample(profile, index, &report, store_stats)?;
        let baseline_observation =
            process_memo_baseline_observation(profile, &report, post_warmup_store);
        validate_package_verifier_process_memo_scope_baseline(
            memo_baseline_source,
            profile.id,
            baseline_observation,
        )
        .map_err(|error| format!("dedicated memo-scope baseline mismatch: {error}"))?;
        if let Some(common_source) = common_baseline_source {
            let measurements = report
                .measurements
                .as_ref()
                .ok_or("Summary profile omitted common measurements")?;
            validate_performance_measurement_baseline(common_source, profile.id, measurements)
                .map_err(|error| format!("common Summary baseline mismatch: {error}"))?;
        }
        samples_ns.push(elapsed_ns);
        sample_json.push(process_memo_sample_json(
            index,
            elapsed_ns,
            &report,
            store_stats,
        ));
        final_measurements = report.measurements;
    }

    let build = process_memo_build_provenance(&args.source_identity)?;
    let build_identity_hash = current_executable_hash()?;
    let elapsed = elapsed_statistics(&samples_ns);
    let measurements = final_measurements
        .as_ref()
        .map(performance_measurement_report_json);
    println!(
        "{}",
        process_memo_scope_run_json(ProcessMemoScopeRunJson {
            profile,
            fixture_manifest_hash: &fixture_manifest_hash,
            memo_scope_baseline_hash: &memo_scope_baseline_hash,
            common_baseline_hash: common_baseline_hash.as_deref(),
            source_identity: build.source_identity,
            build_identity_hash: &build_identity_hash,
            cargo_lock_hash: &build.cargo_lock_hash,
            harness_source_hash: &build.harness_source_hash,
            production_source_set_hash: &build.production_source_set_hash,
            rustc_vv: &build.rustc_vv,
            cargo_profile: build.cargo_profile,
            target: build.target,
            features: &build.features,
            rustflags: &build.rustflags,
            samples: &sample_json,
            elapsed: &elapsed,
            measurements: measurements.as_deref(),
        })
    );
    Ok(())
}

fn run_process_memo_scope_once(
    profile: ProcessMemoScopeProfile,
    handle: Option<&PackageVerificationProcessMemoHandle>,
    validated: &npa_package::ValidatedPackageManifest,
    lock: &npa_package::PackageLockManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<npa_api::PackageVerificationReport, String> {
    verify_package_fast_source_free_with_options(
        validated,
        lock,
        package_artifacts(artifacts),
        PackageVerificationExecutionOptions {
            jobs: profile.execution.jobs,
            selected_modules: profile.execution.selection.selected_modules(),
            memoization: handle
                .cloned()
                .map(PackageVerificationMemoMode::ProcessLocal)
                .unwrap_or(PackageVerificationMemoMode::Disabled),
            decode_cache: PackageVerificationDecodeCacheMode::Disabled,
            collect_decode_cache_counters: false,
            measurement_mode: profile.execution.measurement_mode,
        },
    )
    .map_err(|error| format!("process-memo verification failed: {error:?}"))
}

fn validate_process_memo_fixture_identity(
    package_token: &str,
    lock: &npa_package::PackageLockManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<(), String> {
    let (
        expected_local_modules,
        expected_execution_modules,
        expected_bytes,
        leaf,
        leaf_modules,
        leaf_bytes,
    ) = match package_token {
        "testdata/package/npa-std" => (2, 2, 1_106, "Std.Nat.Basic", 1, 655),
        "external/npa-project-iut/proofs" => (992, 998, 46_772_555, IUT_LEAF, 611, 33_462_537),
        _ => return Err("unlisted process-memo package token".to_owned()),
    };
    let local_modules = lock
        .entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
        .count();
    require_equal(
        "local-module fixture identity",
        u64_from_usize(local_modules),
        expected_local_modules,
    )?;
    require_equal(
        "execution-module fixture identity",
        u64_from_usize(lock.entries.len()),
        expected_execution_modules,
    )?;
    let total_bytes = lock.entries.iter().try_fold(0_u64, |total, entry| {
        let bytes = artifacts
            .get(&entry.certificate)
            .ok_or_else(|| format!("lock entry {:?} has no artifact", entry.module))?;
        total
            .checked_add(u64_from_usize(bytes.len()))
            .ok_or_else(|| "fixture byte total exceeds u64".to_owned())
    })?;
    require_equal(
        "full certificate-byte fixture identity",
        total_bytes,
        expected_bytes,
    )?;

    let graph = build_package_lock_graph(lock)
        .map_err(|error| format!("fixture lock graph is invalid: {error}"))?;
    let mut entries = lock.entries.iter().collect::<Vec<_>>();
    entries.sort_by(|left, right| left.module.cmp(&right.module));
    let leaf = Name::from_dotted(leaf);
    if !entries.iter().any(|entry| entry.module == leaf) {
        return Err("non-comparable leaf module fixture identity".to_owned());
    }
    let mut closure = BTreeSet::from([leaf]);
    loop {
        let mut changed = false;
        for (entry_index, entry) in entries.iter().enumerate() {
            if !closure.contains(&entry.module) {
                continue;
            }
            for import in &graph.resolved_entry_imports[entry_index] {
                changed |= closure.insert(import.module.clone());
            }
        }
        if !changed {
            break;
        }
    }
    require_equal(
        "leaf-closure module identity",
        u64_from_usize(closure.len()),
        leaf_modules,
    )?;
    let entries_by_module = entries
        .iter()
        .map(|entry| (&entry.module, *entry))
        .collect::<BTreeMap<_, _>>();
    let closure_bytes = closure.iter().try_fold(0_u64, |total, module| {
        let entry = entries_by_module
            .get(module)
            .ok_or_else(|| format!("leaf closure module {module:?} is absent from lock"))?;
        let bytes = artifacts.get(&entry.certificate).ok_or_else(|| {
            format!("leaf closure module {module:?} has no loaded certificate bytes")
        })?;
        total
            .checked_add(u64_from_usize(bytes.len()))
            .ok_or_else(|| "leaf closure byte total exceeds u64".to_owned())
    })?;
    require_equal(
        "leaf-closure certificate-byte identity",
        closure_bytes,
        leaf_bytes,
    )?;
    Ok(())
}

fn validate_process_memo_scope_identity(
    profile: ProcessMemoScopeProfile,
    report: &npa_api::PackageVerificationReport,
    lock: &npa_package::PackageLockManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<(), String> {
    if report.status.as_str() != "passed" {
        return Err(format!(
            "process-memo verification returned status {}",
            report.status.as_str()
        ));
    }
    require_equal(
        "executed module count",
        u64_from_usize(report.modules.len()),
        profile.closure_modules,
    )?;
    let entries = lock
        .entries
        .iter()
        .map(|entry| (&entry.module, entry))
        .collect::<BTreeMap<_, _>>();
    let bytes = report.modules.iter().try_fold(0_u64, |total, module| {
        let entry = entries
            .get(&module.module)
            .ok_or_else(|| format!("report module {:?} is absent from lock", module.module))?;
        let bytes = artifacts
            .get(&entry.certificate)
            .ok_or_else(|| format!("report module {:?} has no artifact", module.module))?;
        Ok::<_, String>(total.saturating_add(u64_from_usize(bytes.len())))
    })?;
    require_equal(
        "executed certificate-byte identity",
        bytes,
        profile.closure_bytes,
    )?;
    Ok(())
}

fn require_equal(label: &str, actual: u64, expected: u64) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "non-comparable {label}: expected {expected}, observed {actual}"
        ))
    }
}

fn validate_process_memo_warmup(
    profile: ProcessMemoScopeProfile,
    report: &npa_api::PackageVerificationReport,
) -> Result<(), String> {
    match profile.memo {
        ProcessMemoOwner::Disabled => {
            if report.memo_counters == Default::default() {
                Ok(())
            } else {
                Err("disabled memo warmup reported memo work".to_owned())
            }
        }
        ProcessMemoOwner::Warm { .. } => {
            for (label, actual, expected) in [
                ("warmup hits", u64_from_usize(report.memo_counters.hits), 0),
                (
                    "warmup misses",
                    u64_from_usize(report.memo_counters.misses),
                    profile.closure_modules,
                ),
                (
                    "warmup insertions",
                    u64_from_usize(report.memo_counters.inserted),
                    profile.closure_modules,
                ),
                (
                    "warmup keys",
                    u64_from_usize(report.memo_counters.keys_built),
                    profile.closure_modules,
                ),
                (
                    "warmup certificate bytes",
                    report.memo_counters.certificate_bytes_hashed,
                    profile.closure_bytes,
                ),
            ] {
                require_equal(label, actual, expected)?;
            }
            Ok(())
        }
    }
}

fn validate_process_memo_post_warmup_store(
    profile: ProcessMemoScopeProfile,
    stats: Option<PackageVerificationProcessMemoStats>,
) -> Result<(), String> {
    match (profile.memo, stats) {
        (ProcessMemoOwner::Disabled, None) => Ok(()),
        (ProcessMemoOwner::Disabled, Some(_)) => {
            Err("disabled memo profile unexpectedly owns store stats".to_owned())
        }
        (ProcessMemoOwner::Warm { .. }, None) => {
            Err("warm memo profile omitted post-warmup store stats".to_owned())
        }
        (ProcessMemoOwner::Warm { .. }, Some(stats)) => {
            for (label, actual, expected) in [
                (
                    "post-warmup retained entries",
                    u64_from_usize(stats.retained_entries),
                    profile.closure_modules,
                ),
                (
                    "post-warmup retained bytes",
                    stats.retained_weighted_certificate_bytes,
                    profile.closure_bytes,
                ),
                ("post-warmup hits", stats.cumulative_hits, 0),
                (
                    "post-warmup misses",
                    stats.cumulative_misses,
                    profile.closure_modules,
                ),
                (
                    "post-warmup insertions",
                    stats.cumulative_inserted,
                    profile.closure_modules,
                ),
            ] {
                require_equal(label, actual, expected)?;
            }
            Ok(())
        }
    }
}

fn validate_process_memo_measured_sample(
    profile: ProcessMemoScopeProfile,
    index: usize,
    report: &npa_api::PackageVerificationReport,
    stats: Option<PackageVerificationProcessMemoStats>,
) -> Result<(), String> {
    match profile.memo {
        ProcessMemoOwner::Disabled => {
            if report.memo_counters != Default::default() || stats.is_some() {
                return Err("disabled memo sample reported store work".to_owned());
            }
        }
        ProcessMemoOwner::Warm { .. } => {
            let expected_hits = (u64_from_usize(index) + 1)
                .checked_mul(profile.closure_modules)
                .ok_or("cumulative memo-hit expectation exceeds u64")?;
            for (label, actual, expected) in [
                (
                    "sample hits",
                    u64_from_usize(report.memo_counters.hits),
                    profile.closure_modules,
                ),
                (
                    "sample misses",
                    u64_from_usize(report.memo_counters.misses),
                    0,
                ),
                (
                    "sample insertions",
                    u64_from_usize(report.memo_counters.inserted),
                    0,
                ),
                (
                    "sample keys",
                    u64_from_usize(report.memo_counters.keys_built),
                    profile.closure_modules,
                ),
                (
                    "sample certificate bytes",
                    report.memo_counters.certificate_bytes_hashed,
                    profile.closure_bytes,
                ),
            ] {
                require_equal(label, actual, expected)?;
            }
            let stats = stats.ok_or("warm memo sample omitted store stats")?;
            require_equal(
                "sample cumulative hits",
                stats.cumulative_hits,
                expected_hits,
            )?;
            require_equal(
                "sample cumulative misses",
                stats.cumulative_misses,
                profile.closure_modules,
            )?;
            require_equal(
                "sample cumulative insertions",
                stats.cumulative_inserted,
                profile.closure_modules,
            )?;
        }
    }
    Ok(())
}

fn process_memo_baseline_observation<'a>(
    profile: ProcessMemoScopeProfile,
    report: &'a npa_api::PackageVerificationReport,
    post_warmup_store: Option<PackageVerificationProcessMemoStats>,
) -> PackageVerifierProcessMemoScopeBaselineObservation<'a> {
    let (max_entries, max_weighted_certificate_bytes) = match profile.memo {
        ProcessMemoOwner::Disabled => (None, None),
        ProcessMemoOwner::Warm {
            max_entries,
            max_bytes,
        } => (Some(max_entries), Some(max_bytes)),
    };
    PackageVerifierProcessMemoScopeBaselineObservation {
        status: report.status.as_str(),
        selection_kind: profile.execution.selection.kind(),
        selected_module: profile.execution.selection.module(),
        closure_module_count: profile.closure_modules,
        closure_certificate_bytes: profile.closure_bytes,
        jobs: u64_from_usize(profile.execution.jobs),
        measurement_mode: profile.measurement_name(),
        memo_mode: profile.memo_name(),
        max_entries,
        max_weighted_certificate_bytes,
        hits: u64_from_usize(report.memo_counters.hits),
        misses: u64_from_usize(report.memo_counters.misses),
        inserted: u64_from_usize(report.memo_counters.inserted),
        keys_built: u64_from_usize(report.memo_counters.keys_built),
        certificate_bytes_hashed: report.memo_counters.certificate_bytes_hashed,
        evicted: u64_from_usize(report.memo_counters.evicted),
        rejected_oversize: u64_from_usize(report.memo_counters.rejected_oversize),
        bypassed_store_unavailable: u64_from_usize(report.memo_counters.bypassed_store_unavailable),
        post_warmup_store: post_warmup_store.map(process_memo_store_observation),
    }
}

fn process_memo_store_observation(
    stats: PackageVerificationProcessMemoStats,
) -> PackageVerifierProcessMemoScopeStoreObservation {
    PackageVerifierProcessMemoScopeStoreObservation {
        retained_entries: u64_from_usize(stats.retained_entries),
        retained_weighted_certificate_bytes: stats.retained_weighted_certificate_bytes,
        cumulative_hits: stats.cumulative_hits,
        cumulative_misses: stats.cumulative_misses,
        cumulative_inserted: stats.cumulative_inserted,
        cumulative_evicted: stats.cumulative_evicted,
        cumulative_rejected_oversize: stats.cumulative_rejected_oversize,
    }
}

fn process_memo_store_json(stats: PackageVerificationProcessMemoStats) -> String {
    format!(
        "{{\"retained_entries\":{},\"retained_weighted_certificate_bytes\":{},\"cumulative_hits\":{},\"cumulative_misses\":{},\"cumulative_inserted\":{},\"cumulative_evicted\":{},\"cumulative_rejected_oversize\":{}}}",
        stats.retained_entries,
        stats.retained_weighted_certificate_bytes,
        stats.cumulative_hits,
        stats.cumulative_misses,
        stats.cumulative_inserted,
        stats.cumulative_evicted,
        stats.cumulative_rejected_oversize,
    )
}

fn process_memo_sample_json(
    index: usize,
    elapsed_ns: u64,
    report: &npa_api::PackageVerificationReport,
    stats: Option<PackageVerificationProcessMemoStats>,
) -> String {
    let counters = report.memo_counters;
    let store = stats
        .map(process_memo_store_json)
        .unwrap_or_else(|| "null".to_owned());
    format!(
        "{{\"index\":{},\"elapsed_ns\":{},\"status\":\"{}\",\"executed_module_count\":{},\"memo_counters\":{{\"hits\":{},\"misses\":{},\"inserted\":{},\"keys_built\":{},\"certificate_bytes_hashed\":{},\"evicted\":{},\"rejected_oversize\":{},\"bypassed_store_unavailable\":{}}},\"store_stats\":{}}}",
        index,
        elapsed_ns,
        report.status.as_str(),
        report.modules.len(),
        counters.hits,
        counters.misses,
        counters.inserted,
        counters.keys_built,
        counters.certificate_bytes_hashed,
        counters.evicted,
        counters.rejected_oversize,
        counters.bypassed_store_unavailable,
        store,
    )
}

struct ProcessMemoScopeRunJson<'a> {
    profile: ProcessMemoScopeProfile,
    fixture_manifest_hash: &'a str,
    memo_scope_baseline_hash: &'a str,
    common_baseline_hash: Option<&'a str>,
    source_identity: &'a str,
    build_identity_hash: &'a str,
    cargo_lock_hash: &'a str,
    harness_source_hash: &'a str,
    production_source_set_hash: &'a str,
    rustc_vv: &'a str,
    cargo_profile: &'a str,
    target: &'a str,
    features: &'a [&'a str],
    rustflags: &'a str,
    samples: &'a [String],
    elapsed: &'a ElapsedStatistics,
    measurements: Option<&'a str>,
}

fn process_memo_scope_run_json(run: ProcessMemoScopeRunJson<'_>) -> String {
    assert_eq!(
        run.samples.len(),
        7,
        "memo-scope run requires seven samples"
    );
    assert_eq!(
        run.common_baseline_hash.is_some(),
        run.measurements.is_some(),
        "memo-scope common baseline and measurements must appear together"
    );
    assert_eq!(
        run.measurements.is_some(),
        run.profile.execution.measurement_mode.is_enabled(),
        "memo-scope measurement payload must match its profile"
    );
    let features = run
        .features
        .iter()
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    let selection_module = run
        .profile
        .execution
        .selection
        .module()
        .map(|module| format!("\"{}\"", json_escape(module)))
        .unwrap_or_else(|| "null".to_owned());
    let (max_entries, max_bytes) = match run.profile.memo {
        ProcessMemoOwner::Disabled => ("null".to_owned(), "null".to_owned()),
        ProcessMemoOwner::Warm {
            max_entries,
            max_bytes,
        } => (max_entries.to_string(), max_bytes.to_string()),
    };
    let common_hash = run
        .common_baseline_hash
        .map(|hash| format!("\"{hash}\""))
        .unwrap_or_else(|| "null".to_owned());
    let measurements = run.measurements.unwrap_or("null");
    format!(
        "{{\"schema\":\"npa.package_verifier.process_memo_scope.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"{}\",\"fixture_manifest_hash\":\"{}\",\"memo_scope_baseline_hash\":\"{}\",\"common_baseline_hash\":{},\"source_identity\":\"{}\",\"build_identity_hash\":\"{}\",\"cargo_lock_hash\":\"{}\",\"harness_source_hash\":\"{}\",\"production_source_set_hash\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"features\":[{}],\"rustflags\":\"{}\",\"verifier\":\"fast\",\"cache_policy\":\"disabled\",\"warmup\":1,\"sample_count\":7,\"profile\":{{\"selection\":{{\"kind\":\"{}\",\"module\":{},\"closure_module_count\":{},\"closure_certificate_bytes\":{}}},\"jobs\":{},\"measurement_mode\":\"{}\",\"memo\":{{\"mode\":\"{}\",\"max_entries\":{},\"max_weighted_certificate_bytes\":{}}}}},\"samples\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{}}}",
        run.profile.id,
        run.fixture_manifest_hash,
        run.memo_scope_baseline_hash,
        common_hash,
        json_escape(run.source_identity),
        run.build_identity_hash,
        run.cargo_lock_hash,
        run.harness_source_hash,
        run.production_source_set_hash,
        json_escape(run.rustc_vv),
        json_escape(run.cargo_profile),
        json_escape(run.target),
        features,
        json_escape(run.rustflags),
        run.profile.execution.selection.kind(),
        selection_module,
        run.profile.closure_modules,
        run.profile.closure_bytes,
        run.profile.execution.jobs,
        run.profile.measurement_name(),
        run.profile.memo_name(),
        max_entries,
        max_bytes,
        run.samples.join(","),
        run.elapsed.median,
        run.elapsed.median_absolute_deviation,
        run.elapsed.minimum,
        run.elapsed.maximum,
        measurements,
    )
}

fn u64_from_usize(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

struct Args {
    root: Option<PathBuf>,
    fixture_package_root: Option<String>,
    package_lock: Option<String>,
    selection: Option<String>,
    jobs: Option<usize>,
    fixture_manifest: PathBuf,
    baseline: Option<PathBuf>,
    memo_scope_baseline: Option<PathBuf>,
    memo_scope_iut_root: Option<PathBuf>,
    source_identity: String,
    mode: String,
    measurements: PerformanceMeasurementMode,
    scenario: String,
    warmup: usize,
    samples: usize,
    validate_legacy_report: Option<PathBuf>,
}

impl Args {
    fn parse() -> Result<Self, String> {
        Self::parse_from(std::env::args().skip(1))
    }

    fn parse_from(args: impl IntoIterator<Item = String>) -> Result<Self, String> {
        let mut root = None;
        let mut fixture_package_root = None;
        let mut package_lock = None;
        let mut selection = None;
        let mut jobs = None;
        let mut fixture_manifest = None;
        let mut baseline = None;
        let mut memo_scope_baseline = None;
        let mut memo_scope_iut_root = None;
        let mut source_identity = None;
        let mut mode = "fast".to_owned();
        let mut measurements = PerformanceMeasurementMode::Summary;
        let mut scenario = "compact-package-fast".to_owned();
        let mut warmup = 1;
        let mut samples = 3;
        let mut validate_legacy_report = None;
        let mut args = args.into_iter();
        let mut seen = BTreeSet::new();
        while let Some(flag) = args.next() {
            if !seen.insert(flag.clone()) {
                return Err(format!("duplicate option {flag}"));
            }
            let value = args
                .next()
                .ok_or_else(|| format!("missing value for {flag}"))?;
            match flag.as_str() {
                "--root" => root = Some(PathBuf::from(value)),
                "--fixture-package-root" => fixture_package_root = Some(value),
                "--package-lock" if value == "reconstructed" => package_lock = Some(value),
                "--selection" if value == "empty" => selection = Some(value),
                "--jobs" => {
                    jobs = Some(
                        value
                            .parse()
                            .map_err(|_| "--jobs must be an integer".to_owned())?,
                    )
                }
                "--fixture-manifest" => fixture_manifest = Some(PathBuf::from(value)),
                "--baseline" => baseline = Some(PathBuf::from(value)),
                "--memo-scope-baseline" => memo_scope_baseline = Some(PathBuf::from(value)),
                "--memo-scope-iut-root" => memo_scope_iut_root = Some(PathBuf::from(value)),
                "--source-identity" => source_identity = Some(value),
                "--mode" if matches!(value.as_str(), "fast" | "reference") => mode = value,
                "--measurements" => {
                    measurements = match value.as_str() {
                        "off" => PerformanceMeasurementMode::Off,
                        "summary" => PerformanceMeasurementMode::Summary,
                        "detailed" => PerformanceMeasurementMode::Detailed,
                        _ => {
                            return Err(
                                "--measurements must be off, summary, or detailed".to_owned()
                            )
                        }
                    }
                }
                "--scenario" => scenario = value,
                "--warmup" => {
                    warmup = value
                        .parse()
                        .map_err(|_| "--warmup must be an integer".to_owned())?
                }
                "--samples" => {
                    samples = value
                        .parse()
                        .map_err(|_| "--samples must be an integer".to_owned())?
                }
                "--validate-legacy-report" => validate_legacy_report = Some(PathBuf::from(value)),
                "--package-lock" => return Err("--package-lock must be reconstructed".to_owned()),
                "--selection" => return Err("--selection must be empty".to_owned()),
                "--mode" => return Err("--mode must be fast or reference".to_owned()),
                _ => return Err(format!("unknown option {flag}")),
            }
        }
        if samples == 0 {
            return Err("--samples must be positive".to_owned());
        }
        let memo_scope = ProcessMemoScopeProfile::from_id(&scenario).is_some();
        let linear_dag_iut = LinearDagIutProfile::from_id(&scenario).is_some();
        if !memo_scope && !linear_dag_iut {
            if !measurements.is_enabled() {
                return Err(
                    "--measurements off cannot run the deterministic performance gate".to_owned(),
                );
            }
            if root.is_none() {
                return Err("--root is required".to_owned());
            }
            if baseline.is_none() {
                return Err("--baseline is required".to_owned());
            }
        }
        if memo_scope {
            if warmup != 1 || samples != 7 {
                return Err("process-memo profiles require --warmup 1 --samples 7".to_owned());
            }
            if memo_scope_baseline.is_none() {
                return Err("--memo-scope-baseline is required".to_owned());
            }
            if ProcessMemoScopeProfile::from_id(&scenario)
                .is_some_and(|profile| profile.execution.package_token.starts_with("external/"))
                && memo_scope_iut_root.is_none()
            {
                return Err("--memo-scope-iut-root is required for IUT profiles".to_owned());
            }
            if ProcessMemoScopeProfile::from_id(&scenario)
                .is_some_and(|profile| profile.execution.measurement_mode.is_enabled())
                && baseline.is_none()
            {
                return Err("--baseline is required for Summary profiles".to_owned());
            }
        }
        if linear_dag_iut
            && LinearDagIutProfile::from_id(&scenario)
                .is_some_and(|profile| profile.measurement_mode.is_enabled())
            && baseline.is_none()
        {
            return Err("--baseline is required for enabled linear-DAG modes".to_owned());
        }
        Ok(Self {
            root,
            fixture_package_root,
            package_lock,
            selection,
            jobs,
            fixture_manifest: fixture_manifest
                .ok_or_else(|| "--fixture-manifest is required".to_owned())?,
            baseline,
            memo_scope_baseline,
            memo_scope_iut_root,
            source_identity: source_identity
                .ok_or_else(|| "--source-identity is required".to_owned())?,
            mode,
            measurements,
            scenario,
            warmup,
            samples,
            validate_legacy_report,
        })
    }
}

struct ElapsedStatistics {
    median: u64,
    median_absolute_deviation: u64,
    minimum: u64,
    maximum: u64,
}

fn elapsed_statistics(samples: &[u64]) -> ElapsedStatistics {
    let median_ns = median(samples);
    let deviations = samples
        .iter()
        .map(|sample| sample.abs_diff(median_ns))
        .collect::<Vec<_>>();
    ElapsedStatistics {
        median: median_ns,
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

fn valid_source_identity(value: &str) -> bool {
    let object_id = value.strip_suffix("-dirty").unwrap_or(value);
    object_id.len() == 40
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

struct ProcessMemoBuildProvenance<'a> {
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

fn process_memo_build_provenance(
    requested_source_identity: &str,
) -> Result<ProcessMemoBuildProvenance<'static>, String> {
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
    runtime_source_set::validate_runtime_source_identity(&workspace_root(), source_identity)?;
    let cargo_lock_hash = format!("sha256:{}", env!("NPA_BUILD_CARGO_LOCK_SHA256"));
    let workspace = workspace_root()
        .canonicalize()
        .map_err(|error| format!("canonicalize workspace: {error}"))?;
    let runtime_lock = read_absolute_regular_file(
        &workspace.join("Cargo.lock"),
        32 * 1024 * 1024,
        "Cargo.lock",
    )?;
    let runtime_lock_hash = format_package_hash(&package_file_hash(&runtime_lock));
    if runtime_lock_hash != cargo_lock_hash {
        return Err(format!(
            "runtime Cargo.lock {runtime_lock_hash} does not match embedded build Cargo.lock {cargo_lock_hash}"
        ));
    }
    let harness_source_hash = format!("sha256:{}", env!("NPA_BUILD_PMEM_SOURCE_SHA256"));
    let runtime_harness = read_absolute_regular_file(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/bench_package_verifier.rs"),
        32 * 1024 * 1024,
        "memo-scope harness source",
    )?;
    let runtime_harness_hash = format_package_hash(&package_file_hash(&runtime_harness));
    if runtime_harness_hash != harness_source_hash {
        return Err(format!(
            "runtime harness {runtime_harness_hash} does not match embedded harness {harness_source_hash}"
        ));
    }
    let production_source_set_hash = validate_production_source_set()?;
    let mut features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .collect::<Vec<_>>();
    features.sort_unstable();
    features.dedup();
    Ok(ProcessMemoBuildProvenance {
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

fn validate_production_source_set() -> Result<String, String> {
    runtime_source_set::validate_runtime_source_set(
        &workspace_root(),
        env!("NPA_BUILD_PACKAGE_VERIFIER_SOURCE_SET_PATHS"),
        b"npa-package-verifier-source-set-v1\0",
        env!("NPA_BUILD_PACKAGE_VERIFIER_SOURCE_SET_SHA256"),
        "package-verifier",
    )
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .map_or_else(
            || PathBuf::from(env!("CARGO_MANIFEST_DIR")),
            std::path::Path::to_path_buf,
        )
}

fn json_escape(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                let _ = write!(&mut output, "\\u{:04x}", u32::from(character));
            }
            character => output.push(character),
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_metadata_decode_and_json_escape_cover_control_bytes_without_panics() {
        assert_eq!(decode_build_hex("6100621f").unwrap(), "a\0b\u{001f}");
        assert!(decode_build_hex("0").is_err());
        assert!(decode_build_hex("gg").is_err());
        assert!(decode_build_hex("ff").is_err());
        let escaped = json_escape("a\0\u{0008}\u{000c}\u{001f}z");
        assert_eq!(escaped, "a\\u0000\\u0008\\u000c\\u001fz");
    }

    fn checked_fixture(path: &str) -> String {
        std::fs::read_to_string(workspace_root().join(path)).expect("checked fixture readable")
    }

    fn small_inputs() -> (
        npa_package::ValidatedPackageManifest,
        npa_package::PackageLockManifest,
        BTreeMap<PackagePath, Vec<u8>>,
    ) {
        let root = workspace_root().join("testdata/package/npa-std");
        let validated = parse_and_validate_manifest_str(
            &std::fs::read_to_string(root.join("npa-package.toml")).unwrap(),
        )
        .unwrap();
        let lock = parse_package_lock_json(
            &std::fs::read_to_string(root.join("generated/package-lock.json")).unwrap(),
        )
        .unwrap();
        let artifacts = lock
            .entries
            .iter()
            .map(|entry| {
                (
                    entry.certificate.clone(),
                    std::fs::read(root.join(entry.certificate.as_str())).unwrap(),
                )
            })
            .collect();
        (validated, lock, artifacts)
    }

    fn owned_args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn legacy_args(fixture: &str) -> Args {
        let root = workspace_root()
            .join("testdata/package/npa-std")
            .to_string_lossy()
            .into_owned();
        let baseline = workspace_root()
            .join("testdata/performance/baselines/measurements.v0.1.json")
            .to_string_lossy()
            .into_owned();
        let source_identity = env!("NPA_BUILD_SOURCE_IDENTITY");
        Args::parse_from(owned_args(&[
            "--root",
            &root,
            "--fixture-manifest",
            fixture,
            "--baseline",
            &baseline,
            "--source-identity",
            source_identity,
            "--scenario",
            "compact-package-fast",
            "--mode",
            "fast",
            "--measurements",
            "summary",
            "--warmup",
            "1",
            "--samples",
            "3",
        ]))
        .unwrap()
    }

    #[test]
    fn legacy_run_v02_is_build_bound_and_strict() {
        if env!("NPA_BUILD_SOURCE_IDENTITY") == "unbound" {
            assert!(process_memo_build_provenance("a").is_err());
        }
        const SOURCE_IDENTITY: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let build = ProcessMemoBuildProvenance {
            source_identity: SOURCE_IDENTITY,
            cargo_lock_hash: format!("sha256:{}", "c".repeat(64)),
            harness_source_hash: format!("sha256:{}", "d".repeat(64)),
            production_source_set_hash: format!("sha256:{}", "e".repeat(64)),
            rustc_vv: "rustc 1.0\nhost: test\n".to_owned(),
            cargo_profile: "test-profile",
            target: "test-target",
            features: vec![],
            rustflags: "-Copt-level=1\u{001f}-Cdebuginfo=0".to_owned(),
        };
        let fixture = workspace_root().join("testdata/performance/fixtures/manifest.v0.1.json");
        let mut args = legacy_args(
            &workspace_root()
                .join("testdata/performance/fixtures/manifest.v0.1.json")
                .to_string_lossy(),
        );
        args.source_identity = SOURCE_IDENTITY.to_owned();
        let fixture_hash =
            format_package_hash(&package_file_hash(&std::fs::read(fixture).unwrap()));
        let baseline_hash = format_package_hash(&package_file_hash(
            &std::fs::read(args.baseline.as_ref().unwrap()).unwrap(),
        ));
        let executable_hash = format_package_hash(&package_file_hash(
            &std::fs::read(std::env::current_exe().unwrap()).unwrap(),
        ));
        let (validated, lock, artifacts) = small_inputs();
        let measurements = run_once(
            "fast",
            &validated,
            &lock,
            &artifacts,
            PerformanceMeasurementMode::Summary,
        )
        .unwrap()
        .measurements
        .as_ref()
        .map(performance_measurement_report_json)
        .unwrap();
        let report = format!(
            "{{\"schema\":\"npa.performance.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"compact-package-fast\",\"fixture_manifest_hash\":\"{}\",\"baseline_hash\":\"{}\",\"source_identity\":\"{}\",\"build_identity\":{{\"executable_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"harness_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"target\":\"{}\",\"cargo_profile\":\"{}\",\"features\":[{}],\"rustflags\":\"{}\"}},\"verifier\":\"fast\",\"cache_policy\":\"disabled\",\"warmup\":1,\"sample_count\":3,\"samples_ns\":[1,2,3],\"elapsed_summary_ns\":{{\"median\":2,\"median_absolute_deviation\":1,\"minimum\":1,\"maximum\":3}},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{measurements}}}",
            fixture_hash,
            baseline_hash,
            build.source_identity,
            executable_hash,
            build.cargo_lock_hash,
            build.harness_source_hash,
            build.production_source_set_hash,
            json_escape(&build.rustc_vv),
            build.target,
            build.cargo_profile,
            build
                .features
                .iter()
                .map(|feature| format!("\"{feature}\""))
                .collect::<Vec<_>>()
                .join(","),
            json_escape(&build.rustflags),
        );
        validate_legacy_run_json(&report, &args, &build).unwrap();
        assert!(report.contains("-Copt-level=1\\u001f-Cdebuginfo=0"));
        for invalid in [
            report.replacen("\"schema\":", "\"unknown\":0,\"schema\":", 1),
            report.replacen(
                &build.cargo_lock_hash,
                &format!("sha256:{}", "0".repeat(64)),
                1,
            ),
            report.replacen(
                &build.production_source_set_hash,
                &format!("sha256:{}", "0".repeat(64)),
                1,
            ),
            report.replacen("\"median\":2", "\"median\":3", 1),
            report.replacen("{\"schema\":", "{ \"schema\":", 1),
            format!("{report}x"),
        ] {
            assert!(validate_legacy_run_json(&invalid, &args, &build).is_err());
        }
        let path = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("npa-legacy-compact-report-{}", std::process::id()));
        std::fs::write(&path, format!("{report}\n")).unwrap();
        assert_eq!(read_published_legacy_report(&path).unwrap(), report);
        std::fs::write(&path, format!("{report}\n\n")).unwrap();
        assert!(read_published_legacy_report(&path).is_err());
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn closed_pmem_and_pdg_invocations_return_controlled_errors() {
        let source_identity = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let missing_fixture = workspace_root().join("testdata/performance/missing-fixture.json");
        let missing_fixture = missing_fixture.to_string_lossy().into_owned();
        let memo_baseline = workspace_root()
            .join("testdata/performance/baselines/package-verifier-process-memo-scope.v0.1.json")
            .to_string_lossy()
            .into_owned();
        let pmem = Args::parse_from(owned_args(&[
            "--scenario",
            "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
            "--fixture-manifest",
            &missing_fixture,
            "--memo-scope-baseline",
            &memo_baseline,
            "--source-identity",
            source_identity,
            "--measurements",
            "off",
            "--warmup",
            "1",
            "--samples",
            "7",
        ]))
        .unwrap();
        let pmem_error = run_process_memo_scope(
            &pmem,
            ProcessMemoScopeProfile::from_id(&pmem.scenario).unwrap(),
        )
        .unwrap_err();
        assert!(pmem_error.starts_with("fixture manifest is unavailable:"));

        let package_root = workspace_root()
            .join("testdata/package/npa-std")
            .to_string_lossy()
            .into_owned();
        let pdg = Args::parse_from(owned_args(&[
            "--scenario",
            "package.verifier.linear_dag_planning.v1.iut992.empty.j4.off",
            "--root",
            &package_root,
            "--fixture-package-root",
            "external/npa-project-iut/proofs",
            "--package-lock",
            "reconstructed",
            "--selection",
            "empty",
            "--jobs",
            "4",
            "--fixture-manifest",
            &missing_fixture,
            "--source-identity",
            source_identity,
            "--mode",
            "fast",
            "--measurements",
            "off",
            "--warmup",
            "1",
            "--samples",
            "7",
        ]))
        .unwrap();
        let pdg_error =
            run_linear_dag_iut(&pdg, LinearDagIutProfile::from_id(&pdg.scenario).unwrap())
                .unwrap_err();
        assert!(pdg_error.starts_with("fixture manifest is unavailable:"));

        for malformed in [
            owned_args(&["--scenario"]),
            owned_args(&[
                "--scenario",
                "compact-package-fast",
                "--scenario",
                "compact-package-fast",
            ]),
            owned_args(&["--jobs", "not-an-integer"]),
            owned_args(&["--unknown", "value"]),
        ] {
            assert!(Args::parse_from(malformed).is_err());
        }
        let sha256_object = "a".repeat(64);
        let wrong_identity = owned_args(&[
            "--root",
            "testdata/package/npa-std",
            "--fixture-manifest",
            "testdata/performance/fixtures/manifest.v0.1.json",
            "--baseline",
            "testdata/performance/baselines/measurements.v0.1.json",
            "--source-identity",
            &sha256_object,
        ]);
        let wrong_identity = Args::parse_from(wrong_identity).unwrap();
        assert!(!valid_source_identity(&wrong_identity.source_identity));
    }

    #[test]
    fn benchmark_controlled_error_subprocess_child() {
        let Some(kind) = std::env::var_os("NPA_BENCH_CONTROLLED_ERROR_CHILD") else {
            return;
        };
        let error = match kind.to_string_lossy().as_ref() {
            "missing" | "malformed" => {
                let fixture = std::env::var("NPA_BENCH_CONTROLLED_ERROR_FIXTURE").unwrap();
                run_legacy(&legacy_args(&fixture)).unwrap_err()
            }
            "verification" => {
                let (validated, lock, mut artifacts) = small_inputs();
                let bytes = artifacts.values_mut().next().unwrap();
                bytes[0] ^= 0xff;
                run_once(
                    "fast",
                    &validated,
                    &lock,
                    &artifacts,
                    PerformanceMeasurementMode::Summary,
                )
                .unwrap_err()
            }
            "fixture-identity" => {
                let (_, lock, artifacts) = small_inputs();
                validate_process_memo_fixture_identity(
                    "external/npa-project-iut/proofs",
                    &lock,
                    &artifacts,
                )
                .unwrap_err()
            }
            "report-identity" => {
                let (validated, lock, artifacts) = small_inputs();
                let profile = ProcessMemoScopeProfile::from_id(
                    "package.verifier.process_memo_scope.v1.small.full.disabled.j1.off",
                )
                .unwrap();
                let mut report =
                    run_process_memo_scope_once(profile, None, &validated, &lock, &artifacts)
                        .unwrap();
                report.modules.pop();
                validate_process_memo_scope_identity(profile, &report, &lock, &artifacts)
                    .unwrap_err()
            }
            "store-identity" => {
                let profile = ProcessMemoScopeProfile::from_id(
                    "package.verifier.process_memo_scope.v1.small.full.warm.j1.off",
                )
                .unwrap();
                validate_process_memo_post_warmup_store(
                    profile,
                    Some(PackageVerificationProcessMemoStats::default()),
                )
                .unwrap_err()
            }
            other => panic!("unknown controlled-error child kind {other}"),
        };
        eprintln!("package-verifier benchmark failed: {error}");
        std::process::exit(2);
    }

    #[test]
    fn benchmark_errors_exit_two_without_panicking() {
        let temp = std::env::temp_dir().join(format!(
            "npa-package-verifier-controlled-error-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&temp).unwrap();
        let missing = temp.join("missing.json");
        let malformed = temp.join("malformed.json");
        std::fs::write(&malformed, b"not-json\n").unwrap();
        for (kind, fixture) in [
            ("missing", missing.as_path()),
            ("malformed", malformed.as_path()),
            ("verification", malformed.as_path()),
            ("fixture-identity", malformed.as_path()),
            ("report-identity", malformed.as_path()),
            ("store-identity", malformed.as_path()),
        ] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "tests::benchmark_controlled_error_subprocess_child",
                    "--nocapture",
                ])
                .env("NPA_BENCH_CONTROLLED_ERROR_CHILD", kind)
                .env("NPA_BENCH_CONTROLLED_ERROR_FIXTURE", fixture)
                .output()
                .unwrap();
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert_eq!(output.status.code(), Some(2), "{kind}: {stderr}");
            assert!(
                stderr.contains("package-verifier benchmark failed:"),
                "{kind}: {stderr}"
            );
            assert!(!stderr.contains("panicked at"), "{kind}: {stderr}");
        }
        std::fs::remove_file(&malformed).unwrap();
        std::fs::remove_dir(&temp).unwrap();
    }

    #[test]
    fn linear_dag_iut_profile_catalog_and_fixture_are_closed() {
        assert_eq!(LINEAR_DAG_IUT_PROFILES.len(), 3);
        let ids = LINEAR_DAG_IUT_PROFILES
            .iter()
            .map(|profile| profile.id)
            .collect::<BTreeSet<_>>();
        assert_eq!(ids.len(), 3);
        let fixture = checked_fixture("testdata/performance/fixtures/manifest.v0.1.json");
        for profile in LINEAR_DAG_IUT_PROFILES {
            assert_eq!(LinearDagIutProfile::from_id(profile.id), Some(*profile));
            validate_performance_fixture_selection(
                &fixture,
                PerformanceFixtureSelection {
                    scenario: profile.id,
                    kind: "warmed-checked-artifact-verifier",
                    package_root: "external/npa-project-iut/proofs",
                    verifier: "fast",
                    cache_policy: "disabled",
                    warmup: 1,
                    samples: 7,
                },
            )
            .unwrap();
        }
        assert!(LinearDagIutProfile::from_id(
            "package.verifier.linear_dag_planning.v1.iut992.empty.j4.unknown"
        )
        .is_none());
    }

    #[test]
    fn linear_dag_iut_profile_is_closed() {
        let profile = LINEAR_DAG_IUT_PROFILES[1];
        let exact = LinearDagIutSelectors {
            fixture_package_root: Some("external/npa-project-iut/proofs"),
            package_lock: Some("reconstructed"),
            selection: Some("empty"),
            jobs: Some(4),
            verifier: "fast",
            measurements: PerformanceMeasurementMode::Summary,
            warmup: 1,
            samples: 7,
        };
        validate_linear_dag_iut_selectors(profile, exact).unwrap();
        for drifted in [
            LinearDagIutSelectors {
                fixture_package_root: Some("external/other/proofs"),
                ..exact
            },
            LinearDagIutSelectors {
                package_lock: None,
                ..exact
            },
            LinearDagIutSelectors {
                selection: None,
                ..exact
            },
            LinearDagIutSelectors {
                jobs: Some(1),
                ..exact
            },
            LinearDagIutSelectors {
                verifier: "reference",
                ..exact
            },
            LinearDagIutSelectors {
                measurements: PerformanceMeasurementMode::Detailed,
                ..exact
            },
            LinearDagIutSelectors { warmup: 0, ..exact },
            LinearDagIutSelectors {
                samples: 3,
                ..exact
            },
        ] {
            assert!(validate_linear_dag_iut_selectors(profile, drifted).is_err());
        }
    }

    #[test]
    fn linear_dag_iut_identity_is_exact_and_redacted() {
        let exact = LinearDagIutIdentity {
            manifest_hash:
                "sha256:c8594c27e661f3fa5afb00b0a1039f9519c086741870efc4328860dc92365576",
            local_modules: 992,
            imported_modules: 6,
            certificate_bytes: 46_772_555,
        };
        validate_linear_dag_iut_identity(exact).unwrap();
        for drifted in [
            LinearDagIutIdentity {
                manifest_hash:
                    "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                ..exact
            },
            LinearDagIutIdentity {
                local_modules: 991,
                ..exact
            },
            LinearDagIutIdentity {
                imported_modules: 5,
                ..exact
            },
            LinearDagIutIdentity {
                certificate_bytes: 46_772_554,
                ..exact
            },
        ] {
            let error = validate_linear_dag_iut_identity(drifted).unwrap_err();
            assert!(error.starts_with("linear-DAG IUT "));
            assert!(!error.contains('/'));
        }
    }

    #[test]
    fn linear_dag_iut_enabled_measurement_baselines_are_exact() {
        let (validated, lock, artifacts) = small_inputs();
        let baseline = checked_fixture("testdata/performance/baselines/measurements.v0.1.json");
        for profile in LINEAR_DAG_IUT_PROFILES
            .iter()
            .filter(|profile| profile.measurement_mode.is_enabled())
        {
            let report = verify_package_fast_source_free_with_options(
                &validated,
                &lock,
                package_artifacts(&artifacts),
                PackageVerificationExecutionOptions {
                    jobs: 4,
                    selected_modules: Some(BTreeSet::new()),
                    memoization: PackageVerificationMemoMode::Disabled,
                    decode_cache: PackageVerificationDecodeCacheMode::Disabled,
                    collect_decode_cache_counters: true,
                    measurement_mode: profile.measurement_mode,
                },
            )
            .unwrap();
            validate_performance_measurement_baseline(
                &baseline,
                profile.id,
                report.measurements.as_ref().unwrap(),
            )
            .unwrap();
        }
    }

    #[test]
    fn linear_dag_benchmark_measurement_modes() {
        linear_dag_iut_profile_catalog_and_fixture_are_closed();
        linear_dag_iut_enabled_measurement_baselines_are_exact();
        assert_eq!(
            LINEAR_DAG_IUT_PROFILES[0].measurement_mode,
            PerformanceMeasurementMode::Off
        );
        assert_eq!(
            LINEAR_DAG_IUT_PROFILES[1].measurement_mode,
            PerformanceMeasurementMode::Summary
        );
        assert_eq!(
            LINEAR_DAG_IUT_PROFILES[2].measurement_mode,
            PerformanceMeasurementMode::Detailed
        );
    }

    #[test]
    fn process_memo_scope_profile_catalog_is_closed() {
        assert_eq!(PROCESS_MEMO_SCOPE_PROFILES.len(), 11);
        let ids = PROCESS_MEMO_SCOPE_PROFILES
            .iter()
            .map(|profile| profile.id)
            .collect::<BTreeSet<_>>();
        assert_eq!(ids.len(), 11);
        assert!(ids
            .iter()
            .all(|id| id.starts_with(PROCESS_MEMO_SCOPE_PREFIX)));
        assert!(
            ProcessMemoScopeProfile::from_id("package.verifier.process_memo_scope.v1.unknown")
                .is_none()
        );
        assert!(ProcessMemoScopeProfile::from_id("compact-package-fast").is_none());
    }

    #[test]
    fn process_memo_scope_iut_uses_fixed_stack_profile() {
        assert_eq!(PROCESS_MEMO_IUT_STACK_BYTES, 64 * 1024 * 1024);
        assert_eq!(
            PROCESS_MEMO_SCOPE_PROFILES
                .iter()
                .filter(|profile| profile.execution.package_token.starts_with("external/"))
                .count(),
            6
        );
    }

    #[test]
    fn process_memo_scope_arguments_bind_exact_fixture() {
        let fixture = checked_fixture("testdata/performance/fixtures/manifest.v0.1.json");
        for profile in PROCESS_MEMO_SCOPE_PROFILES {
            validate_performance_fixture_selection(
                &fixture,
                PerformanceFixtureSelection {
                    scenario: profile.id,
                    kind: "package-verifier-process-memo-scope",
                    package_root: profile.execution.package_token,
                    verifier: "fast",
                    cache_policy: "disabled",
                    warmup: 1,
                    samples: 7,
                },
            )
            .unwrap();
        }
    }

    #[test]
    fn process_memo_scope_runner_applies_exact_options() {
        for profile in PROCESS_MEMO_SCOPE_PROFILES {
            assert!(profile.execution.jobs == 1 || profile.execution.jobs == 4);
            if profile.execution.package_token.starts_with("external/") {
                assert_eq!(
                    profile.execution.lock_input,
                    PackageVerifierBenchmarkLockInput::Reconstructed
                );
            } else {
                assert_eq!(
                    profile.execution.lock_input,
                    PackageVerifierBenchmarkLockInput::Checked
                );
            }
            match profile.execution.selection {
                ProcessMemoSelection::Empty => {
                    assert_eq!(
                        profile.execution.selection.selected_modules(),
                        Some(BTreeSet::new())
                    );
                }
                ProcessMemoSelection::Leaf(module) => assert_eq!(
                    profile.execution.selection.selected_modules(),
                    Some(BTreeSet::from([Name::from_dotted(module)]))
                ),
                ProcessMemoSelection::Full => {
                    assert!(profile.execution.selection.selected_modules().is_none())
                }
            }
        }
    }

    #[test]
    fn process_memo_scope_warmup_and_samples_are_isolated() {
        let profile = ProcessMemoScopeProfile::from_id(
            "package.verifier.process_memo_scope.v1.small.full.warm.j1.off",
        )
        .unwrap();
        let (validated, lock, artifacts) = small_inputs();
        let handle =
            PackageVerificationProcessMemoHandle::new(PackageVerificationProcessMemoLimits {
                max_entries: NonZeroUsize::new(2).unwrap(),
                max_weighted_certificate_bytes: NonZeroU64::new(1_106).unwrap(),
            });
        let warmup =
            run_process_memo_scope_once(profile, Some(&handle), &validated, &lock, &artifacts)
                .unwrap();
        assert_eq!(warmup.memo_counters.misses, 2);
        assert_eq!(warmup.memo_counters.inserted, 2);
        let measured =
            run_process_memo_scope_once(profile, Some(&handle), &validated, &lock, &artifacts)
                .unwrap();
        assert_eq!(measured.memo_counters.hits, 2);
        assert_eq!(measured.memo_counters.misses, 0);
        let distinct = PackageVerificationProcessMemoHandle::new(handle.limits());
        let isolated =
            run_process_memo_scope_once(profile, Some(&distinct), &validated, &lock, &artifacts)
                .unwrap();
        assert_eq!(isolated.memo_counters.hits, 0);
        assert_eq!(isolated.memo_counters.misses, 2);
    }

    #[test]
    fn process_memo_scope_run_json_is_closed_and_canonical() {
        const HASH_A: &str =
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        const HASH_B: &str =
            "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        const HASH_C: &str =
            "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
        const SOURCE: &str = "0123456789abcdef0123456789abcdef01234567";

        fn report() -> npa_api::PackageVerificationReport {
            npa_api::PackageVerificationReport {
                mode: npa_api::PackageVerificationMode::FastKernel,
                axiom_policy_hash: npa_package::PackageHash::new([0; 32]),
                verdict_source:
                    npa_api::PackageVerificationVerdictSource::FastKernelCertificateVerifier,
                reference_checker_verdict: false,
                locally_accelerated: false,
                status: npa_api::PackageVerificationStatus::Passed,
                topological_order: Vec::new(),
                modules: Vec::new(),
                memo_counters: Default::default(),
                decode_cache_counters: None,
                measurements: None,
            }
        }

        fn field<'value, 'source>(
            value: &'value npa_api::JsonValue<'source>,
            key: &str,
        ) -> &'value npa_api::JsonValue<'source> {
            value
                .object_members()
                .expect("JSON object")
                .iter()
                .find(|member| member.key() == key)
                .unwrap_or_else(|| panic!("missing JSON field {key}"))
                .value()
        }

        fn assert_keys(value: &npa_api::JsonValue<'_>, expected: &[&str]) {
            assert_eq!(
                value
                    .object_members()
                    .expect("JSON object")
                    .iter()
                    .map(|member| member.key())
                    .collect::<Vec<_>>(),
                expected
            );
        }

        fn assert_envelope(source: &str, measurement_mode: &str, warm: bool) {
            let document = npa_api::JsonDocument::parse(source).expect("canonical run JSON");
            let root = document.root();
            assert_keys(
                root,
                &[
                    "schema",
                    "trusted",
                    "proof_evidence",
                    "scenario",
                    "fixture_manifest_hash",
                    "memo_scope_baseline_hash",
                    "common_baseline_hash",
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
                    "verifier",
                    "cache_policy",
                    "warmup",
                    "sample_count",
                    "profile",
                    "samples",
                    "elapsed_summary_ns",
                    "elapsed_profile",
                    "elapsed_gate",
                    "status",
                    "measurements",
                ],
            );
            assert_eq!(
                field(root, "schema").string_value(),
                Some("npa.package_verifier.process_memo_scope.run.v0.2")
            );
            assert_eq!(field(root, "trusted").bool_value(), Some(false));
            assert_eq!(field(root, "proof_evidence").bool_value(), Some(false));
            assert_eq!(field(root, "warmup").number_raw(), Some("1"));
            assert_eq!(field(root, "sample_count").number_raw(), Some("7"));
            assert_eq!(
                field(root, "elapsed_profile").kind(),
                npa_api::JsonValueKind::Null
            );

            let profile = field(root, "profile");
            assert_keys(profile, &["selection", "jobs", "measurement_mode", "memo"]);
            assert_eq!(
                field(profile, "measurement_mode").string_value(),
                Some(measurement_mode)
            );
            assert_keys(
                field(profile, "selection"),
                &[
                    "kind",
                    "module",
                    "closure_module_count",
                    "closure_certificate_bytes",
                ],
            );
            assert_keys(
                field(profile, "memo"),
                &["mode", "max_entries", "max_weighted_certificate_bytes"],
            );

            let samples = field(root, "samples")
                .array_elements()
                .expect("sample array");
            assert_eq!(samples.len(), 7);
            for (index, sample) in samples.iter().enumerate() {
                assert_keys(
                    sample,
                    &[
                        "index",
                        "elapsed_ns",
                        "status",
                        "executed_module_count",
                        "memo_counters",
                        "store_stats",
                    ],
                );
                assert_eq!(
                    field(sample, "index")
                        .number_raw()
                        .expect("sample index")
                        .parse::<usize>(),
                    Ok(index)
                );
                assert_keys(
                    field(sample, "memo_counters"),
                    &[
                        "hits",
                        "misses",
                        "inserted",
                        "keys_built",
                        "certificate_bytes_hashed",
                        "evicted",
                        "rejected_oversize",
                        "bypassed_store_unavailable",
                    ],
                );
                let store = field(sample, "store_stats");
                if warm {
                    assert_keys(
                        store,
                        &[
                            "retained_entries",
                            "retained_weighted_certificate_bytes",
                            "cumulative_hits",
                            "cumulative_misses",
                            "cumulative_inserted",
                            "cumulative_evicted",
                            "cumulative_rejected_oversize",
                        ],
                    );
                } else {
                    assert_eq!(store.kind(), npa_api::JsonValueKind::Null);
                }
            }
            assert_keys(
                field(root, "elapsed_summary_ns"),
                &["median", "median_absolute_deviation", "minimum", "maximum"],
            );
            if measurement_mode == "off" {
                assert_eq!(
                    field(root, "common_baseline_hash").kind(),
                    npa_api::JsonValueKind::Null
                );
                assert_eq!(
                    field(root, "measurements").kind(),
                    npa_api::JsonValueKind::Null
                );
            } else {
                assert_eq!(
                    field(root, "common_baseline_hash").string_value(),
                    Some(HASH_C)
                );
                let measurements = field(root, "measurements");
                assert_keys(
                    measurements,
                    &[
                        "schema",
                        "trusted",
                        "proof_evidence",
                        "mode",
                        "input_identity",
                        "counters",
                        "modules",
                        "module_details",
                        "declarations",
                        "declaration_details",
                        "candidates",
                        "candidate_details",
                        "workers",
                        "worker_details",
                        "package_sharding",
                        "package_layers",
                        "package_layer_details",
                        "package_shards",
                        "package_shard_details",
                        "detail_truncated",
                        "overflowed",
                        "clock",
                    ],
                );
                assert_eq!(
                    field(measurements, "schema").string_value(),
                    Some("npa.performance.measurements.v0.9")
                );
                assert_eq!(field(measurements, "trusted").bool_value(), Some(false));
                assert_eq!(
                    field(measurements, "proof_evidence").bool_value(),
                    Some(false)
                );
                assert_eq!(field(measurements, "mode").string_value(), Some("summary"));
                let input_identity = field(measurements, "input_identity")
                    .string_value()
                    .expect("Summary input identity");
                assert_eq!(input_identity.len(), 71);
                assert!(input_identity.starts_with("sha256:"));
                assert!(input_identity[7..]
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)));
                let counters = field(measurements, "counters")
                    .array_elements()
                    .expect("measurement counters");
                assert_eq!(counters.len(), 47);
                let counter_labels = counters
                    .iter()
                    .map(|counter| {
                        assert_keys(counter, &["label", "unit", "value"]);
                        field(counter, "label").string_value().unwrap()
                    })
                    .collect::<Vec<_>>();
                assert!(counter_labels.windows(2).all(|pair| pair[0] < pair[1]));
                for (label, unit, value) in [
                    ("package.cache_results", "count", "0"),
                    ("package.certificate_bytes", "bytes", "0"),
                    ("package.effective_jobs", "count", "0"),
                    ("package.live_results", "count", "0"),
                    ("package.memo_results", "count", "0"),
                    ("package.modules_checked", "count", "0"),
                    ("package.requested_jobs", "count", "4"),
                ] {
                    let counter = counters
                        .iter()
                        .find(|counter| field(counter, "label").string_value() == Some(label))
                        .unwrap_or_else(|| panic!("missing Summary counter {label}"));
                    assert_eq!(field(counter, "unit").string_value(), Some(unit));
                    assert_eq!(field(counter, "value").number_raw(), Some(value));
                }
                for array_field in [
                    "modules",
                    "declarations",
                    "candidates",
                    "workers",
                    "package_layers",
                    "package_shards",
                ] {
                    assert!(field(measurements, array_field)
                        .array_elements()
                        .expect("measurement detail array")
                        .is_empty());
                }
                for detail_field in [
                    "module_details",
                    "declaration_details",
                    "candidate_details",
                    "worker_details",
                    "package_layer_details",
                    "package_shard_details",
                ] {
                    assert_keys(
                        field(measurements, detail_field),
                        &["attempted", "retained", "omitted"],
                    );
                }
                assert_eq!(
                    field(measurements, "package_sharding").kind(),
                    npa_api::JsonValueKind::Null
                );
                assert_eq!(
                    field(measurements, "detail_truncated").bool_value(),
                    Some(false)
                );
                assert_eq!(field(measurements, "overflowed").bool_value(), Some(false));
                assert_keys(
                    field(measurements, "clock"),
                    &["source", "resolution_ns", "coarse_stage_reads"],
                );
            }
            for forbidden in [
                "/Users/",
                "/tmp/",
                "memo_key",
                "certificate_payload",
                "environment",
                "acceptance_threshold",
            ] {
                assert!(!source.contains(forbidden), "{forbidden}");
            }
        }

        let elapsed = ElapsedStatistics {
            median: 4,
            median_absolute_deviation: 2,
            minimum: 1,
            maximum: 7,
        };
        let store = PackageVerificationProcessMemoStats {
            retained_entries: 2,
            retained_weighted_certificate_bytes: 1_106,
            cumulative_hits: 14,
            cumulative_misses: 2,
            cumulative_inserted: 2,
            cumulative_evicted: 0,
            cumulative_rejected_oversize: 0,
        };
        let off_samples = (0..7)
            .map(|index| process_memo_sample_json(index, index as u64 + 1, &report(), Some(store)))
            .collect::<Vec<_>>();
        let off_profile = ProcessMemoScopeProfile::from_id(
            "package.verifier.process_memo_scope.v1.small.full.warm.j1.off",
        )
        .unwrap();
        let off = process_memo_scope_run_json(ProcessMemoScopeRunJson {
            profile: off_profile,
            fixture_manifest_hash: HASH_A,
            memo_scope_baseline_hash: HASH_B,
            common_baseline_hash: None,
            source_identity: SOURCE,
            build_identity_hash: HASH_A,
            cargo_lock_hash: HASH_B,
            harness_source_hash: HASH_C,
            production_source_set_hash: HASH_A,
            rustc_vv: "rustc test\nbinary: rustc",
            cargo_profile: "release",
            target: "test-target",
            features: &["alpha", "zeta"],
            rustflags: "-Ctest",
            samples: &off_samples,
            elapsed: &elapsed,
            measurements: None,
        });
        assert_eq!(
            format_package_hash(&package_file_hash(off.as_bytes())),
            "sha256:492fbfffdbe0b0f9addb68b526805fe43b782e848245a4fd67abf930eda150d0"
        );
        assert_envelope(&off, "off", true);
        assert_eq!(
            off,
            process_memo_scope_run_json(ProcessMemoScopeRunJson {
                profile: off_profile,
                fixture_manifest_hash: HASH_A,
                memo_scope_baseline_hash: HASH_B,
                common_baseline_hash: None,
                source_identity: SOURCE,
                build_identity_hash: HASH_A,
                cargo_lock_hash: HASH_B,
                harness_source_hash: HASH_C,
                production_source_set_hash: HASH_A,
                rustc_vv: "rustc test\nbinary: rustc",
                cargo_profile: "release",
                target: "test-target",
                features: &["alpha", "zeta"],
                rustflags: "-Ctest",
                samples: &off_samples,
                elapsed: &elapsed,
                measurements: None,
            })
        );

        let summary_samples = (0..7)
            .map(|index| process_memo_sample_json(index, index as u64 + 1, &report(), None))
            .collect::<Vec<_>>();
        let summary_profile = ProcessMemoScopeProfile::from_id(
            "package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.summary",
        )
        .unwrap();
        let (validated, lock, artifacts) = small_inputs();
        let summary_report =
            run_process_memo_scope_once(summary_profile, None, &validated, &lock, &artifacts)
                .unwrap();
        let summary_measurements = performance_measurement_report_json(
            summary_report
                .measurements
                .as_ref()
                .expect("Summary report has measurements"),
        );
        let summary = process_memo_scope_run_json(ProcessMemoScopeRunJson {
            profile: summary_profile,
            fixture_manifest_hash: HASH_A,
            memo_scope_baseline_hash: HASH_B,
            common_baseline_hash: Some(HASH_C),
            source_identity: SOURCE,
            build_identity_hash: HASH_A,
            cargo_lock_hash: HASH_B,
            harness_source_hash: HASH_C,
            production_source_set_hash: HASH_A,
            rustc_vv: "rustc test\nbinary: rustc",
            cargo_profile: "release",
            target: "test-target",
            features: &[],
            rustflags: "",
            samples: &summary_samples,
            elapsed: &elapsed,
            measurements: Some(&summary_measurements),
        });
        assert_eq!(
            format_package_hash(&package_file_hash(summary.as_bytes())),
            "sha256:5e59313fcd08d340e9b04c8a7e96d30d4d018f6a5f19db78bbe9c65a20e6b82e"
        );
        assert_envelope(&summary, "summary", false);
    }

    fn expected_observation(
        profile: ProcessMemoScopeProfile,
    ) -> PackageVerifierProcessMemoScopeBaselineObservation<'static> {
        let warm = match profile.memo {
            ProcessMemoOwner::Disabled => None,
            ProcessMemoOwner::Warm { .. } => {
                Some(PackageVerifierProcessMemoScopeStoreObservation {
                    retained_entries: profile.closure_modules,
                    retained_weighted_certificate_bytes: profile.closure_bytes,
                    cumulative_hits: 0,
                    cumulative_misses: profile.closure_modules,
                    cumulative_inserted: profile.closure_modules,
                    cumulative_evicted: 0,
                    cumulative_rejected_oversize: 0,
                })
            }
        };
        let (max_entries, max_bytes, hits, keys, bytes) = match profile.memo {
            ProcessMemoOwner::Disabled => (None, None, 0, 0, 0),
            ProcessMemoOwner::Warm {
                max_entries,
                max_bytes,
            } => (
                Some(max_entries),
                Some(max_bytes),
                profile.closure_modules,
                profile.closure_modules,
                profile.closure_bytes,
            ),
        };
        PackageVerifierProcessMemoScopeBaselineObservation {
            status: "passed",
            selection_kind: profile.execution.selection.kind(),
            selected_module: profile.execution.selection.module(),
            closure_module_count: profile.closure_modules,
            closure_certificate_bytes: profile.closure_bytes,
            jobs: u64_from_usize(profile.execution.jobs),
            measurement_mode: profile.measurement_name(),
            memo_mode: profile.memo_name(),
            max_entries,
            max_weighted_certificate_bytes: max_bytes,
            hits,
            misses: 0,
            inserted: 0,
            keys_built: keys,
            certificate_bytes_hashed: bytes,
            evicted: 0,
            rejected_oversize: 0,
            bypassed_store_unavailable: 0,
            post_warmup_store: warm,
        }
    }

    #[test]
    fn performance_process_memo_scope_fixture_catalog_is_strict() {
        process_memo_scope_arguments_bind_exact_fixture();
    }

    #[test]
    fn performance_process_memo_scope_checked_baseline_is_strict() {
        let baseline = checked_fixture(
            "testdata/performance/baselines/package-verifier-process-memo-scope.v0.1.json",
        );
        for profile in PROCESS_MEMO_SCOPE_PROFILES {
            validate_package_verifier_process_memo_scope_baseline(
                &baseline,
                profile.id,
                expected_observation(*profile),
            )
            .unwrap();
        }
        let mismatched = expected_observation(PROCESS_MEMO_SCOPE_PROFILES[0]);
        assert!(validate_package_verifier_process_memo_scope_baseline(
            &baseline,
            "package.verifier.process_memo_scope.v1.missing",
            mismatched,
        )
        .is_err());
    }

    #[test]
    fn performance_process_memo_scope_common_summary_baseline_is_strict() {
        let profile = ProcessMemoScopeProfile::from_id(
            "package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.summary",
        )
        .unwrap();
        let (validated, lock, artifacts) = small_inputs();
        let report =
            run_process_memo_scope_once(profile, None, &validated, &lock, &artifacts).unwrap();
        let baseline = checked_fixture("testdata/performance/baselines/measurements.v0.1.json");
        validate_performance_measurement_baseline(
            &baseline,
            profile.id,
            report.measurements.as_ref().unwrap(),
        )
        .unwrap();
    }
}

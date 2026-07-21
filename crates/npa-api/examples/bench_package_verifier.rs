//! Explicit, fixture-driven source-free verifier performance harness.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

use npa_api::{
    performance_measurement_report_json, validate_performance_fixture_selection,
    validate_performance_measurement_baseline, verify_package_fast_source_free_with_options,
    verify_package_reference_source_free_with_options, PackageCertificateArtifact,
    PackageVerificationDecodeCacheMode, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PerformanceFixtureSelection, PerformanceMeasurementMode,
};
use npa_package::{
    format_package_hash, package_file_hash, parse_and_validate_manifest_str,
    parse_package_lock_json, PackagePath,
};

fn main() {
    let args = Args::parse();
    assert!(
        valid_source_identity(&args.source_identity),
        "--source-identity must be a lowercase Git object id with optional -dirty suffix"
    );
    let fixture_manifest =
        std::fs::read(&args.fixture_manifest).expect("fixture manifest readable");
    let fixture_manifest_hash = format_package_hash(&package_file_hash(&fixture_manifest));
    let fixture_manifest_source =
        std::str::from_utf8(&fixture_manifest).expect("fixture manifest is UTF-8");
    validate_performance_fixture_selection(
        fixture_manifest_source,
        PerformanceFixtureSelection {
            scenario: &args.scenario,
            kind: "warmed-checked-artifact-verifier",
            package_root: args.root.to_str().expect("package root is UTF-8"),
            verifier: &args.mode,
            cache_policy: "disabled",
            warmup: u64::try_from(args.warmup).expect("warmup fits u64"),
            samples: u64::try_from(args.samples).expect("samples fit u64"),
        },
    )
    .expect("fixture selection matches manifest");
    let baseline = std::fs::read(&args.baseline).expect("performance baseline readable");
    let baseline_hash = format_package_hash(&package_file_hash(&baseline));
    let baseline_source = std::str::from_utf8(&baseline).expect("performance baseline is UTF-8");
    let cargo_lock =
        std::fs::read(workspace_root().join("Cargo.lock")).expect("Cargo.lock readable");
    let cargo_lock_hash = format_package_hash(&package_file_hash(&cargo_lock));
    let executable = std::env::current_exe().expect("current executable path available");
    let executable_bytes = std::fs::read(executable).expect("current executable readable");
    let build_identity_hash = format_package_hash(&package_file_hash(&executable_bytes));
    let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"));
    let cargo_profile = env!("NPA_BUILD_CARGO_PROFILE");
    let features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    let manifest_source =
        std::fs::read_to_string(args.root.join("npa-package.toml")).expect("manifest readable");
    let validated = parse_and_validate_manifest_str(&manifest_source).expect("manifest valid");
    let lock_source = std::fs::read_to_string(args.root.join("generated/package-lock.json"))
        .expect("package lock readable");
    let lock = parse_package_lock_json(&lock_source).expect("package lock valid");
    let artifacts: BTreeMap<PackagePath, Vec<u8>> = lock
        .entries
        .iter()
        .map(|entry| {
            (
                entry.certificate.clone(),
                std::fs::read(args.root.join(entry.certificate.as_str()))
                    .expect("certificate readable"),
            )
        })
        .collect();

    for _ in 0..args.warmup {
        run_once(
            &args.mode,
            &validated,
            &lock,
            &artifacts,
            PerformanceMeasurementMode::Off,
        );
    }

    let mut samples_ns = Vec::with_capacity(args.samples);
    let mut final_report = None;
    for _ in 0..args.samples {
        let started = Instant::now();
        let report = run_once(&args.mode, &validated, &lock, &artifacts, args.measurements);
        samples_ns.push(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
        validate_performance_measurement_baseline(
            baseline_source,
            &args.scenario,
            report
                .measurements
                .as_ref()
                .expect("performance gate requires enabled measurements"),
        )
        .expect("deterministic measurement baseline matches");
        final_report = report.measurements;
        assert_eq!(report.status.as_str(), "passed");
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
    println!(
        "{{\"schema\":\"npa.performance.run.v0.1\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"{}\",\"fixture_manifest_hash\":\"{}\",\"baseline_hash\":\"{}\",\"source_identity\":\"{}\",\"build_identity_hash\":\"{}\",\"cargo_lock_hash\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"features\":[{}],\"verifier\":\"{}\",\"cache_policy\":\"disabled\",\"warmup\":{},\"sample_count\":{},\"samples_ns\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":{}}}",
        json_escape(&args.scenario),
        fixture_manifest_hash,
        baseline_hash,
        json_escape(&args.source_identity),
        build_identity_hash,
        cargo_lock_hash,
        json_escape(&rustc_vv),
        json_escape(cargo_profile),
        features,
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
}

fn decode_build_hex(encoded: &str) -> String {
    assert!(
        encoded.len().is_multiple_of(2),
        "build metadata hex is even"
    );
    let bytes = encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_digit(pair[0]) << 4) | hex_digit(pair[1]))
        .collect::<Vec<_>>();
    String::from_utf8(bytes).expect("embedded rustc -Vv metadata is UTF-8")
}

fn hex_digit(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => panic!("build metadata contains invalid hex"),
    }
}

fn run_once(
    mode: &str,
    validated: &npa_package::ValidatedPackageManifest,
    lock: &npa_package::PackageLockManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    measurement_mode: PerformanceMeasurementMode,
) -> npa_api::PackageVerificationReport {
    let options = PackageVerificationExecutionOptions {
        jobs: 1,
        selected_modules: None,
        memoization: PackageVerificationMemoMode::Disabled,
        decode_cache: PackageVerificationDecodeCacheMode::Disabled,
        collect_decode_cache_counters: measurement_mode.is_enabled(),
        measurement_mode,
    };
    match mode {
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
        _ => unreachable!("mode validated by Args::parse"),
    }
    .expect("source-free verification runs")
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

struct Args {
    root: PathBuf,
    fixture_manifest: PathBuf,
    baseline: PathBuf,
    source_identity: String,
    mode: String,
    measurements: PerformanceMeasurementMode,
    scenario: String,
    warmup: usize,
    samples: usize,
}

impl Args {
    fn parse() -> Self {
        let mut root = None;
        let mut fixture_manifest = None;
        let mut baseline = None;
        let mut source_identity = None;
        let mut mode = "fast".to_owned();
        let mut measurements = PerformanceMeasurementMode::Summary;
        let mut scenario = "compact-package-fast".to_owned();
        let mut warmup = 1;
        let mut samples = 3;
        let mut args = std::env::args().skip(1);
        while let Some(flag) = args.next() {
            let value = args
                .next()
                .unwrap_or_else(|| panic!("missing value for {flag}"));
            match flag.as_str() {
                "--root" => root = Some(PathBuf::from(value)),
                "--fixture-manifest" => fixture_manifest = Some(PathBuf::from(value)),
                "--baseline" => baseline = Some(PathBuf::from(value)),
                "--source-identity" => source_identity = Some(value),
                "--mode" if matches!(value.as_str(), "fast" | "reference") => mode = value,
                "--measurements" => {
                    measurements = match value.as_str() {
                        "off" => PerformanceMeasurementMode::Off,
                        "summary" => PerformanceMeasurementMode::Summary,
                        "detailed" => PerformanceMeasurementMode::Detailed,
                        _ => panic!("--measurements must be off, summary, or detailed"),
                    }
                }
                "--scenario" => scenario = value,
                "--warmup" => warmup = value.parse().expect("--warmup is an integer"),
                "--samples" => samples = value.parse().expect("--samples is an integer"),
                "--mode" => panic!("--mode must be fast or reference"),
                _ => panic!("unknown option {flag}"),
            }
        }
        assert!(samples > 0, "--samples must be positive");
        assert!(
            measurements.is_enabled(),
            "--measurements off cannot run the deterministic performance gate"
        );
        Self {
            root: root.expect("--root is required"),
            fixture_manifest: fixture_manifest.expect("--fixture-manifest is required"),
            baseline: baseline.expect("--baseline is required"),
            source_identity: source_identity.expect("--source-identity is required"),
            mode,
            measurements,
            scenario,
            warmup,
            samples,
        }
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
        minimum: samples.iter().copied().min().expect("samples are nonempty"),
        maximum: samples.iter().copied().max().expect("samples are nonempty"),
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
    matches!(object_id.len(), 40 | 64)
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("npa-api crate lives under crates/")
        .to_path_buf()
}

fn json_escape(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

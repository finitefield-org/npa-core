//! Fresh-process rollout harness for targeted `package build-certs --check`.

#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "../../npa-api/examples/support/runtime_source_set.rs"]
mod runtime_source_set;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use npa_api::{
    validate_performance_fixture_selection, JsonDocument, JsonValue, PerformanceFixtureSelection,
};
use npa_cert::{AxiomPolicy, Name, VerifiedModule};
use npa_cli::args::{PackageBuildCheckCacheMode, PackageTimingMode};
use npa_cli::diagnostic::CommandExitCode;
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{build_certs_check, common_options};
use npa_cli::package_build::run_package_build_certs;
use npa_frontend::{
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface,
};
use npa_package::{
    build_package_lock_from_artifacts, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_targeted_authoring_support_context_entry, PackageHash,
    PackageLockArtifact, PackagePath, TargetedAuthoringSupportContextEntry,
};
use sha2::{Digest, Sha256};

use closed_private_tree::{
    read_absolute_regular_tree, read_invocation_regular_file, AttachedExecutable,
    ClosedPrivateDirectory,
};
use runtime_source_set::{validate_runtime_source_identity, validate_runtime_source_set};

const FIXTURE_MANIFEST: &str = "testdata/performance/fixtures/manifest.v0.1.json";
const BASELINE: &str = "testdata/performance/baselines/measurements.v0.1.json";
const WARMUP_COUNT: usize = 1;
const SAMPLE_COUNT: usize = 5;
const TARGET_EDIT: &str = "append-comment-without-support-identity-change";
const TARGET_EDIT_BYTES: &str = "\n-- targeted performance edit\n";
const LOCK_PATH: &str = "generated/package-lock.json";
const MAX_REPORT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_CONTRACT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_SOURCE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_PACKAGE_TREE_ENTRIES: usize = 16_384;
const MAX_PACKAGE_FILE_BYTES: u64 = 128 * 1024 * 1024;
const MAX_PACKAGE_TREE_BYTES: u64 = 512 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FixtureSize {
    Small,
    Large,
}

impl FixtureSize {
    const fn support_count(self) -> usize {
        match self {
            Self::Small => 2,
            Self::Large => 24,
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::Small => "small",
            Self::Large => "large",
        }
    }

    const fn package_root(self) -> &'static str {
        match self {
            Self::Small => "generated/targeted-build-certs-small",
            Self::Large => "generated/targeted-build-certs-large",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CachePolicy {
    Cold,
    Warm,
    PartiallyWarm,
    FullyWarm,
}

impl CachePolicy {
    const fn label(self) -> &'static str {
        match self {
            Self::Cold => "local-hit-cold",
            Self::Warm => "local-hit-warm",
            Self::PartiallyWarm => "local-hit-partially-warm",
            Self::FullyWarm => "local-hit-fully-warm",
        }
    }

    const fn api_mode(self) -> PackageBuildCheckCacheMode {
        PackageBuildCheckCacheMode::LocalHit
    }

    const fn is_warm(self) -> bool {
        !matches!(self, Self::Cold)
    }
}

#[derive(Clone, Copy, Debug)]
struct Scenario {
    id: &'static str,
    size: FixtureSize,
    policy: CachePolicy,
}

const SCENARIOS: [Scenario; 5] = [
    Scenario {
        id: "targeted-build-certs-small-local-hit-cold",
        size: FixtureSize::Small,
        policy: CachePolicy::Cold,
    },
    Scenario {
        id: "targeted-build-certs-small-local-hit-warm",
        size: FixtureSize::Small,
        policy: CachePolicy::Warm,
    },
    Scenario {
        id: "targeted-build-certs-large-local-hit-cold",
        size: FixtureSize::Large,
        policy: CachePolicy::Cold,
    },
    Scenario {
        id: "targeted-build-certs-large-local-hit-partially-warm",
        size: FixtureSize::Large,
        policy: CachePolicy::PartiallyWarm,
    },
    Scenario {
        id: "targeted-build-certs-large-local-hit-fully-warm",
        size: FixtureSize::Large,
        policy: CachePolicy::FullyWarm,
    },
];

#[derive(Clone)]
struct ManifestModule {
    module: Name,
    source: String,
    certificate: String,
    imports: Vec<Name>,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

struct GeneratedFixture {
    root: PathBuf,
    root_relative: PathBuf,
    target: Name,
    support_modules: Vec<Name>,
    target_certificate_path: PathBuf,
    support_identity_hash: String,
    target_source_hash_before_edit: String,
    target_source_hash_after_edit: String,
    target_certificate_hash: String,
    package_snapshot_hash: String,
    tree_files: BTreeSet<PathBuf>,
    tree_directories: BTreeSet<PathBuf>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExpectedCounters {
    values: BTreeMap<String, u64>,
}

#[derive(Clone, Debug)]
struct WorkerReport {
    selection: String,
    cache_summary: String,
    target_certificate_hash: String,
    package_snapshot_hash: String,
    cache_lookup_ms: u64,
    measurements: BTreeMap<String, u64>,
}

#[derive(Clone, Copy, Debug)]
struct ProcessMeasurement {
    wall_ns: u64,
    peak_rss_kib: u64,
}

#[derive(Clone, Copy, Debug)]
struct Statistics {
    median: u64,
    median_absolute_deviation: u64,
    minimum: u64,
    maximum: u64,
}

struct Sample {
    measurement: ProcessMeasurement,
    counters: ExpectedCounters,
    common_measurements: BTreeMap<String, u64>,
    cache_lookup_ms: u64,
    cache_size_bytes: u64,
}

struct ScenarioRun {
    scenario: Scenario,
    samples: Vec<Sample>,
    support_cache_keys: BTreeMap<String, String>,
    executable_hash: String,
    authoring_abis: BTreeMap<String, String>,
    compiler_options: Vec<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("targeted build-certs benchmark failed: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.first().is_some_and(|argument| argument == "--worker") {
        return run_worker(&args[1..]);
    }
    if args.len() == 2 && args[0] == "--validate-report" {
        return validate_rollout_report(Path::new(&args[1]));
    }
    if args != ["--scenario", "all", "--verify"] {
        return Err(
            "usage: targeted_build_certs_bench --scenario all --verify | --validate-report PATH"
                .to_owned(),
        );
    }
    run_rollout()
}

fn validate_rollout_report(path: &Path) -> Result<(), String> {
    let workspace = workspace_root();
    let source_identity = validate_runtime_build_identity(&workspace)?;
    let report = String::from_utf8(read_invocation_regular_file(
        path,
        MAX_REPORT_BYTES,
        "TBAC rollout report",
    )?)
    .map_err(display_error)?;
    if report.contains("/Users/") || report.contains("/private/") {
        return Err("rollout report contains a host-private absolute path".to_owned());
    }
    let fixture_manifest = read_invocation_regular_file(
        &workspace.join(FIXTURE_MANIFEST),
        MAX_CONTRACT_BYTES,
        "TBAC fixture manifest",
    )?;
    let baseline = read_invocation_regular_file(
        &workspace.join(BASELINE),
        MAX_CONTRACT_BYTES,
        "TBAC measurement baseline",
    )?;
    let temp = ClosedPrivateDirectory::new("npa-tbac-report-validation")?;
    let small = generate_fixture(&temp, FixtureSize::Small)?;
    let large = generate_fixture(&temp, FixtureSize::Large)?;
    let executable_source = std::env::current_exe().map_err(display_error)?;
    let executable = temp.create_executable_snapshot(
        Path::new("harness-executable"),
        &executable_source,
        MAX_EXECUTABLE_BYTES,
        "TBAC harness executable",
    )?;
    let small_support_identity = validation_support_store_identity(&executable, &small, &temp)?;
    let large_support_identity = validation_support_store_identity(&executable, &large, &temp)?;
    let executable_hash = format!("sha256:{}", executable.sha256());
    validate_rollout_report_source(
        &report,
        &source_identity,
        &fixture_manifest,
        &baseline,
        &small,
        &large,
        &executable_hash,
        &small_support_identity,
        &large_support_identity,
    )?;
    cleanup_tbac_private_root(&temp, &[&small, &large])?;
    Ok(())
}

fn validation_support_store_identity(
    executable: &AttachedExecutable,
    fixture: &GeneratedFixture,
    temporary_root: &ClosedPrivateDirectory,
) -> Result<SupportStoreIdentity, String> {
    let cache_relative = unique_child(
        temporary_root,
        &format!("validation-{}-support", fixture_support_count(fixture)),
    )?;
    let cache_root = temporary_root.path().join(&cache_relative);
    executable.verify()?;
    let output = Command::new(executable.path())
        .args(worker_args(
            fixture,
            PackageBuildCheckCacheMode::ReadThrough,
            &cache_root,
            std::slice::from_ref(&fixture.target),
        ))
        .output()
        .map_err(display_error)?;
    executable.verify()?;
    if !output.status.success() {
        return Err(format!(
            "validation support population failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    parse_worker_report(&String::from_utf8(output.stdout).map_err(display_error)?)?;
    let entries = support_cache_entries(temporary_root, &cache_relative)?;
    if entries.len() != fixture_support_count(fixture) {
        return Err("validation support population has incomplete coverage".to_owned());
    }
    let identity = support_store_identity(&entries)?;
    cleanup_tbac_cache_root(temporary_root, &cache_relative)?;
    Ok(identity)
}

fn run_rollout() -> Result<(), String> {
    let workspace = workspace_root();
    let source_identity = validate_runtime_build_identity(&workspace)?;
    let fixture_manifest_path = workspace.join(FIXTURE_MANIFEST);
    let baseline_path = workspace.join(BASELINE);
    let fixture_manifest_bytes = read_invocation_regular_file(
        &fixture_manifest_path,
        MAX_CONTRACT_BYTES,
        "TBAC fixture manifest",
    )?;
    let baseline_bytes = read_invocation_regular_file(
        &baseline_path,
        MAX_CONTRACT_BYTES,
        "TBAC measurement baseline",
    )?;
    if hex(&Sha256::digest(&fixture_manifest_bytes))
        != env!("NPA_CLI_BUILD_PERFORMANCE_MANIFEST_V01_SHA256")
        || hex(&Sha256::digest(&baseline_bytes))
            != env!("NPA_CLI_BUILD_PERFORMANCE_BASELINE_SHA256")
    {
        return Err("runtime TBAC fixture or baseline differs from the benchmark build".to_owned());
    }
    let fixture_manifest_source =
        std::str::from_utf8(&fixture_manifest_bytes).map_err(display_error)?;
    let baseline_source = std::str::from_utf8(&baseline_bytes).map_err(display_error)?;
    verify_contract_sources(fixture_manifest_source, baseline_source)?;

    let temp = ClosedPrivateDirectory::new("npa-tbac-run")?;
    let small = generate_fixture(&temp, FixtureSize::Small)?;
    let large = generate_fixture(&temp, FixtureSize::Large)?;
    let executable_source = std::env::current_exe().map_err(display_error)?;
    let executable = temp.create_executable_snapshot(
        Path::new("harness-executable"),
        &executable_source,
        MAX_EXECUTABLE_BYTES,
        "TBAC harness executable",
    )?;
    let executable_hash = format!("sha256:{}", executable.sha256());
    let cargo_lock_hash = env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256").to_owned();
    let harness_source_hash = env!("NPA_CLI_BUILD_TBAC_HARNESS_SOURCE_SHA256").to_owned();
    let production_source_set_hash = env!("NPA_CLI_BUILD_TBAC_SOURCE_SET_SHA256").to_owned();
    let rustc_vv = decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?;
    let cargo_profile = env!("NPA_CLI_BUILD_CARGO_PROFILE");
    let target = env!("NPA_CLI_BUILD_TARGET");
    let rustflags = decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?;
    let features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();

    let mut runs = Vec::with_capacity(SCENARIOS.len());
    for scenario in SCENARIOS {
        let fixture = match scenario.size {
            FixtureSize::Small => &small,
            FixtureSize::Large => &large,
        };
        runs.push(run_scenario(
            &executable,
            fixture,
            scenario,
            baseline_source,
            &temp,
        )?);
    }
    let reference_run = runs
        .first()
        .ok_or_else(|| "rollout matrix recorded no scenarios".to_owned())?;
    for run in &runs {
        if run.executable_hash != executable_hash {
            return Err(format!(
                "{} support executable identity differs from the harness",
                run.scenario.id
            ));
        }
        if run.authoring_abis != reference_run.authoring_abis
            || run.compiler_options != reference_run.compiler_options
        {
            return Err(format!(
                "{} compiler/toolchain identity differs from the rollout matrix",
                run.scenario.id
            ));
        }
    }

    let output = report_json(
        &runs,
        &small,
        &large,
        &fixture_manifest_bytes,
        &baseline_bytes,
        &source_identity,
        &cargo_lock_hash,
        &harness_source_hash,
        &production_source_set_hash,
        &executable_hash,
        &rustc_vv,
        cargo_profile,
        &features,
        target,
        &rustflags,
    )?;
    cleanup_tbac_private_root(&temp, &[&small, &large])?;
    println!("{output}");
    Ok(())
}

fn validate_runtime_build_identity(workspace: &Path) -> Result<String, String> {
    let source_identity = env!("NPA_CLI_BUILD_SOURCE_REVISION");
    if source_identity == "unbound" {
        return Err(
            "targeted build-certs benchmark requires a build bound by NPA_BENCH_SOURCE_IDENTITY"
                .to_owned(),
        );
    }
    validate_runtime_source_identity(workspace, source_identity)?;
    let runtime_lock = read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SOURCE_BYTES,
        "TBAC Cargo.lock",
    )?;
    if hex(&Sha256::digest(&runtime_lock)) != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime Cargo.lock differs from the targeted benchmark build".to_owned());
    }
    let runtime_harness = read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/targeted_build_certs_bench.rs"),
        MAX_SOURCE_BYTES,
        "TBAC harness source",
    )?;
    if hex(&Sha256::digest(&runtime_harness)) != env!("NPA_CLI_BUILD_TBAC_HARNESS_SOURCE_SHA256") {
        return Err("runtime targeted benchmark source differs from the build".to_owned());
    }
    let runtime_source_set = validate_runtime_source_set(
        workspace,
        env!("NPA_CLI_BUILD_TBAC_SOURCE_SET_PATHS"),
        b"npa-tbac-source-set-v1\0",
        env!("NPA_CLI_BUILD_TBAC_SOURCE_SET_SHA256"),
        "TBAC",
    )?;
    let _ = runtime_source_set;
    Ok(source_identity.to_owned())
}

/// Verify the checked-in contract and deterministic fixture generator without recording samples.
pub fn verify_fixture_contract_only() -> Result<(), String> {
    let workspace = workspace_root();
    let fixture = String::from_utf8(read_invocation_regular_file(
        &workspace.join(FIXTURE_MANIFEST),
        MAX_CONTRACT_BYTES,
        "TBAC fixture manifest",
    )?)
    .map_err(display_error)?;
    let baseline = String::from_utf8(read_invocation_regular_file(
        &workspace.join(BASELINE),
        MAX_CONTRACT_BYTES,
        "TBAC measurement baseline",
    )?)
    .map_err(display_error)?;
    verify_contract_sources(&fixture, &baseline)?;
    let temp = ClosedPrivateDirectory::new("npa-tbac-fixture-test")?;
    let mut generated_fixtures = Vec::new();
    for size in [FixtureSize::Small, FixtureSize::Large] {
        let generated = generate_fixture(&temp, size)?;
        if generated.target_source_hash_before_edit == generated.target_source_hash_after_edit {
            return Err(format!(
                "{} target edit did not change source identity",
                size.label()
            ));
        }
        if generated.target_certificate_hash != hash_file(&generated.target_certificate_path)? {
            return Err(format!(
                "{} target certificate identity drifted",
                size.label()
            ));
        }
        generated_fixtures.push(generated);
    }
    cleanup_tbac_private_root(&temp, &generated_fixtures.iter().collect::<Vec<_>>())?;
    Ok(())
}

fn verify_contract_sources(fixture: &str, baseline: &str) -> Result<(), String> {
    for scenario in SCENARIOS {
        validate_performance_fixture_selection(
            fixture,
            PerformanceFixtureSelection {
                scenario: scenario.id,
                kind: "targeted-build-certs",
                package_root: scenario.size.package_root(),
                verifier: "build-certs-check",
                cache_policy: scenario.policy.label(),
                warmup: WARMUP_COUNT as u64,
                samples: SAMPLE_COUNT as u64,
            },
        )
        .map_err(display_error)?;
        let manifest_counts = targeted_fixture_counts(fixture, scenario.id)?;
        if manifest_counts
            != (
                scenario.size.support_count() as u64,
                1,
                TARGET_EDIT.to_owned(),
            )
        {
            return Err(format!("fixture counts/edit disagree for {}", scenario.id));
        }
        let population = targeted_fixture_population(fixture, scenario.id)?;
        if population != expected_population_contract(scenario) {
            return Err(format!(
                "fixture population contract disagrees for {}",
                scenario.id
            ));
        }
        let expected = expected_counters(scenario.size, scenario.policy);
        if baseline_counters(baseline, scenario.id)? != expected.values {
            return Err(format!(
                "deterministic baseline disagrees for {}",
                scenario.id
            ));
        }
    }
    Ok(())
}

fn run_scenario(
    executable: &AttachedExecutable,
    fixture: &GeneratedFixture,
    scenario: Scenario,
    baseline_source: &str,
    temp_root: &ClosedPrivateDirectory,
) -> Result<ScenarioRun, String> {
    let expected = ExpectedCounters {
        values: baseline_counters(baseline_source, scenario.id)?,
    };
    let warmup_relative = unique_child(temp_root, &format!("{}-warmup", scenario.id))?;
    let warmup_root = temp_root.path().join(&warmup_relative);
    let _ = run_one_sample(
        executable,
        fixture,
        scenario.policy,
        temp_root,
        &warmup_relative,
        &warmup_root,
        &expected,
    )?;
    cleanup_tbac_sample_files(temp_root, &warmup_relative)?;

    let mut samples = Vec::with_capacity(SAMPLE_COUNT);
    let mut reference_entries = None;
    for sample_index in 0..SAMPLE_COUNT {
        let cache_relative = unique_child(
            temp_root,
            &format!("{}-sample-{}", scenario.id, sample_index + 1),
        )?;
        let cache_root = temp_root.path().join(&cache_relative);
        let sample = run_one_sample(
            executable,
            fixture,
            scenario.policy,
            temp_root,
            &cache_relative,
            &cache_root,
            &expected,
        )?;
        let entries = support_cache_entries(temp_root, &cache_relative)?;
        if entries.len() != scenario.size.support_count() {
            return Err(format!(
                "{} ended with {} support entries instead of {}",
                scenario.id,
                entries.len(),
                scenario.size.support_count()
            ));
        }
        if let Some(reference) = reference_entries.as_ref() {
            if reference != &entries {
                return Err(format!("support cache identity drifted in {}", scenario.id));
            }
        } else {
            reference_entries = Some(entries);
        }
        samples.push(sample);
        cleanup_tbac_sample_files(temp_root, &cache_relative)?;
    }
    let entries = reference_entries.ok_or_else(|| "scenario recorded no samples".to_owned())?;
    let identity = support_store_identity(&entries)?;
    Ok(ScenarioRun {
        scenario,
        samples,
        support_cache_keys: identity.cache_keys,
        executable_hash: identity.executable_hash,
        authoring_abis: identity.authoring_abis,
        compiler_options: identity.compiler_options,
    })
}

fn run_one_sample(
    executable: &AttachedExecutable,
    fixture: &GeneratedFixture,
    policy: CachePolicy,
    owner: &ClosedPrivateDirectory,
    cache_relative: &Path,
    cache_root: &Path,
    expected: &ExpectedCounters,
) -> Result<Sample, String> {
    if policy.is_warm() {
        let population_targets = population_targets(fixture, policy)?;
        executable.verify()?;
        let population = Command::new(executable.path())
            .args(worker_args(
                fixture,
                PackageBuildCheckCacheMode::ReadThrough,
                cache_root,
                &population_targets,
            ))
            .output()
            .map_err(display_error)?;
        executable.verify()?;
        if !population.status.success() {
            return Err(format!(
                "warm cache population failed: {}",
                String::from_utf8_lossy(&population.stderr)
            ));
        }
        parse_worker_report(&String::from_utf8(population.stdout).map_err(display_error)?)?;
        if policy == CachePolicy::PartiallyWarm {
            let gap = fixture
                .support_modules
                .get(fixture.support_modules.len() / 2)
                .ok_or_else(|| "partial-warm fixture has no midpoint support".to_owned())?;
            remove_support_cache_entry(owner, cache_relative, gap)?;
        }
    }
    validate_population(
        fixture,
        policy,
        &support_cache_entries(owner, cache_relative)?,
    )?;

    let stdout_relative = cache_relative.with_extension("consumer.stdout");
    let stderr_relative = cache_relative.with_extension("consumer.stderr");
    let stdout = owner.create_new_file_handle(&stdout_relative)?;
    let stderr = owner.create_new_file_handle(&stderr_relative)?;
    executable.verify()?;
    let mut command = Command::new(executable.path());
    command
        .args(worker_args(
            fixture,
            policy.api_mode(),
            cache_root,
            std::slice::from_ref(&fixture.target),
        ))
        .stdout(Stdio::from(stdout.try_clone_file().map_err(display_error)?))
        .stderr(Stdio::from(stderr.try_clone_file().map_err(display_error)?));
    let measurement = measure_process(&mut command)?;
    executable.verify()?;
    stdout.sync_all().map_err(display_error)?;
    stderr.sync_all().map_err(display_error)?;
    let worker_stdout =
        String::from_utf8(stdout.read_all_bounded(4 * 1024 * 1024)?).map_err(display_error)?;
    let report = parse_worker_report(&worker_stdout)?;
    if report.selection
        != format!(
            "mode=modules,seeds=1,rebuild=1,support_local={},support_external=0,changed_external=0",
            fixture_support_count(fixture)
        )
    {
        return Err("worker selected a different target closure".to_owned());
    }
    let observed = local_hit_summary_counters(&report.cache_summary)?;
    validate_expected_counters(expected, &observed)?;
    validate_common_measurements(expected, &observed, &report.measurements)?;
    if report.target_certificate_hash != fixture.target_certificate_hash
        || report.package_snapshot_hash != fixture.package_snapshot_hash
    {
        return Err("worker changed or observed different fixture bytes".to_owned());
    }
    Ok(Sample {
        measurement,
        counters: expected.clone(),
        common_measurements: report.measurements,
        cache_lookup_ms: report.cache_lookup_ms,
        cache_size_bytes: directory_file_bytes(owner, cache_relative)?,
    })
}

fn worker_args(
    fixture: &GeneratedFixture,
    mode: PackageBuildCheckCacheMode,
    cache_root: &Path,
    targets: &[Name],
) -> Vec<String> {
    vec![
        "--worker".to_owned(),
        "--package-root".to_owned(),
        fixture.root.display().to_string(),
        "--cache-root".to_owned(),
        cache_root.display().to_string(),
        "--targets".to_owned(),
        targets
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>()
            .join(","),
        "--mode".to_owned(),
        mode.as_str().to_owned(),
    ]
}

fn run_worker(args: &[String]) -> Result<(), String> {
    let parsed = parse_worker_args(args)?;
    let before = package_snapshot_hash(&parsed.package_root)?;
    let target_certificate = target_certificate_path(&parsed.package_root, &parsed.report_target)?;
    let certificate_hash = hash_file(&target_certificate)?;
    let result = run_package_build_certs(
        build_certs_check(common_options(&parsed.package_root, true))
            .with_modules(parsed.targets)
            .with_build_check_cache(parsed.mode)
            .with_build_check_cache_root(parsed.cache_root)
            .with_timings(PackageTimingMode::Summary),
    );
    if result.exit_code() != CommandExitCode::Success || !result.artifacts.is_empty() {
        return Err(result.render_json());
    }
    let selection = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_build_selection")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .ok_or_else(|| "worker did not emit package_build_selection".to_owned())?;
    let cache_summary = result
        .diagnostics
        .iter()
        .find(|diagnostic| {
            matches!(
                diagnostic.reason_code.as_str(),
                "build_check_cache_summary" | "targeted_authoring_cache_summary"
            )
        })
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .unwrap_or("off");
    let timings = result
        .timings
        .as_ref()
        .ok_or_else(|| "worker did not emit summary timings".to_owned())?;
    let cache_lookup_ms = timings
        .metrics
        .iter()
        .find(|metric| metric.field == "cache_lookup_ms")
        .map(|metric| metric.milliseconds)
        .ok_or_else(|| "worker did not emit cache_lookup_ms".to_owned())?;
    let cache_lookup_ms = u64::try_from(cache_lookup_ms).map_err(display_error)?;
    let measurements = timings
        .measurements
        .as_ref()
        .ok_or_else(|| "worker did not emit common measurements".to_owned())?
        .counters
        .iter()
        .filter(|counter| counter.label.as_str().starts_with("cache."))
        .map(|counter| (counter.label.as_str().to_owned(), counter.value))
        .collect::<BTreeMap<_, _>>();
    let after = package_snapshot_hash(&parsed.package_root)?;
    if before != after || certificate_hash != hash_file(&target_certificate)? {
        return Err("check-mode worker changed fixture bytes".to_owned());
    }
    println!(
        "passed\t{selection}\t{cache_summary}\t{certificate_hash}\t{after}\t{cache_lookup_ms}\t{}",
        flat_counters(&measurements)
    );
    Ok(())
}

struct WorkerArgs {
    package_root: PathBuf,
    cache_root: PathBuf,
    targets: Vec<Name>,
    report_target: Name,
    mode: PackageBuildCheckCacheMode,
}

fn parse_worker_args(args: &[String]) -> Result<WorkerArgs, String> {
    if args.len() != 8 {
        return Err("invalid private worker arguments".to_owned());
    }
    let mut fields = BTreeMap::new();
    for pair in args.as_chunks::<2>().0 {
        fields.insert(pair[0].as_str(), pair[1].as_str());
    }
    let package_root = PathBuf::from(required_arg(&fields, "--package-root")?);
    let cache_root = PathBuf::from(required_arg(&fields, "--cache-root")?);
    let targets = required_arg(&fields, "--targets")?
        .split(',')
        .filter(|target| !target.is_empty())
        .map(Name::from_dotted)
        .collect::<Vec<_>>();
    let report_target = targets
        .last()
        .cloned()
        .ok_or_else(|| "private worker target selection is empty".to_owned())?;
    let mode = match required_arg(&fields, "--mode")? {
        "read-through" => PackageBuildCheckCacheMode::ReadThrough,
        "local-hit" => PackageBuildCheckCacheMode::LocalHit,
        _ => return Err("invalid private worker cache mode".to_owned()),
    };
    Ok(WorkerArgs {
        package_root,
        cache_root,
        targets,
        report_target,
        mode,
    })
}

fn required_arg<'a>(fields: &'a BTreeMap<&str, &str>, name: &str) -> Result<&'a str, String> {
    fields
        .get(name)
        .copied()
        .ok_or_else(|| format!("missing private worker argument {name}"))
}

fn parse_worker_report(source: &str) -> Result<WorkerReport, String> {
    let fields = source.trim_end().split('\t').collect::<Vec<_>>();
    if fields.len() != 7 || fields[0] != "passed" {
        return Err("invalid worker report".to_owned());
    }
    Ok(WorkerReport {
        selection: fields[1].to_owned(),
        cache_summary: fields[2].to_owned(),
        target_certificate_hash: fields[3].to_owned(),
        package_snapshot_hash: fields[4].to_owned(),
        cache_lookup_ms: fields[5].parse::<u64>().map_err(display_error)?,
        measurements: parse_flat_counters(fields[6])?,
    })
}

fn measure_process(command: &mut Command) -> Result<ProcessMeasurement, String> {
    let started = Instant::now();
    let child = command.spawn().map_err(display_error)?;
    let pid = i32::try_from(child.id()).map_err(display_error)?;
    let mut status = 0;
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
    let waited = unsafe { libc::wait4(pid, &mut status, 0, usage.as_mut_ptr()) };
    if waited != pid {
        return Err(std::io::Error::last_os_error().to_string());
    }
    let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    let usage = unsafe { usage.assume_init() };
    if !libc::WIFEXITED(status) || libc::WEXITSTATUS(status) != 0 {
        return Err(format!("worker process exited with wait status {status}"));
    }
    let raw_rss = u64::try_from(usage.ru_maxrss).unwrap_or(0);
    #[cfg(target_os = "macos")]
    let peak_rss_kib = raw_rss / 1024;
    #[cfg(not(target_os = "macos"))]
    let peak_rss_kib = raw_rss;
    Ok(ProcessMeasurement {
        wall_ns: elapsed,
        peak_rss_kib,
    })
}

fn generate_fixture(
    owner: &ClosedPrivateDirectory,
    size: FixtureSize,
) -> Result<GeneratedFixture, String> {
    let root_relative = PathBuf::from(format!("fixture-{}", size.label()));
    owner.create_directory(&root_relative)?;
    let root = owner.path().join(&root_relative);
    let prefix = match size {
        FixtureSize::Small => "Small",
        FixtureSize::Large => "Large",
    };
    let mut modules = Vec::new();
    let mut previous_verified: Option<VerifiedModule> = None;
    let mut previous_interface: Option<HumanImportedSourceInterface> = None;
    let mut previous_name: Option<Name> = None;

    for index in 0..size.support_count() {
        let module_name = format!("Fixture.{prefix}.Support{index:02}");
        let theorem_name = format!("support_{index:02}_id");
        let source = if let (Some(import), Some(_)) = (&previous_name, &previous_verified) {
            format!(
                "import {}\n\ntheorem {theorem_name} :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @support_{:02}_id P p\n",
                import.as_dotted(),
                index - 1
            )
        } else {
            format!(
                "theorem {theorem_name} :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n"
            )
        };
        let verified = previous_verified.iter().cloned().collect::<Vec<_>>();
        let interfaces = previous_interface.iter().cloned().collect::<Vec<_>>();
        let (certificate, next_verified, next_interface) = compile_module(
            u32::try_from(index).map_err(display_error)?,
            &module_name,
            &source,
            &verified,
            &interfaces,
        )?;
        let source_path = format!("Fixture/{prefix}/Support{index:02}/source.npa");
        let certificate_path = format!("Fixture/{prefix}/Support{index:02}/certificate.npcert");
        write_artifact(owner, &root_relative, &source_path, source.as_bytes())?;
        write_artifact(owner, &root_relative, &certificate_path, &certificate)?;
        let imports = previous_name.iter().cloned().collect();
        modules.push(manifest_module(
            &module_name,
            &source_path,
            &certificate_path,
            source.as_bytes(),
            &certificate,
            imports,
        )?);
        previous_name = Some(Name::from_dotted(&module_name));
        previous_verified = Some(next_verified);
        previous_interface = Some(next_interface);
    }

    let target_name = format!("Fixture.{prefix}.Target");
    let support_name = previous_name
        .clone()
        .ok_or_else(|| "support is empty".to_owned())?;
    let target_source_before = format!(
        "import {}\n\ntheorem target_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @support_{:02}_id P p\n",
        support_name.as_dotted(),
        size.support_count() - 1
    );
    let target_source_after = format!("{target_source_before}{TARGET_EDIT_BYTES}");
    let verified = vec![previous_verified
        .clone()
        .ok_or_else(|| "support fixture omitted its verified module".to_owned())?];
    let interfaces = vec![previous_interface
        .clone()
        .ok_or_else(|| "support fixture omitted its source interface".to_owned())?];
    let (target_certificate_before, _, _) = compile_module(
        u32::try_from(size.support_count()).map_err(display_error)?,
        &target_name,
        &target_source_before,
        &verified,
        &interfaces,
    )?;
    let (target_certificate_after, _, _) = compile_module(
        u32::try_from(size.support_count()).map_err(display_error)?,
        &target_name,
        &target_source_after,
        &verified,
        &interfaces,
    )?;
    if target_certificate_before != target_certificate_after {
        return Err(format!(
            "{} target comment edit changed canonical certificate bytes",
            size.label()
        ));
    }
    let target_source_path = format!("Fixture/{prefix}/Target/source.npa");
    let target_certificate_relative = format!("Fixture/{prefix}/Target/certificate.npcert");
    write_artifact(
        owner,
        &root_relative,
        &target_source_path,
        target_source_before.as_bytes(),
    )?;
    write_artifact(
        owner,
        &root_relative,
        &target_certificate_relative,
        &target_certificate_before,
    )?;
    let initial_target = manifest_module(
        &target_name,
        &target_source_path,
        &target_certificate_relative,
        target_source_before.as_bytes(),
        &target_certificate_before,
        vec![support_name.clone()],
    )?;
    let support_identity_before = support_identity_hash(owner, &root_relative, &modules)?;
    let mut initial_modules = modules.clone();
    initial_modules.push(initial_target);
    write_manifest_and_lock(owner, &root_relative, &initial_modules, None)?;

    owner.replace_exact_file(
        &root_relative.join(&target_source_path),
        target_source_before.as_bytes(),
        target_source_after.as_bytes(),
    )?;
    let edited_target = manifest_module(
        &target_name,
        &target_source_path,
        &target_certificate_relative,
        target_source_after.as_bytes(),
        &target_certificate_after,
        vec![support_name],
    )?;
    let support_identity_after = support_identity_hash(owner, &root_relative, &modules)?;
    if support_identity_before != support_identity_after {
        return Err(format!(
            "{} support identity changed after target edit",
            size.label()
        ));
    }
    modules.push(edited_target);
    write_manifest_and_lock(owner, &root_relative, &modules, Some(&initial_modules))?;
    let target_certificate_path = root.join(&target_certificate_relative);
    let (tree_files, tree_directories) = owner.catalog_subtree_paths(&root_relative)?;
    let package_snapshot_hash =
        package_snapshot_hash_owned(owner, &root_relative, &tree_files, &tree_directories)?;
    Ok(GeneratedFixture {
        package_snapshot_hash,
        root,
        root_relative,
        target: Name::from_dotted(&target_name),
        support_modules: modules[..modules.len() - 1]
            .iter()
            .map(|module| module.module.clone())
            .collect(),
        target_certificate_path: target_certificate_path.clone(),
        support_identity_hash: support_identity_after,
        target_source_hash_before_edit: hash_bytes(target_source_before.as_bytes()),
        target_source_hash_after_edit: hash_bytes(target_source_after.as_bytes()),
        target_certificate_hash: hash_file(&target_certificate_path)?,
        tree_files,
        tree_directories,
    })
}

fn compile_module(
    file_id: u32,
    module_name: &str,
    source: &str,
    verified_modules: &[VerifiedModule],
    source_interfaces: &[HumanImportedSourceInterface],
) -> Result<(Vec<u8>, VerifiedModule, HumanImportedSourceInterface), String> {
    let module = Name::from_dotted(module_name);
    let output =
        compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
            FileId(file_id),
            module.clone(),
            source,
            verified_modules,
            source_interfaces,
            &HumanCompileOptions::default(),
            &AxiomPolicy::normal(),
        )
        .map_err(debug_error)?;
    let bytes = npa_cert::encode_module_cert(&output.certificate).map_err(debug_error)?;
    let source_interface = HumanImportedSourceInterface {
        module,
        export_hash: output.certificate.hashes().export_hash,
        certificate_hash: Some(output.certificate.hashes().certificate_hash),
        source_interface: output.source_interface,
    };
    Ok((bytes, output.verified_module, source_interface))
}

fn manifest_module(
    module: &str,
    source: &str,
    certificate: &str,
    source_bytes: &[u8],
    certificate_bytes: &[u8],
    imports: Vec<Name>,
) -> Result<ManifestModule, String> {
    let certificate_value = npa_cert::decode_module_cert(certificate_bytes).map_err(debug_error)?;
    Ok(ManifestModule {
        module: Name::from_dotted(module),
        source: source.to_owned(),
        certificate: certificate.to_owned(),
        imports,
        source_hash: package_file_hash(source_bytes),
        certificate_file_hash: package_file_hash(certificate_bytes),
        export_hash: PackageHash::from(certificate_value.hashes().export_hash),
        axiom_report_hash: PackageHash::from(certificate_value.hashes().axiom_report_hash),
        certificate_hash: PackageHash::from(certificate_value.hashes().certificate_hash),
    })
}

fn write_manifest_and_lock(
    owner: &ClosedPrivateDirectory,
    root_relative: &Path,
    modules: &[ManifestModule],
    previous_modules: Option<&[ManifestModule]>,
) -> Result<(), String> {
    let manifest = fixture_manifest(modules);
    let validated = parse_and_validate_manifest_str(&manifest).map_err(display_error)?;
    let artifact_bytes = modules
        .iter()
        .map(|module| {
            owner.read_regular_file(&root_relative.join(&module.certificate), 128 * 1024 * 1024)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let lock = build_package_lock_from_artifacts(
        &validated,
        PackagePath::new(PACKAGE_MANIFEST_PATH),
        manifest.as_bytes(),
        modules
            .iter()
            .zip(&artifact_bytes)
            .map(|(module, bytes)| PackageLockArtifact {
                path: PackagePath::new(module.certificate.clone()),
                bytes,
            }),
    )
    .map_err(display_error)?;
    let canonical_lock = lock.canonical_json().map_err(display_error)?;
    let manifest_path = root_relative.join(PACKAGE_MANIFEST_PATH);
    let lock_path = root_relative.join(LOCK_PATH);
    if let Some(previous_modules) = previous_modules {
        let previous_manifest = fixture_manifest(previous_modules);
        let previous_lock = owner.read_regular_file(&lock_path, 16 * 1024 * 1024)?;
        owner.replace_exact_file(
            &manifest_path,
            previous_manifest.as_bytes(),
            manifest.as_bytes(),
        )?;
        owner.replace_exact_file(&lock_path, &previous_lock, canonical_lock.as_bytes())
    } else {
        owner.create_new_file(&manifest_path, manifest.as_bytes())?;
        owner.create_directories(
            lock_path
                .parent()
                .ok_or("fixture lock path has no parent")?,
        )?;
        owner.create_new_file(&lock_path, canonical_lock.as_bytes())
    }
}

fn fixture_manifest(modules: &[ManifestModule]) -> String {
    let mut source = String::from(
        r#"schema = "npa.package.v0.1"
package = "targeted-build-certs-performance"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

"#,
    );
    for module in modules {
        let imports = module
            .imports
            .iter()
            .map(|name| format!("\"{}\"", name.as_dotted()))
            .collect::<Vec<_>>()
            .join(", ");
        source.push_str(&format!(
            r#"[[modules]]
module = "{}"
source = "{}"
certificate = "{}"
imports = [{}]
expected_source_hash = "{}"
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []

"#,
            module.module.as_dotted(),
            module.source,
            module.certificate,
            imports,
            format_package_hash(&module.source_hash),
            format_package_hash(&module.certificate_file_hash),
            format_package_hash(&module.export_hash),
            format_package_hash(&module.axiom_report_hash),
            format_package_hash(&module.certificate_hash),
        ));
    }
    source
}

fn write_artifact(
    owner: &ClosedPrivateDirectory,
    root_relative: &Path,
    relative: &str,
    bytes: &[u8],
) -> Result<(), String> {
    let path = root_relative.join(relative);
    let parent = path
        .parent()
        .ok_or_else(|| "fixture artifact path has no parent".to_owned())?;
    owner.create_directories(parent)?;
    owner.create_new_file(&path, bytes)
}

fn support_identity_hash(
    owner: &ClosedPrivateDirectory,
    root_relative: &Path,
    modules: &[ManifestModule],
) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for module in modules {
        hasher.update(module.module.as_dotted().as_bytes());
        hasher.update(
            owner.read_regular_file(&root_relative.join(&module.source), 16 * 1024 * 1024)?,
        );
        hasher.update(
            owner.read_regular_file(&root_relative.join(&module.certificate), 128 * 1024 * 1024)?,
        );
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn package_snapshot_hash(root: &Path) -> Result<String, String> {
    let tree = read_absolute_regular_tree(
        root,
        MAX_PACKAGE_TREE_ENTRIES,
        MAX_PACKAGE_FILE_BYTES,
        MAX_PACKAGE_TREE_BYTES,
        "TBAC package snapshot",
    )?;
    let mut hasher = Sha256::new();
    for (relative, bytes) in tree.files {
        hasher.update(canonical_relative_path(&relative)?.as_bytes());
        hasher.update([0]);
        hasher.update(bytes);
        hasher.update([0]);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn package_snapshot_hash_owned(
    owner: &ClosedPrivateDirectory,
    root: &Path,
    files: &BTreeSet<PathBuf>,
    directories: &BTreeSet<PathBuf>,
) -> Result<String, String> {
    let (actual_files, actual_directories) = owner.catalog_subtree_paths(root)?;
    if &actual_files != files || &actual_directories != directories {
        return Err("TBAC fixture tree differs from its immutable catalog".to_owned());
    }
    let mut hasher = Sha256::new();
    for file in files {
        let relative = file.strip_prefix(root).map_err(display_error)?;
        hasher.update(canonical_relative_path(relative)?.as_bytes());
        hasher.update([0]);
        hasher.update(owner.read_regular_file(file, 128 * 1024 * 1024)?);
        hasher.update([0]);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn canonical_relative_path(path: &Path) -> Result<String, String> {
    path.components()
        .map(|component| {
            component
                .as_os_str()
                .to_str()
                .map(str::to_owned)
                .ok_or_else(|| "fixture path is not UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|components| components.join("/"))
}

fn target_certificate_path(package_root: &Path, target: &Name) -> Result<PathBuf, String> {
    let manifest = String::from_utf8(read_invocation_regular_file(
        &package_root.join(PACKAGE_MANIFEST_PATH),
        MAX_CONTRACT_BYTES,
        "TBAC package manifest",
    )?)
    .map_err(display_error)?;
    let validated = parse_and_validate_manifest_str(&manifest).map_err(display_error)?;
    let module = validated
        .manifest()
        .modules
        .iter()
        .find(|module| &module.module == target)
        .ok_or_else(|| "worker target is absent from fixture manifest".to_owned())?;
    Ok(package_root.join(module.certificate.as_str()))
}

fn expected_counters(size: FixtureSize, policy: CachePolicy) -> ExpectedCounters {
    let support = size.support_count() as u64;
    let (hits, bypassed, misses, live, avoided, written) = match policy {
        CachePolicy::Cold => (0, 0, support, support, 0, support),
        CachePolicy::Warm | CachePolicy::FullyWarm => (support, 0, 0, 0, support, 0),
        CachePolicy::PartiallyWarm => (11, 12, 1, 13, 11, 1),
    };
    ExpectedCounters {
        values: BTreeMap::from([
            ("support_selected".to_owned(), support),
            ("targets_selected".to_owned(), 1),
            ("external_selected".to_owned(), 0),
            ("forced_live_support".to_owned(), 0),
            ("targets_forced_live".to_owned(), 0),
            ("visited_support".to_owned(), support),
            ("visited_targets".to_owned(), 1),
            ("visited_external".to_owned(), 0),
            ("context_hits".to_owned(), hits),
            ("context_bypassed_hits".to_owned(), bypassed),
            ("context_misses".to_owned(), misses),
            ("context_stale".to_owned(), 0),
            ("context_schema_misses".to_owned(), 0),
            ("context_invalid".to_owned(), 0),
            ("context_ineligible".to_owned(), 0),
            ("live_prerequisite_checks".to_owned(), live),
            ("avoided_kernel_checks".to_owned(), avoided),
            ("avoided_source_interface_resolutions".to_owned(), avoided),
            ("target_attempts".to_owned(), 1),
            ("target_fresh_builds".to_owned(), 1),
            ("entries_written".to_owned(), written),
        ]),
    }
}

fn local_hit_summary_counters(summary: &str) -> Result<BTreeMap<String, u64>, String> {
    let fields = summary
        .split(';')
        .map(|field| {
            field
                .split_once('=')
                .ok_or_else(|| format!("malformed local-hit summary field {field:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let text = fields.iter().copied().collect::<BTreeMap<_, _>>();
    for (name, expected) in [
        ("mode", "local-hit"),
        ("complete", "true"),
        ("trusted", "false"),
        ("build_evidence", "false"),
        ("proof_evidence", "false"),
    ] {
        if text.get(name).copied() != Some(expected) {
            return Err(format!("local-hit summary has unexpected {name}"));
        }
    }
    let mut counters = BTreeMap::new();
    for (name, value) in fields {
        if matches!(
            name,
            "mode" | "complete" | "trusted" | "build_evidence" | "proof_evidence"
        ) {
            continue;
        }
        counters.insert(
            name.to_owned(),
            value.parse::<u64>().map_err(display_error)?,
        );
    }
    let target_attempts = counters
        .get("visited_targets")
        .copied()
        .ok_or_else(|| "local-hit summary omitted visited_targets".to_owned())?;
    counters.insert("target_attempts".to_owned(), target_attempts);
    Ok(counters)
}

fn validate_expected_counters(
    expected: &ExpectedCounters,
    observed: &BTreeMap<String, u64>,
) -> Result<(), String> {
    for (name, expected_value) in &expected.values {
        let actual = observed
            .get(name)
            .ok_or_else(|| format!("local-hit summary omitted {name}"))?;
        if actual != expected_value {
            return Err(format!(
                "local-hit counter {name} expected {expected_value}, got {actual}"
            ));
        }
    }
    Ok(())
}

fn validate_common_measurements(
    expected: &ExpectedCounters,
    summary: &BTreeMap<String, u64>,
    measurements: &BTreeMap<String, u64>,
) -> Result<(), String> {
    for (summary_name, measurement_name) in [
        ("support_selected", "cache.support_selected"),
        ("targets_forced_live", "cache.targets_forced_live"),
        ("context_hits", "cache.context_hits"),
        ("context_bypassed_hits", "cache.context_bypassed_hits"),
        ("context_misses", "cache.context_misses"),
        ("context_stale", "cache.context_stale"),
        ("context_schema_misses", "cache.context_schema_misses"),
        ("context_ineligible", "cache.context_ineligible"),
        ("live_prerequisite_checks", "cache.live_prerequisite_checks"),
        ("avoided_kernel_checks", "cache.avoided_kernel_checks"),
        (
            "avoided_source_interface_resolutions",
            "cache.avoided_source_interface_resolutions",
        ),
        ("target_fresh_builds", "cache.target_fresh_builds"),
        ("bytes_loaded", "cache.bytes_loaded"),
        ("bytes_written", "cache.bytes_written"),
    ] {
        let expected_value = summary
            .get(summary_name)
            .ok_or_else(|| format!("local-hit summary omitted {summary_name}"))?;
        let actual = measurements
            .get(measurement_name)
            .ok_or_else(|| format!("common measurements omitted {measurement_name}"))?;
        if actual != expected_value {
            return Err(format!(
                "measurement {measurement_name} expected {expected_value}, got {actual}"
            ));
        }
    }
    for duration in [
        "cache.tool_identity_elapsed",
        "cache.current_byte_validation_elapsed",
        "cache.reconstruction_elapsed",
        "cache.live_support_elapsed",
        "cache.source_interface_resolution_elapsed",
        "cache.fresh_target_elapsed",
    ] {
        if !measurements.contains_key(duration) {
            return Err(format!("common measurements omitted {duration}"));
        }
    }
    if measurements
        .get("cache.tool_identity_bytes")
        .copied()
        .unwrap_or(0)
        == 0
    {
        return Err("local-hit measurement omitted executable identity bytes".to_owned());
    }
    validate_expected_counters(expected, summary)
}

fn population_targets(
    fixture: &GeneratedFixture,
    policy: CachePolicy,
) -> Result<Vec<Name>, String> {
    match policy {
        CachePolicy::Cold => Err("cold scenario requested warm population".to_owned()),
        CachePolicy::Warm | CachePolicy::FullyWarm => Ok(vec![fixture.target.clone()]),
        CachePolicy::PartiallyWarm => Ok(vec![fixture.target.clone()]),
    }
}

fn validate_population(
    fixture: &GeneratedFixture,
    policy: CachePolicy,
    entries: &[TargetedAuthoringSupportContextEntry],
) -> Result<(), String> {
    let actual = entries
        .iter()
        .map(|entry| entry.key_input.module.clone())
        .collect::<Vec<_>>();
    let expected = match policy {
        CachePolicy::Cold => Vec::new(),
        CachePolicy::Warm | CachePolicy::FullyWarm => fixture.support_modules.clone(),
        CachePolicy::PartiallyWarm => fixture
            .support_modules
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != fixture.support_modules.len() / 2)
            .map(|(_, module)| module.clone())
            .collect(),
    };
    if actual != expected {
        return Err(format!(
            "{} population coverage mismatch: expected {:?}, got {:?}",
            policy.label(),
            expected,
            actual
        ));
    }
    Ok(())
}

fn support_cache_entries(
    owner: &ClosedPrivateDirectory,
    root: &Path,
) -> Result<Vec<TargetedAuthoringSupportContextEntry>, String> {
    let (files, directories) = owner.catalog_subtree_paths(root)?;
    validate_tbac_cache_catalog(root, &files, &directories)?;
    let mut entries = Vec::new();
    for file in files {
        if file
            .components()
            .any(|component| component.as_os_str() == "targeted-authoring-support-v0.1")
            && file.extension().and_then(|extension| extension.to_str()) == Some("json")
        {
            entries.push(
                parse_targeted_authoring_support_context_entry(
                    &owner.read_regular_file(&file, 16 * 1024 * 1024)?,
                )
                .map_err(display_error)?,
            );
        }
    }
    entries.sort_by(|left, right| left.key_input.module.cmp(&right.key_input.module));
    Ok(entries)
}

fn validate_tbac_cache_catalog(
    root: &Path,
    files: &BTreeSet<PathBuf>,
    directories: &BTreeSet<PathBuf>,
) -> Result<(), String> {
    if !directories.contains(root)
        || !files.iter().all(|path| path.starts_with(root))
        || !directories.iter().all(|path| path.starts_with(root))
    {
        return Err("TBAC cache catalog escaped its sample root".to_owned());
    }
    for directory in directories {
        let relative = directory.strip_prefix(root).map_err(display_error)?;
        let components = relative
            .components()
            .map(|component| component.as_os_str().to_str().unwrap_or(""))
            .collect::<Vec<_>>();
        if components.is_empty() {
            continue;
        }
        let valid = match components.as_slice() {
            ["packages"] => true,
            ["packages", namespace] => valid_lowercase_hex(namespace, 64),
            ["packages", namespace, store] => {
                valid_lowercase_hex(namespace, 64)
                    && matches!(
                        *store,
                        "build-check-v0.2" | "targeted-authoring-support-v0.1"
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(format!(
                "TBAC cache catalog contains an unexpected directory: {}",
                directory.display()
            ));
        }
    }
    for file in files {
        let parent = file.parent().ok_or("TBAC cache file has no parent")?;
        if !directories.contains(parent) {
            return Err("TBAC cache file parent is absent from its catalog".to_owned());
        }
        let name = file
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("TBAC cache filename is not UTF-8")?;
        let Some(stem) = name.strip_suffix(".json") else {
            return Err("TBAC cache filename does not end in .json".to_owned());
        };
        if !valid_lowercase_hex(stem, 64)
            || !parent.components().any(|component| {
                matches!(
                    component.as_os_str().to_str(),
                    Some("build-check-v0.2" | "targeted-authoring-support-v0.1")
                )
            })
        {
            return Err("TBAC cache filename/store grammar is invalid".to_owned());
        }
    }
    Ok(())
}

fn valid_lowercase_hex(value: &str, width: usize) -> bool {
    value.len() == width
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn cleanup_tbac_cache_root(owner: &ClosedPrivateDirectory, root: &Path) -> Result<(), String> {
    let (files, directories) = owner.catalog_subtree_paths(root)?;
    validate_tbac_cache_catalog(root, &files, &directories)?;
    owner.remove_exact_subtree(root, &files, &directories)
}

fn cleanup_tbac_sample_files(
    owner: &ClosedPrivateDirectory,
    cache_relative: &Path,
) -> Result<(), String> {
    cleanup_tbac_cache_root(owner, cache_relative)?;
    let stdout = cache_relative.with_extension("consumer.stdout");
    let stderr = cache_relative.with_extension("consumer.stderr");
    let stdout_bytes = owner.read_regular_file(&stdout, 4 * 1024 * 1024)?;
    let stderr_bytes = owner.read_regular_file(&stderr, 4 * 1024 * 1024)?;
    owner.remove_exact_file(&stdout, &stdout_bytes)?;
    owner.remove_exact_file(&stderr, &stderr_bytes)
}

fn cleanup_tbac_private_root(
    owner: &ClosedPrivateDirectory,
    fixtures: &[&GeneratedFixture],
) -> Result<(), String> {
    for fixture in fixtures {
        let (files, directories) = owner.catalog_subtree_paths(&fixture.root_relative)?;
        validate_tbac_fixture_catalog(fixture, &files, &directories)?;
        owner.remove_exact_subtree(&fixture.root_relative, &files, &directories)?;
    }
    let (remaining_files, remaining_directories) = owner.catalog_root_paths()?;
    if !remaining_directories.is_empty()
        || (remaining_files != BTreeSet::new()
            && remaining_files != BTreeSet::from([PathBuf::from("harness-executable")]))
    {
        return Err("TBAC private root contains an unknown residual entry".to_owned());
    }
    if remaining_files.contains(Path::new("harness-executable")) {
        let executable =
            owner.read_regular_file(Path::new("harness-executable"), MAX_EXECUTABLE_BYTES)?;
        owner.remove_exact_file(Path::new("harness-executable"), &executable)?;
    }
    owner.remove_empty_root()
}

fn validate_tbac_fixture_catalog(
    fixture: &GeneratedFixture,
    files: &BTreeSet<PathBuf>,
    directories: &BTreeSet<PathBuf>,
) -> Result<(), String> {
    if files != &fixture.tree_files || directories != &fixture.tree_directories {
        return Err(format!(
            "TBAC fixture differs from its exact generated catalog: files={files:?} directories={directories:?}"
        ));
    }
    Ok(())
}

fn remove_support_cache_entry(
    owner: &ClosedPrivateDirectory,
    root: &Path,
    module: &Name,
) -> Result<(), String> {
    let (files, directories) = owner.catalog_subtree_paths(root)?;
    validate_tbac_cache_catalog(root, &files, &directories)?;
    let mut matches = Vec::new();
    for file in files {
        if file
            .components()
            .any(|component| component.as_os_str() == "targeted-authoring-support-v0.1")
            && file.extension().and_then(|extension| extension.to_str()) == Some("json")
        {
            let bytes = owner.read_regular_file(&file, 16 * 1024 * 1024)?;
            let entry =
                parse_targeted_authoring_support_context_entry(&bytes).map_err(display_error)?;
            if &entry.key_input.module == module {
                matches.push((file, bytes));
            }
        }
    }
    if matches.len() != 1 {
        return Err(format!(
            "partial-warm gap {} matched {} support entries",
            module.as_dotted(),
            matches.len()
        ));
    }
    owner.remove_exact_file(&matches[0].0, &matches[0].1)
}

struct SupportStoreIdentity {
    cache_keys: BTreeMap<String, String>,
    executable_hash: String,
    authoring_abis: BTreeMap<String, String>,
    compiler_options: Vec<String>,
}

fn support_store_identity(
    entries: &[TargetedAuthoringSupportContextEntry],
) -> Result<SupportStoreIdentity, String> {
    let first = entries
        .first()
        .ok_or_else(|| "support store has no entries".to_owned())?;
    let toolchain = &first.key_input.toolchain;
    let compiler_options = first.key_input.semantic_compiler_options.clone();
    for entry in entries {
        if &entry.key_input.toolchain != toolchain
            || entry.key_input.semantic_compiler_options != compiler_options
        {
            return Err("support entries disagree on compiler/toolchain identity".to_owned());
        }
    }
    Ok(SupportStoreIdentity {
        cache_keys: entries
            .iter()
            .map(|entry| (entry.key_input.module.as_dotted(), entry.cache_key.clone()))
            .collect(),
        executable_hash: format_package_hash(&toolchain.executable_hash),
        authoring_abis: BTreeMap::from([
            ("cli".to_owned(), toolchain.cli_authoring_abi.clone()),
            (
                "frontend".to_owned(),
                toolchain.frontend_authoring_abi.clone(),
            ),
            (
                "producer".to_owned(),
                toolchain.producer_authoring_abi.clone(),
            ),
            ("kernel".to_owned(), toolchain.kernel_authoring_abi.clone()),
        ]),
        compiler_options,
    })
}

fn directory_file_bytes(owner: &ClosedPrivateDirectory, root: &Path) -> Result<u64, String> {
    let (files, directories) = owner.catalog_subtree_paths(root)?;
    validate_tbac_cache_catalog(root, &files, &directories)?;
    files.iter().try_fold(0_u64, |total, file| {
        let bytes = owner.read_regular_file(file, 16 * 1024 * 1024)?;
        total
            .checked_add(u64::try_from(bytes.len()).map_err(display_error)?)
            .ok_or_else(|| "TBAC cache byte total overflow".to_owned())
    })
}

fn flat_counters(counters: &BTreeMap<String, u64>) -> String {
    counters
        .iter()
        .map(|(name, value)| format!("{name}={value}"))
        .collect::<Vec<_>>()
        .join(";")
}

fn parse_flat_counters(source: &str) -> Result<BTreeMap<String, u64>, String> {
    if source.is_empty() {
        return Ok(BTreeMap::new());
    }
    source
        .split(';')
        .map(|field| {
            let (name, value) = field
                .split_once('=')
                .ok_or_else(|| "malformed worker measurement".to_owned())?;
            Ok((
                name.to_owned(),
                value.parse::<u64>().map_err(display_error)?,
            ))
        })
        .collect()
}

fn fixture_support_count(fixture: &GeneratedFixture) -> usize {
    if fixture.target.as_dotted().contains(".Small.") {
        FixtureSize::Small.support_count()
    } else {
        FixtureSize::Large.support_count()
    }
}

fn targeted_fixture_counts(source: &str, scenario_id: &str) -> Result<(u64, u64, String), String> {
    let document = JsonDocument::parse(source).map_err(debug_error)?;
    let scenario = find_scenario(document.root(), "scenarios", scenario_id)?;
    Ok((
        json_u64(json_field(scenario, "support_module_count")?)?,
        json_u64(json_field(scenario, "target_module_count")?)?,
        json_text(json_field(scenario, "target_edit")?)?.to_owned(),
    ))
}

fn targeted_fixture_population(
    source: &str,
    scenario_id: &str,
) -> Result<(Vec<String>, Vec<String>), String> {
    let document = JsonDocument::parse(source).map_err(debug_error)?;
    let scenario = find_scenario(document.root(), "scenarios", scenario_id)?;
    Ok((
        json_text_array(json_field(scenario, "population_modules")?)?,
        json_text_array(json_field(scenario, "removed_support_modules")?)?,
    ))
}

fn expected_population_contract(scenario: Scenario) -> (Vec<String>, Vec<String>) {
    let prefix = match scenario.size {
        FixtureSize::Small => "Small",
        FixtureSize::Large => "Large",
    };
    let population = if scenario.policy.is_warm() {
        vec![format!("Fixture.{prefix}.Target")]
    } else {
        Vec::new()
    };
    let removed = if scenario.policy == CachePolicy::PartiallyWarm {
        vec![format!(
            "Fixture.{prefix}.Support{:02}",
            scenario.size.support_count() / 2
        )]
    } else {
        Vec::new()
    };
    (population, removed)
}

fn baseline_counters(source: &str, scenario_id: &str) -> Result<BTreeMap<String, u64>, String> {
    let document = JsonDocument::parse(source).map_err(debug_error)?;
    let scenario = find_scenario(document.root(), "targeted_build_certs_rollout", scenario_id)?;
    let counters = json_field(scenario, "deterministic_counters")?;
    let members = counters
        .object_members()
        .ok_or_else(|| "deterministic_counters must be an object".to_owned())?;
    let mut result = BTreeMap::new();
    for member in members {
        if result
            .insert(member.key().to_owned(), json_u64(member.value())?)
            .is_some()
        {
            return Err("duplicate deterministic counter".to_owned());
        }
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn validate_rollout_report_source(
    source: &str,
    source_identity: &str,
    fixture_manifest: &[u8],
    baseline: &[u8],
    small: &GeneratedFixture,
    large: &GeneratedFixture,
    executable_hash: &str,
    small_support_identity: &SupportStoreIdentity,
    large_support_identity: &SupportStoreIdentity,
) -> Result<(), String> {
    let document = JsonDocument::parse(source).map_err(debug_error)?;
    let root = document.root();
    require_object_keys(
        root,
        &[
            "schema",
            "trusted",
            "proof_evidence",
            "status",
            "elapsed_gate",
            "speedup_claimed",
            "rollout_decision",
            "automatic_selection",
            "fixture_manifest_hash",
            "baseline_hash",
            "source_identity",
            "cargo_lock_hash",
            "harness_source_hash",
            "production_source_set_hash",
            "harness_executable_hash",
            "rustc_vv",
            "cargo_profile",
            "features",
            "target",
            "rustflags",
            "warmup_count",
            "sample_count",
            "cache_root_policy",
            "process_policy",
            "fixture_identities",
            "scenarios",
        ],
        "rollout report",
    )?;
    require_text(root, "schema", "npa.targeted_build_certs.rollout_run.v0.2")?;
    require_bool(root, "trusted", false)?;
    require_bool(root, "proof_evidence", false)?;
    require_text(root, "status", "passed")?;
    require_text(root, "elapsed_gate", "advisory")?;
    require_bool(root, "speedup_claimed", false)?;
    require_text(
        root,
        "rollout_decision",
        "retain-explicit-advisory-local-hit",
    )?;
    require_bool(root, "automatic_selection", false)?;
    require_text(root, "fixture_manifest_hash", &hash_bytes(fixture_manifest))?;
    require_text(root, "baseline_hash", &hash_bytes(baseline))?;
    require_text(root, "source_identity", source_identity)?;
    require_text(
        root,
        "cargo_lock_hash",
        env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256"),
    )?;
    require_text(
        root,
        "harness_source_hash",
        env!("NPA_CLI_BUILD_TBAC_HARNESS_SOURCE_SHA256"),
    )?;
    require_text(
        root,
        "production_source_set_hash",
        env!("NPA_CLI_BUILD_TBAC_SOURCE_SET_SHA256"),
    )?;
    require_text(root, "harness_executable_hash", executable_hash)?;
    require_text(
        root,
        "rustc_vv",
        &decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?,
    )?;
    require_text(root, "cargo_profile", env!("NPA_CLI_BUILD_CARGO_PROFILE"))?;
    let expected_features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if json_text_array(json_field(root, "features")?)? != expected_features {
        return Err("rollout report features differ from the build".to_owned());
    }
    require_text(root, "target", env!("NPA_CLI_BUILD_TARGET"))?;
    require_text(
        root,
        "rustflags",
        &decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?,
    )?;
    require_u64(root, "warmup_count", WARMUP_COUNT as u64)?;
    require_u64(root, "sample_count", SAMPLE_COUNT as u64)?;
    require_text(
        root,
        "cache_root_policy",
        "fresh-explicit-root-per-recorded-sample",
    )?;
    require_text(
        root,
        "process_policy",
        "fresh-worker-process-per-run;warm-roots-populated-by-distinct-unmeasured-read-through-process",
    )?;
    validate_fixture_identities(json_field(root, "fixture_identities")?, small, large)?;
    validate_scenario_reports(
        json_field(root, "scenarios")?,
        executable_hash,
        small_support_identity,
        large_support_identity,
    )
}

fn validate_fixture_identities(
    value: &JsonValue<'_>,
    small: &GeneratedFixture,
    large: &GeneratedFixture,
) -> Result<(), String> {
    let rows = value
        .array_elements()
        .ok_or_else(|| "fixture_identities must be an array".to_owned())?;
    if rows.len() != 2 {
        return Err("fixture_identities must contain small then large".to_owned());
    }
    for (row, size, fixture) in [
        (&rows[0], FixtureSize::Small, small),
        (&rows[1], FixtureSize::Large, large),
    ] {
        require_object_keys(
            row,
            &[
                "size",
                "support_module_count",
                "target_module_count",
                "target_edit",
                "support_identity_hash",
                "target_source_hash_before_edit",
                "target_source_hash_after_edit",
                "target_certificate_hash",
                "package_snapshot_hash",
                "support_identity_unchanged",
                "target_certificate_bytes_stable",
            ],
            "fixture identity",
        )?;
        require_text(row, "size", size.label())?;
        require_u64(row, "support_module_count", size.support_count() as u64)?;
        require_u64(row, "target_module_count", 1)?;
        require_text(row, "target_edit", TARGET_EDIT)?;
        require_text(row, "support_identity_hash", &fixture.support_identity_hash)?;
        require_text(
            row,
            "target_source_hash_before_edit",
            &fixture.target_source_hash_before_edit,
        )?;
        require_text(
            row,
            "target_source_hash_after_edit",
            &fixture.target_source_hash_after_edit,
        )?;
        require_text(
            row,
            "target_certificate_hash",
            &fixture.target_certificate_hash,
        )?;
        require_text(row, "package_snapshot_hash", &fixture.package_snapshot_hash)?;
        require_bool(row, "support_identity_unchanged", true)?;
        require_bool(row, "target_certificate_bytes_stable", true)?;
    }
    Ok(())
}

fn validate_scenario_reports(
    value: &JsonValue<'_>,
    executable_hash: &str,
    small_support_identity: &SupportStoreIdentity,
    large_support_identity: &SupportStoreIdentity,
) -> Result<(), String> {
    let rows = value
        .array_elements()
        .ok_or_else(|| "scenarios must be an array".to_owned())?;
    if rows.len() != SCENARIOS.len() {
        return Err("rollout report does not contain the exact scenario catalog".to_owned());
    }
    let mut compiler_options: Option<Vec<String>> = None;
    for (row, scenario) in rows.iter().zip(SCENARIOS) {
        require_object_keys(
            row,
            &[
                "id",
                "fixture_size",
                "cache_policy",
                "support_cache_keys",
                "support_executable_hash",
                "authoring_abis",
                "compiler_options",
                "samples",
                "wall_summary_ns",
                "peak_rss_summary_kib",
                "cache_lookup_summary_ms",
                "cache_size_summary_bytes",
                "common_cache_measurement_summaries",
                "invariants",
                "status",
            ],
            "rollout scenario",
        )?;
        require_text(row, "id", scenario.id)?;
        require_text(row, "fixture_size", scenario.size.label())?;
        require_text(row, "cache_policy", scenario.policy.label())?;
        let expected_support_identity = match scenario.size {
            FixtureSize::Small => small_support_identity,
            FixtureSize::Large => large_support_identity,
        };
        if json_text_object(json_field(row, "support_cache_keys")?)?
            != expected_support_identity.cache_keys
        {
            return Err("support cache keys differ from the production fixture".to_owned());
        }
        require_text(row, "support_executable_hash", executable_hash)?;
        if json_text_object(json_field(row, "authoring_abis")?)?
            != expected_support_identity.authoring_abis
        {
            return Err("authoring ABI identity differs from the production fixture".to_owned());
        }
        let row_options = json_text_array(json_field(row, "compiler_options")?)?;
        if row_options != expected_support_identity.compiler_options {
            return Err("rollout compiler options differ from the production fixture".to_owned());
        }
        if compiler_options
            .as_ref()
            .is_some_and(|expected| expected != &row_options)
        {
            return Err("rollout scenarios disagree on compiler options".to_owned());
        }
        compiler_options.get_or_insert(row_options);
        let samples = validate_samples(json_field(row, "samples")?, scenario)?;
        validate_statistics(json_field(row, "wall_summary_ns")?, &samples.wall)?;
        validate_statistics(json_field(row, "peak_rss_summary_kib")?, &samples.rss)?;
        validate_statistics(json_field(row, "cache_lookup_summary_ms")?, &samples.lookup)?;
        validate_statistics(
            json_field(row, "cache_size_summary_bytes")?,
            &samples.cache_size,
        )?;
        validate_common_summaries(
            json_field(row, "common_cache_measurement_summaries")?,
            &samples.common,
        )?;
        validate_invariants(json_field(row, "invariants")?, scenario)?;
        require_text(row, "status", "passed")?;
    }
    Ok(())
}

struct ValidatedSamples {
    wall: Vec<u64>,
    rss: Vec<u64>,
    lookup: Vec<u64>,
    cache_size: Vec<u64>,
    common: BTreeMap<String, Vec<u64>>,
}

fn validate_samples(value: &JsonValue<'_>, scenario: Scenario) -> Result<ValidatedSamples, String> {
    let rows = value
        .array_elements()
        .ok_or_else(|| "scenario samples must be an array".to_owned())?;
    if rows.len() != SAMPLE_COUNT {
        return Err("scenario sample count differs from the fixed contract".to_owned());
    }
    let expected = expected_counters(scenario.size, scenario.policy).values;
    let mut result = ValidatedSamples {
        wall: Vec::with_capacity(SAMPLE_COUNT),
        rss: Vec::with_capacity(SAMPLE_COUNT),
        lookup: Vec::with_capacity(SAMPLE_COUNT),
        cache_size: Vec::with_capacity(SAMPLE_COUNT),
        common: BTreeMap::new(),
    };
    for row in rows {
        require_object_keys(
            row,
            &[
                "wall_ns",
                "peak_rss_kib",
                "cache_lookup_ms",
                "cache_size_bytes",
                "deterministic_counters",
                "common_cache_measurements",
            ],
            "rollout sample",
        )?;
        let wall = json_u64(json_field(row, "wall_ns")?)?;
        let rss = json_u64(json_field(row, "peak_rss_kib")?)?;
        let lookup = json_u64(json_field(row, "cache_lookup_ms")?)?;
        let cache_size = json_u64(json_field(row, "cache_size_bytes")?)?;
        if wall == 0 || rss == 0 || cache_size == 0 {
            return Err("rollout sample has an impossible zero measurement".to_owned());
        }
        let counters = json_u64_object(json_field(row, "deterministic_counters")?)?;
        if counters != expected {
            return Err(
                "rollout sample counters differ from the deterministic baseline".to_owned(),
            );
        }
        let common = json_u64_object(json_field(row, "common_cache_measurements")?)?;
        validate_common_cache_measurements(&common, &expected)?;
        for (label, value) in common {
            result.common.entry(label).or_default().push(value);
        }
        result.wall.push(wall);
        result.rss.push(rss);
        result.lookup.push(lookup);
        result.cache_size.push(cache_size);
    }
    Ok(result)
}

fn validate_common_cache_measurements(
    actual: &BTreeMap<String, u64>,
    counters: &BTreeMap<String, u64>,
) -> Result<(), String> {
    const LABELS: [&str; 21] = [
        "cache.avoided_kernel_checks",
        "cache.avoided_source_interface_resolutions",
        "cache.bytes_loaded",
        "cache.bytes_written",
        "cache.context_bypassed_hits",
        "cache.context_hits",
        "cache.context_ineligible",
        "cache.context_misses",
        "cache.context_schema_misses",
        "cache.context_stale",
        "cache.current_byte_validation_elapsed",
        "cache.fresh_target_elapsed",
        "cache.live_prerequisite_checks",
        "cache.live_support_elapsed",
        "cache.reconstruction_elapsed",
        "cache.source_interface_resolution_elapsed",
        "cache.support_selected",
        "cache.target_fresh_builds",
        "cache.targets_forced_live",
        "cache.tool_identity_bytes",
        "cache.tool_identity_elapsed",
    ];
    if actual.keys().map(String::as_str).collect::<Vec<_>>() != LABELS {
        return Err("common cache measurements have a noncanonical label set".to_owned());
    }
    for (counter, measurement) in [
        ("avoided_kernel_checks", "cache.avoided_kernel_checks"),
        (
            "avoided_source_interface_resolutions",
            "cache.avoided_source_interface_resolutions",
        ),
        ("context_bypassed_hits", "cache.context_bypassed_hits"),
        ("context_hits", "cache.context_hits"),
        ("context_ineligible", "cache.context_ineligible"),
        ("context_misses", "cache.context_misses"),
        ("context_schema_misses", "cache.context_schema_misses"),
        ("context_stale", "cache.context_stale"),
        ("live_prerequisite_checks", "cache.live_prerequisite_checks"),
        ("support_selected", "cache.support_selected"),
        ("target_fresh_builds", "cache.target_fresh_builds"),
        ("targets_forced_live", "cache.targets_forced_live"),
    ] {
        if actual.get(measurement) != counters.get(counter) {
            return Err(format!(
                "common measurement {measurement} disagrees with counters"
            ));
        }
    }
    if actual
        .get("cache.tool_identity_bytes")
        .copied()
        .unwrap_or(0)
        == 0
    {
        return Err("common measurements omit tool identity bytes".to_owned());
    }
    Ok(())
}

fn validate_invariants(value: &JsonValue<'_>, scenario: Scenario) -> Result<(), String> {
    require_object_keys(
        value,
        &[
            "same_selected_target",
            "same_certificate_bytes",
            "every_target_fresh",
            "target_attempts",
            "target_fresh_builds",
            "targets_forced_live",
            "retained_context_hits",
            "bypassed_context_hits",
            "live_context_misses",
            "avoided_kernel_checks",
            "avoided_source_interface_resolutions",
            "persistent_cache_distinct_from_process_global_memo",
        ],
        "scenario invariants",
    )?;
    require_bool(value, "same_selected_target", true)?;
    require_bool(value, "same_certificate_bytes", true)?;
    require_bool(value, "every_target_fresh", true)?;
    let expected = expected_counters(scenario.size, scenario.policy).values;
    for (field, counter) in [
        ("target_attempts", "target_attempts"),
        ("target_fresh_builds", "target_fresh_builds"),
        ("targets_forced_live", "targets_forced_live"),
        ("retained_context_hits", "context_hits"),
        ("bypassed_context_hits", "context_bypassed_hits"),
        ("live_context_misses", "context_misses"),
        ("avoided_kernel_checks", "avoided_kernel_checks"),
        (
            "avoided_source_interface_resolutions",
            "avoided_source_interface_resolutions",
        ),
    ] {
        require_u64(value, field, expected[counter])?;
    }
    require_bool(
        value,
        "persistent_cache_distinct_from_process_global_memo",
        true,
    )
}

fn validate_common_summaries(
    value: &JsonValue<'_>,
    samples: &BTreeMap<String, Vec<u64>>,
) -> Result<(), String> {
    let members = value
        .object_members()
        .ok_or_else(|| "common measurement summaries must be an object".to_owned())?;
    if members
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>()
        != samples.keys().map(String::as_str).collect::<Vec<_>>()
    {
        return Err("common measurement summary labels are noncanonical".to_owned());
    }
    for member in members {
        validate_statistics(member.value(), &samples[member.key()])?;
    }
    Ok(())
}

fn validate_statistics(value: &JsonValue<'_>, samples: &[u64]) -> Result<(), String> {
    require_object_keys(
        value,
        &["median", "median_absolute_deviation", "minimum", "maximum"],
        "statistics",
    )?;
    let expected = statistics(samples)?;
    require_u64(value, "median", expected.median)?;
    require_u64(
        value,
        "median_absolute_deviation",
        expected.median_absolute_deviation,
    )?;
    require_u64(value, "minimum", expected.minimum)?;
    require_u64(value, "maximum", expected.maximum)
}

fn require_object_keys(
    value: &JsonValue<'_>,
    expected: &[&str],
    context: &str,
) -> Result<(), String> {
    let actual = value
        .object_members()
        .ok_or_else(|| format!("{context} must be an object"))?
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>();
    if actual != expected {
        return Err(format!(
            "{context} has missing, unknown, duplicate, or reordered fields"
        ));
    }
    Ok(())
}

fn require_text(value: &JsonValue<'_>, field: &str, expected: &str) -> Result<(), String> {
    if json_text(json_field(value, field)?)? != expected {
        return Err(format!("field {field} differs from the report contract"));
    }
    Ok(())
}

fn require_bool(value: &JsonValue<'_>, field: &str, expected: bool) -> Result<(), String> {
    if json_field(value, field)?.bool_value() != Some(expected) {
        return Err(format!("field {field} differs from the report contract"));
    }
    Ok(())
}

fn require_u64(value: &JsonValue<'_>, field: &str, expected: u64) -> Result<(), String> {
    if json_u64(json_field(value, field)?)? != expected {
        return Err(format!("field {field} differs from the report contract"));
    }
    Ok(())
}

fn json_u64_object(value: &JsonValue<'_>) -> Result<BTreeMap<String, u64>, String> {
    value
        .object_members()
        .ok_or_else(|| "JSON value must be an object".to_owned())?
        .iter()
        .map(|member| Ok((member.key().to_owned(), json_u64(member.value())?)))
        .collect()
}

fn json_text_object(value: &JsonValue<'_>) -> Result<BTreeMap<String, String>, String> {
    value
        .object_members()
        .ok_or_else(|| "JSON value must be an object".to_owned())?
        .iter()
        .map(|member| {
            Ok((
                member.key().to_owned(),
                json_text(member.value())?.to_owned(),
            ))
        })
        .collect()
}

fn find_scenario<'a>(
    root: &'a JsonValue<'_>,
    array_name: &str,
    scenario_id: &str,
) -> Result<&'a JsonValue<'a>, String> {
    let scenarios = json_field(root, array_name)?
        .array_elements()
        .ok_or_else(|| format!("{array_name} must be an array"))?;
    let selected = scenarios
        .iter()
        .filter(|scenario| {
            json_field(scenario, "id")
                .ok()
                .and_then(JsonValue::string_value)
                == Some(scenario_id)
        })
        .collect::<Vec<_>>();
    if selected.len() != 1 {
        return Err(format!(
            "scenario {scenario_id} was not selected exactly once"
        ));
    }
    Ok(selected[0])
}

fn json_field<'a>(value: &'a JsonValue<'_>, name: &str) -> Result<&'a JsonValue<'a>, String> {
    let members = value
        .object_members()
        .ok_or_else(|| "JSON value must be an object".to_owned())?;
    let selected = members
        .iter()
        .filter(|member| member.key() == name)
        .collect::<Vec<_>>();
    if selected.len() != 1 {
        return Err(format!("JSON field {name} was not selected exactly once"));
    }
    Ok(selected[0].value())
}

fn json_text<'a>(value: &'a JsonValue<'_>) -> Result<&'a str, String> {
    value
        .string_value()
        .ok_or_else(|| "JSON value must be a string".to_owned())
}

fn json_text_array(value: &JsonValue<'_>) -> Result<Vec<String>, String> {
    value
        .array_elements()
        .ok_or_else(|| "JSON value must be an array".to_owned())?
        .iter()
        .map(|value| json_text(value).map(str::to_owned))
        .collect()
}

fn json_u64(value: &JsonValue<'_>) -> Result<u64, String> {
    value
        .number_raw()
        .ok_or_else(|| "JSON value must be a number".to_owned())?
        .parse::<u64>()
        .map_err(display_error)
}

fn statistics(values: &[u64]) -> Result<Statistics, String> {
    if values.is_empty() {
        return Err("statistics require at least one sample".to_owned());
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let median = sorted[sorted.len() / 2];
    let mut deviations = sorted
        .iter()
        .map(|value| value.abs_diff(median))
        .collect::<Vec<_>>();
    deviations.sort_unstable();
    Ok(Statistics {
        median,
        median_absolute_deviation: deviations[deviations.len() / 2],
        minimum: sorted[0],
        maximum: sorted[sorted.len() - 1],
    })
}

#[allow(clippy::too_many_arguments)]
fn report_json(
    runs: &[ScenarioRun],
    small: &GeneratedFixture,
    large: &GeneratedFixture,
    fixture_manifest: &[u8],
    baseline: &[u8],
    source_identity: &str,
    cargo_lock_hash: &str,
    harness_source_hash: &str,
    production_source_set_hash: &str,
    executable_hash: &str,
    rustc_vv: &str,
    cargo_profile: &str,
    features: &[String],
    target: &str,
    rustflags: &str,
) -> Result<String, String> {
    let scenarios = runs
        .iter()
        .map(scenario_json)
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    let features = features
        .iter()
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"npa.targeted_build_certs.rollout_run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"status\":\"passed\",\"elapsed_gate\":\"advisory\",\"speedup_claimed\":false,\"rollout_decision\":\"retain-explicit-advisory-local-hit\",\"automatic_selection\":false,\"fixture_manifest_hash\":\"{}\",\"baseline_hash\":\"{}\",\"source_identity\":\"{}\",\"cargo_lock_hash\":\"{}\",\"harness_source_hash\":\"{}\",\"production_source_set_hash\":\"{}\",\"harness_executable_hash\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"features\":[{}],\"target\":\"{}\",\"rustflags\":\"{}\",\"warmup_count\":{},\"sample_count\":{},\"cache_root_policy\":\"fresh-explicit-root-per-recorded-sample\",\"process_policy\":\"fresh-worker-process-per-run;warm-roots-populated-by-distinct-unmeasured-read-through-process\",\"fixture_identities\":[{},{}],\"scenarios\":[{}]}}",
        hash_bytes(fixture_manifest),
        hash_bytes(baseline),
        json_escape(source_identity),
        cargo_lock_hash,
        harness_source_hash,
        production_source_set_hash,
        executable_hash,
        json_escape(rustc_vv),
        json_escape(cargo_profile),
        features,
        json_escape(target),
        json_escape(rustflags),
        WARMUP_COUNT,
        SAMPLE_COUNT,
        fixture_identity_json(FixtureSize::Small, small),
        fixture_identity_json(FixtureSize::Large, large),
        scenarios,
    ))
}

fn fixture_identity_json(size: FixtureSize, fixture: &GeneratedFixture) -> String {
    format!(
        "{{\"size\":\"{}\",\"support_module_count\":{},\"target_module_count\":1,\"target_edit\":\"{}\",\"support_identity_hash\":\"{}\",\"target_source_hash_before_edit\":\"{}\",\"target_source_hash_after_edit\":\"{}\",\"target_certificate_hash\":\"{}\",\"package_snapshot_hash\":\"{}\",\"support_identity_unchanged\":true,\"target_certificate_bytes_stable\":true}}",
        size.label(),
        size.support_count(),
        TARGET_EDIT,
        fixture.support_identity_hash,
        fixture.target_source_hash_before_edit,
        fixture.target_source_hash_after_edit,
        fixture.target_certificate_hash,
        fixture.package_snapshot_hash,
    )
}

fn scenario_json(run: &ScenarioRun) -> Result<String, String> {
    let wall = run
        .samples
        .iter()
        .map(|sample| sample.measurement.wall_ns)
        .collect::<Vec<_>>();
    let rss = run
        .samples
        .iter()
        .map(|sample| sample.measurement.peak_rss_kib)
        .collect::<Vec<_>>();
    let wall_stats = statistics(&wall)?;
    let rss_stats = statistics(&rss)?;
    let lookup = run
        .samples
        .iter()
        .map(|sample| sample.cache_lookup_ms)
        .collect::<Vec<_>>();
    let cache_sizes = run
        .samples
        .iter()
        .map(|sample| sample.cache_size_bytes)
        .collect::<Vec<_>>();
    let samples = run
        .samples
        .iter()
        .map(|sample| {
            format!(
                "{{\"wall_ns\":{},\"peak_rss_kib\":{},\"cache_lookup_ms\":{},\"cache_size_bytes\":{},\"deterministic_counters\":{},\"common_cache_measurements\":{}}}",
                sample.measurement.wall_ns,
                sample.measurement.peak_rss_kib,
                sample.cache_lookup_ms,
                sample.cache_size_bytes,
                counters_json(&sample.counters.values),
                counters_json(&sample.common_measurements),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let compiler_options = run
        .compiler_options
        .iter()
        .map(|option| format!("\"{}\"", json_escape(option)))
        .collect::<Vec<_>>()
        .join(",");
    let support_cache_keys = string_map_json(&run.support_cache_keys);
    let authoring_abis = string_map_json(&run.authoring_abis);
    let common_summaries = common_measurement_summaries_json(&run.samples)?;
    let expected = expected_counters(run.scenario.size, run.scenario.policy);
    Ok(format!(
        "{{\"id\":\"{}\",\"fixture_size\":\"{}\",\"cache_policy\":\"{}\",\"support_cache_keys\":{},\"support_executable_hash\":\"{}\",\"authoring_abis\":{},\"compiler_options\":[{}],\"samples\":[{}],\"wall_summary_ns\":{},\"peak_rss_summary_kib\":{},\"cache_lookup_summary_ms\":{},\"cache_size_summary_bytes\":{},\"common_cache_measurement_summaries\":{},\"invariants\":{{\"same_selected_target\":true,\"same_certificate_bytes\":true,\"every_target_fresh\":true,\"target_attempts\":{},\"target_fresh_builds\":{},\"targets_forced_live\":{},\"retained_context_hits\":{},\"bypassed_context_hits\":{},\"live_context_misses\":{},\"avoided_kernel_checks\":{},\"avoided_source_interface_resolutions\":{},\"persistent_cache_distinct_from_process_global_memo\":true}},\"status\":\"passed\"}}",
        run.scenario.id,
        run.scenario.size.label(),
        run.scenario.policy.label(),
        support_cache_keys,
        run.executable_hash,
        authoring_abis,
        compiler_options,
        samples,
        stats_json(wall_stats),
        stats_json(rss_stats),
        stats_json(statistics(&lookup)?),
        stats_json(statistics(&cache_sizes)?),
        common_summaries,
        expected.values["target_attempts"],
        expected.values["target_fresh_builds"],
        expected.values["targets_forced_live"],
        expected.values["context_hits"],
        expected.values["context_bypassed_hits"],
        expected.values["context_misses"],
        expected.values["avoided_kernel_checks"],
        expected.values["avoided_source_interface_resolutions"],
    ))
}

fn common_measurement_summaries_json(samples: &[Sample]) -> Result<String, String> {
    let labels = samples
        .first()
        .ok_or("scenario has no samples")?
        .common_measurements
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let fields = labels
        .iter()
        .map(|label| -> Result<String, String> {
            let values = samples
                .iter()
                .map(|sample| sample.common_measurements[label])
                .collect::<Vec<_>>();
            Ok(format!(
                "\"{}\":{}",
                json_escape(label),
                stats_json(statistics(&values)?)
            ))
        })
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    Ok(format!("{{{fields}}}"))
}

fn string_map_json(values: &BTreeMap<String, String>) -> String {
    let fields = values
        .iter()
        .map(|(name, value)| format!("\"{}\":\"{}\"", json_escape(name), json_escape(value)))
        .collect::<Vec<_>>()
        .join(",");
    format!("{{{fields}}}")
}

fn counters_json(counters: &BTreeMap<String, u64>) -> String {
    let fields = counters
        .iter()
        .map(|(label, value)| format!("\"{}\":{}", json_escape(label), value))
        .collect::<Vec<_>>()
        .join(",");
    format!("{{{fields}}}")
}

fn stats_json(statistics: Statistics) -> String {
    format!(
        "{{\"median\":{},\"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}}",
        statistics.median,
        statistics.median_absolute_deviation,
        statistics.minimum,
        statistics.maximum,
    )
}

fn decode_build_hex(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("build rustc metadata hex has odd length".to_owned());
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
        _ => Err("build rustc metadata contains invalid hex".to_owned()),
    }
}

fn unique_child(owner: &ClosedPrivateDirectory, label: &str) -> Result<PathBuf, String> {
    let relative = PathBuf::from(label);
    owner.create_directory(&relative)?;
    Ok(relative)
}

fn hash_file(path: &Path) -> Result<String, String> {
    read_invocation_regular_file(path, MAX_EXECUTABLE_BYTES, "TBAC identity file")
        .map(|bytes| hash_bytes(&bytes))
}

fn hash_bytes(bytes: &[u8]) -> String {
    format_package_hash(&package_file_hash(bytes))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."))
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = Vec::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(DIGITS[usize::from(byte >> 4)]);
        output.push(DIGITS[usize::from(byte & 0x0f)]);
    }
    String::from_utf8(output).unwrap_or_default()
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
                escaped.push_str(&format!("\\u{:04x}", u32::from(character)));
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
mod private_root_tests {
    use super::*;
    use std::fs;

    #[test]
    fn targeted_build_json_escape_round_trips_all_control_characters() {
        let source = (0_u8..=0x1f)
            .map(char::from)
            .chain(['"', '\\', 'x'])
            .collect::<String>();
        let encoded = format!("{{\"value\":\"{}\"}}", json_escape(&source));
        let document = JsonDocument::parse(&encoded).unwrap();
        assert_eq!(
            json_text(json_field(document.root(), "value").unwrap()).unwrap(),
            source
        );
        assert!(encoded.contains("\\u001f"));
        assert!(encoded.contains("\\u0000"));
    }

    #[cfg(unix)]
    #[test]
    fn targeted_build_private_root_rejects_symlink_parent() {
        use std::os::unix::fs::symlink;

        let container = ClosedPrivateDirectory::new("npa-tbac-test-container").unwrap();
        let link = container.path().join("parent-link");
        symlink(container.path(), &link).unwrap();
        let error = match ClosedPrivateDirectory::new_in(&link, "npa-tbac-child") {
            Ok(_) => panic!("symlink temporary parent was accepted"),
            Err(error) => error,
        };
        assert_eq!(error, "temporary parent is not a real directory");
    }

    #[cfg(unix)]
    #[test]
    fn targeted_build_private_root_drop_rejects_path_replacement() {
        let root = ClosedPrivateDirectory::new("npa-tbac-replacement-test").unwrap();
        let original = root.path().to_path_buf();
        let relocated = original.with_extension("original-directory");
        fs::rename(&original, &relocated).unwrap();
        fs::create_dir(&original).unwrap();

        drop(root);

        assert!(original.is_dir(), "replacement directory must survive Drop");
        assert!(
            relocated.is_dir(),
            "original directory must survive relocation"
        );
        fs::remove_dir(&original).unwrap();
        fs::remove_dir(&relocated).unwrap();
    }
}

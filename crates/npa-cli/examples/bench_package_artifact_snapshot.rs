//! Closed SNAP raw/operation-owned-artifact performance harness.
//!
//! Workload generation and cache prepopulation are outside the internal
//! sample intervals. The repository controller may wrap this executable with
//! `measure_process`; the verifier remains in this direct child process.

#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "../../npa-api/examples/support/performance_fixture_generator.rs"]
mod performance_fixture_generator;
#[path = "../../npa-api/examples/support/runtime_source_set.rs"]
mod runtime_source_set;

use std::{
    alloc::{GlobalAlloc, Layout, System},
    collections::BTreeMap,
    num::{NonZeroU64, NonZeroUsize},
    path::{Path, PathBuf},
    sync::atomic::{AtomicBool, AtomicU64, Ordering},
    time::Instant,
};

use npa_api::{
    clear_package_import_context_export_disk_cache, clear_package_verification_decode_cache,
    validate_checked_performance_fixture_selection_v02,
    verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation_indexed,
    verify_package_fast_source_free_with_options_indexed, JsonDocument, JsonValue,
    PackageCertificateArtifact, PackageCertificateArtifactObservation,
    PackageVerificationDecodeCacheMode, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PackageVerificationProcessMemoHandle,
    PackageVerificationProcessMemoLimits, PerformanceFixtureArtifactMode,
    PerformanceFixtureAuditCachePolicy, PerformanceFixtureDecodeCachePolicy,
    PerformanceFixtureDiskMemoPolicy, PerformanceFixtureExecutionLane,
    PerformanceFixtureProcessMemoPolicy, PerformanceFixtureSelectionV02,
    PerformanceFixtureVerifier, PerformanceMeasurementCounter, PerformanceMeasurementLabel,
    PerformanceMeasurementMode, PerformanceMeasurementUnit,
};
use npa_cert::CertificatePayloadObservation;
use npa_cli::{
    args::{PackageAuditCacheMode, PackageChecker, PackageTimingMode, PackageVerifierMemoMode},
    package_api::v1,
    package_verify::{benchmark_run_package_verify_certs, PackageArtifactSnapshotBenchmarkMode},
};
use npa_package::{
    build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation,
    parse_and_validate_manifest_str, OwnedPackageLockArtifact,
    PackageArtifactPreparationObservation, PackagePath, PreparedArtifactObservationMode,
    PreparedArtifactRetentionObservation, PreparedArtifactRetentionPolicy,
    PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR,
};
use sha2::{Digest, Sha256};

use closed_private_tree::{
    consume_inherited_detached_executable, read_invocation_regular_file, ClosedPrivateDirectory,
};
use runtime_source_set::{validate_runtime_source_identity, validate_runtime_source_set};

const SAMPLE_SCHEMA: &str = "npa.package_artifact_snapshot.benchmark_sample.v2";
const BASELINE_SCHEMA: &str = "npa.performance.baselines.v0.1";
const BASELINE_MEASUREMENT_SCHEMA: &str = "npa.performance.measurements.v0.9";
const BASELINE_UPDATE_POLICY: &str = "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request. Raw elapsed time and peak RSS are advisory evidence and must never be copied into this generic deterministic baseline.";
const MANIFEST_PATH: &str = "npa-package.toml";
const MAX_MANIFEST_BYTES: u64 = 4 * 1024 * 1024;
const MAX_BASELINE_BYTES: u64 = 16 * 1024 * 1024;
const MAX_ORACLE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_SOURCE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;
const SNAPSHOT_COUNTER_CATALOG: [(PerformanceMeasurementLabel, PerformanceMeasurementUnit); 19] = [
    (
        PerformanceMeasurementLabel::PackageArtifactFileHashes,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackageArtifactFilesRead,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackageArtifactFullDecodes,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackageArtifactPreparedReuses,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactAdmissions,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactAdmittedBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactByteLimitFallbacks,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactCurrentBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactCurrentEntries,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactDerivationCurrentBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactDerivationPeakBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactEntryLimitFallbacks,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactKeyCurrentBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactKeyPeakBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactPeakBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactPeakEntries,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactReleasedBytes,
        PerformanceMeasurementUnit::Bytes,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactReleases,
        PerformanceMeasurementUnit::Count,
    ),
    (
        PerformanceMeasurementLabel::PackagePreparedArtifactSaturatedChargeFallbacks,
        PerformanceMeasurementUnit::Count,
    ),
];
struct TrackingAllocator;
static TRACK_ALLOCATIONS: AtomicBool = AtomicBool::new(false);
static ALLOCATION_EVENTS: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_BYTES: AtomicU64 = AtomicU64::new(0);

#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let result = unsafe { System.alloc(layout) };
        if !result.is_null() {
            observe_allocation(layout.size());
        }
        result
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let result = unsafe { System.alloc_zeroed(layout) };
        if !result.is_null() {
            observe_allocation(layout.size());
        }
        result
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let result = unsafe { System.realloc(pointer, layout, size) };
        if !result.is_null() {
            observe_allocation(size);
        }
        result
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) };
    }
}

fn observe_allocation(bytes: usize) {
    if TRACK_ALLOCATIONS.load(Ordering::Relaxed) {
        ALLOCATION_EVENTS.fetch_add(1, Ordering::Relaxed);
        ALLOCATED_BYTES.fetch_add(u64::try_from(bytes).unwrap_or(u64::MAX), Ordering::Relaxed);
    }
}

#[derive(Clone, Debug)]
struct Arguments {
    scenario: String,
    manifest: PathBuf,
    baseline: PathBuf,
    oracle: PathBuf,
    source_identity: String,
    sample_index: u64,
}

#[derive(Clone, Debug)]
struct Sample {
    elapsed_ns: u64,
    acquisition_ns: u64,
    checker_ns: u64,
    allocation_events: u64,
    allocated_bytes: u64,
    counters: BTreeMap<String, u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BaselineExpectation {
    module_count: u64,
    counters: BTreeMap<String, u64>,
}

struct CurrentDirectoryGuard(PathBuf);

impl CurrentDirectoryGuard {
    fn enter(path: &Path) -> Result<Self, String> {
        let previous = std::env::current_dir().map_err(display_error)?;
        std::env::set_current_dir(path).map_err(display_error)?;
        Ok(Self(previous))
    }
}

impl Drop for CurrentDirectoryGuard {
    fn drop(&mut self) {
        let _ = std::env::set_current_dir(&self.0);
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("snapshot benchmark failed: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let raw_args = std::env::args().skip(1).collect::<Vec<_>>();
    if raw_args == ["--list"] {
        let source = String::from_utf8(read_invocation_regular_file(
            Path::new("testdata/performance/fixtures/manifest.v0.2.json"),
            MAX_MANIFEST_BYTES,
            "performance fixture manifest",
        )?)
        .map_err(display_error)?;
        for row in snapshot_rows(&source)? {
            println!("{}", row.common.id);
        }
        return Ok(());
    }
    let inherited_executable = consume_inherited_benchmark_executable()?;
    if raw_args == ["--npa-build-descriptor"] {
        println!("{}", benchmark_build_descriptor()?);
        return Ok(());
    }
    let args = parse_arguments(&raw_args)?;
    if env!("NPA_CLI_BUILD_SOURCE_REVISION") == "unbound"
        || env!("NPA_CLI_BUILD_SOURCE_REVISION") != args.source_identity
    {
        return Err("caller source identity differs from the bound benchmark build".to_owned());
    }
    let workspace = workspace_root()?;
    validate_runtime_source_identity(&workspace, &args.source_identity)?;
    let manifest_source = String::from_utf8(read_invocation_regular_file(
        &args.manifest,
        MAX_MANIFEST_BYTES,
        "performance fixture manifest",
    )?)
    .map_err(display_error)?;
    require_embedded_input_hash(
        "performance fixture manifest",
        manifest_source.as_bytes(),
        env!("NPA_CLI_BUILD_PERFORMANCE_MANIFEST_V02_SHA256"),
    )?;
    let row = select_row(&manifest_source, &args.scenario)?;
    let baseline_source = String::from_utf8(read_invocation_regular_file(
        &args.baseline,
        MAX_BASELINE_BYTES,
        "performance baseline",
    )?)
    .map_err(display_error)?;
    require_embedded_input_hash(
        "performance baseline",
        baseline_source.as_bytes(),
        env!("NPA_CLI_BUILD_PERFORMANCE_BASELINE_SHA256"),
    )?;
    let expected = baseline_expectation(&baseline_source, &args.scenario)?;

    let temporary = ClosedPrivateDirectory::new("npa-snapshot-bench")?;
    let fixture_root = resolve_package_root(&row.package_root, profile_name(row.fixture_profile))?;
    let generated = performance_fixture_generator::materialize_fixture_profile(
        profile_name(row.fixture_profile),
        &temporary,
        &fixture_root,
    )?;
    if generated.certificate_bytes != row.artifact_bytes {
        return Err(format!(
            "fixture byte mismatch: manifest={} generated={}",
            row.artifact_bytes, generated.certificate_bytes
        ));
    }
    if generated.module_count != expected.module_count {
        return Err(format!(
            "baseline module_count mismatch: expected {}, generated {}",
            expected.module_count, generated.module_count
        ));
    }
    validate_oracle(&args.oracle, &generated)?;
    let original_tree = (
        generated.artifact_tree_sha256.clone(),
        generated.tree_file_count,
    );
    let state = ScenarioState::new(row.clone(), &temporary, Path::new("row-work"))?;
    state.prepare_lifecycle(&generated)?;
    for _ in 0..row.common.warmup {
        state.run(&generated, false)?;
    }
    state.reset_after_warmup()?;
    state.prepare_sample(args.sample_index)?;
    let sample = state.run(&generated, true)?;
    validate_counters(&expected.counters, &sample.counters)?;
    let current_tree =
        performance_fixture_generator::artifact_tree_identity(&temporary, &generated)?;
    if current_tree != original_tree {
        return Err("warmup or sample mutated the generated workload tree".to_owned());
    }
    let output = render_sample(
        &args,
        &row,
        &generated,
        &sample,
        &workspace,
        &inherited_executable,
    )?;
    state.cleanup()?;
    performance_fixture_generator::remove_generated_fixture(&temporary, &generated)?;
    cleanup_snapshot_fixture_parent(&temporary)?;
    temporary.remove_empty_root()?;
    println!("{output}");
    Ok(())
}

fn benchmark_build_descriptor() -> Result<String, String> {
    let source_identity = env!("NPA_CLI_BUILD_SOURCE_REVISION");
    if source_identity == "unbound" {
        return Err("benchmark build descriptor is not source-revision-bound".to_owned());
    }
    let workspace = workspace_root()?;
    validate_runtime_source_identity(&workspace, source_identity)?;
    let source_set = validate_runtime_source_set(
        &workspace,
        env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_PATHS"),
        b"npa-snap-source-set-v1\0",
        env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_SHA256"),
        "SNAP",
    )?;
    let raw_source_set = raw_sha256(&source_set, "SNAP source set")?;
    let cargo_lock = read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SOURCE_BYTES,
        "SNAP Cargo.lock",
    )?;
    let cargo_lock_hash = hex(&Sha256::digest(cargo_lock));
    if cargo_lock_hash != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime SNAP Cargo.lock differs from its benchmark build".to_owned());
    }
    let features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"npa.performance.benchmark-build.v1\",\"lane_id\":\"package-artifact-snapshot\",\"source_identity\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"features\":[{features}],\"rustc_vv\":\"{}\",\"rustflags\":\"{}\",\"harness_source_sha256\":\"{}\",\"source_set_sha256\":\"{}\",\"fixture_parser_source_sha256\":null,\"measure_process_source_sha256\":\"{}\"}}",
        json_escape(source_identity),
        cargo_lock_hash,
        env!("NPA_CLI_BUILD_CARGO_PROFILE"),
        env!("NPA_CLI_BUILD_TARGET"),
        json_escape(&decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?),
        json_escape(&decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?),
        env!("NPA_CLI_BUILD_SNAPSHOT_HARNESS_SOURCE_SHA256"),
        raw_source_set,
        env!("NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
    ))
}

struct ScenarioState<'a> {
    row: npa_api::PackageArtifactSnapshotFixture,
    process_memo: Option<PackageVerificationProcessMemoHandle>,
    owner: &'a ClosedPrivateDirectory,
    work_relative: PathBuf,
    work_root: PathBuf,
}

impl<'a> ScenarioState<'a> {
    fn new(
        row: npa_api::PackageArtifactSnapshotFixture,
        owner: &'a ClosedPrivateDirectory,
        work_relative: &Path,
    ) -> Result<Self, String> {
        owner.create_directory(work_relative)?;
        let process_memo = process_memo_handle(row.process_memo_policy)?;
        Ok(Self {
            row,
            process_memo,
            owner,
            work_relative: work_relative.to_path_buf(),
            work_root: owner.path().join(work_relative),
        })
    }

    fn in_work_root<T>(&self, run: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        let _guard = CurrentDirectoryGuard::enter(&self.work_root)?;
        run()
    }

    fn prepare_lifecycle(
        &self,
        generated: &performance_fixture_generator::GeneratedFixtureProfile,
    ) -> Result<(), String> {
        self.in_work_root(|| prepare_lifecycle(&self.row, generated, self.process_memo.as_ref()))
    }

    fn reset_after_warmup(&self) -> Result<(), String> {
        self.in_work_root(|| {
            reset_after_warmup(
                &self.row,
                self.process_memo.as_ref(),
                self.owner,
                &self.work_relative,
            )
        })
    }

    fn prepare_sample(&self, sample_index: u64) -> Result<(), String> {
        self.in_work_root(|| {
            prepare_sample(&self.row, sample_index, self.owner, &self.work_relative)
        })
    }

    fn run(
        &self,
        generated: &performance_fixture_generator::GeneratedFixtureProfile,
        measured: bool,
    ) -> Result<Sample, String> {
        self.in_work_root(|| run_one(&self.row, generated, self.process_memo.as_ref(), measured))
    }

    fn cleanup(&self) -> Result<(), String> {
        let (files, directories) = self.owner.catalog_subtree_paths(&self.work_relative)?;
        validate_snapshot_work_catalog(&self.work_relative, &files, &directories)?;
        self.owner
            .remove_exact_subtree(&self.work_relative, &files, &directories)
    }
}

fn parse_arguments(args: &[String]) -> Result<Arguments, String> {
    let mut values = BTreeMap::<&str, String>::new();
    let mut index = 0;
    while index < args.len() {
        let name = args[index].as_str();
        if !matches!(
            name,
            "--scenario"
                | "--manifest"
                | "--baseline"
                | "--oracle"
                | "--source-identity"
                | "--sample-index"
        ) {
            return Err(format!("unknown argument: {name}"));
        }
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing {name} value"))?;
        if values.insert(name, value.clone()).is_some() {
            return Err(format!("duplicate {name}"));
        }
        index += 2;
    }
    let take = |name| {
        values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing {name}"))
    };
    let result = Arguments {
        scenario: take("--scenario")?,
        manifest: PathBuf::from(take("--manifest")?),
        baseline: PathBuf::from(take("--baseline")?),
        oracle: PathBuf::from(take("--oracle")?),
        source_identity: take("--source-identity")?,
        sample_index: take("--sample-index")?
            .parse::<u64>()
            .map_err(display_error)?,
    };
    if !valid_source_identity(&result.source_identity) {
        return Err(
            "source identity must be a lowercase 40-digit Git OID with optional -dirty suffix"
                .to_owned(),
        );
    }
    if result.sample_index >= 5 {
        return Err("--sample-index must be in 0..5".to_owned());
    }
    Ok(result)
}

fn require_embedded_input_hash(label: &str, bytes: &[u8], expected: &str) -> Result<(), String> {
    if hex(&Sha256::digest(bytes)) == expected {
        Ok(())
    } else {
        Err(format!("{label} differs from the locked benchmark input"))
    }
}

fn snapshot_rows(source: &str) -> Result<Vec<npa_api::PackageArtifactSnapshotFixture>, String> {
    let parsed =
        validate_checked_performance_fixture_selection_v02(source).map_err(display_error)?;
    Ok(parsed
        .scenarios
        .iter()
        .filter_map(|row| match row {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(row) => Some(row.clone()),
            _ => None,
        })
        .collect())
}

fn select_row(
    source: &str,
    scenario: &str,
) -> Result<npa_api::PackageArtifactSnapshotFixture, String> {
    let rows = snapshot_rows(source)?;
    let mut matches = rows.into_iter().filter(|row| row.common.id == scenario);
    let selected = matches
        .next()
        .ok_or_else(|| format!("snapshot scenario is absent: {scenario}"))?;
    if matches.next().is_some() {
        return Err(format!("snapshot scenario is duplicated: {scenario}"));
    }
    if selected.common.measurement_mode.as_str() != "detailed"
        || selected.common.warmup != 1
        || selected.common.samples != 5
    {
        return Err("selected row does not use the closed detailed/1/5 envelope".to_owned());
    }
    Ok(selected)
}

#[cfg(test)]
fn select_snapshot_companion(
    source: &str,
    selected: &npa_api::PackageArtifactSnapshotFixture,
) -> Result<npa_api::PackageArtifactSnapshotFixture, String> {
    let rows = snapshot_rows(source)?;
    let mut matches = rows.into_iter().filter(|row| {
        row.common.interleave_group == selected.common.interleave_group
            && row.artifact_mode != selected.artifact_mode
    });
    let companion = matches
        .next()
        .ok_or("selected snapshot scenario has no paired companion")?;
    if matches.next().is_some() {
        return Err("selected snapshot scenario has multiple paired companions".to_owned());
    }
    Ok(companion)
}

fn resolve_package_root(relative: &str, profile: &str) -> Result<PathBuf, String> {
    let path = Path::new(relative);
    let expected = Path::new("generated").join(profile);
    if path != expected
        || path.is_absolute()
        || path.components().count() != 2
        || path
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(
            "SNAP package_root must be the exact generated/<fixture_profile> path".to_owned(),
        );
    }
    Ok(path.to_path_buf())
}

fn cleanup_snapshot_fixture_parent(owner: &ClosedPrivateDirectory) -> Result<(), String> {
    let parent = Path::new("generated");
    let (files, directories) = owner.catalog_subtree_paths(parent)?;
    if !files.is_empty() || directories != std::collections::BTreeSet::from([parent.to_path_buf()])
    {
        return Err(
            "SNAP generated fixture parent contains an unexpected retained entry".to_owned(),
        );
    }
    owner.remove_exact_subtree(parent, &files, &directories)
}

fn profile_name(profile: npa_api::PerformanceFixtureProfile) -> &'static str {
    profile.as_str()
}

fn validate_oracle(
    path: &Path,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
) -> Result<(), String> {
    let source = String::from_utf8(read_invocation_regular_file(
        path,
        MAX_ORACLE_BYTES,
        "fixture oracle",
    )?)
    .map_err(display_error)?;
    require_embedded_input_hash(
        "fixture oracle",
        source.as_bytes(),
        env!("NPA_CLI_BUILD_FIXTURE_ORACLE_SHA256"),
    )?;
    let mut lines = source.lines();
    if lines.next() != Some(performance_fixture_generator::ORACLE_TSV_HEADER) {
        return Err("fixture oracle header mismatch".to_owned());
    }
    let prefix = format!(
        "{}\t{}\t",
        performance_fixture_generator::GENERATOR_SCHEMA,
        generated.profile
    );
    let mut matches = lines.filter(|line| line.starts_with(&prefix));
    let row = matches.next().ok_or("fixture oracle row is missing")?;
    if matches.next().is_some() || row != generated.oracle_tsv_row() {
        return Err("fixture oracle identity mismatch".to_owned());
    }
    Ok(())
}

fn process_memo_handle(
    mode: PerformanceFixtureProcessMemoPolicy,
) -> Result<Option<PackageVerificationProcessMemoHandle>, String> {
    match mode {
        PerformanceFixtureProcessMemoPolicy::Disabled => Ok(None),
        PerformanceFixtureProcessMemoPolicy::ProcessLocal => Ok(Some(
            PackageVerificationProcessMemoHandle::new(PackageVerificationProcessMemoLimits {
                max_entries: NonZeroUsize::new(1_024).ok_or("memo entry limit is zero")?,
                max_weighted_certificate_bytes: NonZeroU64::new(536_870_912)
                    .ok_or("memo byte limit is zero")?,
            }),
        )),
        _ => Err("fixture selected a future process-memo policy".to_owned()),
    }
}

fn prepare_lifecycle(
    row: &npa_api::PackageArtifactSnapshotFixture,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
    process_memo: Option<&PackageVerificationProcessMemoHandle>,
) -> Result<(), String> {
    if let Some(handle) = process_memo {
        handle.clear().map_err(debug_error)?;
    }
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    match (
        row.execution_lane,
        row.audit_cache_policy,
        row.disk_memo_policy,
    ) {
        (
            PerformanceFixtureExecutionLane::CliLocal,
            PerformanceFixtureAuditCachePolicy::LocalHit,
            _,
        ) => {
            let mut populate = row.clone();
            populate.audit_cache_policy = PerformanceFixtureAuditCachePolicy::ReadThrough;
            run_one(&populate, generated, process_memo, false)?;
        }
        (PerformanceFixtureExecutionLane::CliLocal, _, PerformanceFixtureDiskMemoPolicy::Disk) => {
            let mut populate = row.clone();
            populate.disk_memo_policy = PerformanceFixtureDiskMemoPolicy::ReadThrough;
            run_one(&populate, generated, process_memo, false)?;
        }
        _ => {}
    }
    Ok(())
}

fn reset_after_warmup(
    row: &npa_api::PackageArtifactSnapshotFixture,
    _process_memo: Option<&PackageVerificationProcessMemoHandle>,
    owner: &ClosedPrivateDirectory,
    work_relative: &Path,
) -> Result<(), String> {
    if row.execution_lane == PerformanceFixtureExecutionLane::CliLocal
        && (row.audit_cache_policy == PerformanceFixtureAuditCachePolicy::ReadThrough
            || row.disk_memo_policy == PerformanceFixtureDiskMemoPolicy::ReadThrough)
    {
        reset_cli_readthrough(row, owner, work_relative)?;
    }
    Ok(())
}

fn prepare_sample(
    row: &npa_api::PackageArtifactSnapshotFixture,
    sample_index: u64,
    owner: &ClosedPrivateDirectory,
    work_relative: &Path,
) -> Result<(), String> {
    if sample_index > 0
        && row.execution_lane == PerformanceFixtureExecutionLane::CliLocal
        && (row.audit_cache_policy == PerformanceFixtureAuditCachePolicy::ReadThrough
            || row.disk_memo_policy == PerformanceFixtureDiskMemoPolicy::ReadThrough)
    {
        reset_cli_readthrough(row, owner, work_relative)?;
    }
    Ok(())
}

fn reset_cli_readthrough(
    row: &npa_api::PackageArtifactSnapshotFixture,
    owner: &ClosedPrivateDirectory,
    work_relative: &Path,
) -> Result<(), String> {
    let relative = if row.audit_cache_policy == PerformanceFixtureAuditCachePolicy::ReadThrough {
        PACKAGE_AUDIT_CACHE_LAYOUT_DIR
    } else {
        PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR
    };
    let target = work_relative.join(relative);
    match owner.catalog_subtree_paths(&target) {
        Ok((files, directories)) => {
            validate_snapshot_cache_catalog(&target, &files, &directories)?;
            owner.remove_exact_subtree(&target, &files, &directories)?;
        }
        Err(error) if error.contains("No such file") || error.contains("not found") => {}
        Err(error) => return Err(error),
    }
    owner.create_directories(&target)
}

fn validate_snapshot_work_catalog(
    work_relative: &Path,
    files: &std::collections::BTreeSet<PathBuf>,
    directories: &std::collections::BTreeSet<PathBuf>,
) -> Result<(), String> {
    let allowed_directories = [
        work_relative.to_path_buf(),
        work_relative.join("target"),
        work_relative.join("target/npa-package-audit-cache"),
        work_relative.join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR),
        work_relative.join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR),
        work_relative.join("target/npa-package-audit-cache/import-context-export-v0.2"),
    ]
    .into_iter()
    .collect::<std::collections::BTreeSet<_>>();
    for directory in directories {
        if !allowed_directories.contains(directory) {
            return Err(format!(
                "snapshot work tree contains an unexpected directory: {}",
                directory.display()
            ));
        }
    }
    for file in files {
        validate_snapshot_cache_file(work_relative, file)?;
    }
    Ok(())
}

fn validate_snapshot_cache_catalog(
    target: &Path,
    files: &std::collections::BTreeSet<PathBuf>,
    directories: &std::collections::BTreeSet<PathBuf>,
) -> Result<(), String> {
    if !directories.iter().all(|path| path.starts_with(target))
        || !files.iter().all(|path| path.starts_with(target))
    {
        return Err("snapshot cache catalog escaped its selected cache root".to_owned());
    }
    let work_relative = Path::new("row-work");
    validate_snapshot_work_catalog(work_relative, files, directories)?;
    for file in files {
        validate_snapshot_cache_file(work_relative, file)?;
    }
    Ok(())
}

fn validate_snapshot_cache_file(work_relative: &Path, file: &Path) -> Result<(), String> {
    if !file.starts_with(work_relative.join("target/npa-package-audit-cache")) {
        return Err(format!(
            "snapshot work tree contains an unexpected file: {}",
            file.display()
        ));
    }
    let allowed_parents = [
        work_relative.join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR),
        work_relative.join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR),
        work_relative.join("target/npa-package-audit-cache/import-context-export-v0.2"),
    ];
    if !allowed_parents
        .iter()
        .any(|parent| file.parent() == Some(parent.as_path()))
    {
        return Err("snapshot cache file is outside an exact cache leaf".to_owned());
    }
    let name = file
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("snapshot cache filename is not UTF-8")?;
    let stem = name
        .strip_suffix(".json")
        .ok_or("snapshot cache filename does not end in .json")?;
    if stem.len() != 71
        || !stem.starts_with("sha256:")
        || !stem[7..]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("snapshot cache filename is not an exact package hash".to_owned());
    }
    Ok(())
}

fn run_one(
    row: &npa_api::PackageArtifactSnapshotFixture,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
    process_memo: Option<&PackageVerificationProcessMemoHandle>,
    measured: bool,
) -> Result<Sample, String> {
    ALLOCATION_EVENTS.store(0, Ordering::Relaxed);
    ALLOCATED_BYTES.store(0, Ordering::Relaxed);
    TRACK_ALLOCATIONS.store(measured, Ordering::SeqCst);
    let started = Instant::now();
    let result = match row.execution_lane {
        PerformanceFixtureExecutionLane::CliLocal => run_cli(row, generated),
        PerformanceFixtureExecutionLane::Api => run_api(row, generated, process_memo),
        _ => Err("fixture selected a future execution lane".to_owned()),
    };
    let elapsed_ns = nanos(started.elapsed().as_nanos());
    TRACK_ALLOCATIONS.store(false, Ordering::SeqCst);
    let mut sample = result?;
    sample.elapsed_ns = elapsed_ns;
    sample.allocation_events = ALLOCATION_EVENTS.load(Ordering::Relaxed);
    sample.allocated_bytes = ALLOCATED_BYTES.load(Ordering::Relaxed);
    Ok(sample)
}

fn run_cli(
    row: &npa_api::PackageArtifactSnapshotFixture,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
) -> Result<Sample, String> {
    let checker = match row.verifier {
        PerformanceFixtureVerifier::Fast => PackageChecker::Fast,
        PerformanceFixtureVerifier::Reference => PackageChecker::Reference,
        _ => return Err("fixture selected a future verifier".to_owned()),
    };
    let audit = match row.audit_cache_policy {
        PerformanceFixtureAuditCachePolicy::Off => PackageAuditCacheMode::Off,
        PerformanceFixtureAuditCachePolicy::ReadThrough => PackageAuditCacheMode::ReadThrough,
        PerformanceFixtureAuditCachePolicy::LocalHit => PackageAuditCacheMode::LocalHit,
        _ => return Err("fixture selected a future audit-cache policy".to_owned()),
    };
    let disk = match row.disk_memo_policy {
        PerformanceFixtureDiskMemoPolicy::Off => PackageVerifierMemoMode::Off,
        PerformanceFixtureDiskMemoPolicy::ReadThrough => PackageVerifierMemoMode::ReadThrough,
        PerformanceFixtureDiskMemoPolicy::Disk => PackageVerifierMemoMode::Disk,
        _ => return Err("fixture selected a future disk-memo policy".to_owned()),
    };
    let options = v1::verify_certs_full(v1::common_options(&generated.root, false), checker)
        .with_audit_cache(audit)
        .with_verifier_memo(disk)
        .with_jobs(usize::try_from(row.jobs).map_err(display_error)?)
        .with_timings(PackageTimingMode::Detailed);
    let mode = match row.artifact_mode {
        PerformanceFixtureArtifactMode::Raw => PackageArtifactSnapshotBenchmarkMode::Raw,
        PerformanceFixtureArtifactMode::Snapshot => PackageArtifactSnapshotBenchmarkMode::Snapshot,
        _ => return Err("fixture selected a future artifact mode".to_owned()),
    };
    let result = benchmark_run_package_verify_certs(options, mode);
    if result.status.as_str() != "passed" {
        return Err(format!("CLI verification failed: {}", result.render_json()));
    }
    let timings = result
        .timings
        .as_ref()
        .ok_or("detailed CLI result omitted timings")?;
    if timings.mode != "detailed" {
        return Err("CLI detailed mode was not preserved".to_owned());
    }
    let acquisition_ns = timing_ns(timings, "decode_certificates_ms")
        .saturating_add(timing_ns(timings, "build_graph_ms"));
    let checker_ns = timing_ns(timings, "checker_ms");
    let counters = project_snapshot_counters(
        timings
            .measurements
            .as_ref()
            .ok_or("detailed CLI result omitted common measurements")?,
    )?;
    validate_snapshot_counter_catalog(&counters)?;
    Ok(Sample {
        elapsed_ns: 0,
        acquisition_ns,
        checker_ns,
        allocation_events: 0,
        allocated_bytes: 0,
        counters,
    })
}

fn run_api(
    row: &npa_api::PackageArtifactSnapshotFixture,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
    process_memo: Option<&PackageVerificationProcessMemoHandle>,
) -> Result<Sample, String> {
    let manifest_source = String::from_utf8(read_invocation_regular_file(
        &generated.root.join(MANIFEST_PATH),
        MAX_MANIFEST_BYTES,
        "generated package manifest",
    )?)
    .map_err(display_error)?;
    let validated = parse_and_validate_manifest_str(&manifest_source).map_err(debug_error)?;
    let owned = generated.modules.iter().map(|module| {
        OwnedPackageLockArtifact::from_vec(
            PackagePath::new(module.certificate_path.clone()),
            module.certificate_bytes.clone(),
        )
    });
    let retention_policy =
        if row.artifact_mode == PerformanceFixtureArtifactMode::Snapshot && row.jobs == 1 {
            PreparedArtifactRetentionPolicy::FastCandidateV1
        } else {
            PreparedArtifactRetentionPolicy::RawOnly
        };
    let mut preparation = PackageArtifactPreparationObservation::default();
    let mut payload = CertificatePayloadObservation::default();
    let acquisition_started = Instant::now();
    let (indexed, mut prepared) =
        build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
            &validated,
            PackagePath::new(MANIFEST_PATH),
            manifest_source.as_bytes(),
            owned,
            retention_policy,
            PreparedArtifactObservationMode::Aggregate,
            Some(&mut preparation),
            Some(&mut payload),
        )
        .map_err(debug_error)?;
    let acquisition_ns = nanos(acquisition_started.elapsed().as_nanos());
    let mut artifact_observation = PackageCertificateArtifactObservation::default();
    artifact_observation.merge_preparation(preparation);
    let options = PackageVerificationExecutionOptions {
        jobs: usize::try_from(row.jobs).map_err(display_error)?,
        selected_modules: None,
        memoization: match row.process_memo_policy {
            PerformanceFixtureProcessMemoPolicy::Disabled => PackageVerificationMemoMode::Disabled,
            PerformanceFixtureProcessMemoPolicy::ProcessLocal => {
                PackageVerificationMemoMode::ProcessLocal(
                    process_memo
                        .ok_or("process-local row has no memo handle")?
                        .clone(),
                )
            }
            _ => return Err("fixture selected a future process-memo policy".to_owned()),
        },
        decode_cache: match row.decode_cache_policy {
            PerformanceFixtureDecodeCachePolicy::Disabled => {
                PackageVerificationDecodeCacheMode::Disabled
            }
            PerformanceFixtureDecodeCachePolicy::ProcessLocal => {
                PackageVerificationDecodeCacheMode::ProcessLocal
            }
            PerformanceFixtureDecodeCachePolicy::ProcessLocalAndPersistent => {
                PackageVerificationDecodeCacheMode::ProcessLocalAndPersistent
            }
            _ => return Err("fixture selected a future decode-cache policy".to_owned()),
        },
        collect_decode_cache_counters: true,
        measurement_mode: PerformanceMeasurementMode::Detailed,
    };
    let checker_started = Instant::now();
    let used_prepared_entry =
        row.artifact_mode == PerformanceFixtureArtifactMode::Snapshot && row.jobs == 1;
    let report = if used_prepared_entry {
        verify_package_fast_source_free_with_artifact_snapshots_and_options_and_observation_indexed(
            &validated,
            &indexed,
            &mut prepared,
            options,
            Some(&mut artifact_observation),
        )
    } else {
        verify_package_fast_source_free_with_options_indexed(
            &validated,
            &indexed,
            generated
                .modules
                .iter()
                .map(|module| PackageCertificateArtifact {
                    path: PackagePath::new(module.certificate_path.clone()),
                    bytes: &module.certificate_bytes,
                }),
            options,
        )
    }
    .map_err(debug_error)?;
    let checker_ns = nanos(checker_started.elapsed().as_nanos());
    if report.status.as_str() != "passed" {
        return Err("API verification returned a failed report".to_owned());
    }
    if !used_prepared_entry {
        let checker_decodes = report
            .measurements
            .as_ref()
            .and_then(|measurements| {
                measurements
                    .counters
                    .iter()
                    .find(|counter| counter.label.as_str() == "package.modules_decoded")
            })
            .map(|counter| counter.value)
            .unwrap_or(0);
        artifact_observation.artifact_full_decodes = artifact_observation
            .artifact_full_decodes
            .saturating_add(checker_decodes);
    }
    prepared.release_all_decoded(npa_package::PreparedArtifactReleaseReason::OperationTeardown);
    let retention = prepared.retention_observation();
    let mut counters = report
        .measurements
        .as_ref()
        .map(project_snapshot_counters)
        .transpose()?
        .unwrap_or_default();
    insert_artifact_counters(&mut counters, artifact_observation, retention);
    validate_snapshot_counter_catalog(&counters)?;
    Ok(Sample {
        elapsed_ns: 0,
        acquisition_ns,
        checker_ns,
        allocation_events: 0,
        allocated_bytes: 0,
        counters,
    })
}

fn timing_ns(timings: &npa_cli::diagnostic::CommandTimings, field: &str) -> u64 {
    timings
        .metrics
        .iter()
        .find(|metric| metric.field == field)
        .map(|metric| nanos(metric.milliseconds.saturating_mul(1_000_000)))
        .unwrap_or(0)
}

fn project_snapshot_counters(
    report: &npa_api::PerformanceMeasurementReport,
) -> Result<BTreeMap<String, u64>, String> {
    project_snapshot_counter_records(&report.counters)
}

fn project_snapshot_counter_records(
    counters: &[PerformanceMeasurementCounter],
) -> Result<BTreeMap<String, u64>, String> {
    let mut projected = BTreeMap::new();
    let mut previous = None;
    for counter in counters {
        let name = counter.label.as_str();
        if previous.is_some_and(|previous| previous >= name) {
            return Err(
                "common measurement counters must be unique and strictly ordered".to_owned(),
            );
        }
        previous = Some(name);
        if let Some((_, expected_unit)) = SNAPSHOT_COUNTER_CATALOG
            .iter()
            .find(|(label, _)| *label == counter.label)
        {
            if counter.unit != *expected_unit {
                return Err(format!("snapshot counter {name} has the wrong unit"));
            }
            if projected.insert(name.to_owned(), counter.value).is_some() {
                return Err(format!("snapshot counter {name} is duplicated"));
            }
        }
    }
    Ok(projected)
}

fn validate_snapshot_counter_catalog(counters: &BTreeMap<String, u64>) -> Result<(), String> {
    if counters.len() != SNAPSHOT_COUNTER_CATALOG.len()
        || !counters
            .keys()
            .map(String::as_str)
            .eq(SNAPSHOT_COUNTER_CATALOG
                .iter()
                .map(|(label, _)| label.as_str()))
    {
        return Err("snapshot sample has a non-canonical counter catalog".to_owned());
    }
    Ok(())
}

fn insert_artifact_counters(
    counters: &mut BTreeMap<String, u64>,
    work: PackageCertificateArtifactObservation,
    retention: Option<PreparedArtifactRetentionObservation>,
) {
    for (name, value) in [
        ("package.artifact_files_read", work.artifact_files_read),
        ("package.artifact_file_hashes", work.artifact_file_hashes),
        ("package.artifact_full_decodes", work.artifact_full_decodes),
        (
            "package.artifact_prepared_reuses",
            work.artifact_prepared_reuses,
        ),
        (
            "package.prepared_artifact_key_current_bytes",
            work.key_candidate_current_bytes,
        ),
        (
            "package.prepared_artifact_key_peak_bytes",
            work.key_candidate_peak_bytes,
        ),
    ] {
        counters.insert(name.to_owned(), value);
    }
    let retention = retention.unwrap_or_default();
    for (name, value) in [
        ("package.prepared_artifact_admissions", retention.admissions),
        (
            "package.prepared_artifact_admitted_bytes",
            retention.admitted_bytes,
        ),
        (
            "package.prepared_artifact_current_entries",
            retention.current_entries,
        ),
        (
            "package.prepared_artifact_peak_entries",
            retention.peak_entries,
        ),
        (
            "package.prepared_artifact_current_bytes",
            retention.current_bytes,
        ),
        ("package.prepared_artifact_peak_bytes", retention.peak_bytes),
        (
            "package.prepared_artifact_derivation_current_bytes",
            retention.derivation_candidate_current_bytes,
        ),
        (
            "package.prepared_artifact_derivation_peak_bytes",
            retention.derivation_candidate_peak_bytes,
        ),
        (
            "package.prepared_artifact_entry_limit_fallbacks",
            retention.entry_limit_fallbacks,
        ),
        (
            "package.prepared_artifact_byte_limit_fallbacks",
            retention.byte_limit_fallbacks,
        ),
        (
            "package.prepared_artifact_saturated_charge_fallbacks",
            retention.saturated_charge_fallbacks,
        ),
        (
            "package.prepared_artifact_releases",
            retention.charged_releases,
        ),
        (
            "package.prepared_artifact_released_bytes",
            retention.released_bytes,
        ),
    ] {
        counters.insert(name.to_owned(), value);
    }
}

fn baseline_expectation(source: &str, scenario: &str) -> Result<BaselineExpectation, String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("baseline JSON error at byte {}", error.offset))?;
    let root_members = document
        .root()
        .object_members()
        .ok_or("baseline root must be an object")?;
    let root_keys = root_members
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>();
    let expected_root_prefix = ["schema", "measurement_schema", "scenarios"];
    if !root_keys.starts_with(&expected_root_prefix)
        || root_keys.last().copied() != Some("update_policy")
        || root_keys.iter().any(|key| {
            !matches!(
                *key,
                "schema"
                    | "measurement_schema"
                    | "scenarios"
                    | "targeted_build_certs"
                    | "targeted_build_certs_rollout"
                    | "update_policy"
            )
        })
        || root_keys.windows(2).any(|pair| pair[0] == pair[1])
    {
        return Err(
            "baseline root has missing, unknown, duplicate, or reordered fields".to_owned(),
        );
    }
    if object_field(document.root(), "schema")?.string_value() != Some(BASELINE_SCHEMA) {
        return Err("baseline schema mismatch".to_owned());
    }
    if object_field(document.root(), "measurement_schema")?.string_value()
        != Some(BASELINE_MEASUREMENT_SCHEMA)
    {
        return Err("baseline measurement schema mismatch".to_owned());
    }
    if object_field(document.root(), "update_policy")?.string_value()
        != Some(BASELINE_UPDATE_POLICY)
    {
        return Err("baseline update policy mismatch".to_owned());
    }
    let scenarios = object_field(document.root(), "scenarios")?
        .array_elements()
        .ok_or("baseline.scenarios must be an array")?;
    let mut found = None;
    for row in scenarios {
        if object_field(row, "id")?.string_value() == Some(scenario) && found.replace(row).is_some()
        {
            return Err("duplicate baseline scenario".to_owned());
        }
    }
    let row = found.ok_or("baseline scenario is missing")?;
    let row_keys = row
        .object_members()
        .ok_or("baseline scenario must be an object")?
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>();
    if row_keys
        != [
            "id",
            "status",
            "module_count",
            "deterministic_counters",
            "coverage",
        ]
    {
        return Err(
            "baseline scenario has missing, unknown, duplicate, or reordered fields".to_owned(),
        );
    }
    if object_field(row, "status")?.string_value() != Some("passed") {
        return Err("baseline scenario is not passed".to_owned());
    }
    let module_count = object_field(row, "module_count")?
        .number_raw()
        .ok_or("baseline module_count must be an unsigned integer")?
        .parse::<u64>()
        .map_err(display_error)?;
    let coverage = object_field(row, "coverage")?;
    let coverage_members = coverage
        .object_members()
        .ok_or("baseline coverage must be an object")?;
    if coverage_members
        .iter()
        .map(|member| member.key())
        .collect::<Vec<_>>()
        != ["live_results_min", "proof_evidence_reduction_allowed"]
        || coverage_members[0]
            .value()
            .number_raw()
            .ok_or("baseline live_results_min must be an unsigned integer")?
            .parse::<u64>()
            .is_err()
        || coverage_members[0].value().number_raw() != Some("0")
        || coverage_members[1].value().bool_value() != Some(false)
    {
        return Err("baseline coverage has an invalid closed shape".to_owned());
    }
    let members = object_field(row, "deterministic_counters")?
        .object_members()
        .ok_or("deterministic_counters must be an object")?;
    let mut counters = BTreeMap::new();
    let mut previous = None;
    for member in members {
        if previous.is_some_and(|previous| previous >= member.key()) {
            return Err("baseline counter keys must be unique and strictly ordered".to_owned());
        }
        previous = Some(member.key());
        let raw = member
            .value()
            .number_raw()
            .ok_or("baseline counter must be unsigned integer")?;
        let value = raw.parse::<u64>().map_err(display_error)?;
        if counters.insert(member.key().to_owned(), value).is_some() {
            return Err("baseline counter key is duplicated".to_owned());
        }
    }
    if counters.len() != 19 {
        return Err("snapshot baseline must contain the exact 19-counter catalog".to_owned());
    }
    validate_snapshot_counter_catalog(&counters)?;
    Ok(BaselineExpectation {
        module_count,
        counters,
    })
}

fn validate_counters(
    expected: &BTreeMap<String, u64>,
    actual: &BTreeMap<String, u64>,
) -> Result<(), String> {
    if actual.len() != expected.len() {
        return Err("measured report counter set differs from the baseline".to_owned());
    }
    for (name, expected_value) in expected {
        let actual_value = actual
            .get(name)
            .ok_or_else(|| format!("measured report omitted baseline counter {name}"))?;
        if actual_value != expected_value {
            return Err(format!(
                "counter {name} mismatch: expected {expected_value}, actual {actual_value}"
            ));
        }
    }
    if actual != expected {
        return Err("measured report counter map differs from the baseline".to_owned());
    }
    Ok(())
}

fn object_field<'a>(value: &'a JsonValue<'a>, key: &str) -> Result<&'a JsonValue<'a>, String> {
    value
        .object_members()
        .ok_or_else(|| format!("object containing {key} expected"))?
        .iter()
        .find(|member| member.key() == key)
        .map(|member| member.value())
        .ok_or_else(|| format!("missing field {key}"))
}

fn render_sample(
    args: &Arguments,
    row: &npa_api::PackageArtifactSnapshotFixture,
    generated: &performance_fixture_generator::GeneratedFixtureProfile,
    sample: &Sample,
    workspace: &Path,
    inherited_executable: &[u8],
) -> Result<String, String> {
    let cargo_lock = read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SOURCE_BYTES,
        "runtime Cargo.lock",
    )?;
    let cargo_lock_sha256 = hex(&Sha256::digest(&cargo_lock));
    if cargo_lock_sha256 != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime Cargo.lock differs from the locked benchmark build".to_owned());
    }
    let production_source_set_hash = validate_runtime_source_set(
        workspace,
        env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_PATHS"),
        b"npa-snap-source-set-v1\0",
        env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_SHA256"),
        "SNAP",
    )?;
    let production_source_set_sha256 = raw_sha256(&production_source_set_hash, "SNAP source set")?;
    let harness_source = read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/bench_package_artifact_snapshot.rs"),
        MAX_SOURCE_BYTES,
        "snapshot harness source",
    )?;
    if hex(&Sha256::digest(&harness_source)) != env!("NPA_CLI_BUILD_SNAPSHOT_HARNESS_SOURCE_SHA256")
    {
        return Err("runtime snapshot harness source differs from the benchmark build".to_owned());
    }
    let measure_source = read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/measure_process.rs"),
        MAX_SOURCE_BYTES,
        "process-measurement source",
    )?;
    if hex(&Sha256::digest(&measure_source)) != env!("NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256")
    {
        return Err(
            "runtime process-measurement source differs from the benchmark build".to_owned(),
        );
    }
    let build_identity = hex(&Sha256::digest(inherited_executable));
    let counters = sample
        .counters
        .iter()
        .map(|(name, value)| format!("\"{}\":{value}", json_escape(name)))
        .collect::<Vec<_>>()
        .join(",");
    let rustc_vv = decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?;
    let rustflags = decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?;
    let features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(|feature| format!("\"{}\"", json_escape(feature)))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{{\"schema\":\"{SAMPLE_SCHEMA}\",\"scenario_id\":\"{}\",\"source_identity\":\"{}\",\"build_identity_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"features\":[{features}],\"target\":\"{}\",\"rustflags\":\"{}\",\"harness_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\",\"measure_process_source_sha256\":\"{}\",\"measurement_mode\":\"detailed\",\"execution_lane\":\"{}\",\"artifact_mode\":\"{}\",\"fixture_profile\":\"{}\",\"artifact_bytes\":{},\"fixture_descriptor_sha256\":\"{}\",\"fixture_logical_identity_sha256\":\"{}\",\"fixture_tree_sha256\":\"{}\",\"warmup\":{},\"manifest_samples\":{},\"sample_index\":{},\"interleave_group\":\"{}\",\"process_peak_rss_scope\":\"row-sample-child\",\"elapsed_ns\":{},\"acquisition_ns\":{},\"checker_ns\":{},\"allocation_events\":{},\"allocated_bytes\":{},\"process_peak_rss_kib\":null,\"deterministic_counters\":{{{counters}}}}}",
        json_escape(&args.scenario), json_escape(&args.source_identity), build_identity,
        cargo_lock_sha256, json_escape(&rustc_vv), env!("NPA_CLI_BUILD_CARGO_PROFILE"),
        env!("NPA_CLI_BUILD_TARGET"), json_escape(&rustflags),
        env!("NPA_CLI_BUILD_SNAPSHOT_HARNESS_SOURCE_SHA256"),
        production_source_set_sha256,
        env!("NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
        row.execution_lane.as_str(), row.artifact_mode.as_str(), row.fixture_profile.as_str(),
        generated.certificate_bytes, generated.descriptor_sha256, generated.logical_identity_sha256,
        generated.artifact_tree_sha256, row.common.warmup, row.common.samples, args.sample_index,
        json_escape(&row.common.interleave_group),
        sample.elapsed_ns, sample.acquisition_ns, sample.checker_ns, sample.allocation_events,
        sample.allocated_bytes,
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
        "snapshot benchmark executable",
    )?;
    if hex(&Sha256::digest(&bytes)) != expected {
        return Err("inherited snapshot executable hash mismatch".to_owned());
    }
    Ok(bytes)
}

fn workspace_root() -> Result<PathBuf, String> {
    let manifest_directory = Path::new(env!("CARGO_MANIFEST_DIR"));
    if !manifest_directory.is_absolute() {
        return Err("embedded SNAP manifest directory must be absolute".to_owned());
    }
    let workspace = manifest_directory
        .parent()
        .and_then(Path::parent)
        .ok_or("embedded SNAP manifest directory is not nested under a workspace")?;
    let canonical = workspace
        .canonicalize()
        .map_err(|error| format!("canonicalize embedded SNAP workspace: {error}"))?;
    if canonical != workspace {
        return Err(
            "embedded SNAP workspace must already be canonical and symlink-free".to_owned(),
        );
    }
    Ok(workspace.to_path_buf())
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn decode_build_hex(value: &str) -> Result<String, String> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    {
        return Err("embedded build metadata is not lowercase hexadecimal".to_owned());
    }
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.as_chunks::<2>().0 {
        let high = (pair[0] as char)
            .to_digit(16)
            .ok_or("embedded build metadata has an invalid high nibble")?;
        let low = (pair[1] as char)
            .to_digit(16)
            .ok_or("embedded build metadata has an invalid low nibble")?;
        decoded.push(u8::try_from((high << 4) | low).map_err(display_error)?);
    }
    String::from_utf8(decoded).map_err(display_error)
}

fn json_escape(value: &str) -> String {
    let mut output = String::new();
    for character in value.chars() {
        match character {
            '\"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                let value = character as u32;
                const HEX: &[u8; 16] = b"0123456789abcdef";
                output.push_str("\\u");
                for shift in [12, 8, 4, 0] {
                    output.push(char::from(HEX[((value >> shift) & 0xf) as usize]));
                }
            }
            character => output.push(character),
        }
    }
    output
}

fn hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(bytes.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn raw_sha256(prefixed: &str, label: &str) -> Result<String, String> {
    let raw = prefixed
        .strip_prefix("sha256:")
        .ok_or_else(|| format!("{label} digest lacks the sha256 prefix"))?;
    if raw.len() != 64
        || !raw
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!("{label} digest is not canonical lowercase sha256"));
    }
    Ok(raw.to_owned())
}

fn nanos(value: u128) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
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
    use std::fs;

    #[test]
    fn snapshot_workspace_root_is_embedded_absolute_and_independent_of_cwd() {
        let expected = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .unwrap()
            .to_path_buf();
        let temporary = ClosedPrivateDirectory::new("snapshot-workspace-root-test").unwrap();
        let _guard = CurrentDirectoryGuard::enter(temporary.path()).unwrap();
        assert_eq!(workspace_root().unwrap(), expected);
        assert!(workspace_root().unwrap().is_absolute());
        assert!(validate_runtime_source_set(
            Path::new("."),
            env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_PATHS"),
            b"npa-snap-source-set-v1\0",
            env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_SHA256"),
            "SNAP ambient-dot regression",
        )
        .unwrap_err()
        .contains("must be absolute"));
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_runtime_workspace_rejects_symlink_root() {
        use std::os::unix::fs::symlink;

        let temporary = ClosedPrivateDirectory::new("snapshot-workspace-symlink-test").unwrap();
        temporary.create_directory(Path::new("real")).unwrap();
        symlink(
            temporary.path().join("real"),
            temporary.path().join("linked"),
        )
        .unwrap();
        let error = validate_runtime_source_set(
            &temporary.path().join("linked"),
            "member.rs",
            b"test-domain\0",
            &"0".repeat(64),
            "SNAP symlink regression",
        )
        .unwrap_err();
        assert!(error.contains("canonical") || error.contains("source directory"));
    }

    #[test]
    fn snapshot_json_escape_round_trips_all_control_characters() {
        let source = (0_u8..=0x1f)
            .map(char::from)
            .chain(['"', '\\', 'x'])
            .collect::<String>();
        let encoded = format!("{{\"value\":\"{}\"}}", json_escape(&source));
        let document = JsonDocument::parse(&encoded).unwrap();
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
    fn snapshot_private_root_is_owner_only() {
        let root = ClosedPrivateDirectory::new("snapshot-permission-test").unwrap();
        let metadata = fs::symlink_metadata(root.path()).unwrap();
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
    fn snapshot_private_root_rejects_symlink_temporary_parent() {
        use std::os::unix::fs::symlink;

        let container = ClosedPrivateDirectory::new("snapshot-symlink-parent-container").unwrap();
        let link = container.path().join("temporary-parent-link");
        symlink(container.path(), &link).unwrap();
        let error = match ClosedPrivateDirectory::new_in(&link, "snapshot-symlink-parent") {
            Ok(_) => panic!("symlink temporary parent was accepted"),
            Err(error) => error,
        };
        assert_eq!(error, "temporary parent is not a real directory");
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_private_root_drop_rejects_path_replacement() {
        let root = ClosedPrivateDirectory::new("snapshot-replacement-test").unwrap();
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

    #[test]
    fn snapshot_fixture_profiles() {
        for (profile, modules, edges, bytes) in [
            ("representative-1000-certificates", 1_000, 975, 49_283_072),
            ("synthetic-1kib", 1, 0, 1_024),
            ("synthetic-1mib", 1, 0, 1_048_576),
            ("synthetic-near-limit", 1, 0, 67_108_000),
        ] {
            let descriptor =
                performance_fixture_generator::fixture_profile_descriptor(profile).unwrap();
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
    fn snapshot_fixture_identity_v1() {
        let source = include_str!("../../../testdata/performance/fixture-generator.v1.tsv");
        assert_eq!(source.lines().count(), 11);
        assert!(source
            .lines()
            .skip(1)
            .all(|row| row.split('\t').count() == 13));
        for profile in [
            "representative-1000-certificates",
            "synthetic-1kib",
            "synthetic-1mib",
            "synthetic-near-limit",
        ] {
            assert_eq!(
                source
                    .lines()
                    .filter(|row| row.split('\t').nth(1) == Some(profile))
                    .count(),
                1
            );
        }
    }

    #[test]
    fn snapshot_cache_lifecycle_v1() {
        let manifest = include_str!("../../../testdata/performance/fixtures/manifest.v0.2.json");
        let rows = snapshot_rows(manifest).unwrap();
        assert_eq!(rows.len(), 40);
        assert!(rows.iter().all(|row| {
            resolve_package_root(&row.package_root, profile_name(row.fixture_profile))
                == Ok(Path::new("generated").join(profile_name(row.fixture_profile)))
        }));
        for rejected in [
            "fixture/synthetic-1kib",
            "generated/other",
            "generated/synthetic-1kib/extra",
            "generated/../synthetic-1kib",
        ] {
            assert!(resolve_package_root(rejected, "synthetic-1kib").is_err());
        }
        assert_eq!(
            rows.iter()
                .filter(|row| row.execution_lane == PerformanceFixtureExecutionLane::CliLocal)
                .count(),
            20
        );
        assert_eq!(
            rows.iter()
                .filter(|row| row.execution_lane == PerformanceFixtureExecutionLane::Api)
                .count(),
            20
        );
        assert!(rows
            .iter()
            .all(|row| row.common.warmup == 1 && row.common.samples == 5));
        let groups = rows.iter().fold(
            BTreeMap::<&str, Vec<&npa_api::PackageArtifactSnapshotFixture>>::new(),
            |mut groups, row| {
                groups
                    .entry(&row.common.interleave_group)
                    .or_default()
                    .push(row);
                groups
            },
        );
        assert_eq!(groups.len(), 20);
        for values in groups.values() {
            assert_eq!(values.len(), 2);
            assert!(values
                .iter()
                .any(|row| row.artifact_mode == PerformanceFixtureArtifactMode::Raw));
            assert!(values
                .iter()
                .any(|row| row.artifact_mode == PerformanceFixtureArtifactMode::Snapshot));
            for selected in values {
                let companion = select_snapshot_companion(manifest, selected).unwrap();
                assert_eq!(
                    companion.common.interleave_group,
                    selected.common.interleave_group
                );
                assert_ne!(companion.artifact_mode, selected.artifact_mode);
            }
        }
        assert_eq!(
            (0_u64..5)
                .flat_map(|sample| {
                    if sample.is_multiple_of(2) {
                        [format!("{sample}:raw"), format!("{sample}:snapshot")]
                    } else {
                        [format!("{sample}:snapshot"), format!("{sample}:raw")]
                    }
                })
                .collect::<Vec<_>>(),
            [
                "0:raw",
                "0:snapshot",
                "1:snapshot",
                "1:raw",
                "2:raw",
                "2:snapshot",
                "3:snapshot",
                "3:raw",
                "4:raw",
                "4:snapshot",
            ]
        );
    }

    #[test]
    fn snapshot_fixture_parent_cleanup_is_closed_and_preserves_unknowns() {
        let clean = ClosedPrivateDirectory::new("snapshot-generated-parent-test").unwrap();
        clean.create_directory(Path::new("generated")).unwrap();
        cleanup_snapshot_fixture_parent(&clean).unwrap();
        clean.remove_empty_root().unwrap();

        let unknown = ClosedPrivateDirectory::new("snapshot-generated-parent-test").unwrap();
        unknown.create_directory(Path::new("generated")).unwrap();
        unknown
            .create_new_file(Path::new("generated/sentinel"), b"preserve")
            .unwrap();
        assert!(cleanup_snapshot_fixture_parent(&unknown).is_err());
        assert_eq!(
            unknown
                .read_regular_file(Path::new("generated/sentinel"), 8)
                .unwrap(),
            b"preserve"
        );
        unknown
            .remove_exact_file(Path::new("generated/sentinel"), b"preserve")
            .unwrap();
        cleanup_snapshot_fixture_parent(&unknown).unwrap();
        unknown.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_fixture_parent_cleanup_rejects_renamed_replacement() {
        let root = ClosedPrivateDirectory::new("snapshot-generated-parent-test").unwrap();
        root.create_directory(Path::new("generated")).unwrap();
        let relocated = root.path().join("generated-original");
        fs::rename(root.path().join("generated"), &relocated).unwrap();
        fs::create_dir(root.path().join("generated")).unwrap();
        fs::write(root.path().join("generated/sentinel"), b"replacement").unwrap();
        assert!(cleanup_snapshot_fixture_parent(&root).is_err());
        assert_eq!(
            fs::read(root.path().join("generated/sentinel")).unwrap(),
            b"replacement"
        );
        assert!(relocated.is_dir());
        fs::remove_file(root.path().join("generated/sentinel")).unwrap();
        fs::remove_dir(root.path().join("generated")).unwrap();
        fs::remove_dir(relocated).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[test]
    fn snapshot_baseline_parser_and_counter_set_are_closed() {
        let baseline =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let manifest = include_str!("../../../testdata/performance/fixtures/manifest.v0.2.json");
        let rows = snapshot_rows(manifest).unwrap();
        assert_eq!(rows.len(), 40);
        for row in rows {
            let expected = baseline_expectation(baseline, &row.common.id).unwrap();
            validate_snapshot_counter_catalog(&expected.counters).unwrap();
            assert!(SNAPSHOT_COUNTER_CATALOG
                .iter()
                .all(|(label, unit)| label.unit() == *unit));
        }

        let scenario = "package-artifact-snapshot-rep-api-pm0-dc0-fast-raw-j1";
        let expected = baseline_expectation(baseline, scenario).unwrap();
        assert_eq!(expected.module_count, 1_000);
        assert!(validate_counters(&expected.counters, &expected.counters).is_ok());

        let mut extra = expected.counters.clone();
        extra.insert("package.unknown".to_owned(), 0);
        assert!(validate_counters(&expected.counters, &extra).is_err());
        let mut missing = expected.counters.clone();
        missing.pop_first();
        assert!(validate_counters(&expected.counters, &missing).is_err());

        let mutate_selected = |needle: &str, replacement: &str| {
            let marker = format!("\"id\": \"{scenario}\"");
            let offset = baseline.find(&marker).unwrap();
            let mut mutated = baseline[..offset].to_owned();
            let suffix = baseline[offset..].replacen(needle, replacement, 1);
            assert_ne!(suffix, baseline[offset..]);
            mutated.push_str(&suffix);
            mutated
        };

        for malformed in [
            baseline.replacen(
                "\"schema\": \"npa.performance.baselines.v0.1\"",
                "\"unknown\": 0,\n  \"schema\": \"npa.performance.baselines.v0.1\"",
                1,
            ),
            baseline.replacen(
                "\"schema\": \"npa.performance.baselines.v0.1\"",
                "\"measurement_schema\": \"npa.performance.measurements.v0.9\",\n  \"schema\": \"npa.performance.baselines.v0.1\"",
                1,
            ),
            baseline.replacen(
                "\"schema\": \"npa.performance.baselines.v0.1\",\n  \"measurement_schema\": \"npa.performance.measurements.v0.9\"",
                "\"measurement_schema\": \"npa.performance.measurements.v0.9\",\n  \"schema\": \"npa.performance.baselines.v0.1\"",
                1,
            ),
            baseline.replacen(
                &format!("\"id\": \"{scenario}\",\n      \"status\": \"passed\""),
                &format!("\"status\": \"passed\",\n      \"id\": \"{scenario}\""),
                1,
            ),
            baseline.replacen(
                &format!("\"id\": \"{scenario}\""),
                &format!("\"id\": \"{scenario}\",\n      \"unknown\": 0"),
                1,
            ),
            baseline.replacen(
                &format!("\"id\": \"{scenario}\""),
                &format!("\"id\": \"{scenario}\",\n      \"id\": \"{scenario}\""),
                1,
            ),
            baseline.replacen(
                &format!("\"id\": \"{scenario}\",\n      \"status\": \"passed\",\n      \"module_count\": 1000"),
                &format!("\"id\": \"{scenario}\",\n      \"status\": \"passed\",\n      \"module_count\": \"1000\""),
                1,
            ),
            mutate_selected(
                "\"package.artifact_file_hashes\": 1000,\n        \"package.artifact_files_read\": 0",
                "\"package.artifact_files_read\": 0,\n        \"package.artifact_file_hashes\": 1000",
            ),
            mutate_selected(
                "\"package.artifact_file_hashes\": 1000",
                "\"package.unknown\": 1000",
            ),
            mutate_selected("\"live_results_min\": 0", "\"live_results_min\": 1"),
            mutate_selected(
                "\"proof_evidence_reduction_allowed\": false",
                "\"proof_evidence_reduction_allowed\": true",
            ),
        ] {
            assert!(baseline_expectation(&malformed, scenario).is_err());
        }
    }

    #[test]
    fn snapshot_source_set_digest_projects_to_raw_sha256() {
        let raw = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        assert_eq!(
            raw_sha256(&format!("sha256:{raw}"), "source set").unwrap(),
            raw
        );
        for malformed in [
            raw,
            "sha256:0123",
            "sha256:0123456789ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef",
            "sha512:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        ] {
            assert!(raw_sha256(malformed, "source set").is_err());
        }
    }

    #[test]
    fn snapshot_counter_projection_closes_a_superset_with_exact_units_and_order() {
        let mut superset = SNAPSHOT_COUNTER_CATALOG
            .iter()
            .enumerate()
            .map(|(index, (label, unit))| PerformanceMeasurementCounter {
                label: *label,
                unit: *unit,
                value: u64::try_from(index).unwrap(),
            })
            .collect::<Vec<_>>();
        superset.extend([
            PerformanceMeasurementCounter {
                label: PerformanceMeasurementLabel::PackageModulesDecoded,
                unit: PerformanceMeasurementUnit::Count,
                value: 1_000,
            },
            PerformanceMeasurementCounter {
                label: PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
                unit: PerformanceMeasurementUnit::Count,
                value: 1_000,
            },
        ]);
        superset.sort_by_key(|counter| counter.label.as_str());

        let projected = project_snapshot_counter_records(&superset).unwrap();
        validate_snapshot_counter_catalog(&projected).unwrap();
        assert_eq!(projected.len(), 19);
        assert!(!projected.contains_key("package.modules_decoded"));
        assert!(!projected.contains_key("package.module_payloads_frozen"));

        let mut wrong_unit = superset.clone();
        let selected = wrong_unit
            .iter_mut()
            .find(|counter| counter.label == PerformanceMeasurementLabel::PackageArtifactFileHashes)
            .unwrap();
        selected.unit = PerformanceMeasurementUnit::Bytes;
        assert!(project_snapshot_counter_records(&wrong_unit).is_err());

        let mut reordered = superset.clone();
        reordered.swap(0, 1);
        assert!(project_snapshot_counter_records(&reordered).is_err());

        let mut duplicated = superset;
        duplicated.insert(1, duplicated[0].clone());
        assert!(project_snapshot_counter_records(&duplicated).is_err());
    }
}

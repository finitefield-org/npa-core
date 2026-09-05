//! Deterministic changed-selection Git-batching harness.
//!
//! The production release comparison additionally binds preserved executable
//! and source identities. This example deliberately keeps deterministic
//! catalog/batch expectations executable without claiming host elapsed
//! evidence from a mutable worktree.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::{CString, OsStr, OsString};
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

use npa_api::{
    validate_package_changed_selection_baseline, validate_performance_fixture_selection,
    verify_package_fast_source_free_from_root, JsonDocument, JsonMember, JsonValue,
    PerformanceFixtureSelection, PerformanceMeasurementLabel,
    PerformancePackageSelectionBatchPolicy, PerformancePackageSelectionObservation,
};
use npa_cert::{build_module_cert, encode_module_cert, CoreModule, Name};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, PackageHash, PackagePath,
};
use sha2::{Digest, Sha256};
use toml_edit::DocumentMut;

#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;

use closed_private_tree::{
    read_absolute_regular_tree, read_invocation_regular_file,
    write_invocation_regular_file_create_or_same, AttachedExecutable, ClosedCleanupCatalog,
    ClosedPrivateDirectory,
};

const PREFIX: &str = "package.changed_selection.git_batching.v1.";
const POINTER_BYTES: usize = std::mem::size_of::<*const u8>();
const TARGET_BYTES: usize = 65_536;
const MAX_PATHSPECS: usize = 1_024;
const LEGACY_PATHSPECS: usize = 128;
const EXACT_PATHSPEC_GROUP_SIZE: usize = 2;
const WARMUP: u64 = 1;
const SAMPLES: u64 = 7;
const RUN_SCHEMA: &str = "npa.package.changed_selection.benchmark_run.v3";
const PROVENANCE_SCHEMA: &str = "npa.package.changed_selection.provenance.v3";
const ARTIFACT_SCHEMA: &str = "npa.package.changed_selection.artifact_provenance.v3";
const BENCHMARK_BASENAME: &str = "bench_package_changed_selection";
const NPA_BASENAME: &str = "npa";
const GIT_PATH: &str = "/usr/bin/git";
const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
const MAX_FIXTURE_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;
const MAX_DETERMINISTIC_BASELINE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_ARTIFACT_SIDECAR_BYTES: u64 = 4 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_IUT_MANIFEST_BYTES: u64 = 8 * 1024 * 1024;
const MAX_IUT_TREE_ENTRIES: usize = 16_384;
const MAX_IUT_FILE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_IUT_TREE_BYTES: u64 = 512 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Population {
    TimingOffTotal,
    TimingSummarySelection,
}

impl Population {
    const fn as_str(self) -> &'static str {
        match self {
            Self::TimingOffTotal => "timing-off-total",
            Self::TimingSummarySelection => "timing-summary-selection",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BenchmarkArguments {
    scenario: String,
    population: Population,
    fixture_manifest: PathBuf,
    deterministic_baseline: PathBuf,
    npa_binary: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Invocation {
    List,
    Benchmark(BenchmarkArguments),
    WriteArtifact {
        directory: PathBuf,
        npa_binary: PathBuf,
        source_revision: String,
        cargo_lock: PathBuf,
        cargo_profile: String,
        cargo_features: Vec<String>,
    },
    CheckArtifact {
        directory: PathBuf,
    },
}

fn parse_arguments(args: &[String]) -> Result<Invocation, String> {
    if args == ["--list"] {
        return Ok(Invocation::List);
    }
    let mut scenario = None;
    let mut population = None;
    let mut fixture_manifest = None;
    let mut deterministic_baseline = None;
    let mut npa_binary = None;
    let mut source_revision = None;
    let mut cargo_lock = None;
    let mut cargo_profile = None;
    let mut cargo_features = None;
    let mut write_artifact = None;
    let mut check_artifact = None;
    let mut index = 0;
    while index < args.len() {
        let (slot, name): (&mut Option<String>, &str) = match args[index].as_str() {
            "--scenario" => (&mut scenario, "--scenario"),
            "--population" => (&mut population, "--population"),
            "--fixture-manifest" => (&mut fixture_manifest, "--fixture-manifest"),
            "--deterministic-baseline" => (&mut deterministic_baseline, "--deterministic-baseline"),
            "--npa-binary" => (&mut npa_binary, "--npa-binary"),
            "--source-revision" => (&mut source_revision, "--source-revision"),
            "--cargo-lock" => (&mut cargo_lock, "--cargo-lock"),
            "--cargo-profile" => (&mut cargo_profile, "--cargo-profile"),
            "--cargo-features" => (&mut cargo_features, "--cargo-features"),
            "--write-artifact-provenance" => (&mut write_artifact, "--write-artifact-provenance"),
            "--check-artifact-provenance" => (&mut check_artifact, "--check-artifact-provenance"),
            "--list" => return Err("--list cannot be combined with benchmark arguments".to_owned()),
            unknown => return Err(format!("unknown argument: {unknown}")),
        };
        if slot.is_some() {
            return Err(format!("duplicate {name}"));
        }
        *slot = Some(
            args.get(index + 1)
                .ok_or_else(|| format!("missing {name} value"))?
                .clone(),
        );
        index += 2;
    }
    if write_artifact.is_some() && check_artifact.is_some() {
        return Err("artifact writer and checker modes are mutually exclusive".to_owned());
    }
    if let Some(directory) = check_artifact {
        if scenario.is_some()
            || population.is_some()
            || fixture_manifest.is_some()
            || deterministic_baseline.is_some()
            || npa_binary.is_some()
            || source_revision.is_some()
            || cargo_lock.is_some()
            || cargo_profile.is_some()
            || cargo_features.is_some()
        {
            return Err("artifact checker mode accepts only its directory".to_owned());
        }
        return Ok(Invocation::CheckArtifact {
            directory: PathBuf::from(directory),
        });
    }
    if let Some(directory) = write_artifact {
        if scenario.is_some()
            || population.is_some()
            || fixture_manifest.is_some()
            || deterministic_baseline.is_some()
        {
            return Err("artifact writer mode does not accept workload arguments".to_owned());
        }
        let npa_binary = PathBuf::from(npa_binary.ok_or("missing --npa-binary")?);
        let source_revision = source_revision.ok_or("missing --source-revision")?;
        validate_source_revision(&source_revision)?;
        let cargo_lock = PathBuf::from(cargo_lock.ok_or("missing --cargo-lock")?);
        let cargo_profile = cargo_profile.ok_or("missing --cargo-profile")?;
        validate_identity_string(&cargo_profile, "cargo profile")?;
        let cargo_features =
            canonical_features(&cargo_features.ok_or("missing --cargo-features")?)?;
        return Ok(Invocation::WriteArtifact {
            directory: PathBuf::from(directory),
            npa_binary,
            source_revision,
            cargo_lock,
            cargo_profile,
            cargo_features,
        });
    }
    if source_revision.is_some()
        || cargo_lock.is_some()
        || cargo_profile.is_some()
        || cargo_features.is_some()
    {
        return Err(
            "benchmark mode derives build provenance from the executable and rejects caller provenance"
                .to_owned(),
        );
    }
    let npa_binary = PathBuf::from(npa_binary.ok_or("missing --npa-binary")?);
    let population = Population::parse(&population.ok_or("missing --population")?)?;
    Ok(Invocation::Benchmark(BenchmarkArguments {
        scenario: scenario.ok_or("missing --scenario")?,
        population,
        fixture_manifest: PathBuf::from(fixture_manifest.ok_or("missing --fixture-manifest")?),
        deterministic_baseline: PathBuf::from(
            deterministic_baseline.ok_or("missing --deterministic-baseline")?,
        ),
        npa_binary,
    }))
}

fn validate_source_revision(value: &str) -> Result<(), String> {
    let object_id = value.strip_suffix("-dirty").unwrap_or(value);
    if object_id.len() == 40
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        Ok(())
    } else {
        Err(
            "source revision must be exactly 40 lowercase hexadecimal characters with optional -dirty suffix"
                .to_owned(),
        )
    }
}

fn validate_identity_string(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty() || value.bytes().any(|byte| byte.is_ascii_control()) {
        Err(format!("{label} must be a nonempty printable string"))
    } else {
        Ok(())
    }
}

fn validate_identity_text(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty()
        || value
            .bytes()
            .any(|byte| byte.is_ascii_control() && byte != b'\n')
    {
        Err(format!(
            "{label} must be nonempty printable text with LF line separators"
        ))
    } else {
        Ok(())
    }
}

fn canonical_features(value: &str) -> Result<Vec<String>, String> {
    if value == "none" {
        return Ok(Vec::new());
    }
    let mut features = value.split(',').map(str::to_owned).collect::<Vec<_>>();
    if features.is_empty()
        || features
            .iter()
            .any(|feature| validate_identity_string(feature, "cargo feature").is_err())
    {
        return Err("cargo features must be 'none' or a comma-separated nonempty list".to_owned());
    }
    features.sort();
    features.dedup();
    Ok(features)
}

impl Population {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "timing-off-total" => Ok(Self::TimingOffTotal),
            "timing-summary-selection" => Ok(Self::TimingSummarySelection),
            _ => Err(format!("unsupported population: {value}")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Profile {
    suffix: &'static str,
    package_root: &'static str,
    count: usize,
    ordinary_length: usize,
    final_length: Option<usize>,
    environment: &'static str,
    change: &'static str,
}

impl Profile {
    fn id(self) -> String {
        format!("{PREFIX}{}", self.suffix)
    }

    fn candidate_profile(self) -> &'static str {
        match self.suffix {
            "empty0.clean" => "e0",
            "tiny1.clean" | "tiny1.tracked1" | "tiny1.untracked1" => "s1",
            "former127.clean" => "s127",
            "former128.clean" => "s128",
            "former129.clean" => "s129",
            "count1023.clean" => "c1023",
            "count1024.clean" => "c1024",
            "count1025.clean" => "c1025",
            "byte65535.clean" => "b65535",
            "byte65536.clean" => "b65536",
            "byte65537.clean" => "b65537",
            "long32.mixed" => "l32",
            "long128.mixed" => "l128",
            "long1024.mixed" => "l1024",
            "fallback1.clean" => "f1",
            "fallback129.clean" => "f129",
            "fallback1024.clean" => "f1024",
            "inflated129.clean" => "x129",
            "inflated992.clean" => "x992",
            "iut1401.clean" | "iut1401.tracked1" | "iut1401.untracked1" => "i1401",
            "large4096.mixed" => "g4096",
            _ => unreachable!("profile table is closed"),
        }
    }
}

macro_rules! profile {
    ($suffix:literal, $root:literal, $count:expr, $length:expr, $final:expr, $environment:literal, $change:literal) => {
        Profile {
            suffix: $suffix,
            package_root: $root,
            count: $count,
            ordinary_length: $length,
            final_length: $final,
            environment: $environment,
            change: $change,
        }
    };
}

const PROFILES: &[Profile] = &[
    profile!(
        "empty0.clean",
        "generated/empty-package",
        0,
        0,
        None,
        "n64",
        "none"
    ),
    profile!(
        "tiny1.clean",
        "generated/short-package",
        1,
        96,
        None,
        "n64",
        "none"
    ),
    profile!(
        "tiny1.tracked1",
        "generated/short-package",
        1,
        96,
        None,
        "n64",
        "t1"
    ),
    profile!(
        "tiny1.untracked1",
        "generated/short-package",
        1,
        96,
        None,
        "n64",
        "u1"
    ),
    profile!(
        "former127.clean",
        "generated/short-package",
        127,
        96,
        None,
        "n64",
        "none"
    ),
    profile!(
        "former128.clean",
        "generated/short-package",
        128,
        96,
        None,
        "n64",
        "none"
    ),
    profile!(
        "former129.clean",
        "generated/short-package",
        129,
        96,
        None,
        "n64",
        "none"
    ),
    profile!(
        "count1023.clean",
        "generated/count-package",
        1023,
        32,
        None,
        "n64",
        "none"
    ),
    profile!(
        "count1024.clean",
        "generated/count-package",
        1024,
        32,
        None,
        "n64",
        "none"
    ),
    profile!(
        "count1025.clean",
        "generated/count-package",
        1025,
        32,
        None,
        "n64",
        "none"
    ),
    profile!(
        "byte65535.clean",
        "generated/byte-boundary-package",
        550,
        96,
        Some(181),
        "n64",
        "none"
    ),
    profile!(
        "byte65536.clean",
        "generated/byte-boundary-package",
        550,
        96,
        Some(182),
        "n64",
        "none"
    ),
    profile!(
        "byte65537.clean",
        "generated/byte-boundary-package",
        550,
        96,
        Some(183),
        "n64",
        "none"
    ),
    profile!(
        "long32.mixed",
        "generated/long-path-package",
        32,
        768,
        None,
        "n64",
        "mix4"
    ),
    profile!(
        "long128.mixed",
        "generated/long-path-package",
        128,
        768,
        None,
        "n64",
        "mix4"
    ),
    profile!(
        "long1024.mixed",
        "generated/long-path-package",
        1024,
        768,
        None,
        "n64",
        "mix4"
    ),
    profile!(
        "fallback1.clean",
        "generated/fallback-package",
        1,
        96,
        None,
        "h0",
        "none"
    ),
    profile!(
        "fallback129.clean",
        "generated/fallback-package",
        129,
        96,
        None,
        "h0",
        "none"
    ),
    profile!(
        "fallback1024.clean",
        "generated/fallback-package",
        1024,
        96,
        None,
        "h0",
        "none"
    ),
    profile!(
        "inflated129.clean",
        "generated/inflated-environment-package",
        129,
        96,
        None,
        "h16",
        "none"
    ),
    profile!(
        "inflated992.clean",
        "generated/inflated-environment-package",
        992,
        96,
        None,
        "h16",
        "none"
    ),
    profile!(
        "iut1401.clean",
        "npa-project-iut/proofs",
        1401,
        0,
        None,
        "n64",
        "none"
    ),
    profile!(
        "iut1401.tracked1",
        "npa-project-iut/proofs",
        1401,
        0,
        None,
        "n64",
        "t1"
    ),
    profile!(
        "iut1401.untracked1",
        "npa-project-iut/proofs",
        1401,
        0,
        None,
        "n64",
        "u1"
    ),
    profile!(
        "large4096.mixed",
        "generated/large-package",
        4096,
        96,
        None,
        "n64",
        "mix4"
    ),
];

fn generated_path(package_root: &str, length: usize, index: usize) -> Result<String, String> {
    let suffix = format!("{index:08x}");
    let padding = length
        .checked_sub(package_root.len() + 1 + suffix.len())
        .ok_or_else(|| "candidate length underflow".to_owned())?;
    if padding == 1 {
        return Err("candidate padding charge 1 is not canonical".to_owned());
    }
    let mut components = vec![package_root.to_owned()];
    if padding > 0 {
        let (quotient, remainder) = (padding / 201, padding % 201);
        if remainder == 0 {
            components.extend((0..quotient).map(|_| "p".repeat(200)));
        } else if remainder == 1 {
            if quotient == 0 {
                return Err("candidate padding charge 1 is not canonical".to_owned());
            }
            components.extend((0..quotient - 1).map(|_| "p".repeat(200)));
            components.push("p".repeat(100));
            components.push("p".repeat(100));
        } else {
            components.extend((0..quotient).map(|_| "p".repeat(200)));
            components.push("p".repeat(remainder - 1));
        }
    }
    components.push(suffix);
    let path = components.join("/");
    (path.len() == length)
        .then_some(path)
        .ok_or_else(|| "generated candidate has the wrong byte length".to_owned())
}

fn generated_catalog(profile: Profile) -> Result<Vec<String>, String> {
    if profile.count == 0 {
        return Ok(Vec::new());
    }
    if profile.ordinary_length == 0 {
        return Err("IUT catalog is not synthetic".to_owned());
    }
    (0..profile.count)
        .map(|index| {
            let length = if index + 1 == profile.count {
                profile.final_length.unwrap_or(profile.ordinary_length)
            } else {
                profile.ordinary_length
            };
            generated_path(profile.package_root, length, index)
        })
        .collect()
}

fn iut_catalog_from_manifest(source: &str) -> Result<Vec<String>, String> {
    let document = source
        .parse::<DocumentMut>()
        .map_err(|error| format!("IUT manifest is invalid TOML: {error}"))?;
    let modules = document
        .get("modules")
        .and_then(toml_edit::Item::as_array_of_tables)
        .ok_or("IUT manifest has no modules array")?;
    let mut paths = modules
        .iter()
        .map(|module| {
            module
                .get("certificate")
                .and_then(toml_edit::Item::as_str)
                .map(|certificate| format!("npa-project-iut/proofs/{certificate}"))
                .ok_or_else(|| "IUT module has no certificate path".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    paths.sort();
    if paths.len() != 1_401 || paths.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err("IUT certificate catalog is not the exact sorted 1401-path set".to_owned());
    }
    let path_bytes = paths.iter().map(String::len).sum::<usize>();
    let min = paths.iter().map(String::len).min();
    let max = paths.iter().map(String::len).max();
    if path_bytes != 177_575
        || min != Some(55)
        || max != Some(184)
        || nul_hash(&paths) != "434e068753f94f9ddcadf6159538cdd7497a2b29dc3eafe405db1f3c623ce663"
    {
        return Err(
            "IUT certificate catalog disagrees with its checked byte/hash oracle".to_owned(),
        );
    }
    Ok(paths)
}

fn profile_catalog(profile: Profile, iut_manifest: Option<&str>) -> Result<Vec<String>, String> {
    if profile.candidate_profile() == "i1401" {
        iut_catalog_from_manifest(iut_manifest.ok_or("IUT manifest source is required")?)
    } else {
        generated_catalog(profile)
    }
}

fn nul_hash(paths: &[String]) -> String {
    let mut digest = Sha256::new();
    for path in paths {
        digest.update(path.as_bytes());
        digest.update([0]);
    }
    format!("{:x}", digest.finalize())
}

fn git_glob_escape_path(path: &str) -> String {
    let mut escaped = String::with_capacity(path.len());
    for character in path.chars() {
        if matches!(character, '\\' | '*' | '?' | '[' | ']') {
            escaped.push('\\');
        }
        escaped.push(character);
    }
    escaped
}

fn exact_pathspec_groups(paths: &[String]) -> Vec<Vec<String>> {
    let mut groups = BTreeMap::<usize, Vec<String>>::new();
    for path in paths {
        let depth = path.bytes().filter(|byte| *byte == b'/').count();
        let pathspecs = groups.entry(depth).or_default();
        pathspecs.push(format!(":(top,literal){path}"));
        pathspecs.push(format!(
            ":(top,exclude,glob){}/**",
            git_glob_escape_path(path)
        ));
    }
    groups.into_values().collect()
}

fn pathspec_charges(pathspec: &str) -> (usize, usize) {
    let payload = pathspec
        .len()
        .checked_add(1)
        .expect("reviewed benchmark pathspec payload fits usize");
    let argv = payload
        .checked_add(POINTER_BYTES)
        .expect("reviewed benchmark pathspec argv charge fits usize");
    (payload, argv)
}

fn batch_counts(
    pathspecs: &[String],
    target: Option<usize>,
    max_pathspecs: usize,
) -> Vec<(usize, usize, usize)> {
    assert!(
        pathspecs.len().is_multiple_of(EXACT_PATHSPEC_GROUP_SIZE),
        "exact pathspec pairs must remain complete"
    );
    let mut batches = Vec::new();
    let mut count = 0usize;
    let mut payload = 0usize;
    let mut charge = 0usize;
    for pair in pathspecs.as_chunks::<EXACT_PATHSPEC_GROUP_SIZE>().0 {
        let (next_payload, next_charge) =
            pair.iter()
                .fold((0usize, 0usize), |(payload, charge), pathspec| {
                    let (pathspec_payload, pathspec_charge) = pathspec_charges(pathspec);
                    (
                        payload
                            .checked_add(pathspec_payload)
                            .expect("reviewed benchmark batch payload fits usize"),
                        charge
                            .checked_add(pathspec_charge)
                            .expect("reviewed benchmark batch charge fits usize"),
                    )
                });
        let exceeds_charge = target.is_some_and(|target| {
            charge
                .checked_add(next_charge)
                .is_none_or(|value| value > target)
        });
        let exceeds_count = count.saturating_add(EXACT_PATHSPEC_GROUP_SIZE) > max_pathspecs;
        if count > 0 && (exceeds_count || exceeds_charge) {
            batches.push((count, payload, charge));
            count = 0;
            payload = 0;
            charge = 0;
        }
        count += EXACT_PATHSPEC_GROUP_SIZE;
        payload = payload
            .checked_add(next_payload)
            .expect("reviewed benchmark batch payload fits usize");
        charge = charge
            .checked_add(next_charge)
            .expect("reviewed benchmark batch charge fits usize");
    }
    if count > 0 {
        batches.push((count, payload, charge));
    }
    batches
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BatchPolicy {
    NotSelected,
    ExecBudget,
    Legacy128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DeterministicObservation {
    policy: BatchPolicy,
    candidate_paths: usize,
    pathspec_payload_bytes: usize,
    effective_argv_charge_bytes: usize,
    max_batch_payload_bytes: usize,
    max_batch_argv_charge_bytes: usize,
    pathspec_batches: usize,
    worktree_root_queries: usize,
    head_queries: usize,
    tracked_queries: usize,
    untracked_queries: usize,
    tracked_output_paths: usize,
    untracked_output_paths: usize,
    selected_paths: usize,
}

impl TryFrom<DeterministicObservation> for PerformancePackageSelectionObservation {
    type Error = String;

    fn try_from(observation: DeterministicObservation) -> Result<Self, Self::Error> {
        let to_u64 = |value: usize| {
            u64::try_from(value)
                .map_err(|_| "deterministic selection observation exceeds u64".to_owned())
        };
        Ok(Self {
            batch_policy: match observation.policy {
                BatchPolicy::NotSelected => PerformancePackageSelectionBatchPolicy::NotSelected,
                BatchPolicy::ExecBudget => PerformancePackageSelectionBatchPolicy::ExecBudget,
                BatchPolicy::Legacy128 => PerformancePackageSelectionBatchPolicy::Legacy128,
            },
            candidate_paths: to_u64(observation.candidate_paths)?,
            pathspec_payload_bytes: to_u64(observation.pathspec_payload_bytes)?,
            effective_argv_charge_bytes: to_u64(observation.effective_argv_charge_bytes)?,
            max_batch_payload_bytes: to_u64(observation.max_batch_payload_bytes)?,
            max_batch_argv_charge_bytes: to_u64(observation.max_batch_argv_charge_bytes)?,
            pathspec_batches: to_u64(observation.pathspec_batches)?,
            worktree_root_queries: to_u64(observation.worktree_root_queries)?,
            head_queries: to_u64(observation.head_queries)?,
            tracked_queries: to_u64(observation.tracked_queries)?,
            untracked_queries: to_u64(observation.untracked_queries)?,
            tracked_output_paths: to_u64(observation.tracked_output_paths)?,
            untracked_output_paths: to_u64(observation.untracked_output_paths)?,
            selected_paths: to_u64(observation.selected_paths)?,
            overflowed: false,
            ..PerformancePackageSelectionObservation::default()
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ChangedSelectionBenchmarkObservation {
    measurement_schema: String,
    selection: PerformancePackageSelectionObservation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ChangedSelectionBenchmarkSample {
    TimingOffTotal {
        ordinal: u64,
        elapsed_ns: u64,
    },
    TimingSummarySelection {
        ordinal: u64,
        selection_ms: u64,
        observation: Box<ChangedSelectionBenchmarkObservation>,
    },
}

fn exact_object<'value, 'src>(
    value: &'value JsonValue<'src>,
    expected: &[&str],
    path: &str,
) -> Result<&'value [JsonMember<'src>], String> {
    let members = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    let actual = members.iter().map(JsonMember::key).collect::<Vec<_>>();
    if actual != expected {
        return Err(format!(
            "{path} fields/order mismatch: expected {expected:?}, got {actual:?}"
        ));
    }
    Ok(members)
}

fn object_members_unique<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
) -> Result<&'value [JsonMember<'src>], String> {
    let members = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key()) {
            return Err(format!("{path} duplicates field '{}'", member.key()));
        }
    }
    Ok(members)
}

fn member<'value, 'src>(
    members: &'value [JsonMember<'src>],
    key: &str,
    path: &str,
) -> Result<&'value JsonValue<'src>, String> {
    members
        .iter()
        .find(|candidate| candidate.key() == key)
        .map(JsonMember::value)
        .ok_or_else(|| format!("{path} is missing '{key}'"))
}

fn expect_string<'a>(value: &'a JsonValue<'_>, path: &str) -> Result<&'a str, String> {
    value
        .string_value()
        .ok_or_else(|| format!("{path} must be a string"))
}

fn expect_exact_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    let actual = expect_string(value, path)?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{path} must be '{expected}', got '{actual}'"))
    }
}

fn expect_false(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    match value.bool_value() {
        Some(false) => Ok(()),
        _ => Err(format!("{path} must be false")),
    }
}

fn expect_u64(value: &JsonValue<'_>, path: &str) -> Result<u64, String> {
    let raw = value
        .number_raw()
        .ok_or_else(|| format!("{path} must be a canonical u64"))?;
    if raw.is_empty()
        || (raw.len() > 1 && raw.starts_with('0'))
        || !raw.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{path} must be a canonical u64"));
    }
    raw.parse::<u64>()
        .map_err(|_| format!("{path} exceeds u64"))
}

const SELECTION_COUNTERS: &[(PerformanceMeasurementLabel, &str)] = &[
    (
        PerformanceMeasurementLabel::PackageSelectionCandidatePaths,
        "candidate_paths",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionPathspecPayloadBytes,
        "pathspec_payload_bytes",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionEffectiveArgvChargeBytes,
        "effective_argv_charge_bytes",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionMaxBatchPayloadBytes,
        "max_batch_payload_bytes",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionMaxBatchArgvChargeBytes,
        "max_batch_argv_charge_bytes",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionPathspecBatches,
        "pathspec_batches",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionWorktreeRootQueries,
        "worktree_root_queries",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionHeadQueries,
        "head_queries",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionTrackedQueries,
        "tracked_queries",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionUntrackedQueries,
        "untracked_queries",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionTrackedOutputPaths,
        "tracked_output_paths",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionUntrackedOutputPaths,
        "untracked_output_paths",
    ),
    (
        PerformanceMeasurementLabel::PackageSelectionChangedPaths,
        "selected_paths",
    ),
];

fn parse_selection_observation(
    value: &JsonValue<'_>,
) -> Result<ChangedSelectionBenchmarkObservation, String> {
    let members = exact_object(
        value,
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
        "timings.measurements",
    )?;
    let schema = expect_string(
        member(members, "schema", "timings.measurements")?,
        "timings.measurements.schema",
    )?;
    if !matches!(
        schema,
        "npa.performance.measurements.v0.5"
            | "npa.performance.measurements.v0.6"
            | "npa.performance.measurements.v0.7"
            | "npa.performance.measurements.v0.8"
            | "npa.performance.measurements.v0.9"
    ) {
        return Err(format!("unsupported common measurement schema: {schema}"));
    }
    expect_false(
        member(members, "trusted", "timings.measurements")?,
        "timings.measurements.trusted",
    )?;
    expect_false(
        member(members, "proof_evidence", "timings.measurements")?,
        "timings.measurements.proof_evidence",
    )?;
    expect_exact_string(
        member(members, "mode", "timings.measurements")?,
        "summary",
        "timings.measurements.mode",
    )?;
    let overflowed = member(members, "overflowed", "timings.measurements")?
        .bool_value()
        .ok_or("timings.measurements.overflowed must be boolean")?;
    let counters = member(members, "counters", "timings.measurements")?
        .array_elements()
        .ok_or("timings.measurements.counters must be an array")?;
    let mut parsed = BTreeMap::<PerformanceMeasurementLabel, u64>::new();
    for (index, counter) in counters.iter().enumerate() {
        let path = format!("timings.measurements.counters[{index}]");
        let fields = exact_object(counter, &["label", "unit", "value"], &path)?;
        let label_text = expect_string(fields[0].value(), &format!("{path}.label"))?;
        let label = PerformanceMeasurementLabel::from_schema_identifier(schema, label_text)
            .ok_or_else(|| format!("{path}.label is not valid for {schema}"))?;
        expect_exact_string(
            fields[1].value(),
            label.unit().as_str(),
            &format!("{path}.unit"),
        )?;
        let value = expect_u64(fields[2].value(), &format!("{path}.value"))?;
        if parsed.insert(label, value).is_some() {
            return Err(format!("{path}.label duplicates '{label_text}'"));
        }
    }
    let read = |label: PerformanceMeasurementLabel| {
        parsed
            .get(&label)
            .copied()
            .ok_or_else(|| format!("missing selection counter '{}'", label.as_str()))
    };
    for (label, _) in SELECTION_COUNTERS {
        let _ = read(*label)?;
    }
    let exec = parsed
        .get(&PerformanceMeasurementLabel::PackageSelectionExecBudgetPolicy)
        .copied();
    let legacy = parsed
        .get(&PerformanceMeasurementLabel::PackageSelectionLegacy128Policy)
        .copied();
    let batch_policy = match (exec, legacy) {
        (None, None) => PerformancePackageSelectionBatchPolicy::NotSelected,
        (Some(1), None) => PerformancePackageSelectionBatchPolicy::ExecBudget,
        (None, Some(1)) => PerformancePackageSelectionBatchPolicy::Legacy128,
        _ => {
            return Err(
                "selection policy counters must contain zero or one value-one label".to_owned(),
            )
        }
    };
    Ok(ChangedSelectionBenchmarkObservation {
        measurement_schema: schema.to_owned(),
        selection: PerformancePackageSelectionObservation {
            batch_policy,
            candidate_paths: read(PerformanceMeasurementLabel::PackageSelectionCandidatePaths)?,
            pathspec_payload_bytes: read(
                PerformanceMeasurementLabel::PackageSelectionPathspecPayloadBytes,
            )?,
            effective_argv_charge_bytes: read(
                PerformanceMeasurementLabel::PackageSelectionEffectiveArgvChargeBytes,
            )?,
            max_batch_payload_bytes: read(
                PerformanceMeasurementLabel::PackageSelectionMaxBatchPayloadBytes,
            )?,
            max_batch_argv_charge_bytes: read(
                PerformanceMeasurementLabel::PackageSelectionMaxBatchArgvChargeBytes,
            )?,
            pathspec_batches: read(PerformanceMeasurementLabel::PackageSelectionPathspecBatches)?,
            worktree_root_queries: read(
                PerformanceMeasurementLabel::PackageSelectionWorktreeRootQueries,
            )?,
            head_queries: read(PerformanceMeasurementLabel::PackageSelectionHeadQueries)?,
            tracked_queries: read(PerformanceMeasurementLabel::PackageSelectionTrackedQueries)?,
            untracked_queries: read(PerformanceMeasurementLabel::PackageSelectionUntrackedQueries)?,
            tracked_output_paths: read(
                PerformanceMeasurementLabel::PackageSelectionTrackedOutputPaths,
            )?,
            untracked_output_paths: read(
                PerformanceMeasurementLabel::PackageSelectionUntrackedOutputPaths,
            )?,
            selected_paths: read(PerformanceMeasurementLabel::PackageSelectionChangedPaths)?,
            overflowed,
            ..PerformancePackageSelectionObservation::default()
        },
    })
}

fn parse_child_json(
    source: &str,
    population: Population,
    ordinal: u64,
    elapsed_ns: u64,
) -> Result<ChangedSelectionBenchmarkSample, String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("child emitted invalid JSON at {}", error.offset))?;
    let root = object_members_unique(document.root(), "child")?;
    expect_exact_string(
        member(root, "schema", "child")?,
        "npa.package.command_result.v0.5",
        "child.schema",
    )?;
    expect_exact_string(member(root, "status", "child")?, "passed", "child.status")?;
    let timings = root.iter().find(|field| field.key() == "timings");
    match population {
        Population::TimingOffTotal => {
            if timings.is_some() {
                return Err("timing-off child must omit timings".to_owned());
            }
            Ok(ChangedSelectionBenchmarkSample::TimingOffTotal {
                ordinal,
                elapsed_ns,
            })
        }
        Population::TimingSummarySelection => {
            let timings = timings
                .map(JsonMember::value)
                .ok_or("timing-summary child must contain timings")?;
            let fields = object_members_unique(timings, "child.timings")?;
            expect_exact_string(
                member(fields, "schema", "child.timings")?,
                "npa.package.timings.v0.2",
                "child.timings.schema",
            )?;
            expect_exact_string(
                member(fields, "mode", "child.timings")?,
                "summary",
                "child.timings.mode",
            )?;
            expect_exact_string(
                member(fields, "unit", "child.timings")?,
                "ms",
                "child.timings.unit",
            )?;
            for claim in ["proof_evidence", "build_evidence", "trusted"] {
                expect_false(
                    member(fields, claim, "child.timings")?,
                    &format!("child.timings.{claim}"),
                )?;
            }
            let selection_ms = expect_u64(
                member(fields, "selection_ms", "child.timings")?,
                "child.timings.selection_ms",
            )?;
            let observation =
                parse_selection_observation(member(fields, "measurements", "child.timings")?)?;
            Ok(ChangedSelectionBenchmarkSample::TimingSummarySelection {
                ordinal,
                selection_ms,
                observation: Box::new(observation),
            })
        }
    }
}

fn deterministic_observation(profile: Profile, paths: &[String]) -> DeterministicObservation {
    if paths.is_empty() {
        return DeterministicObservation {
            policy: BatchPolicy::NotSelected,
            candidate_paths: 0,
            pathspec_payload_bytes: 0,
            effective_argv_charge_bytes: 0,
            max_batch_payload_bytes: 0,
            max_batch_argv_charge_bytes: 0,
            pathspec_batches: 0,
            worktree_root_queries: 0,
            head_queries: 0,
            tracked_queries: 0,
            untracked_queries: 0,
            tracked_output_paths: 0,
            untracked_output_paths: 0,
            selected_paths: 0,
        };
    }
    let pathspec_groups = exact_pathspec_groups(paths);
    let requested_target = match profile.environment {
        "h0" => None,
        "h16" => Some(16_384),
        "n64" => Some(TARGET_BYTES),
        _ => unreachable!("environment profile table is closed"),
    };
    let pair_exceeds_target = requested_target.is_some_and(|target| {
        pathspec_groups.iter().any(|group| {
            group
                .as_chunks::<EXACT_PATHSPEC_GROUP_SIZE>()
                .0
                .iter()
                .any(|pair| {
                    pair.iter()
                        .map(|pathspec| pathspec_charges(pathspec).1)
                        .try_fold(0usize, usize::checked_add)
                        .is_none_or(|charge| charge > target)
                })
        })
    });
    let (policy, effective_argv_charge_bytes, batch_target, max_pathspecs) =
        match requested_target.filter(|_| !pair_exceeds_target) {
            Some(target) => (BatchPolicy::ExecBudget, target, Some(target), MAX_PATHSPECS),
            None => (BatchPolicy::Legacy128, 0, None, LEGACY_PATHSPECS),
        };
    let batches = pathspec_groups
        .iter()
        .flat_map(|group| batch_counts(group, batch_target, max_pathspecs))
        .collect::<Vec<_>>();
    let (tracked_output_paths, untracked_output_paths, selected_paths) = match profile.change {
        "none" => (0, 0, 0),
        "t1" => (1, 0, 1),
        "u1" => (1, 1, 1),
        "mix4" => (4, 1, 4),
        _ => unreachable!("change profile table is closed"),
    };
    DeterministicObservation {
        policy,
        candidate_paths: paths.len(),
        pathspec_payload_bytes: pathspec_groups
            .iter()
            .flatten()
            .map(|pathspec| pathspec_charges(pathspec).0)
            .sum(),
        effective_argv_charge_bytes,
        max_batch_payload_bytes: batches
            .iter()
            .map(|(_, payload, _)| *payload)
            .max()
            .unwrap_or(0),
        max_batch_argv_charge_bytes: batches.iter().map(|(_, _, argv)| *argv).max().unwrap_or(0),
        pathspec_batches: batches.len(),
        worktree_root_queries: 1,
        head_queries: 1,
        tracked_queries: batches.len(),
        untracked_queries: batches.len(),
        tracked_output_paths,
        untracked_output_paths,
        selected_paths,
    }
}

fn materialization_preflight(
    temporary_root: &Path,
    paths: &[String],
    path_max: Option<usize>,
    name_max: Option<usize>,
) -> Result<(), String> {
    #[cfg(unix)]
    use std::os::unix::ffi::OsStrExt;

    #[cfg(unix)]
    let root_bytes = temporary_root.as_os_str().as_bytes().len();
    #[cfg(not(unix))]
    let root_bytes = temporary_root.to_string_lossy().as_bytes().len();
    if root_bytes > 127 {
        return Err("non-comparable input: canonical temporary root exceeds 127 bytes".to_owned());
    }
    let path_max = path_max.ok_or("non-comparable input: PATH_MAX is indeterminate")?;
    let name_max = name_max.ok_or("non-comparable input: NAME_MAX is indeterminate")?;
    if path_max < 1024 || name_max < 200 {
        return Err("non-comparable input: filesystem path limits are too small".to_owned());
    }
    for path in paths {
        if path.split('/').any(|component| component.len() > name_max)
            || root_bytes + 1 + path.len() + 1 > path_max
        {
            return Err(
                "non-comparable input: candidate exceeds filesystem path limits".to_owned(),
            );
        }
    }
    Ok(())
}

#[cfg(unix)]
fn filesystem_path_limits(parent: &Path) -> Result<(usize, usize), String> {
    use std::os::unix::ffi::OsStrExt;

    let path = CString::new(parent.as_os_str().as_bytes())
        .map_err(|_| "non-comparable input: temporary parent contains NUL".to_owned())?;
    // SAFETY: `path` is a live NUL-terminated byte string and pathconf does not retain it.
    let path_max = unsafe { libc::pathconf(path.as_ptr(), libc::_PC_PATH_MAX) };
    // SAFETY: same path and lifetime argument as above.
    let name_max = unsafe { libc::pathconf(path.as_ptr(), libc::_PC_NAME_MAX) };
    if path_max < 0 || name_max < 0 {
        return Err("non-comparable input: filesystem path limits are indeterminate".to_owned());
    }
    Ok((
        usize::try_from(path_max)
            .map_err(|_| "non-comparable input: PATH_MAX is not representable".to_owned())?,
        usize::try_from(name_max)
            .map_err(|_| "non-comparable input: NAME_MAX is not representable".to_owned())?,
    ))
}

#[cfg(not(unix))]
fn filesystem_path_limits(_parent: &Path) -> Result<(usize, usize), String> {
    Err("non-comparable input: changed-selection benchmark requires Unix pathconf".to_owned())
}

fn elapsed_median_and_mad(mut values: Vec<u64>) -> Result<(u64, u64), String> {
    if values.is_empty() || values.len().is_multiple_of(2) {
        return Err("elapsed summary requires a nonempty odd sample count".to_owned());
    }
    values.sort_unstable();
    let median = values[values.len() / 2];
    let mut deviations = values
        .iter()
        .map(|value| value.abs_diff(median))
        .collect::<Vec<_>>();
    deviations.sort_unstable();
    Ok((median, deviations[deviations.len() / 2]))
}

struct TemporaryRoot {
    path: PathBuf,
    owner: ClosedPrivateDirectory,
    cleanup: TemporaryCleanup,
}

enum TemporaryCleanup {
    /// Only this harness and the fixed system Git binary have populated the
    /// root, so a fresh closed catalog may still be collected for cleanup.
    Trusted,
    /// The exact complete tree was fixed immediately before an untrusted child
    /// received paths inside it. Cleanup may remove only this captured tree.
    Armed(ClosedCleanupCatalog),
    Complete,
}

impl TemporaryRoot {
    fn create() -> Result<Self, String> {
        let owner = ClosedPrivateDirectory::new("npa-gitsel")?;
        let path = owner.path().to_owned();
        Ok(Self {
            path,
            owner,
            cleanup: TemporaryCleanup::Trusted,
        })
    }

    fn arm_untrusted_cleanup(&mut self) -> Result<(), String> {
        if !matches!(self.cleanup, TemporaryCleanup::Trusted) {
            return Err("temporary root cleanup is already armed or complete".to_owned());
        }
        self.cleanup = TemporaryCleanup::Armed(self.owner.capture_cleanup_catalog()?);
        Ok(())
    }

    fn cleanup(&mut self) -> Result<(), String> {
        let result = match &self.cleanup {
            TemporaryCleanup::Trusted => self.owner.remove_cataloged_root(),
            TemporaryCleanup::Armed(catalog) => self.owner.remove_captured_root(catalog),
            TemporaryCleanup::Complete => return Ok(()),
        };
        if result.is_ok() {
            self.cleanup = TemporaryCleanup::Complete;
        }
        result
    }
}

impl Drop for TemporaryRoot {
    fn drop(&mut self) {
        let _ = self.cleanup();
    }
}

#[derive(Clone)]
struct GeneratedModule {
    name: String,
    source: String,
    certificate: String,
    certificate_bytes: Vec<u8>,
    source_hash: String,
    file_hash: String,
    export_hash: String,
    axiom_report_hash: String,
    certificate_hash: String,
}

fn certificate_hash(hash: [u8; 32]) -> String {
    format_package_hash(&PackageHash::new(hash))
}

fn generated_module(
    profile: Profile,
    top_relative_candidate: &str,
    index: usize,
    alternate: bool,
) -> Result<GeneratedModule, String> {
    let prefix = format!("{}/", profile.package_root);
    let certificate = top_relative_candidate
        .strip_prefix(&prefix)
        .ok_or("candidate is outside package root")?
        .to_owned();
    let suffix = format!("{index:08x}");
    let name = format!("Bench.{}{suffix}", if alternate { 'D' } else { 'C' });
    let cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted(&name),
            declarations: Vec::new(),
        },
        &[],
    )
    .map_err(|error| format!("certificate generation failed for {name}: {error:?}"))?;
    let certificate_bytes = encode_module_cert(&cert)
        .map_err(|error| format!("certificate encoding failed for {name}: {error:?}"))?;
    Ok(GeneratedModule {
        name,
        source: format!("sources/{suffix}.npa"),
        certificate,
        file_hash: format_package_hash(&package_file_hash(&certificate_bytes)),
        export_hash: certificate_hash(cert.hashes().export_hash),
        axiom_report_hash: certificate_hash(cert.hashes().axiom_report_hash),
        certificate_hash: certificate_hash(cert.hashes().certificate_hash),
        certificate_bytes,
        source_hash: format!("sha256:{EMPTY_SHA256}"),
    })
}

fn render_generated_manifest(modules: &[GeneratedModule]) -> String {
    let mut out = String::from(
        "schema = \"npa.package.v0.1\"\npackage = \"npa-changed-selection-benchmark\"\nversion = \"0.1.0\"\nlicense = \"Apache-2.0\"\n\ncore_spec = \"npa.core.v0.1\"\nkernel_profile = \"npa.kernel.v0.1\"\ncertificate_format = \"npa.certificate.canonical.v0.1\"\nchecker_profile = \"npa.checker.reference.v0.1\"\n",
    );
    if modules.is_empty() {
        out.push_str("modules = []\n");
    }
    out.push_str("\n[policy]\nallow_custom_axioms = false\nallowed_axioms = []\n");
    for module in modules {
        out.push_str(&format!(
            "\n[[modules]]\nmodule = \"{}\"\nsource = \"{}\"\ncertificate = \"{}\"\nproducer_profile = \"human-surface-explicit-term\"\nexpected_source_hash = \"{}\"\nexpected_certificate_file_hash = \"{}\"\nexpected_export_hash = \"{}\"\nexpected_axiom_report_hash = \"{}\"\nexpected_certificate_hash = \"{}\"\nimports = []\ndefinitions = []\ntheorems = []\naxioms = []\n",
            module.name,
            module.source,
            module.certificate,
            module.source_hash,
            module.file_hash,
            module.export_hash,
            module.axiom_report_hash,
            module.certificate_hash,
        ));
    }
    out
}

fn write_generated_package(
    repository: &Path,
    profile: Profile,
    catalog: &[String],
    alternates: &BTreeSet<usize>,
) -> Result<Vec<GeneratedModule>, String> {
    let package_root = repository.join(profile.package_root);
    let package_relative = package_root
        .strip_prefix(repository)
        .map_err(|_| "generated package root escapes private repository".to_owned())?;
    let owner = ClosedPrivateDirectory::open_existing(repository, "npa-gitsel")?;
    owner.create_directories(package_relative)?;
    let modules = catalog
        .iter()
        .enumerate()
        .map(|(index, path)| generated_module(profile, path, index, alternates.contains(&index)))
        .collect::<Result<Vec<_>, _>>()?;
    for module in &modules {
        write_owned_file(&owner, package_relative.join(&module.source), b"")?;
        write_owned_file(
            &owner,
            package_relative.join(&module.certificate),
            &module.certificate_bytes,
        )?;
    }
    write_owned_file(
        &owner,
        package_relative.join("npa-package.toml"),
        render_generated_manifest(&modules).as_bytes(),
    )?;
    Ok(modules)
}

fn write_owned_file(
    owner: &ClosedPrivateDirectory,
    relative: PathBuf,
    bytes: &[u8],
) -> Result<(), String> {
    if u64::try_from(bytes.len()).map_err(|_| "private file length does not fit u64".to_owned())?
        > MAX_IUT_FILE_BYTES
    {
        return Err("private file exceeds the IUT member byte limit".to_owned());
    }
    if let Some(parent) = relative
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        owner.create_directories(parent)?;
    }
    match owner.create_new_file(&relative, bytes) {
        Ok(()) => Ok(()),
        Err(_) => {
            // The old preimage can legitimately be larger than the replacement
            // (for example when a reviewed manifest shrinks).  Read it under
            // the closed per-member bound instead of using the new byte count
            // as an accidental exact-size ceiling.
            let existing = owner.read_regular_file(&relative, MAX_IUT_FILE_BYTES)?;
            owner.replace_exact_file(&relative, &existing, bytes)
        }
    }
}

fn copy_tree(
    source: &Path,
    destination_root: &ClosedPrivateDirectory,
    destination: &Path,
) -> Result<(), String> {
    let tree = read_absolute_regular_tree(
        source,
        MAX_IUT_TREE_ENTRIES,
        MAX_IUT_FILE_BYTES,
        MAX_IUT_TREE_BYTES,
        "reviewed IUT tree",
    )?;
    destination_root.create_directories(destination)?;
    let mut directories = tree.directories.into_iter().collect::<Vec<_>>();
    directories.sort_by_key(|path| (path.components().count(), path.clone()));
    for relative in directories {
        if relative.as_os_str().is_empty() {
            continue;
        }
        destination_root.create_directories(&destination.join(&relative))?;
    }
    for (relative, bytes) in tree.files {
        destination_root.create_new_file(&destination.join(relative), &bytes)?;
    }
    Ok(())
}

fn reviewed_iut_root() -> Result<PathBuf, String> {
    for candidate in [
        PathBuf::from("npa-project-iut/proofs"),
        PathBuf::from("../npa-project-iut/proofs"),
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../npa-project-iut/proofs"),
    ] {
        if read_invocation_regular_file(
            &candidate.join("npa-package.toml"),
            MAX_IUT_MANIFEST_BYTES,
            "reviewed IUT manifest",
        )
        .is_ok()
        {
            return candidate
                .canonicalize()
                .map_err(|error| format!("cannot canonicalize reviewed IUT: {error}"));
        }
    }
    Err("reviewed IUT package root is unavailable".to_owned())
}

fn verify_materialized_package(package_root: &Path) -> Result<(), String> {
    let manifest_source = String::from_utf8(read_invocation_regular_file(
        &package_root.join("npa-package.toml"),
        MAX_IUT_MANIFEST_BYTES,
        "materialized manifest",
    )?)
    .map_err(|_| "materialized manifest is not UTF-8".to_owned())?;
    let validated = parse_and_validate_manifest_str(&manifest_source)
        .map_err(|error| format!("materialized manifest is invalid: {error}"))?;
    let lock = build_package_lock_from_package_root(
        &validated,
        package_root,
        PackagePath::new("npa-package.toml"),
    )
    .map_err(|error| format!("materialized lock reconstruction failed: {error}"))?;
    verify_package_fast_source_free_from_root(&validated, &lock, package_root)
        .map_err(|error| format!("materialized package verification failed: {error:?}"))?;
    Ok(())
}

fn git_output(repository: &Path, args: &[&OsStr]) -> Result<Output, String> {
    let home = repository.join(".bench-home");
    let temporary = repository.join(".bench-tmp");
    let owner = ClosedPrivateDirectory::open_existing(repository, "npa-gitsel")?;
    owner.create_directories(Path::new(".bench-home"))?;
    owner.create_directories(Path::new(".bench-tmp"))?;
    Command::new(GIT_PATH)
        .args(args)
        .current_dir(repository)
        .env_clear()
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("HOME", home)
        .env("TMPDIR", temporary)
        .output()
        .map_err(|error| format!("cannot execute /usr/bin/git: {error}"))
}

fn git(repository: &Path, arguments: &[&str]) -> Result<(), String> {
    let args = arguments.iter().map(OsStr::new).collect::<Vec<_>>();
    let output = git_output(repository, &args)?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "/usr/bin/git {} failed: {}",
            arguments.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ))
    }
}

fn initialize_repository(repository: &Path) -> Result<(), String> {
    git(repository, &["init", "--quiet"])?;
    git(
        repository,
        &["config", "user.name", "NPA Changed Selection Benchmark"],
    )?;
    git(
        repository,
        &["config", "user.email", "benchmark@npa.invalid"],
    )?;
    git(repository, &["add", "--all"])?;
    git(repository, &["commit", "--quiet", "-m", "base fixture"])
}

fn apply_git_state(repository: &Path, profile: Profile, catalog: &[String]) -> Result<(), String> {
    match profile.change {
        "none" => Ok(()),
        "t1" => {
            if profile.candidate_profile() == "i1401" {
                mutate_iut_certificate(repository, profile, catalog, 0)?;
            } else {
                write_generated_package(repository, profile, catalog, &BTreeSet::from([0]))?;
            }
            Ok(())
        }
        "u1" => git(
            repository,
            &["rm", "--cached", "--quiet", "--", &catalog[0]],
        ),
        "mix4" => {
            if catalog.len() < 4 {
                return Err("mix4 requires at least four candidates".to_owned());
            }
            write_generated_package(repository, profile, catalog, &BTreeSet::from([0, 1]))?;
            git(repository, &["add", "--", &catalog[1]])?;
            git(
                repository,
                &["rm", "--cached", "--quiet", "--", &catalog[2], &catalog[3]],
            )?;
            let mut exclude = File::options()
                .append(true)
                .open(repository.join(".git/info/exclude"))
                .map_err(|error| format!("cannot open Git exclude file: {error}"))?;
            writeln!(exclude, "/{}", catalog[3])
                .map_err(|error| format!("cannot write Git exclude entry: {error}"))
        }
        _ => Err("unknown change profile".to_owned()),
    }
}

fn mutate_iut_certificate(
    repository: &Path,
    profile: Profile,
    catalog: &[String],
    index: usize,
) -> Result<(), String> {
    let owner = ClosedPrivateDirectory::open_existing(repository, "npa-gitsel")?;
    let package_root = repository.join(profile.package_root);
    let relative = catalog[index]
        .strip_prefix(&format!("{}/", profile.package_root))
        .ok_or("IUT candidate is outside package root")?;
    let generated = generated_module(profile, &catalog[index], index, true)?;
    write_owned_file(
        &owner,
        Path::new(profile.package_root).join(relative),
        &generated.certificate_bytes,
    )?;
    let manifest_path = package_root.join("npa-package.toml");
    let mut document = String::from_utf8(read_invocation_regular_file(
        &manifest_path,
        MAX_IUT_MANIFEST_BYTES,
        "IUT manifest",
    )?)
    .map_err(|_| "IUT manifest is not UTF-8".to_owned())?
    .parse::<DocumentMut>()
    .map_err(|error| format!("IUT manifest is invalid TOML: {error}"))?;
    let modules = document
        .get_mut("modules")
        .and_then(toml_edit::Item::as_array_of_tables_mut)
        .ok_or("IUT manifest has no modules array")?;
    let module = modules
        .iter_mut()
        .find(|module| {
            module.get("certificate").and_then(toml_edit::Item::as_str) == Some(relative)
        })
        .ok_or("IUT candidate has no manifest module")?;
    module["module"] = toml_edit::value(generated.name);
    module["expected_source_hash"] = toml_edit::value(generated.source_hash);
    module["expected_certificate_file_hash"] = toml_edit::value(generated.file_hash);
    module["expected_export_hash"] = toml_edit::value(generated.export_hash);
    module["expected_axiom_report_hash"] = toml_edit::value(generated.axiom_report_hash);
    module["expected_certificate_hash"] = toml_edit::value(generated.certificate_hash);
    for field in ["imports", "definitions", "theorems", "axioms"] {
        module[field] = toml_edit::value(toml_edit::Array::new());
    }
    write_owned_file(
        &owner,
        Path::new(profile.package_root).join("npa-package.toml"),
        document.to_string().as_bytes(),
    )
}

struct MaterializedRepository {
    temporary: TemporaryRoot,
    package_root: PathBuf,
}

fn materialize_repository(
    profile: Profile,
    catalog: &[String],
) -> Result<MaterializedRepository, String> {
    let temporary = TemporaryRoot::create()
        .map_err(|error| format!("cannot create changed-selection temporary root: {error}"))?;
    let parent = temporary
        .path
        .parent()
        .ok_or("temporary repository has no parent")?;
    let (path_max, name_max) = filesystem_path_limits(parent)?;
    materialization_preflight(&temporary.path, catalog, Some(path_max), Some(name_max))
        .map_err(|error| format!("changed-selection materialization preflight failed: {error}"))?;
    if profile.candidate_profile() == "i1401" {
        copy_tree(
            &reviewed_iut_root()?,
            &temporary.owner,
            Path::new(profile.package_root),
        )
        .map_err(|error| format!("cannot copy reviewed IUT tree: {error}"))?;
    } else {
        write_generated_package(&temporary.path, profile, catalog, &BTreeSet::new())
            .map_err(|error| format!("cannot write generated benchmark package: {error}"))?;
    }
    verify_materialized_package(&temporary.path.join(profile.package_root))
        .map_err(|error| format!("generated package pre-Git validation failed: {error}"))?;
    initialize_repository(&temporary.path)
        .map_err(|error| format!("cannot initialize benchmark Git repository: {error}"))?;
    apply_git_state(&temporary.path, profile, catalog)
        .map_err(|error| format!("cannot apply benchmark Git state: {error}"))?;
    verify_materialized_package(&temporary.path.join(profile.package_root))
        .map_err(|error| format!("generated package post-Git validation failed: {error}"))?;
    Ok(MaterializedRepository {
        package_root: temporary.path.join(profile.package_root),
        temporary,
    })
}

fn observed_changed_candidates(
    repository: &Path,
    catalog: &[String],
) -> Result<Vec<String>, String> {
    let arguments = [
        OsStr::new("status"),
        OsStr::new("--porcelain=v1"),
        OsStr::new("-z"),
        OsStr::new("--untracked-files=all"),
    ];
    let output = git_output(repository, &arguments)?;
    if !output.status.success() {
        return Err(format!(
            "Git state preflight failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let catalog = catalog.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let mut selected = BTreeSet::new();
    for record in output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
    {
        if record.len() < 4 || record[2] != b' ' {
            return Err("Git state preflight emitted malformed porcelain output".to_owned());
        }
        let path = std::str::from_utf8(&record[3..])
            .map_err(|_| "Git state preflight emitted non-UTF-8 path".to_owned())?;
        if catalog.contains(path) {
            selected.insert(path.to_owned());
        }
    }
    Ok(selected.into_iter().collect())
}

fn expected_changed_candidates(profile: Profile, catalog: &[String]) -> Vec<String> {
    match profile.change {
        "none" => Vec::new(),
        "t1" | "u1" => catalog[..1].to_vec(),
        "mix4" => catalog[..4].to_vec(),
        _ => unreachable!("change profile table is closed"),
    }
}

fn environment_charge(environment: &[(String, String)]) -> Option<usize> {
    let payload = environment.iter().try_fold(0usize, |total, (key, value)| {
        total
            .checked_add(key.len())?
            .checked_add(1)?
            .checked_add(value.len())?
            .checked_add(1)
    })?;
    payload.checked_add(
        environment
            .len()
            .checked_add(1)?
            .checked_mul(POINTER_BYTES)?,
    )
}

fn argv_charge(program: &str, arguments: &[&str]) -> Option<usize> {
    let payload = program.len().checked_add(1)?.checked_add(
        arguments.iter().try_fold(0usize, |total, argument| {
            total.checked_add(argument.len())?.checked_add(1)
        })?,
    )?;
    payload.checked_add(arguments.len().checked_add(2)?.checked_mul(POINTER_BYTES)?)
}

fn fixed_git_argv_charge() -> Result<usize, String> {
    let tracked = argv_charge(
        GIT_PATH,
        &[
            "diff",
            "--name-only",
            "-z",
            "--no-ext-diff",
            "--no-renames",
            "HEAD",
            "--",
        ],
    );
    let untracked = argv_charge(
        GIT_PATH,
        &["ls-files", "--others", "--exclude-standard", "-z", "--"],
    );
    tracked
        .into_iter()
        .chain(untracked)
        .max()
        .ok_or_else(|| "fixed Git argv charge overflow".to_owned())
}

#[cfg(unix)]
fn unix_arg_max() -> Result<usize, String> {
    // SAFETY: sysconf receives a fixed constant and reads no caller-owned memory.
    let value = unsafe { libc::sysconf(libc::_SC_ARG_MAX) };
    if value <= 0 {
        Err("non-comparable input: ARG_MAX is indeterminate".to_owned())
    } else {
        usize::try_from(value).map_err(|_| "non-comparable input: ARG_MAX overflow".to_owned())
    }
}

#[cfg(not(unix))]
fn unix_arg_max() -> Result<usize, String> {
    Err("non-comparable input: changed-selection benchmark requires Unix ARG_MAX".to_owned())
}

fn child_environment(
    repository: &MaterializedRepository,
    profile: Profile,
) -> Result<Vec<(String, String)>, String> {
    let home = repository.temporary.path.join(".child-home");
    let temporary = repository.temporary.path.join(".child-tmp");
    repository
        .temporary
        .owner
        .create_directories(Path::new(".child-home"))?;
    repository
        .temporary
        .owner
        .create_directories(Path::new(".child-tmp"))?;
    let mut environment = vec![
        ("LC_ALL".to_owned(), "C".to_owned()),
        ("LANG".to_owned(), "C".to_owned()),
        ("GIT_CONFIG_NOSYSTEM".to_owned(), "1".to_owned()),
        ("GIT_CONFIG_GLOBAL".to_owned(), "/dev/null".to_owned()),
        ("HOME".to_owned(), home.to_string_lossy().into_owned()),
        (
            "TMPDIR".to_owned(),
            temporary.to_string_lossy().into_owned(),
        ),
    ];
    let arg_max = unix_arg_max()?;
    let fixed = fixed_git_argv_charge()?;
    let reserve = 32 * 1024usize;
    let base = environment_charge(&environment).ok_or("child environment charge overflow")?;
    match profile.environment {
        "n64" => {
            let safe = arg_max
                .checked_sub(base)
                .and_then(|value| value.checked_sub(fixed))
                .and_then(|value| value.checked_sub(reserve))
                .ok_or("non-comparable input: base environment exhausts ARG_MAX")?;
            if safe < TARGET_BYTES {
                return Err("non-comparable input: n64 headroom is below 65536 bytes".to_owned());
            }
        }
        "h0" | "h16" => {
            let desired_safe = if profile.environment == "h0" {
                0
            } else {
                16_384
            };
            let desired_environment = arg_max
                .checked_sub(fixed)
                .and_then(|value| value.checked_sub(reserve))
                .and_then(|value| value.checked_sub(desired_safe))
                .ok_or("non-comparable input: desired headroom is impossible")?;
            let padding_key = "NPA_CHANGED_SELECTION_BENCH_PADDING";
            let overhead = padding_key
                .len()
                .checked_add(2)
                .and_then(|value| value.checked_add(POINTER_BYTES))
                .ok_or("padding charge overflow")?;
            let value_length = desired_environment
                .checked_sub(base)
                .and_then(|value| value.checked_sub(overhead))
                .ok_or("non-comparable input: ARG_MAX cannot host padding profile")?;
            environment.push((padding_key.to_owned(), "x".repeat(value_length)));
            let actual = environment_charge(&environment).ok_or("padded environment overflow")?;
            if actual != desired_environment {
                return Err(
                    "padded environment charge disagrees with requested headroom".to_owned(),
                );
            }
        }
        _ => return Err("unknown environment profile".to_owned()),
    }
    Ok(environment)
}

fn run_sample_at(
    profile: &Profile,
    population: Population,
    npa_binary: &AttachedExecutable,
    ordinal: u64,
) -> Result<ChangedSelectionBenchmarkSample, String> {
    let iut_manifest = if profile.candidate_profile() == "i1401" {
        Some(
            String::from_utf8(read_invocation_regular_file(
                &reviewed_iut_root()?.join("npa-package.toml"),
                MAX_IUT_MANIFEST_BYTES,
                "reviewed IUT manifest",
            )?)
            .map_err(|_| "reviewed IUT manifest is not UTF-8".to_owned())?,
        )
    } else {
        None
    };
    let catalog = profile_catalog(*profile, iut_manifest.as_deref())?;
    let expected_catalog_hash = if profile.candidate_profile() == "i1401" {
        "434e068753f94f9ddcadf6159538cdd7497a2b29dc3eafe405db1f3c623ce663".to_owned()
    } else {
        nul_hash(&generated_catalog(*profile)?)
    };
    if nul_hash(&catalog) != expected_catalog_hash {
        return Err("candidate catalog identity changed during sample setup".to_owned());
    }
    let mut repository = materialize_repository(*profile, &catalog)?;
    let actual = observed_changed_candidates(&repository.temporary.path, &catalog)
        .map_err(|error| format!("cannot observe benchmark changed candidates: {error}"))?;
    let expected = expected_changed_candidates(*profile, &catalog);
    if actual != expected {
        return Err(format!(
            "fixture changed set mismatch: expected {} candidates, got {}",
            expected.len(),
            actual.len()
        ));
    }
    let environment = child_environment(&repository, *profile)
        .map_err(|error| format!("cannot prepare benchmark child environment: {error}"))?;
    repository
        .temporary
        .arm_untrusted_cleanup()
        .map_err(|error| format!("cannot capture benchmark cleanup catalog: {error}"))?;
    npa_binary.verify()?;
    let mut command = Command::new(npa_binary.path());
    command
        .arg("package")
        .arg("verify-certs")
        .arg("--root")
        .arg(&repository.package_root)
        .arg("--changed")
        .arg("--package-lock")
        .arg("reconstructed")
        .arg("--checker")
        .arg("fast")
        .arg("--audit-cache")
        .arg("off")
        .arg("--verifier-memo")
        .arg("off")
        .arg("--jobs")
        .arg("4")
        .arg("--json")
        .current_dir(&repository.temporary.path)
        .env_clear();
    for (key, value) in environment {
        command.env(key, value);
    }
    if population == Population::TimingSummarySelection {
        command.arg("--timings").arg("summary");
    }
    let started = Instant::now();
    let output = command
        .output()
        .map_err(|error| format!("cannot execute supplied npa binary: {error}"))?;
    npa_binary.verify()?;
    let elapsed_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    if !output.status.success() {
        return Err(format!(
            "npa child failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|_| "npa child stdout is not UTF-8".to_owned())?;
    let sample = parse_child_json(stdout.trim(), population, ordinal, elapsed_ns)?;
    repository
        .temporary
        .cleanup()
        .map_err(|error| format!("cannot clean changed-selection temporary root: {error}"))?;
    Ok(sample)
}

fn run_changed_selection_sample(
    profile: &Profile,
    population: Population,
    npa_binary: &AttachedExecutable,
) -> Result<ChangedSelectionBenchmarkSample, String> {
    run_sample_at(profile, population, npa_binary, 0)
}

fn run_samples(
    profile: &Profile,
    population: Population,
    npa_binary: &AttachedExecutable,
    warmup: u64,
    samples: u64,
) -> Result<Vec<ChangedSelectionBenchmarkSample>, String> {
    if samples == 0 {
        return Err("benchmark sample count must be nonzero".to_owned());
    }
    for _ in 0..warmup {
        let _ = run_changed_selection_sample(profile, population, npa_binary)?;
    }
    (0..samples)
        .map(|ordinal| run_sample_at(profile, population, npa_binary, ordinal))
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArtifactProvenance {
    source_revision: String,
    benchmark_executable_sha256: String,
    npa_executable_sha256: String,
    cargo_lock_sha256: String,
    rustc_vv: String,
    cargo_profile: String,
    cargo_features: Vec<String>,
    target: String,
    rustflags: String,
    benchmark_source_sha256: String,
    npa_main_source_sha256: String,
    production_source_set_sha256: String,
    git_version: String,
    build_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WorkloadProvenance {
    fixture_manifest_sha256: String,
    deterministic_baseline_sha256: String,
    candidate_profile: String,
    environment_profile: String,
    change_profile: String,
    command_lane: String,
    batch_policy: String,
    effective_argv_charge_bytes: u64,
    cache_policy: String,
    measurement_mode: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BenchmarkProvenance {
    artifact: ArtifactProvenance,
    workload: WorkloadProvenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CompletedRun {
    scenario_id: String,
    population: Population,
    provenance: BenchmarkProvenance,
    samples: Vec<ChangedSelectionBenchmarkSample>,
    median: u64,
    mad: u64,
}

fn sha256_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes = read_invocation_regular_file(path, MAX_EXECUTABLE_BYTES, "identity file")
        .map_err(|error| format!("cannot hash identity file {}: {error}", path.display()))?;
    Ok(sha256_bytes(&bytes))
}

fn command_identity(program: &Path, arguments: &[&str], label: &str) -> Result<String, String> {
    let output = Command::new(program)
        .args(arguments)
        .output()
        .map_err(|error| format!("cannot collect {label}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "cannot collect {label}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let value = std::str::from_utf8(&output.stdout)
        .map_err(|_| format!("{label} output is not UTF-8"))?
        .trim_end_matches(['\r', '\n'])
        .to_owned();
    validate_identity_text(&value, label)?;
    Ok(value)
}

fn frame_string(digest: &mut Sha256, value: &str) {
    digest.update(u64::try_from(value.len()).unwrap_or(u64::MAX).to_be_bytes());
    digest.update(value.as_bytes());
}

fn build_identity(artifact: &ArtifactProvenance) -> String {
    let mut digest = Sha256::new();
    for value in [
        artifact.source_revision.as_str(),
        artifact.benchmark_executable_sha256.as_str(),
        artifact.npa_executable_sha256.as_str(),
        artifact.cargo_lock_sha256.as_str(),
        artifact.rustc_vv.as_str(),
        artifact.cargo_profile.as_str(),
        artifact.target.as_str(),
        artifact.rustflags.as_str(),
        artifact.benchmark_source_sha256.as_str(),
        artifact.npa_main_source_sha256.as_str(),
        artifact.production_source_set_sha256.as_str(),
    ] {
        frame_string(&mut digest, value);
    }
    digest.update(
        u64::try_from(artifact.cargo_features.len())
            .unwrap_or(u64::MAX)
            .to_be_bytes(),
    );
    for feature in &artifact.cargo_features {
        frame_string(&mut digest, feature);
    }
    frame_string(&mut digest, &artifact.git_version);
    format!("{:x}", digest.finalize())
}

fn collect_artifact_provenance(npa_binary: &Path) -> Result<ArtifactProvenance, String> {
    let build = live_artifact_build_binding()?;
    collect_artifact_provenance_for_build(
        npa_binary,
        &build.source_revision,
        &build.cargo_lock_sha256,
        &build.cargo_features,
    )
}

struct NpaExecutableSnapshot {
    owner: ClosedPrivateDirectory,
    executable: Option<AttachedExecutable>,
    cleanup: Option<ClosedCleanupCatalog>,
}

impl NpaExecutableSnapshot {
    fn executable(&self) -> &AttachedExecutable {
        self.executable
            .as_ref()
            .expect("live npa snapshot retains its executable")
    }

    fn path(&self) -> &Path {
        self.executable().path()
    }

    fn sha256(&self) -> &str {
        self.executable().sha256()
    }

    fn verify(&self) -> Result<(), String> {
        self.executable().verify()
    }

    fn cleanup(mut self) -> Result<(), String> {
        self.executable.take();
        let cleanup = self
            .cleanup
            .take()
            .expect("live npa snapshot retains its cleanup catalog");
        self.owner.remove_captured_root(&cleanup)
    }
}

impl Drop for NpaExecutableSnapshot {
    fn drop(&mut self) {
        self.executable.take();
        if let Some(cleanup) = self.cleanup.take() {
            let _ = self.owner.remove_captured_root(&cleanup);
        }
    }
}

fn snapshot_npa_executable(source: &Path) -> Result<NpaExecutableSnapshot, String> {
    let owner = ClosedPrivateDirectory::new("npa-gitsel-executable")?;
    let executable = match owner.create_executable_snapshot(
        Path::new("npa"),
        source,
        MAX_EXECUTABLE_BYTES,
        "supplied npa executable",
    ) {
        Ok(executable) => executable,
        Err(error) => {
            let cleanup = owner.capture_cleanup_catalog().map_err(|cleanup_error| {
                format!("{error}; cannot capture failed snapshot cleanup: {cleanup_error}")
            })?;
            owner
                .remove_captured_root(&cleanup)
                .map_err(|cleanup_error| {
                    format!("{error}; cannot clean failed executable snapshot: {cleanup_error}")
                })?;
            return Err(error);
        }
    };
    let cleanup = match owner.capture_cleanup_catalog() {
        Ok(cleanup) => cleanup,
        Err(error) => {
            drop(executable);
            owner
                .remove_exact_root(&BTreeSet::from([PathBuf::from("npa")]))
                .map_err(|cleanup_error| {
                    format!(
                        "{error}; cannot clean uncataloged executable snapshot: {cleanup_error}"
                    )
                })?;
            return Err(error);
        }
    };
    Ok(NpaExecutableSnapshot {
        owner,
        executable: Some(executable),
        cleanup: Some(cleanup),
    })
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("npa-core workspace is canonical")
}

fn current_source_revision() -> Result<String, String> {
    let workspace = workspace_root();
    let head = Command::new(GIT_PATH)
        .args([
            "-C",
            workspace.to_str().ok_or("workspace path is not UTF-8")?,
        ])
        .args(["rev-parse", "--verify", "HEAD"])
        .env_clear()
        .output()
        .map_err(|error| format!("cannot read runtime Git HEAD: {error}"))?;
    if !head.status.success() {
        return Err("cannot read runtime Git HEAD".to_owned());
    }
    let mut identity = std::str::from_utf8(&head.stdout)
        .map_err(|_| "runtime Git HEAD is not UTF-8".to_owned())?
        .trim()
        .to_owned();
    validate_source_revision(&identity)?;
    let status = Command::new(GIT_PATH)
        .args([
            "-C",
            workspace.to_str().ok_or("workspace path is not UTF-8")?,
        ])
        .args(["status", "--porcelain", "--untracked-files=normal"])
        .env_clear()
        .output()
        .map_err(|error| format!("cannot read runtime Git status: {error}"))?;
    if !status.status.success() {
        return Err("cannot read runtime Git status".to_owned());
    }
    if !status.stdout.is_empty() {
        identity.push_str("-dirty");
    }
    Ok(identity)
}

fn collect_artifact_provenance_for_build(
    npa_binary: &Path,
    source_revision: &str,
    cargo_lock_sha256: &str,
    cargo_features: &[String],
) -> Result<ArtifactProvenance, String> {
    if source_revision == "unbound" {
        return Err(
            "benchmark was built without NPA_BENCH_SOURCE_IDENTITY; rebuild the exact source"
                .to_owned(),
        );
    }
    validate_source_revision(source_revision)?;
    validate_executable(npa_binary, "npa binary")?;
    let build = artifact_build_binding(source_revision, cargo_lock_sha256, cargo_features)?;
    validate_npa_build_attestation(npa_binary, &build)?;
    let benchmark = env::current_exe()
        .map_err(|error| format!("benchmark executable is unavailable: {error}"))?
        .canonicalize()
        .map_err(|error| format!("benchmark executable cannot be canonicalized: {error}"))?;
    let mut artifact = ArtifactProvenance {
        source_revision: source_revision.to_owned(),
        benchmark_executable_sha256: sha256_file(&benchmark)?,
        npa_executable_sha256: sha256_file(npa_binary)?,
        cargo_lock_sha256: cargo_lock_sha256.to_owned(),
        rustc_vv: build.rustc_vv,
        cargo_profile: build.cargo_profile,
        cargo_features: build.cargo_features,
        target: build.target,
        rustflags: build.rustflags,
        benchmark_source_sha256: build.benchmark_source_sha256,
        npa_main_source_sha256: build.npa_main_source_sha256,
        production_source_set_sha256: build.production_source_set_sha256,
        git_version: command_identity(Path::new(GIT_PATH), &["--version"], "Git version")?,
        build_identity_sha256: String::new(),
    };
    artifact.build_identity_sha256 = build_identity(&artifact);
    Ok(artifact)
}

fn validate_npa_build_attestation(
    npa_binary: &Path,
    build: &ArtifactBuildBinding,
) -> Result<(), String> {
    let output = Command::new(npa_binary)
        .arg("--build-provenance-json-v2")
        .env_clear()
        .output()
        .map_err(|error| format!("cannot collect supplied npa build provenance: {error}"))?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err("supplied npa build provenance command failed or wrote stderr".to_owned());
    }
    let source = std::str::from_utf8(&output.stdout)
        .map_err(|_| "supplied npa build provenance is not UTF-8".to_owned())?;
    let source = source
        .strip_suffix('\n')
        .ok_or("supplied npa build provenance must end in one LF")?;
    if source.contains('\n') || source.contains('\r') {
        return Err("supplied npa build provenance must be one JSON line".to_owned());
    }
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid supplied npa build provenance at {}", error.offset))?;
    let fields = exact_object(
        document.root(),
        &[
            "schema",
            "source_revision",
            "cargo_lock_sha256",
            "rustc_vv",
            "cargo_profile",
            "target",
            "cargo_features",
            "rustflags",
            "npa_main_source_sha256",
            "production_source_set_sha256",
        ],
        "supplied npa build provenance",
    )?;
    expect_exact_string(
        fields[0].value(),
        "npa.cli.build_provenance.v2",
        "supplied npa build provenance.schema",
    )?;
    let expected_scalars = [
        (build.source_revision.as_str(), "source_revision"),
        (build.cargo_lock_sha256.as_str(), "cargo_lock_sha256"),
        (build.rustc_vv.as_str(), "rustc_vv"),
        (build.cargo_profile.as_str(), "cargo_profile"),
        (build.target.as_str(), "target"),
    ];
    for (index, (expected, name)) in expected_scalars.iter().enumerate() {
        expect_exact_string(
            fields[index + 1].value(),
            expected,
            &format!("supplied npa build provenance.{name}"),
        )?;
    }
    let actual_features = fields[6]
        .value()
        .array_elements()
        .ok_or("supplied npa build provenance.cargo_features must be an array")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            expect_string(
                value,
                &format!("supplied npa build provenance.cargo_features[{index}]"),
            )
            .map(str::to_owned)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if actual_features != build.cargo_features {
        return Err("supplied npa Cargo features do not match benchmark build".to_owned());
    }
    expect_exact_string(
        fields[7].value(),
        &build.rustflags,
        "supplied npa build provenance.rustflags",
    )?;
    expect_exact_string(
        fields[8].value(),
        &build.npa_main_source_sha256,
        "supplied npa build provenance.npa_main_source_sha256",
    )?;
    expect_exact_string(
        fields[9].value(),
        &build.production_source_set_sha256,
        "supplied npa build provenance.production_source_set_sha256",
    )?;
    Ok(())
}

fn validate_declared_build_inputs(
    artifact: &ArtifactProvenance,
    source_revision: &str,
    cargo_profile: &str,
    cargo_features: &[String],
) -> Result<(), String> {
    if source_revision != artifact.source_revision
        || cargo_profile != artifact.cargo_profile
        || cargo_features != artifact.cargo_features
    {
        return Err(
            "caller-declared source/profile/features do not match embedded build provenance"
                .to_owned(),
        );
    }
    Ok(())
}

fn decode_build_hex(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("embedded build metadata has odd hex length".to_owned());
    }
    let bytes = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let high = hex_digit(pair[0])?;
            let low = hex_digit(pair[1])?;
            Ok((high << 4) | low)
        })
        .collect::<Result<Vec<_>, String>>()?;
    String::from_utf8(bytes).map_err(|_| "embedded build metadata is not UTF-8".to_owned())
}

fn hex_digit(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("embedded build metadata contains non-hex input".to_owned()),
    }
}

fn embedded_cargo_features() -> Vec<String> {
    let mut features = env!("NPA_CLI_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    features.sort();
    features.dedup();
    features
}

fn validate_runtime_production_source_set() -> Result<String, String> {
    const DOMAIN: &[u8] = b"npa-gitsel-source-set-v1\0";
    let expected = env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256");
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("canonicalize GITSEL workspace: {error}"))?;
    let paths = env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_PATHS");
    let observed = hash_runtime_source_set(&workspace, paths, DOMAIN)?;
    if observed != expected {
        return Err(format!(
            "runtime GITSEL source set {observed} does not match embedded build source set {expected}"
        ));
    }
    Ok(expected.to_owned())
}

fn hash_runtime_source_set(workspace: &Path, paths: &str, domain: &[u8]) -> Result<String, String> {
    if paths.is_empty() {
        return Err("embedded GITSEL source set is empty".to_owned());
    }
    let mut digest = Sha256::new();
    digest.update(domain);
    let workspace = RuntimeSourceDirectory::open(workspace)?;
    let mut observed_paths = BTreeSet::new();
    for relative in paths.split(',') {
        if relative.is_empty()
            || relative.starts_with('/')
            || relative.split('/').any(|component| component == "..")
            || !observed_paths.insert(relative)
        {
            return Err("embedded GITSEL source paths are noncanonical".to_owned());
        }
        let bytes = workspace.read(relative)?;
        digest.update(
            u64::try_from(relative.len())
                .map_err(|_| "GITSEL source path length exceeds u64".to_owned())?
                .to_le_bytes(),
        );
        digest.update(relative.as_bytes());
        digest.update(
            u64::try_from(bytes.len())
                .map_err(|_| "GITSEL source byte length exceeds u64".to_owned())?
                .to_le_bytes(),
        );
        digest.update(&bytes);
    }
    Ok(format!("{:x}", digest.finalize()))
}

const MAX_GITSEL_SOURCE_FILE_BYTES: u64 = 67_108_864;

#[cfg(unix)]
struct RuntimeSourceDirectory {
    file: File,
}

#[cfg(unix)]
impl RuntimeSourceDirectory {
    fn open(path: &Path) -> Result<Self, String> {
        let mut components = Vec::<OsString>::new();
        let mut directory = if path.is_absolute() {
            open_runtime_directory(None, OsStr::new("/"))?
        } else {
            open_runtime_directory(None, OsStr::new("."))?
        };
        for component in path.components() {
            match component {
                std::path::Component::RootDir | std::path::Component::CurDir => {}
                std::path::Component::Normal(component) => components.push(component.to_owned()),
                std::path::Component::ParentDir => {
                    if components.pop().is_none() {
                        return Err("GITSEL workspace escapes its retained root".to_owned());
                    }
                }
                std::path::Component::Prefix(_) => {
                    return Err("GITSEL workspace prefix is unsupported".to_owned())
                }
            }
        }
        for component in components {
            directory = open_runtime_directory(Some(&directory), &component)?;
        }
        Ok(Self { file: directory })
    }

    fn read(&self, relative: &str) -> Result<Vec<u8>, String> {
        use std::os::{
            fd::{AsRawFd, FromRawFd},
            unix::ffi::OsStrExt,
        };

        let components = Path::new(relative).components().collect::<Vec<_>>();
        let mut directory = self.file.try_clone().map_err(|error| error.to_string())?;
        for (index, component) in components.iter().enumerate() {
            let std::path::Component::Normal(component) = component else {
                return Err("embedded GITSEL source paths are noncanonical".to_owned());
            };
            if index + 1 < components.len() {
                directory = open_runtime_directory(Some(&directory), component)?;
                continue;
            }
            let component = CString::new(component.as_bytes())
                .map_err(|_| "GITSEL source path contains NUL".to_owned())?;
            // SAFETY: the retained directory fd and C string are valid.
            let descriptor = unsafe {
                libc::openat(
                    directory.as_raw_fd(),
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                )
            };
            if descriptor < 0 {
                return Err(format!(
                    "open GITSEL source {relative}: {}",
                    std::io::Error::last_os_error()
                ));
            }
            // SAFETY: descriptor is freshly owned.
            let mut file = unsafe { File::from_raw_fd(descriptor) };
            let metadata = file.metadata().map_err(|error| error.to_string())?;
            if !metadata.file_type().is_file() || metadata.len() > MAX_GITSEL_SOURCE_FILE_BYTES {
                return Err(format!(
                    "GITSEL source is not a bounded regular file: {relative}"
                ));
            }
            let mut bytes = Vec::new();
            std::io::Read::by_ref(&mut file)
                .take(MAX_GITSEL_SOURCE_FILE_BYTES + 1)
                .read_to_end(&mut bytes)
                .map_err(|error| error.to_string())?;
            if bytes.len() as u64 > MAX_GITSEL_SOURCE_FILE_BYTES {
                return Err(format!("GITSEL source exceeds byte limit: {relative}"));
            }
            return Ok(bytes);
        }
        Err("embedded GITSEL source path is empty".to_owned())
    }
}

#[cfg(unix)]
fn open_runtime_directory(parent: Option<&File>, name: &OsStr) -> Result<File, String> {
    use std::os::{
        fd::{AsRawFd, FromRawFd},
        unix::ffi::OsStrExt,
    };

    let name = CString::new(name.as_bytes())
        .map_err(|_| "GITSEL directory path contains NUL".to_owned())?;
    let descriptor = unsafe {
        match parent {
            Some(parent) => libc::openat(
                parent.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            ),
            None => libc::open(
                name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            ),
        }
    };
    if descriptor < 0 {
        return Err(format!(
            "open GITSEL directory: {}",
            std::io::Error::last_os_error()
        ));
    }
    Ok(unsafe { File::from_raw_fd(descriptor) })
}

#[cfg(not(unix))]
struct RuntimeSourceDirectory;

#[cfg(not(unix))]
impl RuntimeSourceDirectory {
    fn open(_path: &Path) -> Result<Self, String> {
        Err("GITSEL source-set validation requires Unix no-follow I/O".to_owned())
    }

    fn read(&self, _relative: &str) -> Result<Vec<u8>, String> {
        Err("GITSEL source-set validation requires Unix no-follow I/O".to_owned())
    }
}

fn validate_executable(path: &Path, label: &str) -> Result<(), String> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| format!("{label} is unavailable: {error}"))?;
    if metadata.file_type().is_symlink() {
        return Err(format!("{label} must not be a symbolic link"));
    }
    if !metadata.is_file() {
        return Err(format!("{label} is not a regular file"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o111 == 0 {
            return Err(format!("{label} is not executable"));
        }
    }
    Ok(())
}

fn resolve_executable(path: &Path, label: &str) -> Result<PathBuf, String> {
    validate_executable(path, label)?;
    path.canonicalize()
        .map_err(|error| format!("{label} cannot be canonicalized: {error}"))
}

fn valid_hash(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn json_escape(value: &str) -> String {
    let mut out = String::new();
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            character if character.is_control() => {
                out.push_str(&format!("\\u{:04x}", u32::from(character)))
            }
            character => out.push(character),
        }
    }
    out
}

fn string_array_json(values: &[String]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!("\"{}\"", json_escape(value)))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn artifact_fields_json(artifact: &ArtifactProvenance) -> String {
    format!(
        "\"source_revision\":\"{}\",\"benchmark_executable_sha256\":\"{}\",\"npa_executable_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"cargo_features\":{},\"target\":\"{}\",\"rustflags\":\"{}\",\"benchmark_source_sha256\":\"{}\",\"npa_main_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\",\"git_version\":\"{}\",\"build_identity_sha256\":\"{}\"",
        json_escape(&artifact.source_revision),
        artifact.benchmark_executable_sha256,
        artifact.npa_executable_sha256,
        artifact.cargo_lock_sha256,
        json_escape(&artifact.rustc_vv),
        json_escape(&artifact.cargo_profile),
        string_array_json(&artifact.cargo_features),
        json_escape(&artifact.target),
        json_escape(&artifact.rustflags),
        artifact.benchmark_source_sha256,
        artifact.npa_main_source_sha256,
        artifact.production_source_set_sha256,
        json_escape(&artifact.git_version),
        artifact.build_identity_sha256,
    )
}

fn artifact_sidecar_json(artifact: &ArtifactProvenance) -> Result<String, String> {
    validate_artifact_fields(artifact)?;
    Ok(format!(
        "{{\"schema\":\"{ARTIFACT_SCHEMA}\",{}}}\n",
        artifact_fields_json(artifact)
    ))
}

fn validate_artifact_fields(artifact: &ArtifactProvenance) -> Result<(), String> {
    validate_source_revision(&artifact.source_revision)?;
    for (label, hash) in [
        (
            "benchmark executable hash",
            &artifact.benchmark_executable_sha256,
        ),
        ("npa executable hash", &artifact.npa_executable_sha256),
        ("Cargo.lock hash", &artifact.cargo_lock_sha256),
        ("benchmark source hash", &artifact.benchmark_source_sha256),
        ("npa main source hash", &artifact.npa_main_source_sha256),
        (
            "production source-set hash",
            &artifact.production_source_set_sha256,
        ),
        ("build identity hash", &artifact.build_identity_sha256),
    ] {
        if !valid_hash(hash) {
            return Err(format!(
                "{label} must be 64 lowercase hexadecimal characters"
            ));
        }
    }
    validate_identity_text(&artifact.rustc_vv, "rustc -Vv")?;
    validate_identity_string(&artifact.cargo_profile, "cargo profile")?;
    validate_identity_string(&artifact.target, "target")?;
    if artifact
        .rustflags
        .bytes()
        .any(|byte| byte.is_ascii_control() && byte != 0x1f)
    {
        return Err("rustflags must contain printable text or Cargo unit separators".to_owned());
    }
    validate_identity_string(&artifact.git_version, "Git version")?;
    if artifact
        .cargo_features
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
        || artifact
            .cargo_features
            .iter()
            .any(|feature| validate_identity_string(feature, "cargo feature").is_err())
    {
        return Err("cargo features must be sorted and duplicate-free".to_owned());
    }
    if build_identity(artifact) != artifact.build_identity_sha256 {
        return Err("build identity hash mismatch".to_owned());
    }
    Ok(())
}

fn parse_artifact_sidecar(source: &str) -> Result<ArtifactProvenance, String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid provenance JSON at {}", error.offset))?;
    let fields = exact_object(
        document.root(),
        &[
            "schema",
            "source_revision",
            "benchmark_executable_sha256",
            "npa_executable_sha256",
            "cargo_lock_sha256",
            "rustc_vv",
            "cargo_profile",
            "cargo_features",
            "target",
            "rustflags",
            "benchmark_source_sha256",
            "npa_main_source_sha256",
            "production_source_set_sha256",
            "git_version",
            "build_identity_sha256",
        ],
        "artifact provenance",
    )?;
    expect_exact_string(
        fields[0].value(),
        ARTIFACT_SCHEMA,
        "artifact provenance.schema",
    )?;
    let features = fields[7]
        .value()
        .array_elements()
        .ok_or("artifact provenance.cargo_features must be an array")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            expect_string(
                value,
                &format!("artifact provenance.cargo_features[{index}]"),
            )
            .map(str::to_owned)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let artifact = ArtifactProvenance {
        source_revision: expect_string(fields[1].value(), "artifact provenance.source_revision")?
            .to_owned(),
        benchmark_executable_sha256: expect_string(
            fields[2].value(),
            "artifact provenance.benchmark_executable_sha256",
        )?
        .to_owned(),
        npa_executable_sha256: expect_string(
            fields[3].value(),
            "artifact provenance.npa_executable_sha256",
        )?
        .to_owned(),
        cargo_lock_sha256: expect_string(
            fields[4].value(),
            "artifact provenance.cargo_lock_sha256",
        )?
        .to_owned(),
        rustc_vv: expect_string(fields[5].value(), "artifact provenance.rustc_vv")?.to_owned(),
        cargo_profile: expect_string(fields[6].value(), "artifact provenance.cargo_profile")?
            .to_owned(),
        cargo_features: features,
        target: expect_string(fields[8].value(), "artifact provenance.target")?.to_owned(),
        rustflags: expect_string(fields[9].value(), "artifact provenance.rustflags")?.to_owned(),
        benchmark_source_sha256: expect_string(
            fields[10].value(),
            "artifact provenance.benchmark_source_sha256",
        )?
        .to_owned(),
        npa_main_source_sha256: expect_string(
            fields[11].value(),
            "artifact provenance.npa_main_source_sha256",
        )?
        .to_owned(),
        production_source_set_sha256: expect_string(
            fields[12].value(),
            "artifact provenance.production_source_set_sha256",
        )?
        .to_owned(),
        git_version: expect_string(fields[13].value(), "artifact provenance.git_version")?
            .to_owned(),
        build_identity_sha256: expect_string(
            fields[14].value(),
            "artifact provenance.build_identity_sha256",
        )?
        .to_owned(),
    };
    validate_artifact_fields(&artifact)?;
    Ok(artifact)
}

fn write_artifact_sidecar(directory: &Path, artifact: &ArtifactProvenance) -> Result<(), String> {
    let source = artifact_sidecar_json(artifact)?;
    write_invocation_regular_file_create_or_same(
        &directory.join("provenance.json"),
        source.as_bytes(),
        MAX_ARTIFACT_SIDECAR_BYTES,
        "artifact provenance",
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArtifactBuildBinding {
    source_revision: String,
    cargo_lock_sha256: String,
    rustc_vv: String,
    cargo_profile: String,
    cargo_features: Vec<String>,
    target: String,
    rustflags: String,
    benchmark_source_sha256: String,
    npa_main_source_sha256: String,
    production_source_set_sha256: String,
}

fn artifact_build_binding(
    source_revision: &str,
    cargo_lock_sha256: &str,
    cargo_features: &[String],
) -> Result<ArtifactBuildBinding, String> {
    if source_revision == "unbound" {
        return Err(
            "benchmark was built without NPA_BENCH_SOURCE_IDENTITY; rebuild the exact source"
                .to_owned(),
        );
    }
    let build = ArtifactBuildBinding {
        source_revision: source_revision.to_owned(),
        cargo_lock_sha256: cargo_lock_sha256.to_owned(),
        rustc_vv: decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"))?,
        cargo_profile: env!("NPA_CLI_BUILD_CARGO_PROFILE").to_owned(),
        cargo_features: cargo_features.to_vec(),
        target: env!("NPA_CLI_BUILD_TARGET").to_owned(),
        rustflags: decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"))?,
        benchmark_source_sha256: env!("NPA_CLI_BUILD_GITSEL_HARNESS_SOURCE_SHA256").to_owned(),
        npa_main_source_sha256: env!("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256").to_owned(),
        production_source_set_sha256: env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256").to_owned(),
    };
    validate_artifact_build_binding_shape(&build)?;
    Ok(build)
}

fn live_artifact_build_binding() -> Result<ArtifactBuildBinding, String> {
    let source_revision = env!("NPA_CLI_BUILD_SOURCE_REVISION");
    let runtime_source_revision = current_source_revision()?;
    if runtime_source_revision != source_revision {
        return Err(format!(
            "runtime source identity {runtime_source_revision:?} does not match embedded build identity {source_revision:?}"
        ));
    }
    let runtime_lock = sha256_file(&workspace_root().join("Cargo.lock"))?;
    if runtime_lock != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime Cargo.lock does not match embedded build provenance".to_owned());
    }
    let build = artifact_build_binding(
        source_revision,
        env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256"),
        &embedded_cargo_features(),
    )?;
    let runtime_source_set = validate_runtime_production_source_set()?;
    if runtime_source_set != build.production_source_set_sha256 {
        return Err("runtime production source set does not match embedded provenance".to_owned());
    }
    Ok(build)
}

fn preserved_artifact_build_binding() -> Result<ArtifactBuildBinding, String> {
    artifact_build_binding(
        env!("NPA_CLI_BUILD_SOURCE_REVISION"),
        env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256"),
        &embedded_cargo_features(),
    )
}

fn validate_artifact_build_binding_shape(build: &ArtifactBuildBinding) -> Result<(), String> {
    validate_source_revision(&build.source_revision)?;
    for (label, value) in [
        ("Cargo.lock", &build.cargo_lock_sha256),
        ("benchmark source", &build.benchmark_source_sha256),
        ("npa main source", &build.npa_main_source_sha256),
        ("production source set", &build.production_source_set_sha256),
    ] {
        if !valid_hash(value) {
            return Err(format!(
                "embedded {label} hash must be 64 lowercase hexadecimal characters"
            ));
        }
    }
    if build.rustc_vv.is_empty() || build.cargo_profile.is_empty() || build.target.is_empty() {
        return Err("embedded build provenance contains an empty identity".to_owned());
    }
    if build
        .cargo_features
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err("embedded Cargo features are not canonical".to_owned());
    }
    Ok(())
}

fn validate_artifact_build_binding(
    artifact: &ArtifactProvenance,
    build: &ArtifactBuildBinding,
) -> Result<(), String> {
    for (label, actual, expected) in [
        (
            "source revision",
            artifact.source_revision.as_str(),
            build.source_revision.as_str(),
        ),
        (
            "Cargo.lock hash",
            artifact.cargo_lock_sha256.as_str(),
            build.cargo_lock_sha256.as_str(),
        ),
        (
            "rustc identity",
            artifact.rustc_vv.as_str(),
            build.rustc_vv.as_str(),
        ),
        (
            "Cargo profile",
            artifact.cargo_profile.as_str(),
            build.cargo_profile.as_str(),
        ),
        ("target", artifact.target.as_str(), build.target.as_str()),
        (
            "rustflags",
            artifact.rustflags.as_str(),
            build.rustflags.as_str(),
        ),
        (
            "benchmark source hash",
            artifact.benchmark_source_sha256.as_str(),
            build.benchmark_source_sha256.as_str(),
        ),
        (
            "npa main source hash",
            artifact.npa_main_source_sha256.as_str(),
            build.npa_main_source_sha256.as_str(),
        ),
        (
            "production source-set hash",
            artifact.production_source_set_sha256.as_str(),
            build.production_source_set_sha256.as_str(),
        ),
    ] {
        if actual != expected {
            return Err(format!(
                "artifact {label} does not match preserved benchmark build"
            ));
        }
    }
    if artifact.cargo_features != build.cargo_features {
        return Err("artifact Cargo features do not match preserved benchmark build".to_owned());
    }
    Ok(())
}

fn validate_artifact_bundle_for_build(
    directory: &Path,
    build: &ArtifactBuildBinding,
) -> Result<(ArtifactProvenance, String), String> {
    let benchmark = directory.join(BENCHMARK_BASENAME);
    let npa = directory.join(NPA_BASENAME);
    validate_executable(&benchmark, "preserved benchmark executable")?;
    validate_executable(&npa, "preserved npa executable")?;
    let source = String::from_utf8(read_invocation_regular_file(
        &directory.join("provenance.json"),
        MAX_ARTIFACT_SIDECAR_BYTES,
        "artifact provenance",
    )?)
    .map_err(|_| "artifact provenance is not UTF-8".to_owned())?;
    let artifact = parse_artifact_sidecar(&source)?;
    if artifact_sidecar_json(&artifact)? != source {
        return Err("artifact provenance is not canonical JSON".to_owned());
    }
    if sha256_file(&benchmark)? != artifact.benchmark_executable_sha256 {
        return Err("preserved benchmark executable hash mismatch".to_owned());
    }
    if sha256_file(&npa)? != artifact.npa_executable_sha256 {
        return Err("preserved npa executable hash mismatch".to_owned());
    }
    validate_artifact_build_binding(&artifact, build)?;
    validate_npa_build_attestation(&npa, build)?;
    Ok((artifact, source))
}

fn validate_artifact_bundle(directory: &Path) -> Result<(ArtifactProvenance, String), String> {
    validate_artifact_bundle_for_build(directory, &preserved_artifact_build_binding()?)
}

fn batch_policy_string(policy: PerformancePackageSelectionBatchPolicy) -> &'static str {
    match policy {
        PerformancePackageSelectionBatchPolicy::NotSelected => "not_selected",
        PerformancePackageSelectionBatchPolicy::ExecBudget => "exec_budget",
        PerformancePackageSelectionBatchPolicy::Legacy128 => "legacy128",
    }
}

fn observation_json(observation: &ChangedSelectionBenchmarkObservation) -> String {
    let value = observation.selection;
    format!(
        "{{\"measurement_schema\":\"{}\",\"overflowed\":{},\"batch_policy\":\"{}\",\"candidate_paths\":{},\"pathspec_payload_bytes\":{},\"effective_argv_charge_bytes\":{},\"max_batch_payload_bytes\":{},\"max_batch_argv_charge_bytes\":{},\"pathspec_batches\":{},\"worktree_root_queries\":{},\"head_queries\":{},\"tracked_queries\":{},\"untracked_queries\":{},\"tracked_output_paths\":{},\"untracked_output_paths\":{},\"selected_paths\":{}}}",
        json_escape(&observation.measurement_schema),
        value.overflowed,
        batch_policy_string(value.batch_policy),
        value.candidate_paths,
        value.pathspec_payload_bytes,
        value.effective_argv_charge_bytes,
        value.max_batch_payload_bytes,
        value.max_batch_argv_charge_bytes,
        value.pathspec_batches,
        value.worktree_root_queries,
        value.head_queries,
        value.tracked_queries,
        value.untracked_queries,
        value.tracked_output_paths,
        value.untracked_output_paths,
        value.selected_paths,
    )
}

fn workload_json(workload: &WorkloadProvenance) -> String {
    format!(
        "{{\"fixture_manifest_sha256\":\"{}\",\"deterministic_baseline_sha256\":\"{}\",\"candidate_profile\":\"{}\",\"environment_profile\":\"{}\",\"change_profile\":\"{}\",\"command_lane\":\"{}\",\"batch_policy\":\"{}\",\"effective_argv_charge_bytes\":{},\"cache_policy\":\"{}\",\"measurement_mode\":\"{}\"}}",
        workload.fixture_manifest_sha256,
        workload.deterministic_baseline_sha256,
        json_escape(&workload.candidate_profile),
        json_escape(&workload.environment_profile),
        json_escape(&workload.change_profile),
        json_escape(&workload.command_lane),
        json_escape(&workload.batch_policy),
        workload.effective_argv_charge_bytes,
        json_escape(&workload.cache_policy),
        json_escape(&workload.measurement_mode),
    )
}

fn benchmark_run_json(run: &CompletedRun) -> Result<String, String> {
    if run.samples.len() != usize::try_from(SAMPLES).unwrap() {
        return Err("benchmark run must contain exactly seven samples".to_owned());
    }
    validate_artifact_fields(&run.provenance.artifact)?;
    if !valid_hash(&run.provenance.workload.fixture_manifest_sha256)
        || !valid_hash(&run.provenance.workload.deterministic_baseline_sha256)
    {
        return Err("workload hashes must be 64 lowercase hexadecimal characters".to_owned());
    }
    let workload = &run.provenance.workload;
    if workload.measurement_mode != run.population.as_str()
        || workload.command_lane != "vf"
        || workload.cache_policy != "disabled"
    {
        return Err("workload identity disagrees with the run population/lane".to_owned());
    }
    let profile = PROFILES
        .iter()
        .find(|profile| profile.id() == run.scenario_id)
        .ok_or("run scenario is outside the closed catalog")?;
    if workload.candidate_profile != profile.candidate_profile()
        || workload.environment_profile != profile.environment
        || workload.change_profile != profile.change
    {
        return Err("workload profile identity disagrees with the scenario catalog".to_owned());
    }
    match run.population {
        Population::TimingOffTotal
            if workload.batch_policy == "unobserved"
                && workload.effective_argv_charge_bytes == 0 => {}
        Population::TimingSummarySelection
            if matches!(
                workload.batch_policy.as_str(),
                "not_selected" | "exec_budget" | "legacy128"
            ) => {}
        _ => return Err("workload batch policy is invalid for the population".to_owned()),
    }
    let mut samples = Vec::with_capacity(run.samples.len());
    let mut summary_observation = None;
    for (index, sample) in run.samples.iter().enumerate() {
        let expected = u64::try_from(index).unwrap();
        match (run.population, sample) {
            (
                Population::TimingOffTotal,
                ChangedSelectionBenchmarkSample::TimingOffTotal {
                    ordinal,
                    elapsed_ns,
                },
            ) if *ordinal == expected => samples.push(format!(
                "{{\"ordinal\":{ordinal},\"status\":\"passed\",\"elapsed_ns\":{elapsed_ns}}}"
            )),
            (
                Population::TimingSummarySelection,
                ChangedSelectionBenchmarkSample::TimingSummarySelection {
                    ordinal,
                    selection_ms,
                    observation,
                },
            ) if *ordinal == expected => {
                let selection = observation.selection;
                if workload.batch_policy != batch_policy_string(selection.batch_policy)
                    || workload.effective_argv_charge_bytes != selection.effective_argv_charge_bytes
                    || !matches!(
                        observation.measurement_schema.as_str(),
                        "npa.performance.measurements.v0.5"
                            | "npa.performance.measurements.v0.6"
                            | "npa.performance.measurements.v0.7"
                            | "npa.performance.measurements.v0.8"
                            | "npa.performance.measurements.v0.9"
                    )
                    || selection.overflowed
                {
                    return Err("summary workload and observation disagree".to_owned());
                }
                if summary_observation
                    .as_ref()
                    .is_some_and(|prior| prior != observation)
                {
                    return Err("summary observations differ inside one run".to_owned());
                }
                summary_observation = Some(observation.clone());
                samples.push(format!(
                    "{{\"ordinal\":{ordinal},\"status\":\"passed\",\"selection_ms\":{selection_ms},\"observation\":{}}}",
                    observation_json(observation)
                ));
            }
            _ => return Err("sample population or ordinal mismatch".to_owned()),
        }
    }
    let unit = match run.population {
        Population::TimingOffTotal => "nanoseconds",
        Population::TimingSummarySelection => "milliseconds",
    };
    Ok(format!(
        "{{\"schema\":\"{RUN_SCHEMA}\",\"trusted\":false,\"proof_evidence\":false,\"scenario_id\":\"{}\",\"population\":\"{}\",\"provenance\":{{\"schema\":\"{PROVENANCE_SCHEMA}\",\"artifact\":{{{}}},\"workload\":{}}},\"warmup\":{WARMUP},\"sample_count\":{SAMPLES},\"status\":\"passed\",\"samples\":[{}],\"summary\":{{\"unit\":\"{unit}\",\"median\":{},\"mad\":{}}},\"elapsed_gate\":\"advisory\"}}",
        json_escape(&run.scenario_id),
        run.population.as_str(),
        artifact_fields_json(&run.provenance.artifact),
        workload_json(&run.provenance.workload),
        samples.join(","),
        run.median,
        run.mad,
    ))
}

fn main() {
    if let Err(error) = run() {
        eprintln!("changed-selection benchmark failed: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let arguments = match parse_arguments(&args)? {
        Invocation::List => {
            for profile in PROFILES {
                println!("{}", profile.id());
            }
            return Ok(());
        }
        Invocation::CheckArtifact { directory } => {
            let (_, canonical) = validate_artifact_bundle(&directory)?;
            print!("{canonical}");
            return Ok(());
        }
        Invocation::WriteArtifact {
            directory,
            npa_binary,
            source_revision,
            cargo_lock,
            cargo_profile,
            cargo_features,
        } => {
            validate_executable(
                &directory.join(BENCHMARK_BASENAME),
                "preserved benchmark executable",
            )?;
            validate_executable(&directory.join(NPA_BASENAME), "preserved npa executable")?;
            let artifact = collect_artifact_provenance(&npa_binary)?;
            validate_declared_build_inputs(
                &artifact,
                &source_revision,
                &cargo_profile,
                &cargo_features,
            )?;
            if sha256_file(&cargo_lock)? != artifact.cargo_lock_sha256 {
                return Err("caller Cargo.lock does not match embedded build provenance".to_owned());
            }
            if sha256_file(&directory.join(BENCHMARK_BASENAME))?
                != artifact.benchmark_executable_sha256
                || sha256_file(&directory.join(NPA_BASENAME))? != artifact.npa_executable_sha256
                || npa_binary
                    .canonicalize()
                    .map_err(|error| format!("cannot canonicalize supplied npa binary: {error}"))?
                    != directory
                        .join(NPA_BASENAME)
                        .canonicalize()
                        .map_err(|error| {
                            format!("cannot canonicalize preserved npa binary: {error}")
                        })?
            {
                return Err("artifact writer inputs do not match the preserved bundle".to_owned());
            }
            write_artifact_sidecar(&directory, &artifact)?;
            return Ok(());
        }
        Invocation::Benchmark(arguments) => arguments,
    };
    let profile = *PROFILES
        .iter()
        .find(|profile| arguments.scenario == profile.id())
        .ok_or_else(|| format!("unknown changed-selection scenario: {}", arguments.scenario))?;
    let npa_binary = resolve_executable(&arguments.npa_binary, "npa binary")?;
    let npa_snapshot = snapshot_npa_executable(&npa_binary)?;
    let fixture_bytes = read_invocation_regular_file(
        &arguments.fixture_manifest,
        MAX_FIXTURE_MANIFEST_BYTES,
        "fixture manifest",
    )?;
    let fixture_source = std::str::from_utf8(&fixture_bytes)
        .map_err(|_| "fixture manifest is not UTF-8".to_owned())?;
    validate_performance_fixture_selection(
        fixture_source,
        PerformanceFixtureSelection {
            scenario: &arguments.scenario,
            kind: "package-changed-selection-git-batching",
            package_root: profile.package_root,
            verifier: "fast",
            cache_policy: "disabled",
            warmup: WARMUP,
            samples: SAMPLES,
        },
    )
    .map_err(|error| format!("fixture manifest mismatch: {error}"))?;
    let baseline_bytes = read_invocation_regular_file(
        &arguments.deterministic_baseline,
        MAX_DETERMINISTIC_BASELINE_BYTES,
        "deterministic baseline",
    )?;
    let baseline_source = std::str::from_utf8(&baseline_bytes)
        .map_err(|_| "deterministic baseline is not UTF-8".to_owned())?;
    let iut_manifest = if profile.candidate_profile() == "i1401" {
        Some(
            String::from_utf8(read_invocation_regular_file(
                &reviewed_iut_root()?.join("npa-package.toml"),
                MAX_IUT_MANIFEST_BYTES,
                "reviewed IUT manifest",
            )?)
            .map_err(|_| "reviewed IUT manifest is not UTF-8".to_owned())?,
        )
    } else {
        None
    };
    let catalog = profile_catalog(profile, iut_manifest.as_deref())?;
    let expected = deterministic_observation(profile, &catalog);
    let artifact = collect_artifact_provenance(npa_snapshot.path())?;
    if artifact.npa_executable_sha256 != npa_snapshot.sha256() {
        return Err("supplied npa executable snapshot disagrees with artifact identity".to_owned());
    }
    let samples = run_samples(
        &profile,
        arguments.population,
        npa_snapshot.executable(),
        WARMUP,
        SAMPLES,
    )?;
    let (policy, effective_charge, values) = match arguments.population {
        Population::TimingOffTotal => {
            let values = samples
                .iter()
                .map(|sample| match sample {
                    ChangedSelectionBenchmarkSample::TimingOffTotal { elapsed_ns, .. } => {
                        Ok(*elapsed_ns)
                    }
                    _ => Err("timing-off run retained a summary sample".to_owned()),
                })
                .collect::<Result<Vec<_>, _>>()?;
            ("unobserved".to_owned(), 0, values)
        }
        Population::TimingSummarySelection => {
            let expected: PerformancePackageSelectionObservation = expected.try_into()?;
            let mut first = None::<Box<ChangedSelectionBenchmarkObservation>>;
            let mut values = Vec::with_capacity(samples.len());
            for sample in &samples {
                let ChangedSelectionBenchmarkSample::TimingSummarySelection {
                    selection_ms,
                    observation,
                    ..
                } = sample
                else {
                    return Err("timing-summary run retained an off sample".to_owned());
                };
                validate_package_changed_selection_baseline(
                    baseline_source,
                    &arguments.scenario,
                    observation.selection,
                )
                .map_err(|error| format!("deterministic baseline mismatch: {error}"))?;
                if observation.selection != expected {
                    return Err(
                        "live selection observation disagrees with catalog oracle".to_owned()
                    );
                }
                if first.as_ref().is_some_and(|prior| prior != observation) {
                    return Err("selection observation changed inside one benchmark run".to_owned());
                }
                first = Some(observation.clone());
                values.push(*selection_ms);
            }
            let first = first.ok_or("timing-summary run has no observation")?;
            (
                batch_policy_string(first.selection.batch_policy).to_owned(),
                first.selection.effective_argv_charge_bytes,
                values,
            )
        }
    };
    let (median, mad) = elapsed_median_and_mad(values)?;
    let completed = CompletedRun {
        scenario_id: arguments.scenario,
        population: arguments.population,
        provenance: BenchmarkProvenance {
            artifact,
            workload: WorkloadProvenance {
                fixture_manifest_sha256: sha256_bytes(&fixture_bytes),
                deterministic_baseline_sha256: sha256_bytes(&baseline_bytes),
                candidate_profile: profile.candidate_profile().to_owned(),
                environment_profile: profile.environment.to_owned(),
                change_profile: profile.change.to_owned(),
                command_lane: "vf".to_owned(),
                batch_policy: policy,
                effective_argv_charge_bytes: effective_charge,
                cache_policy: "disabled".to_owned(),
                measurement_mode: arguments.population.as_str().to_owned(),
            },
        },
        samples,
        median,
        mad,
    };
    npa_snapshot.verify()?;
    println!("{}", benchmark_run_json(&completed)?);
    npa_snapshot.cleanup()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reviewed_iut_manifest_source() -> String {
        fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../../npa-project-iut/proofs/npa-package.toml"),
        )
        .expect("the reviewed IUT checkout is present for the repository integration test")
    }

    #[test]
    fn canonical_candidate_catalogs_match_all_hash_oracles() {
        let expected = [
            (
                "empty0.clean",
                0,
                0,
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                "tiny1.clean",
                96,
                97,
                "3d7c8e25a3884e0c7a9927d818871901c42ab22505804fe6125216d6a17cd9a0",
            ),
            (
                "former127.clean",
                12_192,
                12_319,
                "258b4bf4d00010a7a3c45173aea905d8c09427e7f98c6cedc71d4ab453c9a1dc",
            ),
            (
                "former128.clean",
                12_288,
                12_416,
                "816e843f2730297a022595e14f95dd3d3d48e447720453e33da1417aff993d58",
            ),
            (
                "former129.clean",
                12_384,
                12_513,
                "2f51af077009ee9f4f93a157425750f0ea408d5c45e155f58bbd67232372fb63",
            ),
            (
                "count1023.clean",
                32_736,
                33_759,
                "462a98fe878b47a88d8a3a95d5d35c2f2f7f771fcd74e0d74557da9727e024a4",
            ),
            (
                "count1024.clean",
                32_768,
                33_792,
                "f6778845725032097a4b341b80987e6ac786af17bdb651f8014234c9c4c64805",
            ),
            (
                "count1025.clean",
                32_800,
                33_825,
                "85aa6647e78f20cb62ab99e15b3a02420ad13e4119ab0c3d645e9e9a9f585155",
            ),
            (
                "byte65535.clean",
                52_885,
                53_435,
                "7e5d5b8271a85b1c70e2ac5732e58c692c383321d407772b58455651bdfa0130",
            ),
            (
                "byte65536.clean",
                52_886,
                53_436,
                "ace1e0e7bcfc3cd583e846c999fde4dbf489bbde93e7b88dd6b99964ac1fc6f8",
            ),
            (
                "byte65537.clean",
                52_887,
                53_437,
                "5eaa743cfda0a2319965d520517a7d4375a18227def837f521e17e3159f9960d",
            ),
            (
                "long32.mixed",
                24_576,
                24_608,
                "c9dfd0aaf6972b5a730779f898ad4889f3f6910ddaa40a46df5c3084bd3044d9",
            ),
            (
                "long128.mixed",
                98_304,
                98_432,
                "be6d7c4727e082c448f5848d03b553b5b3231580f0b6a9f6686e3a3dafbea24b",
            ),
            (
                "long1024.mixed",
                786_432,
                787_456,
                "81aa8851d6b3158f4abd3921eb92c95ce250080dc4c043e9973fd6a7871583be",
            ),
            (
                "fallback1.clean",
                96,
                97,
                "7db67a3531655a5829d6ee1b722850d9c8c5cc87fe7a2814e74a1583048367be",
            ),
            (
                "fallback129.clean",
                12_384,
                12_513,
                "6efaff3808e9ec43d0a0e18a0872a6df8ca514c509dc0fc6e222fb72ff7b38c9",
            ),
            (
                "fallback1024.clean",
                98_304,
                99_328,
                "fdeb4d631346fa80cf91d9a11ba8d519cbf47e43c68f16343bd78bb563017306",
            ),
            (
                "inflated129.clean",
                12_384,
                12_513,
                "3cf906ab7fabcb81d72ce5a1fc007921fdf5326398ca0d4eacb95c97973a7cca",
            ),
            (
                "inflated992.clean",
                95_232,
                96_224,
                "e555a099bee7be1dfc3615c5439cb0089abbcf76ca63b2455913ac776ba78192",
            ),
            (
                "large4096.mixed",
                393_216,
                397_312,
                "87b2b1137f41907e29c6590b9cff2eda3c536935b7335f01076aa26d9ee3e4ed",
            ),
        ];
        for (suffix, path_bytes, nul_bytes, hash) in expected {
            let profile = *PROFILES
                .iter()
                .find(|profile| profile.suffix == suffix)
                .unwrap();
            let catalog = generated_catalog(profile).unwrap();
            assert!(catalog.windows(2).all(|pair| pair[0] < pair[1]));
            assert!(catalog
                .iter()
                .flat_map(|path| path.split('/'))
                .all(|part| part.len() <= 200));
            assert_eq!(catalog.iter().map(String::len).sum::<usize>(), path_bytes);
            assert_eq!(path_bytes + catalog.len(), nul_bytes);
            assert_eq!(nul_hash(&catalog), hash, "{suffix}");
        }

        let iut_manifest = reviewed_iut_manifest_source();
        let iut = iut_catalog_from_manifest(&iut_manifest).unwrap();
        assert_eq!(iut.len(), 1_401);
        assert_eq!(iut.iter().map(String::len).sum::<usize>(), 177_575);
        assert_eq!(iut.iter().map(String::len).min(), Some(55));
        assert_eq!(iut.iter().map(String::len).max(), Some(184));
        assert_eq!(
            nul_hash(&iut),
            "434e068753f94f9ddcadf6159538cdd7497a2b29dc3eafe405db1f3c623ce663"
        );
    }

    #[test]
    fn closed_catalog_has_twenty_five_exact_ids() {
        assert_eq!(PROFILES.len(), 25);
        let ids = PROFILES
            .iter()
            .map(|profile| format!("{PREFIX}{}", profile.suffix))
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(ids.len(), 25);
    }

    #[test]
    fn benchmark_arguments_resolve_one_changed_selection_scenario() {
        let arguments = [
            "--scenario",
            "package.changed_selection.git_batching.v1.tiny1.clean",
            "--population",
            "timing-summary-selection",
            "--fixture-manifest",
            "fixtures.json",
            "--deterministic-baseline",
            "baseline.json",
            "--npa-binary",
            "npa",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
        let Invocation::Benchmark(parsed) = parse_arguments(&arguments).unwrap() else {
            panic!("expected benchmark invocation")
        };
        assert_eq!(
            parsed,
            BenchmarkArguments {
                scenario: "package.changed_selection.git_batching.v1.tiny1.clean".to_owned(),
                population: Population::TimingSummarySelection,
                fixture_manifest: PathBuf::from("fixtures.json"),
                deterministic_baseline: PathBuf::from("baseline.json"),
                npa_binary: PathBuf::from("npa"),
            }
        );
        for invalid in [
            vec!["--scenario", "x"],
            vec![
                "--scenario",
                "x",
                "--scenario",
                "y",
                "--population",
                "timing-off-total",
            ],
            vec!["--population", "summary"],
            vec!["--list", "--scenario", "x"],
        ] {
            let invalid = invalid.into_iter().map(str::to_owned).collect::<Vec<_>>();
            assert!(parse_arguments(&invalid).is_err(), "{invalid:?}");
        }
    }

    #[test]
    fn provenance_source_revision_is_caller_bound() {
        assert!(validate_source_revision("0123456789abcdef0123456789abcdef01234567").is_ok());
        assert!(validate_source_revision("0123456789abcdef0123456789abcdef01234567-dirty").is_ok());
        for invalid in [
            "",
            "0123456",
            "0123456789abcdef0123456789abcdef0123456",
            "0123456789abcdef0123456789abcdef012345678",
            "0123456789ABCDEF0123456789ABCDEF01234567",
            "g123456789abcdef0123456789abcdef01234567",
        ] {
            assert!(validate_source_revision(invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn relative_npa_binary_is_resolved_before_repository_current_dir() {
        let current_dir = env::current_dir().unwrap().canonicalize().unwrap();
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .canonicalize()
            .unwrap();
        assert_eq!(current_dir, manifest_dir);
        let workspace = manifest_dir.join("../..").canonicalize().unwrap();
        let current_exe = env::current_exe().unwrap().canonicalize().unwrap();
        let relative = Path::new("../..").join(
            current_exe
                .strip_prefix(&workspace)
                .expect("Cargo example tests execute below the workspace"),
        );
        let resolved = resolve_executable(&relative, "test executable").unwrap();
        assert!(resolved.is_absolute());
        assert_eq!(resolved, current_exe);
    }

    fn valid_summary_child(observation: PerformancePackageSelectionObservation) -> String {
        let mut recorder = npa_api::PerformanceMeasurementRecorder::new(
            npa_api::PerformanceMeasurementMode::Summary,
        );
        recorder.observe_package_selection(&observation);
        let measurements = npa_api::performance_measurement_report_json(
            &recorder.report().expect("summary report"),
        );
        let mut output = String::from(
            "{\"schema\":\"npa.package.command_result.v0.5\",\"status\":\"passed\",\"timings\":{\"schema\":\"npa.package.timings.v0.2\",\"mode\":\"summary\",\"unit\":\"ms\",\"proof_evidence\":false,\"build_evidence\":false,\"trusted\":false,\"selection_ms\":9,\"measurements\":"
        );
        output.push_str(&measurements);
        output.push_str("}}");
        output
    }

    #[test]
    fn child_json_population_contract_is_strict() {
        let off = r#"{"schema":"npa.package.command_result.v0.5","status":"passed"}"#;
        assert_eq!(
            parse_child_json(off, Population::TimingOffTotal, 2, 17).unwrap(),
            ChangedSelectionBenchmarkSample::TimingOffTotal {
                ordinal: 2,
                elapsed_ns: 17
            }
        );
        let observation = PerformancePackageSelectionObservation {
            batch_policy: PerformancePackageSelectionBatchPolicy::ExecBudget,
            candidate_paths: 1,
            pathspec_payload_bytes: 230,
            effective_argv_charge_bytes: 65_536,
            max_batch_payload_bytes: 230,
            max_batch_argv_charge_bytes: 246,
            pathspec_batches: 1,
            worktree_root_queries: 1,
            head_queries: 1,
            tracked_queries: 1,
            untracked_queries: 1,
            tracked_output_paths: 1,
            untracked_output_paths: 0,
            selected_paths: 1,
            overflowed: false,
            ..PerformancePackageSelectionObservation::default()
        };
        let summary = valid_summary_child(observation);
        let parsed = parse_child_json(&summary, Population::TimingSummarySelection, 3, 0).unwrap();
        let ChangedSelectionBenchmarkSample::TimingSummarySelection {
            ordinal,
            selection_ms,
            observation: parsed,
        } = parsed
        else {
            panic!("expected summary sample")
        };
        assert_eq!(ordinal, 3);
        assert_eq!(selection_ms, 9);
        assert_eq!(parsed.selection, observation);
        assert!(parse_child_json(&summary, Population::TimingOffTotal, 0, 0).is_err());
        assert!(parse_child_json(off, Population::TimingSummarySelection, 0, 0).is_err());
        for malformed in [
            summary.replace("\"selection_ms\":9,", ""),
            summary.replace(
                "{\"label\":\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":1},",
                "",
            ),
            summary.replace(
                "{\"label\":\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":1}",
                "{\"label\":\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":1},{\"label\":\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":1}",
            ),
            summary.replace("\"unit\":\"count\"", "\"unit\":\"bytes\""),
            summary.replace(
                "\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":1",
                "\"package.selection_candidate_paths\",\"unit\":\"count\",\"value\":-1",
            ),
            summary.replace(
                "\"package.selection_exec_budget_policy\",\"unit\":\"count\",\"value\":1",
                "\"package.selection_exec_budget_policy\",\"unit\":\"count\",\"value\":2",
            ),
            summary.replace(
                "{\"label\":\"package.selection_exec_budget_policy\",\"unit\":\"count\",\"value\":1}",
                "{\"label\":\"package.selection_exec_budget_policy\",\"unit\":\"count\",\"value\":1},{\"label\":\"package.selection_legacy128_policy\",\"unit\":\"count\",\"value\":1}",
            ),
            summary.replace(
                "\"schema\":\"npa.package.command_result.v0.5\"",
                "\"schema\":\"npa.package.command_result.v9\"",
            ),
            summary.replace(
                "\"schema\":\"npa.performance.measurements.v0.9\"",
                "\"schema\":\"npa.performance.measurements.v9\"",
            ),
        ] {
            assert!(
                parse_child_json(&malformed, Population::TimingSummarySelection, 0, 0).is_err(),
                "{malformed}"
            );
        }
        let overflow = summary.replacen("\"overflowed\":false", "\"overflowed\":true", 1);
        let ChangedSelectionBenchmarkSample::TimingSummarySelection { observation, .. } =
            parse_child_json(&overflow, Population::TimingSummarySelection, 0, 0).unwrap()
        else {
            panic!("expected summary")
        };
        assert!(observation.selection.overflowed);
    }

    #[test]
    fn deterministic_changed_selection_fields_are_blocking() {
        const CHECKED_BASELINE: &str =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let iut_manifest = reviewed_iut_manifest_source();
        for profile in PROFILES.iter().copied() {
            let catalog = profile_catalog(profile, Some(&iut_manifest)).unwrap();
            let observation = deterministic_observation(profile, &catalog);
            validate_package_changed_selection_baseline(
                CHECKED_BASELINE,
                &profile.id(),
                observation.try_into().unwrap(),
            )
            .unwrap_or_else(|error| panic!("{}: {error}", profile.suffix));
            assert_eq!(
                observation.candidate_paths, profile.count,
                "{}",
                profile.suffix
            );
            assert_eq!(
                observation.worktree_root_queries,
                usize::from(profile.count > 0),
                "{}",
                profile.suffix
            );
            assert_eq!(observation.head_queries, observation.worktree_root_queries);
            assert_eq!(observation.tracked_queries, observation.pathspec_batches);
            assert_eq!(observation.untracked_queries, observation.pathspec_batches);
            assert!(observation.pathspec_batches <= 32);
            match profile.environment {
                "h0" => {
                    assert_eq!(observation.policy, BatchPolicy::Legacy128);
                    assert_eq!(observation.effective_argv_charge_bytes, 0);
                }
                _ if profile.count == 0 => {
                    assert_eq!(observation.policy, BatchPolicy::NotSelected)
                }
                "n64" => {
                    assert_eq!(observation.policy, BatchPolicy::ExecBudget);
                    assert_eq!(observation.effective_argv_charge_bytes, 65_536);
                    assert!(observation.max_batch_argv_charge_bytes <= 65_536);
                }
                "h16" => {
                    assert_eq!(observation.policy, BatchPolicy::ExecBudget);
                    assert_eq!(observation.effective_argv_charge_bytes, 16_384);
                    assert!(observation.max_batch_argv_charge_bytes <= 16_384);
                }
                _ => unreachable!(),
            }
        }
        let iut = *PROFILES
            .iter()
            .find(|profile| profile.suffix == "iut1401.clean")
            .unwrap();
        let catalog = profile_catalog(iut, Some(&iut_manifest)).unwrap();
        let observation = deterministic_observation(iut, &catalog);
        assert_eq!(observation.pathspec_batches, 10);
        assert_eq!(
            observation.tracked_queries + observation.untracked_queries,
            20
        );
        assert_eq!(observation.max_batch_argv_charge_bytes, 65_422);
    }

    fn test_artifact() -> ArtifactProvenance {
        let mut artifact = ArtifactProvenance {
            source_revision: "0123456789abcdef0123456789abcdef01234567".to_owned(),
            benchmark_executable_sha256: "11".repeat(32),
            npa_executable_sha256: "22".repeat(32),
            cargo_lock_sha256: "33".repeat(32),
            rustc_vv: "rustc 1.test\nbinary: rustc".to_owned(),
            cargo_profile: "release".to_owned(),
            cargo_features: vec!["alpha".to_owned(), "zeta".to_owned()],
            target: "test-target".to_owned(),
            rustflags: "-Ctest".to_owned(),
            benchmark_source_sha256: "44".repeat(32),
            npa_main_source_sha256: "55".repeat(32),
            production_source_set_sha256: "66".repeat(32),
            git_version: "git version 2.test".to_owned(),
            build_identity_sha256: String::new(),
        };
        artifact.build_identity_sha256 = build_identity(&artifact);
        artifact
    }

    fn test_build_binding(artifact: &ArtifactProvenance) -> ArtifactBuildBinding {
        ArtifactBuildBinding {
            source_revision: artifact.source_revision.clone(),
            cargo_lock_sha256: artifact.cargo_lock_sha256.clone(),
            rustc_vv: artifact.rustc_vv.clone(),
            cargo_profile: artifact.cargo_profile.clone(),
            cargo_features: artifact.cargo_features.clone(),
            target: artifact.target.clone(),
            rustflags: artifact.rustflags.clone(),
            benchmark_source_sha256: artifact.benchmark_source_sha256.clone(),
            npa_main_source_sha256: artifact.npa_main_source_sha256.clone(),
            production_source_set_sha256: artifact.production_source_set_sha256.clone(),
        }
    }

    #[test]
    fn provenance_build_identity_is_canonical() {
        let artifact = test_artifact();
        let identity = artifact.build_identity_sha256.clone();
        assert_eq!(identity, build_identity(&artifact));
        let mut reordered_input = artifact.clone();
        reordered_input.cargo_features = vec!["zeta".to_owned(), "alpha".to_owned()];
        assert_ne!(identity, build_identity(&reordered_input));
        let mut changed = artifact;
        changed.git_version.push_str(".changed");
        assert_ne!(identity, build_identity(&changed));
    }

    #[cfg(unix)]
    #[test]
    fn provenance_source_set_rejects_intermediate_directory_symlink() {
        let temporary = TemporaryRoot::create().unwrap();
        fs::create_dir(temporary.path.join("real")).unwrap();
        fs::write(temporary.path.join("real/member.rs"), b"source").unwrap();
        std::os::unix::fs::symlink(temporary.path.join("real"), temporary.path.join("linked"))
            .unwrap();
        let error = hash_runtime_source_set(
            &temporary.path,
            "linked/member.rs",
            b"npa-gitsel-source-set-test\0",
        )
        .unwrap_err();
        assert!(error.starts_with("open GITSEL directory:"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn temporary_root_is_private_and_canonical() {
        use std::os::unix::fs::PermissionsExt;
        let temporary = TemporaryRoot::create().unwrap();
        let metadata = fs::symlink_metadata(&temporary.path).unwrap();
        assert!(metadata.is_dir());
        assert!(!metadata.file_type().is_symlink());
        assert_eq!(metadata.permissions().mode() & 0o777, 0o700);
        assert_eq!(temporary.path, temporary.path.canonicalize().unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn temporary_root_cleanup_refuses_unknown_symlink_and_renamed_out_tree() {
        let temporary = TemporaryRoot::create().unwrap();
        fs::write(temporary.path.join("sentinel"), b"keep").unwrap();
        std::os::unix::fs::symlink("missing", temporary.path.join("unknown-link")).unwrap();
        let original = temporary.path.clone();
        let relocated = original.with_extension("relocated");
        fs::rename(&original, &relocated).unwrap();
        fs::create_dir(&original).unwrap();
        drop(temporary);
        assert_eq!(fs::read(relocated.join("sentinel")).unwrap(), b"keep");
        assert!(relocated.join("unknown-link").is_symlink());
        assert!(original.is_dir());
        fs::remove_dir(&original).unwrap();
        fs::remove_file(relocated.join("unknown-link")).unwrap();
        fs::remove_file(relocated.join("sentinel")).unwrap();
        fs::remove_dir(&relocated).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn temporary_root_cleanup_refuses_external_directory_renamed_in_after_capture() {
        let mut temporary = TemporaryRoot::create().unwrap();
        temporary
            .owner
            .create_new_file(Path::new("owned"), b"owned")
            .unwrap();
        temporary.arm_untrusted_cleanup().unwrap();

        let external = TemporaryRoot::create().unwrap();
        external
            .owner
            .create_directory(Path::new("external"))
            .unwrap();
        external
            .owner
            .create_new_file(Path::new("external/sentinel"), b"keep")
            .unwrap();
        fs::rename(
            external.path.join("external"),
            temporary.path.join("renamed-in"),
        )
        .unwrap();

        let retained = temporary.path.clone();
        drop(temporary);
        assert_eq!(fs::read(retained.join("owned")).unwrap(), b"owned");
        assert_eq!(
            fs::read(retained.join("renamed-in/sentinel")).unwrap(),
            b"keep"
        );

        fs::remove_file(retained.join("renamed-in/sentinel")).unwrap();
        fs::remove_dir(retained.join("renamed-in")).unwrap();
        fs::remove_file(retained.join("owned")).unwrap();
        fs::remove_dir(retained).unwrap();
    }

    #[test]
    fn provenance_record_shape_is_closed() {
        let artifact = test_artifact();
        let source = artifact_sidecar_json(&artifact).unwrap();
        let document = JsonDocument::parse(&source).unwrap();
        let fields = exact_object(
            document.root(),
            &[
                "schema",
                "source_revision",
                "benchmark_executable_sha256",
                "npa_executable_sha256",
                "cargo_lock_sha256",
                "rustc_vv",
                "cargo_profile",
                "cargo_features",
                "target",
                "rustflags",
                "benchmark_source_sha256",
                "npa_main_source_sha256",
                "production_source_set_sha256",
                "git_version",
                "build_identity_sha256",
            ],
            "artifact provenance",
        )
        .unwrap();
        assert_eq!(
            fields[7].value().array_elements().unwrap().len(),
            artifact.cargo_features.len()
        );
        for (index, field) in fields.iter().enumerate() {
            if index != 7 {
                assert!(field.value().string_value().is_some(), "{}", field.key());
            }
        }
        let unknown = source.replacen("{\"schema\":", "{\"unknown\":0,\"schema\":", 1);
        assert!(parse_artifact_sidecar(&unknown).is_err());

        let workload = test_workload(Population::TimingSummarySelection);
        let workload_source = workload_json(&workload);
        let workload_document = JsonDocument::parse(&workload_source).unwrap();
        let workload_fields = exact_object(
            workload_document.root(),
            &[
                "fixture_manifest_sha256",
                "deterministic_baseline_sha256",
                "candidate_profile",
                "environment_profile",
                "change_profile",
                "command_lane",
                "batch_policy",
                "effective_argv_charge_bytes",
                "cache_policy",
                "measurement_mode",
            ],
            "workload provenance",
        )
        .unwrap();
        assert_eq!(
            expect_u64(
                workload_fields[7].value(),
                "workload.effective_argv_charge_bytes"
            )
            .unwrap(),
            65_536
        );
        assert!(workload_fields
            .iter()
            .enumerate()
            .all(|(index, field)| index == 7 || field.value().string_value().is_some()));
    }

    #[test]
    fn provenance_workload_identity_separates_populations() {
        let base = WorkloadProvenance {
            fixture_manifest_sha256: "44".repeat(32),
            deterministic_baseline_sha256: "55".repeat(32),
            candidate_profile: "s1".to_owned(),
            environment_profile: "n64".to_owned(),
            change_profile: "none".to_owned(),
            command_lane: "vf".to_owned(),
            batch_policy: "unobserved".to_owned(),
            effective_argv_charge_bytes: 0,
            cache_policy: "disabled".to_owned(),
            measurement_mode: "timing-off-total".to_owned(),
        };
        let mut summary = base.clone();
        summary.batch_policy = "exec_budget".to_owned();
        summary.effective_argv_charge_bytes = 65_536;
        summary.measurement_mode = "timing-summary-selection".to_owned();
        assert_ne!(workload_json(&base), workload_json(&summary));
        assert!(!workload_json(&base).contains("65536"));
        assert!(workload_json(&summary).contains("65536"));
    }

    #[test]
    fn provenance_sidecar_writer_is_canonical_and_non_sampling() {
        let temporary = TemporaryRoot::create().unwrap();
        let artifact = test_artifact();
        write_artifact_sidecar(&temporary.path, &artifact).unwrap();
        let first = fs::read(temporary.path.join("provenance.json")).unwrap();
        write_artifact_sidecar(&temporary.path, &artifact).unwrap();
        let second = fs::read(temporary.path.join("provenance.json")).unwrap();
        assert_eq!(first, second);
        let mut changed = artifact.clone();
        changed.source_revision = "ff".repeat(20);
        changed.build_identity_sha256 = build_identity(&changed);
        let error = write_artifact_sidecar(&temporary.path, &changed).unwrap_err();
        assert!(
            error.contains("existing artifact provenance has different bytes"),
            "{error}"
        );
        assert_eq!(
            parse_artifact_sidecar(std::str::from_utf8(&first).unwrap()).unwrap(),
            artifact
        );
        let source = std::str::from_utf8(&first).unwrap();
        for forbidden in [
            "scenario",
            "sample",
            "fixture",
            "baseline",
            "elapsed",
            "environment",
        ] {
            assert!(!source.contains(forbidden), "{forbidden}");
        }
    }

    #[cfg(unix)]
    fn executable_file(path: &Path, bytes: &[u8]) {
        use std::os::unix::fs::PermissionsExt;
        fs::write(path, bytes).unwrap();
        let mut permissions = fs::metadata(path).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).unwrap();
    }

    #[cfg(unix)]
    fn attesting_npa(path: &Path, overrides: &[(&str, &str)]) {
        let mut values = BTreeMap::from([
            ("schema", "npa.cli.build_provenance.v2".to_owned()),
            (
                "source_revision",
                "0123456789abcdef0123456789abcdef01234567".to_owned(),
            ),
            ("cargo_lock_sha256", "33".repeat(32)),
            (
                "rustc_vv",
                decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX")).unwrap(),
            ),
            (
                "cargo_profile",
                env!("NPA_CLI_BUILD_CARGO_PROFILE").to_owned(),
            ),
            ("target", env!("NPA_CLI_BUILD_TARGET").to_owned()),
            (
                "rustflags",
                decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX")).unwrap(),
            ),
            (
                "npa_main_source_sha256",
                env!("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256").to_owned(),
            ),
            (
                "production_source_set_sha256",
                env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256").to_owned(),
            ),
        ]);
        for (key, value) in overrides {
            values.insert(*key, (*value).to_owned());
        }
        let features = string_array_json(&[]);
        let json = format!(
            "{{\"schema\":\"{}\",\"source_revision\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"cargo_features\":{},\"rustflags\":\"{}\",\"npa_main_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\"}}",
            json_escape(&values["schema"]),
            json_escape(&values["source_revision"]),
            json_escape(&values["cargo_lock_sha256"]),
            json_escape(&values["rustc_vv"]),
            json_escape(&values["cargo_profile"]),
            json_escape(&values["target"]),
            features,
            json_escape(&values["rustflags"]),
            json_escape(&values["npa_main_source_sha256"]),
            json_escape(&values["production_source_set_sha256"]),
        );
        raw_attesting_npa(path, &json);
    }

    #[cfg(unix)]
    fn raw_attesting_npa(path: &Path, json: &str) {
        executable_file(
            path,
            format!(
                "#!/bin/sh\nprintf '%s\\n' '{}'\n",
                json.replace('\'', "'\\''")
            )
            .as_bytes(),
        );
    }

    #[cfg(unix)]
    #[test]
    fn provenance_benchmark_executable_hash_matches_bytes() {
        let temporary = TemporaryRoot::create().unwrap();
        let npa = temporary.path.join("exact-npa");
        attesting_npa(&npa, &[]);
        let artifact = collect_artifact_provenance_for_build(
            &npa,
            "0123456789abcdef0123456789abcdef01234567",
            &"33".repeat(32),
            &[],
        )
        .unwrap();
        let current = env::current_exe().unwrap().canonicalize().unwrap();
        let independent = sha256_bytes(&fs::read(current).unwrap());
        assert_eq!(artifact.benchmark_executable_sha256, independent);
    }

    #[cfg(unix)]
    #[test]
    fn provenance_npa_executable_hash_uses_exact_path() {
        let temporary = TemporaryRoot::create().unwrap();
        let supplied_dir = temporary.path.join("supplied");
        let other_dir = temporary.path.join("other");
        fs::create_dir_all(&supplied_dir).unwrap();
        fs::create_dir_all(&other_dir).unwrap();
        let supplied = supplied_dir.join(NPA_BASENAME);
        let other = other_dir.join(NPA_BASENAME);
        attesting_npa(&supplied, &[]);
        executable_file(&other, b"other bytes");
        let artifact = collect_artifact_provenance_for_build(
            &supplied,
            "0123456789abcdef0123456789abcdef01234567",
            &"33".repeat(32),
            &[],
        )
        .unwrap();
        assert_eq!(
            artifact.npa_executable_sha256,
            sha256_file(&supplied).unwrap()
        );
        executable_file(&other, b"mutated unrelated same-basename bytes");
        assert_eq!(
            artifact.npa_executable_sha256,
            sha256_file(&supplied).unwrap()
        );
        assert_ne!(artifact.npa_executable_sha256, sha256_file(&other).unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn provenance_supplied_npa_attestation_rejects_every_build_mismatch() {
        let temporary = TemporaryRoot::create().unwrap();
        let npa = temporary.path.join("npa-attested");
        let source = "0123456789abcdef0123456789abcdef01234567";
        let lock = "33".repeat(32);
        let build = artifact_build_binding(source, &lock, &[]).unwrap();
        attesting_npa(&npa, &[]);
        assert!(validate_npa_build_attestation(&npa, &build).is_ok());
        for (field, wrong) in [
            (
                "source_revision",
                "ffffffffffffffffffffffffffffffffffffffff",
            ),
            (
                "cargo_lock_sha256",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            ),
            ("rustc_vv", "wrong rustc"),
            ("cargo_profile", "wrong-profile"),
            ("target", "wrong-target"),
            ("rustflags", "wrong-rustflags"),
            (
                "npa_main_source_sha256",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            ),
            (
                "production_source_set_sha256",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            ),
            ("schema", "npa.cli.build_provenance.v9"),
        ] {
            attesting_npa(&npa, &[(field, wrong)]);
            assert!(
                validate_npa_build_attestation(&npa, &build).is_err(),
                "{field}"
            );
        }
        attesting_npa(&npa, &[]);
        let unexpected_features =
            artifact_build_binding(source, &lock, &["unexpected".to_owned()]).unwrap();
        assert!(validate_npa_build_attestation(&npa, &unexpected_features).is_err());
        raw_attesting_npa(
            &npa,
            r#"{"schema":"npa.cli.build_provenance.v2","unknown":0}"#,
        );
        assert!(validate_npa_build_attestation(&npa, &build).is_err());
        raw_attesting_npa(
            &npa,
            r#"{"schema":"npa.cli.build_provenance.v2","schema":"npa.cli.build_provenance.v2"}"#,
        );
        assert!(validate_npa_build_attestation(&npa, &build).is_err());
        raw_attesting_npa(
            &npa,
            &format!(
                "{{\"source_revision\":\"{source}\",\"schema\":\"npa.cli.build_provenance.v2\",\"cargo_lock_sha256\":\"{lock}\",\"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\"target\":\"{}\",\"cargo_features\":[],\"rustflags\":\"{}\",\"npa_main_source_sha256\":\"{}\",\"production_source_set_sha256\":\"{}\"}}",
                json_escape(&decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX")).unwrap()),
                json_escape(env!("NPA_CLI_BUILD_CARGO_PROFILE")),
                json_escape(env!("NPA_CLI_BUILD_TARGET")),
                json_escape(&decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX")).unwrap()),
                env!("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256"),
                env!("NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256"),
            ),
        );
        assert!(validate_npa_build_attestation(&npa, &build).is_err());

        let symlink = temporary.path.join("npa-link");
        std::os::unix::fs::symlink(&npa, &symlink).unwrap();
        assert_eq!(
            validate_executable(&symlink, "npa binary").unwrap_err(),
            "npa binary must not be a symbolic link"
        );
    }

    #[cfg(unix)]
    #[test]
    fn provenance_sidecar_validation_rejects_every_mismatch() {
        let temporary = TemporaryRoot::create().unwrap();
        executable_file(&temporary.path.join(BENCHMARK_BASENAME), b"benchmark");
        let mut artifact = test_artifact();
        artifact.cargo_features.clear();
        attesting_npa(
            &temporary.path.join(NPA_BASENAME),
            &[
                ("source_revision", &artifact.source_revision),
                ("cargo_lock_sha256", &artifact.cargo_lock_sha256),
                ("rustc_vv", &artifact.rustc_vv),
                ("cargo_profile", &artifact.cargo_profile),
                ("target", &artifact.target),
                ("rustflags", &artifact.rustflags),
                ("npa_main_source_sha256", &artifact.npa_main_source_sha256),
                (
                    "production_source_set_sha256",
                    &artifact.production_source_set_sha256,
                ),
            ],
        );
        artifact.benchmark_executable_sha256 = sha256_bytes(b"benchmark");
        artifact.npa_executable_sha256 = sha256_file(&temporary.path.join(NPA_BASENAME)).unwrap();
        artifact.build_identity_sha256 = build_identity(&artifact);
        let build = test_build_binding(&artifact);
        write_artifact_sidecar(&temporary.path, &artifact).unwrap();
        let valid = validate_artifact_bundle_for_build(&temporary.path, &build);
        assert!(valid.is_ok(), "{valid:?}");

        let mut relabeled = Vec::new();
        for field in [
            "source_revision",
            "cargo_lock_sha256",
            "rustc_vv",
            "cargo_profile",
            "cargo_features",
            "target",
            "rustflags",
            "benchmark_source_sha256",
            "npa_main_source_sha256",
            "production_source_set_sha256",
        ] {
            let mut changed = artifact.clone();
            match field {
                "source_revision" => {
                    changed.source_revision = "ffffffffffffffffffffffffffffffffffffffff".to_owned()
                }
                "cargo_lock_sha256" => changed.cargo_lock_sha256 = "66".repeat(32),
                "rustc_vv" => changed.rustc_vv = "different rustc".to_owned(),
                "cargo_profile" => changed.cargo_profile = "different-profile".to_owned(),
                "cargo_features" => changed.cargo_features = vec!["different".to_owned()],
                "target" => changed.target = "different-target".to_owned(),
                "rustflags" => changed.rustflags = "-Cdifferent".to_owned(),
                "benchmark_source_sha256" => changed.benchmark_source_sha256 = "77".repeat(32),
                "npa_main_source_sha256" => changed.npa_main_source_sha256 = "88".repeat(32),
                "production_source_set_sha256" => {
                    changed.production_source_set_sha256 = "99".repeat(32)
                }
                _ => unreachable!(),
            }
            changed.build_identity_sha256 = build_identity(&changed);
            relabeled.push((field, changed));
        }
        for (field, changed) in relabeled {
            fs::write(
                temporary.path.join("provenance.json"),
                artifact_sidecar_json(&changed).unwrap(),
            )
            .unwrap();
            assert!(
                validate_artifact_bundle_for_build(&temporary.path, &build).is_err(),
                "{field}"
            );
        }
        fs::write(
            temporary.path.join("provenance.json"),
            artifact_sidecar_json(&artifact).unwrap(),
        )
        .unwrap();

        let canonical = fs::read_to_string(temporary.path.join("provenance.json")).unwrap();
        for corrupt in [
            canonical.replace(
                &format!("\"schema\":\"{ARTIFACT_SCHEMA}\""),
                &format!("\"schema\":\"{ARTIFACT_SCHEMA}\",\"unknown\":0"),
            ),
            canonical.replace("\"source_revision\":", "\"missing_source_revision\":"),
            canonical.replace(&artifact.build_identity_sha256, "not-a-canonical-identity"),
        ] {
            assert!(parse_artifact_sidecar(&corrupt).is_err());
        }

        fs::remove_file(temporary.path.join("provenance.json")).unwrap();
        let error = validate_artifact_bundle_for_build(&temporary.path, &build).unwrap_err();
        assert!(error.starts_with("open artifact provenance:"), "{error}");
        fs::write(temporary.path.join("provenance.json"), &canonical).unwrap();

        fs::remove_file(temporary.path.join(BENCHMARK_BASENAME)).unwrap();
        assert!(validate_artifact_bundle_for_build(&temporary.path, &build)
            .unwrap_err()
            .contains("preserved benchmark executable is unavailable"));
        executable_file(&temporary.path.join(BENCHMARK_BASENAME), b"benchmark");

        fs::remove_file(temporary.path.join(NPA_BASENAME)).unwrap();
        assert!(validate_artifact_bundle_for_build(&temporary.path, &build)
            .unwrap_err()
            .contains("preserved npa executable is unavailable"));
        attesting_npa(
            &temporary.path.join(NPA_BASENAME),
            &[
                ("source_revision", &artifact.source_revision),
                ("cargo_lock_sha256", &artifact.cargo_lock_sha256),
                ("rustc_vv", &artifact.rustc_vv),
                ("cargo_profile", &artifact.cargo_profile),
                ("target", &artifact.target),
                ("rustflags", &artifact.rustflags),
                ("npa_main_source_sha256", &artifact.npa_main_source_sha256),
                (
                    "production_source_set_sha256",
                    &artifact.production_source_set_sha256,
                ),
            ],
        );

        use std::os::unix::fs::PermissionsExt;
        let benchmark_path = temporary.path.join(BENCHMARK_BASENAME);
        let mut permissions = fs::metadata(&benchmark_path).unwrap().permissions();
        permissions.set_mode(0o644);
        fs::set_permissions(&benchmark_path, permissions).unwrap();
        assert_eq!(
            validate_artifact_bundle_for_build(&temporary.path, &build).unwrap_err(),
            "preserved benchmark executable is not executable"
        );
        executable_file(&benchmark_path, b"benchmark");

        fs::write(&benchmark_path, b"tampered benchmark").unwrap();
        assert_eq!(
            validate_artifact_bundle_for_build(&temporary.path, &build).unwrap_err(),
            "preserved benchmark executable hash mismatch"
        );
        executable_file(&benchmark_path, b"benchmark");

        fs::write(temporary.path.join(NPA_BASENAME), b"tampered").unwrap();
        assert_eq!(
            validate_artifact_bundle_for_build(&temporary.path, &build).unwrap_err(),
            "preserved npa executable hash mismatch"
        );

        raw_attesting_npa(
            &temporary.path.join(NPA_BASENAME),
            r#"{"schema":"npa.cli.build_provenance.v2","unknown":0}"#,
        );
        let mut bad_attestation = artifact.clone();
        bad_attestation.npa_executable_sha256 =
            sha256_file(&temporary.path.join(NPA_BASENAME)).unwrap();
        bad_attestation.build_identity_sha256 = build_identity(&bad_attestation);
        fs::write(
            temporary.path.join("provenance.json"),
            artifact_sidecar_json(&bad_attestation).unwrap(),
        )
        .unwrap();
        assert!(validate_artifact_bundle_for_build(&temporary.path, &build)
            .unwrap_err()
            .contains("supplied npa build provenance"));
    }

    fn test_workload(population: Population) -> WorkloadProvenance {
        WorkloadProvenance {
            fixture_manifest_sha256: "44".repeat(32),
            deterministic_baseline_sha256: "55".repeat(32),
            candidate_profile: "s1".to_owned(),
            environment_profile: "n64".to_owned(),
            change_profile: "t1".to_owned(),
            command_lane: "vf".to_owned(),
            batch_policy: if population == Population::TimingOffTotal {
                "unobserved".to_owned()
            } else {
                "exec_budget".to_owned()
            },
            effective_argv_charge_bytes: if population == Population::TimingOffTotal {
                0
            } else {
                65_536
            },
            cache_policy: "disabled".to_owned(),
            measurement_mode: population.as_str().to_owned(),
        }
    }

    fn test_observation() -> ChangedSelectionBenchmarkObservation {
        ChangedSelectionBenchmarkObservation {
            measurement_schema: "npa.performance.measurements.v0.9".to_owned(),
            selection: PerformancePackageSelectionObservation {
                batch_policy: PerformancePackageSelectionBatchPolicy::ExecBudget,
                candidate_paths: 1,
                pathspec_payload_bytes: 230,
                effective_argv_charge_bytes: 65_536,
                max_batch_payload_bytes: 230,
                max_batch_argv_charge_bytes: 246,
                pathspec_batches: 1,
                worktree_root_queries: 1,
                head_queries: 1,
                tracked_queries: 1,
                untracked_queries: 1,
                tracked_output_paths: 1,
                untracked_output_paths: 0,
                selected_paths: 1,
                overflowed: false,
                ..PerformancePackageSelectionObservation::default()
            },
        }
    }

    #[test]
    fn benchmark_run_json_is_closed_and_canonical() {
        let off = CompletedRun {
            scenario_id: format!("{PREFIX}tiny1.tracked1"),
            population: Population::TimingOffTotal,
            provenance: BenchmarkProvenance {
                artifact: test_artifact(),
                workload: test_workload(Population::TimingOffTotal),
            },
            samples: (0..SAMPLES)
                .map(|ordinal| ChangedSelectionBenchmarkSample::TimingOffTotal {
                    ordinal,
                    elapsed_ns: 100 + ordinal,
                })
                .collect(),
            median: 103,
            mad: 2,
        };
        let off_json = benchmark_run_json(&off).unwrap();
        assert_eq!(
            sha256_bytes(off_json.as_bytes()),
            "f90d456e3c5d2fd8202f5465caaf7a34abb3425192e30b502c6277a24de66d24"
        );
        let document = JsonDocument::parse(&off_json).unwrap();
        let root = exact_object(
            document.root(),
            &[
                "schema",
                "trusted",
                "proof_evidence",
                "scenario_id",
                "population",
                "provenance",
                "warmup",
                "sample_count",
                "status",
                "samples",
                "summary",
                "elapsed_gate",
            ],
            "run",
        )
        .unwrap();
        let provenance = exact_object(
            root[5].value(),
            &["schema", "artifact", "workload"],
            "run.provenance",
        )
        .unwrap();
        exact_object(
            provenance[1].value(),
            &[
                "source_revision",
                "benchmark_executable_sha256",
                "npa_executable_sha256",
                "cargo_lock_sha256",
                "rustc_vv",
                "cargo_profile",
                "cargo_features",
                "target",
                "rustflags",
                "benchmark_source_sha256",
                "npa_main_source_sha256",
                "production_source_set_sha256",
                "git_version",
                "build_identity_sha256",
            ],
            "run.provenance.artifact",
        )
        .unwrap();
        exact_object(
            provenance[2].value(),
            &[
                "fixture_manifest_sha256",
                "deterministic_baseline_sha256",
                "candidate_profile",
                "environment_profile",
                "change_profile",
                "command_lane",
                "batch_policy",
                "effective_argv_charge_bytes",
                "cache_policy",
                "measurement_mode",
            ],
            "run.provenance.workload",
        )
        .unwrap();
        let off_samples = root[9].value().array_elements().unwrap();
        for sample in off_samples {
            exact_object(
                sample,
                &["ordinal", "status", "elapsed_ns"],
                "run.samples[]",
            )
            .unwrap();
        }
        exact_object(root[10].value(), &["unit", "median", "mad"], "run.summary").unwrap();
        assert!(off_json.contains("\"unit\":\"nanoseconds\""));
        assert!(!off_json.contains("selection_ms"));
        assert!(!off_json.contains("observation"));

        let summary = CompletedRun {
            scenario_id: off.scenario_id.clone(),
            population: Population::TimingSummarySelection,
            provenance: BenchmarkProvenance {
                artifact: test_artifact(),
                workload: test_workload(Population::TimingSummarySelection),
            },
            samples: (0..SAMPLES)
                .map(
                    |ordinal| ChangedSelectionBenchmarkSample::TimingSummarySelection {
                        ordinal,
                        selection_ms: ordinal,
                        observation: Box::new(test_observation()),
                    },
                )
                .collect(),
            median: 3,
            mad: 2,
        };
        let summary_json = benchmark_run_json(&summary).unwrap();
        assert_eq!(
            sha256_bytes(summary_json.as_bytes()),
            "e650c543b3f56c609c8c4d5f98fe0061e046af3f4b604e5f918582c7fb8a0a1a"
        );
        let summary_document = JsonDocument::parse(&summary_json).unwrap();
        let summary_root = summary_document.root().object_members().unwrap();
        let summary_samples = summary_root[9].value().array_elements().unwrap();
        for sample in summary_samples {
            let sample = exact_object(
                sample,
                &["ordinal", "status", "selection_ms", "observation"],
                "run.samples[]",
            )
            .unwrap();
            exact_object(
                sample[3].value(),
                &[
                    "measurement_schema",
                    "overflowed",
                    "batch_policy",
                    "candidate_paths",
                    "pathspec_payload_bytes",
                    "effective_argv_charge_bytes",
                    "max_batch_payload_bytes",
                    "max_batch_argv_charge_bytes",
                    "pathspec_batches",
                    "worktree_root_queries",
                    "head_queries",
                    "tracked_queries",
                    "untracked_queries",
                    "tracked_output_paths",
                    "untracked_output_paths",
                    "selected_paths",
                ],
                "run.samples[].observation",
            )
            .unwrap();
        }
        assert!(summary_json.contains("\"unit\":\"milliseconds\""));
        assert!(summary_json.contains("\"selection_ms\":0"));
        assert!(!summary_json.contains("elapsed_ns"));
        for forbidden in [
            "NPA_CHANGED_SELECTION_BENCH_PADDING",
            "pathspecs",
            "stderr",
            "acceptance_threshold",
        ] {
            assert!(!summary_json.contains(forbidden));
        }
        let mut wrong_count = summary.clone();
        wrong_count.samples.pop();
        assert!(benchmark_run_json(&wrong_count).is_err());
        let mut wrong_population = summary;
        wrong_population.population = Population::TimingOffTotal;
        assert!(benchmark_run_json(&wrong_population).is_err());
    }

    #[test]
    fn provenance_json_is_canonical_and_redacted() {
        let run = CompletedRun {
            scenario_id: format!("{PREFIX}tiny1.tracked1"),
            population: Population::TimingSummarySelection,
            provenance: BenchmarkProvenance {
                artifact: test_artifact(),
                workload: test_workload(Population::TimingSummarySelection),
            },
            samples: (0..SAMPLES)
                .map(
                    |ordinal| ChangedSelectionBenchmarkSample::TimingSummarySelection {
                        ordinal,
                        selection_ms: 1,
                        observation: Box::new(test_observation()),
                    },
                )
                .collect(),
            median: 1,
            mad: 0,
        };
        let json = benchmark_run_json(&run).unwrap();
        let provenance_start = json.find("\"provenance\":").unwrap();
        assert!(json[provenance_start..].starts_with(&format!(
            "\"provenance\":{{\"schema\":\"{PROVENANCE_SCHEMA}\",\"artifact\":{{\"source_revision\""
        )));
        for forbidden in [
            "/tmp/",
            "NPA_CHANGED_SELECTION_BENCH_PADDING",
            "generated/short-package",
            "stderr",
        ] {
            assert!(!json.contains(forbidden), "{forbidden}");
        }
    }

    #[test]
    fn synthetic_packages_remain_valid_across_exact_git_states() {
        for suffix in [
            "empty0.clean",
            "tiny1.clean",
            "tiny1.tracked1",
            "tiny1.untracked1",
            "long32.mixed",
            "long1024.mixed",
            "large4096.mixed",
        ] {
            let profile = *PROFILES
                .iter()
                .find(|profile| profile.suffix == suffix)
                .unwrap();
            let catalog = generated_catalog(profile).unwrap();
            let repository = materialize_repository(profile, &catalog)
                .unwrap_or_else(|error| panic!("{suffix}: {error}"));
            assert_eq!(
                observed_changed_candidates(&repository.temporary.path, &catalog).unwrap(),
                expected_changed_candidates(profile, &catalog),
                "{suffix}"
            );
        }
    }

    #[cfg(unix)]
    fn changed_selection_stub(temporary: &TemporaryRoot) -> PathBuf {
        let path = temporary.path.join("npa");
        executable_file(
            &path,
            br#"#!/bin/sh
[ "$#" -eq 16 ] || exit 91
[ "$1" = package ] || exit 91
[ "$2" = verify-certs ] || exit 91
[ "$3" = --root ] || exit 91
[ "$5" = --changed ] || exit 91
[ "$6" = --package-lock ] || exit 91
[ "$7" = reconstructed ] || exit 91
[ "$8" = --checker ] || exit 91
[ "$9" = fast ] || exit 91
[ "${10}" = --audit-cache ] || exit 91
[ "${11}" = off ] || exit 91
[ "${12}" = --verifier-memo ] || exit 91
[ "${13}" = off ] || exit 91
[ "${14}" = --jobs ] || exit 91
[ "${15}" = 4 ] || exit 91
[ "${16}" = --json ] || exit 91
printf '%s\n' '{"schema":"npa.package.command_result.v0.5","status":"passed"}'
"#,
        );
        path
    }

    #[cfg(unix)]
    #[test]
    fn one_sample_uses_public_changed_selection_surface() {
        let binary_root = TemporaryRoot::create().unwrap();
        let binary = changed_selection_stub(&binary_root);
        let snapshot = snapshot_npa_executable(&binary).unwrap();
        let profile = PROFILES
            .iter()
            .find(|profile| profile.suffix == "tiny1.clean")
            .unwrap();
        let sample = run_changed_selection_sample(
            profile,
            Population::TimingOffTotal,
            snapshot.executable(),
        )
        .unwrap();
        assert!(matches!(
            sample,
            ChangedSelectionBenchmarkSample::TimingOffTotal { ordinal: 0, .. }
        ));
        snapshot.cleanup().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn warmups_are_excluded_from_retained_samples() {
        let binary_root = TemporaryRoot::create().unwrap();
        let binary = changed_selection_stub(&binary_root);
        let snapshot = snapshot_npa_executable(&binary).unwrap();
        let profile = PROFILES
            .iter()
            .find(|profile| profile.suffix == "tiny1.clean")
            .unwrap();
        let samples = run_samples(
            profile,
            Population::TimingOffTotal,
            snapshot.executable(),
            1,
            3,
        )
        .unwrap();
        assert_eq!(samples.len(), 3);
        assert_eq!(
            samples
                .iter()
                .map(|sample| match sample {
                    ChangedSelectionBenchmarkSample::TimingOffTotal { ordinal, .. } => *ordinal,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
        snapshot.cleanup().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn attached_npa_snapshot_drop_removes_only_its_captured_tree() {
        let binary_root = TemporaryRoot::create().unwrap();
        let binary = changed_selection_stub(&binary_root);
        let snapshot = snapshot_npa_executable(&binary).unwrap();
        let snapshot_root = snapshot.owner.path().to_owned();
        assert!(snapshot_root.is_dir());
        drop(snapshot);
        assert!(!snapshot_root.exists());
    }

    #[cfg(unix)]
    #[test]
    fn changed_selection_samples_execute_only_the_attached_npa_snapshot() {
        let binary_root = TemporaryRoot::create().unwrap();
        let binary = changed_selection_stub(&binary_root);
        let snapshot = snapshot_npa_executable(&binary).unwrap();
        let original_source = binary.with_extension("original");
        fs::rename(&binary, &original_source).unwrap();
        executable_file(&binary, b"#!/bin/sh\nexit 97\n");

        let profile = PROFILES
            .iter()
            .find(|profile| profile.suffix == "tiny1.clean")
            .unwrap();
        run_changed_selection_sample(profile, Population::TimingOffTotal, snapshot.executable())
            .unwrap();

        let relocated_snapshot = snapshot.path().with_file_name("relocated-npa");
        fs::rename(snapshot.path(), &relocated_snapshot).unwrap();
        executable_file(snapshot.path(), b"#!/bin/sh\nexit 98\n");
        assert!(run_changed_selection_sample(
            profile,
            Population::TimingOffTotal,
            snapshot.executable(),
        )
        .is_err());
        assert_eq!(fs::read(snapshot.path()).unwrap(), b"#!/bin/sh\nexit 98\n");

        fs::remove_file(snapshot.path()).unwrap();
        fs::rename(&relocated_snapshot, snapshot.path()).unwrap();
        snapshot.verify().unwrap();
        snapshot.cleanup().unwrap();
    }

    #[test]
    fn benchmark_materialization_preflight_respects_path_limits() {
        let long = *PROFILES
            .iter()
            .find(|profile| profile.suffix == "long1024.mixed")
            .unwrap();
        let paths = generated_catalog(long).unwrap();
        assert!(materialization_preflight(
            Path::new("/tmp/npa-gitsel"),
            &paths,
            Some(1024),
            Some(255)
        )
        .is_ok());
        let root_127 = format!("/{}", "r".repeat(126));
        assert!(
            materialization_preflight(Path::new(&root_127), &paths, Some(896), Some(255)).is_err()
        );
        assert!(materialization_preflight(
            Path::new("/tmp/npa-gitsel"),
            &paths,
            Some(1024),
            Some(199)
        )
        .is_err());
        let root_128 = format!("/{}", "r".repeat(127));
        assert!(
            materialization_preflight(Path::new(&root_128), &paths, Some(2048), Some(255)).is_err()
        );
        assert!(
            materialization_preflight(Path::new("/tmp/npa-gitsel"), &paths, None, Some(255))
                .is_err()
        );
        assert!(
            materialization_preflight(Path::new("/tmp/npa-gitsel"), &paths, Some(1024), None)
                .is_err()
        );
    }

    #[test]
    fn elapsed_summary_reports_median_and_mad() {
        assert_eq!(
            elapsed_median_and_mad(vec![8, 1, 7, 2, 6, 3, 5]),
            Ok((5, 2))
        );
        assert!(elapsed_median_and_mad(Vec::new()).is_err());
        assert!(elapsed_median_and_mad(vec![1, 2]).is_err());
    }
}

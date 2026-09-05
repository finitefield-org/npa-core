#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/performance_fixture_generator.rs"]
mod performance_fixture_generator;

use std::{
    io::Write as _,
    path::{Path, PathBuf},
};

use sha2::{Digest, Sha256};

use closed_private_tree::{
    create_new_invocation_file, read_invocation_regular_file,
    replace_invocation_regular_file_exact, ClosedPrivateDirectory,
};

const MAX_FIXTURE_MANIFEST_BYTES: u64 = 4 * 1024 * 1024;
const MAX_GENERATED_OUTPUT_BYTES: u64 = 16 * 1024 * 1024;

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn valid_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn read_bounded_regular_output(path: &Path, maximum_bytes: u64) -> Result<String, String> {
    let bytes = read_invocation_regular_file(path, maximum_bytes, "generator output")?;
    String::from_utf8(bytes).map_err(display_error)
}

fn publish_generated_output(
    path: &Path,
    bytes: &[u8],
    expected_preimage_sha256: Option<&str>,
) -> Result<(), String> {
    if expected_preimage_sha256.is_some_and(|hash| !valid_sha256(hash)) {
        return Err("expected output preimage is not a lowercase SHA-256".to_owned());
    }
    if u64::try_from(bytes.len()).map_err(display_error)? > MAX_GENERATED_OUTPUT_BYTES {
        return Err("generated output exceeds its byte limit".to_owned());
    }
    match expected_preimage_sha256 {
        None => {
            let mut output = create_new_invocation_file(path, "generator output")?;
            output.write_all(bytes).map_err(display_error)?;
            output.sync_all().map_err(display_error)
        }
        Some(expected_hash) => {
            let current = read_invocation_regular_file(
                path,
                MAX_GENERATED_OUTPUT_BYTES,
                "generator output preimage",
            )?;
            if hex_sha256(&current) != expected_hash {
                return Err("generator output preimage SHA-256 mismatch".to_owned());
            }
            replace_invocation_regular_file_exact(
                path,
                &current,
                bytes,
                MAX_GENERATED_OUTPUT_BYTES,
                "generator output",
            )
        }
    }
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod private_root_tests {
    use super::*;
    use std::fs;

    #[test]
    fn generator_publication_is_create_new_and_preimage_bound() {
        let root = ClosedPrivateDirectory::new("npa-snap-vmsp-publication-test").unwrap();
        let output = root.path().join("artifact.json");

        publish_generated_output(&output, b"first", None).unwrap();
        assert_eq!(read_bounded_regular_output(&output, 32).unwrap(), "first");
        assert!(publish_generated_output(&output, b"duplicate", None).is_err());
        assert!(publish_generated_output(&output, b"wrong", Some(&"0".repeat(64))).is_err());
        assert_eq!(read_bounded_regular_output(&output, 32).unwrap(), "first");

        publish_generated_output(&output, b"second", Some(&hex_sha256(b"first"))).unwrap();
        assert_eq!(read_bounded_regular_output(&output, 32).unwrap(), "second");
        root.remove_exact_file(Path::new("artifact.json"), b"second")
            .unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn generator_publication_rejects_symlink_leaf() {
        use std::os::unix::fs::symlink;

        let root = ClosedPrivateDirectory::new("npa-snap-vmsp-output-link-test").unwrap();
        let outside = root.path().with_extension("outside-file");
        fs::write(&outside, b"outside").unwrap();
        let link = root.path().join("artifact.json");
        symlink(&outside, &link).unwrap();

        assert!(publish_generated_output(&link, b"replacement", None).is_err());
        assert!(
            publish_generated_output(&link, b"replacement", Some(&hex_sha256(b"outside"))).is_err()
        );
        assert_eq!(fs::read(&outside).unwrap(), b"outside");

        fs::remove_file(&link).unwrap();
        root.remove_empty_root().unwrap();
        fs::remove_file(outside).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn generator_private_root_rejects_symlink_parent() {
        use std::os::unix::fs::symlink;

        let container = ClosedPrivateDirectory::new("npa-snap-vmsp-test-container").unwrap();
        let link = container.path().join("parent-link");
        symlink(container.path(), &link).unwrap();
        let error = match ClosedPrivateDirectory::new_in(&link, "npa-snap-vmsp-child") {
            Ok(_) => panic!("symlink temporary parent was accepted"),
            Err(error) => error,
        };
        assert_eq!(error, "temporary parent is not a real directory");
    }

    #[cfg(unix)]
    #[test]
    fn generator_private_root_drop_rejects_path_replacement() {
        let root = ClosedPrivateDirectory::new("npa-snap-vmsp-replacement-test").unwrap();
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

fn main() {
    if let Err(error) = run() {
        eprintln!("generate SNAP/VMSP performance manifest: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let (mode, output, update) = match args.as_slice() {
        [mode, output] => (mode.as_str(), PathBuf::from(output), None),
        [mode, output, flag, expected] if flag == "--update-existing" && valid_sha256(expected) => {
            (
                mode.as_str(),
                PathBuf::from(output),
                Some(expected.as_str()),
            )
        }
        _ => return Err(usage()),
    };
    match mode {
        "--output" => generate_manifest(output, update),
        "--oracle-output" => generate_oracle(output, update),
        "--snapshot-baseline-output" => generate_snapshot_baseline(output, update),
        _ => Err(usage()),
    }
}

fn usage() -> String {
    "usage: generate_snap_vmsp_performance_manifest (--output|--oracle-output|--snapshot-baseline-output) PATH [--update-existing EXPECTED_LOWERCASE_SHA256]".to_owned()
}

fn generate_manifest(output: PathBuf, update: Option<&str>) -> Result<(), String> {
    let source = String::from_utf8(read_invocation_regular_file(
        Path::new("testdata/performance/fixtures/manifest.v0.1.json"),
        MAX_FIXTURE_MANIFEST_BYTES,
        "v0.1 performance fixture manifest",
    )?)
    .map_err(display_error)?;
    let manifest = performance_fixture_generator::successor_manifest(&source)?;
    let parsed = npa_api::validate_performance_fixture_selection_v02(&manifest)
        .map_err(|error| error.to_string())?;
    let snapshot = parsed
        .scenarios
        .iter()
        .filter(|row| {
            matches!(
                row,
                npa_api::PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)
            )
        })
        .count();
    let shared = parsed
        .scenarios
        .iter()
        .filter(|row| {
            matches!(
                row,
                npa_api::PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                    | npa_api::PerformanceFixtureSelectionV02::SharedPayloadCache(_)
                    | npa_api::PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
                    | npa_api::PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                    | npa_api::PerformanceFixtureSelectionV02::SharedPayloadShard(_)
                    | npa_api::PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
            )
        })
        .count();
    if snapshot != 40 || shared != 47 {
        return Err(format!(
            "generated wrong catalog cardinality: SNAP={snapshot} VMSP={shared}"
        ));
    }
    publish_generated_output(&output, manifest.as_bytes(), update)
}

fn generate_oracle(output: PathBuf, update: Option<&str>) -> Result<(), String> {
    let temporary = ClosedPrivateDirectory::new("npa-snap-vmsp-oracle")?;
    let profiles = [
        "representative-1000-certificates",
        "synthetic-1kib",
        "synthetic-1mib",
        "synthetic-near-limit",
        "payload-1mib",
        "payload-16mib",
        "payload-near-limit",
        "payload-heavy-multi-module",
        "session-index",
        "small-certificate",
    ];
    let result = (|| {
        let mut rows = vec![performance_fixture_generator::ORACLE_TSV_HEADER.to_owned()];
        for profile in profiles {
            eprintln!("generating fixture oracle: {profile}");
            let relative = PathBuf::from(profile);
            let generated = performance_fixture_generator::materialize_fixture_profile(
                profile, &temporary, &relative,
            )?;
            rows.push(generated.oracle_tsv_row());
            performance_fixture_generator::remove_generated_fixture(&temporary, &generated)?;
        }
        temporary.remove_empty_root()?;
        publish_generated_output(&output, format!("{}\n", rows.join("\n")).as_bytes(), update)
    })();
    result
}

fn generate_snapshot_baseline(output: PathBuf, update: Option<&str>) -> Result<(), String> {
    use std::collections::BTreeMap;

    let temporary = ClosedPrivateDirectory::new("npa-snap-vmsp-snapshot-baseline")?;
    let result = (|| {
        let mut charges = BTreeMap::<&str, (u64, u64, u64, u64)>::new();
        for profile in [
            "representative-1000-certificates",
            "synthetic-1kib",
            "synthetic-1mib",
            "synthetic-near-limit",
        ] {
            eprintln!("computing snapshot baseline charge: {profile}");
            let generated = performance_fixture_generator::materialize_fixture_profile(
                profile,
                &temporary,
                &PathBuf::from(profile),
            )?;
            let manifest_source = String::from_utf8(temporary.read_regular_file(
                &generated.root_relative.join("npa-package.toml"),
                16 * 1024 * 1024,
            )?)
            .map_err(display_error)?;
            let validated = npa_package::parse_and_validate_manifest_str(&manifest_source)
                .map_err(|error| format!("{error:?}"))?;
            let owned = generated.modules.iter().map(|module| {
                npa_package::OwnedPackageLockArtifact::from_vec(
                    npa_package::PackagePath::new(module.certificate_path.clone()),
                    module.certificate_bytes.clone(),
                )
            });
            let (_, prepared) = npa_package::build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
                &validated,
                npa_package::PackagePath::new("npa-package.toml"),
                manifest_source.as_bytes(),
                owned,
                npa_package::PreparedArtifactRetentionPolicy::FastCandidateV1,
                npa_package::PreparedArtifactObservationMode::Aggregate,
                None,
                None,
            )
            .map_err(|error| format!("{error:?}"))?;
            let retention = prepared
                .retention_observation()
                .ok_or_else(|| "aggregate retention observation is absent".to_owned())?;
            let total = retention.admitted_bytes;
            let peak = retention.derivation_candidate_peak_bytes;
            let maximum_certificate_bytes = generated
                .modules
                .iter()
                .map(|module| u64::try_from(module.certificate_bytes.len()).unwrap_or(u64::MAX))
                .max()
                .unwrap_or(0);
            charges.insert(
                profile,
                (
                    generated.module_count,
                    total,
                    peak,
                    maximum_certificate_bytes,
                ),
            );
            performance_fixture_generator::remove_generated_fixture(&temporary, &generated)?;
        }
        let manifest = String::from_utf8(read_invocation_regular_file(
            Path::new("testdata/performance/fixtures/manifest.v0.2.json"),
            MAX_FIXTURE_MANIFEST_BYTES,
            "v0.2 performance fixture manifest",
        )?)
        .map_err(display_error)?;
        let selected = npa_api::validate_performance_fixture_selection_v02(&manifest)
            .map_err(|error| error.to_string())?;
        let rows = selected
            .scenarios
            .iter()
            .filter_map(|selection| match selection {
                npa_api::PerformanceFixtureSelectionV02::PackageArtifactSnapshot(row) => {
                    Some(snapshot_baseline_row(row, &charges))
                }
                _ => None,
            })
            .collect::<Result<Vec<_>, _>>()?;
        if rows.len() != 40 {
            return Err(format!(
                "snapshot baseline row count is {}, expected 40",
                rows.len()
            ));
        }
        let expected_hash = update.ok_or(
            "snapshot baseline generation updates an existing file and requires --update-existing",
        )?;
        let source = read_bounded_regular_output(&output, 16 * 1024 * 1024)?;
        let document = npa_api::JsonDocument::parse(&source)
            .map_err(|error| format!("baseline JSON at byte {}", error.offset))?;
        let root = document
            .root()
            .object_members()
            .ok_or_else(|| "baseline root must be an object".to_owned())?;
        let scenarios = root
            .iter()
            .find(|member| member.key() == "scenarios")
            .and_then(|member| member.value().array_elements())
            .ok_or_else(|| "baseline scenarios must be an array".to_owned())?;
        let mut retained = Vec::new();
        for scenario in scenarios {
            let id = scenario
                .object_members()
                .and_then(|members| members.iter().find(|member| member.key() == "id"))
                .and_then(|member| member.value().string_value())
                .ok_or_else(|| "baseline scenario id is missing".to_owned())?;
            if !id.starts_with("package-artifact-snapshot-") {
                retained.push(scenario.raw_slice().to_owned());
            }
        }
        retained.extend(rows);
        let prefix = "  \"scenarios\": [\n";
        let suffix = "\n  ],\n  \"targeted_build_certs\": [";
        let (before, remainder) = source
            .split_once(prefix)
            .ok_or_else(|| "baseline scenarios prefix is not unique".to_owned())?;
        let (_, after) = remainder
            .split_once(suffix)
            .ok_or_else(|| "baseline scenarios suffix is not unique".to_owned())?;
        let updated = format!(
            "{before}{prefix}    {}{suffix}{after}",
            retained.join(",\n    ")
        );
        let result = publish_generated_output(&output, updated.as_bytes(), Some(expected_hash));
        if result.is_ok() {
            temporary.remove_empty_root()?;
        }
        result
    })();
    result
}

fn snapshot_baseline_row(
    row: &npa_api::PackageArtifactSnapshotFixture,
    charges: &std::collections::BTreeMap<&str, (u64, u64, u64, u64)>,
) -> Result<String, String> {
    use npa_api::{
        PerformanceFixtureArtifactMode, PerformanceFixtureAuditCachePolicy,
        PerformanceFixtureDecodeCachePolicy, PerformanceFixtureDiskMemoPolicy,
        PerformanceFixtureExecutionLane, PerformanceFixtureProcessMemoPolicy,
        PerformanceFixtureVerifier,
    };

    let profile = row.fixture_profile.as_str();
    let (modules, retained_bytes, peak_charge, maximum_certificate_bytes) = charges
        .get(profile)
        .copied()
        .ok_or_else(|| format!("snapshot baseline charge missing for {profile}"))?;
    let prepared = row.artifact_mode == PerformanceFixtureArtifactMode::Snapshot
        && row.verifier == PerformanceFixtureVerifier::Fast
        && row.jobs == 1;
    let live = match row.execution_lane {
        PerformanceFixtureExecutionLane::Api => {
            row.process_memo_policy == PerformanceFixtureProcessMemoPolicy::Disabled
        }
        PerformanceFixtureExecutionLane::CliLocal => {
            row.audit_cache_policy != PerformanceFixtureAuditCachePolicy::LocalHit
                && row.disk_memo_policy != PerformanceFixtureDiskMemoPolicy::Disk
        }
        _ => return Err("future snapshot execution lane cannot be baselined".to_owned()),
    };
    let key_decodes = if row.execution_lane == PerformanceFixtureExecutionLane::CliLocal
        && row.audit_cache_policy != PerformanceFixtureAuditCachePolicy::Off
        && !prepared
    {
        modules
    } else {
        0
    };
    let checker_decodes = if live
        && row.verifier == PerformanceFixtureVerifier::Fast
        && !prepared
        && (row.execution_lane == PerformanceFixtureExecutionLane::CliLocal
            || row.decode_cache_policy == PerformanceFixtureDecodeCachePolicy::Disabled)
    {
        modules
    } else {
        0
    };
    let prepared_reuses = if live && prepared { modules } else { 0 };
    let admissions = if prepared { modules } else { 0 };
    let admitted_bytes = if prepared { retained_bytes } else { 0 };
    let derivation_peak = if prepared { peak_charge } else { 0 };
    let key_peak = if key_decodes > 0 {
        maximum_certificate_bytes
    } else {
        0
    };
    let files_read = if row.execution_lane == PerformanceFixtureExecutionLane::CliLocal {
        modules
    } else {
        0
    };
    let mut counters = [
        ("package.artifact_files_read", files_read),
        ("package.artifact_file_hashes", modules),
        (
            "package.artifact_full_decodes",
            modules
                .saturating_add(key_decodes)
                .saturating_add(checker_decodes),
        ),
        ("package.artifact_prepared_reuses", prepared_reuses),
        ("package.prepared_artifact_admissions", admissions),
        ("package.prepared_artifact_admitted_bytes", admitted_bytes),
        ("package.prepared_artifact_current_entries", 0),
        ("package.prepared_artifact_peak_entries", admissions),
        ("package.prepared_artifact_current_bytes", 0),
        ("package.prepared_artifact_peak_bytes", admitted_bytes),
        ("package.prepared_artifact_derivation_current_bytes", 0),
        (
            "package.prepared_artifact_derivation_peak_bytes",
            derivation_peak,
        ),
        ("package.prepared_artifact_key_current_bytes", 0),
        ("package.prepared_artifact_key_peak_bytes", key_peak),
        ("package.prepared_artifact_entry_limit_fallbacks", 0),
        ("package.prepared_artifact_byte_limit_fallbacks", 0),
        ("package.prepared_artifact_saturated_charge_fallbacks", 0),
        ("package.prepared_artifact_releases", admissions),
        ("package.prepared_artifact_released_bytes", admitted_bytes),
    ];
    counters.sort_by_key(|(name, _)| *name);
    let counters = counters
        .iter()
        .map(|(name, value)| format!("        \"{name}\": {value}"))
        .collect::<Vec<_>>()
        .join(",\n");
    Ok(format!(
        "{{\n      \"id\": \"{}\",\n      \"status\": \"passed\",\n      \"module_count\": {modules},\n      \"deterministic_counters\": {{\n{counters}\n      }},\n      \"coverage\": {{\n        \"live_results_min\": 0,\n        \"proof_evidence_reduction_allowed\": false\n      }}\n    }}",
        row.common.id
    ))
}

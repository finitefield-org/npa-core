use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};

const HISTORICAL_V0_7_CONTRACT: &str = concat!(
    "{\"command_result_schema\":\"npa.package.command_result.v0.3\",",
    "\"policy_preflight_schema\":\"npa.checker_ext.toolchain_v0_7.policy_preflight.v1\",",
    "\"preflight_schema\":\"npa.checker_ext.toolchain_v0_7.prepared_inputs.v1\",",
    "\"toolchain_tag\":\"toolchain-v0.7.0-compat\"}\n",
);
const HISTORICAL_V0_7_GATE: &[u8] =
    include_bytes!("../../../checkers/npa-checker-ext/scripts/toolchain-v0.7.sh");

fn binary() -> Command {
    Command::new(env!("CARGO_BIN_EXE_npa-checker-ext-toolchain-evidence"))
}

fn temp(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!("npa-evidence-{label}-{unique}"));
    fs::create_dir(&path).unwrap();
    path
}

#[test]
fn reports_only_the_current_v0_8_contract() {
    let output = binary().arg("contract").output().unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("toolchain-v0.8.0-compat"));
    assert!(text.contains("npa.package.command_result.v0.4"));
    assert!(text.contains("npa-cli 0.8.0"));
    assert!(text.contains("npa-checker-ext 0.3.0"));
    assert!(text.contains("npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat.tar.gz"));
    assert!(text.contains("npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat.sha256"));
    assert!(text
        .contains("npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat-manifest.json"));
    assert!(!text.contains("toolchain-v0.7.0-compat"));
    assert!(!text.contains("npa.package.command_result.v0.3"));
    assert_ne!(text, HISTORICAL_V0_7_CONTRACT);
}

#[test]
fn capture_rejects_historical_fixture_labels_and_fast_kernel_attribution() {
    let root = temp("capture-current-labels");
    fs::create_dir_all(&root).unwrap();
    let command = root.join("command.json");
    let fixture = root.join("fixture.json");
    let preflight = root.join("preflight.json");
    let evidence = root.join("evidence");
    fs::write(
        &command,
        r#"{"command":"package verify-certs","root":"proofs","schema":"npa.package.command_result.v0.4","status":"passed"}"#,
    )
    .unwrap();
    fs::write(
        &fixture,
        r#"{"schema":"npa.checker_ext.toolchain_v0_7.fixture.v1"}"#,
    )
    .unwrap();
    fs::write(
        &preflight,
        r#"{"schema":"npa.checker_ext.toolchain_v0_8.policy_preflight.v1"}"#,
    )
    .unwrap();

    let historical = binary()
        .args([
            "capture-run",
            "--root",
            root.to_str().unwrap(),
            "--command-result",
            command.to_str().unwrap(),
            "--evidence-dir",
            evidence.to_str().unwrap(),
            "--fixture-record",
            fixture.to_str().unwrap(),
            "--preflight",
            preflight.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!historical.status.success());
    assert!(String::from_utf8_lossy(&historical.stderr).contains("fixture schema mismatch"));

    fs::write(
        &fixture,
        r#"{"schema":"npa.checker_ext.toolchain_v0_8.fixture.v1"}"#,
    )
    .unwrap();
    fs::write(
        &command,
        r#"{"command":"package verify-certs","diagnostics":[{"kernel_fuel":{"subsystem":"conversion"}}],"root":"proofs","schema":"npa.package.command_result.v0.4","status":"passed"}"#,
    )
    .unwrap();
    let attributed = binary()
        .args([
            "capture-run",
            "--root",
            root.to_str().unwrap(),
            "--command-result",
            command.to_str().unwrap(),
            "--evidence-dir",
            evidence.to_str().unwrap(),
            "--fixture-record",
            fixture.to_str().unwrap(),
            "--preflight",
            preflight.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!attributed.status.success());
    assert!(String::from_utf8_lossy(&attributed.stderr)
        .contains("external checker evidence must not contain a fast-kernel fuel report"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn historical_v0_7_gate_and_contract_remain_frozen() {
    assert_eq!(
        format!("{:x}", Sha256::digest(HISTORICAL_V0_7_GATE)),
        "fdb885c33bd31f7c44849fb074a51eb13f5422867274c503bbfa43034280ec8a"
    );
    assert!(HISTORICAL_V0_7_CONTRACT.contains("toolchain-v0.7.0-compat"));
    assert!(HISTORICAL_V0_7_CONTRACT.contains("npa.package.command_result.v0.3"));
    assert!(!HISTORICAL_V0_7_CONTRACT.contains("toolchain-v0.8.0-compat"));
}

#[test]
fn unknown_option_is_rejected_before_environment_preflight() {
    let output = binary().arg("--unknown").output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8(output.stderr).unwrap().contains("usage:"));
}

#[test]
fn duplicate_json_fields_are_rejected() {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!("npa-evidence-duplicate-{unique}.json"));
    fs::write(&path, "{\"x\":1,\"x\":2}\n").unwrap();
    let output = binary()
        .args([
            "json-field",
            "--path",
            path.to_str().unwrap(),
            "--field",
            "x",
        ])
        .output()
        .unwrap();
    let _ = fs::remove_file(path);
    assert!(!output.status.success());
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("duplicate JSON field"));
}

#[test]
fn check_metadata_tracks_current_workspace_version_axes() {
    let root = temp("metadata-axes");
    let metadata = root.join("metadata.json");
    let current = r#"{"packages":[
      {"name":"npa-api","version":"0.4.0"},
      {"name":"npa-cert","version":"0.4.0"},
      {"name":"npa-checker-ref","version":"0.4.0"},
      {"name":"npa-cli","version":"0.8.0"},
      {"name":"npa-frontend","version":"0.4.0"},
      {"name":"npa-kernel","version":"0.3.0"},
      {"name":"npa-package","version":"0.3.0"},
      {"name":"npa-tactic","version":"0.2.0"}
    ]}"#;
    fs::write(&metadata, current).unwrap();

    let accepted = binary()
        .args(["check-metadata", "--metadata", metadata.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr)
    );

    fs::write(
        &metadata,
        current.replace(
            "{\"name\":\"npa-cli\",\"version\":\"0.8.0\"}",
            "{\"name\":\"npa-cli\",\"version\":\"0.7.0\"}",
        ),
    )
    .unwrap();
    let rejected = binary()
        .args(["check-metadata", "--metadata", metadata.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("npa-cli metadata is not 0.8.0"));

    fs::write(
        &metadata,
        current.replace(
            "{\"name\":\"npa-cert\",\"version\":\"0.4.0\"}",
            "{\"name\":\"npa-cert\",\"version\":\"0.3.0\"}",
        ),
    )
    .unwrap();
    let rejected = binary()
        .args(["check-metadata", "--metadata", metadata.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("npa-cert metadata left its 0.4.0 axis")
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn prepare_inputs_emits_v0_8_identity_and_executable_checker() {
    let root = temp("prepare-inputs");
    let checker = root.join("checker-input");
    let version = root.join("version.txt");
    fs::write(&checker, b"checker bytes\n").unwrap();
    fs::write(
        &version,
        concat!(
            "npa-checker-ext 0.3.0\n",
            "checker_build_hash sha256:abababababababababababababababababababababababababababababababab\n",
            "certificate_format NPA-CERT-0.3.0\n",
            "core_spec NPA-Core-0.3.0\n",
            "implementation_profile ocaml-clean-room\n",
            "project_directory checkers/npa-checker-ext/\n",
            "feature_policy_contract m0-05:first-release-empty-core-feature-set\n",
            "vendored_sha256_source_identity vendored-sha256-source:v1\n",
            "checker_identity_manifest_signature_required false\n",
        ),
    )
    .unwrap();
    let output = binary()
        .args([
            "prepare-inputs",
            "--root",
            root.to_str().unwrap(),
            "--checker",
            checker.to_str().unwrap(),
            "--version-file",
            version.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(report.contains("npa.checker_ext.toolchain_v0_8.prepared_inputs.v1"));
    let policy = fs::read_to_string(root.join("ci/runner.release.json")).unwrap();
    assert!(policy.contains("npa-checker-ext-toolchain-v0-8-compat"));
    assert!(policy.contains("npa-checker-ext-toolchain-v0-8-real"));
    assert!(policy.contains("\"checker_version\":\"0.3.0\""));
    assert!(
        policy.contains("\"raw_result_schema\":\"npa.independent-checker.checker_raw_result.v2\"")
    );
    assert!(policy.contains("\"certificate_format\":\"NPA-CERT-0.3.0\""));
    assert!(policy.contains("\"core_spec\":\"NPA-Core-0.3.0\""));
    assert!(policy.contains("npa-fast-kernel-toolchain-v0-8-fixture"));
    assert!(policy.contains("npa-checker-ref-toolchain-v0-8-fixture"));
    assert!(!policy.contains("toolchain-v0-7"));
    let identity = fs::read_to_string(root.join("ci/checker-identity-manifest.json")).unwrap();
    assert!(identity.contains("\"checker_version\":\"0.3.0\""));
    assert!(identity.contains("\"certificate_format\":\"NPA-CERT-0.3.0\""));
    let mode = fs::metadata(root.join("tools/checkers/npa-checker-ext"))
        .unwrap()
        .permissions()
        .mode();
    assert_ne!(mode & 0o111, 0);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn prepare_inputs_rejects_stale_v0_2_checker_metadata() {
    let root = temp("stale-v0-2");
    let checker = root.join("checker-input");
    let version = root.join("version.txt");
    fs::write(&checker, b"checker bytes\n").unwrap();
    fs::write(
        &version,
        concat!(
            "npa-checker-ext 0.2.0\n",
            "checker_build_hash sha256:abababababababababababababababababababababababababababababababab\n",
            "certificate_format NPA-CERT-0.2.0\n",
            "core_spec NPA-Core-0.2.0\n",
            "implementation_profile ocaml-clean-room\n",
            "project_directory checkers/npa-checker-ext/\n",
            "feature_policy_contract m0-05:first-release-empty-core-feature-set\n",
            "vendored_sha256_source_identity vendored-sha256-source:v1\n",
            "checker_identity_manifest_signature_required false\n",
        ),
    )
    .unwrap();
    let output = binary()
        .args([
            "prepare-inputs",
            "--root",
            root.to_str().unwrap(),
            "--checker",
            checker.to_str().unwrap(),
            "--version-file",
            version.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("checker --version line 1 mismatch"));
    fs::remove_dir_all(root).unwrap();
}

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

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
fn reports_only_the_current_v0_7_contract() {
    let output = binary().arg("contract").output().unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("toolchain-v0.7.0-compat"));
    assert!(text.contains("npa.package.command_result.v0.3"));
    assert!(!text.contains("toolchain-v0.4"));
    assert!(!text.contains("toolchain-v0.5"));
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
fn prepare_inputs_emits_v0_7_identity_and_executable_checker() {
    let root = temp("prepare-inputs");
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
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(report.contains("npa.checker_ext.toolchain_v0_7.prepared_inputs.v1"));
    let policy = fs::read_to_string(root.join("ci/runner.release.json")).unwrap();
    assert!(policy.contains("npa-checker-ext-toolchain-v0-7-compat"));
    assert!(policy.contains("npa-checker-ext-toolchain-v0-7-real"));
    assert!(policy.contains("npa-fast-kernel-toolchain-v0-7-fixture"));
    assert!(policy.contains("npa-checker-ref-toolchain-v0-7-fixture"));
    assert!(!policy.contains("toolchain-v0-5"));
    let mode = fs::metadata(root.join("tools/checkers/npa-checker-ext"))
        .unwrap()
        .permissions()
        .mode();
    assert_ne!(mode & 0o111, 0);
    fs::remove_dir_all(root).unwrap();
}

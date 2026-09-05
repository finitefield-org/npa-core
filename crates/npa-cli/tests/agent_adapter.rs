use std::io::Write;
use std::process::{Command, Stdio};

fn hash(byte: u8) -> String {
    format!("sha256:{}", format!("{byte:02x}").repeat(32))
}

fn request(operation: &str) -> String {
    let (endpoint_path, operation_fields) = match operation {
        "snapshot_get" => (
            "/v1/npa/snapshots/get",
            r#",
    "project_id": "project",
    "task_id": "task""#
                .to_owned(),
        ),
        "focused_replay" => (
            "/v1/npa/replay",
            format!(
                r#",
    "candidate_hash": "{}",
    "replay_artifact_hash": "{}",
    "max_steps": 1000"#,
                hash(9),
                hash(10)
            ),
        ),
        "module_build" => (
            "/v1/npa/module/build",
            format!(
                r#",
    "module_name": "Fixture.Module",
    "source_artifact_hash": "{}",
    "options_hash": "{}",
    "base_export_hash": "{}""#,
                hash(9),
                hash(10),
                hash(11)
            ),
        ),
        "certificate_build" => (
            "/v1/npa/certificate/build",
            format!(
                r#",
    "candidate_hash": "{}",
    "module_artifact_hash": "{}",
    "export_hash": "{}""#,
                hash(9),
                hash(10),
                hash(11)
            ),
        ),
        "certificate_verify" => (
            "/v1/npa/certificate/verify",
            format!(
                r#",
    "certificate_hash": "{}",
    "export_hash": "{}",
    "axiom_report_hash": "{}""#,
                hash(10),
                hash(11),
                hash(12)
            ),
        ),
        "source_free_verification" => (
            "/v1/npa/source-free/verify",
            format!(
                r#",
    "statement_hash": "{}",
    "certificate_hash": "{}",
    "export_hash": "{}""#,
                hash(9),
                hash(10),
                hash(11)
            ),
        ),
        "independent_checker" => (
            "/v1/npa/checker/independent",
            format!(
                r#",
    "checker_profile": "npa-reference-checker/v1",
    "certificate_hash": "{}",
    "export_hash": "{}",
    "axiom_report_hash": "{}""#,
                hash(10),
                hash(11),
                hash(12)
            ),
        ),
        _ => panic!("test operation must be known"),
    };
    format!(
        r#"{{
  "schema_id": "npa-client.local-process-request.v1",
  "operation": "{operation}",
  "endpoint_path": "{endpoint_path}",
  "request_hash": "{request_hash}",
  "npa_root": "{npa_root}",
  "workspace_root": "{workspace_root}",
  "expected_npa_build_hash": "{build_hash}",
  "expected_verifier_binary_hash": "{verifier_hash}",
  "payload": {{
    "context": {{
      "request_id": "run:test",
      "workspace_id": "workspace",
      "snapshot_hash": "{snapshot_hash}",
      "environment_hash": "{environment_hash}",
      "policy_hash": "{policy_hash}",
      "supply_chain_pin_set_hash": "{pin_hash}",
      "sandbox_profile_hash": "{sandbox_hash}",
      "timeout_ms": 30000
    }}{operation_fields}
  }}
}}"#,
        request_hash = hash(1),
        npa_root = env!("CARGO_MANIFEST_DIR").replace('\\', "\\\\"),
        workspace_root = std::env::temp_dir().display(),
        build_hash = hash(2),
        verifier_hash = hash(3),
        snapshot_hash = hash(4),
        environment_hash = hash(5),
        policy_hash = hash(6),
        pin_hash = hash(7),
        sandbox_hash = hash(8),
    )
}

#[test]
fn npa_agent_operation_snapshot_get_fails_closed_without_identity_binding() {
    let output = run_bin(
        env!("CARGO_BIN_EXE_npa"),
        "snapshot_get",
        &request("snapshot_get"),
    );

    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8(output.stderr).unwrap().is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""schema_id":"npa-client.local-process-response.v1""#));
    assert!(stdout.contains(r#""operation":"snapshot_get""#));
    assert!(stdout.contains(r#""status":"invalid_request""#));
    assert!(stdout.contains(r#""diagnostic_hash":"sha256:"#));
}

#[test]
fn npa_cert_operation_fails_closed_without_identity_binding() {
    let output = run_bin(
        env!("CARGO_BIN_EXE_npa-cert"),
        "certificate_verify",
        &request("certificate_verify"),
    );

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""status":"invalid_request""#));
    assert!(stdout.contains(r#""diagnostic_hash":"sha256:"#));
}

#[test]
fn npa_cert_source_free_verification_does_not_report_synthetic_success() {
    let output = run_bin(
        env!("CARGO_BIN_EXE_npa-cert"),
        "source_free_verification",
        &request("source_free_verification"),
    );

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""status":"invalid_request""#));
    assert!(stdout.contains(r#""operation":"source_free_verification""#));
    assert!(!stdout.contains(r#""status":"ok""#));
    assert!(!stdout.contains(r#""result":"#));
}

#[test]
fn npa_checker_independent_checker_does_not_report_synthetic_success() {
    let output = run_bin(
        env!("CARGO_BIN_EXE_npa-checker"),
        "independent_checker",
        &request("independent_checker"),
    );

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""status":"invalid_request""#));
    assert!(stdout.contains(r#""operation":"independent_checker""#));
    assert!(!stdout.contains(r#""status":"ok""#));
    assert!(!stdout.contains(r#""result":"#));
}

#[test]
fn adapter_binary_rejects_wrong_operation() {
    let output = run_bin(
        env!("CARGO_BIN_EXE_npa-replay"),
        "module_build",
        &request("module_build"),
    );

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""operation":"module_build""#));
    assert!(stdout.contains(r#""status":"invalid_request""#));
}

#[test]
fn adapter_binary_rejects_malformed_json() {
    let output = run_bin(env!("CARGO_BIN_EXE_npa-build"), "module_build", "not-json");

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""operation":"module_build""#));
    assert!(stdout.contains(r#""status":"invalid_request""#));
}

#[test]
fn adapter_binary_rejects_oversized_stdin_before_parsing() {
    let oversized = vec![b'x'; 1024 * 1024 + 1];
    let output = run_bin_bytes(env!("CARGO_BIN_EXE_npa-build"), "module_build", &oversized);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("local-process request stdin"));
    assert!(stderr.contains("byte limit"));
}

fn run_bin(binary: &str, operation: &str, stdin_body: &str) -> std::process::Output {
    run_bin_bytes(binary, operation, stdin_body.as_bytes())
}

fn run_bin_bytes(binary: &str, operation: &str, stdin_body: &[u8]) -> std::process::Output {
    let mut child = Command::new(binary)
        .args(["--agent-operation", operation, "--input-json-stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("adapter binary must spawn");
    child
        .stdin
        .as_mut()
        .expect("stdin must be piped")
        .write_all(stdin_body)
        .expect("stdin write must succeed");
    child.wait_with_output().expect("adapter must exit")
}

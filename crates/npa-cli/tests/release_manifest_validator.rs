use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use npa_api::JsonDocument;
use npa_cli::release_manifest::validate_release_manifest;

const V0_1_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.1";
const V0_2_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.2";
const VALIDATION_SCHEMA: &str = "npa.generated_artifact_release_manifest.validation.v0.1";
const COMMAND_RESULT_V0_1: &str = "npa.package.command_result.v0.1";
const COMMAND_RESULT_V0_2: &str = "npa.package.command_result.v0.2";
const COMMAND_RESULT_V0_3: &str = "npa.package.command_result.v0.3";

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn core_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core root")
}

fn aggregate_root() -> PathBuf {
    core_root().parent().expect("aggregate root").to_path_buf()
}

fn fixture_dir() -> PathBuf {
    core_root().join("testdata/release-manifest")
}

fn fixture(name: &str) -> String {
    fs::read_to_string(fixture_dir().join(name)).expect("read release-manifest fixture")
}

fn expected_success(input_schema: &str, classification: &str) -> String {
    format!(
        "{{\"schema\":\"{VALIDATION_SCHEMA}\",\"status\":\"valid\",\"input_schema\":\"{input_schema}\",\"evidence_classification\":\"{classification}\"}}\n"
    )
}

fn run_path(path: &Path, require_v0_2: bool) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_npa-release-manifest-validator"));
    if require_v0_2 {
        command.arg("--require-v0.2");
    }
    command
        .arg(path)
        .current_dir(aggregate_root())
        .output()
        .expect("run release-manifest validator")
}

fn run_fixture(name: &str, require_v0_2: bool) -> Output {
    run_path(&fixture_dir().join(name), require_v0_2)
}

fn run_document(source: &str, require_v0_2: bool) -> Output {
    let serial = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "npa-release-manifest-validator-{}-{serial}.json",
        std::process::id()
    ));
    fs::write(&path, source).expect("write temporary manifest");
    let output = run_path(&path, require_v0_2);
    fs::remove_file(&path).expect("remove temporary manifest");
    output
}

fn stdout(output: &Output) -> String {
    String::from_utf8(output.stdout.clone()).expect("UTF-8 stdout")
}

fn stderr(output: &Output) -> String {
    String::from_utf8(output.stderr.clone()).expect("UTF-8 stderr")
}

fn assert_invalid(output: &Output) {
    assert!(
        !output.status.success(),
        "unexpected success: {}",
        stdout(output)
    );
    assert_eq!(stdout(output), "");
    assert!(stderr(output).starts_with("error: "), "{}", stderr(output));
}

fn replace_once(source: &str, from: &str, to: &str) -> String {
    assert_eq!(
        source.matches(from).count(),
        1,
        "replacement must be unique: {from}"
    );
    source.replacen(from, to, 1)
}

fn remove_field(source: &str, object_path: &[&str], field: &str) -> String {
    let document = JsonDocument::parse(source).expect("parse fixture for field removal");
    let mut object = document.root();
    for path_field in object_path {
        object = object
            .object_members()
            .expect("path component is object")
            .iter()
            .find(|member| member.key() == *path_field)
            .expect("path field exists")
            .value();
    }
    let members = object.object_members().expect("target is object");
    let index = members
        .iter()
        .position(|member| member.key() == field)
        .expect("target field exists");
    let (start, end) = if members.len() == 1 {
        (object.span().start + 1, object.span().end - 1)
    } else if index + 1 < members.len() {
        (
            members[index].key_span().start,
            members[index + 1].key_span().start,
        )
    } else {
        (
            members[index - 1].value().span().end,
            members[index].value().span().end,
        )
    };
    let mut changed = source.to_owned();
    changed.replace_range(start..end, "");
    JsonDocument::parse(&changed).expect("field removal preserves JSON syntax");
    changed
}

fn object_fields(source: &str, object_path: &[&str]) -> Vec<String> {
    let document = JsonDocument::parse(source).expect("parse fixture for field inventory");
    let mut object = document.root();
    for path_field in object_path {
        object = object
            .object_members()
            .expect("path component is object")
            .iter()
            .find(|member| member.key() == *path_field)
            .expect("path field exists")
            .value();
    }
    object
        .object_members()
        .expect("target is object")
        .iter()
        .map(|member| member.key().to_owned())
        .collect()
}

#[test]
fn positive_fixtures_have_exact_deterministic_classification() {
    let historical = run_fixture("valid-v0.1.json", false);
    assert!(historical.status.success(), "{}", stderr(&historical));
    assert_eq!(stderr(&historical), "");
    assert_eq!(
        stdout(&historical),
        expected_success(V0_1_SCHEMA, "historical-v0.1")
    );

    for name in [
        "valid-v0.2-in-process.json",
        "valid-v0.2-fast.json",
        "valid-v0.2-external.json",
    ] {
        let output = run_fixture(name, true);
        assert!(output.status.success(), "{name}: {}", stderr(&output));
        assert_eq!(stderr(&output), "");
        assert_eq!(
            stdout(&output),
            expected_success(V0_2_SCHEMA, "checked-v0.2")
        );
    }

    let default_v0_2 = run_fixture("valid-v0.2-in-process.json", false);
    assert!(default_v0_2.status.success(), "{}", stderr(&default_v0_2));
}

#[test]
fn require_v0_2_rejects_historical_without_schema_invalid_claim() {
    let output = run_fixture("valid-v0.1.json", true);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(stdout(&output), "");
    assert_eq!(
        stderr(&output),
        "error: historical v0.1 evidence does not satisfy --require-v0.2\n"
    );
    assert!(!stderr(&output).contains("schema-invalid"));
}

#[test]
fn cli_argument_errors_and_option_separator_are_deterministic() {
    let missing = Command::new(env!("CARGO_BIN_EXE_npa-release-manifest-validator"))
        .current_dir(aggregate_root())
        .output()
        .expect("run validator without arguments");
    assert_eq!(missing.status.code(), Some(2));
    assert_eq!(stdout(&missing), "");
    assert!(stderr(&missing).starts_with("error: missing release manifest path\n"));

    let unknown = Command::new(env!("CARGO_BIN_EXE_npa-release-manifest-validator"))
        .arg("--unknown")
        .current_dir(aggregate_root())
        .output()
        .expect("run validator with unknown option");
    assert_eq!(unknown.status.code(), Some(2));
    assert_eq!(stdout(&unknown), "");
    assert!(stderr(&unknown).starts_with("error: unsupported option '--unknown'\n"));

    let separated = Command::new(env!("CARGO_BIN_EXE_npa-release-manifest-validator"))
        .args([
            "--require-v0.2",
            "--",
            fixture_dir()
                .join("valid-v0.2-fast.json")
                .to_str()
                .expect("UTF-8 fixture path"),
        ])
        .current_dir(aggregate_root())
        .output()
        .expect("run validator with option separator");
    assert!(separated.status.success(), "{}", stderr(&separated));
}

#[test]
fn every_named_negative_fixture_fails_at_its_intended_guard() {
    let expected = BTreeMap::from([
        (
            "invalid-absolute-locator.json",
            "must be a relative slash-separated path",
        ),
        (
            "invalid-checker-disagreement.json",
            "verdict_source disagrees with checker_mode",
        ),
        (
            "invalid-command-non-explicit-lock.json",
            "must select 'package_lock' exactly once",
        ),
        (
            "invalid-command-reconstructed-lock.json",
            "must explicitly select --package-lock checked",
        ),
        (
            "invalid-command-unlocked.json",
            "must select 'locked' exactly once",
        ),
        (
            "invalid-duplicate-checked-provenance.json",
            "one package_lock_checked diagnostic",
        ),
        (
            "invalid-external-aggregate-shape.json",
            "invalid aggregate evidence",
        ),
        (
            "invalid-external-command-acceleration.json",
            "must select --audit-cache off",
        ),
        (
            "invalid-external-missing-identity.json",
            "missing field 'checker_build_hash'",
        ),
        (
            "invalid-external-null-identity.json",
            "external_checker must be an object",
        ),
        (
            "invalid-external-policy-disagreement.json",
            "runner policy hash disagrees",
        ),
        (
            "invalid-external-result-acceleration.json",
            "non-live verification diagnostic",
        ),
        (
            "invalid-external-unknown-field.json",
            "unknown field 'unexpected'",
        ),
        (
            "invalid-failed-command-result.json",
            "command_result.status must be 'passed'",
        ),
        (
            "invalid-in-process-external-identity.json",
            "must be null for in-process modes",
        ),
        (
            "invalid-incompatible-cli-version.json",
            "command_result.schema does not match verification.npa_cli_crate_version",
        ),
        (
            "invalid-locally-accelerated.json",
            "invalid aggregate evidence",
        ),
        (
            "invalid-lock-hash-disagreement.json",
            "hash disagrees with generated_files",
        ),
        (
            "invalid-missing-checked-provenance.json",
            "one package_lock_checked diagnostic",
        ),
        (
            "invalid-missing-identity.json",
            "missing field 'host_executable_sha256'",
        ),
        (
            "invalid-non-explicit-cache.json",
            "must select 'verifier_memo' exactly once",
        ),
        (
            "invalid-noncanonical-locator.json",
            "must not contain empty, '.' or '..' segments",
        ),
        (
            "invalid-provenance-disagreement.json",
            "hash disagrees with package_lock_sha256",
        ),
        (
            "invalid-retained-hash-format.json",
            "must contain a lowercase SHA-256 digest",
        ),
        (
            "invalid-retired-helper-host.json",
            "host_executable_name is unsupported",
        ),
        (
            "invalid-unknown-top-field.json",
            "manifest has unknown field 'unexpected'",
        ),
        (
            "invalid-unknown-verification-field.json",
            "verification has unknown field 'unexpected'",
        ),
        (
            "invalid-verdict-disagreement.json",
            "verdict_source disagrees with checker_mode",
        ),
        (
            "invalid-verification-hash-format.json",
            "must be sha256:<64-lowercase-hex>",
        ),
        (
            "invalid-wrong-command-result.json",
            "command_result.command must be 'package verify-certs'",
        ),
    ]);
    let fixture_names = fs::read_dir(fixture_dir())
        .expect("read fixture directory")
        .map(|entry| entry.expect("fixture entry").file_name())
        .map(|name| name.to_string_lossy().into_owned())
        .filter(|name| name.starts_with("invalid-") && name.ends_with(".json"))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        fixture_names,
        expected.keys().map(|name| (*name).to_owned()).collect()
    );
    for (name, expected_error) in expected {
        let output = run_fixture(name, true);
        assert_invalid(&output);
        assert!(
            stderr(&output).contains(expected_error),
            "{name}: {}",
            stderr(&output)
        );
    }
}

#[test]
fn every_required_manifest_and_identity_field_is_enforced() {
    let historical = fixture("valid-v0.1.json");
    for field in object_fields(&historical, &[]) {
        assert_invalid(&run_document(&remove_field(&historical, &[], &field), true));
    }

    let in_process = fixture("valid-v0.2-in-process.json");
    assert_invalid(&run_document(
        &remove_field(&in_process, &[], "verification"),
        true,
    ));
    for field in object_fields(&in_process, &["verification"]) {
        assert_invalid(&run_document(
            &remove_field(&in_process, &["verification"], &field),
            true,
        ));
    }

    let external = fixture("valid-v0.2-external.json");
    for field in object_fields(&external, &["verification", "external_checker"]) {
        assert_invalid(&run_document(
            &remove_field(&external, &["verification", "external_checker"], &field),
            true,
        ));
    }
}

#[test]
fn every_verification_hash_requires_lowercase_prefixed_sha256() {
    let uppercase = "A".repeat(64);
    let in_process = fixture("valid-v0.2-in-process.json");
    for (field, digest) in [
        (
            "package_lock_sha256",
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ),
        (
            "cargo_lock_sha256",
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        ),
        (
            "host_executable_sha256",
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
        ),
    ] {
        let changed = replace_once(
            &in_process,
            &format!("\"{field}\": \"sha256:{digest}\""),
            &format!("\"{field}\": \"sha256:{uppercase}\""),
        );
        assert_invalid(&run_document(&changed, true));
    }

    let external = fixture("valid-v0.2-external.json");
    for (field, digest) in [
        (
            "runner_policy_sha256",
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
        ),
        (
            "checker_registry_sha256",
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ),
        (
            "checker_binary_sha256",
            "1111111111111111111111111111111111111111111111111111111111111111",
        ),
        (
            "checker_build_hash",
            "2222222222222222222222222222222222222222222222222222222222222222",
        ),
    ] {
        let changed = replace_once(
            &external,
            &format!("\"{field}\": \"sha256:{digest}\""),
            &format!("\"{field}\": \"sha256:{uppercase}\""),
        );
        assert_invalid(&run_document(&changed, true));
    }
}

#[test]
fn reference_commands_reject_parallel_jobs() {
    let reference = fixture("valid-v0.2-in-process.json");
    assert!(run_document(&reference, true).status.success());
    let parallel = replace_once(&reference, "--jobs 1", "--jobs 4");
    let output = run_document(&parallel, true);
    assert_invalid(&output);
    assert_eq!(
        stderr(&output),
        "error: reference verification command must use one job\n"
    );

    let fast = fixture("valid-v0.2-fast.json");
    let parallel_fast = replace_once(
        &fast,
        "--verifier-memo off --json\"",
        "--verifier-memo off --jobs 4 --json\"",
    );
    let output = run_document(&parallel_fast, true);
    assert!(output.status.success(), "{}", stderr(&output));
}

#[test]
fn package_lock_path_is_bound_to_package_root() {
    let source = fixture("valid-v0.2-fast.json");
    let changed_root = replace_once(
        &source,
        "\"package_root\": \"proofs\"",
        "\"package_root\": \"other-proofs\"",
    );
    let output = run_document(&changed_root, true);
    assert_invalid(&output);
    assert!(stderr(&output).contains("must be derived from package_root"));

    let rebound = changed_root.replace(
        "proofs/generated/package-lock.json",
        "other-proofs/generated/package-lock.json",
    );
    let output = run_document(&rebound, true);
    assert!(output.status.success(), "{}", stderr(&output));
}

#[test]
fn v0_2_pairs_historical_and_current_cli_command_result_series() {
    let source = fixture("valid-v0.2-in-process.json");
    for version in ["0.3.0", "0.3.99", "0.4.0", "0.4.12"] {
        let changed = source
            .replace(
                "\"npa_cli_crate_version\": \"0.3.0\"",
                &format!("\"npa_cli_crate_version\": \"{version}\""),
            )
            .replace(COMMAND_RESULT_V0_2, COMMAND_RESULT_V0_1);
        let output = run_document(&changed, true);
        assert!(output.status.success(), "{version}: {}", stderr(&output));
    }
    for version in ["0.5.0", "0.5.12"] {
        let changed = source
            .replace(
                "\"npa_cli_crate_version\": \"0.3.0\"",
                &format!("\"npa_cli_crate_version\": \"{version}\""),
            )
            .replace(COMMAND_RESULT_V0_1, COMMAND_RESULT_V0_2);
        let output = run_document(&changed, true);
        assert!(output.status.success(), "{version}: {}", stderr(&output));
    }
    for version in ["0.6.0", "0.6.12", "0.7.0", "0.7.12"] {
        let changed = source
            .replace(
                "\"npa_cli_crate_version\": \"0.3.0\"",
                &format!("\"npa_cli_crate_version\": \"{version}\""),
            )
            .replace(COMMAND_RESULT_V0_1, COMMAND_RESULT_V0_3);
        let output = run_document(&changed, true);
        assert!(output.status.success(), "{version}: {}", stderr(&output));
    }
    for (version, schema) in [
        ("0.3.0", COMMAND_RESULT_V0_2),
        ("0.4.12", COMMAND_RESULT_V0_2),
        ("0.5.0", COMMAND_RESULT_V0_1),
        ("0.5.0", COMMAND_RESULT_V0_3),
        ("0.6.0", COMMAND_RESULT_V0_2),
        ("0.7.0", COMMAND_RESULT_V0_2),
    ] {
        let changed = source
            .replace(
                "\"npa_cli_crate_version\": \"0.3.0\"",
                &format!("\"npa_cli_crate_version\": \"{version}\""),
            )
            .replace(COMMAND_RESULT_V0_1, schema);
        let output = run_document(&changed, true);
        assert_invalid(&output);
        assert_eq!(
            stderr(&output),
            "error: verification.command_result.schema does not match verification.npa_cli_crate_version\n"
        );
    }
}

#[test]
fn v0_3_source_and_conversion_shapes_are_closed_and_bounded() {
    let source = fixture("valid-v0.2-in-process.json")
        .replace(
            "\"npa_cli_crate_version\": \"0.3.0\"",
            "\"npa_cli_crate_version\": \"0.6.0\"",
        )
        .replace(COMMAND_RESULT_V0_1, COMMAND_RESULT_V0_3);
    let insert_context = |document: &str, source_object: &str, conversion_object: &str| {
        replace_once(
            document,
            "\"reason_code\": \"package_verified\",\n          \"severity\": \"info\",\n          \"field\":",
            &format!(
                "\"reason_code\": \"package_verified\",\n          \"severity\": \"info\",\n          \"source\": {source_object},\n          \"conversion\": {conversion_object},\n          \"field\":"
            ),
        )
    };
    let valid_source = r#"{"path":"Proofs/A/source.npa","start_byte":4,"end_byte":8,"declaration":"A.term","line":2,"column":3,"token":"term"}"#;
    let valid_conversion = r#"{"phase":"definitional_equality","outcome":"not_defeq","lhs_head":"application","rhs_head":"constant:A.expected","depth":7}"#;
    let output = run_document(
        &insert_context(&source, valid_source, valid_conversion),
        true,
    );
    assert_invalid(&output);
    assert!(stderr(&output).contains("diagnostic has an unexpected shape"));

    for (source_object, conversion_object, expected) in [
        (
            r#"{"path":"Proofs/A/source.npa","start_byte":4,"end_byte":8,"line":2}"#,
            valid_conversion,
            "line and column must appear together",
        ),
        (
            valid_source,
            r#"{"phase":"unknown","outcome":"not_defeq","lhs_head":"application","rhs_head":"sort","depth":7}"#,
            ".conversion.phase is unsupported",
        ),
        (
            valid_source,
            r#"{"phase":"term_check","outcome":"not_defeq","lhs_head":"constant:","rhs_head":"sort","depth":7}"#,
            "bounded expression head",
        ),
    ] {
        let output = run_document(
            &insert_context(&source, source_object, conversion_object),
            true,
        );
        assert_invalid(&output);
        assert!(stderr(&output).contains(expected), "{}", stderr(&output));
    }
}

#[test]
fn v0_2_source_shape_is_validated_but_rejected_from_passed_evidence() {
    let source = fixture("valid-v0.2-in-process.json");
    let current = source
        .replace(
            "\"npa_cli_crate_version\": \"0.3.0\"",
            "\"npa_cli_crate_version\": \"0.5.0\"",
        )
        .replace(COMMAND_RESULT_V0_1, COMMAND_RESULT_V0_2);
    let insert_source = |document: &str, source_object: &str| {
        replace_once(
            document,
            "\"reason_code\": \"package_verified\",\n          \"severity\": \"info\",\n          \"field\":",
            &format!(
                "\"reason_code\": \"package_verified\",\n          \"severity\": \"info\",\n          \"source\": {source_object},\n          \"field\":"
            ),
        )
    };
    let valid_source = r#"{"path":"Proofs/Ai/Basic/source.npa","start_byte":41,"end_byte":48,"declaration":"product_enumeration_bad"}"#;
    let output = run_document(&insert_source(&current, valid_source), true);
    assert_invalid(&output);
    assert!(stderr(&output).contains("diagnostic has an unexpected shape"));

    for (source_object, expected) in [
        (
            r#"{"path":"/absolute/source.npa","start_byte":1,"end_byte":2}"#,
            "relative",
        ),
        (
            r#"{"path":"source.npa","start_byte":-1,"end_byte":2}"#,
            "nonnegative",
        ),
        (
            r#"{"path":"source.npa","start_byte":3,"end_byte":2}"#,
            "reversed",
        ),
        (
            r#"{"path":"source.npa","start_byte":1,"end_byte":2,"declaration":""}"#,
            "nonempty string",
        ),
    ] {
        let output = run_document(&insert_source(&current, source_object), true);
        assert_invalid(&output);
        assert!(stderr(&output).contains(expected), "{}", stderr(&output));
    }

    let historical_source = insert_source(
        &source,
        r#"{"path":"source.npa","start_byte":1,"end_byte":2}"#,
    );
    let output = run_document(&historical_source, true);
    assert_invalid(&output);
    assert!(stderr(&output).contains("unknown field 'source'"));
}

#[test]
fn v0_2_rejects_unsupported_cli_versions() {
    let source = fixture("valid-v0.2-in-process.json");
    for version in [
        "0.2.9",
        "0.3.01",
        "0.4.00",
        "0.4.01",
        "0.5.00",
        "0.5.01",
        "0.6.00",
        "0.6.01",
        "0.7.00",
        "0.7.01",
        "0.4",
        "0.4.0-dev",
        "latest",
    ] {
        let changed = replace_once(
            &source,
            "\"npa_cli_crate_version\": \"0.3.0\"",
            &format!("\"npa_cli_crate_version\": \"{version}\""),
        );
        assert_invalid(&run_document(&changed, true));
    }
}

#[test]
fn relative_direct_manifest_path_and_timing_identity_are_supported() {
    let source = fixture("valid-v0.2-fast.json");
    let with_timings = replace_once(
        &source,
        "\"status\": \"passed\",\n      \"diagnostics\": [",
        "\"status\": \"passed\",\n      \"timings\": {\"schema\":\"npa.package.timings.v0.1\",\"mode\":\"summary\",\"unit\":\"ms\",\"proof_evidence\":false,\"build_evidence\":false,\"load_root_ms\":1},\n      \"diagnostics\": [",
    );
    let with_telemetry = replace_once(
        &with_timings,
        "          \"checker\": \"fast-kernel-certificate-verifier\"\n        }\n      ],\n      \"artifacts\": []",
        "          \"checker\": \"fast-kernel-certificate-verifier\"\n        },\n        {\"kind\":\"GeneratedArtifact\",\"reason_code\":\"process_memo_summary\",\"severity\":\"info\",\"field\":\"process_memo\",\"actual_value\":\"mode=process-local;hits=0;misses=1;inserted=1;trusted=false\"},\n        {\"kind\":\"GeneratedArtifact\",\"reason_code\":\"decode_cache_summary\",\"severity\":\"info\",\"field\":\"decode_cache\",\"actual_value\":\"mode=process-local;certificate_hits=0;certificate_misses=1;certificate_inserted=1;import_context_hits=0;import_context_misses=0;import_context_inserted=0;import_context_disk_hits=0;import_context_disk_misses=0;import_context_disk_stale=0;import_context_disk_schema_misses=0;import_context_disk_inserted=0;trusted=false;proof_evidence=false\"}\n      ],\n      \"artifacts\": []",
    );
    let relative = with_telemetry
        .replace(
            "--manifest-path npa-core/Cargo.toml",
            "--manifest-path ../npa-core/Cargo.toml",
        )
        .replace(
            "--root npa-project-iut/proofs --package-lock",
            "--root proofs --timings summary --package-lock",
        )
        .replace(
            "\"root\": \"npa-project-iut/proofs\"",
            "\"root\": \"proofs\"",
        );
    let output = run_document(&relative, true);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stderr(&output), "");
    assert_eq!(
        stdout(&output),
        expected_success(V0_2_SCHEMA, "checked-v0.2")
    );

    let invalid = replace_once(
        &relative,
        "trusted=false;proof_evidence=false",
        "trusted=false;proof_evidence=true",
    );
    assert_invalid(&run_document(&invalid, true));
}

#[test]
fn validation_is_read_only_and_preserves_result_bytes() {
    let fixture_paths = fs::read_dir(fixture_dir())
        .expect("read fixture directory")
        .map(|entry| entry.expect("fixture entry").path())
        .filter(|path| path.is_file())
        .collect::<Vec<_>>();
    let before = fixture_paths
        .iter()
        .map(|path| (path.clone(), fs::read(path).expect("read fixture bytes")))
        .collect::<BTreeMap<_, _>>();
    let status_before = Command::new("/usr/bin/git")
        .args([
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--",
            ".",
        ])
        .current_dir(core_root())
        .output()
        .expect("git status before")
        .stdout;

    let output = run_fixture("valid-v0.2-in-process.json", true);
    assert!(output.status.success(), "{}", stderr(&output));

    let after = fixture_paths
        .iter()
        .map(|path| (path.clone(), fs::read(path).expect("read fixture bytes")))
        .collect::<BTreeMap<_, _>>();
    let status_after = Command::new("/usr/bin/git")
        .args([
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--",
            ".",
        ])
        .current_dir(core_root())
        .output()
        .expect("git status after")
        .stdout;
    assert_eq!(after, before);
    assert_eq!(status_after, status_before);
}

#[test]
fn duplicate_fields_and_shell_tokenization_are_rejected_or_supported() {
    let duplicate = fixture("valid-v0.1.json").replacen(
        "{",
        "{\n  \"schema\": \"npa.generated_artifact_release_manifest.v0.1\",",
        1,
    );
    let error = validate_release_manifest(&duplicate, false).expect_err("duplicate field");
    assert!(error.to_string().contains("duplicate JSON field 'schema'"));

    let source = fixture("valid-v0.2-fast.json");
    let quoted = replace_once(
        &source,
        "--manifest-path npa-core/Cargo.toml",
        "--manifest-path 'npa-core/Cargo.toml'",
    );
    validate_release_manifest(&quoted, true).expect("quoted command path remains valid");
}

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

const MODULE: &str = "Proofs.Ai.Basic";
const META_PATH: &str = "Proofs/Ai/Basic/meta.json";
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const ONE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-cli is under npa-core/crates")
        .join("testdata/package/proofs")
}

fn temp_fixture() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "npa-package-artifact-ledger-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    copy_tree(&fixture_root(), &path);
    path
}

fn copy_tree(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn snapshot(root: &Path) -> BTreeMap<String, Vec<u8>> {
    fn visit(root: &Path, current: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
        for entry in fs::read_dir(current).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if entry.file_type().unwrap().is_dir() {
                visit(root, &path, out);
            } else {
                out.insert(
                    path.strip_prefix(root)
                        .unwrap()
                        .to_string_lossy()
                        .replace('\\', "/"),
                    fs::read(path).unwrap(),
                );
            }
        }
    }
    let mut out = BTreeMap::new();
    visit(root, root, &mut out);
    out
}

fn run(root: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_npa"))
        .args([
            "package",
            "audit-artifact-ledger",
            "--root",
            root.to_str().unwrap(),
            "--module",
            MODULE,
            "--json",
        ])
        .output()
        .unwrap()
}

fn stdout(output: &Output) -> String {
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout.clone()).unwrap()
}

fn replace_json_hash(root: &Path, field: &str, replacement: &str) {
    let path = root.join(META_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let prefix = format!("\"{field}\": \"");
    let start = source.find(&prefix).unwrap() + prefix.len();
    let end = source[start..].find('"').unwrap() + start;
    let mut changed = source;
    changed.replace_range(start..end, replacement);
    fs::write(path, changed).unwrap();
}

fn replace_manifest_hash(root: &Path, field: &str, replacement: &str) {
    let path = root.join("npa-package.toml");
    let source = fs::read_to_string(&path).unwrap();
    let module_start = source.find(&format!("module = \"{MODULE}\"")).unwrap();
    let field_start = source[module_start..]
        .find(&format!("{field} = \""))
        .unwrap()
        + module_start
        + field.len()
        + 4;
    let field_end = source[field_start..].find('"').unwrap() + field_start;
    let mut changed = source;
    changed.replace_range(field_start..field_end, replacement);
    fs::write(path, changed).unwrap();
}

fn replace_metadata_value(root: &Path, from: &str, to: &str) {
    let path = root.join(META_PATH);
    let source = fs::read_to_string(&path).unwrap();
    assert!(
        source.contains(from),
        "missing metadata fixture value: {from}"
    );
    fs::write(path, source.replacen(from, to, 1)).unwrap();
}

fn replace_manifest_value(root: &Path, from: &str, to: &str) {
    let path = root.join("npa-package.toml");
    let source = fs::read_to_string(&path).unwrap();
    let module_start = source.find(&format!("module = \"{MODULE}\"")).unwrap();
    let relative = source[module_start..]
        .find(from)
        .unwrap_or_else(|| panic!("missing manifest fixture value: {from}"));
    let start = module_start + relative;
    let mut changed = source;
    changed.replace_range(start..start + from.len(), to);
    fs::write(path, changed).unwrap();
}

#[test]
fn package_artifact_ledger_matching_audit_is_deterministic_and_read_only() {
    let root = temp_fixture();
    let before = snapshot(&root);
    let first = run(&root);
    let second = run(&root);
    assert_eq!(first.status.code(), Some(0));
    assert_eq!(second.status.code(), Some(0));
    assert_eq!(first.stdout, second.stdout);
    assert_eq!(snapshot(&root), before);

    let json = stdout(&first);
    assert!(json.contains("\"schema\":\"npa.package.command_result.v0.3\""));
    assert!(json.contains("\"status\":\"passed\""));
    assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 10);
    assert!(
        json.contains("hash_drift_class=consistent,identity_parity=matches,checker_status=checked")
    );
    assert!(json.ends_with("\"artifacts\":[]}\n"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn package_artifact_ledger_classifies_each_ledger_drift_location() {
    let metadata_only = temp_fixture();
    replace_json_hash(&metadata_only, "source_sha256", ZERO_HASH);
    let output = run(&metadata_only);
    assert_eq!(output.status.code(), Some(1));
    assert!(stdout(&output).contains("hash_drift_class=metadata_only_drift"));
    fs::remove_dir_all(metadata_only).unwrap();

    let manifest_only = temp_fixture();
    replace_manifest_hash(&manifest_only, "expected_source_hash", ZERO_HASH);
    let output = run(&manifest_only);
    assert_eq!(output.status.code(), Some(1));
    assert!(stdout(&output).contains("hash_drift_class=manifest_only_drift"));
    fs::remove_dir_all(manifest_only).unwrap();

    let same_stale = temp_fixture();
    replace_json_hash(&same_stale, "source_sha256", ZERO_HASH);
    replace_manifest_hash(&same_stale, "expected_source_hash", ZERO_HASH);
    let output = run(&same_stale);
    assert_eq!(output.status.code(), Some(1));
    assert!(stdout(&output).contains("hash_drift_class=both_ledgers_same_stale_identity"));
    fs::remove_dir_all(same_stale).unwrap();

    let diverge = temp_fixture();
    replace_json_hash(&diverge, "source_sha256", ONE_HASH);
    replace_manifest_hash(&diverge, "expected_source_hash", ZERO_HASH);
    let output = run(&diverge);
    assert_eq!(output.status.code(), Some(1));
    assert!(stdout(&output).contains("hash_drift_class=both_ledgers_diverge"));
    fs::remove_dir_all(diverge).unwrap();
}

#[test]
fn package_artifact_ledger_invalid_metadata_keeps_ten_slot_accounting() {
    let root = temp_fixture();
    fs::write(root.join(META_PATH), b"{").unwrap();
    let before = snapshot(&root);
    let output = run(&root);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(snapshot(&root), before);
    let json = stdout(&output);
    assert_eq!(
        json.matches("\"artifact_ledger_comparison_unavailable\"")
            .count(),
        5
    );
    assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 5);
    assert!(json.contains(
        "hash_drift_class=unavailable,identity_parity=incomplete,checker_status=checked"
    ));
    assert!(!json.contains("const_left"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn package_artifact_ledger_reports_each_hash_field_independently() {
    let fields = [
        ("source_sha256", "expected_source_hash", "source_hash"),
        (
            "certificate_file_sha256",
            "expected_certificate_file_hash",
            "certificate_file_hash",
        ),
        ("export_hash", "expected_export_hash", "export_hash"),
        (
            "axiom_report_hash",
            "expected_axiom_report_hash",
            "axiom_report_hash",
        ),
        (
            "certificate_hash",
            "expected_certificate_hash",
            "certificate_hash",
        ),
    ];

    for (metadata_field, manifest_field, reason_stem) in fields {
        let metadata_root = temp_fixture();
        replace_json_hash(&metadata_root, metadata_field, ZERO_HASH);
        let json = stdout(&run(&metadata_root));
        assert!(json.contains(&format!("artifact_ledger_metadata_{reason_stem}_mismatch")));
        assert!(json.contains("hash_drift_class=metadata_only_drift"));
        assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 9);
        fs::remove_dir_all(metadata_root).unwrap();

        let manifest_root = temp_fixture();
        replace_manifest_hash(&manifest_root, manifest_field, ZERO_HASH);
        let json = stdout(&run(&manifest_root));
        assert!(json.contains(&format!("artifact_ledger_manifest_{reason_stem}_mismatch")));
        assert!(json.contains("hash_drift_class=manifest_only_drift"));
        assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 9);
        fs::remove_dir_all(manifest_root).unwrap();
    }
}

#[test]
fn package_artifact_ledger_non_hash_drift_is_independent_of_hash_class() {
    let cases = [
        (
            r#""module": "Proofs.Ai.Basic""#,
            r#""module": "Proofs.Ai.Other""#,
        ),
        (
            r#""source": "Proofs/Ai/Basic/source.npa""#,
            r#""source": "Proofs/Ai/Other/source.npa""#,
        ),
        (
            r#""certificate": "Proofs/Ai/Basic/certificate.npcert""#,
            r#""certificate": "Proofs/Ai/Other/certificate.npcert""#,
        ),
        (r#""imports": []"#, r#""imports": ["Std.Logic.Eq"]"#),
        (r#""axioms": []"#, r#""axioms": ["Eq.rec"]"#),
        (
            r#""producer_profile": "human-surface-explicit-term""#,
            r#""producer_profile": "other-profile""#,
        ),
    ];
    for (from, to) in cases {
        let root = temp_fixture();
        replace_metadata_value(&root, from, to);
        let output = run(&root);
        assert_eq!(output.status.code(), Some(1));
        let json = stdout(&output);
        assert!(json
            .contains("hash_drift_class=consistent,identity_parity=drift,checker_status=checked"));
        assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 10);
        fs::remove_dir_all(root).unwrap();
    }

    let unavailable_profile = temp_fixture();
    replace_metadata_value(
        &unavailable_profile,
        r#""producer_profile": "human-surface-explicit-term""#,
        r#""producer_profile": "unavailable""#,
    );
    replace_manifest_value(
        &unavailable_profile,
        r#"producer_profile = "human-surface-explicit-term""#,
        r#"producer_profile = "unavailable""#,
    );
    let output = run(&unavailable_profile);
    assert_eq!(output.status.code(), Some(0));
    assert!(stdout(&output).contains("identity_parity=matches"));
    fs::remove_dir_all(unavailable_profile).unwrap();
}

#[test]
fn package_artifact_ledger_read_failures_preserve_slot_accounting() {
    let missing_metadata = temp_fixture();
    fs::remove_file(missing_metadata.join(META_PATH)).unwrap();
    let output = run(&missing_metadata);
    assert_eq!(output.status.code(), Some(1));
    let json = stdout(&output);
    assert!(json.contains("artifact_ledger_meta_missing"));
    assert_eq!(
        json.matches("\"artifact_ledger_comparison_unavailable\"")
            .count(),
        5
    );
    assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 5);
    fs::remove_dir_all(missing_metadata).unwrap();

    let missing_source = temp_fixture();
    fs::remove_file(missing_source.join("Proofs/Ai/Basic/source.npa")).unwrap();
    let output = run(&missing_source);
    assert_eq!(output.status.code(), Some(1));
    let json = stdout(&output);
    assert!(json.contains("\"reason_code\":\"source_missing\""));
    assert_eq!(
        json.matches("\"artifact_ledger_comparison_unavailable\"")
            .count(),
        2
    );
    assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 8);
    assert!(json.contains("hash_drift_class=unavailable"));
    assert!(json.contains("checker_status=checked"));
    fs::remove_dir_all(missing_source).unwrap();

    let missing_certificate = temp_fixture();
    fs::remove_file(missing_certificate.join("Proofs/Ai/Basic/certificate.npcert")).unwrap();
    let output = run(&missing_certificate);
    assert_eq!(output.status.code(), Some(1));
    let json = stdout(&output);
    assert!(json.contains("\"reason_code\":\"certificate_missing\""));
    assert_eq!(
        json.matches("\"artifact_ledger_comparison_unavailable\"")
            .count(),
        8
    );
    assert_eq!(json.matches("\"artifact_ledger_hash_match\"").count(), 2);
    assert!(json.contains("checker_status=not_run"));
    fs::remove_dir_all(missing_certificate).unwrap();

    let invalid_metadata_path = temp_fixture();
    let private_path = "/Users/private/package/source.npa";
    replace_metadata_value(
        &invalid_metadata_path,
        r#""source": "Proofs/Ai/Basic/source.npa""#,
        &format!(r#""source": "{private_path}""#),
    );
    let output = run(&invalid_metadata_path);
    assert_eq!(output.status.code(), Some(1));
    let json = stdout(&output);
    assert!(json.contains("artifact_ledger_meta_invalid_path"));
    assert!(json.contains("\"actual_value\":\"invalid path\""));
    assert!(!json.contains(private_path));
    fs::remove_dir_all(invalid_metadata_path).unwrap();

    for (field, reason, sanitized_value) in [
        (
            "schema",
            "artifact_ledger_meta_unsupported_schema",
            "unsupported schema",
        ),
        (
            "module",
            "artifact_ledger_meta_invalid_name",
            "invalid name",
        ),
        (
            "source_sha256",
            "artifact_ledger_meta_invalid_hash",
            "invalid hash",
        ),
    ] {
        let root = temp_fixture();
        let private_value = format!("/Users/private/package/{field}");
        replace_json_hash(&root, field, &private_value);
        let output = run(&root);
        assert_eq!(output.status.code(), Some(1));
        let json = stdout(&output);
        assert!(json.contains(reason));
        assert!(json.contains(&format!(r#""actual_value":"{sanitized_value}""#)));
        assert!(!json.contains(&private_value));
        fs::remove_dir_all(root).unwrap();
    }

    let duplicate_private_key = temp_fixture();
    let private_key = "/Users/private/package/duplicate-key";
    replace_metadata_value(
        &duplicate_private_key,
        r#""trusted_status": "verified_by_certificate","#,
        &format!(
            r#""trusted_status": "verified_by_certificate", "description": {{"{private_key}": 1, "{private_key}": 2}},"#,
        ),
    );
    let output = run(&duplicate_private_key);
    assert_eq!(output.status.code(), Some(1));
    let json = stdout(&output);
    assert!(json.contains("artifact_ledger_meta_invalid_json"));
    assert!(json.contains(r#""field":"duplicate_key""#));
    assert!(!json.contains(private_key));
    fs::remove_dir_all(duplicate_private_key).unwrap();
}

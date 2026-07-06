use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::PackageCommonOptions;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_check::run_package_check;

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-check-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write_manifest(&self, source: &str) {
        fs::write(self.path.join(PACKAGE_MANIFEST_PATH), source).unwrap();
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_check_succeeds_on_proof_corpus_fixture() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args(["package", "check", "--root", "proofs"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "package check: passed\n"
    );
}

#[test]
fn package_check_succeeds_on_proof_corpus_fixture_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args(["package", "check", "--root", "proofs", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"npa.package.command_result.v0.1\",\"command\":\"package check\",\"root\":\"proofs\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
}

#[test]
fn package_check_reads_only_manifest_and_ignores_missing_artifacts() {
    let package = TestPackage::new("missing-artifacts");
    package.write_manifest(&valid_manifest(&module_block_with_sidecars(
        "Fixture.Basic",
        "Missing/Source.npa",
        "Missing/Certificate.npcert",
        "Missing/Meta.json",
        "Missing/Replay.json",
    )));

    let result = run_package_check(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    });

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.status.as_str(), "passed");
    assert!(result.diagnostics.is_empty());
}

#[test]
fn package_check_rejects_representative_invalid_manifests() {
    for fixture in invalid_fixtures() {
        let package = TestPackage::new(fixture.label);
        package.write_manifest(&fixture.source);

        let result = run_package_check(PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        });

        assert_eq!(
            result.exit_code(),
            CommandExitCode::PackageFailure,
            "{}",
            fixture.label
        );
        assert_eq!(result.diagnostics.len(), 1, "{}", fixture.label);
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.kind, fixture.kind, "{}", fixture.label);
        assert_eq!(
            diagnostic.reason_code, fixture.reason_code,
            "{}",
            fixture.label
        );
        if let Some(path) = fixture.path {
            assert_eq!(diagnostic.path.as_deref(), Some(path), "{}", fixture.label);
        }
        let json = result.render_json();
        assert!(json.contains("\"status\":\"failed\""), "{}", fixture.label);
        assert!(json.contains(fixture.reason_code), "{}", fixture.label);
        assert!(!json.contains(&package.path().to_string_lossy().to_string()));
    }
}

#[test]
fn package_check_cli_returns_exit_one_for_manifest_validation_failure() {
    let package = TestPackage::new("cli-invalid");
    package.write_manifest(&valid_manifest(&module_block(
        "Fixture.Basic",
        "../Source.npa",
        "Fixture/Basic/certificate.npcert",
        "[]",
        "[]",
    )));

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check", "--root"])
        .arg(package.path())
        .arg("--json")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"kind\":\"PackageManifest\""));
    assert!(stdout.contains("\"reason_code\":\"invalid_path\""));
    assert!(stdout.contains("\"path\":\"modules[0].source\""));
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));
}

struct InvalidFixture {
    label: &'static str,
    source: String,
    kind: DiagnosticKind,
    reason_code: &'static str,
    path: Option<&'static str>,
}

fn invalid_fixtures() -> Vec<InvalidFixture> {
    vec![
        InvalidFixture {
            label: "unknown-import",
            source: valid_manifest(&module_block(
                "Fixture.Basic",
                "Fixture/Basic/source.npa",
                "Fixture/Basic/certificate.npcert",
                r#"["Fixture.Missing"]"#,
                "[]",
            )),
            kind: DiagnosticKind::PackageGraph,
            reason_code: "unknown_import",
            path: Some("modules[0].imports[0]"),
        },
        InvalidFixture {
            label: "import-cycle",
            source: valid_manifest(&format!(
                "{}{}",
                module_block(
                    "Fixture.A",
                    "Fixture/A/source.npa",
                    "Fixture/A/certificate.npcert",
                    r#"["Fixture.B"]"#,
                    "[]",
                ),
                module_block(
                    "Fixture.B",
                    "Fixture/B/source.npa",
                    "Fixture/B/certificate.npcert",
                    r#"["Fixture.A"]"#,
                    "[]",
                )
            )),
            kind: DiagnosticKind::PackageGraph,
            reason_code: "import_cycle",
            path: None,
        },
        InvalidFixture {
            label: "path-escape",
            source: valid_manifest(&module_block(
                "Fixture.Basic",
                "../source.npa",
                "Fixture/Basic/certificate.npcert",
                "[]",
                "[]",
            )),
            kind: DiagnosticKind::PackageManifest,
            reason_code: "invalid_path",
            path: Some("modules[0].source"),
        },
        InvalidFixture {
            label: "malformed-hash",
            source: valid_manifest(&module_block_with_source_hash(
                "Fixture.Basic",
                "Fixture/Basic/source.npa",
                "Fixture/Basic/certificate.npcert",
                "sha256:not-a-valid-hash",
            )),
            kind: DiagnosticKind::PackageManifest,
            reason_code: "invalid_hash_format",
            path: Some("modules[0].expected_source_hash"),
        },
        InvalidFixture {
            label: "duplicate-module",
            source: valid_manifest(&format!(
                "{}{}",
                module_block(
                    "Fixture.Basic",
                    "Fixture/Basic/source.npa",
                    "Fixture/Basic/certificate.npcert",
                    "[]",
                    "[]",
                ),
                module_block(
                    "Fixture.Basic",
                    "Fixture/Basic2/source.npa",
                    "Fixture/Basic2/certificate.npcert",
                    "[]",
                    "[]",
                )
            )),
            kind: DiagnosticKind::PackageManifest,
            reason_code: "duplicate_module",
            path: Some("modules[1].module"),
        },
        InvalidFixture {
            label: "disallowed-axiom",
            source: valid_manifest(&module_block(
                "Fixture.Basic",
                "Fixture/Basic/source.npa",
                "Fixture/Basic/certificate.npcert",
                "[]",
                r#"["Classical.choice"]"#,
            )),
            kind: DiagnosticKind::PackageManifest,
            reason_code: "disallowed_axiom",
            path: Some("modules[0].axioms[0]"),
        },
    ]
}

fn valid_manifest(modules: &str) -> String {
    format!(
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

{modules}
"#
    )
}

fn module_block(
    module: &str,
    source: &str,
    certificate: &str,
    imports: &str,
    axioms: &str,
) -> String {
    module_block_with_hashes(module, source, certificate, imports, axioms, ZERO_HASH)
}

fn module_block_with_source_hash(
    module: &str,
    source: &str,
    certificate: &str,
    source_hash: &str,
) -> String {
    module_block_with_hashes(module, source, certificate, "[]", "[]", source_hash)
}

fn module_block_with_sidecars(
    module: &str,
    source: &str,
    certificate: &str,
    meta: &str,
    replay: &str,
) -> String {
    let mut block = module_block(module, source, certificate, "[]", "[]");
    block.push_str(&format!("meta = \"{meta}\"\nreplay = \"{replay}\"\n"));
    block
}

fn module_block_with_hashes(
    module: &str,
    source: &str,
    certificate: &str,
    imports: &str,
    axioms: &str,
    source_hash: &str,
) -> String {
    format!(
        r#"[[modules]]
module = "{module}"
source = "{source}"
certificate = "{certificate}"
imports = {imports}
expected_source_hash = "{source_hash}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
inductives = []
definitions = []
theorems = ["theorem"]
axioms = {axioms}
tags = []

"#
    )
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

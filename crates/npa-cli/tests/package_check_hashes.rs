use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::PackageCommonOptions;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_hashes::run_package_check_hashes;
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, PackageExternalImport, PackageModule, PackagePath,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-check-hashes-{}-{label}-{index}",
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

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_check_hashes_succeeds_on_proof_corpus_fixture() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args(["package", "check-hashes", "--root", "proofs"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "package check-hashes: passed\n"
    );
}

#[test]
fn package_check_hashes_succeeds_on_proof_corpus_fixture_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args(["package", "check-hashes", "--root", "proofs", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"npa.package.command_result.v0.1\",\"command\":\"package check-hashes\",\"root\":\"proofs\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
}

#[test]
fn package_check_hashes_rejects_stale_source_hash() {
    let package = build_minimal_fixture("stale-source", false);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/source.npa"),
        b"changed source bytes",
    )
    .unwrap();

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "source_hash_mismatch",
        Some("Proofs/Ai/Basic/source.npa"),
        Some("expected_source_hash"),
    );
}

#[test]
fn package_check_hashes_rejects_stale_local_certificate_file_hash() {
    let package = build_minimal_fixture("stale-local-cert", false);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        fs::read(repo_root().join("proofs/Proofs/Ai/EqReasoning/certificate.npcert")).unwrap(),
    )
    .unwrap();

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "certificate_file_hash_mismatch",
        Some("modules[0].expected_certificate_file_hash"),
        Some("expected_certificate_file_hash"),
    );
}

#[test]
fn package_check_hashes_rejects_stale_external_certificate_identity() {
    let package = build_minimal_fixture("stale-external-cert", true);
    replace_manifest_hash(&package, "export_hash = \"", "export_hash = \"", ZERO_HASH);

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "export_hash_mismatch",
        Some("imports[0].export_hash"),
        Some("export_hash"),
    );
}

#[test]
fn package_check_hashes_rejects_stale_external_certificate_file() {
    let package = build_minimal_fixture("stale-external-cert-file", true);
    tamper_certificate_hash(
        package.artifact_path("vendor/npa-std/Std/Logic/Eq/certificate.npcert"),
    );

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "certificate_hash_mismatch",
        Some("imports[0].certificate_hash"),
        Some("certificate_hash"),
    );
}

#[test]
fn package_check_hashes_maps_certificate_import_hash_mismatch_to_hash_diagnostic() {
    let package = build_module_fixture("stale-import-identity", "Proofs.Ai.Eq");
    let certificate = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_first_import_export_hash(&certificate);
    refresh_expected_certificate_file_hash(&package, &certificate);

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "lock_import_export_hash_mismatch",
        Some("entries[0].imports[0].export_hash"),
        Some("export_hash"),
    );
}

#[test]
fn package_check_hashes_rejects_stale_canonical_certificate_hash() {
    let package = build_minimal_fixture("stale-canonical-cert", false);
    replace_manifest_hash(
        &package,
        "expected_certificate_hash = \"",
        "expected_certificate_hash = \"",
        ZERO_HASH,
    );

    let result = run_hashes(&package);

    assert_hash_failure(
        &result,
        "certificate_hash_mismatch",
        Some("modules[0].expected_certificate_hash"),
        Some("expected_certificate_hash"),
    );
}

#[test]
fn package_check_hashes_rejects_stale_package_lock() {
    let package = build_minimal_fixture("stale-lock", false);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();

    let result = run_hashes(&package);

    assert_hash_failure(&result, "package_lock_stale", Some(LOCK_PATH), None);
}

#[test]
fn package_check_hashes_cli_returns_exit_one_for_hash_failure() {
    let package = build_minimal_fixture("cli-stale-source", false);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/source.npa"),
        b"changed source bytes",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check-hashes", "--root"])
        .arg(package.path())
        .arg("--json")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"kind\":\"HashMismatch\""));
    assert!(stdout.contains("\"reason_code\":\"source_hash_mismatch\""));
    assert!(stdout.contains("\"path\":\"Proofs/Ai/Basic/source.npa\""));
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));
}

fn run_hashes(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_check_hashes(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    })
}

fn assert_hash_failure(
    result: &npa_cli::diagnostic::CommandResult,
    reason: &str,
    path: Option<&str>,
    field: Option<&str>,
) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::HashMismatch);
    assert_eq!(diagnostic.reason_code, reason);
    if let Some(path) = path {
        assert_eq!(diagnostic.path.as_deref(), Some(path));
    }
    if let Some(field) = field {
        assert_eq!(diagnostic.field.as_deref(), Some(field));
    }
    assert!(!result.render_json().contains("/tmp/"));
}

fn build_minimal_fixture(label: &str, include_external: bool) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
        .unwrap();
    copy_artifact(&package, module.source.as_str());
    copy_artifact(&package, module.certificate.as_str());

    let externals = if include_external {
        let import = manifest
            .imports
            .as_ref()
            .unwrap()
            .iter()
            .find(|import| import.module.as_dotted() == "Std.Logic.Eq")
            .unwrap();
        copy_artifact(&package, import.certificate.as_str());
        vec![import]
    } else {
        Vec::new()
    };

    let manifest_source = fixture_manifest(module, &externals);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_module_fixture(label: &str, module_name: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == module_name)
        .unwrap();
    copy_artifact(&package, module.source.as_str());
    copy_artifact(&package, module.certificate.as_str());

    let imports = manifest.imports.as_ref().unwrap();
    let externals = module
        .imports
        .iter()
        .map(|module_import| {
            let import = imports
                .iter()
                .find(|import| import.module == *module_import)
                .unwrap();
            copy_artifact(&package, import.certificate.as_str());
            import
        })
        .collect::<Vec<_>>();

    let manifest_source = fixture_manifest(module, &externals);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn write_lock(package: &TestPackage, manifest_source: &str) {
    let validated = parse_and_validate_manifest_str(manifest_source).unwrap();
    let lock = build_package_lock_from_package_root(
        &validated,
        package.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap();
    let lock_json = lock.canonical_json().unwrap();
    let lock_path = package.artifact_path(LOCK_PATH);
    fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
    fs::write(lock_path, lock_json).unwrap();
}

fn fixture_manifest(module: &PackageModule, externals: &[&PackageExternalImport]) -> String {
    let mut source = format!(
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

[[modules]]
module = "{}"
source = "{}"
certificate = "{}"
imports = {}
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
        module.source.as_str(),
        module.certificate.as_str(),
        module_imports_array(module),
        format_package_hash(&module.expected_source_hash),
        format_package_hash(&module.expected_certificate_file_hash),
        format_package_hash(&module.expected_export_hash),
        format_package_hash(&module.expected_axiom_report_hash),
        format_package_hash(&module.expected_certificate_hash),
    );
    for external in externals {
        source.push_str(&format!(
            r#"[[imports]]
module = "{}"
package = "{}"
version = "{}"
certificate = "{}"
export_hash = "{}"
certificate_hash = "{}"
"#,
            external.module.as_dotted(),
            external.package.as_str(),
            external.version.as_str(),
            external.certificate.as_str(),
            format_package_hash(&external.export_hash),
            format_package_hash(&external.certificate_hash),
        ));
    }
    source
}

fn module_imports_array(module: &PackageModule) -> String {
    let imports = module
        .imports
        .iter()
        .map(|name| format!("\"{}\"", name.as_dotted()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{imports}]")
}

fn copy_artifact(package: &TestPackage, relative: &str) {
    let source = repo_root().join("proofs").join(relative);
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::copy(source, target).unwrap();
}

fn replace_manifest_hash(
    package: &TestPackage,
    needle_prefix: &str,
    replacement_prefix: &str,
    replacement_hash: &str,
) {
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let line = source
        .lines()
        .find(|line| line.starts_with(needle_prefix))
        .unwrap();
    let replacement = format!("{replacement_prefix}{replacement_hash}\"");
    fs::write(path, source.replacen(line, &replacement, 1)).unwrap();
}

fn tamper_certificate_hash(path: PathBuf) {
    let mut cert = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
    cert.hashes.certificate_hash[0] ^= 0x01;
    fs::write(path, npa_cert::encode_module_cert(&cert).unwrap()).unwrap();
}

fn tamper_first_import_export_hash(path: &Path) {
    let mut cert = npa_cert::decode_module_cert(&fs::read(path).unwrap()).unwrap();
    cert.imports[0].export_hash[0] ^= 0x01;
    fs::write(path, npa_cert::encode_module_cert(&cert).unwrap()).unwrap();
}

fn refresh_expected_certificate_file_hash(package: &TestPackage, certificate: &Path) {
    let file_hash = package_file_hash(&fs::read(certificate).unwrap());
    replace_manifest_hash(
        package,
        "expected_certificate_file_hash = \"",
        "expected_certificate_file_hash = \"",
        &format_package_hash(&file_hash),
    );
}

fn proof_manifest() -> npa_package::ValidatedPackageManifest {
    let source = fs::read_to_string(repo_root().join("proofs/npa-package.toml")).unwrap();
    parse_and_validate_manifest_str(&source).unwrap()
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

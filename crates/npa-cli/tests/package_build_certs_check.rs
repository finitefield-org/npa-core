use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use npa_cert::{AxiomPolicy, Name, VerifiedModule};
use npa_cli::args::{PackageBuildCheckCacheMode, PackageCommonOptions};
use npa_cli::diagnostic::{CommandExitCode, CommandResult, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_build::{
    run_package_build_certs_check, run_package_build_certs_check_with_cache,
};
use npa_frontend::{
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_package_build_check_result_entry_json,
    PackageBuildCheckCachedStatus, PackageHash, PackagePath, PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);
static BUILD_CHECK_CACHE_TEST_LOCK: Mutex<()> = Mutex::new(());

struct BuildCheckCacheGuard {
    _lock: MutexGuard<'static, ()>,
}

impl Drop for BuildCheckCacheGuard {
    fn drop(&mut self) {
        clear_build_check_cache();
    }
}

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-build-certs-check-{}-{label}-{index}",
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

#[derive(Clone)]
struct ManifestModule {
    module: Name,
    source: String,
    certificate: String,
    imports: Vec<Name>,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[test]
fn package_build_certs_check_succeeds_and_writes_no_files() {
    let package = build_minimal_fixture("no-write");
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_build_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_check_cli_succeeds_json() {
    let package = build_minimal_fixture("cli-json");

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "build-certs", "--root"])
        .arg(package.path())
        .arg("--check")
        .arg("--json")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"npa.package.command_result.v0.1\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
}

#[test]
fn package_build_certs_check_read_through_writes_then_hits_cache() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-hit");

    let first = run_build_check_read_through(&package);

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &first,
        "mode=read-through;hits=0;misses=1;stale=0;schema_misses=0;written=1;live_builds=1;trusted=false;build_evidence=false",
    );
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert!(!entries[0].trusted);
    assert!(!entries[0].build_evidence);
    assert_eq!(entries[0].status, PackageBuildCheckCachedStatus::Accepted);

    let second = run_build_check_read_through(&package);

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &second,
        "mode=read-through;hits=1;misses=0;stale=0;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
}

#[test]
fn package_build_certs_check_read_through_preserves_live_failure() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-failure");
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        fs::read(repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"))
            .unwrap(),
    )
    .unwrap();

    let result = run_build_check_read_through(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.reason_code == "build_certificate_changed")
            .count(),
        1
    );
    assert_build_check_cache_summary(
        &result,
        "mode=read-through;hits=0;misses=1;stale=0;schema_misses=0;written=1;live_builds=1;trusted=false;build_evidence=false",
    );
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].status, PackageBuildCheckCachedStatus::Rejected);
    assert_eq!(
        entries[0].diagnostic_reason.as_deref(),
        Some("build_certificate_changed")
    );
    assert!(!entries[0].trusted);
    assert!(!entries[0].build_evidence);
}

#[test]
fn package_build_certs_check_rejects_checked_in_certificate_byte_drift() {
    let package = build_minimal_fixture("byte-drift");
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        fs::read(repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"))
            .unwrap(),
    )
    .unwrap();

    let result = run_build_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::Build,
        "build_certificate_changed",
        Some("Proofs/Ai/Basic/certificate.npcert"),
        None,
    );
}

#[test]
fn package_build_certs_check_rejects_generated_manifest_hash_mismatch() {
    let package = build_minimal_fixture("manifest-hash");
    replace_manifest_hash(
        &package,
        "expected_certificate_hash = \"",
        "expected_certificate_hash = \"",
        ZERO_HASH,
    );

    let result = run_build_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "certificate_hash_mismatch",
        Some("modules[0].expected_certificate_hash"),
        Some("expected_certificate_hash"),
    );
}

#[test]
fn package_build_certs_check_rejects_stale_package_lock() {
    let package = build_minimal_fixture("stale-lock");
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();

    let result = run_build_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "package_lock_stale",
        Some(LOCK_PATH),
        None,
    );
}

#[test]
fn package_build_certs_check_builds_local_imports_topologically() {
    let package = build_synthetic_local_import_fixture("local-topo");

    let result = run_build_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

#[test]
fn package_build_certs_check_accepts_legacy_std_producer_profile_fixture() {
    let result = run_package_build_certs_check(PackageCommonOptions {
        root: repo_root().join("testdata/package/npa-std"),
        json: true,
    });

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

fn run_build_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    })
}

fn run_build_check_read_through(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check_with_cache(
        PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        PackageBuildCheckCacheMode::ReadThrough,
    )
}

fn build_check_cache_guard() -> BuildCheckCacheGuard {
    let guard = BUILD_CHECK_CACHE_TEST_LOCK.lock().unwrap();
    clear_build_check_cache();
    BuildCheckCacheGuard { _lock: guard }
}

fn clear_build_check_cache() {
    let path = build_check_cache_dir();
    if path.exists() {
        fs::remove_dir_all(&path).unwrap();
    }
    if let Some(parent) = path.parent() {
        let _ = fs::remove_dir(parent);
        if let Some(target_dir) = parent.parent() {
            let _ = fs::remove_dir(target_dir);
        }
    }
}

fn build_check_cache_entries() -> Vec<npa_package::PackageBuildCheckResultEntry> {
    let path = build_check_cache_dir();
    if !path.exists() {
        return Vec::new();
    }
    let mut entries = fs::read_dir(path)
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .map(|entry| {
            parse_package_build_check_result_entry_json(&fs::read_to_string(entry.path()).unwrap())
                .unwrap()
        })
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| left.cache_key.cmp(&right.cache_key));
    entries
}

fn build_check_cache_dir() -> PathBuf {
    std::env::current_dir()
        .unwrap()
        .join(PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR)
}

fn assert_build_check_cache_summary(result: &CommandResult, expected_value: &str) {
    let summary = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "build_check_cache_summary")
        .unwrap();
    assert_eq!(summary.kind, DiagnosticKind::GeneratedArtifact);
    assert_eq!(summary.field.as_deref(), Some("build_check_cache"));
    assert_eq!(summary.actual_value.as_deref(), Some(expected_value));
}

fn assert_failure(
    result: &npa_cli::diagnostic::CommandResult,
    kind: DiagnosticKind,
    reason: &str,
    path: Option<&str>,
    field: Option<&str>,
) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, kind);
    assert_eq!(diagnostic.reason_code, reason);
    if let Some(path) = path {
        assert_eq!(diagnostic.path.as_deref(), Some(path));
    }
    if let Some(field) = field {
        assert_eq!(diagnostic.field.as_deref(), Some(field));
    }
    assert!(!result.render_json().contains("/tmp/"));
}

fn build_minimal_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source =
        "theorem basic_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let (cert, _verified, _interface) =
        compile_fixture_module(0, "Proofs.Ai.Basic", source, &[], &[]);
    let source_path = "Proofs/Ai/Basic/source.npa";
    let cert_path = "Proofs/Ai/Basic/certificate.npcert";
    write_artifact(&package, source_path, source.as_bytes());
    write_artifact(&package, cert_path, &cert);

    let manifest_source = fixture_manifest(&[generated_manifest_module(
        "Proofs.Ai.Basic",
        source_path,
        cert_path,
        source.as_bytes(),
        &cert,
        Vec::new(),
    )]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_synthetic_local_import_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a =
        "theorem a_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let source_b = "import Fixture.A\n\ntheorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_b, _verified_b, _interface_b) = compile_fixture_module(
        1,
        "Fixture.B",
        source_b,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );

    let a_source_path = "Fixture/A/source.npa";
    let a_cert_path = "Fixture/A/certificate.npcert";
    let b_source_path = "Fixture/B/source.npa";
    let b_cert_path = "Fixture/B/certificate.npcert";
    write_artifact(&package, a_source_path, source_a.as_bytes());
    write_artifact(&package, a_cert_path, &cert_a);
    write_artifact(&package, b_source_path, source_b.as_bytes());
    write_artifact(&package, b_cert_path, &cert_b);

    let module_a = generated_manifest_module(
        "Fixture.A",
        a_source_path,
        a_cert_path,
        source_a.as_bytes(),
        &cert_a,
        Vec::new(),
    );
    let module_b = generated_manifest_module(
        "Fixture.B",
        b_source_path,
        b_cert_path,
        source_b.as_bytes(),
        &cert_b,
        vec![Name::from_dotted("Fixture.A")],
    );

    let manifest_source = fixture_manifest(&[module_b, module_a]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn compile_fixture_module(
    file_id: u32,
    module_name: &str,
    source: &str,
    verified_modules: &[VerifiedModule],
    source_interfaces: &[HumanImportedSourceInterface],
) -> (Vec<u8>, VerifiedModule, HumanImportedSourceInterface) {
    let module = Name::from_dotted(module_name);
    let output =
        compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
            FileId(file_id),
            module.clone(),
            source,
            verified_modules,
            source_interfaces,
            &HumanCompileOptions::default(),
            &AxiomPolicy::normal(),
        )
        .unwrap();
    let bytes = npa_cert::encode_module_cert(&output.certificate).unwrap();
    let verified = output.verified_module;
    let source_interface = HumanImportedSourceInterface {
        module,
        export_hash: output.certificate.hashes.export_hash,
        certificate_hash: Some(output.certificate.hashes.certificate_hash),
        source_interface: output.source_interface,
    };
    (bytes, verified, source_interface)
}

fn generated_manifest_module(
    module: &str,
    source: &str,
    certificate: &str,
    source_bytes: &[u8],
    certificate_bytes: &[u8],
    imports: Vec<Name>,
) -> ManifestModule {
    let cert = npa_cert::decode_module_cert(certificate_bytes).unwrap();
    ManifestModule {
        module: Name::from_dotted(module),
        source: source.to_owned(),
        certificate: certificate.to_owned(),
        imports,
        source_hash: package_file_hash(source_bytes),
        certificate_file_hash: package_file_hash(certificate_bytes),
        export_hash: PackageHash::from(cert.hashes.export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes.axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes.certificate_hash),
    }
}

fn fixture_manifest(modules: &[ManifestModule]) -> String {
    let mut source = String::from(
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

"#,
    );
    for module in modules {
        source.push_str(&format!(
            r#"[[modules]]
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
            module.source,
            module.certificate,
            module_imports_array(&module.imports),
            format_package_hash(&module.source_hash),
            format_package_hash(&module.certificate_file_hash),
            format_package_hash(&module.export_hash),
            format_package_hash(&module.axiom_report_hash),
            format_package_hash(&module.certificate_hash),
        ));
    }
    source
}

fn module_imports_array(imports: &[Name]) -> String {
    let imports = imports
        .iter()
        .map(|name| format!("\"{}\"", name.as_dotted()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{imports}]")
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

fn write_artifact(package: &TestPackage, relative: &str, bytes: &[u8]) {
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::write(target, bytes).unwrap();
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

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

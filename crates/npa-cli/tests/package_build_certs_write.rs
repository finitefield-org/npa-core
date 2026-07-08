use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::{AxiomPolicy, Name, VerifiedModule, VerifierSession};
use npa_cli::args::PackageCommonOptions;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_build::run_package_build_certs_write;
use npa_frontend::{
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface, HumanSourceInterface,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, PackageHash, PackagePath,
};

const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-build-certs-write-{}-{label}-{index}",
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

#[derive(Clone)]
struct ManifestImport {
    module: Name,
    package: String,
    version: String,
    certificate: String,
    export_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[test]
fn package_build_certs_write_repairs_local_certificate_and_package_lock() {
    let package = build_module_fixture("write-repair", "Proofs.Ai.Basic", false);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_certificate = fs::read(&certificate_path).unwrap();
    let expected_lock = fs::read_to_string(&lock_path).unwrap();
    fs::write(&certificate_path, replacement_certificate_bytes()).unwrap();
    fs::write(&lock_path, format!("{expected_lock}\n")).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read(certificate_path).unwrap(), expected_certificate);
    assert_eq!(fs::read_to_string(lock_path).unwrap(), expected_lock);
}

#[test]
fn package_build_certs_write_cli_succeeds_json() {
    let package = build_module_fixture("cli-json", "Proofs.Ai.Basic", false);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        replacement_certificate_bytes(),
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "build-certs", "--root"])
        .arg(package.path())
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
fn package_build_certs_write_is_idempotent_when_artifacts_are_current() {
    let package = build_module_fixture("idempotent", "Proofs.Ai.Basic", false);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    let certificate_temp_path = temp_path_for_artifact(&certificate_path);
    let lock_temp_path = temp_path_for_artifact(&lock_path);
    fs::write(&certificate_temp_path, b"existing certificate temp").unwrap();
    fs::write(&lock_temp_path, b"existing lock temp").unwrap();

    let first = run_write(&package);
    let second = run_write(&package);

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    assert!(first.diagnostics.is_empty());
    assert_eq!(second.exit_code(), CommandExitCode::Success);
    assert!(second.diagnostics.is_empty());
    assert_eq!(fs::read(&certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(&lock_path).unwrap(), lock_before);
    assert_eq!(
        fs::read(certificate_temp_path).unwrap(),
        b"existing certificate temp"
    );
    assert_eq!(fs::read(lock_temp_path).unwrap(), b"existing lock temp");
}

#[test]
fn package_build_certs_write_leaves_artifacts_unchanged_on_build_failure() {
    let package = build_module_fixture("build-failure", "Proofs.Ai.Basic", false);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    fs::write(&certificate_path, replacement_certificate_bytes()).unwrap();
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(&lock_path, &lock_source).unwrap();
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/source.npa"),
        b"this is not valid NPA source",
    )
    .unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Build);
    assert_eq!(result.diagnostics[0].reason_code, "build_failed");
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_write_does_not_rewrite_external_imports() {
    let package = build_module_fixture("external-preserved", "Proofs.Ai.Eq", true);
    let local_certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    let external_certificate_path =
        package.artifact_path("vendor/npa-std/Std/Logic/Eq/certificate.npcert");
    let expected_local_certificate = fs::read(&local_certificate_path).unwrap();
    let external_certificate_before = fs::read(&external_certificate_path).unwrap();
    fs::write(&local_certificate_path, replacement_certificate_bytes()).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(
        fs::read(local_certificate_path).unwrap(),
        expected_local_certificate
    );
    assert_eq!(
        fs::read(external_certificate_path).unwrap(),
        external_certificate_before
    );
}

#[test]
fn package_build_certs_write_rejects_protected_certificate_targets() {
    let package = build_module_fixture("protected-target", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let original_manifest = fs::read_to_string(&manifest_path).unwrap();
    let rewritten_manifest = original_manifest.replace(
        r#"certificate = "Proofs/Ai/Basic/certificate.npcert""#,
        r#"certificate = "npa-package.toml""#,
    );
    fs::write(&manifest_path, &rewritten_manifest).unwrap();
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let certificate_before = fs::read(&certificate_path).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::ArtifactIo);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "certificate_write_target_forbidden"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("npa-package.toml")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("package_manifest")
    );
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        rewritten_manifest
    );
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
}

#[test]
fn package_build_certs_write_rejects_external_import_certificate_target() {
    let package = build_module_fixture("external-target", "Proofs.Ai.Eq", true);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let original_manifest = fs::read_to_string(&manifest_path).unwrap();
    let rewritten_manifest = original_manifest.replace(
        r#"certificate = "Proofs/Ai/Eq/certificate.npcert""#,
        r#"certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert""#,
    );
    fs::write(&manifest_path, rewritten_manifest).unwrap();
    let external_certificate_path =
        package.artifact_path("vendor/npa-std/Std/Logic/Eq/certificate.npcert");
    let external_certificate_before = fs::read(&external_certificate_path).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::ArtifactIo);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "certificate_write_target_forbidden"
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("external_import_certificate")
    );
    assert_eq!(
        fs::read(external_certificate_path).unwrap(),
        external_certificate_before
    );
}

fn run_write(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_write(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    })
}

fn build_module_fixture(label: &str, module_name: &str, include_external: bool) -> TestPackage {
    let package = TestPackage::new(label);
    let (source_path, cert_path, source, module_imports) = module_fixture_spec(module_name);

    let (imports, verified_modules, source_interfaces) = if include_external {
        let (import, verified, source_interface) = write_std_logic_eq_external_import(&package);
        assert!(module_imports.contains(&import.module));
        (vec![import], vec![verified], vec![source_interface])
    } else {
        assert!(module_imports.is_empty());
        (Vec::new(), Vec::new(), Vec::new())
    };
    let (cert, _verified, _interface) = compile_fixture_module(
        0,
        module_name,
        source,
        &verified_modules,
        &source_interfaces,
    );
    write_artifact(&package, source_path, source.as_bytes());
    write_artifact(&package, cert_path, &cert);

    let manifest_source = fixture_manifest(
        &imports,
        &[generated_manifest_module(
            module_name,
            source_path,
            cert_path,
            source.as_bytes(),
            &cert,
            module_imports,
        )],
    );
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn module_fixture_spec(module_name: &str) -> (&'static str, &'static str, &'static str, Vec<Name>) {
    match module_name {
        "Proofs.Ai.Basic" => (
            "Proofs/Ai/Basic/source.npa",
            "Proofs/Ai/Basic/certificate.npcert",
            "theorem basic_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n",
            Vec::new(),
        ),
        "Proofs.Ai.Eq" => (
            "Proofs/Ai/Eq/source.npa",
            "Proofs/Ai/Eq/certificate.npcert",
            "import Std.Logic.Eq\n\ntheorem eq_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n",
            vec![Name::from_dotted("Std.Logic.Eq")],
        ),
        other => panic!("unsupported fixture module {other}"),
    }
}

fn write_std_logic_eq_external_import(
    package: &TestPackage,
) -> (ManifestImport, VerifiedModule, HumanImportedSourceInterface) {
    let certificate_path = "vendor/npa-std/Std/Logic/Eq/certificate.npcert";
    let bytes =
        fs::read(repo_root().join("testdata/package/npa-std/Std/Logic/Eq/certificate.npcert"))
            .unwrap();
    write_artifact(package, certificate_path, &bytes);

    let mut session = VerifierSession::new();
    let verified =
        npa_cert::verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    let module = verified.module().clone();
    let source_interface = HumanImportedSourceInterface {
        module: module.clone(),
        export_hash: verified.export_hash(),
        certificate_hash: Some(verified.certificate_hash()),
        source_interface: HumanSourceInterface::new(module.clone()),
    };
    let import = ManifestImport {
        module,
        package: "npa-std".to_owned(),
        version: "0.1.0".to_owned(),
        certificate: certificate_path.to_owned(),
        export_hash: PackageHash::from(verified.export_hash()),
        certificate_hash: PackageHash::from(verified.certificate_hash()),
    };
    (import, verified, source_interface)
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

fn fixture_manifest(imports: &[ManifestImport], modules: &[ManifestModule]) -> String {
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
    for import in imports {
        source.push_str(&format!(
            r#"[[imports]]
module = "{}"
package = "{}"
version = "{}"
certificate = "{}"
export_hash = "{}"
certificate_hash = "{}"

"#,
            import.module.as_dotted(),
            import.package.as_str(),
            import.version.as_str(),
            import.certificate.as_str(),
            format_package_hash(&import.export_hash),
            format_package_hash(&import.certificate_hash),
        ));
    }
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

fn temp_path_for_artifact(path: &Path) -> PathBuf {
    let file_name = path.file_name().unwrap().to_str().unwrap();
    path.with_file_name(format!(".{file_name}.npa-build-certs.tmp"))
}

fn write_artifact(package: &TestPackage, relative: &str, bytes: &[u8]) {
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::write(target, bytes).unwrap();
}

fn replacement_certificate_bytes() -> Vec<u8> {
    fs::read(repo_root().join("testdata/package/npa-std/Std/Nat/Basic/certificate.npcert")).unwrap()
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

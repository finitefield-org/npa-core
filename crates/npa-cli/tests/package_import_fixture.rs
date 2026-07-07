use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::{
    PackageAuditCacheMode, PackageChecker, PackageCommonOptions, PackageTimingMode,
    PackageVerifierMemoMode, PackageVerifyCertsOptions,
};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_hashes::run_package_check_hashes;
use npa_cli::package_verify::run_package_verify_certs;
use npa_package::{
    package_file_hash, parse_and_validate_manifest_str, parse_package_publish_plan_json,
    PackageCheckerMode, PackageDownstreamImportModule, PackageId, PackageVersion,
};

const DOWNSTREAM_FIXTURE_ROOT: &str = "testdata/package/npa-mathlib-seed-downstream";
const SEED_RELEASE_ROOT: &str = "testdata/package/npa-mathlib-seed";
const SEED_PUBLISH_PLAN: &str = "generated/publish-plan.json";
const SEED_PACKAGE: &str = "npa-mathlib-seed";
const SEED_VERSION: &str = "0.1.0";
const SEED_MODULE: &str = "Proofs.Ai.Basic";
const VENDORED_SEED_ROOT: &str = "vendor/npa-mathlib-seed";
const MATHLIB_DOWNSTREAM_FIXTURE_ROOT: &str = "testdata/package/npa-mathlib-downstream";
const MATHLIB_RELEASE_ROOT: &str = "testdata/package/npa-mathlib";
const MATHLIB_PACKAGE: &str = "npa-mathlib";
const MATHLIB_MODULE: &str = "Mathlib.Logic.Basic";
const MATHLIB_DOWNSTREAM_MODULE: &str = "Downstream.MathlibBasic";
const VENDORED_MATHLIB_ROOT: &str = "vendor/npa-mathlib";
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestFixture {
    path: PathBuf,
}

impl TestFixture {
    fn from_fixture_root(label: &str, fixture_root: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-import-fixture-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        copy_dir(&repo_root().join(fixture_root), &path);
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[derive(Clone, Debug)]
struct ReleaseImport {
    module: PackageDownstreamImportModule,
    certificate_bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReleaseImportError {
    ArtifactFileHash,
    FixtureCertificateHash,
    FixtureExportHash,
    FixturePackageName,
    FixturePackageVersion,
    MissingExport,
    PackageName,
    PackageVersion,
    ReferenceSummary,
}

#[test]
fn package_import_fixture_accepts_seed_release_artifacts_source_free() {
    let seed = load_seed_basic_release_import(|_| {}).unwrap();
    let fixture = materialize_downstream_fixture("valid", &seed).unwrap();

    assert_source_free_vendor(&fixture, VENDORED_SEED_ROOT);

    let hashes = run_hashes(&fixture);
    assert_eq!(hashes.exit_code(), CommandExitCode::Success);
    assert!(hashes.diagnostics.is_empty());

    let verify = run_verify(&fixture);
    assert_eq!(verify.exit_code(), CommandExitCode::Success);
    assert!(verify.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::ReferenceVerifier
            && diagnostic.reason_code == "module_verified"
            && diagnostic.module.as_deref() == Some(SEED_MODULE)
            && diagnostic.path.as_deref()
                == Some("vendor/npa-mathlib-seed/Proofs/Ai/Basic/certificate.npcert")
    }));
    assert!(verify.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::ReferenceVerifier
            && diagnostic.reason_code == "module_verified"
            && diagnostic.module.as_deref() == Some("Downstream.SeedBasic")
    }));

    let rendered = verify.render_json();
    assert!(!rendered.contains("source.npa"));
    assert!(!rendered.contains("replay.json"));
    assert!(!rendered.contains("meta.json"));
    assert!(!rendered.contains("theorem-index.json"));
    assert!(!rendered.contains("registry"));
}

#[test]
fn package_import_fixture_accepts_public_mathlib_release_artifacts_source_free() {
    let mathlib = load_mathlib_basic_release_import().unwrap();
    let fixture = materialize_downstream_fixture_from_root(
        "public-valid",
        MATHLIB_DOWNSTREAM_FIXTURE_ROOT,
        VENDORED_MATHLIB_ROOT,
        &mathlib,
    )
    .unwrap();

    assert_source_free_vendor(&fixture, VENDORED_MATHLIB_ROOT);

    let hashes = run_hashes(&fixture);
    assert_eq!(hashes.exit_code(), CommandExitCode::Success);
    assert!(hashes.diagnostics.is_empty());

    let verify = run_verify(&fixture);
    assert_eq!(verify.exit_code(), CommandExitCode::Success);
    assert!(verify.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::ReferenceVerifier
            && diagnostic.reason_code == "module_verified"
            && diagnostic.module.as_deref() == Some(MATHLIB_MODULE)
            && diagnostic.path.as_deref()
                == Some("vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert")
    }));
    assert!(verify.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::ReferenceVerifier
            && diagnostic.reason_code == "module_verified"
            && diagnostic.module.as_deref() == Some(MATHLIB_DOWNSTREAM_MODULE)
    }));

    let rendered = verify.render_json();
    assert!(!rendered.contains("source.npa"));
    assert!(!rendered.contains("replay.json"));
    assert!(!rendered.contains("meta.json"));
    assert!(!rendered.contains("theorem-index.json"));
    assert!(!rendered.contains("registry"));
}

#[test]
fn package_import_fixture_rejects_corrupted_seed_release_metadata() {
    let artifact_hash = load_seed_basic_release_import(|module| {
        module.certificate_file_hash = package_file_hash(b"corrupt seed artifact hash");
    })
    .unwrap_err();
    assert_eq!(artifact_hash, ReleaseImportError::ArtifactFileHash);

    let package_name = load_seed_basic_release_import(|module| {
        module.package = PackageId::new("npa-mathlib-seed-corrupt");
    })
    .unwrap_err();
    assert_eq!(package_name, ReleaseImportError::PackageName);

    let package_version = load_seed_basic_release_import(|module| {
        module.version = PackageVersion::new("9.9.9");
    })
    .unwrap_err();
    assert_eq!(package_version, ReleaseImportError::PackageVersion);
}

#[test]
fn package_import_fixture_rejects_corrupted_public_mathlib_release_metadata() {
    let artifact_hash = load_release_import(
        MATHLIB_RELEASE_ROOT,
        MATHLIB_PACKAGE,
        SEED_VERSION,
        MATHLIB_MODULE,
        |module| {
            module.certificate_file_hash = package_file_hash(b"corrupt mathlib artifact hash");
        },
    )
    .unwrap_err();
    assert_eq!(artifact_hash, ReleaseImportError::ArtifactFileHash);

    let package_name = load_release_import(
        MATHLIB_RELEASE_ROOT,
        MATHLIB_PACKAGE,
        SEED_VERSION,
        MATHLIB_MODULE,
        |module| {
            module.package = PackageId::new("npa-mathlib-corrupt");
        },
    )
    .unwrap_err();
    assert_eq!(package_name, ReleaseImportError::PackageName);

    let package_version = load_release_import(
        MATHLIB_RELEASE_ROOT,
        MATHLIB_PACKAGE,
        SEED_VERSION,
        MATHLIB_MODULE,
        |module| {
            module.version = PackageVersion::new("9.9.9");
        },
    )
    .unwrap_err();
    assert_eq!(package_version, ReleaseImportError::PackageVersion);
}

#[test]
fn package_import_fixture_rejects_corrupted_manifest_hash_pins() {
    let seed = load_seed_basic_release_import(|_| {}).unwrap();

    let export_fixture = materialize_downstream_fixture("bad-export", &seed).unwrap();
    replace_manifest_line_prefix(&export_fixture, "export_hash = \"", ZERO_HASH);
    assert_hash_failure(
        &run_hashes(&export_fixture),
        "export_hash_mismatch",
        Some("imports[0].export_hash"),
        Some("export_hash"),
    );

    let certificate_fixture = materialize_downstream_fixture("bad-certificate", &seed).unwrap();
    replace_manifest_line_prefix(&certificate_fixture, "certificate_hash = \"", ZERO_HASH);
    assert_hash_failure(
        &run_hashes(&certificate_fixture),
        "certificate_hash_mismatch",
        Some("imports[0].certificate_hash"),
        Some("certificate_hash"),
    );

    let mathlib = load_mathlib_basic_release_import().unwrap();

    let public_export_fixture = materialize_downstream_fixture_from_root(
        "public-bad-export",
        MATHLIB_DOWNSTREAM_FIXTURE_ROOT,
        VENDORED_MATHLIB_ROOT,
        &mathlib,
    )
    .unwrap();
    replace_manifest_line_prefix(&public_export_fixture, "export_hash = \"", ZERO_HASH);
    assert_hash_failure(
        &run_hashes(&public_export_fixture),
        "export_hash_mismatch",
        Some("imports[0].export_hash"),
        Some("export_hash"),
    );

    let public_certificate_fixture = materialize_downstream_fixture_from_root(
        "public-bad-certificate",
        MATHLIB_DOWNSTREAM_FIXTURE_ROOT,
        VENDORED_MATHLIB_ROOT,
        &mathlib,
    )
    .unwrap();
    replace_manifest_line_prefix(
        &public_certificate_fixture,
        "certificate_hash = \"",
        ZERO_HASH,
    );
    assert_hash_failure(
        &run_hashes(&public_certificate_fixture),
        "certificate_hash_mismatch",
        Some("imports[0].certificate_hash"),
        Some("certificate_hash"),
    );
}

fn load_seed_basic_release_import<F>(mutate: F) -> Result<ReleaseImport, ReleaseImportError>
where
    F: FnOnce(&mut PackageDownstreamImportModule),
{
    load_release_import(
        SEED_RELEASE_ROOT,
        SEED_PACKAGE,
        SEED_VERSION,
        SEED_MODULE,
        mutate,
    )
}

fn load_mathlib_basic_release_import() -> Result<ReleaseImport, ReleaseImportError> {
    load_release_import(
        MATHLIB_RELEASE_ROOT,
        MATHLIB_PACKAGE,
        SEED_VERSION,
        MATHLIB_MODULE,
        |_| {},
    )
}

fn load_release_import<F>(
    release_root: &str,
    package: &str,
    version: &str,
    module_name: &str,
    mutate: F,
) -> Result<ReleaseImport, ReleaseImportError>
where
    F: FnOnce(&mut PackageDownstreamImportModule),
{
    let publish_plan_path = repo_root().join(release_root).join(SEED_PUBLISH_PLAN);
    let publish_plan_source = fs::read_to_string(publish_plan_path).unwrap();
    let publish_plan = parse_package_publish_plan_json(&publish_plan_source).unwrap();
    assert_eq!(publish_plan.package.as_str(), package);
    assert_eq!(publish_plan.version.as_str(), version);
    assert_eq!(
        publish_plan.downstream_import_bundle.package.as_str(),
        package
    );
    assert_eq!(
        publish_plan.downstream_import_bundle.version.as_str(),
        version
    );

    let mut module = publish_plan
        .downstream_import_bundle
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == module_name)
        .cloned()
        .unwrap();
    mutate(&mut module);

    if module.package.as_str() != publish_plan.downstream_import_bundle.package.as_str()
        || module.package.as_str() != package
    {
        return Err(ReleaseImportError::PackageName);
    }
    if module.version.as_str() != publish_plan.downstream_import_bundle.version.as_str()
        || module.version.as_str() != version
    {
        return Err(ReleaseImportError::PackageVersion);
    }
    if !module
        .exported_declarations
        .iter()
        .any(|declaration| declaration.as_dotted() == "id")
    {
        return Err(ReleaseImportError::MissingExport);
    }
    if !module.checker_summaries.iter().any(|summary| {
        summary.module == module.module
            && summary.mode == PackageCheckerMode::Reference
            && summary.checker == "npa-checker-ref"
            && summary.status == "passed"
            && summary.export_hash == module.export_hash
            && summary.certificate_hash == module.certificate_hash
    }) {
        return Err(ReleaseImportError::ReferenceSummary);
    }

    let certificate_path = repo_root()
        .join(release_root)
        .join(module.certificate.as_str());
    let certificate_bytes = fs::read(certificate_path).unwrap();
    if package_file_hash(&certificate_bytes) != module.certificate_file_hash {
        return Err(ReleaseImportError::ArtifactFileHash);
    }

    Ok(ReleaseImport {
        module,
        certificate_bytes,
    })
}

fn materialize_downstream_fixture(
    label: &str,
    seed: &ReleaseImport,
) -> Result<TestFixture, ReleaseImportError> {
    materialize_downstream_fixture_from_root(
        label,
        DOWNSTREAM_FIXTURE_ROOT,
        VENDORED_SEED_ROOT,
        seed,
    )
}

fn materialize_downstream_fixture_from_root(
    label: &str,
    fixture_root: &str,
    vendor_root: &str,
    release: &ReleaseImport,
) -> Result<TestFixture, ReleaseImportError> {
    let fixture = TestFixture::from_fixture_root(label, fixture_root);
    assert_fixture_manifest_matches_release_bundle(&fixture, &release.module, vendor_root)?;

    let target = fixture.artifact_path(&format!(
        "{vendor_root}/{}",
        release.module.certificate.as_str()
    ));
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::write(&target, &release.certificate_bytes).unwrap();
    Ok(fixture)
}

fn assert_fixture_manifest_matches_release_bundle(
    fixture: &TestFixture,
    release_module: &PackageDownstreamImportModule,
    vendor_root: &str,
) -> Result<(), ReleaseImportError> {
    let manifest_source = fs::read_to_string(fixture.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    assert!(!manifest_source.contains("registry"));
    assert!(!manifest_source.contains("latest"));

    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    let import = validated
        .manifest()
        .imports
        .as_ref()
        .unwrap()
        .iter()
        .find(|import| import.module == release_module.module)
        .unwrap();

    if import.package != release_module.package {
        return Err(ReleaseImportError::FixturePackageName);
    }
    if import.version != release_module.version {
        return Err(ReleaseImportError::FixturePackageVersion);
    }
    if import.export_hash != release_module.export_hash {
        return Err(ReleaseImportError::FixtureExportHash);
    }
    if import.certificate_hash != release_module.certificate_hash {
        return Err(ReleaseImportError::FixtureCertificateHash);
    }
    assert_eq!(
        import.certificate.as_str(),
        format!("{vendor_root}/{}", release_module.certificate.as_str())
    );
    Ok(())
}

fn assert_source_free_vendor(fixture: &TestFixture, vendor_root: &str) {
    let vendor_root = fixture.artifact_path(vendor_root);
    assert!(vendor_root.exists());
    let forbidden_suffixes = [
        "source.npa",
        "replay.json",
        "meta.json",
        "theorem-index.json",
        "registry.json",
    ];
    for path in collect_files(&vendor_root) {
        let display = path.strip_prefix(&fixture.path).unwrap().to_string_lossy();
        assert!(
            !forbidden_suffixes
                .iter()
                .any(|suffix| display.ends_with(suffix)),
            "{display}"
        );
    }
}

fn run_hashes(fixture: &TestFixture) -> npa_cli::diagnostic::CommandResult {
    run_package_check_hashes(PackageCommonOptions {
        root: fixture.path().to_path_buf(),
        json: true,
    })
}

fn run_verify(fixture: &TestFixture) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: fixture.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::Reference,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: None,
        timings: PackageTimingMode::Off,
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

fn replace_manifest_line_prefix(fixture: &TestFixture, prefix: &str, replacement_hash: &str) {
    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&manifest_path).unwrap();
    let line = source
        .lines()
        .find(|line| line.starts_with(prefix))
        .unwrap();
    let replacement = format!("{prefix}{replacement_hash}\"");
    fs::write(manifest_path, source.replacen(line, &replacement, 1)).unwrap();
}

fn copy_dir(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let target_path = target.join(entry.file_name());
        let file_type = entry.file_type().unwrap();
        if file_type.is_dir() {
            copy_dir(&path, &target_path);
        } else if file_type.is_file() {
            fs::copy(path, target_path).unwrap();
        }
    }
}

fn collect_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_files_into(root, &mut files);
    files.sort();
    files
}

fn collect_files_into(root: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let file_type = entry.file_type().unwrap();
        if file_type.is_dir() {
            collect_files_into(&path, files);
        } else if file_type.is_file() {
            files.push(path);
        }
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::{AxiomPolicy, Name, VerifiedModule, VerifierSession};
use npa_cli::args::PackageChecker;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{
    audit_artifact_ledger_modules, common_options, refresh_artifacts_check,
    refresh_artifacts_write, verify_certs_full,
};
use npa_cli::package_artifact_ledger::run_package_artifact_ledger_audit;
use npa_cli::package_build::{
    run_package_build_certs, run_package_build_certs_check, run_package_build_certs_write,
};
use npa_cli::package_hashes::run_package_check_hashes;
use npa_cli::package_verify::run_package_verify_certs;
use npa_frontend::{
    compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy,
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface, HumanSourceInterface,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_package_artifact_ledger_metadata, PackageHash,
    PackageLockErrorReason, PackagePath,
};

const LOCK_PATH: &str = "generated/package-lock.json";
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const FRONTEND_FAILURE_MESSAGE: &str =
    "unannotated Human lambda binder requires an expected function type";
const FRONTEND_FAILURE_SOURCE: &str =
    "def product_enumeration_bad : Type := fun product => product\n";

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
fn package_build_certs_frontend_failure_write_is_atomic() {
    let package = build_frontend_failure_fixture("frontend-failure-write");
    let before = package_snapshot(&package);

    let result = run_write(&package);

    assert_frontend_failure(&result);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_frontend_failure_refresh_check_is_read_only() {
    let package = build_frontend_failure_fixture("frontend-failure-refresh-check");
    let before = package_snapshot(&package);

    let result = run_refresh_check(&package);

    assert_frontend_failure(&result);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_frontend_failure_refresh_write_is_atomic() {
    let package = build_frontend_failure_fixture("frontend-failure-refresh-write");
    let before = package_snapshot(&package);

    let result = run_refresh_write(&package);

    assert_frontend_failure(&result);
    assert_eq!(package_snapshot(&package), before);
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
        "{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
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
fn package_build_certs_refresh_write_is_idempotent_when_artifacts_are_current() {
    let package = build_module_fixture("refresh-write-idempotent", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    let manifest_temp_path = temp_path_for_artifact(&manifest_path);
    let certificate_temp_path = temp_path_for_artifact(&certificate_path);
    let lock_temp_path = temp_path_for_artifact(&lock_path);
    fs::write(&manifest_temp_path, b"existing manifest temp").unwrap();
    fs::write(&certificate_temp_path, b"existing certificate temp").unwrap();
    fs::write(&lock_temp_path, b"existing lock temp").unwrap();

    let first = run_refresh_write(&package);
    let second = run_refresh_write(&package);

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    assert!(first.diagnostics.is_empty());
    assert_eq!(second.exit_code(), CommandExitCode::Success);
    assert!(second.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
    assert_eq!(
        fs::read(manifest_temp_path).unwrap(),
        b"existing manifest temp"
    );
    assert_eq!(
        fs::read(certificate_temp_path).unwrap(),
        b"existing certificate temp"
    );
    assert_eq!(fs::read(lock_temp_path).unwrap(), b"existing lock temp");
}

#[test]
fn package_build_certs_refresh_write_repairs_stale_source_hash() {
    let package = build_module_fixture("refresh-write-stale-source", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_manifest = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    replace_manifest_hash(
        &package,
        "expected_source_hash = \"",
        "expected_source_hash = \"",
        ZERO_HASH,
    );
    let stale_manifest = fs::read_to_string(&manifest_path).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_ne!(stale_manifest, expected_manifest);
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        expected_manifest
    );
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_refresh_write_rebuilds_stale_local_direct_import_identity() {
    let package = build_local_import_fixture("refresh-stale-local-import");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let expected_manifest = fs::read_to_string(&manifest_path).unwrap();
    replace_module_manifest_hash(&package, "Fixture.A", "expected_export_hash", ZERO_HASH);

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        expected_manifest
    );
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_selection_targeted_refresh_rebuilds_dependents() {
    let package = build_local_import_fixture("targeted-refresh-dependent-closure");
    let dependent_path = package.artifact_path("Fixture/B/certificate.npcert");
    let expected_dependent = fs::read(&dependent_path).unwrap();
    fs::write(&dependent_path, replacement_certificate_bytes()).unwrap();

    let result = run_package_build_certs(
        refresh_artifacts_write(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.A")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("seeds=1,rebuild=2"));
    assert_eq!(fs::read(dependent_path).unwrap(), expected_dependent);
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_selection_targeted_leaf_refresh_preserves_unselected_module() {
    let package = build_local_import_fixture("targeted-refresh-leaf");
    let support_path = package.artifact_path("Fixture/A/certificate.npcert");
    let leaf_path = package.artifact_path("Fixture/B/certificate.npcert");
    let support_before = fs::read(&support_path).unwrap();
    let expected_leaf = fs::read(&leaf_path).unwrap();
    fs::write(&leaf_path, replacement_certificate_bytes()).unwrap();

    let result = run_package_build_certs(
        refresh_artifacts_write(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.B")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("seeds=1,rebuild=1,support_local=1"));
    assert_eq!(fs::read(support_path).unwrap(), support_before);
    assert_eq!(fs::read(leaf_path).unwrap(), expected_leaf);
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_write_refresh_outputs_pass_downstream_verification() {
    let package = build_local_import_fixture("refresh-end-to-end");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Fixture/B/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    replace_module_manifest_hash(&package, "Fixture.A", "expected_export_hash", ZERO_HASH);
    let stale_manifest_source = fs::read_to_string(&manifest_path).unwrap();
    let stale_validated = parse_and_validate_manifest_str(&stale_manifest_source).unwrap();
    let stale_lock_error = build_package_lock_from_package_root(
        &stale_validated,
        package.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap_err();
    fs::write(&certificate_path, replacement_certificate_bytes()).unwrap();
    fs::remove_file(&lock_path).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(
        stale_lock_error.reason_code,
        PackageLockErrorReason::ExportHashMismatch
    );
    assert_eq!(stale_lock_error.path, "modules[1].expected_export_hash");
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert!(!fs::read_to_string(&manifest_path)
        .unwrap()
        .contains(ZERO_HASH));
    assert!(lock_path.exists());
    assert_refresh_package_is_hash_clean(&package);
    assert_refresh_package_verifies_with_reference_checker(&package);
    assert_eq!(
        fs::read_to_string(lock_path).unwrap(),
        canonical_lock_json_from_root(&package)
    );
}

#[test]
fn package_build_certs_refresh_write_repairs_certificate_manifest_and_lock_together() {
    let package = build_module_fixture("refresh-repair-all", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_manifest = fs::read_to_string(&manifest_path).unwrap();
    let expected_certificate = fs::read(&certificate_path).unwrap();
    let expected_lock = fs::read_to_string(&lock_path).unwrap();
    replace_manifest_hash(
        &package,
        "expected_source_hash = \"",
        "expected_source_hash = \"",
        ZERO_HASH,
    );
    fs::write(&certificate_path, replacement_certificate_bytes()).unwrap();
    fs::write(&lock_path, format!("{expected_lock}\n")).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        expected_manifest
    );
    assert_eq!(fs::read(certificate_path).unwrap(), expected_certificate);
    assert_eq!(fs::read_to_string(lock_path).unwrap(), expected_lock);
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_refresh_write_recreates_missing_certificate_and_lock() {
    let package = build_module_fixture("refresh-recreate-missing", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_manifest = fs::read_to_string(&manifest_path).unwrap();
    let expected_certificate = fs::read(&certificate_path).unwrap();
    fs::remove_file(&certificate_path).unwrap();
    fs::remove_dir_all(package.artifact_path("generated")).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        expected_manifest
    );
    assert_eq!(fs::read(certificate_path).unwrap(), expected_certificate);
    assert!(lock_path.exists());
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_refresh_write_regenerates_stale_package_lock() {
    let package = build_module_fixture("refresh-stale-lock", "Proofs.Ai.Basic", false);
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_lock = fs::read_to_string(&lock_path).unwrap();
    fs::write(&lock_path, format!("{expected_lock}\n")).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(lock_path).unwrap(), expected_lock);
    assert_refresh_package_is_hash_clean(&package);
}

#[test]
fn package_build_certs_refresh_updates_metadata_and_preserves_extensions() {
    let package = build_module_fixture("refresh-metadata", "Proofs.Ai.Basic", false);
    let metadata_path = install_metadata_target(
        &package,
        Some("{\"schema\":\"npa-ai-proof-meta-v0.1\",\"z_extension\":{\"b\":2,\"a\":1}}\n"),
    );

    let check = run_refresh_check(&package);
    assert_eq!(check.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(check.diagnostics[0].reason_code, "module_metadata_stale");

    let write = run_refresh_write(&package);
    assert_eq!(write.exit_code(), CommandExitCode::Success);
    assert!(write.diagnostics.is_empty());
    let metadata = fs::read_to_string(&metadata_path).unwrap();
    assert!(metadata.contains("\"module\": \"Proofs.Ai.Basic\""));
    assert!(metadata.contains("\"z_extension\": {\"b\":2,\"a\":1}"));
    assert_eq!(
        run_refresh_check(&package).exit_code(),
        CommandExitCode::Success
    );
}

#[test]
fn package_build_certs_refresh_metadata_uses_direct_imports_and_passes_audit() {
    let package = build_transitive_metadata_fixture("refresh-metadata-direct-imports");

    let write = run_refresh_write(&package);

    assert_eq!(write.exit_code(), CommandExitCode::Success);
    assert!(write.diagnostics.is_empty());
    assert_transitive_certificate_and_direct_metadata(&package);
    assert_transitive_metadata_audit_passes(&package);
    assert_eq!(
        run_refresh_check(&package).exit_code(),
        CommandExitCode::Success
    );
}

#[test]
fn package_build_certs_targeted_refresh_metadata_uses_direct_imports() {
    let package = build_transitive_metadata_fixture("targeted-refresh-metadata-direct-imports");

    let write = run_package_build_certs(
        refresh_artifacts_write(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.C")]),
    );

    assert_eq!(write.exit_code(), CommandExitCode::Success);
    assert_eq!(write.diagnostics.len(), 1);
    assert_eq!(write.diagnostics[0].reason_code, "package_build_selection");
    assert_transitive_certificate_and_direct_metadata(&package);
    assert_transitive_metadata_audit_passes(&package);
    assert_eq!(
        run_refresh_check(&package).exit_code(),
        CommandExitCode::Success
    );
}

#[test]
fn package_build_certs_refresh_check_reports_missing_metadata() {
    let package = build_module_fixture("refresh-missing-metadata", "Proofs.Ai.Basic", false);
    let metadata_path = install_metadata_target(&package, None);

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics[0].reason_code, "module_metadata_missing");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("Proofs/Ai/Basic/meta.json")
    );
    assert!(!metadata_path.exists());
}

#[test]
fn package_build_certs_refresh_write_rejects_package_lock_as_metadata_target() {
    let package = build_module_fixture("refresh-metadata-lock-collision", "Proofs.Ai.Basic", false);
    install_package_lock_metadata_target(&package);
    let before = package_snapshot(&package);

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::ArtifactIo);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "module_metadata_write_target_forbidden"
    );
    assert_eq!(result.diagnostics[0].path.as_deref(), Some(LOCK_PATH));
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("modules[0].meta")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("package_lock")
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_refresh_rejects_package_lock_as_metadata_target() {
    let package = build_module_fixture(
        "targeted-refresh-metadata-lock-collision",
        "Proofs.Ai.Basic",
        false,
    );
    install_package_lock_metadata_target(&package);
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_write(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Proofs.Ai.Basic")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "module_metadata_write_target_forbidden"
    );
    assert_eq!(result.diagnostics[1].path.as_deref(), Some(LOCK_PATH));
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some("package_lock")
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_ordinary_check_does_not_refresh_metadata() {
    let package = build_module_fixture("ordinary-check-metadata", "Proofs.Ai.Basic", false);
    let metadata_path = install_metadata_target(&package, Some("{"));
    let before = fs::read(&metadata_path).unwrap();

    let result = run_package_build_certs_check(common_options(package.path(), true));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(fs::read(metadata_path).unwrap(), before);
}

#[test]
fn package_build_certs_refresh_write_cleans_staged_files_on_late_staging_failure() {
    let package = build_module_fixture("refresh-staging-failure", "Proofs.Ai.Basic", false);
    let metadata_path = install_metadata_target(
        &package,
        Some("{\"schema\":\"npa-ai-proof-meta-v0.1\",\"extension\":true}\n"),
    );
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    replace_manifest_hash(
        &package,
        "expected_source_hash = \"",
        "expected_source_hash = \"",
        ZERO_HASH,
    );
    fs::write(&certificate_path, replacement_certificate_bytes()).unwrap();
    fs::remove_file(&lock_path).unwrap();
    fs::create_dir(&lock_path).unwrap();
    let stale_manifest = fs::read_to_string(&manifest_path).unwrap();
    let stale_certificate = fs::read(&certificate_path).unwrap();
    let stale_metadata = fs::read(&metadata_path).unwrap();
    let unrelated_temp = package.artifact_path("generated/.unrelated.npa-build-certs.tmp");
    fs::write(&unrelated_temp, b"pre-existing temp").unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::ArtifactIo);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "package_lock_write_failed"
    );
    assert_eq!(result.diagnostics[0].path.as_deref(), Some(LOCK_PATH));
    assert_eq!(fs::read_to_string(&manifest_path).unwrap(), stale_manifest);
    assert_eq!(fs::read(&certificate_path).unwrap(), stale_certificate);
    assert_eq!(fs::read(&metadata_path).unwrap(), stale_metadata);
    assert!(lock_path.is_dir());
    assert!(!temp_path_for_artifact(&certificate_path).exists());
    assert!(!temp_path_for_artifact(&manifest_path).exists());
    assert_eq!(fs::read(unrelated_temp).unwrap(), b"pre-existing temp");
}

#[test]
fn package_build_certs_refresh_write_reports_certificate_write_failure_without_later_writes() {
    let package = build_module_fixture(
        "refresh-certificate-write-failure",
        "Proofs.Ai.Basic",
        false,
    );
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    fs::remove_file(&certificate_path).unwrap();
    fs::create_dir(&certificate_path).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::ArtifactIo);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "certificate_write_failed"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("Proofs/Ai/Basic/certificate.npcert")
    );
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
    assert!(certificate_path.is_dir());
}

#[test]
fn package_build_certs_refresh_write_preserves_preexisting_manifest_temp_path() {
    let package = build_module_fixture("refresh-manifest-write-failure", "Proofs.Ai.Basic", false);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    replace_manifest_hash(
        &package,
        "expected_source_hash = \"",
        "expected_source_hash = \"",
        ZERO_HASH,
    );
    let stale_manifest = fs::read_to_string(&manifest_path).unwrap();
    let manifest_temp_path = temp_path_for_artifact(&manifest_path);
    fs::create_dir(&manifest_temp_path).unwrap();

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_ne!(fs::read_to_string(manifest_path).unwrap(), stale_manifest);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
    assert!(manifest_temp_path.is_dir());
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
fn package_build_certs_refresh_write_rejects_external_import_drift() {
    let package = build_module_fixture("refresh-external-drift", "Proofs.Ai.Eq", true);
    replace_manifest_hash(&package, "export_hash = \"", "export_hash = \"", ZERO_HASH);

    let result = run_refresh_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[0].reason_code, "export_hash_mismatch");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("imports[0].export_hash")
    );
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("export_hash"));
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
    run_package_build_certs_write(common_options(package.path(), true))
}

fn run_refresh_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(refresh_artifacts_check(common_options(
        package.path(),
        true,
    )))
}

fn run_refresh_write(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(refresh_artifacts_write(common_options(
        package.path(),
        true,
    )))
}

fn install_metadata_target(package: &TestPackage, existing: Option<&str>) -> PathBuf {
    install_metadata_target_for_module(
        package,
        "Proofs.Ai.Basic",
        "Proofs/Ai/Basic/certificate.npcert",
        "Proofs/Ai/Basic/meta.json",
        existing,
    )
}

fn install_metadata_target_for_module(
    package: &TestPackage,
    module: &str,
    certificate: &str,
    metadata: &str,
    existing: Option<&str>,
) -> PathBuf {
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&manifest_path).unwrap();
    let module_marker = format!("module = \"{module}\"\n");
    let module_start = source.find(&module_marker).unwrap();
    let needle = format!("certificate = \"{certificate}\"\n");
    let relative_certificate = source[module_start..].find(&needle).unwrap();
    let certificate_start = module_start + relative_certificate;
    let certificate_end = certificate_start + needle.len();
    let mut updated = source;
    updated.insert_str(
        certificate_end,
        &format!("meta = \"{metadata}\"\nproducer_profile = \"human-surface-explicit-term\"\n"),
    );
    assert_eq!(
        updated.matches(&format!("meta = \"{metadata}\"")).count(),
        1
    );
    fs::write(&manifest_path, &updated).unwrap();
    write_lock(package, &updated);
    let path = package.artifact_path(metadata);
    if let Some(existing) = existing {
        write_artifact(package, metadata, existing.as_bytes());
    }
    path
}

fn install_package_lock_metadata_target(package: &TestPackage) {
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let lock_path = package.artifact_path(LOCK_PATH);
    let source = fs::read_to_string(&manifest_path).unwrap();
    let needle = "certificate = \"Proofs/Ai/Basic/certificate.npcert\"\n";
    assert_eq!(source.matches(needle).count(), 1);
    let source = source.replacen(
        needle,
        &format!(
            "{needle}meta = \"{LOCK_PATH}\"\nproducer_profile = \"human-surface-explicit-term\"\n"
        ),
        1,
    );
    fs::write(manifest_path, source).unwrap();
    fs::remove_file(lock_path).unwrap();
}

fn build_frontend_failure_fixture(label: &str) -> TestPackage {
    let package = build_module_fixture(label, "Proofs.Ai.Basic", false);
    write_artifact(
        &package,
        "Proofs/Ai/Basic/source.npa",
        FRONTEND_FAILURE_SOURCE.as_bytes(),
    );
    let source_hash = format_package_hash(&package_file_hash(FRONTEND_FAILURE_SOURCE.as_bytes()));
    replace_module_manifest_hash(
        &package,
        "Proofs.Ai.Basic",
        "expected_source_hash",
        &source_hash,
    );
    package
}

fn assert_frontend_failure(result: &npa_cli::diagnostic::CommandResult) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.artifacts.is_empty());
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::Build);
    assert_eq!(diagnostic.reason_code, "build_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Basic"));
    assert_eq!(diagnostic.path.as_deref(), Some("modules[0].source"));
    assert_eq!(diagnostic.field.as_deref(), Some("elaborator"));
    assert_eq!(
        diagnostic.actual_value.as_deref(),
        Some(FRONTEND_FAILURE_MESSAGE)
    );
    let source = diagnostic
        .source
        .as_ref()
        .expect("frontend failure should retain source context");
    let start = FRONTEND_FAILURE_SOURCE
        .find("fun product")
        .expect("failing binder") as u32
        + "fun ".len() as u32;
    let end = start + "product".len() as u32;
    assert_eq!(source.path(), "Proofs/Ai/Basic/source.npa");
    assert_eq!(source.start_byte(), start);
    assert_eq!(source.end_byte(), end);
    assert_eq!(
        FRONTEND_FAILURE_SOURCE.get(start as usize..end as usize),
        Some("product")
    );
    assert_eq!(source.declaration(), Some("product_enumeration_bad"));
}

fn package_snapshot(package: &TestPackage) -> BTreeMap<String, Option<Vec<u8>>> {
    fn visit(root: &Path, current: &Path, snapshot: &mut BTreeMap<String, Option<Vec<u8>>>) {
        let mut entries = fs::read_dir(current)
            .unwrap()
            .map(|entry| entry.unwrap())
            .collect::<Vec<_>>();
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            let relative = path
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .into_owned();
            if path.is_dir() {
                snapshot.insert(format!("{relative}/"), None);
                visit(root, &path, snapshot);
            } else {
                snapshot.insert(relative, Some(fs::read(path).unwrap()));
            }
        }
    }

    let mut snapshot = BTreeMap::new();
    visit(package.path(), package.path(), &mut snapshot);
    snapshot
}

fn assert_refresh_package_is_hash_clean(package: &TestPackage) {
    let result = run_package_check_hashes(common_options(package.path(), true));
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(
        result.diagnostics.is_empty(),
        "expected clean check-hashes diagnostics, got {:?}",
        result.diagnostics
    );
}

fn assert_refresh_package_verifies_with_reference_checker(package: &TestPackage) {
    let result = run_package_verify_certs(verify_certs_full(
        common_options(package.path(), true),
        PackageChecker::Reference,
    ));
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::ReferenceVerifier
                && diagnostic.reason_code == "package_verified"
        }),
        "expected reference package verification diagnostic, got {:?}",
        result.diagnostics
    );
}

fn canonical_lock_json_from_root(package: &TestPackage) -> String {
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    build_package_lock_from_package_root(
        &validated,
        package.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap()
    .canonical_json()
    .unwrap()
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

fn build_local_import_fixture(label: &str) -> TestPackage {
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

    let manifest_source = fixture_manifest(&[], &[module_b, module_a]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_transitive_metadata_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a = "def Carrier : Sort 2 := Type\n";
    let source_b = "import Fixture.A\n\ndef Surface : Sort 2 := Carrier\n";
    let source_c = "import Fixture.B\n\ndef SurfaceAlias : Sort 2 := Surface\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_b, verified_b, interface_b) = compile_fixture_module_with_available(
        1,
        "Fixture.B",
        source_b,
        &[&verified_a],
        &[&verified_a],
        std::slice::from_ref(&interface_a),
    );
    let (cert_c, _verified_c, _interface_c) = compile_fixture_module_with_available(
        2,
        "Fixture.C",
        source_c,
        &[&verified_b],
        &[&verified_a, &verified_b],
        std::slice::from_ref(&interface_b),
    );

    let modules = [
        (
            "Fixture.C",
            "Fixture/C/source.npa",
            "Fixture/C/certificate.npcert",
            source_c,
            cert_c,
            vec![Name::from_dotted("Fixture.B")],
        ),
        (
            "Fixture.B",
            "Fixture/B/source.npa",
            "Fixture/B/certificate.npcert",
            source_b,
            cert_b,
            vec![Name::from_dotted("Fixture.A")],
        ),
        (
            "Fixture.A",
            "Fixture/A/source.npa",
            "Fixture/A/certificate.npcert",
            source_a,
            cert_a,
            Vec::new(),
        ),
    ];
    let mut manifest_modules = Vec::new();
    for (module, source_path, certificate_path, source, certificate, imports) in modules {
        write_artifact(&package, source_path, source.as_bytes());
        write_artifact(&package, certificate_path, &certificate);
        manifest_modules.push(generated_manifest_module(
            module,
            source_path,
            certificate_path,
            source.as_bytes(),
            &certificate,
            imports,
        ));
    }
    let manifest_source = fixture_manifest(&[], &manifest_modules);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    install_metadata_target_for_module(
        &package,
        "Fixture.C",
        "Fixture/C/certificate.npcert",
        "Fixture/C/meta.json",
        Some("{\"schema\":\"npa-ai-proof-meta-v0.1\",\"z_extension\":{\"b\":2,\"a\":1}}\n"),
    );
    package
}

fn assert_transitive_certificate_and_direct_metadata(package: &TestPackage) {
    let certificate = fs::read(package.artifact_path("Fixture/C/certificate.npcert")).unwrap();
    let certificate = npa_cert::decode_module_cert(&certificate).unwrap();
    let certificate_imports = certificate
        .imports
        .iter()
        .map(|import| import.module.clone())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        certificate_imports,
        [
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.B")
        ]
        .into_iter()
        .collect()
    );

    let metadata_source = fs::read_to_string(package.artifact_path("Fixture/C/meta.json")).unwrap();
    let metadata = parse_package_artifact_ledger_metadata(&metadata_source).unwrap();
    assert_eq!(metadata.imports, vec![Name::from_dotted("Fixture.B")]);
    assert!(metadata_source.contains("\"z_extension\": {\"b\":2,\"a\":1}"));
}

fn assert_transitive_metadata_audit_passes(package: &TestPackage) {
    let audit = run_package_artifact_ledger_audit(audit_artifact_ledger_modules(
        common_options(package.path(), true),
        vec![Name::from_dotted("Fixture.C")],
    ));
    assert_eq!(audit.exit_code(), CommandExitCode::Success);
    assert!(
        audit.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason_code == "artifact_ledger_module_classified"
                && diagnostic.actual_value.as_deref()
                    == Some(
                        "hash_drift_class=consistent,identity_parity=matches,checker_status=checked",
                    )
        }),
        "expected clean artifact-ledger classification, got {:?}",
        audit.diagnostics
    );
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

fn compile_fixture_module_with_available(
    file_id: u32,
    module_name: &str,
    source: &str,
    direct_verified_modules: &[&VerifiedModule],
    available_verified_modules: &[&VerifiedModule],
    source_interfaces: &[HumanImportedSourceInterface],
) -> (Vec<u8>, VerifiedModule, HumanImportedSourceInterface) {
    let module = Name::from_dotted(module_name);
    let output =
        compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy(
            FileId(file_id),
            module.clone(),
            source,
            direct_verified_modules,
            available_verified_modules,
            source_interfaces,
            &HumanCompileOptions::default(),
            &AxiomPolicy::normal(),
        )
        .unwrap();
    let bytes = npa_cert::encode_module_cert(&output.certificate).unwrap();
    let source_interface = HumanImportedSourceInterface {
        module,
        export_hash: output.certificate.hashes.export_hash,
        certificate_hash: Some(output.certificate.hashes.certificate_hash),
        source_interface: output.source_interface,
    };
    (bytes, output.verified_module, source_interface)
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

fn replace_module_manifest_hash(
    package: &TestPackage,
    module_name: &str,
    field: &str,
    replacement_hash: &str,
) {
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let module_line = format!("module = \"{module_name}\"");
    let field_prefix = format!("{field} = \"");
    let mut output = String::new();
    let mut in_target_module = false;
    let mut replaced = false;
    for line in source.lines() {
        if line == "[[modules]]" {
            in_target_module = false;
        } else if line == module_line {
            in_target_module = true;
        }
        if in_target_module && line.starts_with(&field_prefix) {
            output.push_str(&format!("{field} = \"{replacement_hash}\""));
            replaced = true;
        } else {
            output.push_str(line);
        }
        output.push('\n');
    }
    if !source.ends_with('\n') {
        output.pop();
    }
    assert!(replaced, "expected to replace {field} for {module_name}");
    fs::write(path, output).unwrap();
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

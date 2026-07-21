use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use npa_cert::{AxiomPolicy, Name, VerifiedModule};
use npa_cli::args::PackageBuildCheckCacheMode;
use npa_cli::diagnostic::{CommandExitCode, CommandResult, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{build_certs_check, common_options, refresh_artifacts_check};
use npa_cli::package_build::{
    run_package_build_certs, run_package_build_certs_check,
    run_package_build_certs_check_with_cache,
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
const FRONTEND_FAILURE_MESSAGE: &str =
    "unannotated Human lambda binder requires an expected function type";
const FRONTEND_FAILURE_SOURCE: &str =
    "def product_enumeration_bad : Type := fun product => product\n";

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
fn package_build_certs_frontend_failure_check_terminal_reports_source_context_without_writes() {
    let package = build_minimal_fixture("frontend-failure-terminal");
    install_frontend_failure(&package, "Proofs/Ai/Basic/source.npa", "Proofs.Ai.Basic");
    let before = package_snapshot(&package);

    let result = run_build_check(&package);

    assert_frontend_failure(
        &result,
        "Proofs.Ai.Basic",
        "modules[0].source",
        "Proofs/Ai/Basic/source.npa",
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_frontend_failure_check_dependent_reports_source_context_without_writes() {
    let package = build_synthetic_local_import_fixture("frontend-failure-dependent");
    install_frontend_failure(&package, "Fixture/A/source.npa", "Fixture.A");
    let before = package_snapshot(&package);

    let result = run_build_check(&package);

    assert_frontend_failure(
        &result,
        "Fixture.A",
        "modules[1].source",
        "Fixture/A/source.npa",
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_frontend_failure_check_cli_json_is_exact_and_private() {
    let package = build_minimal_fixture("frontend-failure-cli-json");
    install_frontend_failure(&package, "Proofs/Ai/Basic/source.npa", "Proofs.Ai.Basic");
    let before = package_snapshot(&package);
    let (start, end) = frontend_failure_binder_range();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "build-certs", "--root"])
        .arg(package.path())
        .arg("--check")
        .arg("--json")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        stdout,
        format!(
            "{{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"failed\",\"diagnostics\":[{{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"module\":\"Proofs.Ai.Basic\",\"path\":\"modules[0].source\",\"field\":\"elaborator\",\"actual_value\":\"{FRONTEND_FAILURE_MESSAGE}\",\"source\":{{\"path\":\"Proofs/Ai/Basic/source.npa\",\"start_byte\":{start},\"end_byte\":{end},\"declaration\":\"product_enumeration_bad\",\"line\":1,\"column\":{},\"token\":\"product\"}}}}],\"artifacts\":[]}}\n",
            start + 1
        )
    );
    assert_eq!(stdout.lines().count(), 1);
    assert!(!stdout.contains(&package.path().display().to_string()));
    assert!(!stdout.contains(FRONTEND_FAILURE_SOURCE));
    assert_eq!(package_snapshot(&package), before);
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
fn package_build_certs_selection_named_check_skips_unrelated_dependent_source() {
    let package = build_synthetic_local_import_fixture("targeted-check-skips-dependent");
    install_frontend_failure(&package, "Fixture/B/source.npa", "Fixture.B");
    let before = package_snapshot(&package);
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.A")]),
    );
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("seeds=1,rebuild=1"));
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_selection_rejects_stale_support_source() {
    let package = build_synthetic_local_import_fixture("targeted-check-stale-support");
    let source_path = package.artifact_path("Fixture/A/source.npa");
    let mut source = fs::read_to_string(&source_path).unwrap();
    source.push('\n');
    fs::write(source_path, source).unwrap();
    let before = package_snapshot(&package);
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.B")]),
    );
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(
        result.diagnostics[1].reason_code,
        "selection_dependency_source_stale"
    );
    assert_eq!(result.diagnostics[1].module.as_deref(), Some("Fixture.A"));
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_external_closure_is_topological_and_skips_unrelated() {
    let package = build_synthetic_external_import_chain_fixture("targeted-external-closure");
    fs::write(
        package
            .artifact_path("vendor/fixture-external/Fixture/External/Unrelated/certificate.npcert"),
        b"not a certificate",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some(
            "mode=modules,seeds=1,rebuild=1,support_local=0,support_external=1,changed_external=0"
        )
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_external_closure_rejects_transitive_pin_drift() {
    let package = build_synthetic_external_import_chain_fixture("targeted-external-pin-drift");
    replace_external_manifest_hash(&package, "Fixture.External.Base", "export_hash", ZERO_HASH);
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(result.diagnostics[1].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[1].reason_code, "export_hash_mismatch");
    assert_eq!(
        result.diagnostics[1].path.as_deref(),
        Some("imports[2].export_hash")
    );
    assert_eq!(result.diagnostics[1].field.as_deref(), Some("export_hash"));
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_external_closure_rejects_cycles_deterministically() {
    let package = build_synthetic_external_import_chain_fixture("targeted-external-cycle");
    install_external_import_cycle(&package);
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(result.diagnostics[1].kind, DiagnosticKind::PackageGraph);
    assert_eq!(result.diagnostics[1].reason_code, "lock_import_cycle");
    assert_eq!(
        result.diagnostics[1].module.as_deref(),
        Some("Fixture.External.Base")
    );
    assert_eq!(
        result.diagnostics[1].path.as_deref(),
        Some("imports[2].certificate.imports")
    );
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some("Fixture.External.Leaf -> Fixture.External.Base -> Fixture.External.Leaf")
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_external_changed_selection_uses_transitive_closure() {
    let package = build_synthetic_external_import_chain_fixture("changed-external-closure");
    init_git_package(&package, true);
    install_changed_external_leaf_certificate(&package);
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some(
            "mode=changed,seeds=0,rebuild=0,support_local=0,support_external=0,changed_external=1"
        )
    );
    assert_eq!(result.diagnostics[1].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[1].reason_code, "export_hash_mismatch");
    assert_eq!(
        result.diagnostics[1].path.as_deref(),
        Some("imports[0].export_hash")
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_selection_changed_covers_unstaged_and_staged_source() {
    let package = build_synthetic_local_import_fixture("changed-staged-unstaged");
    init_git_package(&package, true);
    let source_path = package.artifact_path("Fixture/B/source.npa");
    let mut source = fs::read_to_string(&source_path).unwrap();
    source.push('\n');
    fs::write(&source_path, source).unwrap();

    for staged in [false, true] {
        if staged {
            let status = Command::new("/usr/bin/git")
                .args(["add", "--", "Fixture/B/source.npa"])
                .current_dir(package.path())
                .status()
                .unwrap();
            assert!(status.success());
        }
        let result = run_package_build_certs(
            build_certs_check(common_options(package.path(), true)).with_changed(),
        );
        assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
        assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
        assert!(result.diagnostics[0]
            .actual_value
            .as_deref()
            .unwrap()
            .contains("mode=changed,seeds=1,rebuild=1"));
        assert_eq!(result.diagnostics[1].reason_code, "source_hash_mismatch");
        assert_eq!(result.diagnostics[1].module.as_deref(), Some("Fixture.B"));
    }
}

#[test]
fn package_build_certs_selection_changed_refresh_plans_export_stable_rebind() {
    let package = build_synthetic_local_import_fixture("changed-refresh-rebind");
    init_git_package(&package, true);
    fs::write(
        package.artifact_path("Fixture/A/source.npa"),
        "theorem a_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => (fun (q : P) => q) p\n",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 3);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=1,rebuild=2"));
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_plan"
    );
    assert!(result.diagnostics[1]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("source_rebuild=1,certificate_rebind=1,unchanged=0"));
    assert_eq!(result.diagnostics[2].reason_code, "manifest_hashes_stale");
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_selection_changed_without_head_selects_all_local_modules() {
    let package = build_synthetic_local_import_fixture("changed-no-head");
    init_git_package(&package, false);
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=2,rebuild=2"));
}

#[test]
fn package_build_certs_selection_changed_without_head_includes_ignored_local_modules() {
    let package = build_synthetic_local_import_fixture("changed-no-head-ignored");
    let status = Command::new("/usr/bin/git")
        .args(["init", "-q"])
        .current_dir(package.path())
        .status()
        .unwrap();
    assert!(status.success());
    fs::write(package.artifact_path(".git/info/exclude"), "*\n").unwrap();

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=2,rebuild=2"));
}

#[test]
fn package_build_certs_selection_changed_rejects_non_git_package() {
    let package = build_synthetic_local_import_fixture("changed-non-git");

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "git_status_failed");
}

#[test]
fn package_build_certs_selection_changed_manifest_promotes_full_selection() {
    let package = build_synthetic_local_import_fixture("changed-manifest-full");
    init_git_package(&package, true);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let mut manifest = fs::read_to_string(&manifest_path).unwrap();
    manifest.push('\n');
    fs::write(manifest_path, manifest).unwrap();

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=2,rebuild=2"));
}

#[test]
fn package_build_certs_selection_changed_lock_only_is_empty_for_ordinary_check() {
    let package = build_synthetic_local_import_fixture("changed-lock-only");
    init_git_package(&package, true);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock = fs::read_to_string(&lock_path).unwrap();
    lock.push('\n');
    fs::write(lock_path, lock).unwrap();

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=0,rebuild=0"));
}

#[test]
fn package_build_certs_refresh_check_succeeds_and_writes_no_files() {
    let package = build_minimal_fixture("refresh-check-fresh");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_accepts_empty_modules_array() {
    let package = build_empty_modules_array_fixture("refresh-empty-modules-array");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_accepts_inline_module_array() {
    let package = build_inline_module_array_fixture("refresh-inline-module-array");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_rewrites_stale_source_hash_in_memory_without_writes() {
    let package = build_minimal_fixture("refresh-check-stale-source");
    replace_manifest_hash(
        &package,
        "expected_source_hash = \"",
        "expected_source_hash = \"",
        ZERO_HASH,
    );
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[0].reason_code, "manifest_hashes_stale");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_MANIFEST_PATH)
    );
    assert!(result.diagnostics[0].expected_hash.is_some());
    assert!(result.diagnostics[0].actual_hash.is_some());
    let json = result.render_json();
    assert!(json.contains("\"reason_code\":\"manifest_hashes_stale\""));
    assert!(json.contains("\"path\":\"npa-package.toml\""));
    assert!(json.contains("\"artifacts\":[]"));
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_rejects_checked_in_certificate_byte_drift() {
    let package = build_minimal_fixture("refresh-byte-drift");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    fs::write(
        &certificate_path,
        fs::read(repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"))
            .unwrap(),
    )
    .unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();

    let result = run_refresh_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::Build,
        "build_certificate_changed",
        Some("Proofs/Ai/Basic/certificate.npcert"),
        None,
    );
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_rejects_missing_package_lock() {
    let package = build_minimal_fixture("refresh-missing-lock");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    fs::remove_file(&lock_path).unwrap();

    let result = run_refresh_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::PackageLock,
        "package_lock_missing",
        Some(LOCK_PATH),
        None,
    );
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert!(!lock_path.exists());
}

#[test]
fn package_build_certs_check_refresh_rejects_missing_certificate_without_writes() {
    let package = build_minimal_fixture("refresh-missing-certificate");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let lock_path = package.artifact_path(LOCK_PATH);
    let manifest_before = fs::read_to_string(&manifest_path).unwrap();
    let lock_before = fs::read(&lock_path).unwrap();
    fs::remove_file(&certificate_path).unwrap();

    let result = run_refresh_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::ArtifactIo,
        "certificate_missing",
        Some("Proofs/Ai/Basic/certificate.npcert"),
        None,
    );
    assert_eq!(fs::read_to_string(manifest_path).unwrap(), manifest_before);
    assert!(!certificate_path.exists());
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_build_certs_refresh_check_rejects_protected_certificate_targets() {
    let package = build_minimal_fixture("refresh-check-target");
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let original_manifest = fs::read_to_string(&manifest_path).unwrap();
    let rewritten_manifest = original_manifest.replace(
        r#"certificate = "Proofs/Ai/Basic/certificate.npcert""#,
        r#"certificate = "npa-package.toml""#,
    );
    fs::write(&manifest_path, &rewritten_manifest).unwrap();
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let certificate_before = fs::read(&certificate_path).unwrap();

    let result = run_refresh_check(&package);

    assert_failure(
        &result,
        DiagnosticKind::ArtifactIo,
        "certificate_write_target_forbidden",
        Some("npa-package.toml"),
        Some("modules[0].certificate"),
    );
    assert_eq!(
        fs::read_to_string(manifest_path).unwrap(),
        rewritten_manifest
    );
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
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
        "{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
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
fn package_build_certs_check_rejects_stale_local_import_lock_identity() {
    let package = build_synthetic_local_import_fixture("stale-local-import");
    replace_module_manifest_hash(&package, "Fixture.A", "expected_export_hash", ZERO_HASH);

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "build-certs", "--root"])
        .arg(package.path())
        .arg("--check")
        .arg("--json")
        .env("NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS", "1")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("\"reason_code\":\"lock_import_export_hash_mismatch\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"path\":\"entries[1].imports[0].export_hash\""),
        "{stdout}"
    );
    assert!(stdout.contains("\"field\":\"export_hash\""), "{stdout}");
}

#[test]
fn package_build_certs_refresh_check_rebuilds_stale_local_direct_import_identity() {
    let package = build_synthetic_local_import_fixture("refresh-stale-local-import");
    replace_module_manifest_hash(&package, "Fixture.A", "expected_export_hash", ZERO_HASH);

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[0].reason_code, "manifest_hashes_stale");
}

#[test]
fn package_build_certs_refresh_check_reports_manifest_source_import_drift() {
    let package = build_synthetic_local_import_fixture("refresh-source-import-drift");
    fs::write(
        package.artifact_path("Fixture/B/source.npa"),
        "theorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n",
    )
    .unwrap();

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "manifest_source_imports_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some("Fixture.B"));
    assert_eq!(
        result.diagnostics[0].expected_value.as_deref(),
        Some("manifest=[Fixture.A]")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("source=[]")
    );
}

#[test]
fn package_build_certs_refresh_check_reports_import_drift_with_imported_notation() {
    let package = build_synthetic_imported_notation_drift_fixture(
        "refresh-source-import-drift-imported-notation",
    );

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "manifest_source_imports_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some("Fixture.B"));
    assert_eq!(
        result.diagnostics[0].expected_value.as_deref(),
        Some("manifest=[Fixture.A,Fixture.C]")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("source=[Fixture.A]")
    );
}

#[test]
fn package_build_certs_check_reports_manifest_source_import_drift_when_certificate_matches() {
    for targeted in [false, true] {
        let package = build_synthetic_imported_notation_drift_fixture(if targeted {
            "targeted-check-source-import-drift-matching-certificate"
        } else {
            "check-source-import-drift-matching-certificate"
        });
        let drifted_manifest_source =
            fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
        let checked_manifest_source = drifted_manifest_source.replace(
            "imports = [\"Fixture.A\", \"Fixture.C\"]",
            "imports = [\"Fixture.A\"]",
        );
        write_lock(&package, &checked_manifest_source);
        fs::write(
            package.artifact_path(PACKAGE_MANIFEST_PATH),
            drifted_manifest_source,
        )
        .unwrap();

        let result = if targeted {
            run_package_build_certs(
                build_certs_check(common_options(package.path(), true))
                    .with_modules(vec![Name::from_dotted("Fixture.B")]),
            )
        } else {
            run_build_check(&package)
        };

        assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
        let diagnostic_index = usize::from(targeted);
        assert_eq!(result.diagnostics.len(), diagnostic_index + 1);
        if targeted {
            assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
        }
        assert_eq!(
            result.diagnostics[diagnostic_index].reason_code, "manifest_source_imports_mismatch",
            "targeted={targeted}, diagnostics={:?}",
            result.diagnostics,
        );
        assert_eq!(
            result.diagnostics[diagnostic_index]
                .expected_value
                .as_deref(),
            Some("manifest=[Fixture.A,Fixture.C]")
        );
        assert_eq!(
            result.diagnostics[diagnostic_index].actual_value.as_deref(),
            Some("source=[Fixture.A]")
        );
    }
}

#[test]
fn package_build_certs_check_reports_existing_certificate_import_set_drift() {
    let package = build_synthetic_local_import_fixture("check-certificate-import-set-drift");
    let path = package.artifact_path("Fixture/B/certificate.npcert");
    let mut certificate = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
    certificate.imports.clear();
    fs::write(&path, npa_cert::encode_module_cert(&certificate).unwrap()).unwrap();

    let result = run_build_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "manifest_certificate_imports_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some("Fixture.B"));
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("certificate=[]")
    );
}

#[test]
fn package_build_certs_check_reports_existing_certificate_import_drift_with_imported_notation() {
    for targeted in [false, true] {
        let package = build_synthetic_imported_notation_drift_fixture(if targeted {
            "targeted-check-certificate-import-drift-imported-notation"
        } else {
            "check-certificate-import-drift-imported-notation"
        });
        let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
        let manifest_source = fs::read_to_string(&manifest_path).unwrap();
        let manifest_source = manifest_source.replace(
            "imports = [\"Fixture.A\", \"Fixture.C\"]",
            "imports = [\"Fixture.A\"]",
        );
        fs::write(&manifest_path, &manifest_source).unwrap();
        write_lock(&package, &manifest_source);

        let certificate_path = package.artifact_path("Fixture/B/certificate.npcert");
        let mut certificate =
            npa_cert::decode_module_cert(&fs::read(&certificate_path).unwrap()).unwrap();
        certificate.imports.clear();
        fs::write(
            certificate_path,
            npa_cert::encode_module_cert(&certificate).unwrap(),
        )
        .unwrap();

        let result = if targeted {
            run_package_build_certs(
                build_certs_check(common_options(package.path(), true))
                    .with_modules(vec![Name::from_dotted("Fixture.B")]),
            )
        } else {
            run_build_check(&package)
        };

        assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
        let diagnostic_index = usize::from(targeted);
        assert_eq!(result.diagnostics.len(), diagnostic_index + 1);
        if targeted {
            assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
        }
        assert_eq!(
            result.diagnostics[diagnostic_index].reason_code,
            "manifest_certificate_imports_mismatch",
            "targeted={targeted}, diagnostics={:?}",
            result.diagnostics,
        );
        assert_eq!(
            result.diagnostics[diagnostic_index].module.as_deref(),
            Some("Fixture.B")
        );
        assert_eq!(
            result.diagnostics[diagnostic_index].actual_value.as_deref(),
            Some("certificate=[]")
        );
    }
}

#[test]
fn package_build_certs_check_reports_existing_certificate_import_identity_drift() {
    let package = build_synthetic_local_import_fixture("check-certificate-import-identity-drift");
    let path = package.artifact_path("Fixture/B/certificate.npcert");
    let mut certificate = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
    certificate.imports[0].export_hash = [0; 32];
    fs::write(&path, npa_cert::encode_module_cert(&certificate).unwrap()).unwrap();

    let result = run_build_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "certificate_import_identity_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some("Fixture.B"));
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("export_hash"));
}

#[test]
fn package_build_certs_refresh_check_accepts_duplicate_local_imports() {
    let package = build_synthetic_duplicate_local_import_fixture("refresh-duplicate-local-import");

    let result = run_refresh_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

#[test]
fn package_build_certs_refresh_check_accepts_proofs_fixture_import_order() {
    let result = run_package_build_certs(refresh_artifacts_check(common_options(
        repo_root().join("testdata/package/proofs"),
        true,
    )));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

#[test]
fn package_build_certs_check_accepts_legacy_std_producer_profile_fixture() {
    let result = run_package_build_certs_check(common_options(
        repo_root().join("testdata/package/npa-std"),
        true,
    ));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

fn run_build_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check(common_options(package.path(), true))
}

fn run_build_check_read_through(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check_with_cache(
        common_options(package.path(), true),
        PackageBuildCheckCacheMode::ReadThrough,
    )
}

fn run_refresh_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(refresh_artifacts_check(common_options(
        package.path(),
        true,
    )))
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

fn install_frontend_failure(package: &TestPackage, source_path: &str, module_name: &str) {
    write_artifact(package, source_path, FRONTEND_FAILURE_SOURCE.as_bytes());
    let source_hash = format_package_hash(&package_file_hash(FRONTEND_FAILURE_SOURCE.as_bytes()));
    replace_module_manifest_hash(package, module_name, "expected_source_hash", &source_hash);
}

fn assert_frontend_failure(
    result: &CommandResult,
    module: &str,
    manifest_path: &str,
    source_path: &str,
) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.artifacts.is_empty());
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::Build);
    assert_eq!(diagnostic.reason_code, "build_failed");
    assert_eq!(diagnostic.module.as_deref(), Some(module));
    assert_eq!(diagnostic.path.as_deref(), Some(manifest_path));
    assert_eq!(diagnostic.field.as_deref(), Some("elaborator"));
    assert_eq!(
        diagnostic.actual_value.as_deref(),
        Some(FRONTEND_FAILURE_MESSAGE)
    );
    let source = diagnostic
        .source
        .as_ref()
        .expect("frontend failure should retain source context");
    let (start, end) = frontend_failure_binder_range();
    assert_eq!(source.path(), source_path);
    assert_eq!(source.start_byte(), start);
    assert_eq!(source.end_byte(), end);
    assert_eq!(
        FRONTEND_FAILURE_SOURCE.get(start as usize..end as usize),
        Some("product")
    );
    assert_eq!(source.declaration(), Some("product_enumeration_bad"));
}

fn frontend_failure_binder_range() -> (u32, u32) {
    let start = FRONTEND_FAILURE_SOURCE
        .find("fun product")
        .expect("failing binder") as u32
        + "fun ".len() as u32;
    (start, start + "product".len() as u32)
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

fn init_git_package(package: &TestPackage, commit: bool) {
    for args in [
        vec!["init", "-q"],
        vec!["config", "user.name", "NPA Test"],
        vec!["config", "user.email", "npa@example.invalid"],
        vec!["add", "--all"],
    ] {
        let status = Command::new("/usr/bin/git")
            .args(args)
            .current_dir(package.path())
            .status()
            .unwrap();
        assert!(status.success());
    }
    if commit {
        let status = Command::new("/usr/bin/git")
            .args(["commit", "-q", "-m", "fixture"])
            .current_dir(package.path())
            .status()
            .unwrap();
        assert!(status.success());
    }
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

fn build_inline_module_array_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source =
        "theorem basic_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let (cert, _verified, _interface) =
        compile_fixture_module(0, "Proofs.Ai.Basic", source, &[], &[]);
    let source_path = "Proofs/Ai/Basic/source.npa";
    let cert_path = "Proofs/Ai/Basic/certificate.npcert";
    write_artifact(&package, source_path, source.as_bytes());
    write_artifact(&package, cert_path, &cert);

    let manifest_source = inline_fixture_manifest(&generated_manifest_module(
        "Proofs.Ai.Basic",
        source_path,
        cert_path,
        source.as_bytes(),
        &cert,
        Vec::new(),
    ));
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

fn build_synthetic_external_import_chain_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let base_source =
        "theorem base_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let leaf_source = "import Fixture.External.Base\nimport Fixture.External.Base\n\ntheorem leaf_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @base_id P p\n";
    let unrelated_source =
        "theorem unrelated_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let local_source = "import Fixture.External.Leaf\n\ntheorem local_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @leaf_use P p\n";

    let (base_cert, base_verified, base_interface) =
        compile_fixture_module(0, "Fixture.External.Base", base_source, &[], &[]);
    let (leaf_cert, leaf_verified, leaf_interface) = compile_fixture_module(
        1,
        "Fixture.External.Leaf",
        leaf_source,
        &[base_verified.clone(), base_verified],
        &[base_interface.clone(), base_interface],
    );
    let (unrelated_cert, _unrelated_verified, _unrelated_interface) =
        compile_fixture_module(2, "Fixture.External.Unrelated", unrelated_source, &[], &[]);
    let (local_cert, _local_verified, _local_interface) = compile_fixture_module(
        3,
        "Fixture.Local",
        local_source,
        std::slice::from_ref(&leaf_verified),
        std::slice::from_ref(&leaf_interface),
    );

    let base_cert_path = "vendor/fixture-external/Fixture/External/Base/certificate.npcert";
    let leaf_cert_path = "vendor/fixture-external/Fixture/External/Leaf/certificate.npcert";
    let unrelated_cert_path =
        "vendor/fixture-external/Fixture/External/Unrelated/certificate.npcert";
    let local_source_path = "Fixture/Local/source.npa";
    let local_cert_path = "Fixture/Local/certificate.npcert";
    write_artifact(&package, base_cert_path, &base_cert);
    write_artifact(&package, leaf_cert_path, &leaf_cert);
    write_artifact(&package, unrelated_cert_path, &unrelated_cert);
    write_artifact(&package, local_source_path, local_source.as_bytes());
    write_artifact(&package, local_cert_path, &local_cert);

    let imports = vec![
        generated_manifest_import("Fixture.External.Leaf", leaf_cert_path, &leaf_cert),
        generated_manifest_import(
            "Fixture.External.Unrelated",
            unrelated_cert_path,
            &unrelated_cert,
        ),
        generated_manifest_import("Fixture.External.Base", base_cert_path, &base_cert),
    ];
    let module = generated_manifest_module(
        "Fixture.Local",
        local_source_path,
        local_cert_path,
        local_source.as_bytes(),
        &local_cert,
        vec![Name::from_dotted("Fixture.External.Leaf")],
    );
    let manifest_source = fixture_manifest_with_imports(&imports, &[module]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    package
}

fn install_external_import_cycle(package: &TestPackage) {
    let base_path =
        package.artifact_path("vendor/fixture-external/Fixture/External/Base/certificate.npcert");
    let leaf_path =
        package.artifact_path("vendor/fixture-external/Fixture/External/Leaf/certificate.npcert");
    let mut base = npa_cert::decode_module_cert(&fs::read(&base_path).unwrap()).unwrap();
    let leaf = npa_cert::decode_module_cert(&fs::read(leaf_path).unwrap()).unwrap();
    base.imports.push(npa_cert::ImportEntry {
        module: leaf.header.module,
        export_hash: leaf.hashes.export_hash,
        certificate_hash: Some(leaf.hashes.certificate_hash),
    });
    fs::write(base_path, npa_cert::encode_module_cert(&base).unwrap()).unwrap();
}

fn install_changed_external_leaf_certificate(package: &TestPackage) {
    let base_path =
        package.artifact_path("vendor/fixture-external/Fixture/External/Base/certificate.npcert");
    let base_bytes = fs::read(base_path).unwrap();
    let mut session = npa_cert::VerifierSession::new();
    let base_verified =
        npa_cert::verify_module_cert(&base_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    let base_interface = HumanImportedSourceInterface {
        module: base_verified.module().clone(),
        export_hash: base_verified.export_hash(),
        certificate_hash: Some(base_verified.certificate_hash()),
        source_interface: npa_frontend::HumanSourceInterface::new(base_verified.module().clone()),
    };
    let changed_source = "import Fixture.External.Base\n\ntheorem leaf_changed :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let (changed, _verified, _interface) = compile_fixture_module(
        4,
        "Fixture.External.Leaf",
        changed_source,
        std::slice::from_ref(&base_verified),
        std::slice::from_ref(&base_interface),
    );
    fs::write(
        package.artifact_path("vendor/fixture-external/Fixture/External/Leaf/certificate.npcert"),
        changed,
    )
    .unwrap();
}

fn build_synthetic_imported_notation_drift_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a = "def choose (P : Prop) (p : P) : P := p\ninfixl:65 \" <+> \" => choose\n";
    let source_c =
        "theorem c_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let source_b = "import Fixture.A\n\ntheorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => P <+> p\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_c, _verified_c, _interface_c) =
        compile_fixture_module(1, "Fixture.C", source_c, &[], &[]);
    let (cert_b, _verified_b, _interface_b) = compile_fixture_module(
        2,
        "Fixture.B",
        source_b,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );

    let a_source_path = "Fixture/A/source.npa";
    let a_cert_path = "Fixture/A/certificate.npcert";
    let b_source_path = "Fixture/B/source.npa";
    let b_cert_path = "Fixture/B/certificate.npcert";
    let c_source_path = "Fixture/C/source.npa";
    let c_cert_path = "Fixture/C/certificate.npcert";
    write_artifact(&package, a_source_path, source_a.as_bytes());
    write_artifact(&package, a_cert_path, &cert_a);
    write_artifact(&package, b_source_path, source_b.as_bytes());
    write_artifact(&package, b_cert_path, &cert_b);
    write_artifact(&package, c_source_path, source_c.as_bytes());
    write_artifact(&package, c_cert_path, &cert_c);

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
        vec![
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.C"),
        ],
    );
    let module_c = generated_manifest_module(
        "Fixture.C",
        c_source_path,
        c_cert_path,
        source_c.as_bytes(),
        &cert_c,
        Vec::new(),
    );
    let manifest_source = fixture_manifest(&[module_b, module_a, module_c]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        manifest_source,
    )
    .unwrap();
    package
}

fn build_synthetic_duplicate_local_import_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a =
        "theorem a_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let source_b = "import Fixture.A\nimport Fixture.A\n\ntheorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let verified_imports = vec![verified_a.clone(), verified_a];
    let interface_imports = vec![interface_a.clone(), interface_a];
    let (cert_b, _verified_b, _interface_b) = compile_fixture_module(
        1,
        "Fixture.B",
        source_b,
        &verified_imports,
        &interface_imports,
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
        vec![
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.A"),
        ],
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

fn build_empty_modules_array_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let manifest_source = String::from(
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = []

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
    );
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

fn generated_manifest_import(
    module: &str,
    certificate: &str,
    certificate_bytes: &[u8],
) -> ManifestImport {
    let cert = npa_cert::decode_module_cert(certificate_bytes).unwrap();
    ManifestImport {
        module: Name::from_dotted(module),
        package: "fixture-external".to_owned(),
        version: "0.1.0".to_owned(),
        certificate: certificate.to_owned(),
        export_hash: PackageHash::from(cert.hashes.export_hash),
        certificate_hash: PackageHash::from(cert.hashes.certificate_hash),
    }
}

fn fixture_manifest(modules: &[ManifestModule]) -> String {
    fixture_manifest_with_imports(&[], modules)
}

fn fixture_manifest_with_imports(imports: &[ManifestImport], modules: &[ManifestModule]) -> String {
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
            import.package,
            import.version,
            import.certificate,
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

fn inline_fixture_manifest(module: &ManifestModule) -> String {
    format!(
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = [{{ module = "{}", source = "{}", certificate = "{}", imports = {}, expected_source_hash = "{}", expected_certificate_file_hash = "{}", expected_export_hash = "{}", expected_axiom_report_hash = "{}", expected_certificate_hash = "{}" }}]

[policy]
allow_custom_axioms = false
allowed_axioms = []
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
    )
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

fn replace_external_manifest_hash(
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
    let mut in_import = false;
    let mut in_target_import = false;
    let mut replaced = false;
    for line in source.lines() {
        if line == "[[imports]]" {
            in_import = true;
            in_target_import = false;
        } else if line.starts_with("[[") {
            in_import = false;
            in_target_import = false;
        } else if in_import && line == module_line {
            in_target_import = true;
        }
        if in_target_import && line.starts_with(&field_prefix) {
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
    assert!(
        replaced,
        "expected to replace {field} for external import {module_name}"
    );
    fs::write(path, output).unwrap();
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use npa_api::{
    clear_package_import_context_export_disk_cache, clear_package_verification_decode_cache,
    clear_package_verification_process_memo, format_hash_string, independent_checker_file_hash,
    parse_independent_checker_runner_policy,
};
use npa_cert::Name;
use npa_cli::args::{
    PackageAuditCacheMode, PackageChecker, PackageCommonOptions, PackageExternalCheckerOptions,
    PackageTimingMode, PackageVerifierMemoMode, PackageVerifyCertsOptions,
};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind, DiagnosticSeverity};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_verify::run_package_verify_certs;
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_audit_disk_memo_key,
    package_audit_disk_memo_result_entry_json, package_file_hash, parse_and_validate_manifest_str,
    parse_package_audit_disk_memo_result_entry_json, parse_package_audit_result_entry_json,
    parse_package_lock_json, PackageExternalImport, PackageHash, PackageModule, PackagePath,
    PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR,
};

const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
    cleanup_path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-verify-certs-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self {
            path: path.clone(),
            cleanup_path: path,
        }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn cleanup_path(&self) -> &Path {
        &self.cleanup_path
    }

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.cleanup_path);
    }
}

#[derive(Clone)]
struct ManifestModule {
    module: Name,
    source: String,
    certificate: String,
    meta: Option<String>,
    replay: Option<String>,
    imports: Vec<Name>,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[test]
fn package_verify_certs_reference_succeeds_without_source_replay_or_meta() {
    let package = build_source_free_fixture(
        "reference-source-free",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/replay.json")
        .exists());
    assert!(!package.artifact_path("Proofs/Ai/Basic/meta.json").exists());

    let result = run_verify(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 2);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::ReferenceVerifier,
        "package_verified",
        Some("npa-checker-ref"),
    );
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("reference_checker_verdict=true"));
    assert_info(
        &result.diagnostics[1],
        DiagnosticKind::ReferenceVerifier,
        "module_verified",
        Some("npa-checker-ref"),
    );
    assert_eq!(
        result.diagnostics[1].module.as_deref(),
        Some("Proofs.Ai.Basic")
    );
    assert_eq!(
        result.diagnostics[1].path.as_deref(),
        Some("Proofs/Ai/Basic/certificate.npcert")
    );
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_verify_certs_fast_succeeds_and_is_labeled_fast_kernel() {
    let package =
        build_source_free_fixture("fast-source-free", "Proofs.Ai.Basic", false, &["Eq.rec"]);

    let result = run_verify(&package, PackageChecker::Fast);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 2);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::FastVerifier,
        "package_verified",
        Some("fast-kernel-certificate-verifier"),
    );
    let aggregate = result.diagnostics[0].actual_value.as_deref().unwrap();
    assert!(aggregate.contains("mode=fast-kernel"));
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.checker.as_deref() != Some("npa-checker-ref")));
}

#[test]
fn package_verify_certs_changed_verifies_changed_certificate_path_source_free() {
    let package = build_source_free_modules_fixture(
        "changed-certificate-source-free",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/EqReasoning/source.npa")
        .exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Analysis/AbstractMetricTopology/source.npa")
        .exists());
    init_git_baseline(&package);
    stage_worktree_mode_changed(&package, "Proofs/Ai/EqReasoning/certificate.npcert");

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let verified_modules = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| diagnostic.module.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verified_modules,
        vec!["Std.Logic.Eq", "Proofs.Ai.EqReasoning"]
    );
}

#[test]
fn package_verify_certs_changed_ignores_staged_certificate_when_worktree_restored_source_free() {
    let package = build_source_free_modules_fixture(
        "changed-certificate-index-only-source-free",
        &["Proofs.Ai.Basic", "Proofs.Ai.EqReasoning"],
        &["Eq.rec"],
    );
    init_git_baseline(&package);
    stage_changed_then_restore(
        &package,
        "Proofs/Ai/EqReasoning/certificate.npcert",
        b"\nchanged-index-bytes",
    );

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "module_verified"));
    let aggregate = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("modules=0"));
}

#[test]
fn package_verify_certs_changed_verifies_nested_package_certificate_path_source_free() {
    let mut package = build_source_free_modules_fixture(
        "changed-certificate-nested-source-free",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    nest_package_in_worktree(&mut package, "packages/proofs space");
    init_git_worktree_baseline(&package);
    mark_worktree_mode_changed(&package, "Proofs/Ai/EqReasoning/certificate.npcert");

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let verified_modules = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| diagnostic.module.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verified_modules,
        vec!["Std.Logic.Eq", "Proofs.Ai.EqReasoning"]
    );
}

#[test]
fn package_verify_certs_fast_cli_succeeds_json() {
    let package = build_source_free_fixture("cli-fast", "Proofs.Ai.Basic", false, &["Eq.rec"]);

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--root"])
        .arg(package.path())
        .args(["--checker", "fast", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"command\":\"package verify-certs\""));
    assert!(stdout.contains("\"status\":\"passed\""));
    assert!(stdout.contains("\"kind\":\"FastVerifier\""));
    assert!(stdout.contains("\"reason_code\":\"package_verified\""));
    assert!(stdout.contains("\"checker\":\"fast-kernel-certificate-verifier\""));
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));
}

#[test]
fn package_verify_external_succeeds_with_explicit_policy_registry_imports_and_no_source() {
    let package =
        build_source_free_fixture("external-source-free", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    assert!(!package.artifact_path("Proofs/Ai/Eq/source.npa").exists());
    assert!(package
        .artifact_path("vendor/npa-std/Std/Logic/Eq/certificate.npcert")
        .exists());
    let external = write_external_runner_fixture(&package, true);

    let result = run_verify_external(&package, external);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.artifacts.len(), 3);
    assert!(result
        .artifacts
        .iter()
        .all(|artifact| artifact.kind == "machine_check_result"));
    assert!(result.artifacts.iter().any(|artifact| artifact.path
        == "generated/checker-results/fixture-package/0.1.0/Proofs.Ai.Eq/external/result.json"));
    assert!(result.artifacts.iter().any(|artifact| artifact.path
        == "generated/checker-results/fixture-package/0.1.0/Std.Logic.Eq/external/result.json"));
    assert!(
        package
            .artifact_path(
                "generated/checker-imports/fixture-package/0.1.0/Proofs.Ai.Eq/external/vendor/npa-std/Std/Logic/Eq/certificate.npcert"
            )
            .exists()
    );
    assert!(result
        .artifacts
        .iter()
        .all(|artifact| package.artifact_path(&artifact.path).exists()));
    assert_eq!(result.diagnostics.len(), 4);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::ExternalVerifier,
        "package_verified",
        Some("npa-checker-ext"),
    );
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=external"));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.reason_code == "module_verified")
            .count(),
        3
    );
    let local_result = result
        .artifacts
        .iter()
        .find(|artifact| artifact.path.contains("Proofs.Ai.Eq"))
        .unwrap();
    let result_json = fs::read_to_string(package.artifact_path(&local_result.path)).unwrap();
    assert!(result_json.contains("\"schema\":\"npa.independent-checker.machine_check_result.v1\""));
    assert!(result_json.contains("\"profile\":\"external\""));
    assert!(result_json.contains("\"status\":\"checked\""));
    assert!(!result
        .render_json()
        .contains(&package.path().to_string_lossy().to_string()));
}

#[test]
fn package_verify_external_rejects_missing_checker_binary_with_structured_diagnostic() {
    let package = build_source_free_fixture(
        "external-missing-binary",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let external = write_external_runner_fixture(&package, false);

    let result = run_verify_external(&package, external);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::ArtifactIo);
    assert_eq!(diagnostic.reason_code, "checker_binary_file_unreadable");
    assert_eq!(
        diagnostic.path.as_deref(),
        Some("tools/checkers/npa-checker-ext")
    );
    assert!(diagnostic.checker.is_none());
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_verify_external_requires_explicit_policy_and_registry() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--checker", "external", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"command\":\"package verify-certs\""));
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"missing_required_flag\""));
    assert!(stdout.contains("\"field\":\"--runner-policy\""));
}

#[test]
fn package_verify_certs_rejects_stale_package_lock_before_checker_status() {
    let package = build_source_free_fixture("stale-lock", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();

    let result = run_verify(&package, PackageChecker::Reference);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "package_lock_stale",
        Some(LOCK_PATH),
        None,
    );
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));
}

#[test]
fn package_verify_certs_rejects_stale_certificate_hash_before_checker_status() {
    let package =
        build_source_free_fixture("stale-certificate", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        fs::read(repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"))
            .unwrap(),
    )
    .unwrap();

    let result = run_verify(&package, PackageChecker::Reference);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "certificate_file_hash_mismatch",
        Some("modules[0].expected_certificate_file_hash"),
        Some("expected_certificate_file_hash"),
    );
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));
}

#[test]
fn package_verify_certs_reference_preserves_checker_rejection_diagnostic() {
    let package =
        build_source_free_fixture("reference-rejection", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.kind == DiagnosticKind::ReferenceVerifier)
        .expect("reference checker rejection is reported");
    assert_eq!(diagnostic.kind, DiagnosticKind::ReferenceVerifier);
    assert_eq!(diagnostic.reason_code, "reference_checker_rejected");
    assert_eq!(diagnostic.checker.as_deref(), Some("npa-checker-ref"));
    assert_eq!(diagnostic.field.as_deref(), Some("certificate"));
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Eq"));
    let actual = diagnostic.actual_value.as_deref().unwrap();
    assert!(actual.contains("NonCanonical"), "{actual}");
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));
}

#[test]
fn package_verify_certs_audit_cache_read_through_writes_then_hits() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "audit-cache-read-through",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Audit.Cache.Unique"],
    );

    let first = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = audit_cache_summary(&first);
    assert!(first_summary.contains("mode=read-through"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert_eq!(audit_cache_entries().len(), 1);
    let entry_source = fs::read_to_string(&audit_cache_entries()[0]).unwrap();
    let entry = parse_package_audit_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);

    let second = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = audit_cache_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("cached=1"));
}

#[test]
fn package_verify_certs_audit_cache_read_through_preserves_live_checker_failure() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package =
        build_source_free_fixture("audit-cache-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
    let summary = audit_cache_summary(&result);
    assert!(summary.contains("mode=read-through"));
    assert!(summary.contains("trusted=false"));
    assert!(!result
        .render_json()
        .contains("\"reason_code\":\"package_verified\""));
}

#[test]
fn package_verify_certs_audit_cache_external_read_through_is_rejected() {
    let _guard = audit_cache_test_lock();
    let package = build_source_free_fixture(
        "audit-cache-external",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::External,
        changed: false,
        audit_cache: PackageAuditCacheMode::ReadThrough,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: Some(external),
        timings: PackageTimingMode::Off,
    });

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--audit-cache")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("read-through")
    );
}

#[test]
fn package_verify_certs_local_hit_marks_proof_evidence_false_and_follow_up() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "local-hit-proof-evidence",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let warm = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);

    let local = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(local.exit_code(), CommandExitCode::Success);
    let aggregate = local
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert!(aggregate.contains("locally_accelerated=true"));
    let module = local
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=local-audit-cache;proof_evidence=false")
    );
    let summary = audit_cache_summary(&local);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("hits=1"));
    assert!(summary.contains("cached=1"));
    assert!(summary.contains("live_checked=0"));
    let follow_up = audit_cache_follow_up(&local);
    assert!(follow_up.contains("proof_evidence=false"));
    assert!(follow_up.contains("--audit-cache off"));
    assert!(follow_up.contains("--checker reference"));
}

#[test]
fn package_verify_certs_local_hit_does_not_mask_live_miss_failure() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package =
        build_source_free_fixture("local-hit-miss-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
    let summary = audit_cache_summary(&result);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("trusted=false"));
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "audit_cache_follow_up"));
    assert!(!result
        .render_json()
        .contains("\"reason_code\":\"package_verified\""));
}

#[test]
fn package_verify_certs_local_hit_live_checks_cached_dependency_needed_by_live_dependent() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "local-hit-live-dependency",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    let warm = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    remove_audit_cache_entries_for_module("Proofs.Ai.Eq");

    let local = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(local.exit_code(), CommandExitCode::Success);
    let summary = audit_cache_summary(&local);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("cached=0"));
    assert!(!summary.contains("live_checked=0"));
    assert!(local.diagnostics.iter().all(|diagnostic| {
        diagnostic.actual_value.as_deref()
            != Some("status=passed;evidence=local-audit-cache;proof_evidence=false")
    }));
    assert!(local
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "audit_cache_follow_up"));
}

#[test]
fn package_verify_certs_local_hit_external_is_rejected() {
    let _guard = audit_cache_test_lock();
    let package =
        build_source_free_fixture("local-hit-external", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::External,
        changed: false,
        audit_cache: PackageAuditCacheMode::LocalHit,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: Some(external),
        timings: PackageTimingMode::Off,
    });

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--audit-cache")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("local-hit")
    );
}

#[test]
fn package_verify_certs_local_hit_does_not_run_from_package_gate_scripts() {
    let Some(package_gate_path) = corpus_script_path("check-corpus-package.sh") else {
        return;
    };
    let Some(full_gate_path) = corpus_script_path("check-corpus-full.sh") else {
        return;
    };
    let package_gate = fs::read_to_string(package_gate_path).expect("package gate script");
    let full_gate = fs::read_to_string(full_gate_path).expect("full gate script");

    assert!(!package_gate.contains("--audit-cache"));
    assert!(!full_gate.contains("--audit-cache"));
    assert!(!package_gate.contains("--verifier-memo"));
    assert!(!full_gate.contains("--verifier-memo"));
    assert!(full_gate.contains("scripts/check-corpus-package.sh"));
}

#[test]
fn package_verify_certs_disk_memo_writes_hits_and_delete_reruns_live() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "disk-memo-hit",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "DiskMemo.Unique"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);

    let first = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = disk_memo_summary(&first);
    assert!(first_summary.contains("mode=disk"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));
    assert_eq!(disk_memo_entries().len(), 1);
    let entry_source = fs::read_to_string(&disk_memo_entries()[0]).unwrap();
    let entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);
    assert!(!entry.proof_evidence);
    assert_eq!(
        without_disk_memo_summary_and_timings(first.clone()),
        off.clone()
    );

    let second = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = disk_memo_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("live_checked=0"));
    assert!(second_summary.contains("cached=1"));
    let aggregate = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert!(aggregate.contains("locally_accelerated=true"));
    let module = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=disk-verifier-memo;proof_evidence=false")
    );

    clear_disk_memo();
    let rerun = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(rerun.exit_code(), CommandExitCode::Success);
    let rerun_summary = disk_memo_summary(&rerun);
    assert!(rerun_summary.contains("hits=0"));
    assert!(rerun_summary.contains("misses=1"));
    assert!(rerun_summary.contains("live_checked=1"));
    assert_eq!(without_disk_memo_summary_and_timings(rerun), off);
}

#[test]
fn package_verify_certs_cache_aware_disk_memo_live_checks_dirty_reverse_dependents() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_modules_fixture(
        "cache-aware-dag",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec", "CacheAware.Unique"],
    );
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    remove_disk_memo_entries_for_module("Proofs.Ai.EqReasoning");

    let cached = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(cached.exit_code(), CommandExitCode::Success);
    let summary = disk_memo_summary(&cached);
    assert!(summary.contains("mode=disk"));
    assert!(summary.contains("invalidated="), "{summary}");
    assert!(!summary.contains("invalidated=0"), "{summary}");
    assert!(summary.contains("cached=1"), "{summary}");
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.Basic"),
        "status=passed;evidence=disk-verifier-memo;proof_evidence=false"
    );
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.EqReasoning"),
        "status=passed;evidence=live-checker;proof_evidence=true"
    );
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.Analysis.AbstractMetricTopology"),
        "status=passed;evidence=live-checker;proof_evidence=true"
    );
}

#[test]
fn package_verify_certs_persistent_cache_read_through_writes_hits_and_delete_reruns_live() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "persistent-cache-read-through",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "PersistentCache.Unique"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);

    let first = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = disk_memo_summary(&first);
    assert!(first_summary.contains("mode=read-through"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));
    assert_eq!(disk_memo_entries().len(), 1);
    let entry_source = fs::read_to_string(&disk_memo_entries()[0]).unwrap();
    let entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);
    assert!(!entry.proof_evidence);
    assert_eq!(
        without_disk_memo_summary_and_timings(first.clone()),
        off.clone()
    );

    let second = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = disk_memo_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("live_checked=1"));
    assert!(second_summary.contains("cached=0"));
    let module = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=live-checker;proof_evidence=true")
    );
    assert_eq!(
        without_disk_memo_summary_and_timings(second.clone()),
        off.clone()
    );

    clear_disk_memo();
    let rerun = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(rerun.exit_code(), CommandExitCode::Success);
    let rerun_summary = disk_memo_summary(&rerun);
    assert!(rerun_summary.contains("hits=0"));
    assert!(rerun_summary.contains("misses=1"));
    assert!(rerun_summary.contains("live_checked=1"));
    assert_eq!(without_disk_memo_summary_and_timings(rerun), off);
}

#[test]
fn package_verify_certs_persistent_cache_read_through_live_dominates_stale_identity() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture(
        "persistent-cache-stale-identity",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "PersistentCache.Stale"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert!(disk_memo_summary(&warm).contains("written=1"));

    let entry_path = disk_memo_entries()[0].clone();
    let entry_source = fs::read_to_string(&entry_path).unwrap();
    let mut entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    entry.key_input.package_lock_schema = "npa.package.lock.changed".to_owned();
    entry.cache_key = package_audit_disk_memo_key(&entry.key_input);
    fs::write(
        &entry_path,
        package_audit_disk_memo_result_entry_json(&entry),
    )
    .unwrap();

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("hits=0"));
    assert!(summary.contains("stale=1"));
    assert!(summary.contains("written=1"));
    assert!(summary.contains("live_checked=1"));
    assert!(summary.contains("cached=0"));
    assert_eq!(without_disk_memo_summary_and_timings(result), off);
}

#[test]
fn package_verify_certs_persistent_cache_read_through_does_not_mask_stale_certificate() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture(
        "persistent-cache-stale-certificate",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert!(disk_memo_summary(&warm).contains("written=3"));

    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("hits=0"));
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("proof_evidence=false"));
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
}

#[test]
fn package_verify_certs_disk_memo_stale_certificate_misses() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture("disk-memo-stale", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    let warm_summary = disk_memo_summary(&warm);
    assert!(warm_summary.contains("written=3"), "{warm_summary}");

    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("misses=3"));
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
}

#[test]
fn package_verify_certs_disk_memo_external_is_rejected() {
    let _guard = disk_memo_test_lock();
    let package =
        build_source_free_fixture("disk-memo-external", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::External,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Disk,
        jobs: 1,
        external: Some(external),
        timings: PackageTimingMode::Off,
    });

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--verifier-memo")
    );
    assert_eq!(result.diagnostics[0].actual_value.as_deref(), Some("disk"));
}

#[test]
fn package_verify_certs_jobs_one_matches_existing_order() {
    let package =
        build_source_free_fixture("jobs-one-order", "Proofs.Ai.Basic", false, &["Eq.rec"]);

    let default_result = run_verify(&package, PackageChecker::Fast);
    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);

    assert_eq!(jobs_one_result.exit_code(), CommandExitCode::Success);
    assert_eq!(jobs_one_result.render_json(), default_result.render_json());
}

#[test]
fn package_verify_certs_shards_jobs_four_matches_jobs_one_normalized() {
    let package = build_source_free_fixture(
        "shards-jobs-four-normalized",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);
    let jobs_four_result = run_verify_with_jobs(&package, PackageChecker::Fast, 4);

    assert_eq!(jobs_four_result.exit_code(), CommandExitCode::Success);
    assert_eq!(
        jobs_four_result.render_json(),
        jobs_one_result.render_json()
    );
}

#[test]
fn package_verify_certs_shards_failure_matches_jobs_one_and_preserves_diagnostic() {
    let package = build_source_free_fixture("shards-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);
    let jobs_four_result = run_verify_with_jobs(&package, PackageChecker::Fast, 4);

    assert_eq!(
        jobs_four_result.exit_code(),
        CommandExitCode::PackageFailure
    );
    assert_eq!(
        jobs_four_result.render_json(),
        jobs_one_result.render_json()
    );
    let diagnostic = jobs_four_result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.kind == DiagnosticKind::FastVerifier)
        .expect("fast verifier diagnostic is preserved");
    assert_eq!(diagnostic.reason_code, "kernel_verification_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Eq"));
    let actual = diagnostic.actual_value.as_deref().unwrap();
    assert!(actual.contains("NonCanonical"), "{actual}");
}

#[test]
fn package_verify_certs_jobs_reference_parallel_is_rejected() {
    let package = build_source_free_fixture(
        "jobs-reference-rejected",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let result = run_verify_with_jobs(&package, PackageChecker::Reference, 4);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageLock);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "unsupported_parallel_checker"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("execution.jobs")
    );
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("jobs"));
}

#[test]
fn package_verify_certs_jobs_audit_cache_parallel_is_rejected() {
    let package = build_source_free_fixture(
        "jobs-audit-cache-rejected",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let result = run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::Fast,
        changed: false,
        audit_cache: PackageAuditCacheMode::ReadThrough,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 4,
        external: None,
        timings: PackageTimingMode::Off,
    });

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("--jobs"));
}

#[test]
fn package_verify_certs_memo_counters_are_timing_opt_in_and_normalized() {
    let _guard = process_memo_test_lock();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "process-memo-timing",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "ProcessMemo.Unique"],
    );

    let off = run_verify(&package, PackageChecker::Fast);
    clear_package_verification_process_memo();
    let first = run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);
    let second =
        run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("process_memo_summary"));
    assert!(off.timings.is_none());

    let first_summary = process_memo_summary(&first);
    assert!(first_summary.contains("mode=process-local"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("inserted=1"));
    assert!(first_summary.contains("trusted=false"));

    let second_summary = process_memo_summary(&second);
    assert!(second_summary.contains("hits="));
    assert!(!second_summary.contains("hits=0"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("inserted=0"));

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

#[test]
fn package_verify_certs_decode_cache_counters_are_timing_opt_in_and_normalized() {
    let _guard = decode_cache_test_lock();
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let package = build_source_free_fixture(
        "decode-cache-timing",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "DecodeCache.Unique"],
    );

    let off = run_verify(&package, PackageChecker::Fast);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("decode_cache_summary"));
    assert!(off.timings.is_none());

    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let first = run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);
    clear_package_verification_process_memo();
    let second =
        run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);

    let first_summary = decode_cache_summary(&first);
    assert!(first_summary.contains("mode=process-local"));
    assert!(first_summary.contains("certificate_hits="));
    assert!(first_summary.contains("certificate_misses="));
    assert!(first_summary.contains("certificate_inserted="));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));

    let second_summary = decode_cache_summary(&second);
    assert!(second_summary.contains("certificate_hits="));
    assert!(!second_summary.contains("certificate_hits=0"));
    assert!(second_summary.contains("certificate_misses=0"));
    assert!(second_summary.contains("certificate_inserted=0"));

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

#[test]
fn package_verify_certs_import_context_cache_hits_are_timing_opt_in_and_normalized() {
    let _guard = decode_cache_test_lock();
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    let package = build_source_free_fixture(
        "import-context-export-cache",
        "Proofs.Ai.Basic",
        true,
        &["Eq.rec", "ImportContextCache.Unique"],
    );

    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("decode_cache_summary"));
    assert!(off.timings.is_none());

    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let first = run_verify_with_timings(
        &package,
        PackageChecker::Reference,
        PackageTimingMode::Summary,
    );
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let second = run_verify_with_timings(
        &package,
        PackageChecker::Reference,
        PackageTimingMode::Summary,
    );

    let first_summary = decode_cache_summary(&first);
    assert!(first_summary.contains("mode=process-local"));
    assert!(first_summary.contains("import_context_disk_hits=0"));
    assert!(first_summary.contains("import_context_disk_misses="));
    assert!(!first_summary.contains("import_context_disk_misses=0"));
    assert!(first_summary.contains("import_context_disk_inserted="));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));

    let second_summary = decode_cache_summary(&second);
    assert!(second_summary.contains("import_context_disk_hits="));
    assert!(!second_summary.contains("import_context_disk_hits=0"));
    assert!(second_summary.contains("import_context_disk_misses=0"));
    assert!(second_summary.contains("import_context_disk_stale=0"));
    assert!(second_summary.contains("import_context_disk_schema_misses=0"));
    assert!(second_summary.contains("import_context_disk_inserted=0"));

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

fn run_verify(
    package: &TestPackage,
    checker: PackageChecker,
) -> npa_cli::diagnostic::CommandResult {
    run_verify_with_audit_cache(package, checker, PackageAuditCacheMode::Off)
}

fn run_verify_changed(
    package: &TestPackage,
    checker: PackageChecker,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker,
        changed: true,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: None,
        timings: PackageTimingMode::Off,
    })
}

fn init_git_baseline(package: &TestPackage) {
    run_git_at(package.path(), &["init"]);
    run_git_at(package.path(), &["add", "."]);
    run_git_at(
        package.path(),
        &[
            "-c",
            "user.name=NPA Test",
            "-c",
            "user.email=npa-test@example.invalid",
            "commit",
            "-m",
            "baseline",
        ],
    );
}

fn init_git_worktree_baseline(package: &TestPackage) {
    run_git_at(package.cleanup_path(), &["init"]);
    run_git_at(package.cleanup_path(), &["add", "."]);
    run_git_at(
        package.cleanup_path(),
        &[
            "-c",
            "user.name=NPA Test",
            "-c",
            "user.email=npa-test@example.invalid",
            "commit",
            "-m",
            "baseline",
        ],
    );
}

fn nest_package_in_worktree(package: &mut TestPackage, relative_path: &str) {
    let original_package_root = package.path.clone();
    let worktree_root = original_package_root.with_file_name(format!(
        "{}-worktree",
        original_package_root.file_name().unwrap().to_string_lossy()
    ));
    if worktree_root.exists() {
        fs::remove_dir_all(&worktree_root).unwrap();
    }
    let nested_package_root = worktree_root.join(relative_path);
    fs::create_dir_all(nested_package_root.parent().unwrap()).unwrap();
    fs::rename(&original_package_root, &nested_package_root).unwrap();
    package.path = nested_package_root;
    package.cleanup_path = worktree_root;
}

fn stage_changed_then_restore(package: &TestPackage, relative_path: &str, suffix: &[u8]) {
    let path = package.artifact_path(relative_path);
    let original = fs::read(&path).unwrap();
    let mut staged = original.clone();
    staged.extend_from_slice(suffix);
    fs::write(&path, staged).unwrap();
    run_git(package, &["add", relative_path]);
    fs::write(&path, original).unwrap();
}

fn mark_worktree_mode_changed(package: &TestPackage, relative_path: &str) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let path = package.artifact_path(relative_path);
        let mut permissions = fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).unwrap();
    }
    #[cfg(not(unix))]
    {
        let _ = (package, relative_path);
        panic!("worktree mode-change fixture requires unix permissions");
    }
}

fn stage_worktree_mode_changed(package: &TestPackage, relative_path: &str) {
    mark_worktree_mode_changed(package, relative_path);
    run_git(package, &["add", relative_path]);
}

fn run_git(package: &TestPackage, args: &[&str]) {
    run_git_at(package.path(), args);
}

fn run_git_at(cwd: &Path, args: &[&str]) {
    let status = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .status()
        .unwrap();
    assert!(status.success(), "git {args:?} failed with {status}");
}

fn run_verify_with_jobs(
    package: &TestPackage,
    checker: PackageChecker,
    jobs: usize,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs,
        external: None,
        timings: PackageTimingMode::Off,
    })
}

fn run_verify_with_timings(
    package: &TestPackage,
    checker: PackageChecker,
    timings: PackageTimingMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: None,
        timings,
    })
}

fn run_verify_with_verifier_memo(
    package: &TestPackage,
    checker: PackageChecker,
    verifier_memo: PackageVerifierMemoMode,
    timings: PackageTimingMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo,
        jobs: 1,
        external: None,
        timings,
    })
}

fn run_verify_with_audit_cache(
    package: &TestPackage,
    checker: PackageChecker,
    audit_cache: PackageAuditCacheMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker,
        changed: false,
        audit_cache,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: None,
        timings: PackageTimingMode::Off,
    })
}

fn process_memo_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "process_memo_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("process memo summary diagnostic")
}

fn decode_cache_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "decode_cache_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("decode cache summary diagnostic")
}

fn disk_memo_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "disk_memo_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("disk memo summary diagnostic")
}

fn module_actual_value<'a>(
    result: &'a npa_cli::diagnostic::CommandResult,
    module: &str,
) -> &'a str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic.reason_code == "module_verified"
                && diagnostic.module.as_deref() == Some(module)
        })
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("module diagnostic actual value")
}

fn without_process_memo_decode_cache_and_timings(
    mut result: npa_cli::diagnostic::CommandResult,
) -> npa_cli::diagnostic::CommandResult {
    result.diagnostics.retain(|diagnostic| {
        diagnostic.reason_code != "process_memo_summary"
            && diagnostic.reason_code != "decode_cache_summary"
    });
    result.timings = None;
    result
}

fn without_disk_memo_summary_and_timings(
    mut result: npa_cli::diagnostic::CommandResult,
) -> npa_cli::diagnostic::CommandResult {
    result
        .diagnostics
        .retain(|diagnostic| diagnostic.reason_code != "disk_memo_summary");
    result.timings = None;
    result
}

fn run_verify_external(
    package: &TestPackage,
    external: PackageExternalCheckerOptions,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        checker: PackageChecker::External,
        changed: false,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: Some(external),
        timings: PackageTimingMode::Off,
    })
}

fn audit_cache_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "audit_cache_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("audit cache summary diagnostic")
}

fn audit_cache_follow_up(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "audit_cache_follow_up")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("audit cache follow-up diagnostic")
}

fn clear_audit_cache() {
    let _ = fs::remove_dir_all(
        std::env::current_dir()
            .unwrap()
            .join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR),
    );
}

fn audit_cache_entries() -> Vec<PathBuf> {
    let cache_dir = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR);
    let mut entries = fs::read_dir(cache_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

fn clear_disk_memo() {
    let _ = fs::remove_dir_all(
        std::env::current_dir()
            .unwrap()
            .join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR),
    );
}

fn disk_memo_entries() -> Vec<PathBuf> {
    let memo_dir = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR);
    let mut entries = fs::read_dir(memo_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

fn remove_audit_cache_entries_for_module(module: &str) {
    for path in audit_cache_entries() {
        let source = fs::read_to_string(&path).unwrap();
        let entry = parse_package_audit_result_entry_json(&source).unwrap();
        if entry.key_input.module.as_dotted() == module {
            fs::remove_file(path).unwrap();
        }
    }
}

fn remove_disk_memo_entries_for_module(module: &str) {
    for path in disk_memo_entries() {
        let source = fs::read_to_string(&path).unwrap();
        let entry = parse_package_audit_disk_memo_result_entry_json(&source).unwrap();
        if entry.key_input.module.as_dotted() == module {
            fs::remove_file(path).unwrap();
        }
    }
}

fn audit_cache_test_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap()
}

fn process_memo_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn disk_memo_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn decode_cache_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn shared_process_state_test_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn write_external_runner_fixture(
    package: &TestPackage,
    create_binary: bool,
) -> PackageExternalCheckerOptions {
    let checker_build_hash = test_hash(0x55);
    let lock_source = fs::read_to_string(package.artifact_path(LOCK_PATH)).unwrap();
    let lock = parse_package_lock_json(&lock_source).unwrap();
    let mut checker_script = "#!/bin/sh\ncase \"$2\" in\n".to_owned();
    for entry in &lock.entries {
        checker_script.push_str(&format!(
            "  '{}')\n    cat <<'JSON'\n{{\"schema\":\"npa.independent-checker.checker_raw_result.v1\",\"checker_id\":\"npa-checker-ext\",\"checker_version\":\"0.1.0\",\"checker_build_hash\":\"{}\",\"status\":\"checked\",\"module\":\"{}\",\"certificate_hash\":\"{}\",\"export_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}\nJSON\n    ;;\n",
            entry.certificate.as_str(),
            format_hash_string(&checker_build_hash),
            entry.module.as_dotted(),
            format_package_hash(&entry.certificate_hash),
            format_package_hash(&entry.export_hash),
            format_package_hash(&entry.axiom_report_hash),
        ));
    }
    checker_script
        .push_str("  *)\n    echo 'unknown certificate path' >&2\n    exit 2\n    ;;\nesac\n");
    let checker_path = package.artifact_path("tools/checkers/npa-checker-ext");
    let binary_hash = if create_binary {
        fs::create_dir_all(checker_path.parent().unwrap()).unwrap();
        fs::write(&checker_path, checker_script.as_bytes()).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let mut permissions = fs::metadata(&checker_path).unwrap().permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(&checker_path, permissions).unwrap();
        }
        independent_checker_file_hash(checker_script.as_bytes())
    } else {
        independent_checker_file_hash(b"missing external checker fixture")
    };

    let axiom_policy_path = package.artifact_path("ci/axiom-policy.toml");
    let axiom_policy_bytes = b"allow_custom_axioms = false\nallowed_axioms = [\"Eq.rec\"]\n";
    fs::create_dir_all(axiom_policy_path.parent().unwrap()).unwrap();
    fs::write(&axiom_policy_path, axiom_policy_bytes).unwrap();
    let axiom_policy_hash = independent_checker_file_hash(axiom_policy_bytes);

    let registry_source = r#"{"schema":"npa.independent-checker.checker_binary_registry.v1","root_kind":"workspace","entries":[{"binary_id":"npa-checker-ext-macos-aarch64","path":"tools/checkers/npa-checker-ext"}]}"#;
    let registry_path = package.artifact_path("ci/checker-binaries.json");
    fs::write(&registry_path, registry_source).unwrap();

    let policy_source = format!(
        r#"{{
          "schema":"npa.independent-checker.runner_policy.v1",
          "id":"package-external-pr",
          "version":1,
          "trust_mode":"pr",
          "required_checker_profiles":["reference"],
          "optional_checker_profiles":["external"],
          "checker_allowlist":[
            {{
              "profile":"external",
              "checker_id":"npa-checker-ext",
              "binary_id":"npa-checker-ext-macos-aarch64",
              "binary_hash":"{}",
              "build_hash":"{}",
              "allowed_args":[]
            }},
            {{
              "profile":"reference",
              "checker_id":"npa-checker-ref",
              "binary_id":"npa-checker-ref-macos-aarch64",
              "binary_hash":"{}",
              "build_hash":"{}",
              "allowed_args":["--json","--canonical-only"]
            }}
          ],
          "checker_identity_manifest":{{
            "kind":"file",
            "path":"ci/checker-identity.json",
            "manifest_hash":"{}"
          }},
          "import_policy":{{
            "mode":"locked_store",
            "network":"forbidden",
            "require_import_lock_hash":true
          }},
          "axiom_policy":{{
            "path":"ci/axiom-policy.toml",
            "hash":"{}"
          }},
          "budgets":{{
            "external":{{"max_steps":10000000,"max_memory_mb":2048,"timeout_ms":60000}},
            "reference":{{"max_steps":10000000,"max_memory_mb":2048,"timeout_ms":60000}}
          }},
          "on_resource_exhausted":"fail",
          "on_missing_required_checker":"fail",
          "on_profile_requested_by_ai":"ignore_unless_policy_allows"
        }}"#,
        format_hash_string(&binary_hash),
        format_hash_string(&checker_build_hash),
        format_hash_string(&test_hash(0x10)),
        format_hash_string(&test_hash(0x11)),
        format_hash_string(&test_hash(0x12)),
        format_hash_string(&axiom_policy_hash),
    );
    let policy_hash = parse_independent_checker_runner_policy(&policy_source)
        .unwrap()
        .policy_hash();
    let policy_path = package.artifact_path("ci/runner.release.json");
    fs::write(&policy_path, policy_source).unwrap();

    PackageExternalCheckerOptions {
        runner_policy: PathBuf::from("ci/runner.release.json"),
        runner_policy_hash: format_hash_string(&policy_hash),
        checker_registry: PathBuf::from("ci/checker-binaries.json"),
    }
}

fn test_hash(byte: u8) -> npa_cert::Hash {
    [byte; 32]
}

fn assert_info(
    diagnostic: &npa_cli::diagnostic::CommandDiagnostic,
    kind: DiagnosticKind,
    reason: &str,
    checker: Option<&str>,
) {
    assert_eq!(diagnostic.kind, kind);
    assert_eq!(diagnostic.reason_code, reason);
    assert_eq!(diagnostic.severity, DiagnosticSeverity::Info);
    assert_eq!(diagnostic.checker.as_deref(), checker);
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
    assert!(diagnostic.checker.is_none());
    assert!(!result.render_json().contains("/tmp/"));
}

fn build_source_free_fixture(
    label: &str,
    module_name: &str,
    include_external: bool,
    allowed_axioms: &[&str],
) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == module_name)
        .unwrap();
    copy_artifact(&package, module.certificate.as_str());

    let imports = if include_external {
        manifest
            .imports
            .as_deref()
            .unwrap_or(&[])
            .iter()
            .filter(|import| module.imports.contains(&import.module))
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    for import in &imports {
        copy_artifact(&package, import.certificate.as_str());
    }

    let manifest_source = fixture_manifest(
        allowed_axioms,
        &imports,
        &[manifest_module_from_package(module)],
    );
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_source_free_modules_fixture(
    label: &str,
    module_names: &[&str],
    allowed_axioms: &[&str],
) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let local_modules = module_names
        .iter()
        .map(Name::from_dotted)
        .collect::<BTreeSet<_>>();
    let modules = module_names
        .iter()
        .map(|module_name| {
            manifest
                .modules
                .iter()
                .find(|module| module.module.as_dotted() == *module_name)
                .unwrap()
                .clone()
        })
        .collect::<Vec<_>>();
    let external_import_modules = modules
        .iter()
        .flat_map(|module| module.imports.iter().cloned())
        .filter(|module| !local_modules.contains(module))
        .collect::<BTreeSet<_>>();
    let imports = manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .filter(|import| external_import_modules.contains(&import.module))
        .cloned()
        .collect::<Vec<_>>();

    for module in &modules {
        copy_artifact(&package, module.certificate.as_str());
    }
    for import in &imports {
        copy_artifact(&package, import.certificate.as_str());
    }

    let manifest_modules = modules
        .iter()
        .map(manifest_module_from_package)
        .collect::<Vec<_>>();
    let manifest_source = fixture_manifest(allowed_axioms, &imports, &manifest_modules);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn manifest_module_from_package(module: &PackageModule) -> ManifestModule {
    ManifestModule {
        module: module.module.clone(),
        source: module.source.as_str().to_owned(),
        certificate: module.certificate.as_str().to_owned(),
        meta: module.meta.as_ref().map(|path| path.as_str().to_owned()),
        replay: module.replay.as_ref().map(|path| path.as_str().to_owned()),
        imports: module.imports.clone(),
        source_hash: module.expected_source_hash,
        certificate_file_hash: module.expected_certificate_file_hash,
        export_hash: module.expected_export_hash,
        axiom_report_hash: module.expected_axiom_report_hash,
        certificate_hash: module.expected_certificate_hash,
    }
}

fn fixture_manifest(
    allowed_axioms: &[&str],
    imports: &[PackageExternalImport],
    modules: &[ManifestModule],
) -> String {
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
allowed_axioms = {}

"#,
        name_array(allowed_axioms),
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
"#,
            module.module.as_dotted(),
            module.source,
            module.certificate,
        ));
        if let Some(meta) = &module.meta {
            source.push_str(&format!("meta = \"{meta}\"\n"));
        }
        if let Some(replay) = &module.replay {
            source.push_str(&format!("replay = \"{replay}\"\n"));
        }
        source.push_str(&format!(
            r#"imports = {}
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

fn name_array(names: &[&str]) -> String {
    let names = names
        .iter()
        .map(|name| format!("\"{name}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{names}]")
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

fn copy_artifact(package: &TestPackage, relative: &str) {
    let source = repo_root().join("testdata/package/proofs").join(relative);
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::copy(source, target).unwrap();
}

fn tamper_certificate_payload_without_rehash(path: &Path) {
    let mut bytes = fs::read(path).unwrap();
    let needle = b"eq_refl_prop";
    let Some(index) = bytes
        .windows(needle.len())
        .position(|window| window == needle)
    else {
        panic!("expected Eq fixture declaration name in certificate bytes");
    };
    bytes[index] = b'f';
    fs::write(path, bytes).unwrap();
}

fn refresh_expected_certificate_file_hash(package: &TestPackage, certificate: &Path) {
    let file_hash = package_file_hash(&fs::read(certificate).unwrap());
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let line = source
        .lines()
        .find(|line| line.starts_with("expected_certificate_file_hash = \""))
        .unwrap();
    let replacement = format!(
        "expected_certificate_file_hash = \"{}\"",
        format_package_hash(&file_hash)
    );
    fs::write(path, source.replacen(line, &replacement, 1)).unwrap();
}

fn proof_manifest() -> npa_package::ValidatedPackageManifest {
    let source =
        fs::read_to_string(repo_root().join("testdata/package/proofs/npa-package.toml")).unwrap();
    parse_and_validate_manifest_str(&source).unwrap()
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

fn corpus_script_path(script: &str) -> Option<PathBuf> {
    let root = repo_root();
    let standalone_path = root.join("scripts").join(script);
    if standalone_path.exists() {
        return Some(standalone_path);
    }
    let container_path = root.join("../npa-corpus/scripts").join(script);
    container_path.exists().then_some(container_path)
}

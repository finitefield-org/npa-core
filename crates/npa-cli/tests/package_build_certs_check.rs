use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use npa_api::{PerformanceMeasurementLabel, PerformanceMeasurementReport};
use npa_cert::{AxiomPolicy, Name, VerifiedModule};
use npa_cli::args::{KernelFuelReportMode, PackageBuildCheckCacheMode, PackageTimingMode};
use npa_cli::diagnostic::{CommandExitCode, CommandResult, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{
    build_certs_check, build_certs_write, common_options, refresh_artifacts_check,
};
use npa_cli::package_build::{run_package_build_certs, run_package_build_certs_check};
use npa_frontend::{
    compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy,
    compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_build_check_cache_key,
    package_build_check_cache_namespace_digest, package_build_check_result_entry_json,
    package_file_hash, parse_and_validate_manifest_str,
    parse_package_build_check_result_entry_json, parse_targeted_authoring_support_context_entry,
    PackageBuildCheckCachedStatus, PackageCacheKeyDigest, PackageCacheStoreLayout,
    PackageCacheStoreVersion, PackageHash, PackagePath, TargetedAuthoringSupportContextEntry,
    PACKAGE_BUILD_CHECK_CACHE_SCHEMA, PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
    PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA, TARGETED_AUTHORING_CACHE_LIMITS_V1,
};

#[allow(dead_code)]
#[path = "../examples/targeted_build_certs_bench.rs"]
mod targeted_build_certs_bench;

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const LOCK_PATH: &str = "generated/package-lock.json";
const FRONTEND_FAILURE_MESSAGE: &str =
    "unannotated Human lambda binder requires an expected function type";
const FRONTEND_FAILURE_SOURCE: &str =
    "def product_enumeration_bad : Type := fun product => product\n";
const UNIVERSE_ALIAS_FAILURE_SOURCE: &str = "\
def FunctionAlias.{u} : forall (Carrier : Sort u), Sort max 1 u :=
  fun Carrier => Prop -> Carrier
";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);
static BUILD_CHECK_CACHE_TEST_LOCK: Mutex<()> = Mutex::new(());

const FUEL_MODES: [KernelFuelReportMode; 3] = [
    KernelFuelReportMode::Off,
    KernelFuelReportMode::Failure,
    KernelFuelReportMode::Detailed,
];
const TIMING_MODES: [PackageTimingMode; 3] = [
    PackageTimingMode::Off,
    PackageTimingMode::Summary,
    PackageTimingMode::Detailed,
];

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
        let path = fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
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
fn targeted_build_certs_bench_fixture_is_deterministic() {
    targeted_build_certs_bench::verify_fixture_contract_only().unwrap();
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
fn package_build_certs_function_alias_universe_mismatch_is_structured_without_writes() {
    let package = build_minimal_fixture("function-alias-universe-mismatch");
    install_universe_alias_failure(&package, "Proofs/Ai/Basic/source.npa", "Proofs.Ai.Basic");
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Proofs.Ai.Basic")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(result.artifacts.is_empty());
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "package_build_selection"));
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "build_failed")
        .expect("targeted build should retain the frontend failure");
    assert_eq!(diagnostic.kind, DiagnosticKind::Build);
    assert_eq!(diagnostic.reason_code, "build_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Basic"));
    assert_eq!(diagnostic.path.as_deref(), Some("modules[0].source"));
    assert_eq!(diagnostic.field.as_deref(), Some("kernel_handoff"));
    assert_eq!(diagnostic.expected_value.as_deref(), Some("max 1 u"));
    assert_eq!(
        diagnostic.actual_value.as_deref(),
        Some("declaration=FunctionAlias;inferred_level=imax 1 u;type_path=pi_body")
    );
    let source = diagnostic
        .source
        .as_ref()
        .expect("universe mismatch should retain source context");
    assert_eq!(source.path(), "Proofs/Ai/Basic/source.npa");
    assert_eq!(source.declaration(), Some("FunctionAlias"));
    assert_eq!(source.line(), Some(1));
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
            "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"failed\",\"diagnostics\":[{{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"module\":\"Proofs.Ai.Basic\",\"path\":\"modules[0].source\",\"field\":\"elaborator\",\"actual_value\":\"{FRONTEND_FAILURE_MESSAGE}\",\"source\":{{\"path\":\"Proofs/Ai/Basic/source.npa\",\"start_byte\":{start},\"end_byte\":{end},\"declaration\":\"product_enumeration_bad\",\"line\":1,\"column\":{},\"token\":\"product\"}}}}],\"artifacts\":[]}}\n",
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
            "mode=modules,seeds=1,rebuild=1,support_local=0,support_external=1,changed_external=0,promotion=none"
        )
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_refresh_preflight_precedes_first_certificate_read() {
    let package = build_synthetic_external_import_chain_fixture("targeted-preflight-first");
    fs::write(
        package.artifact_path("Fixture/Local/source.npa"),
        "import Fixture.External.Leaf\n\ndef local_bad : Type := (\n",
    )
    .unwrap();
    for path in [
        "vendor/fixture-external/Fixture/External/Leaf/certificate.npcert",
        "vendor/fixture-external/Fixture/External/Base/certificate.npcert",
        "vendor/fixture-external/Fixture/External/Unrelated/certificate.npcert",
    ] {
        fs::write(package.artifact_path(path), b"not a certificate").unwrap();
    }
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 3);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_schedule"
    );
    let diagnostic = &result.diagnostics[2];
    assert_eq!(diagnostic.reason_code, "build_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Fixture.Local"));
    assert_eq!(diagnostic.field.as_deref(), Some("parser"));
    assert_eq!(
        diagnostic.actual_value.as_deref(),
        Some("unclosed delimiter '(' at byte 54; expected ')' before end of input")
    );
    let delimiter = diagnostic
        .delimiter()
        .expect("build preflight should retain structured delimiter context");
    assert_eq!(delimiter.kind(), "unclosed_delimiter");
    assert_eq!(delimiter.expected_closing(), Some(")"));
    assert_eq!(delimiter.actual_closing(), None);
    let opening = delimiter
        .opening_source()
        .expect("unclosed delimiter should identify its opening token");
    assert_eq!(opening.start_byte(), 54);
    assert_eq!(opening.token(), Some("("));
    assert_eq!(
        diagnostic
            .source
            .as_ref()
            .and_then(|source| source.declaration()),
        None
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_refresh_application_failure_precedes_unrelated_import() {
    let package = build_synthetic_external_import_chain_fixture("targeted-application-first");
    fs::write(
        package.artifact_path("Fixture/Local/source.npa"),
        "import Fixture.External.Leaf\n\ndef local_bad : Type := Prop Prop\n",
    )
    .unwrap();
    fs::write(
        package
            .artifact_path("vendor/fixture-external/Fixture/External/Unrelated/certificate.npcert"),
        b"not a certificate",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 3);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_schedule"
    );
    let diagnostic = &result.diagnostics[2];
    assert_eq!(diagnostic.reason_code, "build_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Fixture.Local"));
    assert_eq!(diagnostic.field.as_deref(), Some("kernel_handoff"));
    assert!(
        diagnostic
            .actual_value
            .as_deref()
            .unwrap()
            .contains("expected a function type"),
        "{:?}",
        diagnostic.actual_value
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_targeted_refresh_still_rejects_unrelated_import_after_priority_success() {
    let package = build_synthetic_external_import_chain_fixture("targeted-completion-import");
    fs::write(
        package
            .artifact_path("vendor/fixture-external/Fixture/External/Unrelated/certificate.npcert"),
        b"not a certificate",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.Local")]),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 3);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_schedule"
    );
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some("priority_rebuild=1,priority_support_local=0,priority_external_roots=1,declared_external=3,deferred_rebuild=0,deferred_support_local=0,snapshot_unrelated_local=0")
    );
    assert_eq!(
        result.diagnostics[2].reason_code,
        "external_certificate_rejected"
    );
    assert_eq!(
        result.diagnostics[2].module.as_deref(),
        Some("Fixture.External.Unrelated")
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_full_refresh_preflight_precedes_first_certificate_read() {
    let package = build_synthetic_external_import_chain_fixture("full-preflight-first");
    fs::write(
        package.artifact_path("Fixture/Local/source.npa"),
        "import Fixture.External.Leaf\n\ndef local_bad : Type := [\n",
    )
    .unwrap();
    fs::write(
        package.artifact_path("vendor/fixture-external/Fixture/External/Leaf/certificate.npcert"),
        b"not a certificate",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(refresh_artifacts_check(common_options(
        package.path(),
        true,
    )));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "build_failed");
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("parser"));
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("unclosed delimiter '['"));
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
            "mode=changed,seeds=0,rebuild=0,support_local=0,support_external=0,changed_external=1,promotion=none"
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
    assert_eq!(result.diagnostics.len(), 4);
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=1,rebuild=2"));
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_schedule"
    );
    assert_eq!(
        result.diagnostics[2].reason_code,
        "package_build_refresh_plan"
    );
    assert!(result.diagnostics[2]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("source_rebuild=1,certificate_rebind=1,unchanged=0"));
    assert_eq!(result.diagnostics[3].reason_code, "manifest_hashes_stale");
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
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .ends_with("promotion=manifest_changed"));
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
fn package_build_certs_selection_changed_manifest_refresh_promotes_priority_order() {
    let package = build_synthetic_local_import_fixture("changed-manifest-refresh-full");
    init_git_package(&package, true);
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let mut manifest = fs::read_to_string(&manifest_path).unwrap();
    manifest.push_str("\n# changed selection promotion\n");
    fs::write(manifest_path, manifest).unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true)).with_changed(),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 4);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .ends_with("promotion=manifest_changed"));
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some("priority_rebuild=2,priority_support_local=0,priority_external_roots=0,declared_external=0,deferred_rebuild=0,deferred_support_local=0,snapshot_unrelated_local=0")
    );
    assert_eq!(
        result.diagnostics[2].reason_code,
        "package_build_refresh_plan"
    );
    assert_eq!(result.diagnostics[3].reason_code, "package_lock_stale");
    assert_eq!(package_snapshot(&package), before);
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
fn package_build_certs_selection_changed_lock_only_refresh_has_empty_priority_phase() {
    let package = build_synthetic_local_import_fixture("changed-lock-only-refresh");
    init_git_package(&package, true);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock = fs::read_to_string(&lock_path).unwrap();
    lock.push('\n');
    fs::write(lock_path, lock).unwrap();
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        refresh_artifacts_check(common_options(package.path(), true))
            .with_changed()
            .with_timings(PackageTimingMode::Summary),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 4);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=changed,seeds=0,rebuild=0"));
    assert_eq!(
        result.diagnostics[1].reason_code,
        "package_build_refresh_schedule"
    );
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some("priority_rebuild=0,priority_support_local=0,priority_external_roots=0,declared_external=0,deferred_rebuild=0,deferred_support_local=0,snapshot_unrelated_local=2")
    );
    assert_eq!(
        result.diagnostics[2].reason_code,
        "package_build_refresh_plan"
    );
    assert_eq!(result.diagnostics[3].reason_code, "package_lock_stale");
    assert_eq!(
        result
            .timings
            .as_ref()
            .unwrap()
            .metrics
            .iter()
            .find(|metric| metric.field == "priority_build_ms")
            .unwrap()
            .milliseconds,
        0
    );
    assert_eq!(package_snapshot(&package), before);
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
        "{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
}

#[test]
fn package_build_check_cache_read_through_writes_then_hits() {
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
fn package_build_check_cache_legacy_store_is_inert() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-legacy-inert");
    let legacy_store = build_check_cache_base().join("build-check-v0.2");
    fs::create_dir_all(&legacy_store).unwrap();
    let legacy_entry = legacy_store.join("legacy.json");
    fs::write(&legacy_entry, b"legacy-sidecar").unwrap();

    let result = run_build_check_read_through(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &result,
        "mode=read-through;hits=0;misses=1;stale=0;schema_misses=0;written=1;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read(&legacy_entry).unwrap(), b"legacy-sidecar");
    assert_eq!(build_check_cache_entries().len(), 1);
}

#[test]
fn package_build_check_cache_unavailable_preserves_live_result_and_zero_outcomes() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-unavailable");
    let before = package_snapshot(&package);
    let unsafe_cache_root = package.path().join("package-owned-cache");

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(unsafe_cache_root.clone()),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(package_snapshot(&package), before);
    assert!(!unsafe_cache_root.exists());
    let unavailable = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "build_check_cache_unavailable")
        .collect::<Vec<_>>();
    assert_eq!(unavailable.len(), 1);
    assert_eq!(unavailable[0].kind, DiagnosticKind::GeneratedArtifact);
    assert_eq!(unavailable[0].field.as_deref(), Some("build_check_cache"));
    assert_eq!(
        unavailable[0].actual_value.as_deref(),
        Some("mode=read-through;stores=build-check-v0.2;reason=anchor_or_capability")
    );
    assert_build_check_cache_summary(
        &result,
        "mode=read-through;hits=0;misses=0;stale=0;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
}

#[test]
fn package_build_check_cache_preserves_schema_miss_without_unsafe_replacement() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-schema-miss");
    let first = run_build_check_read_through(&package);
    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let entry_path = fs::read_dir(only_build_check_cache_store_dir())
        .unwrap()
        .filter_map(Result::ok)
        .find(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .unwrap()
        .path();
    let source = fs::read_to_string(&entry_path).unwrap().replacen(
        PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
        "npa.package.build_check_result.v0.1",
        1,
    );
    fs::write(&entry_path, &source).unwrap();

    let second = run_build_check_read_through(&package);
    assert_eq!(second.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &second,
        "mode=read-through;hits=0;misses=0;stale=0;schema_misses=1;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), source);

    let third = run_build_check_read_through(&package);
    assert_eq!(third.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &third,
        "mode=read-through;hits=0;misses=0;stale=0;schema_misses=1;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), source);
}

#[test]
fn package_build_cache_security_result_store_preserves_stale_entry() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-entry-byte-limit");
    let first = run_build_check_read_through(&package);
    assert_eq!(first.exit_code(), CommandExitCode::Success);

    let entry_path = fs::read_dir(only_build_check_cache_store_dir())
        .unwrap()
        .filter_map(Result::ok)
        .find(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .unwrap()
        .path();
    let original = fs::read_to_string(&entry_path).unwrap();
    let oversized = vec![b' '; TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes + 1];
    fs::write(&entry_path, &oversized).unwrap();

    let second = run_build_check_read_through(&package);
    assert_eq!(second.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &second,
        "mode=read-through;hits=0;misses=0;stale=1;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read(&entry_path).unwrap(), oversized);

    let third = run_build_check_read_through(&package);
    assert_eq!(third.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &third,
        "mode=read-through;hits=0;misses=0;stale=1;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read(&entry_path).unwrap(), oversized);

    let mut stale = parse_package_build_check_result_entry_json(&original).unwrap();
    stale.status = PackageBuildCheckCachedStatus::Rejected;
    stale.diagnostic_reason = Some("forged_live_result".to_owned());
    let forged = package_build_check_result_entry_json(&stale);
    fs::write(&entry_path, &forged).unwrap();

    let fourth = run_build_check_read_through(&package);
    assert_eq!(fourth.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &fourth,
        "mode=read-through;hits=0;misses=0;stale=1;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), forged);

    let fifth = run_build_check_read_through(&package);
    assert_eq!(fifth.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &fifth,
        "mode=read-through;hits=0;misses=0;stale=1;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
    );
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), forged);
}

#[test]
fn package_build_check_cache_targeted_read_through_missing_then_valid_hit_is_diagnostic_only() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-hit");
    let modules = vec![Name::from_dotted("Fixture.B")];
    let before = package_snapshot(&package);
    let off = run_targeted_build_check(&package, modules.clone());
    assert!(!build_check_cache_base().exists());

    let missing = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &missing);
    assert_targeted_build_check_cache_summary(&missing, 1, 1, 0, 1, 0, 0, 1, 1);
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.B"));
    assert_eq!(
        targeted_authoring_support_entries(package.path())
            .into_iter()
            .map(|entry| entry.key_input.module)
            .collect::<Vec<_>>(),
        vec![Name::from_dotted("Fixture.A")],
    );

    let hit = run_targeted_build_check_read_through(&package, modules);
    assert_targeted_cache_differential(&off, &hit);
    assert_targeted_build_check_cache_summary(&hit, 1, 1, 1, 0, 0, 0, 0, 0);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_check_cache_targeted_read_through_preserves_stale_invalid_and_schema_miss() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("targeted-cache-repair");
    let modules = vec![Name::from_dotted("Proofs.Ai.Basic")];
    let off = run_targeted_build_check(&package, modules.clone());
    let initial = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &initial);
    assert_targeted_build_check_cache_summary(&initial, 0, 1, 0, 1, 0, 0, 1, 0);

    let entry_path = only_build_check_cache_entry_path();
    let original = fs::read_to_string(&entry_path).unwrap();
    let mut stale = parse_package_build_check_result_entry_json(&original).unwrap();
    stale.status = PackageBuildCheckCachedStatus::Rejected;
    stale.diagnostic_reason = Some("different_live_result".to_owned());
    let stale = package_build_check_result_entry_json(&stale);
    fs::write(&entry_path, &stale).unwrap();
    let preserved_stale = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &preserved_stale);
    assert_targeted_build_check_cache_summary(&preserved_stale, 0, 1, 0, 0, 1, 0, 0, 0);
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), stale);

    let invalid = b"not canonical cache json";
    fs::write(&entry_path, invalid).unwrap();
    let preserved_invalid = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &preserved_invalid);
    assert_targeted_build_check_cache_summary(&preserved_invalid, 0, 1, 0, 0, 1, 0, 0, 0);
    assert_eq!(fs::read(&entry_path).unwrap(), invalid);

    let unsupported_schema = original.replacen(
        PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
        "npa.package.build_check_result.v0.1",
        1,
    );
    fs::write(&entry_path, &unsupported_schema).unwrap();
    let preserved_schema = run_targeted_build_check_read_through(&package, modules);
    assert_targeted_cache_differential(&off, &preserved_schema);
    assert_targeted_build_check_cache_summary(&preserved_schema, 0, 1, 0, 0, 0, 1, 0, 0);
    assert_eq!(fs::read_to_string(&entry_path).unwrap(), unsupported_schema);
}

#[test]
fn package_build_check_cache_targeted_read_through_failed_build_counts_attempts() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-failed-build");
    install_frontend_failure(&package, "Fixture/B/source.npa", "Fixture.B");
    let modules = vec![Name::from_dotted("Fixture.B")];
    let before = package_snapshot(&package);
    let off = run_targeted_build_check(&package, modules.clone());

    let cached = run_targeted_build_check_read_through(&package, modules);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 1, 1, 0, 0, 0, 0, 0, 1);
    assert!(build_check_cache_entries().is_empty());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_check_cache_targeted_read_through_source_mismatch_records_built_identity() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-source-mismatch");
    let source_path = package.artifact_path("Fixture/B/source.npa");
    let mut source = fs::read_to_string(&source_path).unwrap();
    source.push('\n');
    fs::write(source_path, source).unwrap();
    let modules = vec![Name::from_dotted("Fixture.B")];
    let off = run_targeted_build_check(&package, modules.clone());

    let cached = run_targeted_build_check_read_through(&package, modules);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 1, 1, 0, 1, 0, 0, 1, 1);
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.B"));
    assert_eq!(entries[0].status, PackageBuildCheckCachedStatus::Rejected);
    assert_eq!(
        entries[0].diagnostic_reason.as_deref(),
        Some("source_hash_mismatch")
    );
}

#[test]
fn package_build_check_cache_targeted_read_through_late_failure_retains_prior_target_identity() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-late-failure");
    install_frontend_failure(&package, "Fixture/B/source.npa", "Fixture.B");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
    ];
    let off = run_targeted_build_check(&package, modules.clone());

    let missing = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &missing);
    assert_targeted_build_check_cache_summary(&missing, 0, 2, 0, 1, 0, 0, 1, 0);
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.A"));
    assert_eq!(entries[0].status, PackageBuildCheckCachedStatus::Rejected);

    let hit = run_targeted_build_check_read_through(&package, modules);
    assert_targeted_cache_differential(&off, &hit);
    assert_targeted_build_check_cache_summary(&hit, 0, 2, 1, 0, 0, 0, 0, 0);
}

#[test]
fn package_build_check_cache_targeted_read_through_failed_support_counts_attempt() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-failed-support");
    let source_path = package.artifact_path("Fixture/A/source.npa");
    let mut source = fs::read_to_string(&source_path).unwrap();
    source.push('\n');
    fs::write(source_path, source).unwrap();
    let modules = vec![Name::from_dotted("Fixture.B")];
    let before = package_snapshot(&package);
    let off = run_targeted_build_check(&package, modules.clone());

    let cached = run_targeted_build_check_read_through(&package, modules);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 1, 0, 0, 0, 0, 0, 0, 0);
    assert!(build_check_cache_entries().is_empty());
    assert!(targeted_authoring_support_entries(package.path()).is_empty());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_check_cache_targeted_read_through_unavailable_has_zero_result_outcomes() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-unavailable");
    let modules = vec![Name::from_dotted("Fixture.B")];
    let unsafe_cache_root = package.path().join("package-owned-cache");
    let off = run_targeted_build_check(&package, modules.clone());

    let cached = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(unsafe_cache_root.clone()),
    );

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 1, 1, 0, 0, 0, 0, 0, 0);
    let unavailable = cached
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "build_check_cache_unavailable")
        .collect::<Vec<_>>();
    assert_eq!(unavailable.len(), 1);
    assert_eq!(
        unavailable[0].actual_value.as_deref(),
        Some(
            "mode=read-through;stores=build-check-v0.2|targeted-authoring-support-v0.1;reason=anchor_or_capability"
        )
    );
    assert!(!unsafe_cache_root.exists());
}

#[test]
fn package_build_check_cache_targeted_read_through_empty_selection_has_zero_work() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-empty");
    init_git_package(&package, true);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock = fs::read_to_string(&lock_path).unwrap();
    lock.push('\n');
    fs::write(lock_path, lock).unwrap();
    let before = package_snapshot(&package);
    let off = run_changed_build_check(&package);

    let cached = run_changed_build_check_read_through(&package);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 0, 0, 0, 0, 0, 0, 0, 0);
    assert!(build_check_cache_entries().is_empty());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_check_cache_targeted_read_through_external_only_preserves_live_failure() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_external_import_chain_fixture("targeted-cache-external-only");
    init_git_package(&package, true);
    install_changed_external_leaf_certificate(&package);
    let before = package_snapshot(&package);
    let off = run_changed_build_check(&package);

    let cached = run_changed_build_check_read_through(&package);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 0, 0, 0, 0, 0, 0, 0, 0);
    assert!(build_check_cache_entries().is_empty());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_read_through_warming_publishes_live_chain_without_support_lookup() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-read-through-warming-chain");
    let before = package_snapshot(&package);

    let warmed =
        run_targeted_build_check_read_through(&package, vec![Name::from_dotted("Fixture.B")]);

    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    let entries = targeted_authoring_support_entries(package.path());
    assert_eq!(entries.len(), 1, "{:#?}", warmed.diagnostics);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.A"));
    let summary = warmed
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "build_check_cache_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .unwrap();
    assert!(summary.contains("support_context_cache_hits=0"));
    assert!(summary.contains("support_context_entries_written=1"));
    assert_eq!(package_snapshot(&package), before);

    let reused = run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.B")]);
    assert_eq!(reused.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&reused, true);
}

#[test]
fn targeted_read_through_warming_publishes_fully_live_diamond() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_diamond_fixture("targeted-read-through-warming-diamond");

    let warmed =
        run_targeted_build_check_read_through(&package, vec![Name::from_dotted("Fixture.D")]);

    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    assert_eq!(
        targeted_authoring_support_entries(package.path())
            .into_iter()
            .map(|entry| entry.key_input.module)
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from([
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.B"),
            Name::from_dotted("Fixture.C"),
        ])
    );

    let reused = run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.D")]);
    assert_eq!(reused.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&reused, true);
}

#[test]
fn targeted_authoring_publication_full_read_through_warms_only_retained_modules() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_diamond_fixture("full-read-through-warming-diamond");

    let warmed = run_build_check_read_through(&package);

    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    assert_eq!(
        targeted_authoring_support_entries(package.path())
            .into_iter()
            .map(|entry| entry.key_input.module)
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from([
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.B"),
            Name::from_dotted("Fixture.C"),
        ])
    );

    let reused = run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.D")]);
    assert_eq!(reused.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&reused, true);
}

#[test]
fn package_build_cache_security_late_lock_failure_preserves_support_entry_without_a_verdict() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("security-late-lock-failure");
    let lock_path = package.artifact_path(LOCK_PATH);
    let original_lock = fs::read(&lock_path).unwrap();
    let mut stale_lock = original_lock.clone();
    stale_lock.push(b'\n');
    fs::write(&lock_path, &stale_lock).unwrap();
    let before = package_snapshot(&package);

    let failed = run_build_check_read_through(&package);

    assert_eq!(failed.exit_code(), CommandExitCode::PackageFailure);
    assert!(failed.artifacts.is_empty());
    assert!(failed
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "package_lock_stale"));
    assert_eq!(package_snapshot(&package), before);
    let support_entries = targeted_authoring_support_entries(package.path());
    assert_eq!(support_entries.len(), 1, "{:#?}", failed.diagnostics);
    assert_eq!(
        support_entries[0].key_input.module,
        Name::from_dotted("Fixture.A")
    );
    for bytes in targeted_authoring_support_entry_bytes(package.path()) {
        let source = String::from_utf8(bytes).unwrap();
        for forbidden in ["command_verdict", "diagnostic_reason", "\"status\""] {
            assert!(
                !source.contains(forbidden),
                "support entry leaked command verdict field {forbidden}"
            );
        }
    }

    fs::write(&lock_path, original_lock).unwrap();
    let reused = run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.B")]);
    assert_eq!(reused.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&reused, true);
}

#[test]
fn targeted_authoring_differential_current_certificate_bytes_are_reread_after_warming() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("security-current-certificate-reread");
    init_git_package(&package, true);
    let pristine_snapshot = package_snapshot(&package);
    let pristine_status = git_status_snapshot(&package);

    let warmed =
        run_targeted_build_check_read_through(&package, vec![Name::from_dotted("Fixture.B")]);
    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    assert_eq!(package_snapshot(&package), pristine_snapshot);
    assert_eq!(git_status_snapshot(&package), pristine_status);
    assert_eq!(targeted_authoring_support_entries(package.path()).len(), 1);

    fs::write(
        package.artifact_path("Fixture/A/certificate.npcert"),
        b"not a current certificate",
    )
    .unwrap();
    let tampered_snapshot = package_snapshot(&package);
    let tampered_status = git_status_snapshot(&package);
    let modules = vec![Name::from_dotted("Fixture.B")];

    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_targeted_build_check_local_hit(&package, modules);

    assert_eq!(off.exit_code(), CommandExitCode::PackageFailure);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert_eq!(package_snapshot(&package), tampered_snapshot);
    assert_eq!(git_status_snapshot(&package), tampered_status);
    assert_eq!(targeted_authoring_support_entries(package.path()).len(), 1);
    for bytes in targeted_authoring_support_entry_bytes(package.path()) {
        assert!(!String::from_utf8(bytes)
            .unwrap()
            .contains("\"certificate_bytes\":"));
    }
}

#[test]
fn targeted_authoring_differential_cache_state_matrix_falls_back_live_and_remains_immutable() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("security-corrupt-support-fallback");
    let modules = vec![Name::from_dotted("Fixture.B")];
    let off = run_targeted_build_check(&package, modules.clone());
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    let warmed = run_targeted_build_check_read_through(&package, modules.clone());
    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    let package_before = package_snapshot(&package);
    let entry_path = only_targeted_authoring_support_entry_path(package.path());
    let canonical = fs::read(&entry_path).unwrap();

    let schema_miss = String::from_utf8(canonical.clone())
        .unwrap()
        .replacen(
            PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
            "npa.package.targeted_authoring_support_context.future",
            1,
        )
        .into_bytes();
    let mut invalid_digest = canonical.clone();
    let digest_marker = b"\"integrity_digest\":\"sha256:";
    let digest_start = invalid_digest
        .windows(digest_marker.len())
        .position(|window| window == digest_marker)
        .unwrap()
        + digest_marker.len();
    invalid_digest[digest_start] = if invalid_digest[digest_start] == b'0' {
        b'1'
    } else {
        b'0'
    };
    let variants = [
        ("invalid_json", b"{".to_vec()),
        ("schema_miss", schema_miss),
        ("integrity_digest", invalid_digest),
        (
            "entry_limit",
            vec![b' '; TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes + 1],
        ),
    ];

    for (label, hostile) in variants {
        fs::write(&entry_path, &hostile).unwrap();

        let local_hit = run_targeted_build_check_local_hit(&package, modules.clone());

        assert_targeted_authoring_differential(&off, &local_hit);
        assert_targeted_authoring_local_only(&local_hit, false);
        assert!(local_hit.artifacts.is_empty());
        assert!(
            local_hit
                .diagnostics
                .iter()
                .filter(|diagnostic| {
                    matches!(
                        diagnostic.reason_code.as_str(),
                        "targeted_authoring_cache_entry_stale"
                            | "targeted_authoring_cache_entry_schema_miss"
                            | "targeted_authoring_cache_entry_invalid"
                            | "targeted_authoring_cache_publication_failed"
                    )
                })
                .count()
                <= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics,
            "{label}: detailed diagnostics exceeded the fixed bound"
        );
        assert_eq!(
            fs::read(&entry_path).unwrap(),
            hostile,
            "{label}: immutable support entry was replaced"
        );
        assert_eq!(package_snapshot(&package), package_before);
    }
}

#[test]
fn targeted_authoring_publication_forbids_explicit_and_post_target_modules() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_post_target_support_fixture(
        "publication-forbids-explicit-post-target",
    );

    let result = run_targeted_build_check_local_hit(
        &package,
        vec![
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.C"),
        ],
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(targeted_authoring_support_entries(package.path()).is_empty());
}

#[test]
fn targeted_authoring_differential_missing_cold_run_is_non_authoritative() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-local-hit-cold");
    let before = package_snapshot(&package);

    let result = run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.B")]);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.artifacts.is_empty());
    assert_targeted_authoring_local_only(&result, false);
    assert_eq!(result.diagnostics.len(), 3);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "targeted_authoring_cache_summary"
    );
    assert!(build_check_cache_entries().is_empty());
    let support_store = targeted_authoring_support_cache_dir(package.path());
    assert!(support_store.is_dir());
    let entries = targeted_authoring_support_entries(package.path());
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.A"));
    assert!(build_check_cache_base().is_dir());
    assert_eq!(package_snapshot(&package), before);

    let json = result.render_json();
    assert!(json.starts_with("{\"schema\":\"npa.package.command_result.v0.5\""));
    assert!(json
        .contains("\"reason_code\":\"targeted_authoring_cache_local_only\",\"severity\":\"info\""));
    assert!(json.contains(
        "\"field\":\"targeted_authoring_cache\",\"actual_value\":\"trusted=false;build_evidence=false;proof_evidence=false;locally_accelerated=false\""
    ));
    assert!(!json.contains("\"locally_accelerated\":"));
    assert!(!json.contains("\"build_evidence\":"));
}

#[test]
fn targeted_authoring_differential_unavailable_root_falls_back_once_without_entry_io() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-local-hit-unavailable-root");
    let unsafe_cache_root = package.artifact_path("unsafe-cache");
    let before = package_snapshot(&package);

    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.B")])
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(unsafe_cache_root.clone()),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.reason_code == "build_check_cache_unavailable")
            .count(),
        1
    );
    assert_eq!(
        result
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.reason_code == "build_check_cache_unavailable")
            .and_then(|diagnostic| diagnostic.actual_value.as_deref()),
        Some("mode=local-hit;stores=targeted-authoring-support-v0.1;reason=anchor_or_capability")
    );
    assert_targeted_authoring_local_only(&result, false);
    assert!(!unsafe_cache_root.exists());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_early_external_failure_precedes_local_cache_resolution() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_external_support_fixture("targeted-lookup-external-failure");
    fs::write(
        package.artifact_path(
            "vendor/fixture-external/Fixture/External/Dependency/certificate.npcert",
        ),
        b"not a certificate",
    )
    .unwrap();
    let before = package_snapshot(&package);

    let result =
        run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.Target")]);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(
        result.diagnostics[1].reason_code,
        "external_certificate_rejected"
    );
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| {
                diagnostic.reason_code == "targeted_authoring_cache_local_only"
            })
            .count(),
        1
    );
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "build_check_cache_unavailable"));
    assert!(!targeted_authoring_support_cache_dir(package.path()).exists());
    assert!(!build_check_cache_base().exists());
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_empty_and_external_only_preserve_boundaries() {
    let _guard = build_check_cache_guard();
    let empty = build_synthetic_local_import_fixture("targeted-local-hit-empty");
    init_git_package(&empty, true);
    let lock_path = empty.artifact_path(LOCK_PATH);
    let mut lock = fs::read_to_string(&lock_path).unwrap();
    lock.push('\n');
    fs::write(lock_path, lock).unwrap();
    let empty_before = package_snapshot(&empty);

    let empty_result = run_changed_build_check_local_hit(&empty);

    assert_eq!(empty_result.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&empty_result, false);
    assert!(build_check_cache_entries().is_empty());
    assert!(!targeted_authoring_support_cache_dir(empty.path()).exists());
    assert_eq!(package_snapshot(&empty), empty_before);

    let external =
        build_synthetic_external_import_chain_fixture("targeted-local-hit-external-only");
    init_git_package(&external, true);
    install_changed_external_leaf_certificate(&external);
    let external_before = package_snapshot(&external);

    let failed = run_changed_build_check_local_hit(&external);

    assert_eq!(failed.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(failed.diagnostics[0].reason_code, "package_build_selection");
    assert_eq!(failed.diagnostics[1].reason_code, "export_hash_mismatch");
    assert_targeted_authoring_local_only(&failed, false);
    assert_eq!(
        failed
            .diagnostics
            .iter()
            .filter(|diagnostic| {
                diagnostic.reason_code == "targeted_authoring_cache_local_only"
            })
            .count(),
        1
    );
    assert!(build_check_cache_entries().is_empty());
    assert!(!targeted_authoring_support_cache_dir(external.path()).exists());
    assert_eq!(package_snapshot(&external), external_before);
}

#[test]
fn targeted_authoring_differential_no_eligible_support_skips_cache_root_and_io() {
    let _guard = build_check_cache_guard();
    let no_support = build_synthetic_local_import_fixture("targeted-local-hit-no-support");
    let no_support_before = package_snapshot(&no_support);

    let no_support_result =
        run_targeted_build_check_local_hit(&no_support, vec![Name::from_dotted("Fixture.A")]);

    assert_eq!(no_support_result.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&no_support_result, false);
    assert!(build_check_cache_entries().is_empty());
    assert!(!targeted_authoring_support_cache_dir(no_support.path()).exists());
    assert!(!build_check_cache_base().exists());
    assert_eq!(package_snapshot(&no_support), no_support_before);

    let forced = build_synthetic_local_import_fixture("targeted-local-hit-forced");
    let manifest_path = forced.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest_source = fs::read_to_string(&manifest_path).unwrap();
    let certificate_field = "certificate = \"Fixture/B/certificate.npcert\"\n";
    let forced_manifest_source = manifest_source.replacen(
        certificate_field,
        &format!("{certificate_field}producer_profile = \"unsupported-fixture-profile\"\n"),
        1,
    );
    assert_ne!(forced_manifest_source, manifest_source);
    fs::write(&manifest_path, &forced_manifest_source).unwrap();
    write_lock(&forced, &forced_manifest_source);
    let forced_before = package_snapshot(&forced);

    let forced_result =
        run_targeted_build_check_local_hit(&forced, vec![Name::from_dotted("Fixture.B")]);

    assert_eq!(forced_result.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&forced_result, false);
    assert!(build_check_cache_entries().is_empty());
    assert!(!targeted_authoring_support_cache_dir(forced.path()).exists());
    assert!(!build_check_cache_base().exists());
    assert_eq!(package_snapshot(&forced), forced_before);
}

#[test]
fn targeted_authoring_differential_multi_target_fresh_and_forced_execute_once() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_multi_target_fixture("targeted-authoring-multi");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
        Name::from_dotted("Fixture.C"),
    ];
    let before = package_snapshot(&package);

    let off = run_targeted_build_check(&package, modules.clone());
    let read_through = run_targeted_build_check_read_through(&package, modules.clone());
    let local_hit = run_targeted_build_check_local_hit(&package, modules.clone());

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_targeted_cache_differential(&off, &read_through);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert!(local_hit.artifacts.is_empty());

    let observed = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base())
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
            .with_timings(PackageTimingMode::Detailed),
    );
    assert_eq!(observed.exit_code(), CommandExitCode::Success);
    let declaration_modules = observed
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("detailed targeted build measurements")
        .declarations
        .iter()
        .map(|declaration| declaration.module.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        declaration_modules,
        vec!["Fixture.A", "Fixture.B", "Fixture.C"]
    );
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_multi_target_fresh_context_feeds_dependent() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-authoring-fresh-dependent");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
    ];
    let before = package_snapshot(&package);

    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_targeted_build_check_local_hit(&package, modules);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_multi_target_executes_post_target_support_in_order() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_post_target_support_fixture(
        "targeted-authoring-post-target-support",
    );
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.C"),
    ];
    let before = package_snapshot(&package);

    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_targeted_build_check_local_hit(&package, modules);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_multi_target_retains_transitive_fresh_context_to_last_use() {
    let _guard = build_check_cache_guard();
    let package =
        build_targeted_authoring_post_target_support_fixture("targeted-authoring-fresh-chain");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
        Name::from_dotted("Fixture.C"),
    ];
    let before = package_snapshot(&package);

    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_targeted_build_check_local_hit(&package, modules);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_output_parity_preserves_first_target_failure() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_multi_target_fixture("targeted-authoring-failure");
    install_frontend_failure(&package, "Fixture/B/source.npa", "Fixture.B");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
        Name::from_dotted("Fixture.C"),
    ];
    let before = package_snapshot(&package);

    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base())
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
            .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(off.exit_code(), CommandExitCode::PackageFailure);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, false);
    assert_eq!(local_hit.diagnostics[1].reason_code, "build_failed");
    let declaration_modules = local_hit
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("detailed targeted failure measurements")
        .declarations
        .iter()
        .map(|declaration| declaration.module.as_str())
        .collect::<Vec<_>>();
    assert_eq!(declaration_modules, vec!["Fixture.A"]);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn targeted_authoring_differential_retained_hit_then_first_of_many_targets_fails_once() {
    let _guard = build_check_cache_guard();
    let package = build_targeted_authoring_multi_target_fixture(
        "targeted-authoring-retained-hit-first-target-failure",
    );
    let manifest_path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest_source = fs::read_to_string(&manifest_path).unwrap();
    let manifest_source =
        manifest_source.replace("producer_profile = \"unsupported-fixture-profile\"\n", "");
    fs::write(&manifest_path, &manifest_source).unwrap();
    write_lock(&package, &manifest_source);
    let modules = vec![
        Name::from_dotted("Fixture.B"),
        Name::from_dotted("Fixture.C"),
    ];
    init_git_package(&package, true);

    let warmed = run_targeted_build_check_read_through(&package, modules.clone());
    assert_eq!(warmed.exit_code(), CommandExitCode::Success);
    assert_eq!(
        targeted_authoring_support_entries(package.path())
            .into_iter()
            .map(|entry| entry.key_input.module)
            .collect::<Vec<_>>(),
        vec![Name::from_dotted("Fixture.A")]
    );

    install_frontend_failure(&package, "Fixture/B/source.npa", "Fixture.B");
    let git_before = git_status_snapshot(&package);
    let before = package_snapshot(&package);
    let off = run_targeted_build_check(&package, modules.clone());
    let local_hit = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base())
            .with_timings(PackageTimingMode::Summary),
    );

    assert_eq!(off.exit_code(), CommandExitCode::PackageFailure);
    assert_targeted_authoring_differential(&off, &local_hit);
    assert_targeted_authoring_local_only(&local_hit, true);
    assert_eq!(local_hit.diagnostics[1].reason_code, "build_failed");
    let summary = local_hit
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "targeted_authoring_cache_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("local-hit failure summary");
    for field in [
        "complete=false",
        "support_selected=1",
        "targets_selected=2",
        "visited_support=1",
        "visited_targets=1",
        "context_hits=1",
        "target_fresh_builds=1",
    ] {
        assert!(summary.contains(field), "missing {field} in {summary}");
    }
    let measurements = local_hit
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("summary measurements");
    assert_eq!(
        measurement_counter(measurements, PerformanceMeasurementLabel::CacheContextHits,),
        1
    );
    assert_eq!(
        measurement_counter(
            measurements,
            PerformanceMeasurementLabel::CacheTargetFreshBuilds,
        ),
        1
    );
    assert_eq!(package_snapshot(&package), before);
    assert_eq!(git_status_snapshot(&package), git_before);
}

#[test]
fn targeted_authoring_differential_local_only_result_is_not_synthesized_before_a_valid_plan() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-local-hit-pre-plan");

    let result =
        run_targeted_build_check_local_hit(&package, vec![Name::from_dotted("Fixture.Unknown")]);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "targeted_authoring_cache_local_only"));
    assert!(build_check_cache_entries().is_empty());
    assert!(!targeted_authoring_support_cache_dir(package.path()).exists());
    assert!(!build_check_cache_base().exists());
}

#[test]
fn package_build_check_cache_targeted_read_through_changed_target_rebuilds_and_records_result() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-changed");
    init_git_package(&package, true);
    let certificate_path = package.artifact_path("Fixture/B/certificate.npcert");
    let mut certificate = fs::read(&certificate_path).unwrap();
    certificate.push(0);
    fs::write(certificate_path, certificate).unwrap();
    let before = package_snapshot(&package);
    let off = run_changed_build_check(&package);

    let cached = run_changed_build_check_read_through(&package);

    assert_targeted_cache_differential(&off, &cached);
    assert_targeted_build_check_cache_summary(&cached, 1, 1, 0, 1, 0, 0, 1, 1);
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].key_input.module, Name::from_dotted("Fixture.B"));
    assert_eq!(entries[0].status, PackageBuildCheckCachedStatus::Rejected);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_check_cache_targeted_read_through_multi_target_rebuilds_each_once() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-cache-multi");
    let modules = vec![
        Name::from_dotted("Fixture.A"),
        Name::from_dotted("Fixture.B"),
    ];
    let before = package_snapshot(&package);
    let off = run_targeted_build_check(&package, modules.clone());

    let missing = run_targeted_build_check_read_through(&package, modules.clone());
    assert_targeted_cache_differential(&off, &missing);
    assert_targeted_build_check_cache_summary(&missing, 0, 2, 0, 2, 0, 0, 2, 0);
    assert_eq!(
        build_check_cache_entries()
            .into_iter()
            .map(|entry| entry.key_input.module)
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from([
            Name::from_dotted("Fixture.A"),
            Name::from_dotted("Fixture.B"),
        ])
    );

    let hit = run_targeted_build_check_read_through(&package, modules);
    assert_targeted_cache_differential(&off, &hit);
    assert_targeted_build_check_cache_summary(&hit, 0, 2, 2, 0, 0, 0, 0, 0);
    assert_eq!(package_snapshot(&package), before);
}

#[test]
fn package_build_certs_check_leaf_observation_mode_matrix_preserves_artifacts() {
    let package = build_minimal_fixture("leaf-observation-mode-matrix");
    let before = package_snapshot(&package);

    for fuel in FUEL_MODES {
        for timings in TIMING_MODES {
            let result = run_package_build_certs(
                build_certs_check(common_options(package.path(), true))
                    .with_kernel_fuel_report(fuel)
                    .with_timings(timings),
            );

            assert_eq!(result.exit_code(), CommandExitCode::Success);
            assert_build_observation_mode(&result, fuel, timings, 1);
            assert_eq!(package_snapshot(&package), before);
        }
    }
}

#[test]
fn package_build_certs_check_interface_observation_mode_matrix_preserves_artifacts() {
    let package = build_synthetic_local_import_fixture("interface-observation-mode-matrix");
    let before = package_snapshot(&package);

    for fuel in FUEL_MODES {
        for timings in TIMING_MODES {
            let result = run_package_build_certs(
                build_certs_check(common_options(package.path(), true))
                    .with_kernel_fuel_report(fuel)
                    .with_timings(timings),
            );

            assert_eq!(result.exit_code(), CommandExitCode::Success);
            assert_build_observation_mode(&result, fuel, timings, 2);
            assert_eq!(package_snapshot(&package), before);
        }
    }
}

#[test]
fn package_build_check_cache_observation_modes_do_not_change_identity() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-observation-modes");
    let package_before = package_snapshot(&package);
    let mut expected_entries = None;

    for fuel in FUEL_MODES {
        for timings in TIMING_MODES {
            let result = run_package_build_certs(
                build_certs_check(common_options(package.path(), true))
                    .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
                    .with_build_check_cache_root(build_check_cache_base())
                    .with_kernel_fuel_report(fuel)
                    .with_timings(timings),
            );
            assert_eq!(result.exit_code(), CommandExitCode::Success);
            if let Some(command_timings) = result.timings.as_ref() {
                assert!(command_timings
                    .metrics
                    .iter()
                    .any(|metric| metric.field == "cache_lookup_ms"));
                let measurements = command_timings
                    .measurements
                    .as_ref()
                    .expect("enabled full read-through measurements");
                assert!(
                    measurement_counter(
                        measurements,
                        PerformanceMeasurementLabel::CacheToolIdentityBytes,
                    ) > 0
                );
                assert!(
                    measurement_counter(
                        measurements,
                        PerformanceMeasurementLabel::CacheBytesLoaded,
                    ) > 0
                );
                for targeted_label in [
                    PerformanceMeasurementLabel::CacheSupportSelected,
                    PerformanceMeasurementLabel::CacheContextHits,
                    PerformanceMeasurementLabel::CacheLivePrerequisiteChecks,
                    PerformanceMeasurementLabel::CacheTargetFreshBuilds,
                ] {
                    assert!(!has_measurement_counter(measurements, targeted_label));
                }
            } else {
                assert_eq!(timings, PackageTimingMode::Off);
            }
            if let Some(entries) = &expected_entries {
                assert_build_check_cache_summary(
                    &result,
                    "mode=read-through;hits=1;misses=0;stale=0;schema_misses=0;written=0;live_builds=1;trusted=false;build_evidence=false",
                );
                assert_eq!(&build_check_cache_entries(), entries);
            } else {
                assert_build_check_cache_summary(
                    &result,
                    "mode=read-through;hits=0;misses=1;stale=0;schema_misses=0;written=1;live_builds=1;trusted=false;build_evidence=false",
                );
                expected_entries = Some(build_check_cache_entries());
            }
            assert_eq!(package_snapshot(&package), package_before);
        }
    }
}

#[test]
fn package_build_check_cache_stale_tool_identity_misses_without_relabeling() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("cache-stale-tool-identity");
    let initial = run_build_check_read_through(&package);
    assert_eq!(initial.exit_code(), CommandExitCode::Success);
    let mut current = build_check_cache_entries()
        .pop()
        .expect("current cache entry");
    assert_eq!(current.schema, PACKAGE_BUILD_CHECK_RESULT_SCHEMA);
    assert_eq!(current.key_input.schema, PACKAGE_BUILD_CHECK_CACHE_SCHEMA);
    assert_eq!(current.key_input.tool_version, env!("CARGO_PKG_VERSION"));

    clear_build_check_cache();
    current.key_input.tool_version = "stale-tool-version".to_owned();
    current.key_input.tool_build_hash = package_file_hash(b"version-neutral stale tool identity");
    current.cache_key = package_build_check_cache_key(&current.key_input);
    let cache_dir = build_check_cache_dir_for_package(package.path());
    fs::create_dir_all(&cache_dir).unwrap();
    let cache_key = PackageCacheKeyDigest::from_cache_key(&current.cache_key).unwrap();
    fs::write(
        cache_dir.join(format!("{}.json", cache_key.as_str())),
        package_build_check_result_entry_json(&current),
    )
    .unwrap();

    let rebuilt = run_build_check_read_through(&package);
    assert_eq!(rebuilt.exit_code(), CommandExitCode::Success);
    assert_build_check_cache_summary(
        &rebuilt,
        "mode=read-through;hits=0;misses=1;stale=0;schema_misses=0;written=1;live_builds=1;trusted=false;build_evidence=false",
    );
    let entries = build_check_cache_entries();
    assert_eq!(entries.len(), 2);
    assert!(entries.iter().all(|entry| {
        entry.schema == PACKAGE_BUILD_CHECK_RESULT_SCHEMA
            && entry.key_input.schema == PACKAGE_BUILD_CHECK_CACHE_SCHEMA
    }));
    let versions = entries
        .iter()
        .map(|entry| entry.key_input.tool_version.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(versions.len(), 2);
    assert!(versions.contains(env!("CARGO_PKG_VERSION")));
    assert!(versions.contains("stale-tool-version"));
}

#[test]
fn package_build_certs_targeted_check_uses_shared_observation_coordinator() {
    let package = build_synthetic_local_import_fixture("targeted-observations");
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Fixture.B")])
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
            .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_build_observation_mode(
        &result,
        KernelFuelReportMode::Detailed,
        PackageTimingMode::Detailed,
        1,
    );
}

#[test]
fn targeted_authoring_differential_measurements_distinguish_read_through_and_warm_local_hit() {
    let _guard = build_check_cache_guard();
    let package = build_synthetic_local_import_fixture("targeted-summary-measurements");
    let selected = vec![Name::from_dotted("Fixture.B")];

    let read_through = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(selected.clone())
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(build_check_cache_base())
            .with_timings(PackageTimingMode::Summary),
    );
    assert_eq!(read_through.exit_code(), CommandExitCode::Success);
    let read_measurements = read_through
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("read-through measurements");
    assert_eq!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheSupportSelected
        ),
        1
    );
    assert_eq!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheLivePrerequisiteChecks,
        ),
        1
    );
    assert_eq!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheTargetFreshBuilds,
        ),
        1
    );
    assert_eq!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheAvoidedKernelChecks,
        ),
        0
    );
    assert!(!has_measurement_counter(
        read_measurements,
        PerformanceMeasurementLabel::CacheContextMisses,
    ));
    assert!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheLiveSupportElapsed,
        ) > 0
    );
    assert!(
        measurement_counter(
            read_measurements,
            PerformanceMeasurementLabel::CacheSourceInterfaceResolutionElapsed,
        ) > 0
    );

    let local_hit = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(selected)
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base())
            .with_timings(PackageTimingMode::Summary),
    );
    assert_eq!(local_hit.exit_code(), CommandExitCode::Success);
    assert_targeted_authoring_local_only(&local_hit, true);
    let local_measurements = local_hit
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("local-hit measurements");
    for (label, expected) in [
        (PerformanceMeasurementLabel::CacheSupportSelected, 1),
        (PerformanceMeasurementLabel::CacheContextHits, 1),
        (PerformanceMeasurementLabel::CacheContextMisses, 0),
        (PerformanceMeasurementLabel::CacheLivePrerequisiteChecks, 0),
        (PerformanceMeasurementLabel::CacheAvoidedKernelChecks, 1),
        (
            PerformanceMeasurementLabel::CacheAvoidedSourceInterfaceResolutions,
            1,
        ),
        (PerformanceMeasurementLabel::CacheTargetFreshBuilds, 1),
    ] {
        assert_eq!(measurement_counter(local_measurements, label), expected);
    }
    for label in [
        PerformanceMeasurementLabel::CacheToolIdentityBytes,
        PerformanceMeasurementLabel::CacheToolIdentityElapsed,
        PerformanceMeasurementLabel::CacheCurrentByteValidationElapsed,
        PerformanceMeasurementLabel::CacheReconstructionElapsed,
        PerformanceMeasurementLabel::CacheFreshTargetElapsed,
        PerformanceMeasurementLabel::CacheBytesLoaded,
    ] {
        assert!(
            measurement_counter(local_measurements, label) > 0,
            "{label:?}"
        );
    }
    assert_eq!(
        measurement_counter(
            local_measurements,
            PerformanceMeasurementLabel::CacheLiveSupportElapsed,
        ),
        0
    );
    assert_eq!(
        measurement_counter(
            local_measurements,
            PerformanceMeasurementLabel::CacheSourceInterfaceResolutionElapsed,
        ),
        0
    );
}

#[test]
fn targeted_authoring_differential_cache_off_and_no_support_local_hit_omit_tool_identity() {
    let _guard = build_check_cache_guard();
    let package = build_minimal_fixture("targeted-summary-no-support-tool");
    let selected = vec![Name::from_dotted("Proofs.Ai.Basic")];

    for mode in [
        PackageBuildCheckCacheMode::Off,
        PackageBuildCheckCacheMode::LocalHit,
    ] {
        let result = run_package_build_certs(
            build_certs_check(common_options(package.path(), true))
                .with_modules(selected.clone())
                .with_build_check_cache(mode)
                .with_build_check_cache_root(build_check_cache_base())
                .with_timings(PackageTimingMode::Summary),
        );
        assert_eq!(result.exit_code(), CommandExitCode::Success);
        let measurements = result
            .timings
            .as_ref()
            .and_then(|timings| timings.measurements.as_ref())
            .expect("summary measurements");
        assert!(!has_measurement_counter(
            measurements,
            PerformanceMeasurementLabel::CacheToolIdentityBytes,
        ));
        assert!(!has_measurement_counter(
            measurements,
            PerformanceMeasurementLabel::CacheToolIdentityElapsed,
        ));
        if mode == PackageBuildCheckCacheMode::LocalHit {
            assert_targeted_authoring_local_only(&result, false);
            assert_eq!(
                measurement_counter(
                    measurements,
                    PerformanceMeasurementLabel::CacheSupportSelected,
                ),
                0
            );
        }
    }
}

#[test]
fn targeted_authoring_differential_package_and_policy_namespaces_isolate_both_stores() {
    let _guard = build_check_cache_guard();
    let first = build_synthetic_local_import_fixture("cache-namespace-first");
    let second = build_synthetic_local_import_fixture("cache-namespace-second");
    let second_manifest_path = second.artifact_path(PACKAGE_MANIFEST_PATH);
    let second_manifest = fs::read_to_string(&second_manifest_path).unwrap();
    let second_manifest = second_manifest
        .replacen(
            "package = \"fixture-package\"",
            "package = \"fixture-package-isolated\"",
            1,
        )
        .replacen(
            "allow_custom_axioms = false",
            "allow_custom_axioms = true",
            1,
        );
    fs::write(&second_manifest_path, &second_manifest).unwrap();
    write_lock(&second, &second_manifest);
    let selected = vec![Name::from_dotted("Fixture.B")];
    let first_before = package_snapshot(&first);
    let second_before = package_snapshot(&second);

    let first_warm = run_targeted_build_check_read_through(&first, selected.clone());
    let second_warm = run_targeted_build_check_read_through(&second, selected.clone());

    assert_eq!(first_warm.exit_code(), CommandExitCode::Success);
    assert_eq!(second_warm.exit_code(), CommandExitCode::Success);
    let result_entries = build_check_cache_entries();
    assert_eq!(result_entries.len(), 2);
    assert_eq!(
        result_entries[0].cache_key, result_entries[1].cache_key,
        "the legacy module-key material must collide before namespace scoping"
    );
    let first_result_store = build_check_cache_dir_for_package(first.path());
    let second_result_store = build_check_cache_dir_for_package(second.path());
    let first_support_store = targeted_authoring_support_cache_dir(first.path());
    let second_support_store = targeted_authoring_support_cache_dir(second.path());
    assert_ne!(first_result_store, second_result_store);
    assert_ne!(first_support_store, second_support_store);
    for store in [
        &first_result_store,
        &second_result_store,
        &first_support_store,
        &second_support_store,
    ] {
        assert!(
            store.is_dir(),
            "missing namespaced store {}",
            store.display()
        );
        assert_eq!(
            fs::read_dir(store).unwrap().count(),
            1,
            "unexpected entries in {}",
            store.display()
        );
    }

    let first_hit = run_targeted_build_check_local_hit(&first, selected.clone());
    let second_hit = run_targeted_build_check_local_hit(&second, selected);
    assert_targeted_authoring_local_only(&first_hit, true);
    assert_targeted_authoring_local_only(&second_hit, true);
    assert_eq!(package_snapshot(&first), first_before);
    assert_eq!(package_snapshot(&second), second_before);
}

#[test]
fn package_build_certs_changed_no_rebuild_success_is_finalized_once() {
    let package = build_minimal_fixture("changed-no-rebuild-observations");
    init_git_package(&package, true);
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_changed()
            .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let timings = result.timings.as_ref().expect("early success has timings");
    let measurements = timings
        .measurements
        .as_ref()
        .expect("early success has finalized common measurements");
    assert!(measurements.declarations.is_empty());
    assert_eq!(result.render_json().matches("\"timings\":").count(), 1);
}

#[test]
fn package_build_certs_validation_failure_is_finalized_once() {
    let package = build_minimal_fixture("validation-failure-observations");
    let result = run_package_build_certs(
        build_certs_write(common_options(package.path(), true))
            .with_modules(vec![Name::from_dotted("Proofs.Ai.Basic")])
            .with_timings(PackageTimingMode::Summary),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert!(result.timings.is_some());
    assert_eq!(result.render_json().matches("\"timings\":").count(), 1);
}

#[test]
fn package_build_certs_frontend_failure_is_finalized_once() {
    let package = build_minimal_fixture("frontend-failure-observations");
    install_frontend_failure(&package, "Proofs/Ai/Basic/source.npa", "Proofs.Ai.Basic");
    let result = run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed)
            .with_timings(PackageTimingMode::Detailed),
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let measurements = result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .expect("frontend failure has finalized common measurements");
    assert!(measurements.declarations.is_empty());
    assert_eq!(result.render_json().matches("\"timings\":").count(), 1);
}

#[test]
fn package_build_check_cache_read_through_preserves_live_failure() {
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
    let certificate = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
    let mut parts = certificate.into_parts();
    parts.imports.clear();
    let certificate = npa_cert::ModuleCert::from_parts(parts);
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
        let certificate =
            npa_cert::decode_module_cert(&fs::read(&certificate_path).unwrap()).unwrap();
        let mut parts = certificate.into_parts();
        parts.imports.clear();
        let certificate = npa_cert::ModuleCert::from_parts(parts);
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
    let certificate = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
    let mut parts = certificate.into_parts();
    parts.imports[0].export_hash = [0; 32];
    let certificate = npa_cert::ModuleCert::from_parts(parts);
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
fn fixed_proofs_package_fuel_modes_are_byte_and_identity_neutral_with_timings_off() {
    let _guard = build_check_cache_guard();
    let root = repo_root().join("testdata/package/proofs");
    let before = path_snapshot(&root);
    let expected_declaration_hashes = package_declaration_hashes(&root);
    let manifest_source = fs::read_to_string(root.join(PACKAGE_MANIFEST_PATH)).unwrap();
    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    let expected_lock = build_package_lock_from_package_root(
        &validated,
        &root,
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap()
    .canonical_json()
    .unwrap();
    assert_eq!(
        fs::read(root.join(LOCK_PATH)).unwrap(),
        expected_lock.as_bytes()
    );

    let mut expected_json = None;
    let mut expected_cache_entries = None;
    for fuel in FUEL_MODES {
        let cache_before = build_check_cache_entries();
        let result = run_package_build_certs(
            build_certs_check(common_options(&root, true))
                .with_build_check_cache(PackageBuildCheckCacheMode::Off)
                .with_kernel_fuel_report(fuel)
                .with_timings(PackageTimingMode::Off),
        );

        assert_eq!(result.exit_code(), CommandExitCode::Success);
        assert!(result.diagnostics.is_empty());
        assert!(result.timings.is_none());
        assert!(result
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.kernel_fuel.is_none()));
        let json = result.render_json();
        if let Some(expected) = &expected_json {
            assert_eq!(&json, expected);
        } else {
            expected_json = Some(json);
        }
        assert_eq!(path_snapshot(&root), before);
        assert_eq!(
            package_declaration_hashes(&root),
            expected_declaration_hashes
        );
        let lock = build_package_lock_from_package_root(
            &validated,
            &root,
            PackagePath::new(PACKAGE_MANIFEST_PATH),
        )
        .unwrap()
        .canonical_json()
        .unwrap();
        assert_eq!(lock, expected_lock);
        assert_eq!(build_check_cache_entries(), cache_before);

        let cached_result = run_package_build_certs(
            build_certs_check(common_options(&root, true))
                .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
                .with_build_check_cache_root(build_check_cache_base())
                .with_kernel_fuel_report(fuel)
                .with_timings(PackageTimingMode::Off),
        );
        assert_eq!(cached_result.exit_code(), CommandExitCode::Success);
        let entries = build_check_cache_entries();
        if let Some(expected) = &expected_cache_entries {
            assert_eq!(&entries, expected);
        } else {
            assert!(!entries.is_empty());
            expected_cache_entries = Some(entries);
        }
        assert_eq!(path_snapshot(&root), before);
    }
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

#[test]
fn package_build_certs_check_accepts_current_std_producer_profile_fixture() {
    let package = TestPackage::new("current-std-producer-profile");
    let fixture = repo_root().join("testdata/package/npa-std");
    for relative in [
        "Std/Logic/Eq/source.npa",
        "Std/Logic/Eq/certificate.npcert",
        "Std/Nat/Basic/source.npa",
        "Std/Nat/Basic/certificate.npcert",
    ] {
        write_artifact(
            &package,
            relative,
            &fs::read(fixture.join(relative)).unwrap(),
        );
    }
    let manifest = fs::read_to_string(fixture.join(PACKAGE_MANIFEST_PATH))
        .unwrap()
        .replace(
            "std-library-legacy-core-builder",
            "std-library-core-builder",
        );
    write_artifact(&package, PACKAGE_MANIFEST_PATH, manifest.as_bytes());
    write_lock(&package, &manifest);

    let result = run_package_build_certs_check(common_options(package.path(), true));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
}

fn run_build_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check(common_options(package.path(), true))
}

fn run_build_check_read_through(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(build_check_cache_base()),
    )
}

fn run_targeted_build_check(
    package: &TestPackage,
    modules: Vec<Name>,
) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true)).with_modules(modules),
    )
}

fn run_targeted_build_check_read_through(
    package: &TestPackage,
    modules: Vec<Name>,
) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(build_check_cache_base()),
    )
}

fn run_targeted_build_check_local_hit(
    package: &TestPackage,
    modules: Vec<Name>,
) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_modules(modules)
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base()),
    )
}

fn run_changed_build_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(build_certs_check(common_options(package.path(), true)).with_changed())
}

fn run_changed_build_check_read_through(
    package: &TestPackage,
) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_changed()
            .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough)
            .with_build_check_cache_root(build_check_cache_base()),
    )
}

fn run_changed_build_check_local_hit(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(
        build_certs_check(common_options(package.path(), true))
            .with_changed()
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit)
            .with_build_check_cache_root(build_check_cache_base()),
    )
}

fn run_refresh_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs(refresh_artifacts_check(common_options(
        package.path(),
        true,
    )))
}

fn assert_build_observation_mode(
    result: &CommandResult,
    fuel: KernelFuelReportMode,
    timings: PackageTimingMode,
    expected_declarations: usize,
) {
    let Some(command_timings) = result.timings.as_ref() else {
        assert_eq!(timings, PackageTimingMode::Off);
        return;
    };
    assert_ne!(timings, PackageTimingMode::Off);
    let measurements = command_timings
        .measurements
        .as_ref()
        .expect("enabled build timings include common measurements");
    assert!(measurement_counter(measurements, PerformanceMeasurementLabel::KernelCheckCalls) > 0);
    if timings == PackageTimingMode::Detailed {
        assert_eq!(measurements.declarations.len(), expected_declarations);
        assert_eq!(
            measurements.declaration_details.attempted,
            u64::try_from(expected_declarations).unwrap()
        );
        assert!(measurements.declarations.iter().all(|declaration| {
            declaration.term_nodes > 0
                && declaration.kernel.is_some() == (fuel == KernelFuelReportMode::Detailed)
        }));
    } else {
        assert!(measurements.declarations.is_empty());
    }
}

fn measurement_counter(
    measurements: &PerformanceMeasurementReport,
    label: PerformanceMeasurementLabel,
) -> u64 {
    measurements
        .counters
        .iter()
        .find(|counter| counter.label == label)
        .map(|counter| counter.value)
        .expect("kernel counter is present")
}

fn has_measurement_counter(
    measurements: &PerformanceMeasurementReport,
    label: PerformanceMeasurementLabel,
) -> bool {
    measurements
        .counters
        .iter()
        .any(|counter| counter.label == label)
}

fn assert_targeted_authoring_local_only(result: &CommandResult, locally_accelerated: bool) {
    let diagnostics = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "targeted_authoring_cache_local_only")
        .collect::<Vec<_>>();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::GeneratedArtifact);
    assert_eq!(
        diagnostic.field.as_deref(),
        Some("targeted_authoring_cache")
    );
    assert_eq!(
        diagnostic.actual_value.as_deref(),
        Some(if locally_accelerated {
            "trusted=false;build_evidence=false;proof_evidence=false;locally_accelerated=true"
        } else {
            "trusted=false;build_evidence=false;proof_evidence=false;locally_accelerated=false"
        })
    );
}

fn build_check_cache_guard() -> BuildCheckCacheGuard {
    let guard = BUILD_CHECK_CACHE_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    clear_build_check_cache();
    BuildCheckCacheGuard { _lock: guard }
}

fn clear_build_check_cache() {
    let base = build_check_cache_base();
    if base.exists() {
        fs::remove_dir_all(base).unwrap();
    }
}

fn build_check_cache_entries() -> Vec<npa_package::PackageBuildCheckResultEntry> {
    let mut entries = build_check_cache_store_dirs()
        .into_iter()
        .flat_map(|path| fs::read_dir(path).unwrap().filter_map(Result::ok))
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .map(|entry| {
            parse_package_build_check_result_entry_json(&fs::read_to_string(entry.path()).unwrap())
                .unwrap()
        })
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| left.cache_key.cmp(&right.cache_key));
    entries
}

fn build_check_cache_base() -> PathBuf {
    fs::canonicalize(std::env::temp_dir())
        .unwrap()
        .join(format!(
            "npa-cli-package-build-check-cache-{}",
            std::process::id()
        ))
}

fn build_check_cache_store_dirs() -> Vec<PathBuf> {
    let packages = build_check_cache_base().join("packages");
    if !packages.exists() {
        return Vec::new();
    }
    fs::read_dir(packages)
        .unwrap()
        .filter_map(Result::ok)
        .map(|entry| {
            entry
                .path()
                .join(PackageCacheStoreVersion::BUILD_CHECK_RESULT.as_str())
        })
        .filter(|path| path.is_dir())
        .collect()
}

fn build_check_cache_dir_for_package(package_root: &Path) -> PathBuf {
    let manifest_source = fs::read_to_string(package_root.join(PACKAGE_MANIFEST_PATH)).unwrap();
    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    let namespace = package_build_check_cache_namespace_digest(&validated);
    build_check_cache_base()
        .join(PackageCacheStoreLayout::build_check_result(&namespace).relative_path())
}

fn targeted_authoring_support_cache_dir(package_root: &Path) -> PathBuf {
    let manifest_source = fs::read_to_string(package_root.join(PACKAGE_MANIFEST_PATH)).unwrap();
    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    let namespace = package_build_check_cache_namespace_digest(&validated);
    build_check_cache_base()
        .join(PackageCacheStoreLayout::targeted_authoring_support(&namespace).relative_path())
}

fn targeted_authoring_support_entries(
    package_root: &Path,
) -> Vec<TargetedAuthoringSupportContextEntry> {
    let directory = targeted_authoring_support_cache_dir(package_root);
    if !directory.exists() {
        return Vec::new();
    }
    let mut entries = fs::read_dir(directory)
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .map(|entry| {
            parse_targeted_authoring_support_context_entry(&fs::read(entry.path()).unwrap())
                .unwrap()
        })
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| left.cache_key.cmp(&right.cache_key));
    entries
}

fn targeted_authoring_support_entry_bytes(package_root: &Path) -> Vec<Vec<u8>> {
    let directory = targeted_authoring_support_cache_dir(package_root);
    if !directory.exists() {
        return Vec::new();
    }
    let mut entries = fs::read_dir(directory)
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .map(|entry| (entry.file_name(), fs::read(entry.path()).unwrap()))
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    entries.into_iter().map(|(_, bytes)| bytes).collect()
}

fn only_targeted_authoring_support_entry_path(package_root: &Path) -> PathBuf {
    let entries = fs::read_dir(targeted_authoring_support_cache_dir(package_root))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    entries.into_iter().next().unwrap().path()
}

fn only_build_check_cache_store_dir() -> PathBuf {
    let stores = build_check_cache_store_dirs();
    assert_eq!(stores.len(), 1);
    stores.into_iter().next().unwrap()
}

fn only_build_check_cache_entry_path() -> PathBuf {
    let entries = fs::read_dir(only_build_check_cache_store_dir())
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    entries.into_iter().next().unwrap().path()
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

#[allow(clippy::too_many_arguments)]
fn assert_targeted_build_check_cache_summary(
    result: &CommandResult,
    support_live_checked: usize,
    targets_live_built: usize,
    target_result_cache_hits: usize,
    target_result_cache_misses: usize,
    target_result_cache_stale: usize,
    target_result_cache_schema_misses: usize,
    target_result_entries_written: usize,
    support_context_entries_written: usize,
) {
    assert_build_check_cache_summary(
        result,
        &format!(
            "mode=read-through;support_live_checked={support_live_checked};targets_live_built={targets_live_built};target_result_cache_hits={target_result_cache_hits};target_result_cache_misses={target_result_cache_misses};target_result_cache_stale={target_result_cache_stale};target_result_cache_schema_misses={target_result_cache_schema_misses};target_result_entries_written={target_result_entries_written};support_context_cache_hits=0;support_context_entries_written={support_context_entries_written};support_checks_avoided=0;avoided_source_interface_resolutions=0;trusted=false;build_evidence=false"
        ),
    );
}

fn assert_targeted_cache_differential(off: &CommandResult, cached: &CommandResult) {
    assert_eq!(cached.exit_code(), off.exit_code());
    assert_eq!(cached.command, off.command);
    assert_eq!(cached.root, off.root);
    assert_eq!(cached.artifacts, off.artifacts);
    assert_eq!(
        cached
            .diagnostics
            .iter()
            .filter(|diagnostic| { !is_targeted_cache_diagnostic(&diagnostic.reason_code) })
            .collect::<Vec<_>>(),
        off.diagnostics.iter().collect::<Vec<_>>()
    );
    let mut normalized_cached = cached.clone();
    normalized_cached
        .diagnostics
        .retain(|diagnostic| !is_targeted_cache_diagnostic(&diagnostic.reason_code));
    assert_eq!(normalized_cached.render_json(), off.render_json());
    assert_eq!(normalized_cached.render_human(), off.render_human());
}

fn assert_targeted_authoring_differential(off: &CommandResult, local_hit: &CommandResult) {
    assert_eq!(local_hit.exit_code(), off.exit_code());
    assert_eq!(local_hit.command, off.command);
    assert_eq!(local_hit.root, off.root);
    assert_eq!(local_hit.artifacts, off.artifacts);
    assert_eq!(
        local_hit
            .diagnostics
            .iter()
            .filter(|diagnostic| { !is_targeted_cache_diagnostic(&diagnostic.reason_code) })
            .collect::<Vec<_>>(),
        off.diagnostics.iter().collect::<Vec<_>>()
    );
}

fn is_targeted_cache_diagnostic(reason_code: &str) -> bool {
    matches!(
        reason_code,
        "build_check_cache_summary"
            | "build_check_cache_unavailable"
            | "targeted_authoring_cache_summary"
            | "targeted_authoring_cache_entry_stale"
            | "targeted_authoring_cache_entry_schema_miss"
            | "targeted_authoring_cache_entry_invalid"
            | "targeted_authoring_cache_hit_bypassed"
            | "targeted_authoring_cache_publication_failed"
            | "targeted_authoring_module_ineligible"
            | "targeted_authoring_cache_local_only"
    )
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

fn install_universe_alias_failure(package: &TestPackage, source_path: &str, module_name: &str) {
    write_artifact(
        package,
        source_path,
        UNIVERSE_ALIAS_FAILURE_SOURCE.as_bytes(),
    );
    let source_hash =
        format_package_hash(&package_file_hash(UNIVERSE_ALIAS_FAILURE_SOURCE.as_bytes()));
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
    path_snapshot(package.path())
}

fn path_snapshot(root: &Path) -> BTreeMap<String, Option<Vec<u8>>> {
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
    visit(root, root, &mut snapshot);
    snapshot
}

fn package_declaration_hashes(root: &Path) -> BTreeMap<String, Vec<npa_cert::DeclHashes>> {
    fn visit(
        root: &Path,
        current: &Path,
        hashes: &mut BTreeMap<String, Vec<npa_cert::DeclHashes>>,
    ) {
        let mut entries = fs::read_dir(current)
            .unwrap()
            .map(|entry| entry.unwrap())
            .collect::<Vec<_>>();
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            if path.is_dir() {
                visit(root, &path, hashes);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("npcert") {
                let certificate = npa_cert::decode_module_cert(&fs::read(&path).unwrap()).unwrap();
                hashes.insert(
                    path.strip_prefix(root)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                    certificate
                        .declarations()
                        .iter()
                        .map(|declaration| declaration.hashes.clone())
                        .collect(),
                );
            }
        }
    }

    let mut hashes = BTreeMap::new();
    visit(root, root, &mut hashes);
    hashes
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

fn git_status_snapshot(package: &TestPackage) -> Vec<u8> {
    let output = Command::new("/usr/bin/git")
        .args(["status", "--short", "--untracked-files=all"])
        .current_dir(package.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
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

fn build_targeted_authoring_diamond_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a =
        "theorem a_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let source_b = "import Fixture.A\n\ntheorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";
    let source_c = "import Fixture.A\n\ntheorem c_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";
    let source_d = "import Fixture.B\nimport Fixture.C\n\ntheorem d_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @b_use P (@c_use P p)\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_b, verified_b, interface_b) = compile_fixture_module(
        1,
        "Fixture.B",
        source_b,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );
    let (cert_c, verified_c, interface_c) = compile_fixture_module(
        2,
        "Fixture.C",
        source_c,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );
    let (cert_d, _, _) = compile_fixture_module(
        3,
        "Fixture.D",
        source_d,
        &[verified_a, verified_b, verified_c],
        &[interface_a, interface_b, interface_c],
    );

    let artifacts = [
        (
            "Fixture.A",
            "Fixture/A",
            source_a,
            cert_a.as_slice(),
            Vec::new(),
        ),
        (
            "Fixture.B",
            "Fixture/B",
            source_b,
            cert_b.as_slice(),
            vec![Name::from_dotted("Fixture.A")],
        ),
        (
            "Fixture.C",
            "Fixture/C",
            source_c,
            cert_c.as_slice(),
            vec![Name::from_dotted("Fixture.A")],
        ),
        (
            "Fixture.D",
            "Fixture/D",
            source_d,
            cert_d.as_slice(),
            vec![
                Name::from_dotted("Fixture.B"),
                Name::from_dotted("Fixture.C"),
            ],
        ),
    ];
    let mut modules = Vec::new();
    for (module, directory, source, certificate, imports) in artifacts {
        let source_path = format!("{directory}/source.npa");
        let certificate_path = format!("{directory}/certificate.npcert");
        write_artifact(&package, &source_path, source.as_bytes());
        write_artifact(&package, &certificate_path, certificate);
        modules.push(generated_manifest_module(
            module,
            &source_path,
            &certificate_path,
            source.as_bytes(),
            certificate,
            imports,
        ));
    }
    modules.rotate_right(1);
    let manifest_source = fixture_manifest(&modules);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_targeted_authoring_multi_target_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a =
        "theorem a_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let source_b = "import Fixture.A\n\ntheorem b_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";
    let source_c = "import Fixture.A\n\ntheorem c_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @a_id P p\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_b, _, _) = compile_fixture_module(
        1,
        "Fixture.B",
        source_b,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );
    let (cert_c, _, _) = compile_fixture_module(
        2,
        "Fixture.C",
        source_c,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );

    for (source_path, certificate_path, source, certificate) in [
        (
            "Fixture/A/source.npa",
            "Fixture/A/certificate.npcert",
            source_a,
            cert_a.as_slice(),
        ),
        (
            "Fixture/B/source.npa",
            "Fixture/B/certificate.npcert",
            source_b,
            cert_b.as_slice(),
        ),
        (
            "Fixture/C/source.npa",
            "Fixture/C/certificate.npcert",
            source_c,
            cert_c.as_slice(),
        ),
    ] {
        write_artifact(&package, source_path, source.as_bytes());
        write_artifact(&package, certificate_path, certificate);
    }

    let modules = [
        generated_manifest_module(
            "Fixture.B",
            "Fixture/B/source.npa",
            "Fixture/B/certificate.npcert",
            source_b.as_bytes(),
            &cert_b,
            vec![Name::from_dotted("Fixture.A")],
        ),
        generated_manifest_module(
            "Fixture.C",
            "Fixture/C/source.npa",
            "Fixture/C/certificate.npcert",
            source_c.as_bytes(),
            &cert_c,
            vec![Name::from_dotted("Fixture.A")],
        ),
        generated_manifest_module(
            "Fixture.A",
            "Fixture/A/source.npa",
            "Fixture/A/certificate.npcert",
            source_a.as_bytes(),
            &cert_a,
            Vec::new(),
        ),
    ];
    let manifest_source = fixture_manifest(&modules);
    let certificate_field = "certificate = \"Fixture/C/certificate.npcert\"\n";
    let manifest_source = manifest_source.replacen(
        certificate_field,
        &format!("{certificate_field}producer_profile = \"unsupported-fixture-profile\"\n"),
        1,
    );
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_targeted_authoring_post_target_support_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let source_a = "def Carrier : Type := Prop\n";
    let source_b = "import Fixture.A\n\ndef Alias : Type := Carrier\n";
    let source_c = "import Fixture.B\n\ndef use : Type := Alias\n";

    let (cert_a, verified_a, interface_a) =
        compile_fixture_module(0, "Fixture.A", source_a, &[], &[]);
    let (cert_b, verified_b, interface_b) = compile_fixture_module(
        1,
        "Fixture.B",
        source_b,
        std::slice::from_ref(&verified_a),
        std::slice::from_ref(&interface_a),
    );
    let output_c =
        compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy(
            FileId(2),
            Name::from_dotted("Fixture.C"),
            source_c,
            &[&verified_b],
            &[&verified_a, &verified_b],
            std::slice::from_ref(&interface_b),
            &HumanCompileOptions::default(),
            &AxiomPolicy::normal(),
        )
        .unwrap();
    let cert_c = npa_cert::encode_module_cert(&output_c.certificate).unwrap();

    for (source_path, certificate_path, source, certificate) in [
        (
            "Fixture/A/source.npa",
            "Fixture/A/certificate.npcert",
            source_a,
            cert_a.as_slice(),
        ),
        (
            "Fixture/B/source.npa",
            "Fixture/B/certificate.npcert",
            source_b,
            cert_b.as_slice(),
        ),
        (
            "Fixture/C/source.npa",
            "Fixture/C/certificate.npcert",
            source_c,
            cert_c.as_slice(),
        ),
    ] {
        write_artifact(&package, source_path, source.as_bytes());
        write_artifact(&package, certificate_path, certificate);
    }

    let modules = [
        generated_manifest_module(
            "Fixture.A",
            "Fixture/A/source.npa",
            "Fixture/A/certificate.npcert",
            source_a.as_bytes(),
            &cert_a,
            Vec::new(),
        ),
        generated_manifest_module(
            "Fixture.B",
            "Fixture/B/source.npa",
            "Fixture/B/certificate.npcert",
            source_b.as_bytes(),
            &cert_b,
            vec![Name::from_dotted("Fixture.A")],
        ),
        generated_manifest_module(
            "Fixture.C",
            "Fixture/C/source.npa",
            "Fixture/C/certificate.npcert",
            source_c.as_bytes(),
            &cert_c,
            vec![Name::from_dotted("Fixture.B")],
        ),
    ];
    let manifest_source = fixture_manifest(&modules);
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
    write_lock(&package, &manifest_source);
    package
}

fn build_synthetic_external_support_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let external_source =
        "theorem external_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let support_source = "import Fixture.External.Dependency\n\ntheorem support_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @external_id P p\n";
    let target_source = "import Fixture.Support\n\ntheorem target_use :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => @support_use P p\n";

    let (external_cert, external_verified, external_interface) =
        compile_fixture_module(0, "Fixture.External.Dependency", external_source, &[], &[]);
    let (support_cert, support_verified, support_interface) = compile_fixture_module(
        1,
        "Fixture.Support",
        support_source,
        std::slice::from_ref(&external_verified),
        std::slice::from_ref(&external_interface),
    );
    let (target_cert, _, _) = compile_fixture_module(
        2,
        "Fixture.Target",
        target_source,
        std::slice::from_ref(&support_verified),
        std::slice::from_ref(&support_interface),
    );

    let external_cert_path =
        "vendor/fixture-external/Fixture/External/Dependency/certificate.npcert";
    let support_source_path = "Fixture/Support/source.npa";
    let support_cert_path = "Fixture/Support/certificate.npcert";
    let target_source_path = "Fixture/Target/source.npa";
    let target_cert_path = "Fixture/Target/certificate.npcert";
    write_artifact(&package, external_cert_path, &external_cert);
    write_artifact(&package, support_source_path, support_source.as_bytes());
    write_artifact(&package, support_cert_path, &support_cert);
    write_artifact(&package, target_source_path, target_source.as_bytes());
    write_artifact(&package, target_cert_path, &target_cert);

    let imports = [generated_manifest_import(
        "Fixture.External.Dependency",
        external_cert_path,
        &external_cert,
    )];
    let support = generated_manifest_module(
        "Fixture.Support",
        support_source_path,
        support_cert_path,
        support_source.as_bytes(),
        &support_cert,
        vec![Name::from_dotted("Fixture.External.Dependency")],
    );
    let target = generated_manifest_module(
        "Fixture.Target",
        target_source_path,
        target_cert_path,
        target_source.as_bytes(),
        &target_cert,
        vec![Name::from_dotted("Fixture.Support")],
    );
    let manifest_source = fixture_manifest_with_imports(&imports, &[target, support]);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        manifest_source,
    )
    .unwrap();
    package
}

fn install_external_import_cycle(package: &TestPackage) {
    let base_path =
        package.artifact_path("vendor/fixture-external/Fixture/External/Base/certificate.npcert");
    let leaf_path =
        package.artifact_path("vendor/fixture-external/Fixture/External/Leaf/certificate.npcert");
    let base = npa_cert::decode_module_cert(&fs::read(&base_path).unwrap()).unwrap();
    let leaf = npa_cert::decode_module_cert(&fs::read(leaf_path).unwrap()).unwrap();
    let mut parts = base.into_parts();
    parts.imports.push(npa_cert::ImportEntry {
        module: leaf.header().module.clone(),
        export_hash: leaf.hashes().export_hash,
        certificate_hash: Some(leaf.hashes().certificate_hash),
    });
    let base = npa_cert::ModuleCert::from_parts(parts);
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
        export_hash: output.certificate.hashes().export_hash,
        certificate_hash: Some(output.certificate.hashes().certificate_hash),
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
        export_hash: PackageHash::from(cert.hashes().export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes().axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes().certificate_hash),
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
        export_hash: PackageHash::from(cert.hashes().export_hash),
        certificate_hash: PackageHash::from(cert.hashes().certificate_hash),
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

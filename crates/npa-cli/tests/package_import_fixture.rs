use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::{AxiomPolicy, ModuleCert, Name, VerifiedModule};
use npa_cli::args::{PackageBuildSelection, PackageChecker};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{
    build_certs_check, common_options, refresh_artifacts_check, verify_certs_full,
};
use npa_cli::package_build::{
    run_package_build_certs, run_package_build_certs_check, run_package_build_certs_write,
};
use npa_cli::package_hashes::run_package_check_hashes;
use npa_cli::package_verify::run_package_verify_certs;
use npa_frontend::{
    compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy, FileId,
    HumanCompileOptions, HumanImportedSourceInterface, HumanSourceInterface,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_package_publish_plan_json, PackageCheckerMode,
    PackageDownstreamImportModule, PackageHash, PackageId, PackagePath, PackageVersion,
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
const INTERFACE_CLOSURE_LOCK: &str = "generated/package-lock.json";
const INTERFACE_A: &str = "InterfaceClosure.A";
const INTERFACE_B: &str = "InterfaceClosure.B";
const INTERFACE_C: &str = "InterfaceClosure.C";
const INTERFACE_D: &str = "InterfaceClosure.D";
const LEGACY_SUPPORT: &str = "Std.Nat.Basic";
const LEGACY_SUPPORT_TARGET: &str = "LegacySupport.Target";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestFixture {
    path: PathBuf,
}

impl TestFixture {
    fn empty(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-import-fixture-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

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
fn package_import_fixture_accepts_interface_closure_direct_b_available_a() {
    let fixture = materialize_interface_closure_fixture("interface-valid");

    let build = run_build_check(&fixture);
    assert_eq!(build.exit_code(), CommandExitCode::Success);
    assert!(build.diagnostics.is_empty());

    let targeted_build = run_package_build_certs(
        build_certs_check(common_options(fixture.path(), true))
            .with_modules(vec![Name::from_dotted(INTERFACE_C)]),
    );
    assert_eq!(
        targeted_build.exit_code(),
        CommandExitCode::Success,
        "diagnostics={:?}",
        targeted_build.diagnostics
    );
    assert_eq!(targeted_build.diagnostics.len(), 1);
    assert_eq!(
        targeted_build.diagnostics[0].reason_code,
        "package_build_selection"
    );

    let hashes = run_hashes(&fixture);
    assert_eq!(hashes.exit_code(), CommandExitCode::Success);
    assert!(hashes.diagnostics.is_empty());

    for checker in [PackageChecker::Reference, PackageChecker::Fast] {
        let verify = run_verify_with_checker(&fixture, checker);
        assert_eq!(verify.exit_code(), CommandExitCode::Success);
        assert!(verify.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::ReferenceVerifier
                || diagnostic.kind == DiagnosticKind::FastVerifier
        }));
    }

    let c_cert = fs::read(fixture.artifact_path("InterfaceClosure/C/certificate.npcert")).unwrap();
    let c_cert = npa_cert::decode_module_cert(&c_cert).unwrap();
    let imports = c_cert
        .imports
        .iter()
        .map(|import| import.module.as_dotted())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        imports,
        BTreeSet::from([INTERFACE_A.to_owned(), INTERFACE_B.to_owned()])
    );
    assert!(
        fs::read_to_string(fixture.artifact_path("InterfaceClosure/C/source.npa"))
            .unwrap()
            .lines()
            .any(|line| line == format!("import {INTERFACE_B}"))
    );
    assert!(
        !fs::read_to_string(fixture.artifact_path("InterfaceClosure/C/source.npa"))
            .unwrap()
            .lines()
            .any(|line| line == format!("import {INTERFACE_A}"))
    );
}

#[test]
fn package_import_fixture_write_rejects_direct_import_hidden_by_certificate_closure() {
    let fixture = materialize_interface_closure_fixture("interface-write-direct-import-drift");
    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest = fs::read_to_string(&manifest_path).unwrap();
    let drifted_manifest = manifest.replacen(
        "imports = [\"InterfaceClosure.B\"]",
        "imports = [\"InterfaceClosure.A\", \"InterfaceClosure.B\"]",
        1,
    );
    assert_ne!(manifest, drifted_manifest);
    fs::write(&manifest_path, drifted_manifest).unwrap();
    let certificate_path = fixture.artifact_path("InterfaceClosure/C/certificate.npcert");
    let certificate_before = fs::read(&certificate_path).unwrap();
    let lock_path = fixture.artifact_path(INTERFACE_CLOSURE_LOCK);
    let lock_before = fs::read(&lock_path).unwrap();

    let result = run_package_build_certs_write(common_options(fixture.path(), true));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "manifest_source_imports_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some(INTERFACE_C));
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
    assert_eq!(fs::read(lock_path).unwrap(), lock_before);
}

#[test]
fn package_import_fixture_skip_hashes_still_rejects_direct_import_drift() {
    let fixture = materialize_interface_closure_fixture("interface-skip-hashes-import-drift");
    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest = fs::read_to_string(&manifest_path).unwrap();
    let drifted_manifest = manifest.replacen(
        "imports = [\"InterfaceClosure.B\"]",
        "imports = [\"InterfaceClosure.A\", \"InterfaceClosure.B\"]",
        1,
    );
    assert_ne!(manifest, drifted_manifest);
    fs::write(&manifest_path, drifted_manifest).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "build-certs", "--root"])
        .arg(fixture.path())
        .arg("--check")
        .arg("--json")
        .env("NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS", "1")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("\"reason_code\":\"manifest_source_imports_mismatch\""),
        "{stdout}"
    );
    assert!(
        stdout.contains(&format!("\"module\":\"{INTERFACE_C}\"")),
        "{stdout}"
    );
}

#[test]
fn package_import_fixture_targeted_check_prioritizes_support_direct_import_drift() {
    let fixture =
        materialize_interface_closure_with_dependent_fixture("interface-targeted-support-drift");
    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest = fs::read_to_string(&manifest_path).unwrap();
    let drifted_manifest = manifest.replacen(
        "imports = [\"InterfaceClosure.B\"]",
        "imports = [\"InterfaceClosure.A\", \"InterfaceClosure.B\"]",
        1,
    );
    assert_ne!(manifest, drifted_manifest);
    let certificate_path = fixture.artifact_path("InterfaceClosure/C/certificate.npcert");
    let certificate_hash =
        format_package_hash(&package_file_hash(&fs::read(certificate_path).unwrap()));
    let expected_hash = format!("expected_certificate_file_hash = \"{certificate_hash}\"");
    let stale_hash = format!("expected_certificate_file_hash = \"{ZERO_HASH}\"");
    let drifted_manifest = drifted_manifest.replacen(&expected_hash, &stale_hash, 1);
    assert!(drifted_manifest.contains(&stale_hash));
    fs::write(&manifest_path, drifted_manifest).unwrap();
    let mut options = build_certs_check(common_options(fixture.path(), true));
    options.selection = PackageBuildSelection::Modules(vec![Name::from_dotted(INTERFACE_D)]);

    let result = run_package_build_certs(options);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason_code == "manifest_source_imports_mismatch"
                && diagnostic.module.as_deref() == Some(INTERFACE_C)
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn package_import_fixture_targeted_modes_reject_legacy_support_source_import_drift() {
    for refresh in [false, true] {
        let fixture = materialize_legacy_support_fixture(if refresh {
            "targeted-refresh-legacy-support-drift"
        } else {
            "targeted-check-legacy-support-drift"
        });
        let source_path = fixture.artifact_path("Std/Nat/Basic/source.npa");
        let source = fs::read_to_string(&source_path).unwrap();
        let drifted_source = format!("{source}\nimport Std.Logic.Eq\n");
        fs::write(&source_path, &drifted_source).unwrap();
        let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
        let manifest = fs::read_to_string(&manifest_path).unwrap();
        let drifted_manifest = replace_fixture_module_field(
            &manifest,
            LEGACY_SUPPORT,
            "expected_source_hash",
            &format!(
                "\"{}\"",
                format_package_hash(&package_file_hash(drifted_source.as_bytes()))
            ),
        );
        assert_ne!(manifest, drifted_manifest);
        fs::write(&manifest_path, drifted_manifest).unwrap();
        let options = if refresh {
            refresh_artifacts_check(common_options(fixture.path(), true))
        } else {
            build_certs_check(common_options(fixture.path(), true))
        }
        .with_modules(vec![Name::from_dotted(LEGACY_SUPPORT_TARGET)]);

        let result = run_package_build_certs(options);

        assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
        assert!(
            result.diagnostics.iter().any(|diagnostic| {
                diagnostic.reason_code == "manifest_source_imports_mismatch"
                    && diagnostic.module.as_deref() == Some(LEGACY_SUPPORT)
            }),
            "refresh={refresh}, diagnostics={:?}",
            result.diagnostics
        );
    }
}

#[test]
fn package_import_fixture_large_terminal_check_rejects_direct_import_hidden_by_closure() {
    let fixture = materialize_interface_closure_fixture("interface-large-terminal-import-drift");
    let source_path = fixture.artifact_path("InterfaceClosure/C/source.npa");
    let mut source = fs::read_to_string(&source_path).unwrap();
    let large_source_size = 32 * 1024 * 1024;
    source.push_str(&" ".repeat(large_source_size + 1 - source.len()));
    fs::write(&source_path, &source).unwrap();

    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let manifest = fs::read_to_string(&manifest_path).unwrap();
    let drifted_manifest = manifest.replacen(
        "imports = [\"InterfaceClosure.B\"]",
        "imports = [\"InterfaceClosure.A\", \"InterfaceClosure.B\"]",
        1,
    );
    assert_ne!(manifest, drifted_manifest);
    fs::write(&manifest_path, drifted_manifest).unwrap();
    let source_hash = format_package_hash(&package_file_hash(source.as_bytes()));
    replace_file_first_hash_after(
        &fixture,
        PACKAGE_MANIFEST_PATH,
        &format!("module = \"{INTERFACE_C}\""),
        &source_hash,
    );
    let drifted_manifest = fs::read_to_string(&manifest_path).unwrap();
    write_interface_closure_lock(&fixture, &drifted_manifest);

    let result = run_build_check(&fixture);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "manifest_source_imports_mismatch"
    );
    assert_eq!(result.diagnostics[0].module.as_deref(), Some(INTERFACE_C));
}

#[test]
fn package_import_fixture_large_terminal_check_rejects_stale_certificate_for_changed_body() {
    let fixture = materialize_interface_closure_fixture("interface-large-terminal-stale-body");
    let source_path = fixture.artifact_path("InterfaceClosure/C/source.npa");
    let source = fs::read_to_string(&source_path).unwrap();
    let mut changed_source = source.replacen(
        "def SurfaceAlias : Sort 2 := Surface",
        "def SurfaceAlias : Sort 2 := MissingSurface",
        1,
    );
    assert_ne!(source, changed_source);
    let large_source_size = 32 * 1024 * 1024;
    changed_source.push_str(&" ".repeat(large_source_size + 1 - changed_source.len()));
    fs::write(&source_path, &changed_source).unwrap();

    let source_hash = format_package_hash(&package_file_hash(changed_source.as_bytes()));
    replace_file_first_hash_after(
        &fixture,
        PACKAGE_MANIFEST_PATH,
        &format!("module = \"{INTERFACE_C}\""),
        &source_hash,
    );
    let manifest = fs::read_to_string(fixture.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_interface_closure_lock(&fixture, &manifest);

    let result = run_build_check(&fixture);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].reason_code, "build_failed");
    assert_eq!(result.diagnostics[0].module.as_deref(), Some(INTERFACE_C));
}

#[test]
fn package_import_fixture_rejects_interface_closure_missing_a_certificate() {
    let fixture = materialize_interface_closure_fixture("interface-missing-a");
    fs::remove_file(fixture.artifact_path("InterfaceClosure/A/certificate.npcert")).unwrap();

    for checker in [PackageChecker::Reference, PackageChecker::Fast] {
        let verify = run_verify_with_checker(&fixture, checker);
        assert_eq!(verify.exit_code(), CommandExitCode::PackageFailure);
        assert!(verify.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::ArtifactIo
                || diagnostic.kind == DiagnosticKind::PackageLock
        }));
        let rendered = verify.render_json();
        assert!(!rendered.contains("source.npa"));
        assert!(!rendered.contains("replay.json"));
        assert!(!rendered.contains("meta.json"));
        assert!(!rendered.contains("theorem-index.json"));
    }
}

#[test]
fn package_import_fixture_rejects_interface_closure_stale_a_lock_hash() {
    let fixture = materialize_interface_closure_fixture("interface-stale-a");
    replace_file_first_hash_after(
        &fixture,
        INTERFACE_CLOSURE_LOCK,
        &format!("\"module\":\"{INTERFACE_A}\""),
        ZERO_HASH,
    );

    for checker in [PackageChecker::Reference, PackageChecker::Fast] {
        let verify = run_verify_with_checker(&fixture, checker);
        assert_eq!(verify.exit_code(), CommandExitCode::PackageFailure);
        assert!(verify.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::PackageLock
                || diagnostic.kind == DiagnosticKind::HashMismatch
                || diagnostic.kind == DiagnosticKind::ReferenceVerifier
                || diagnostic.kind == DiagnosticKind::FastVerifier
        }));
    }
}

#[test]
fn package_import_fixture_rejects_unauthorized_direct_source_import_even_when_available() {
    let fixture = materialize_interface_closure_fixture("interface-unauthorized-source");
    let source = format!(
        "\
import {INTERFACE_A}
import {INTERFACE_B}

def SurfaceAlias : Sort 2 := Surface
"
    );
    fs::write(
        fixture.artifact_path("InterfaceClosure/C/source.npa"),
        &source,
    )
    .unwrap();
    let source_hash = format_package_hash(&package_file_hash(source.as_bytes()));
    replace_file_first_hash_after(
        &fixture,
        PACKAGE_MANIFEST_PATH,
        &format!("module = \"{INTERFACE_C}\""),
        &source_hash,
    );

    let build = run_build_check(&fixture);
    assert_eq!(build.exit_code(), CommandExitCode::PackageFailure);
    assert!(
        build.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::Build
                && diagnostic.reason_code == "build_failed"
                && diagnostic.actual_value.as_deref().is_some_and(|actual| {
                    actual.contains("not present in the verified import set")
                        && actual.contains(INTERFACE_A)
                })
        }),
        "{:?}",
        build.diagnostics
    );
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

#[derive(Clone)]
struct InterfaceClosureModule {
    module: Name,
    source_path: &'static str,
    certificate_path: &'static str,
    source: &'static str,
    imports: Vec<Name>,
    definitions: Vec<&'static str>,
    certificate: ModuleCert,
    certificate_bytes: Vec<u8>,
    verified: VerifiedModule,
    source_interface: HumanSourceInterface,
}

fn materialize_interface_closure_fixture(label: &str) -> TestFixture {
    materialize_interface_closure_fixture_with_dependent(label, false)
}

fn materialize_interface_closure_with_dependent_fixture(label: &str) -> TestFixture {
    materialize_interface_closure_fixture_with_dependent(label, true)
}

fn materialize_interface_closure_fixture_with_dependent(
    label: &str,
    include_dependent: bool,
) -> TestFixture {
    let fixture = TestFixture::empty(label);
    let a = build_interface_closure_module(
        0,
        INTERFACE_A,
        "InterfaceClosure/A/source.npa",
        "InterfaceClosure/A/certificate.npcert",
        "def Carrier : Sort 2 := Type\n",
        Vec::new(),
        vec!["Carrier"],
        &[],
        &[],
        &[],
    );
    let a_import = imported_source_interface(&a);
    let b = build_interface_closure_module(
        1,
        INTERFACE_B,
        "InterfaceClosure/B/source.npa",
        "InterfaceClosure/B/certificate.npcert",
        "import InterfaceClosure.A\n\ndef Surface : Sort 2 := Carrier\n",
        vec![Name::from_dotted(INTERFACE_A)],
        vec!["Surface"],
        &[&a.verified],
        &[&a.verified],
        std::slice::from_ref(&a_import),
    );
    let b_import = imported_source_interface(&b);
    let c = build_interface_closure_module(
        2,
        INTERFACE_C,
        "InterfaceClosure/C/source.npa",
        "InterfaceClosure/C/certificate.npcert",
        "import InterfaceClosure.B\n\ndef SurfaceAlias : Sort 2 := Surface\n",
        vec![Name::from_dotted(INTERFACE_B)],
        vec!["SurfaceAlias"],
        &[&b.verified],
        &[&a.verified, &b.verified],
        std::slice::from_ref(&b_import),
    );
    let modules = if include_dependent {
        let c_import = imported_source_interface(&c);
        let d = build_interface_closure_module(
            3,
            INTERFACE_D,
            "InterfaceClosure/D/source.npa",
            "InterfaceClosure/D/certificate.npcert",
            "import InterfaceClosure.C\n\ndef FinalSurface : Sort 2 := SurfaceAlias\n",
            vec![Name::from_dotted(INTERFACE_C)],
            vec!["FinalSurface"],
            &[&c.verified],
            &[&a.verified, &b.verified, &c.verified],
            std::slice::from_ref(&c_import),
        );
        vec![a, b, c, d]
    } else {
        vec![a, b, c]
    };

    for module in &modules {
        write_fixture_artifact(&fixture, module.source_path, module.source.as_bytes());
        write_fixture_artifact(&fixture, module.certificate_path, &module.certificate_bytes);
    }
    let manifest = interface_closure_manifest(&modules);
    write_fixture_artifact(&fixture, PACKAGE_MANIFEST_PATH, manifest.as_bytes());
    write_interface_closure_lock(&fixture, &manifest);
    fixture
}

fn materialize_legacy_support_fixture(label: &str) -> TestFixture {
    let fixture = TestFixture::from_fixture_root(label, "testdata/package/npa-std");
    let legacy_certificate_bytes =
        fs::read(fixture.artifact_path("Std/Nat/Basic/certificate.npcert")).unwrap();
    let legacy_verified = npa_cert::verify_module_cert_with_import_refs(
        &legacy_certificate_bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let legacy_name = Name::from_dotted(LEGACY_SUPPORT);
    let legacy_import = HumanImportedSourceInterface {
        module: legacy_name.clone(),
        export_hash: legacy_verified.export_hash(),
        certificate_hash: Some(legacy_verified.certificate_hash()),
        source_interface: HumanSourceInterface::new(legacy_name),
    };
    let target_source = "import Std.Nat.Basic\n\ntheorem target_id :\n  forall (P : Prop), forall (p : P), P :=\n  fun P => fun p => p\n";
    let legacy_verified_refs = [&legacy_verified];
    let target = build_interface_closure_module(
        2,
        LEGACY_SUPPORT_TARGET,
        "LegacySupport/Target/source.npa",
        "LegacySupport/Target/certificate.npcert",
        target_source,
        vec![Name::from_dotted(LEGACY_SUPPORT)],
        Vec::new(),
        &legacy_verified_refs,
        &legacy_verified_refs,
        std::slice::from_ref(&legacy_import),
    );

    write_fixture_artifact(&fixture, target.source_path, target.source.as_bytes());
    write_fixture_artifact(&fixture, target.certificate_path, &target.certificate_bytes);
    let manifest_path = fixture.artifact_path(PACKAGE_MANIFEST_PATH);
    let mut manifest = fs::read_to_string(&manifest_path).unwrap();
    manifest.push_str(&format!(
        r#"
[[modules]]
module = "{target_module}"
source = "{target_source_path}"
certificate = "{target_certificate_path}"
producer_profile = "human-surface-explicit-term"
expected_source_hash = "{target_source_hash}"
expected_certificate_file_hash = "{target_certificate_file_hash}"
expected_export_hash = "{target_export_hash}"
expected_axiom_report_hash = "{target_axiom_report_hash}"
expected_certificate_hash = "{target_certificate_hash}"
imports = ["{legacy_module}"]
inductives = []
definitions = []
theorems = ["target_id"]
axioms = []
"#,
        target_module = target.module.as_dotted(),
        target_source_path = target.source_path,
        target_certificate_path = target.certificate_path,
        target_source_hash = format_package_hash(&package_file_hash(target.source.as_bytes())),
        target_certificate_file_hash =
            format_package_hash(&package_file_hash(&target.certificate_bytes)),
        target_export_hash =
            format_package_hash(&PackageHash::from(target.certificate.hashes.export_hash)),
        target_axiom_report_hash = format_package_hash(&PackageHash::from(
            target.certificate.hashes.axiom_report_hash
        )),
        target_certificate_hash = format_package_hash(&PackageHash::from(
            target.certificate.hashes.certificate_hash
        )),
        legacy_module = LEGACY_SUPPORT,
    ));
    fs::write(&manifest_path, &manifest).unwrap();
    write_interface_closure_lock(&fixture, &manifest);
    fixture
}

fn replace_fixture_module_field(manifest: &str, module: &str, field: &str, value: &str) -> String {
    let module_line = format!("module = \"{module}\"");
    let field_prefix = format!("{field} = ");
    let mut output = String::new();
    let mut in_target_module = false;
    let mut replaced = false;
    for line in manifest.lines() {
        if line == "[[modules]]" {
            in_target_module = false;
        } else if line == module_line {
            in_target_module = true;
        }
        if in_target_module && line.starts_with(&field_prefix) {
            output.push_str(&format!("{field} = {value}"));
            replaced = true;
        } else {
            output.push_str(line);
        }
        output.push('\n');
    }
    if !manifest.ends_with('\n') {
        output.pop();
    }
    assert!(replaced, "expected to replace {field} for {module}");
    output
}

// Keep the fixture's source metadata and direct/transitive import sets visible at call sites.
#[allow(clippy::too_many_arguments)]
fn build_interface_closure_module(
    file_id: u32,
    module: &str,
    source_path: &'static str,
    certificate_path: &'static str,
    source: &'static str,
    imports: Vec<Name>,
    definitions: Vec<&'static str>,
    direct_verified_modules: &[&VerifiedModule],
    available_verified_modules: &[&VerifiedModule],
    imported_source_interfaces: &[HumanImportedSourceInterface],
) -> InterfaceClosureModule {
    let output =
        compile_human_source_to_certificate_output_with_available_import_refs_and_axiom_policy(
            FileId(file_id),
            Name::from_dotted(module),
            source,
            direct_verified_modules,
            available_verified_modules,
            imported_source_interfaces,
            &HumanCompileOptions::default(),
            &AxiomPolicy::normal(),
        )
        .unwrap();
    let certificate_bytes = npa_cert::encode_module_cert(&output.certificate).unwrap();
    InterfaceClosureModule {
        module: Name::from_dotted(module),
        source_path,
        certificate_path,
        source,
        imports,
        definitions,
        certificate: output.certificate,
        certificate_bytes,
        verified: output.verified_module,
        source_interface: output.source_interface,
    }
}

fn imported_source_interface(module: &InterfaceClosureModule) -> HumanImportedSourceInterface {
    HumanImportedSourceInterface {
        module: module.module.clone(),
        export_hash: module.certificate.hashes.export_hash,
        certificate_hash: Some(module.certificate.hashes.certificate_hash),
        source_interface: module.source_interface.clone(),
    }
}

fn interface_closure_manifest(modules: &[InterfaceClosureModule]) -> String {
    let mut source = String::from(
        r#"schema = "npa.package.v0.1"
package = "interface-closure-fixture"
version = "0.1.0"
license = "Apache-2.0"
description = "Compact interface-closure regression fixture."

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
producer_profile = "human-surface-explicit-term"
imports = {}
expected_source_hash = "{}"
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
inductives = []
definitions = {}
theorems = []
axioms = []
tags = []

"#,
            module.module.as_dotted(),
            module.source_path,
            module.certificate_path,
            package_name_array(&module.imports),
            format_package_hash(&package_file_hash(module.source.as_bytes())),
            format_package_hash(&package_file_hash(&module.certificate_bytes)),
            format_package_hash(&PackageHash::from(module.certificate.hashes.export_hash)),
            format_package_hash(&PackageHash::from(
                module.certificate.hashes.axiom_report_hash
            )),
            format_package_hash(&PackageHash::from(
                module.certificate.hashes.certificate_hash
            )),
            string_array(&module.definitions),
        ));
    }
    source
}

fn package_name_array(imports: &[Name]) -> String {
    let imports = imports
        .iter()
        .map(|name| format!("\"{}\"", name.as_dotted()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{imports}]")
}

fn string_array(values: &[&str]) -> String {
    let values = values
        .iter()
        .map(|value| format!("\"{value}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{values}]")
}

fn write_interface_closure_lock(fixture: &TestFixture, manifest: &str) {
    let validated = parse_and_validate_manifest_str(manifest).unwrap();
    let lock = build_package_lock_from_package_root(
        &validated,
        fixture.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap();
    write_fixture_artifact(
        fixture,
        INTERFACE_CLOSURE_LOCK,
        lock.canonical_json().unwrap().as_bytes(),
    );
}

fn write_fixture_artifact(fixture: &TestFixture, relative: &str, bytes: &[u8]) {
    let path = fixture.artifact_path(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
}

fn replace_file_first_hash_after(
    fixture: &TestFixture,
    relative: &str,
    marker: &str,
    replacement: &str,
) {
    let path = fixture.artifact_path(relative);
    let mut text = fs::read_to_string(&path).unwrap();
    let marker_start = text.find(marker).unwrap();
    let hash_start = text[marker_start..].find("sha256:").unwrap() + marker_start;
    text.replace_range(hash_start..hash_start + replacement.len(), replacement);
    fs::write(path, text).unwrap();
}

fn run_build_check(fixture: &TestFixture) -> npa_cli::diagnostic::CommandResult {
    run_package_build_certs_check(common_options(fixture.path(), true))
}

fn run_hashes(fixture: &TestFixture) -> npa_cli::diagnostic::CommandResult {
    run_package_check_hashes(common_options(fixture.path(), true))
}

fn run_verify(fixture: &TestFixture) -> npa_cli::diagnostic::CommandResult {
    run_verify_with_checker(fixture, PackageChecker::Reference)
}

fn run_verify_with_checker(
    fixture: &TestFixture,
    checker: PackageChecker,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(verify_certs_full(
        common_options(fixture.path(), true),
        checker,
    ))
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

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::{
    PackageCandidateMetadataOptions, PackageCommonOptions, PackageIndexOptions, PackageTimingMode,
};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package_artifacts::{PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH};
use npa_cli::package_build::run_package_build_certs_write;
use npa_cli::package_candidate_metadata::run_package_export_candidate_metadata;
use npa_cli::package_index::run_package_index;

static NEXT_OUTPUT: AtomicUsize = AtomicUsize::new(0);
static NEXT_TEMP_PACKAGE: AtomicUsize = AtomicUsize::new(0);

#[test]
fn package_export_candidate_metadata_writes_metadata_for_checked_theorem_index_entry() {
    let out = unique_out_path("valid");
    let result = run_export("Proofs.Ai.Algebra.AbstractGroup", "group_conj_slide", &out);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.artifacts.len(), 1);
    assert_eq!(result.artifacts[0].kind, "candidate_verification_metadata");
    assert_eq!(result.artifacts[0].path, out.to_string_lossy());

    let metadata_path = fixture_root().join(&out);
    let metadata = fs::read_to_string(&metadata_path).unwrap();
    assert!(metadata.contains("\"schema_id\": \"npa.candidate-verification-metadata.v1\""));
    assert!(metadata.contains("\"module_name\": \"Proofs.Ai.Algebra.AbstractGroup\""));
    assert!(metadata.contains("\"declaration_name\": \"group_conj_slide\""));
    assert!(metadata.contains(
        "\"statement_hash\": \"sha256:42547086409efa98f37f294809d2fac88636f30e740e128ffade69bfac1377bb\""
    ));
    assert!(metadata.contains("\"source_free_required\": true"));
    assert!(metadata.contains("\"proof_evidence\": false"));

    fs::remove_file(metadata_path).unwrap();
}

#[test]
fn package_export_candidate_metadata_rejects_unknown_declaration_without_writing() {
    let out = unique_out_path("missing");
    let result = run_export("Proofs.Ai.Algebra.AbstractGroup", "missing_theorem", &out);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::TheoremIndex);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "candidate_metadata_declaration_missing"
    );
    assert!(!fixture_root().join(out).exists());
}

#[test]
fn package_export_candidate_metadata_reports_missing_package_lock_prerequisite() {
    let package = TempPackage::from_fixture("missing-lock");
    fs::remove_file(package.artifact_path(PACKAGE_LOCK_PATH)).unwrap();
    let out = PathBuf::from("target/missing-lock.metadata.json");

    let result = run_export_at(
        package.path(),
        "Proofs.Ai.Algebra.AbstractGroup",
        "group_conj_slide",
        &out,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].kind,
        DiagnosticKind::GeneratedArtifact
    );
    assert_eq!(
        result.diagnostics[0].reason_code,
        "candidate_metadata_package_lock_missing"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_LOCK_PATH)
    );
    assert_eq!(
        result.diagnostics[0].expected_value.as_deref(),
        Some("run `npa package build-certs --root <proofs> --json` first")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("missing")
    );
    assert!(!package.artifact_path(out).exists());
}

#[test]
fn package_export_candidate_metadata_reports_missing_theorem_index_prerequisite() {
    let package = TempPackage::from_fixture("missing-index");
    fs::remove_file(package.artifact_path(PACKAGE_THEOREM_INDEX_PATH)).unwrap();
    let out = PathBuf::from("target/missing-index.metadata.json");

    let result = run_export_at(
        package.path(),
        "Proofs.Ai.Algebra.AbstractGroup",
        "group_conj_slide",
        &out,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].kind,
        DiagnosticKind::GeneratedArtifact
    );
    assert_eq!(
        result.diagnostics[0].reason_code,
        "candidate_metadata_theorem_index_missing"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_THEOREM_INDEX_PATH)
    );
    assert_eq!(
        result.diagnostics[0].expected_value.as_deref(),
        Some("run `npa package index --root <proofs> --json` first")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("missing")
    );
    assert!(!package.artifact_path(out).exists());
}

#[test]
fn package_export_candidate_metadata_after_regenerating_standalone_artifacts() {
    let package = TempPackage::from_fixture("regenerate");
    fs::remove_file(package.artifact_path(PACKAGE_LOCK_PATH)).unwrap();
    fs::remove_file(package.artifact_path(PACKAGE_THEOREM_INDEX_PATH)).unwrap();

    let build = run_package_build_certs_write(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    });
    assert_eq!(build.exit_code(), CommandExitCode::Success);
    assert!(package.artifact_path(PACKAGE_LOCK_PATH).exists());

    let index = run_package_index(PackageIndexOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        check: false,
        timings: PackageTimingMode::Off,
    });
    assert_eq!(index.exit_code(), CommandExitCode::Success);
    assert!(package.artifact_path(PACKAGE_THEOREM_INDEX_PATH).exists());

    let out = PathBuf::from("generated/group_conj_slide.metadata.json");
    let result = run_export_at(
        package.path(),
        "Proofs.Ai.Algebra.AbstractGroup",
        "group_conj_slide",
        &out,
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let metadata = fs::read_to_string(package.artifact_path(&out)).unwrap();
    assert!(metadata.contains("\"schema_id\": \"npa.candidate-verification-metadata.v1\""));
    assert!(metadata.contains("\"module_name\": \"Proofs.Ai.Algebra.AbstractGroup\""));
    assert!(metadata.contains("\"declaration_name\": \"group_conj_slide\""));
    assert!(metadata.contains("\"proof_evidence\": false"));
}

#[test]
fn package_export_candidate_metadata_rejects_unknown_module_without_corpus_error() {
    let out = unique_out_path("unknown-module");
    let result = run_export("Proofs.Ai.Standalone.Unknown", "missing_theorem", &out);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::TheoremIndex);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "candidate_metadata_module_missing"
    );
    assert!(!result.diagnostics[0].reason_code.contains("proof-corpus"));
    assert!(!fixture_root().join(out).exists());
}

fn run_export(module: &str, declaration: &str, out: &Path) -> npa_cli::diagnostic::CommandResult {
    run_export_at(&fixture_root(), module, declaration, out)
}

fn run_export_at(
    root: &Path,
    module: &str,
    declaration: &str,
    out: &Path,
) -> npa_cli::diagnostic::CommandResult {
    run_package_export_candidate_metadata(PackageCandidateMetadataOptions {
        common: PackageCommonOptions {
            root: root.to_path_buf(),
            json: true,
        },
        module: module.to_owned(),
        declaration: declaration.to_owned(),
        out: out.to_path_buf(),
    })
}

struct TempPackage {
    path: PathBuf,
}

impl TempPackage {
    fn from_fixture(label: &str) -> Self {
        let index = NEXT_TEMP_PACKAGE.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-candidate-metadata-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        copy_dir_all(&fixture_root(), &path);
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn artifact_path(&self, relative: impl AsRef<Path>) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TempPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn copy_dir_all(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        let target_path = target.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_all(&entry.path(), &target_path);
        } else if file_type.is_file() {
            fs::copy(entry.path(), target_path).unwrap();
        }
    }
}

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package/proofs")
}

fn unique_out_path(label: &str) -> PathBuf {
    let index = NEXT_OUTPUT.fetch_add(1, Ordering::SeqCst);
    PathBuf::from(format!(
        "target/test-candidate-metadata-{}-{label}-{index}.json",
        std::process::id()
    ))
}

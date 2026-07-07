use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::{PackageCandidateMetadataOptions, PackageCommonOptions};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package_candidate_metadata::run_package_export_candidate_metadata;

static NEXT_OUTPUT: AtomicUsize = AtomicUsize::new(0);

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

fn run_export(module: &str, declaration: &str, out: &Path) -> npa_cli::diagnostic::CommandResult {
    run_package_export_candidate_metadata(PackageCandidateMetadataOptions {
        common: PackageCommonOptions {
            root: fixture_root(),
            json: true,
        },
        module: module.to_owned(),
        declaration: declaration.to_owned(),
        out: out.to_path_buf(),
    })
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

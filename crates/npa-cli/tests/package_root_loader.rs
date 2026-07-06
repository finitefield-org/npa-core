use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::fs::{join_package_path, render_package_root};
use npa_cli::package::{load_package_root, PACKAGE_MANIFEST_PATH};
use npa_package::PackagePath;

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-root-loader-{}-{label}-{index}",
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
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_root_loader_loads_checked_in_proof_package_manifest() {
    let loaded = load_package_root(repo_root().join("proofs"), "package check").unwrap();

    assert_eq!(loaded.root_display, "<absolute-root>");
    assert_eq!(loaded.manifest_path.as_str(), PACKAGE_MANIFEST_PATH);
    assert!(loaded
        .manifest_source
        .contains("schema = \"npa.package.v0.1\""));
    assert_eq!(
        loaded.validated.manifest().package.as_str(),
        "npa-proof-corpus"
    );
}

#[test]
fn package_root_loader_reports_missing_manifest_with_package_relative_path() {
    let dir = TestDir::new("missing-manifest");
    let result = load_package_root(dir.path(), "package check").unwrap_err();

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.root, "<absolute-root>");
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageManifest);
    assert_eq!(result.diagnostics[0].reason_code, "manifest_missing");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_MANIFEST_PATH)
    );

    let json = result.render_json();
    assert!(json.contains("\"path\":\"npa-package.toml\""));
    assert!(!json.contains(&dir.path().to_string_lossy().to_string()));
}

#[test]
fn package_root_loader_preserves_manifest_validation_diagnostic() {
    let dir = TestDir::new("invalid-manifest");
    fs::write(
        dir.path().join(PACKAGE_MANIFEST_PATH),
        "schema = \"npa.package.v0.1\"\ntrusted_status = \"verified_by_certificate\"\n",
    )
    .unwrap();

    let result = load_package_root(dir.path(), "package check").unwrap_err();

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageManifest);
    assert_eq!(result.diagnostics[0].reason_code, "unknown_field");
    assert_eq!(result.diagnostics[0].path.as_deref(), Some("$"));
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("trusted_status")
    );
}

#[test]
fn package_root_loader_joins_package_relative_paths_after_validation() {
    let joined = join_package_path(
        Path::new("proofs"),
        &PackagePath::new("Proofs/Ai/Basic/source.npa"),
        "modules[0].source",
    )
    .unwrap();

    assert_eq!(
        joined,
        PathBuf::from("proofs").join("Proofs/Ai/Basic/source.npa")
    );
}

#[test]
fn package_root_loader_rejects_package_path_escape_before_join() {
    let diagnostic = join_package_path(
        Path::new("proofs"),
        &PackagePath::new("../outside.npa"),
        "modules[0].source",
    )
    .unwrap_err();
    let diagnostic = *diagnostic;

    assert_eq!(diagnostic.kind, DiagnosticKind::PackageManifest);
    assert_eq!(diagnostic.reason_code, "invalid_path");
    assert_eq!(diagnostic.path.as_deref(), Some("modules[0].source"));
    assert_eq!(diagnostic.actual_value.as_deref(), Some("../outside.npa"));
}

#[test]
fn package_root_loader_sanitizes_absolute_root_display() {
    assert_eq!(
        render_package_root(Path::new("/tmp/example")),
        "<absolute-root>"
    );
    assert_eq!(render_package_root(Path::new("proofs")), "proofs");
    assert_eq!(render_package_root(Path::new("")), ".");
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

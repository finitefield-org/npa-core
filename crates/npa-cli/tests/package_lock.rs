use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::PackageCommonOptions;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package_lock::{run_package_lock_check, run_package_lock_write};

const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn from_proof_fixture(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-lock-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        copy_dir_all(&repo_root().join("testdata/package/proofs"), &path);
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

#[test]
fn package_lock_check_succeeds_on_proof_corpus_fixture() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args([
            "package",
            "lock",
            "check",
            "--root",
            "testdata/package/proofs",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "package lock check: passed\n"
    );
}

#[test]
fn package_lock_check_succeeds_on_proof_corpus_fixture_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args([
            "package",
            "lock",
            "check",
            "--root",
            "testdata/package/proofs",
            "--json",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"npa.package.command_result.v0.1\",\"command\":\"package lock check\",\"root\":\"testdata/package/proofs\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
}

#[test]
fn package_lock_check_rejects_missing_lock() {
    let package = TestPackage::from_proof_fixture("missing-lock");
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();

    let result = run_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageLock);
    assert_eq!(result.diagnostics[0].reason_code, "package_lock_missing");
    assert_eq!(result.diagnostics[0].path.as_deref(), Some(LOCK_PATH));
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_lock_check_rejects_stale_lock() {
    let package = TestPackage::from_proof_fixture("stale-lock");
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();

    let result = run_check(&package);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::HashMismatch);
    assert_eq!(result.diagnostics[0].reason_code, "package_lock_stale");
    assert_eq!(result.diagnostics[0].path.as_deref(), Some(LOCK_PATH));
    assert!(result.diagnostics[0].expected_hash.is_some());
    assert!(result.diagnostics[0].actual_hash.is_some());
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_lock_write_repairs_only_package_lock() {
    let package = TestPackage::from_proof_fixture("write-repair");
    let lock_path = package.artifact_path(LOCK_PATH);
    let certificate_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let expected_lock = fs::read_to_string(&lock_path).unwrap();
    let certificate_before = fs::read(&certificate_path).unwrap();
    fs::write(&lock_path, format!("{expected_lock}\n")).unwrap();

    let result = run_write(&package);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert_eq!(fs::read_to_string(lock_path).unwrap(), expected_lock);
    assert_eq!(fs::read(certificate_path).unwrap(), certificate_before);
}

#[test]
fn package_lock_write_creates_missing_lock_and_reports_json() {
    let package = TestPackage::from_proof_fixture("write-missing");
    let lock_path = package.artifact_path(LOCK_PATH);
    let expected_lock = fs::read_to_string(&lock_path).unwrap();
    fs::remove_file(&lock_path).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "lock", "write", "--root"])
        .arg(package.path())
        .arg("--json")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"npa.package.command_result.v0.1\",\"command\":\"package lock write\",\"root\":\"<absolute-root>\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}\n"
    );
    assert_eq!(fs::read_to_string(lock_path).unwrap(), expected_lock);
}

fn run_check(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_lock_check(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    })
}

fn run_write(package: &TestPackage) -> npa_cli::diagnostic::CommandResult {
    run_package_lock_write(PackageCommonOptions {
        root: package.path().to_path_buf(),
        json: true,
    })
}

fn copy_dir_all(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_dir_all(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

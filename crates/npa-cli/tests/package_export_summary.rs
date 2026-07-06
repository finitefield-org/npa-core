use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::{PackageCommonOptions, PackageExportSummaryOptions, PackageTimingMode};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind, PACKAGE_COMMAND_RESULT_SCHEMA};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_artifacts::PACKAGE_LOCK_PATH;
use npa_cli::package_export_summary::run_package_export_summary;
use npa_package::{
    build_package_lock_from_artifacts, parse_and_validate_manifest_str,
    parse_package_verified_export_summary_json, PackageLockArtifact, PackagePath,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

const BASIC_CERTIFICATE_PATH: &str = "Proofs/Ai/Basic/certificate.npcert";
const PROOF_CORPUS_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;
const STALE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-export-summary-{}-{label}-{index}",
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

#[test]
fn package_export_summary_write_creates_summary_from_source_free_inputs() {
    let package = source_free_fixture("write-source-free");
    assert!(!package
        .artifact_path("missing/source/Proofs/Ai/Basic.npa")
        .exists());
    assert!(!package
        .artifact_path("missing/replay/Proofs/Ai/Basic.json")
        .exists());
    assert!(!package
        .artifact_path("missing/meta/Proofs/Ai/Basic.json")
        .exists());
    let before = collect_files(package.path());

    let result = run_write(&package, None);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "verified_export_summary_metadata"));
    assert_eq!(result.artifacts.len(), 1);
    assert_eq!(result.artifacts[0].kind, "package_verified_export_summary");
    assert_eq!(
        result.artifacts[0].path,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH
    );
    let after = collect_files(package.path());
    let added = after
        .keys()
        .filter(|path| !before.contains_key(*path))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(added, vec![PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH.to_owned()]);

    let summary = parse_package_verified_export_summary_json(
        &fs::read_to_string(package.artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)).unwrap(),
    )
    .unwrap();
    assert!(!summary.trusted);
    assert_eq!(summary.modules.len(), 1);
    assert_eq!(summary.modules[0].module.as_dotted(), "Proofs.Ai.Basic");
    assert!(!summary.modules[0].exported_globals.is_empty());
}

#[test]
fn package_export_summary_check_succeeds_and_writes_no_files() {
    let package = source_free_fixture("check-no-write");
    assert_eq!(
        run_write(&package, None).exit_code(),
        CommandExitCode::Success
    );
    let before = collect_files(package.path());

    let result = run_check(&package, None);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(collect_files(package.path()), before);
}

#[test]
fn package_export_summary_check_rejects_missing_stale_and_tampered_summary() {
    let missing = source_free_fixture("missing");
    assert_failure(
        &run_check(&missing, None),
        "verified_export_summary_missing",
    );

    let stale = source_free_fixture("stale");
    assert_eq!(
        run_write(&stale, None).exit_code(),
        CommandExitCode::Success
    );
    let lock_path = stale.artifact_path(PACKAGE_LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();
    assert_failure(&run_check(&stale, None), "verified_export_summary_stale");

    let tampered = source_free_fixture("tampered");
    assert_eq!(
        run_write(&tampered, None).exit_code(),
        CommandExitCode::Success
    );
    replace_json_hash_field(
        &tampered.artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH),
        "summary_hash",
        STALE_HASH,
    );
    let result = run_check(&tampered, None);
    assert_failure(&result, "verified_export_summary_hash_mismatch");
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("summary_hash"));
}

#[test]
fn package_export_summary_custom_out_is_package_relative() {
    let package = source_free_fixture("custom-out");
    let out = Path::new("generated/custom-export-summary.json");

    let result = run_write(&package, Some(out));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(!package
        .artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)
        .exists());
    assert!(package
        .artifact_path("generated/custom-export-summary.json")
        .exists());
    assert_eq!(
        result.artifacts[0].path,
        "generated/custom-export-summary.json"
    );
}

#[test]
fn package_export_summary_proof_corpus_check_mode_succeeds_with_checked_in_artifact() {
    let root = repo_root().join("proofs");
    let summary_path = root.join(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH);
    let before_summary = fs::read(&summary_path).unwrap();

    let root_for_run = root.clone();
    let result = run_with_proof_corpus_stack(move || {
        run_package_export_summary(PackageExportSummaryOptions {
            common: PackageCommonOptions {
                root: root_for_run,
                json: true,
            },
            out: None,
            check: true,
            timings: PackageTimingMode::Off,
        })
    });

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.artifacts.len(), 1);
    assert_eq!(result.artifacts[0].kind, "package_verified_export_summary");
    assert_eq!(
        result.artifacts[0].path,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH
    );

    let json = result.render_json();
    assert!(json.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"package export-summary\","
    )));
    assert!(json.contains("\"root\":\"<absolute-root>\""));
    assert!(json.contains("\"status\":\"passed\""));
    assert!(json.contains("proof_evidence=false"));
    assert_eq!(fs::read(summary_path).unwrap(), before_summary);
}

fn run_write(package: &TestPackage, out: Option<&Path>) -> npa_cli::diagnostic::CommandResult {
    run_export_summary(package, false, out)
}

fn run_check(package: &TestPackage, out: Option<&Path>) -> npa_cli::diagnostic::CommandResult {
    run_export_summary(package, true, out)
}

fn run_export_summary(
    package: &TestPackage,
    check: bool,
    out: Option<&Path>,
) -> npa_cli::diagnostic::CommandResult {
    run_package_export_summary(PackageExportSummaryOptions {
        common: PackageCommonOptions {
            root: package.path().to_path_buf(),
            json: true,
        },
        out: out.map(Path::to_path_buf),
        check,
        timings: PackageTimingMode::Off,
    })
}

fn assert_failure(result: &npa_cli::diagnostic::CommandResult, reason: &str) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].kind,
        DiagnosticKind::GeneratedArtifact
    );
    assert_eq!(result.diagnostics[0].reason_code, reason);
}

fn source_free_fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let manifest_source = basic_manifest_source();
    write_file(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    );
    let certificate_bytes =
        fs::read(repo_root().join("proofs").join(BASIC_CERTIFICATE_PATH)).unwrap();
    write_bytes(
        package.artifact_path(BASIC_CERTIFICATE_PATH),
        certificate_bytes.as_slice(),
    );
    let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
    let lock = build_package_lock_from_artifacts(
        &validated,
        PackagePath::new(PACKAGE_MANIFEST_PATH),
        manifest_source.as_bytes(),
        [PackageLockArtifact {
            path: PackagePath::new(BASIC_CERTIFICATE_PATH),
            bytes: certificate_bytes.as_slice(),
        }],
    )
    .unwrap();
    write_file(
        package.artifact_path(PACKAGE_LOCK_PATH),
        &lock.canonical_json().unwrap(),
    );
    package
}

fn basic_manifest_source() -> String {
    r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[modules]]
module = "Proofs.Ai.Basic"
source = "missing/source/Proofs/Ai/Basic.npa"
certificate = "Proofs/Ai/Basic/certificate.npcert"
meta = "missing/meta/Proofs/Ai/Basic.json"
replay = "missing/replay/Proofs/Ai/Basic.json"
producer_profile = "human-surface-explicit-term"
expected_source_hash = "sha256:2176be7570deae66754789868aa373ab01434512b4f50b992089886d2c655387"
expected_certificate_file_hash = "sha256:448a3de71485d4f38e45ac7bf3b637b0e9e38d7ce215dd4847a2a2188099ee21"
expected_export_hash = "sha256:6cbf881b56f61d413c2584eb9b1cdd6fb09e504f6ff6c855fa73ee55d763b839"
expected_axiom_report_hash = "sha256:fed11e73accfbfb0dfc28b4f510e151fa33d8af82d58fdb23b92567e04e59e40"
expected_certificate_hash = "sha256:7a50b381af353fe15c0b602fad60f4b9d5f70613dfe6f47832da2d8c11b391dd"
imports = []
definitions = []
theorems = ["id"]
axioms = []
"#
    .to_owned()
}

fn run_with_proof_corpus_stack(
    run: impl FnOnce() -> npa_cli::diagnostic::CommandResult + Send + 'static,
) -> npa_cli::diagnostic::CommandResult {
    std::thread::Builder::new()
        .stack_size(PROOF_CORPUS_TEST_STACK_SIZE)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap()
}

fn collect_files(root: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut files = BTreeMap::new();
    collect_files_rec(root, root, &mut files);
    files
}

fn collect_files_rec(root: &Path, path: &Path, files: &mut BTreeMap<String, Vec<u8>>) {
    for entry in fs::read_dir(path).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            collect_files_rec(root, &path, files);
        } else {
            let relative = path
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            files.insert(relative, fs::read(path).unwrap());
        }
    }
}

fn replace_json_hash_field(path: &Path, field: &str, replacement: &str) {
    let mut source = fs::read_to_string(path).unwrap();
    let marker = format!("\"{field}\":\"sha256:");
    let start = source.find(&marker).unwrap() + marker.len() - "sha256:".len();
    source.replace_range(start..start + replacement.len(), replacement);
    fs::write(path, source).unwrap();
}

fn write_file(path: PathBuf, contents: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, contents).unwrap();
}

fn write_bytes(path: PathBuf, contents: &[u8]) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, contents).unwrap();
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-cli crate lives under crates/")
        .to_path_buf()
}

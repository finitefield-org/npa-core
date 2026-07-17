use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use npa_cli::{
    args::PackageTimingMode,
    diagnostic::{CommandExitCode, DiagnosticKind},
    generated_artifact_writer::write_package_generated_artifact_atomic,
    package_api::v1::{common_options, theorem_premise_report},
    package_artifacts::PACKAGE_THEOREM_PREMISE_REPORT_PATH,
    package_theorem_premise_report::run_package_theorem_premise_report,
};
use npa_package::{
    build_package_lock_from_package_root, parse_and_validate_manifest_str,
    parse_package_theorem_premise_report_json, PackagePath,
};

const MANIFEST_PATH: &str = "npa-package.toml";
const LOCK_PATH: &str = "generated/package-lock.json";
const CERTIFICATE_PATH: &str = "Proofs/Ai/Basic/certificate.npcert";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-theorem-premise-report-{}-{label}-{index}",
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

    fn artifact(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn theorem_premise_report_write_and_check_are_canonical_and_idempotent() {
    let package = fixture("write-check");
    let before = collect_files(package.path());

    let written = run(&package, false);
    assert_eq!(
        written.exit_code(),
        CommandExitCode::Success,
        "{written:#?}"
    );
    assert!(written.diagnostics.is_empty());
    assert_eq!(written.artifacts.len(), 1);
    assert_eq!(written.artifacts[0].kind, "package_theorem_premise_report");
    assert_eq!(
        written.artifacts[0].path,
        PACKAGE_THEOREM_PREMISE_REPORT_PATH
    );
    let checked_bytes =
        fs::read_to_string(package.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH)).unwrap();
    let report = parse_package_theorem_premise_report_json(&checked_bytes).unwrap();
    assert_eq!(report.summary.theorem_count, 20);
    assert_eq!(report.entries.len(), 20);

    let after_write = collect_files(package.path());
    let added = after_write
        .keys()
        .filter(|path| !before.contains_key(*path))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(added, vec![PACKAGE_THEOREM_PREMISE_REPORT_PATH.to_owned()]);

    let checked = run(&package, true);
    assert_eq!(checked.exit_code(), CommandExitCode::Success);
    assert!(checked.diagnostics.is_empty());
    assert_eq!(collect_files(package.path()), after_write);

    fs::write(
        package.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        b"stale regular target",
    )
    .unwrap();
    let replaced = run(&package, false);
    assert_eq!(replaced.exit_code(), CommandExitCode::Success);
    assert_eq!(
        fs::read_to_string(package.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH)).unwrap(),
        checked_bytes
    );

    let rewritten = run(&package, false);
    assert_eq!(rewritten.exit_code(), CommandExitCode::Success);
    assert_eq!(collect_files(package.path()), after_write);
}

#[test]
fn theorem_premise_report_check_distinguishes_missing_invalid_and_stale() {
    let missing = fixture("missing");
    assert_failure(&run(&missing, true), "theorem_premise_report_missing");

    let invalid = fixture("invalid");
    let invalid_written = run(&invalid, false);
    assert_eq!(
        invalid_written.exit_code(),
        CommandExitCode::Success,
        "{invalid_written:#?}"
    );
    fs::write(
        invalid.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        b"{\"schema\":",
    )
    .unwrap();
    assert_failure(&run(&invalid, true), "theorem_premise_report_invalid");

    let stale = fixture("stale");
    assert_eq!(run(&stale, false).exit_code(), CommandExitCode::Success);
    let mut lock = fs::read_to_string(stale.artifact(LOCK_PATH)).unwrap();
    lock.push('\n');
    fs::write(stale.artifact(LOCK_PATH), lock).unwrap();
    let result = run(&stale, true);
    assert_failure(&result, "theorem_premise_report_stale");
    assert!(result.diagnostics[0].expected_hash.is_some());
    assert!(result.diagnostics[0].actual_hash.is_some());
}

#[test]
fn theorem_premise_report_reader_rejects_non_utf8_and_symlink_targets() {
    let non_utf8 = fixture("non-utf8");
    fs::write(
        non_utf8.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        [0xff, 0xfe],
    )
    .unwrap();
    assert_failure(&run(&non_utf8, true), "generated_artifact_read_failed");

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        let symlinked = fixture("symlink-target");
        let target = symlinked.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
        symlink("../npa-package.toml", &target).unwrap();
        assert_failure(&run(&symlinked, true), "generated_artifact_read_failed");
    }
}

#[test]
fn atomic_generated_writer_rejects_symlink_parent_target_and_temp_collision() {
    let package = TestPackage::new("atomic-writer");
    fs::create_dir(package.artifact("generated")).unwrap();
    let path = PackagePath::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
    write_package_generated_artifact_atomic(package.path(), &path, b"complete").unwrap();
    assert_eq!(
        fs::read(package.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH)).unwrap(),
        b"complete"
    );

    let target = package.artifact(PACKAGE_THEOREM_PREMISE_REPORT_PATH);
    fs::remove_file(&target).unwrap();
    let temporary = target.with_file_name(format!(
        ".theorem-premise-report.json.tmp.{}",
        std::process::id()
    ));
    fs::write(&temporary, b"collision").unwrap();
    assert!(write_package_generated_artifact_atomic(package.path(), &path, b"new").is_err());
    assert!(!target.exists());
    assert_eq!(fs::read(&temporary).unwrap(), b"collision");
    fs::remove_file(temporary).unwrap();

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        symlink("../npa-package.toml", &target).unwrap();
        assert!(write_package_generated_artifact_atomic(package.path(), &path, b"new").is_err());
        fs::remove_file(&target).unwrap();

        let outside = package.artifact("outside-generated");
        fs::create_dir(&outside).unwrap();
        fs::remove_dir(package.artifact("generated")).unwrap();
        symlink(&outside, package.artifact("generated")).unwrap();
        assert!(write_package_generated_artifact_atomic(package.path(), &path, b"new").is_err());
    }
}

fn run(package: &TestPackage, check: bool) -> npa_cli::diagnostic::CommandResult {
    run_package_theorem_premise_report(
        theorem_premise_report(common_options(package.path(), true), check)
            .with_timings(PackageTimingMode::Off),
    )
}

fn assert_failure(result: &npa_cli::diagnostic::CommandResult, reason: &str) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].kind,
        DiagnosticKind::GeneratedArtifact
    );
    assert_eq!(result.diagnostics[0].reason_code, reason);
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_THEOREM_PREMISE_REPORT_PATH)
    );
}

fn fixture(label: &str) -> TestPackage {
    let package = TestPackage::new(label);
    let certificate = repo_root()
        .join("testdata/package/proofs")
        .join(CERTIFICATE_PATH);
    let target = package.artifact(CERTIFICATE_PATH);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::copy(certificate, target).unwrap();
    let manifest = basic_manifest();
    fs::write(package.artifact(MANIFEST_PATH), &manifest).unwrap();
    let validated = parse_and_validate_manifest_str(&manifest).unwrap();
    let lock = build_package_lock_from_package_root(
        &validated,
        package.path(),
        PackagePath::new(MANIFEST_PATH),
    )
    .unwrap();
    let lock_path = package.artifact(LOCK_PATH);
    fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
    fs::write(lock_path, lock.canonical_json().unwrap()).unwrap();
    package
}

fn basic_manifest() -> String {
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

fn collect_files(root: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut files = BTreeMap::new();
    collect_files_inner(root, root, &mut files);
    files
}

fn collect_files_inner(root: &Path, current: &Path, files: &mut BTreeMap<String, Vec<u8>>) {
    let mut entries = fs::read_dir(current)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_files_inner(root, &path, files);
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

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

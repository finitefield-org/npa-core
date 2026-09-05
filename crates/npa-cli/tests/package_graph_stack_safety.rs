use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::Name;
use npa_package::{
    parse_package_hash, parse_package_lock_json, PackageLockEntry, PackageLockEntryOrigin,
    PackageLockImport, PackagePath,
};

const DEEP_GRAPH_TEST_ENTRIES: usize = 4096;
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-graph-stack-safety-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).expect("stale test package should be removable");
        }
        fs::create_dir_all(&path).expect("test package directory should be creatable");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn deep_manifest_cycle_is_structured_across_package_cli_consumers() {
    let package = TestPackage::new("deep-manifest-cycle");
    fs::write(
        package.path().join("npa-package.toml"),
        deep_manifest_cycle_source(),
    )
    .expect("deep manifest fixture should be writable");

    let commands: [(&str, &[&str]); 5] = [
        ("check", &[]),
        ("index", &[]),
        (
            "build-certs",
            &["--update-manifest-hashes", "--module", "Proofs.Deep.M0000"],
        ),
        ("publish-plan", &[]),
        ("check-generated", &[]),
    ];

    for (subcommand, extra_args) in commands {
        let output = Command::new(env!("CARGO_BIN_EXE_npa"))
            .args(["package", subcommand, "--root"])
            .arg(package.path())
            .arg("--json")
            .args(extra_args)
            .output()
            .unwrap_or_else(|error| panic!("package {subcommand} should launch: {error}"));

        assert_eq!(
            output.status.code(),
            Some(1),
            "package {subcommand} should return a package failure; stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stderr.is_empty(),
            "package {subcommand} should keep JSON diagnostics on stdout: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout)
            .unwrap_or_else(|error| panic!("package {subcommand} JSON should be UTF-8: {error}"));
        assert!(
            stdout.starts_with(&format!(
                "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package {subcommand}\","
            )),
            "package {subcommand} should return a command_result envelope: {stdout}"
        );
        assert!(
            stdout.contains("\"reason_code\":\"import_cycle\""),
            "package {subcommand} should preserve the graph diagnostic: {stdout}"
        );
        assert!(
            stdout.contains(&format!(
                "\"path\":\"modules[{}].imports[0]\"",
                DEEP_GRAPH_TEST_ENTRIES - 1
            )),
            "package {subcommand} should report the closing edge: {stdout}"
        );
    }
}

#[test]
fn deep_package_lock_cycle_is_structured_across_source_free_cli_consumers() {
    let package = TestPackage::new("deep-package-lock-cycle");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package/proofs"),
        package.path(),
    );
    let lock_path = package.path().join("generated/package-lock.json");
    let mut lock = parse_package_lock_json(
        &fs::read_to_string(&lock_path).expect("fixture package lock should be readable"),
    )
    .expect("fixture package lock should parse");
    let hash = parse_package_hash(ZERO_HASH, "test.zero_hash").expect("zero hash should parse");
    lock.entries
        .extend((0..DEEP_GRAPH_TEST_ENTRIES).map(|index| PackageLockEntry {
            module: Name::from_dotted(format!("Proofs.DeepLock.M{index:04}")),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(format!(
                "Proofs/DeepLock/M{index:04}/certificate.npcert"
            )),
            certificate_file_hash: hash,
            export_hash: hash,
            axiom_report_hash: hash,
            certificate_hash: hash,
            imports: vec![PackageLockImport {
                module: Name::from_dotted(format!(
                    "Proofs.DeepLock.M{:04}",
                    (index + 1) % DEEP_GRAPH_TEST_ENTRIES
                )),
                export_hash: hash,
                certificate_hash: hash,
            }],
            package: None,
            version: None,
        }));
    fs::write(
        lock_path,
        lock.canonical_json()
            .expect("cyclic package lock should remain schema-valid"),
    )
    .expect("deep package lock fixture should be writable");

    for subcommand in ["index", "publish-plan", "check-generated"] {
        let output = Command::new(env!("CARGO_BIN_EXE_npa"))
            .args(["package", subcommand, "--root"])
            .arg(package.path())
            .arg("--json")
            .output()
            .unwrap_or_else(|error| panic!("package {subcommand} should launch: {error}"));

        assert_eq!(
            output.status.code(),
            Some(1),
            "package {subcommand} should return a package failure; stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stderr.is_empty(),
            "package {subcommand} should keep JSON diagnostics on stdout: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout)
            .unwrap_or_else(|error| panic!("package {subcommand} JSON should be UTF-8: {error}"));
        assert!(
            stdout.starts_with(&format!(
                "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package {subcommand}\","
            )),
            "package {subcommand} should return a command_result envelope: {stdout}"
        );
        assert!(
            stdout.contains("\"reason_code\":\"lock_graph_invalid\"")
                && stdout.contains("LockImportCycle"),
            "package {subcommand} should preserve the lock-graph diagnostic: {stdout}"
        );
    }
}

fn deep_manifest_cycle_source() -> String {
    let mut source = r#"schema = "npa.package.v0.1"
package = "npa-deep-cli-graph-test"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

"#
    .to_owned();

    for index in 0..DEEP_GRAPH_TEST_ENTRIES {
        let imported_index = if index + 1 < DEEP_GRAPH_TEST_ENTRIES {
            index + 1
        } else {
            0
        };
        writeln!(
            source,
            r#"[[modules]]
module = "Proofs.Deep.M{index:04}"
source = "Proofs/Deep/M{index:04}/source.npa"
certificate = "Proofs/Deep/M{index:04}/certificate.npcert"
imports = ["Proofs.Deep.M{imported_index:04}"]
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []
"#,
        )
        .expect("writing to a String should succeed");
    }

    source.push_str(
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
    );
    source
}

fn copy_tree(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).expect("fixture destination should be creatable");
    for entry in fs::read_dir(source).expect("fixture source directory should be readable") {
        let entry = entry.expect("fixture directory entry should be readable");
        let source_path = entry.path();
        let destination_path = destination.join(entry.file_name());
        if source_path.is_dir() {
            copy_tree(&source_path, &destination_path);
        } else {
            fs::copy(&source_path, &destination_path)
                .expect("fixture file should be copied into the test package");
        }
    }
}

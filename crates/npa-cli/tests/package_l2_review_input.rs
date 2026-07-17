use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use npa_cli::{
    args::{PackageCommand, PackageCommonOptions, PackageL2ReviewInputOptions},
    diagnostic::CommandStatus,
    package::run_package_command,
};

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let root = std::env::temp_dir().join(format!(
            "npa-cli-l2-review-input-{}-{index}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        copy_directory(&repo_root().join("testdata/package/npa-mathlib"), &root);
        Self { root }
    }

    fn options(&self, out: &str) -> PackageL2ReviewInputOptions {
        let mut common = PackageCommonOptions::default();
        common.root = self.root.clone();
        common.json = true;
        PackageL2ReviewInputOptions {
            common,
            policy: repo_root().join("../npa-mathlib/policy/l2-acceptance-policy.json"),
            module: "Mathlib.Core.Reduction".to_owned(),
            declaration: "beta_const_nat".to_owned(),
            out: PathBuf::from(out),
            check: false,
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn review_input_requires_the_current_source_free_generated_snapshot() {
    let fixture = Fixture::new();
    let current = run_package_command(PackageCommand::PrepareL2ReviewInput(
        fixture.options("l2-reviews/current.input.json"),
    ));
    assert_eq!(current.status, CommandStatus::Passed);

    let axiom_path = fixture.root.join("generated/axiom-report.json");
    let mut axiom = fs::read_to_string(&axiom_path).unwrap();
    let start = axiom.find("sha256:").unwrap() + "sha256:".len();
    axiom.replace_range(start..start + 64, &"a".repeat(64));
    fs::write(axiom_path, axiom).unwrap();

    let stale = run_package_command(PackageCommand::PrepareL2ReviewInput(
        fixture.options("l2-reviews/stale.input.json"),
    ));
    assert_eq!(stale.status, CommandStatus::Failed);
    assert!(stale
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.reason_code == "l2_review_generated_identity_mismatch" }));
}

fn copy_directory(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_directory(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::Name;
use npa_cli::args::PackageCheckSourceStructureOptions;
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{
    check_source_structure_all, check_source_structure_modules, check_source_structure_paths,
    common_options,
};
use npa_cli::package_source_structure::run_package_check_source_structure;
use npa_package::PackagePath;

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-source-structure-{}-{label}-{index}",
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

    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.path.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn path_options(package: &TestPackage, paths: &[&str]) -> PackageCheckSourceStructureOptions {
    check_source_structure_paths(
        common_options(package.path(), true),
        paths.iter().map(|path| PackagePath::new(*path)).collect(),
    )
}

#[test]
fn direct_path_check_is_manifest_free_and_lexer_aware() {
    let package = TestPackage::new("direct-balanced");
    package.write(
        "Draft/source.npa",
        "-- unmatched comment ([{\n\ndef text : Type := \"unmatched string )]}\"\n",
    );

    let result = run_package_check_source_structure(path_options(&package, &["Draft/source.npa"]));

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.diagnostics.is_empty());
    assert!(!package.path().join(PACKAGE_MANIFEST_PATH).exists());
}

#[test]
fn programmatic_empty_explicit_selection_fails_closed() {
    let package = TestPackage::new("empty-selection");
    for (options, field) in [
        (
            check_source_structure_paths(common_options(package.path(), true), Vec::new()),
            "--path",
        ),
        (
            check_source_structure_modules(common_options(package.path(), true), Vec::new()),
            "--module",
        ),
    ] {
        let result = run_package_check_source_structure(options);
        assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(
            result.diagnostics[0].reason_code,
            "source_structure_selection_empty"
        );
        assert_eq!(result.diagnostics[0].field.as_deref(), Some(field));
    }
}

#[test]
fn programmatic_invalid_selectors_fail_as_usage_before_package_io() {
    let package = TestPackage::new("invalid-selector");
    fs::remove_dir_all(package.path()).unwrap();

    let cases = [
        (
            check_source_structure_paths(
                common_options(package.path(), true),
                vec![PackagePath::new("../outside.npa")],
            ),
            "invalid_flag_value",
            "--path",
        ),
        (
            check_source_structure_modules(
                common_options(package.path(), true),
                vec![Name::from_dotted("Proofs..Invalid")],
            ),
            "invalid_module_name",
            "--module",
        ),
    ];

    for (options, reason_code, field) in cases {
        let result = run_package_check_source_structure(options);
        assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
        assert_eq!(result.diagnostics.len(), 1);
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.kind, DiagnosticKind::Usage);
        assert_eq!(diagnostic.reason_code, reason_code);
        assert_eq!(diagnostic.field.as_deref(), Some(field));
        assert!(diagnostic.path.is_none());
        assert!(diagnostic.actual_value.is_none());
        assert!(!result.render_json().contains("../outside.npa"));
        assert!(!package.path().exists());
    }
}

#[test]
fn unclosed_delimiter_reports_primary_and_opening_locations() {
    let package = TestPackage::new("unclosed");
    let source = "def sample : Type :=\n  (\n";
    package.write("Draft/source.npa", source);

    let result = run_package_check_source_structure(path_options(&package, &["Draft/source.npa"]));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::SourceStructure);
    assert_eq!(diagnostic.reason_code, "unclosed_delimiter");
    assert_eq!(diagnostic.path.as_deref(), Some("Draft/source.npa"));
    assert_eq!(diagnostic.field.as_deref(), Some("parser"));
    let primary = diagnostic.source.as_ref().expect("primary source context");
    assert_eq!(primary.start_byte(), source.len() as u32);
    assert_eq!(primary.end_byte(), source.len() as u32);
    assert_eq!(primary.line(), Some(3));
    assert_eq!(primary.column(), Some(1));
    let delimiter = diagnostic.delimiter().expect("delimiter context");
    assert_eq!(delimiter.kind(), "unclosed_delimiter");
    assert_eq!(delimiter.expected_closing(), Some(")"));
    assert_eq!(delimiter.actual_closing(), None);
    let opening = delimiter.opening_source().expect("opening source context");
    assert_eq!(opening.start_byte(), source.find('(').unwrap() as u32);
    assert_eq!(opening.line(), Some(2));
    assert_eq!(opening.column(), Some(3));
    assert_eq!(opening.token(), Some("("));

    let json = result.render_json();
    assert!(json.contains("\"kind\":\"SourceStructure\""));
    assert!(json.contains("\"reason_code\":\"unclosed_delimiter\""));
    assert!(json.contains("\"expected_closing\":\")\""));
    assert!(json.contains("\"actual_closing\":null"));
    assert!(json.contains("\"opening_source\":"));
    assert!(!json.contains(&package.path().to_string_lossy().to_string()));

    let human = result.render_human();
    assert!(human.contains("delimiter=unclosed_delimiter"));
    assert!(human.contains("expected_closing=)"));
    assert!(human.contains("opening=Draft/source.npa:byte["));
}

#[test]
fn mismatched_delimiter_reports_both_delimiters_without_message_parsing() {
    let package = TestPackage::new("mismatched");
    package.write("Draft/source.npa", "([)]");

    let result = run_package_check_source_structure(path_options(&package, &["Draft/source.npa"]));

    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.reason_code, "mismatched_closing_delimiter");
    let primary = diagnostic.source.as_ref().unwrap();
    assert_eq!(primary.line(), Some(1));
    assert_eq!(primary.column(), Some(3));
    assert_eq!(primary.token(), Some(")"));
    let delimiter = diagnostic.delimiter().unwrap();
    assert_eq!(delimiter.expected_closing(), Some("]"));
    assert_eq!(delimiter.actual_closing(), Some(")"));
    let opening = delimiter.opening_source().unwrap();
    assert_eq!(opening.line(), Some(1));
    assert_eq!(opening.column(), Some(2));
    assert_eq!(opening.token(), Some("["));
}

#[test]
fn path_check_distinguishes_invalid_utf8() {
    let package = TestPackage::new("invalid-utf8");
    package.write("Draft/source.npa", [0xff, 0xfe]);

    let result = run_package_check_source_structure(path_options(&package, &["Draft/source.npa"]));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "source_structure_invalid_utf8"
    );
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::SourceStructure);
}

#[test]
fn ordinary_lexer_failure_does_not_claim_delimiter_context() {
    let package = TestPackage::new("lexer-error");
    let source = "\"unterminated";
    package.write("Draft/source.npa", source);

    let result = run_package_check_source_structure(path_options(&package, &["Draft/source.npa"]));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::SourceStructure);
    assert_eq!(diagnostic.reason_code, "source_lexical_error");
    assert_eq!(diagnostic.field.as_deref(), Some("parser"));
    assert!(diagnostic.delimiter().is_none());
    let primary = diagnostic.source.as_ref().expect("lexer source context");
    assert_eq!(primary.start_byte(), 0);
    assert_eq!(primary.end_byte(), source.len() as u32);
}

#[test]
fn module_selection_checks_only_requested_registered_sources() {
    let package = TestPackage::new("module-selection");
    package.write("Proofs/Good/source.npa", "def good : Type := Type\n");
    package.write("Proofs/Bad/source.npa", "def bad : Type := (\n");
    package.write(
        PACKAGE_MANIFEST_PATH,
        valid_manifest(&format!(
            "{}{}",
            module_block("Proofs.Good", "Proofs/Good/source.npa"),
            module_block("Proofs.Bad", "Proofs/Bad/source.npa")
        )),
    );

    let selected = run_package_check_source_structure(check_source_structure_modules(
        common_options(package.path(), true),
        vec![Name::from_dotted("Proofs.Good")],
    ));
    assert_eq!(selected.exit_code(), CommandExitCode::Success);

    let full = run_package_check_source_structure(check_source_structure_all(common_options(
        package.path(),
        true,
    )));
    assert_eq!(full.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(full.diagnostics[0].module.as_deref(), Some("Proofs.Bad"));
    assert_eq!(full.diagnostics[0].reason_code, "unclosed_delimiter");
}

#[test]
fn unknown_module_fails_before_source_reads() {
    let package = TestPackage::new("unknown-module");
    package.write(
        PACKAGE_MANIFEST_PATH,
        valid_manifest(&module_block("Proofs.Good", "Missing/source.npa")),
    );

    let result = run_package_check_source_structure(check_source_structure_modules(
        common_options(package.path(), true),
        vec![Name::from_dotted("Proofs.Unknown")],
    ));

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "source_structure_module_unknown"
    );
    assert_eq!(
        result.diagnostics[0].module.as_deref(),
        Some("Proofs.Unknown")
    );
}

#[test]
fn cli_emits_structured_delimiter_json_and_exit_one() {
    let package = TestPackage::new("cli-json");
    package.write("Draft/source.npa", ")");

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check-source-structure", "--root"])
        .arg(package.path())
        .args(["--path", "Draft/source.npa", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"command\":\"package check-source-structure\""));
    assert!(stdout.contains("\"reason_code\":\"unexpected_closing_delimiter\""));
    assert!(stdout.contains("\"delimiter\":{\"kind\":\"unexpected_closing_delimiter\""));
    assert!(stdout.contains("\"expected_closing\":null"));
    assert!(stdout.contains("\"actual_closing\":\")\""));
    assert!(stdout.contains("\"opening_source\":null"));
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));
}

fn valid_manifest(modules: &str) -> String {
    format!(
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

{modules}
"#
    )
}

fn module_block(module: &str, source: &str) -> String {
    format!(
        r#"[[modules]]
module = "{module}"
source = "{source}"
certificate = "{source}.npcert"
imports = []
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
inductives = []
definitions = []
theorems = ["theorem"]
axioms = []
tags = []

"#
    )
}

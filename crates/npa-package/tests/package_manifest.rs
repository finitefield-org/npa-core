use std::{fs, path::Path};

use npa_package::{
    parse_and_validate_manifest_str, parse_manifest_str, parse_package_hash,
    validate_manifest_report, validate_manifest_source_report, PackageManifestError,
    PackageManifestErrorKind, PackageManifestErrorReason, PackageManifestResult,
    PackageManifestValidationReport, ResolvedModuleImportKind, PACKAGE_MANIFEST_SCHEMA,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const ONE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
const TWO_HASH: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const THREE_HASH: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
const FOUR_HASH: &str = "sha256:4444444444444444444444444444444444444444444444444444444444444444";

const VALID_PACKAGE_FIXTURES: &[&str] = &[
    "valid/minimal/npa-package.toml",
    "valid/with-external-import/npa-package.toml",
    "valid/proof-corpus-basic/npa-package.toml",
    "valid/proof-corpus-with-std-imports/npa-package.toml",
    "valid/same-package-imports/npa-package.toml",
    "valid/proof-corpus-equivalent/npa-package.toml",
    "valid/hash-value-mismatch-not-manifest-failure/npa-package.toml",
];

#[derive(Clone, Copy)]
struct InvalidPackageFixture {
    path: &'static str,
    kind: PackageManifestErrorKind,
    reason: PackageManifestErrorReason,
    error_path: &'static str,
    field: Option<&'static str>,
    expected: Option<&'static str>,
    actual: Option<&'static str>,
}

const INVALID_PACKAGE_FIXTURES: &[InvalidPackageFixture] = &[
    InvalidPackageFixture {
        path: "invalid/schema/wrong-schema/npa-package.toml",
        kind: PackageManifestErrorKind::UnsupportedVersion,
        reason: PackageManifestErrorReason::UnsupportedSchema,
        error_path: "schema",
        field: Some("schema"),
        expected: Some("npa.package.v0.1"),
        actual: Some("npa.package.v0.2"),
    },
    InvalidPackageFixture {
        path: "invalid/schema/missing-top-level-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::MissingField,
        error_path: "$",
        field: Some("package"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/missing-policy-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::MissingField,
        error_path: "policy",
        field: Some("allowed_axioms"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/missing-import-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::MissingField,
        error_path: "imports[0]",
        field: Some("export_hash"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/missing-module-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::MissingField,
        error_path: "modules[0]",
        field: Some("certificate"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/unknown-top-level-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "$",
        field: Some("unexpected_top_level"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/unknown-policy-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "policy",
        field: Some("unknown_policy_field"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/unknown-import-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "imports[0]",
        field: Some("latest"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/unknown-module-field/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "modules[0]",
        field: Some("unexpected_module_field"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/forbidden-trusted-status/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "$",
        field: Some("trusted_status"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/forbidden-checker-verdict/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "modules[0]",
        field: Some("checker_verdict"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/forbidden-registry-fetch/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::UnknownField,
        error_path: "$",
        field: Some("registry_url"),
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/schema/duplicate-top-level-key/npa-package.toml",
        kind: PackageManifestErrorKind::Schema,
        reason: PackageManifestErrorReason::DuplicateField,
        error_path: "$",
        field: None,
        expected: None,
        actual: None,
    },
    InvalidPackageFixture {
        path: "invalid/domain/package-name/npa-package.toml",
        kind: PackageManifestErrorKind::Domain,
        reason: PackageManifestErrorReason::InvalidPackageId,
        error_path: "package",
        field: None,
        expected: Some("lowercase ASCII package id"),
        actual: Some("Npa.Bad"),
    },
    InvalidPackageFixture {
        path: "invalid/domain/module-name/npa-package.toml",
        kind: PackageManifestErrorKind::Domain,
        reason: PackageManifestErrorReason::InvalidModuleName,
        error_path: "modules[0].module",
        field: None,
        expected: Some("canonical dotted name"),
        actual: Some("Fixture..Bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-expected-source-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "modules[0].expected_source_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-certificate-file-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "modules[0].expected_certificate_file_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-expected-export-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "modules[0].expected_export_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-expected-axiom-report-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "modules[0].expected_axiom_report_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-expected-certificate-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "modules[0].expected_certificate_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-import-export-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "imports[0].export_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/hash/bad-import-certificate-hash/npa-package.toml",
        kind: PackageManifestErrorKind::Hash,
        reason: PackageManifestErrorReason::InvalidHashFormat,
        error_path: "imports[0].certificate_hash",
        field: None,
        expected: Some("sha256:<64 lowercase hex>"),
        actual: Some("sha256:bad"),
    },
    InvalidPackageFixture {
        path: "invalid/path/absolute-source-path/npa-package.toml",
        kind: PackageManifestErrorKind::Path,
        reason: PackageManifestErrorReason::InvalidPath,
        error_path: "modules[0].source",
        field: None,
        expected: Some("lexical package-relative path"),
        actual: Some("/Fixture/Minimal/source.npa"),
    },
    InvalidPackageFixture {
        path: "invalid/path/source-escapes-root/npa-package.toml",
        kind: PackageManifestErrorKind::Path,
        reason: PackageManifestErrorReason::InvalidPath,
        error_path: "modules[0].source",
        field: None,
        expected: Some("lexical package-relative path"),
        actual: Some("../Fixture/Minimal/source.npa"),
    },
    InvalidPackageFixture {
        path: "invalid/duplicate/module-name/npa-package.toml",
        kind: PackageManifestErrorKind::Duplicate,
        reason: PackageManifestErrorReason::DuplicateModule,
        error_path: "modules[1].module",
        field: Some("module"),
        expected: Some("unique value"),
        actual: Some("Fixture.Duplicate"),
    },
    InvalidPackageFixture {
        path: "invalid/duplicate/external-import-module/npa-package.toml",
        kind: PackageManifestErrorKind::Duplicate,
        reason: PackageManifestErrorReason::DuplicateExternalImport,
        error_path: "imports[1].module",
        field: Some("module"),
        expected: Some("unique value"),
        actual: Some("Std.Logic.Eq"),
    },
    InvalidPackageFixture {
        path: "invalid/graph/local-external-collision/npa-package.toml",
        kind: PackageManifestErrorKind::Duplicate,
        reason: PackageManifestErrorReason::LocalExternalModuleCollision,
        error_path: "modules[0].module",
        field: Some("module"),
        expected: Some("unique value"),
        actual: Some("Std.Logic.Eq"),
    },
    InvalidPackageFixture {
        path: "invalid/graph/unknown-import/npa-package.toml",
        kind: PackageManifestErrorKind::Graph,
        reason: PackageManifestErrorReason::UnknownImport,
        error_path: "modules[0].imports[0]",
        field: Some("imports"),
        expected: Some("local module or hash-pinned top-level external import"),
        actual: Some("Std.Logic.Missing"),
    },
    InvalidPackageFixture {
        path: "invalid/graph/import-cycle/npa-package.toml",
        kind: PackageManifestErrorKind::Graph,
        reason: PackageManifestErrorReason::ImportCycle,
        error_path: "modules[1].imports[0]",
        field: Some("imports"),
        expected: Some("acyclic local module graph"),
        actual: Some("Fixture.Cycle.A"),
    },
    InvalidPackageFixture {
        path: "invalid/policy/axiom-policy-violation/npa-package.toml",
        kind: PackageManifestErrorKind::Policy,
        reason: PackageManifestErrorReason::DisallowedAxiom,
        error_path: "modules[0].axioms[0]",
        field: Some("axioms"),
        expected: Some("allowed axiom or allow_custom_axioms = true"),
        actual: Some("Classical.choice"),
    },
    InvalidPackageFixture {
        path: "invalid/policy/sorry-axiom-violation/npa-package.toml",
        kind: PackageManifestErrorKind::Policy,
        reason: PackageManifestErrorReason::DisallowedAxiom,
        error_path: "modules[0].axioms[0]",
        field: Some("axioms"),
        expected: Some("non-sorry axiom"),
        actual: Some("synthetic.sorry.Proof"),
    },
];

fn valid_manifest() -> String {
    format!(
        r#"schema = "{PACKAGE_MANIFEST_SCHEMA}"
package = "npa-proof-corpus"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
license = "Apache-2.0"
repository = "https://example.invalid/npa-proof-corpus"
description = "proof corpus fixture"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[imports]]
module = "Std.Logic.Eq"
package = "npa-std"
version = "0.1.0"
certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert"
export_hash = "{ZERO_HASH}"
certificate_hash = "{ZERO_HASH}"

[[modules]]
module = "Proofs.Ai.Basic"
source = "Proofs/Ai/Basic/source.npa"
certificate = "Proofs/Ai/Basic/certificate.npcert"
imports = ["Std.Logic.Eq"]
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
meta = "Proofs/Ai/Basic/meta.json"
replay = "Proofs/Ai/Basic/replay.json"
producer_profile = "human-surface-explicit-term"
inductives = []
definitions = []
theorems = ["id"]
axioms = []
tags = ["basic"]
"#
    )
}

fn assert_manifest_error(
    error: &PackageManifestError,
    kind: PackageManifestErrorKind,
    reason: PackageManifestErrorReason,
    path: &str,
    field: Option<&str>,
) {
    assert_eq!(error.kind, kind);
    assert_eq!(error.reason_code, reason);
    assert_eq!(error.reason_code.as_str(), reason.as_str());
    assert_eq!(error.path, path);
    assert_eq!(error.field.as_deref(), field);
}

fn assert_manifest_error_values(
    error: &PackageManifestError,
    expected: Option<&str>,
    actual: Option<&str>,
) {
    assert_eq!(error.expected_value.as_deref(), expected);
    assert_eq!(error.actual_value.as_deref(), actual);
}

fn package_fixture_source(relative_path: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/package")
        .join(relative_path);
    fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
}

fn all_package_fixture_paths() -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/package");
    let mut paths = Vec::new();
    collect_package_fixture_paths(&root, &root, &mut paths);
    paths.sort();
    paths
}

fn collect_package_fixture_paths(root: &Path, directory: &Path, paths: &mut Vec<String>) {
    for entry in fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()))
    {
        let entry = entry.unwrap_or_else(|error| {
            panic!(
                "failed to read fixture entry under {}: {error}",
                directory.display()
            )
        });
        let path = entry.path();
        if path.is_dir() {
            collect_package_fixture_paths(root, &path, paths);
        } else if path.file_name().and_then(|name| name.to_str()) == Some("npa-package.toml") {
            let relative = path
                .strip_prefix(root)
                .unwrap_or_else(|error| {
                    panic!(
                        "failed to relativize {} against {}: {error}",
                        path.display(),
                        root.display()
                    )
                })
                .to_str()
                .unwrap_or_else(|| panic!("fixture path is not utf-8: {}", path.display()))
                .replace('\\', "/");
            paths.push(relative);
        }
    }
}

fn validation_error(source: String) -> PackageManifestError {
    parse_and_validate_manifest_str(&source).unwrap_err()
}

fn report_error(source: String) -> PackageManifestError {
    let report = validate_manifest_source_report(&source);
    assert!(!report.is_valid());
    assert_eq!(report.errors().len(), 1);
    report.first_error().unwrap().clone()
}

fn manifest_with_root_entries(root_entries: &str, policy: &str) -> String {
    format!(
        r#"schema = "{PACKAGE_MANIFEST_SCHEMA}"
package = "npa-proof-corpus"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

{root_entries}

{policy}
"#
    )
}

fn module_block(module: &str, source: &str, certificate: &str) -> String {
    module_block_with_imports_and_hashes(module, source, certificate, "[]", ZERO_HASH, ZERO_HASH)
}

fn module_block_with_imports_and_hashes(
    module: &str,
    source: &str,
    certificate: &str,
    imports: &str,
    expected_export_hash: &str,
    expected_certificate_hash: &str,
) -> String {
    format!(
        r#"
[[modules]]
module = "{module}"
source = "{source}"
certificate = "{certificate}"
imports = {imports}
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{expected_export_hash}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{expected_certificate_hash}"
inductives = []
definitions = []
theorems = ["other"]
axioms = []
tags = []
"#
    )
}

fn external_import_block(module: &str, certificate: &str) -> String {
    format!(
        r#"
[[imports]]
module = "{module}"
package = "npa-std-extra"
version = "0.1.0"
certificate = "{certificate}"
export_hash = "{ZERO_HASH}"
certificate_hash = "{ZERO_HASH}"
"#
    )
}

#[test]
fn package_manifest_fixtures_expectations_cover_every_fixture_file() {
    let mut expected = VALID_PACKAGE_FIXTURES
        .iter()
        .copied()
        .chain(INVALID_PACKAGE_FIXTURES.iter().map(|fixture| fixture.path))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    expected.sort();

    assert_eq!(all_package_fixture_paths(), expected);
}

#[test]
fn package_manifest_fixtures_accept_valid_fixture_files() {
    for fixture in VALID_PACKAGE_FIXTURES {
        let source = package_fixture_source(fixture);
        let report = validate_manifest_source_report(&source);
        assert!(
            report.is_valid(),
            "{fixture}: unexpected fixture validation errors: {:?}",
            report.errors()
        );
    }
}

#[test]
fn package_manifest_fixtures_reject_invalid_fixture_files_with_structured_errors() {
    for fixture in INVALID_PACKAGE_FIXTURES {
        let source = package_fixture_source(fixture.path);
        let error = match parse_and_validate_manifest_str(&source) {
            Ok(_) => panic!("{} unexpectedly validated", fixture.path),
            Err(error) => error,
        };

        assert_manifest_error(
            &error,
            fixture.kind,
            fixture.reason,
            fixture.error_path,
            fixture.field,
        );
        if fixture.expected.is_some() || fixture.actual.is_some() {
            assert_manifest_error_values(&error, fixture.expected, fixture.actual);
        }
    }
}

#[test]
fn package_manifest_fixtures_proof_corpus_equivalent_covers_required_shape() {
    let source = package_fixture_source("valid/proof-corpus-equivalent/npa-package.toml");
    assert!(source.contains("not a replacement for proofs/manifest.toml"));

    let validated = parse_and_validate_manifest_str(&source).unwrap();
    let manifest = validated.manifest();
    let imports = manifest.imports.as_ref().unwrap();
    assert_eq!(imports.len(), 2);
    assert_eq!(imports[0].module.as_dotted(), "Std.Logic.Eq");
    assert_eq!(imports[1].module.as_dotted(), "Std.Nat.Basic");
    assert_eq!(manifest.policy.allowed_axioms[0].as_dotted(), "Eq.rec");

    let basic = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
        .unwrap();
    assert_eq!(basic.source.as_str(), "Proofs/Ai/Basic/source.npa");
    assert_ne!(
        basic.expected_source_hash,
        basic.expected_certificate_file_hash
    );
    assert!(!basic.theorems.as_ref().unwrap().is_empty());

    let eq_reasoning_index = manifest
        .modules
        .iter()
        .position(|module| module.module.as_dotted() == "Proofs.Ai.EqReasoning")
        .unwrap();
    let eq_reasoning = &manifest.modules[eq_reasoning_index];
    assert_eq!(
        eq_reasoning.axioms.as_ref().unwrap()[0].as_dotted(),
        "Eq.rec"
    );
    assert_eq!(eq_reasoning.imports[0].as_dotted(), "Std.Logic.Eq");
    assert_eq!(eq_reasoning.imports[1].as_dotted(), "Proofs.Ai.Basic");

    let resolved = &validated.graph().resolved_module_imports[eq_reasoning_index];
    assert_eq!(
        resolved[0].kind,
        ResolvedModuleImportKind::External { import_index: 0 }
    );
    assert_eq!(
        resolved[1].kind,
        ResolvedModuleImportKind::Local { module_index: 0 }
    );
}

#[test]
fn package_manifest_fixtures_accept_hash_values_without_checking_artifact_bytes() {
    let source =
        package_fixture_source("valid/hash-value-mismatch-not-manifest-failure/npa-package.toml");
    let validated = parse_and_validate_manifest_str(&source).unwrap();

    assert_eq!(
        validated.manifest().modules[0].source.as_str(),
        "Missing/Source/source.npa"
    );
    assert_eq!(
        validated.manifest().modules[0].certificate.as_str(),
        "Missing/Source/certificate.npcert"
    );
}

#[test]
fn package_manifest_parse_accepts_valid_closed_manifest() {
    let manifest = parse_manifest_str(&valid_manifest()).unwrap();

    assert_eq!(manifest.schema, PACKAGE_MANIFEST_SCHEMA);
    assert_eq!(manifest.package.as_str(), "npa-proof-corpus");
    assert_eq!(manifest.version.as_str(), "0.1.0");
    assert!(!manifest.policy.allow_custom_axioms);
    assert_eq!(manifest.policy.allowed_axioms[0].as_dotted(), "Eq.rec");
    assert_eq!(manifest.imports.as_ref().unwrap().len(), 1);
    assert_eq!(manifest.modules.len(), 1);
    assert_eq!(manifest.modules[0].module.as_dotted(), "Proofs.Ai.Basic");
    assert_eq!(
        manifest.modules[0].expected_export_hash.as_bytes(),
        &[0; 32]
    );
}

#[test]
fn package_manifest_parse_rejects_invalid_toml_before_schema_validation() {
    let error = parse_manifest_str(
        r#"schema = "npa.package.v0.1"
["#,
    )
    .unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::TomlSyntax,
        PackageManifestErrorReason::InvalidToml,
        "$",
        None,
    );
}

#[test]
fn package_manifest_parse_rejects_duplicate_key_as_schema_error() {
    let error = parse_manifest_str(
        r#"schema = "npa.package.v0.1"
schema = "npa.package.v0.1"
"#,
    )
    .unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::DuplicateField,
        "$",
        None,
    );
}

#[test]
fn package_manifest_closed_objects_reports_missing_required_field_path() {
    let source = valid_manifest().replace(
        r#"checker_profile = "npa.checker.reference.v0.1"
"#,
        "",
    );

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::MissingField,
        "$",
        Some("checker_profile"),
    );
}

#[test]
fn package_manifest_closed_objects_rejects_unknown_top_level_field() {
    let source = valid_manifest().replacen(
        r#"schema = "npa.package.v0.1"
"#,
        r#"schema = "npa.package.v0.1"
trusted_status = "verified"
"#,
        1,
    );

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::UnknownField,
        "$",
        Some("trusted_status"),
    );
}

#[test]
fn package_manifest_closed_objects_rejects_unknown_policy_field() {
    let source =
        valid_manifest().replacen("[policy]\n", "[policy]\nunknown_policy_field = true\n", 1);

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::UnknownField,
        "policy",
        Some("unknown_policy_field"),
    );
}

#[test]
fn package_manifest_closed_objects_rejects_unknown_import_field() {
    let source = valid_manifest().replacen("[[imports]]\n", "[[imports]]\nlatest = true\n", 1);

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::UnknownField,
        "imports[0]",
        Some("latest"),
    );
}

#[test]
fn package_manifest_closed_objects_rejects_unknown_module_field() {
    let source = valid_manifest().replacen(
        "[[modules]]\n",
        "[[modules]]\nchecker_result = \"accepted\"\n",
        1,
    );

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::UnknownField,
        "modules[0]",
        Some("checker_result"),
    );
}

#[test]
fn package_manifest_closed_objects_rejects_wrong_field_type() {
    let source = valid_manifest().replace(
        "allow_custom_axioms = false",
        r#"allow_custom_axioms = "false""#,
    );

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "policy.allow_custom_axioms",
        Some("allow_custom_axioms"),
    );
    assert_eq!(error.expected_value.as_deref(), Some("bool"));
    assert_eq!(error.actual_value.as_deref(), Some("string"));
}

#[test]
fn package_manifest_closed_objects_rejects_wrong_object_types() {
    let policy_error = parse_manifest_str(&manifest_with_root_entries(
        r#"policy = "strict"
modules = []"#,
        "",
    ))
    .unwrap_err();
    assert_manifest_error(
        &policy_error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "policy",
        Some("policy"),
    );
    assert_eq!(policy_error.expected_value.as_deref(), Some("table"));
    assert_eq!(policy_error.actual_value.as_deref(), Some("string"));

    let import_error = parse_manifest_str(&manifest_with_root_entries(
        r#"imports = "none"
modules = []"#,
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]"#,
    ))
    .unwrap_err();
    assert_manifest_error(
        &import_error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "imports",
        Some("imports"),
    );
    assert_eq!(import_error.expected_value.as_deref(), Some("array"));
    assert_eq!(import_error.actual_value.as_deref(), Some("string"));

    let module_error = parse_manifest_str(&manifest_with_root_entries(
        r#"modules = ["Proofs.Ai.Basic"]"#,
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]"#,
    ))
    .unwrap_err();
    assert_manifest_error(
        &module_error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "modules[0]",
        None,
    );
    assert_eq!(module_error.expected_value.as_deref(), Some("table"));
    assert_eq!(module_error.actual_value.as_deref(), Some("string"));
}

#[test]
fn package_manifest_closed_objects_rejects_wrong_array_item_type() {
    let source = valid_manifest().replace("imports = [\"Std.Logic.Eq\"]", "imports = [1]");

    let error = parse_manifest_str(&source).unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "modules[0].imports[0]",
        None,
    );
    assert_eq!(error.expected_value.as_deref(), Some("string"));
    assert_eq!(error.actual_value.as_deref(), Some("integer"));
}

#[test]
fn package_manifest_scalar_domains_accepts_valid_manifest() {
    let manifest = parse_and_validate_manifest_str(&valid_manifest()).unwrap();

    assert_eq!(manifest.manifest().package.as_str(), "npa-proof-corpus");
    assert_eq!(
        manifest.manifest().modules[0].module.as_dotted(),
        "Proofs.Ai.Basic"
    );
}

#[test]
fn package_manifest_scalar_domains_rejects_exact_schema_and_profile_mismatches() {
    let schema_error = validation_error(valid_manifest().replace(
        r#"schema = "npa.package.v0.1""#,
        r#"schema = "npa.package.v0.2""#,
    ));
    assert_manifest_error(
        &schema_error,
        PackageManifestErrorKind::UnsupportedVersion,
        PackageManifestErrorReason::UnsupportedSchema,
        "schema",
        Some("schema"),
    );
    assert_manifest_error_values(
        &schema_error,
        Some("npa.package.v0.1"),
        Some("npa.package.v0.2"),
    );

    let profile_error = validation_error(valid_manifest().replace(
        r#"kernel_profile = "npa.kernel.v0.1""#,
        r#"kernel_profile = "npa.kernel.v0.2""#,
    ));
    assert_manifest_error(
        &profile_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidProfile,
        "kernel_profile",
        Some("kernel_profile"),
    );
    assert_manifest_error_values(
        &profile_error,
        Some("npa.kernel.v0.1"),
        Some("npa.kernel.v0.2"),
    );
}

#[test]
fn package_manifest_scalar_domains_rejects_package_id_and_version_grammar() {
    let package_error = validation_error(valid_manifest().replace(
        r#"package = "npa-proof-corpus""#,
        r#"package = "Npa-proof-corpus""#,
    ));
    assert_manifest_error(
        &package_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidPackageId,
        "package",
        None,
    );

    let version_error =
        validation_error(valid_manifest().replace(r#"version = "0.1.0""#, r#"version = "0.01.0""#));
    assert_manifest_error(
        &version_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidVersion,
        "version",
        None,
    );

    let prerelease_error = validation_error(
        valid_manifest().replace(r#"version = "0.1.0""#, r#"version = "0.1.0-alpha""#),
    );
    assert_manifest_error(
        &prerelease_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidVersion,
        "version",
        None,
    );
}

#[test]
fn package_manifest_scalar_domains_aligns_names_with_npa_cert_canonical_names() {
    let module_error = validation_error(valid_manifest().replace(
        r#"module = "Proofs.Ai.Basic""#,
        r#"module = "Proofs..Basic""#,
    ));
    assert_manifest_error(
        &module_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidModuleName,
        "modules[0].module",
        None,
    );

    let import_name_error = validation_error(
        valid_manifest().replace(r#"imports = ["Std.Logic.Eq"]"#, r#"imports = ["Std..Eq"]"#),
    );
    assert_manifest_error(
        &import_name_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidModuleName,
        "modules[0].imports[0]",
        None,
    );

    let declaration_error =
        validation_error(valid_manifest().replace(r#"theorems = ["id"]"#, r#"theorems = [""]"#));
    assert_manifest_error(
        &declaration_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidDeclarationName,
        "modules[0].theorems[0]",
        None,
    );

    let axiom_error = validation_error(valid_manifest().replace(
        r#"allowed_axioms = ["Eq.rec"]"#,
        r#"allowed_axioms = ["Eq..rec"]"#,
    ));
    assert_manifest_error(
        &axiom_error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidAxiomName,
        "policy.allowed_axioms[0]",
        None,
    );
}

#[test]
fn package_manifest_paths_rejects_invalid_lexical_paths() {
    for (replacement, path) in [
        ("/Proofs/Ai/Basic/source.npa", "modules[0].source"),
        ("Proofs/Ai/../source.npa", "modules[0].source"),
        ("Proofs/Ai/./source.npa", "modules[0].source"),
        ("Proofs/Ai//source.npa", "modules[0].source"),
        (r#"Proofs\\Ai\\source.npa"#, "modules[0].source"),
        ("https://example.invalid/source.npa", "modules[0].source"),
    ] {
        let error = validation_error(valid_manifest().replace(
            r#"source = "Proofs/Ai/Basic/source.npa""#,
            &format!(r#"source = "{replacement}""#),
        ));
        assert_manifest_error(
            &error,
            PackageManifestErrorKind::Path,
            PackageManifestErrorReason::InvalidPath,
            path,
            None,
        );
    }

    let control_error = validation_error(valid_manifest().replace(
        r#"source = "Proofs/Ai/Basic/source.npa""#,
        r#"source = "Proofs/Ai/\u0008/source.npa""#,
    ));
    assert_manifest_error(
        &control_error,
        PackageManifestErrorKind::Path,
        PackageManifestErrorReason::InvalidPath,
        "modules[0].source",
        None,
    );
}

#[test]
fn package_manifest_paths_checks_external_import_certificate_path() {
    let error = validation_error(valid_manifest().replace(
        r#"certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert""#,
        r#"certificate = "file://vendor/npa-std/Std/Logic/Eq/certificate.npcert""#,
    ));

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Path,
        PackageManifestErrorReason::InvalidPath,
        "imports[0].certificate",
        None,
    );
}

#[test]
fn package_manifest_hashes_rejects_uppercase_hash_hex() {
    let error = parse_and_validate_manifest_str(&valid_manifest().replace(
        r#"expected_export_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000""#,
        r#"expected_export_hash = "sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA""#,
    ))
    .unwrap_err();

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Hash,
        PackageManifestErrorReason::InvalidHashFormat,
        "modules[0].expected_export_hash",
        None,
    );
}

#[test]
fn package_manifest_hashes_rejects_bad_hash_prefix_and_length() {
    let bad_prefix_error = parse_and_validate_manifest_str(&valid_manifest().replace(
        r#"expected_source_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000""#,
        r#"expected_source_hash = "sha512:0000000000000000000000000000000000000000000000000000000000000000""#,
    ))
    .unwrap_err();
    assert_manifest_error(
        &bad_prefix_error,
        PackageManifestErrorKind::Hash,
        PackageManifestErrorReason::InvalidHashFormat,
        "modules[0].expected_source_hash",
        None,
    );

    let bad_length_error = parse_and_validate_manifest_str(&valid_manifest().replacen(
        r#"certificate_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000""#,
        r#"certificate_hash = "sha256:0000""#,
        1,
    ))
    .unwrap_err();
    assert_manifest_error(
        &bad_length_error,
        PackageManifestErrorKind::Hash,
        PackageManifestErrorReason::InvalidHashFormat,
        "imports[0].certificate_hash",
        None,
    );
}

#[test]
fn package_manifest_duplicates_rejects_duplicate_module_names() {
    let source = valid_manifest()
        + &module_block(
            "Proofs.Ai.Basic",
            "Proofs/Ai/Duplicate/source.npa",
            "Proofs/Ai/Duplicate/certificate.npcert",
        );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateModule,
        "modules[1].module",
        Some("module"),
    );
    assert_manifest_error_values(&error, Some("unique value"), Some("Proofs.Ai.Basic"));
}

#[test]
fn package_manifest_duplicates_rejects_duplicate_external_import_modules() {
    let source = valid_manifest()
        + &external_import_block(
            "Std.Logic.Eq",
            "vendor/npa-std-extra/Std/Logic/Eq/certificate.npcert",
        );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateExternalImport,
        "imports[1].module",
        Some("module"),
    );
}

#[test]
fn package_manifest_duplicates_rejects_local_external_module_collision_before_import_resolution() {
    let source = valid_manifest().replace(
        r#"module = "Proofs.Ai.Basic"
source = "Proofs/Ai/Basic/source.npa""#,
        r#"module = "Std.Logic.Eq"
source = "Proofs/Ai/Basic/source.npa""#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::LocalExternalModuleCollision,
        "modules[0].module",
        Some("module"),
    );
}

#[test]
fn package_manifest_duplicates_rejects_duplicate_declaration_summaries_within_module() {
    let source = valid_manifest().replace("definitions = []", r#"definitions = ["id"]"#);

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateDeclaration,
        "modules[0].theorems[0]",
        Some("declaration"),
    );
}

#[test]
fn package_manifest_duplicates_rejects_duplicate_allowed_and_module_axioms() {
    let policy_error = validation_error(valid_manifest().replace(
        r#"allowed_axioms = ["Eq.rec"]"#,
        r#"allowed_axioms = ["Eq.rec", "Eq.rec"]"#,
    ));
    assert_manifest_error(
        &policy_error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateAxiom,
        "policy.allowed_axioms[1]",
        Some("axiom"),
    );

    let module_error = validation_error(
        valid_manifest().replace("axioms = []", r#"axioms = ["Eq.rec", "Eq.rec"]"#),
    );
    assert_manifest_error(
        &module_error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateAxiom,
        "modules[0].axioms[1]",
        Some("axiom"),
    );
}

#[test]
fn package_manifest_duplicates_rejects_duplicate_module_artifact_paths() {
    let same_module_error = validation_error(valid_manifest().replace(
        r#"certificate = "Proofs/Ai/Basic/certificate.npcert""#,
        r#"certificate = "Proofs/Ai/Basic/source.npa""#,
    ));
    assert_manifest_error(
        &same_module_error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateArtifactPath,
        "modules[0].certificate",
        Some("artifact_path"),
    );

    let cross_module_error = validation_error(
        valid_manifest()
            + &module_block(
                "Proofs.Ai.Other",
                "Proofs/Ai/Basic/source.npa",
                "Proofs/Ai/Other/certificate.npcert",
            ),
    );
    assert_manifest_error(
        &cross_module_error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateArtifactPath,
        "modules[1].source",
        Some("artifact_path"),
    );
}

#[test]
fn package_manifest_duplicates_checks_optional_artifact_paths_only_when_present() {
    let optional_duplicate_error = validation_error(valid_manifest().replace(
        r#"meta = "Proofs/Ai/Basic/meta.json""#,
        r#"meta = "Proofs/Ai/Basic/source.npa""#,
    ));
    assert_manifest_error(
        &optional_duplicate_error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateArtifactPath,
        "modules[0].meta",
        Some("artifact_path"),
    );

    let source_without_optional_paths = valid_manifest()
        .replace(
            r#"meta = "Proofs/Ai/Basic/meta.json"
"#,
            "",
        )
        .replace(
            r#"replay = "Proofs/Ai/Basic/replay.json"
"#,
            "",
        )
        + &module_block(
            "Proofs.Ai.Other",
            "Proofs/Ai/Other/source.npa",
            "Proofs/Ai/Other/certificate.npcert",
        );

    parse_and_validate_manifest_str(&source_without_optional_paths).unwrap();
}

#[test]
fn package_manifest_import_resolution_resolves_local_and_external_imports() {
    let source = valid_manifest()
        .replacen(
            &format!(r#"export_hash = "{ZERO_HASH}""#),
            &format!(r#"export_hash = "{THREE_HASH}""#),
            1,
        )
        .replacen(
            &format!(r#"certificate_hash = "{ZERO_HASH}""#),
            &format!(r#"certificate_hash = "{FOUR_HASH}""#),
            1,
        )
        .replace(
            r#"imports = ["Std.Logic.Eq"]"#,
            r#"imports = ["Proofs.Ai.Dependency", "Std.Logic.Eq"]"#,
        )
        + &module_block_with_imports_and_hashes(
            "Proofs.Ai.Dependency",
            "Proofs/Ai/Dependency/source.npa",
            "Proofs/Ai/Dependency/certificate.npcert",
            "[]",
            ONE_HASH,
            TWO_HASH,
        );

    let manifest = parse_and_validate_manifest_str(&source).unwrap();
    let graph = manifest.graph();

    assert_eq!(graph.resolved_module_imports.len(), 2);
    assert_eq!(
        graph.resolved_module_imports[0][0].kind,
        ResolvedModuleImportKind::Local { module_index: 1 }
    );
    assert_eq!(
        graph.resolved_module_imports[0][0].export_hash,
        parse_package_hash(ONE_HASH, "test.local_export").unwrap()
    );
    assert_eq!(
        graph.resolved_module_imports[0][0].certificate_hash,
        parse_package_hash(TWO_HASH, "test.local_certificate").unwrap()
    );
    assert_eq!(
        graph.resolved_module_imports[0][1].kind,
        ResolvedModuleImportKind::External { import_index: 0 }
    );
    assert_eq!(
        graph.resolved_module_imports[0][1].export_hash,
        parse_package_hash(THREE_HASH, "test.external_export").unwrap()
    );
    assert_eq!(
        graph.resolved_module_imports[0][1].certificate_hash,
        parse_package_hash(FOUR_HASH, "test.external_certificate").unwrap()
    );
    assert_eq!(graph.topological_order, vec![1, 0]);
}

#[test]
fn package_manifest_import_resolution_rejects_module_name_only_external_import() {
    let source = valid_manifest().replace(
        r#"imports = ["Std.Logic.Eq"]"#,
        r#"imports = ["Std.Logic.Missing"]"#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Graph,
        PackageManifestErrorReason::UnknownImport,
        "modules[0].imports[0]",
        Some("imports"),
    );
    assert_manifest_error_values(
        &error,
        Some("local module or hash-pinned top-level external import"),
        Some("Std.Logic.Missing"),
    );
}

#[test]
fn package_manifest_import_resolution_rejects_unpinned_external_before_graph() {
    let source = valid_manifest().replacen(
        &format!(
            r#"export_hash = "{ZERO_HASH}"
"#
        ),
        "",
        1,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::MissingField,
        "imports[0]",
        Some("export_hash"),
    );
}

#[test]
fn package_manifest_import_resolution_orders_independent_modules_by_source_order() {
    let modules = module_block(
        "Proofs.Zeta",
        "Proofs/Zeta/source.npa",
        "Proofs/Zeta/certificate.npcert",
    ) + &module_block(
        "Proofs.Alpha",
        "Proofs/Alpha/source.npa",
        "Proofs/Alpha/certificate.npcert",
    );
    let source = manifest_with_root_entries(
        &modules,
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]"#,
    );

    let manifest = parse_and_validate_manifest_str(&source).unwrap();

    assert_eq!(manifest.graph().topological_order, vec![0, 1]);
}

#[test]
fn package_manifest_import_cycles_rejects_self_cycle() {
    let source = valid_manifest().replace(
        r#"imports = ["Std.Logic.Eq"]"#,
        r#"imports = ["Proofs.Ai.Basic"]"#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Graph,
        PackageManifestErrorReason::ImportCycle,
        "modules[0].imports[0]",
        Some("imports"),
    );
    assert_manifest_error_values(
        &error,
        Some("acyclic local module graph"),
        Some("Proofs.Ai.Basic"),
    );
}

#[test]
fn package_manifest_import_cycles_rejects_multi_module_cycle_with_stable_path() {
    let source = valid_manifest().replace(
        r#"imports = ["Std.Logic.Eq"]"#,
        r#"imports = ["Proofs.Ai.Dependency"]"#,
    ) + &module_block_with_imports_and_hashes(
        "Proofs.Ai.Dependency",
        "Proofs/Ai/Dependency/source.npa",
        "Proofs/Ai/Dependency/certificate.npcert",
        r#"["Proofs.Ai.Basic"]"#,
        ONE_HASH,
        TWO_HASH,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Graph,
        PackageManifestErrorReason::ImportCycle,
        "modules[1].imports[0]",
        Some("imports"),
    );
    assert_manifest_error_values(
        &error,
        Some("acyclic local module graph"),
        Some("Proofs.Ai.Basic"),
    );
}

#[test]
fn package_manifest_axiom_policy_accepts_listed_module_axioms() {
    let source = valid_manifest().replace("axioms = []", r#"axioms = ["Eq.rec"]"#);

    let manifest = parse_and_validate_manifest_str(&source).unwrap();

    assert_eq!(
        manifest.manifest().modules[0].axioms.as_ref().unwrap()[0].as_dotted(),
        "Eq.rec"
    );
}

#[test]
fn package_manifest_axiom_policy_rejects_unlisted_axioms_when_custom_axioms_are_disabled() {
    let source = valid_manifest().replace("axioms = []", r#"axioms = ["Classical.choice"]"#);

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Policy,
        PackageManifestErrorReason::DisallowedAxiom,
        "modules[0].axioms[0]",
        Some("axioms"),
    );
    assert_manifest_error_values(
        &error,
        Some("allowed axiom or allow_custom_axioms = true"),
        Some("Classical.choice"),
    );
}

#[test]
fn package_manifest_axiom_policy_accepts_recorded_custom_axioms_when_enabled() {
    let source = valid_manifest()
        .replace("allow_custom_axioms = false", "allow_custom_axioms = true")
        .replace("axioms = []", r#"axioms = ["Classical.choice"]"#);

    let manifest = parse_and_validate_manifest_str(&source).unwrap();

    assert!(manifest.manifest().policy.allow_custom_axioms);
    assert_eq!(
        manifest.manifest().modules[0].axioms.as_ref().unwrap()[0].as_dotted(),
        "Classical.choice"
    );
}

#[test]
fn package_manifest_axiom_policy_rejects_sorry_even_when_custom_axioms_are_enabled() {
    let source = valid_manifest()
        .replace("allow_custom_axioms = false", "allow_custom_axioms = true")
        .replace("axioms = []", r#"axioms = ["sorry.synthetic"]"#);

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Policy,
        PackageManifestErrorReason::DisallowedAxiom,
        "modules[0].axioms[0]",
        Some("axioms"),
    );
    assert_manifest_error_values(&error, Some("non-sorry axiom"), Some("sorry.synthetic"));
}

#[test]
fn package_manifest_axiom_policy_rejects_sorry_allowed_axioms() {
    let source = valid_manifest().replace(
        r#"allowed_axioms = ["Eq.rec"]"#,
        r#"allowed_axioms = ["Eq.rec", "synthetic.sorry.Proof"]"#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Policy,
        PackageManifestErrorReason::DisallowedAxiom,
        "policy.allowed_axioms[1]",
        Some("allowed_axioms"),
    );
    assert_manifest_error_values(
        &error,
        Some("non-sorry axiom"),
        Some("synthetic.sorry.Proof"),
    );
}

#[test]
fn package_manifest_proof_acceptance_negative_axiom_fixtures_reject_with_policy_reason_codes() {
    for fixture in [
        (
            "invalid/policy/axiom-policy-violation/npa-package.toml",
            Some("allowed axiom or allow_custom_axioms = true"),
            Some("Classical.choice"),
        ),
        (
            "invalid/policy/sorry-axiom-violation/npa-package.toml",
            Some("non-sorry axiom"),
            Some("synthetic.sorry.Proof"),
        ),
    ] {
        let error = validation_error(package_fixture_source(fixture.0));

        assert_manifest_error(
            &error,
            PackageManifestErrorKind::Policy,
            PackageManifestErrorReason::DisallowedAxiom,
            "modules[0].axioms[0]",
            Some("axioms"),
        );
        assert_manifest_error_values(&error, fixture.1, fixture.2);
        assert_eq!(error.reason_code.as_str(), "disallowed_axiom");
    }
}

#[test]
fn package_manifest_axiom_policy_rejects_duplicate_allowed_axioms_before_policy() {
    let source = valid_manifest().replace(
        r#"allowed_axioms = ["Eq.rec"]"#,
        r#"allowed_axioms = ["Eq.rec", "Eq.rec"]"#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateAxiom,
        "policy.allowed_axioms[1]",
        Some("axiom"),
    );
}

#[test]
fn package_manifest_axiom_policy_rejects_allowed_axiom_name_grammar_before_policy() {
    let source = valid_manifest().replace(
        r#"allowed_axioms = ["Eq.rec"]"#,
        r#"allowed_axioms = ["Eq..rec"]"#,
    );

    let error = validation_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Domain,
        PackageManifestErrorReason::InvalidAxiomName,
        "policy.allowed_axioms[0]",
        None,
    );
}

#[test]
fn package_manifest_errors_public_report_and_result_types_are_usable() {
    let source = valid_manifest();
    let report: PackageManifestValidationReport = validate_manifest_source_report(&source);
    assert!(report.is_valid());
    assert!(report.errors().is_empty());
    assert_eq!(report.first_error(), None);
    assert!(report.clone().into_errors().is_empty());

    let parsed_report = validate_manifest_report(parse_manifest_str(&source).unwrap());
    assert!(parsed_report.is_valid());

    let result: PackageManifestResult<_> = parse_and_validate_manifest_str(&source);
    assert!(result.is_ok());
}

#[test]
fn package_manifest_errors_report_exposes_structured_schema_values() {
    let source = valid_manifest().replace(
        "allow_custom_axioms = false",
        r#"allow_custom_axioms = "false""#,
    );

    let error = report_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "policy.allow_custom_axioms",
        Some("allow_custom_axioms"),
    );
    assert_manifest_error_values(&error, Some("bool"), Some("string"));
}

#[test]
fn package_manifest_errors_earlier_schema_pass_suppresses_later_errors() {
    let source = valid_manifest()
        .replace(
            "allow_custom_axioms = false",
            r#"allow_custom_axioms = "false""#,
        )
        .replace(
            r#"imports = ["Std.Logic.Eq"]"#,
            r#"imports = ["Std.Logic.Missing"]"#,
        )
        .replace("axioms = []", r#"axioms = ["Classical.choice"]"#);

    let error = report_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Schema,
        PackageManifestErrorReason::WrongType,
        "policy.allow_custom_axioms",
        Some("allow_custom_axioms"),
    );
}

#[test]
fn package_manifest_errors_earlier_duplicate_pass_suppresses_graph_and_policy() {
    let source = valid_manifest()
        .replace(
            r#"imports = ["Std.Logic.Eq"]"#,
            r#"imports = ["Std.Logic.Missing"]"#,
        )
        .replace("axioms = []", r#"axioms = ["Classical.choice"]"#)
        + &module_block(
            "Proofs.Ai.Basic",
            "Proofs/Ai/Duplicate/source.npa",
            "Proofs/Ai/Duplicate/certificate.npcert",
        );

    let error = report_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Duplicate,
        PackageManifestErrorReason::DuplicateModule,
        "modules[1].module",
        Some("module"),
    );
    assert_manifest_error_values(&error, Some("unique value"), Some("Proofs.Ai.Basic"));
}

#[test]
fn package_manifest_errors_graph_pass_suppresses_policy() {
    let source = valid_manifest()
        .replace(
            r#"imports = ["Std.Logic.Eq"]"#,
            r#"imports = ["Std.Logic.Missing"]"#,
        )
        .replace("axioms = []", r#"axioms = ["Classical.choice"]"#);

    let error = report_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Graph,
        PackageManifestErrorReason::UnknownImport,
        "modules[0].imports[0]",
        Some("imports"),
    );
    assert_manifest_error_values(
        &error,
        Some("local module or hash-pinned top-level external import"),
        Some("Std.Logic.Missing"),
    );
}

#[test]
fn package_manifest_errors_same_pass_path_order_is_deterministic() {
    let source = valid_manifest()
        .replace(
            r#"certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert""#,
            r#"certificate = "file://vendor/npa-std/Std/Logic/Eq/certificate.npcert""#,
        )
        .replace(
            r#"source = "Proofs/Ai/Basic/source.npa""#,
            r#"source = "/Proofs/Ai/Basic/source.npa""#,
        );

    let error = report_error(source);

    assert_manifest_error(
        &error,
        PackageManifestErrorKind::Path,
        PackageManifestErrorReason::InvalidPath,
        "imports[0].certificate",
        None,
    );
    assert_manifest_error_values(
        &error,
        Some("lexical package-relative path"),
        Some("file://vendor/npa-std/Std/Logic/Eq/certificate.npcert"),
    );
}

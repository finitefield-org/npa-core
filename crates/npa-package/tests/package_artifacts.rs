use std::{fs, path::PathBuf};

use npa_cert::Name;
use npa_package::{
    compute_package_axiom_report_hash, compute_package_theorem_index_hash, format_package_hash,
    parse_package_axiom_report_json, parse_package_hash, parse_package_theorem_index_json,
    PackageArtifactError, PackageArtifactErrorKind, PackageArtifactErrorReason,
    PackageArtifactFileReference, PackageArtifactOrigin, PackageArtifactPolicy,
    PackageAxiomPolicyStatus, PackageAxiomPolicyStatusKind, PackageAxiomReference,
    PackageAxiomReport, PackageAxiomReportModule, PackageAxiomReportSummary, PackageCheckerMode,
    PackageCheckerSummary, PackageGlobalRef, PackageGlobalRefView, PackageHash, PackageId,
    PackagePath, PackageTheoremIndex, PackageTheoremIndexArtifact, PackageTheoremIndexEntry,
    PackageTheoremIndexKind, PackageTheoremIndexMode, PackageTheoremIndexSummary,
    PackageTheoremStatement, PackageVersion, PACKAGE_AXIOM_REPORT_SCHEMA,
    PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE, PACKAGE_THEOREM_INDEX_SCHEMA,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const ONE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
const TWO_HASH: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const THREE_HASH: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
const FOUR_HASH: &str = "sha256:4444444444444444444444444444444444444444444444444444444444444444";
const FIVE_HASH: &str = "sha256:5555555555555555555555555555555555555555555555555555555555555555";
const SIX_HASH: &str = "sha256:6666666666666666666666666666666666666666666666666666666666666666";
const SEVEN_HASH: &str = "sha256:7777777777777777777777777777777777777777777777777777777777777777";
const EIGHT_HASH: &str = "sha256:8888888888888888888888888888888888888888888888888888888888888888";
const NINE_HASH: &str = "sha256:9999999999999999999999999999999999999999999999999999999999999999";
const A_HASH: &str = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const B_HASH: &str = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const C_HASH: &str = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const D_HASH: &str = "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const E_HASH: &str = "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";

fn hash(value: &str) -> PackageHash {
    parse_package_hash(value, "test").unwrap()
}

fn name(value: &str) -> Name {
    Name::from_dotted(value)
}

fn file_ref(path: &str, file_hash: &str) -> PackageArtifactFileReference {
    PackageArtifactFileReference {
        path: PackagePath::new(path),
        file_hash: hash(file_hash),
    }
}

fn axiom_ref(module: &str, name_value: &str) -> PackageAxiomReference {
    PackageAxiomReference {
        module: name(module),
        name: name(name_value),
        export_hash: hash(THREE_HASH),
        decl_interface_hash: hash(FOUR_HASH),
    }
}

fn checker_summary(module: &str) -> PackageCheckerSummary {
    PackageCheckerSummary {
        module: name(module),
        checker: "npa-kernel".to_owned(),
        profile: "npa.checker.reference.v0.1".to_owned(),
        mode: PackageCheckerMode::Fast,
        status: "passed".to_owned(),
        export_hash: hash(THREE_HASH),
        certificate_hash: hash(FOUR_HASH),
        axiom_report_hash: hash(FIVE_HASH),
    }
}

fn base_axiom_report() -> PackageAxiomReport {
    PackageAxiomReport {
        schema: PACKAGE_AXIOM_REPORT_SCHEMA.to_owned(),
        package: PackageId::new("npa-proof-corpus"),
        version: PackageVersion::new("0.1.0"),
        manifest: file_ref("npa-package.toml", ZERO_HASH),
        package_lock: file_ref("generated/package-lock.json", ONE_HASH),
        policy: PackageArtifactPolicy {
            allow_custom_axioms: false,
            allowed_axioms: vec![name("Eq.rec")],
        },
        modules: vec![
            PackageAxiomReportModule {
                module: name("Proofs.Z"),
                origin: PackageArtifactOrigin::External,
                export_hash: hash(SIX_HASH),
                certificate_hash: hash(SEVEN_HASH),
                axiom_report_hash: hash(EIGHT_HASH),
                certificate_file_hash: hash(NINE_HASH),
                direct_axioms: vec![],
                transitive_axioms: vec![],
                policy_status: PackageAxiomPolicyStatus {
                    status: PackageAxiomPolicyStatusKind::Ok,
                    violations: vec![],
                },
            },
            PackageAxiomReportModule {
                module: name("Proofs.A"),
                origin: PackageArtifactOrigin::Local,
                export_hash: hash(THREE_HASH),
                certificate_hash: hash(FOUR_HASH),
                axiom_report_hash: hash(FIVE_HASH),
                certificate_file_hash: hash(TWO_HASH),
                direct_axioms: vec![axiom_ref("Proofs.A", "Eq.rec")],
                transitive_axioms: vec![axiom_ref("Proofs.A", "Eq.rec")],
                policy_status: PackageAxiomPolicyStatus {
                    status: PackageAxiomPolicyStatusKind::Ok,
                    violations: vec![],
                },
            },
        ],
        checker_summaries: vec![checker_summary("Proofs.A")],
        summary: PackageAxiomReportSummary {
            module_count: 2,
            local_module_count: 1,
            external_module_count: 1,
            direct_axiom_count: 1,
            transitive_axiom_count: 1,
            policy_violation_count: 0,
        },
        package_axiom_report_hash: hash(ZERO_HASH),
    }
}

fn global_ref(module: &str, name_value: &str, certificate_hash: &str) -> PackageGlobalRef {
    PackageGlobalRef {
        module: name(module),
        name: name(name_value),
        export_hash: hash(THREE_HASH),
        certificate_hash: hash(certificate_hash),
        decl_interface_hash: hash(FOUR_HASH),
    }
}

fn global_ref_view(module: &str, name_value: &str) -> PackageGlobalRefView {
    PackageGlobalRefView {
        module: name(module),
        name: name(name_value),
        export_hash: hash(THREE_HASH),
        decl_interface_hash: hash(FOUR_HASH),
    }
}

fn theorem_entry(
    module: &str,
    name_value: &str,
    kind: PackageTheoremIndexKind,
) -> PackageTheoremIndexEntry {
    let has_axiom = kind == PackageTheoremIndexKind::Theorem;
    PackageTheoremIndexEntry {
        global_ref: global_ref(module, name_value, FIVE_HASH),
        kind,
        statement: PackageTheoremStatement {
            core_hash: hash(SIX_HASH),
            head: Some(global_ref_view(module, name_value)),
            constants: vec![
                global_ref_view("Proofs.Z", "helper"),
                global_ref_view("Proofs.A", "base"),
            ],
        },
        modes: vec![
            PackageTheoremIndexMode::Exact,
            PackageTheoremIndexMode::Apply,
        ],
        tags: vec!["logic".to_owned(), "core".to_owned()],
        axiom_dependencies: if has_axiom {
            vec![axiom_ref("Proofs.A", "Eq.rec")]
        } else {
            vec![]
        },
        module_axiom_report_hash: hash(SEVEN_HASH),
        artifact: PackageTheoremIndexArtifact {
            origin: PackageArtifactOrigin::Local,
            certificate: PackagePath::new(format!(
                "{}/certificate.npcert",
                module.replace('.', "/")
            )),
        },
    }
}

fn base_theorem_index() -> PackageTheoremIndex {
    PackageTheoremIndex {
        schema: PACKAGE_THEOREM_INDEX_SCHEMA.to_owned(),
        package: PackageId::new("npa-proof-corpus"),
        version: PackageVersion::new("0.1.0"),
        manifest: file_ref("npa-package.toml", ZERO_HASH),
        package_lock: file_ref("generated/package-lock.json", ONE_HASH),
        index_profile: PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE.to_owned(),
        entries: vec![
            theorem_entry("Proofs.Z", "z_axiom", PackageTheoremIndexKind::Axiom),
            theorem_entry("Proofs.A", "a_theorem", PackageTheoremIndexKind::Theorem),
        ],
        checker_summaries: vec![checker_summary("Proofs.A")],
        summary: PackageTheoremIndexSummary {
            entry_count: 2,
            theorem_count: 1,
            axiom_count: 1,
            module_count: 2,
            entries_with_axioms_count: 1,
        },
        theorem_index_hash: hash(ZERO_HASH),
    }
}

fn assert_artifact_error(
    error: PackageArtifactError,
    kind: PackageArtifactErrorKind,
    reason: PackageArtifactErrorReason,
    path: &str,
    field: Option<&str>,
) {
    assert_eq!(error.kind, kind);
    assert_eq!(error.reason_code, reason);
    assert_eq!(error.reason_code.as_str(), reason.as_str());
    assert_eq!(error.path, path);
    assert_eq!(error.field.as_deref(), field);
}

#[test]
fn package_artifacts_checked_in_generated_axiom_report_and_theorem_index_parse_source_free() {
    let root = repo_root().join("proofs/generated");
    let report_source = fs::read_to_string(root.join("axiom-report.json")).unwrap();
    let index_source = fs::read_to_string(root.join("theorem-index.json")).unwrap();
    let report = parse_package_axiom_report_json(&report_source).unwrap();
    let index = parse_package_theorem_index_json(&index_source).unwrap();

    assert_eq!(report.schema, PACKAGE_AXIOM_REPORT_SCHEMA);
    assert_eq!(index.schema, PACKAGE_THEOREM_INDEX_SCHEMA);
    assert_eq!(report.package, index.package);
    assert_eq!(report.version, index.version);
    assert_eq!(
        u64::try_from(report.modules.len()).unwrap(),
        report.summary.module_count
    );
    assert_eq!(
        u64::try_from(index.entries.len()).unwrap(),
        index.summary.entry_count
    );
    assert_eq!(
        report.package_lock.path.as_str(),
        "generated/package-lock.json"
    );
    assert_eq!(
        index.package_lock.path.as_str(),
        "generated/package-lock.json"
    );
    assert_no_source_boundary_fields(&report_source);
    assert_no_source_boundary_fields(&index_source);
}

#[test]
fn package_axiom_report_schema_constants_and_rejections() {
    let report = base_axiom_report().with_computed_hash().unwrap();
    let canonical = report.canonical_json().unwrap();
    let parsed = parse_package_axiom_report_json(&canonical).unwrap();

    assert_eq!(parsed.schema, "npa.package.axiom_report.v0.1");
    assert_ne!(parsed.schema, "npa.independent-checker.axiom_report.v1");
    assert_ne!(parsed.schema, "npa.std-library.std-axiom-report.v1");

    let unknown_source = canonical.replacen(
        r#""package":"npa-proof-corpus""#,
        r#""source":"Proofs/A/source.npa","package":"npa-proof-corpus""#,
        1,
    );
    assert_artifact_error(
        parse_package_axiom_report_json(&unknown_source).unwrap_err(),
        PackageArtifactErrorKind::ArtifactSchema,
        PackageArtifactErrorReason::UnknownField,
        "$",
        Some("source"),
    );

    let absolute_path = canonical.replacen("npa-package.toml", "/tmp/npa-package.toml", 1);
    assert_artifact_error(
        parse_package_axiom_report_json(&absolute_path).unwrap_err(),
        PackageArtifactErrorKind::Path,
        PackageArtifactErrorReason::InvalidPath,
        "manifest.path",
        None,
    );

    let duplicate_module = canonical.replacen(
        r#""module":"Proofs.Z","origin":"external""#,
        r#""module":"Proofs.A","origin":"external""#,
        1,
    );
    assert_artifact_error(
        parse_package_axiom_report_json(&duplicate_module).unwrap_err(),
        PackageArtifactErrorKind::Duplicate,
        PackageArtifactErrorReason::DuplicateModule,
        "modules[1].module",
        Some("module"),
    );
}

#[test]
fn package_theorem_index_schema_constants_and_rejections() {
    let index = base_theorem_index().with_computed_hash().unwrap();
    let canonical = index.canonical_json().unwrap();
    let parsed = parse_package_theorem_index_json(&canonical).unwrap();

    assert_eq!(parsed.schema, "npa.package.theorem_index.v0.1");
    assert_ne!(parsed.schema, "npa.std-library.std-theorem-index.v1");

    let source_payload = canonical.replacen(
        r#""entries":["#,
        r#""replay":"Proofs/A/replay.json","entries":["#,
        1,
    );
    assert_artifact_error(
        parse_package_theorem_index_json(&source_payload).unwrap_err(),
        PackageArtifactErrorKind::ArtifactSchema,
        PackageArtifactErrorReason::UnknownField,
        "$",
        Some("replay"),
    );

    let registry_url = canonical.replacen(
        "Proofs/A/certificate.npcert",
        "https://registry.example/Proofs/A/certificate.npcert",
        1,
    );
    assert_artifact_error(
        parse_package_theorem_index_json(&registry_url).unwrap_err(),
        PackageArtifactErrorKind::Path,
        PackageArtifactErrorReason::InvalidPath,
        "entries[0].artifact.certificate",
        None,
    );

    let duplicate_entry = canonical.replacen(
        r#""global_ref":{"module":"Proofs.Z","name":"z_axiom""#,
        r#""global_ref":{"module":"Proofs.A","name":"a_theorem""#,
        1,
    );
    assert_artifact_error(
        parse_package_theorem_index_json(&duplicate_entry).unwrap_err(),
        PackageArtifactErrorKind::Duplicate,
        PackageArtifactErrorReason::DuplicateTheoremEntry,
        "entries[1].global_ref",
        Some("global_ref"),
    );
}

#[test]
fn package_artifact_canonical_json_sorts_and_hashes() {
    let report = base_axiom_report().with_computed_hash().unwrap();
    let report_json = report.canonical_json().unwrap();
    let report_hash = report.package_axiom_report_hash;

    assert!(
        report_json.find(r#""module":"Proofs.A""#).unwrap()
            < report_json.find(r#""module":"Proofs.Z""#).unwrap()
    );
    let mut report_with_changed_self_hash = report.clone();
    report_with_changed_self_hash.package_axiom_report_hash = hash(A_HASH);
    assert_eq!(
        compute_package_axiom_report_hash(&report_with_changed_self_hash).unwrap(),
        report_hash
    );
    let stale_report = report_json.replace(&format_package_hash(&report_hash), B_HASH);
    assert_artifact_error(
        parse_package_axiom_report_json(&stale_report).unwrap_err(),
        PackageArtifactErrorKind::SelfHash,
        PackageArtifactErrorReason::SelfHashMismatch,
        "package_axiom_report_hash",
        Some("package_axiom_report_hash"),
    );

    let index = base_theorem_index().with_computed_hash().unwrap();
    let index_json = index.canonical_json().unwrap();
    let index_hash = index.theorem_index_hash;

    assert!(
        index_json.find(r#""name":"a_theorem""#).unwrap()
            < index_json.find(r#""name":"z_axiom""#).unwrap()
    );
    assert!(index_json.contains(r#""modes":["apply","exact"]"#));
    assert!(index_json.contains(r#""tags":["core","logic"]"#));
    let mut index_with_changed_self_hash = index.clone();
    index_with_changed_self_hash.theorem_index_hash = hash(C_HASH);
    assert_eq!(
        compute_package_theorem_index_hash(&index_with_changed_self_hash).unwrap(),
        index_hash
    );
    let stale_index = index_json.replace(&format_package_hash(&index_hash), D_HASH);
    assert_artifact_error(
        parse_package_theorem_index_json(&stale_index).unwrap_err(),
        PackageArtifactErrorKind::SelfHash,
        PackageArtifactErrorReason::SelfHashMismatch,
        "theorem_index_hash",
        Some("theorem_index_hash"),
    );

    let non_canonical_index = index_json.replacen(
        r#""modes":["apply","exact"]"#,
        r#""modes":["exact","apply"]"#,
        1,
    );
    assert_artifact_error(
        parse_package_theorem_index_json(&non_canonical_index).unwrap_err(),
        PackageArtifactErrorKind::CanonicalJson,
        PackageArtifactErrorReason::NonCanonicalOrder,
        "$",
        None,
    );

    assert_ne!(format_package_hash(&report_hash), E_HASH);
    assert_ne!(format_package_hash(&index_hash), E_HASH);
}

fn assert_no_source_boundary_fields(source: &str) {
    for forbidden in [
        r#""source""#,
        r#""replay""#,
        r#""meta""#,
        "manifest.toml",
        ".npa\"",
        "/root/",
        "/tmp/",
    ] {
        assert!(
            !source.contains(forbidden),
            "generated artifact leaked boundary field or host path: {forbidden}"
        );
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

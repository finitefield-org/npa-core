use npa_cert::Name;
use npa_package::{
    build_package_registry_modules, parse_and_validate_manifest_str, parse_package_hash,
    parse_registry_module_json, PackageArtifactError, PackageArtifactErrorKind,
    PackageArtifactErrorReason, PackageArtifactOrigin, PackageCheckerMode, PackageCheckerSummary,
    PackageHash, PackageId, PackageLockEntry, PackageLockEntryOrigin, PackageLockImport,
    PackageLockManifest, PackageLockManifestReference, PackagePath, PackageRegistryCheckerStatus,
    PackageRegistryModuleSeedInput, PackageVersion, PACKAGE_LOCK_SCHEMA,
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

fn hash(value: &str) -> PackageHash {
    parse_package_hash(value, "test").unwrap()
}

fn name(value: &str) -> Name {
    Name::from_dotted(value)
}

fn manifest_source() -> String {
    format!(
        r#"schema = "npa.package.v0.1"
package = "npa-proof-corpus"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

[[imports]]
module = "Std.Logic.Eq"
package = "npa-std"
version = "0.1.0"
certificate = "vendor/std/Std/Logic/Eq/certificate.npcert"
export_hash = "{A_HASH}"
certificate_hash = "{B_HASH}"

[[modules]]
module = "Proofs.A"
source = "Proofs/A.npa"
certificate = "Proofs/A/certificate.npcert"
imports = ["Proofs.B", "Std.Logic.Eq"]
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ONE_HASH}"
expected_export_hash = "{TWO_HASH}"
expected_axiom_report_hash = "{THREE_HASH}"
expected_certificate_hash = "{FOUR_HASH}"
definitions = []
theorems = []
axioms = []

[[modules]]
module = "Proofs.B"
source = "Proofs/B.npa"
certificate = "Proofs/B/certificate.npcert"
imports = []
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{FIVE_HASH}"
expected_export_hash = "{SIX_HASH}"
expected_axiom_report_hash = "{SEVEN_HASH}"
expected_certificate_hash = "{EIGHT_HASH}"
definitions = []
theorems = []
axioms = []
"#
    )
}

fn lock_manifest(entries: Vec<PackageLockEntry>) -> PackageLockManifest {
    PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: PackageId::new("npa-proof-corpus"),
        version: PackageVersion::new("0.1.0"),
        manifest: PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: hash(ZERO_HASH),
        },
        entries,
    }
}

fn local_lock_entry(
    module: &str,
    certificate: &str,
    certificate_file_hash: &str,
    export_hash: &str,
    axiom_report_hash: &str,
    certificate_hash: &str,
    imports: Vec<PackageLockImport>,
) -> PackageLockEntry {
    PackageLockEntry {
        module: name(module),
        origin: PackageLockEntryOrigin::Local,
        certificate: PackagePath::new(certificate),
        certificate_file_hash: hash(certificate_file_hash),
        export_hash: hash(export_hash),
        axiom_report_hash: hash(axiom_report_hash),
        certificate_hash: hash(certificate_hash),
        imports,
        package: None,
        version: None,
    }
}

fn external_lock_entry(
    module: &str,
    certificate: &str,
    certificate_file_hash: &str,
    export_hash: &str,
    axiom_report_hash: &str,
    certificate_hash: &str,
) -> PackageLockEntry {
    PackageLockEntry {
        module: name(module),
        origin: PackageLockEntryOrigin::External,
        certificate: PackagePath::new(certificate),
        certificate_file_hash: hash(certificate_file_hash),
        export_hash: hash(export_hash),
        axiom_report_hash: hash(axiom_report_hash),
        certificate_hash: hash(certificate_hash),
        imports: Vec::new(),
        package: Some(PackageId::new("npa-std")),
        version: Some(PackageVersion::new("0.1.0")),
    }
}

fn import(module: &str, export_hash: &str, certificate_hash: &str) -> PackageLockImport {
    PackageLockImport {
        module: name(module),
        export_hash: hash(export_hash),
        certificate_hash: hash(certificate_hash),
    }
}

fn package_lock() -> PackageLockManifest {
    lock_manifest(vec![
        external_lock_entry(
            "Std.Logic.Eq",
            "vendor/std/Std/Logic/Eq/certificate.npcert",
            C_HASH,
            A_HASH,
            NINE_HASH,
            B_HASH,
        ),
        local_lock_entry(
            "Proofs.B",
            "Proofs/B/certificate.npcert",
            FIVE_HASH,
            SIX_HASH,
            SEVEN_HASH,
            EIGHT_HASH,
            Vec::new(),
        ),
        local_lock_entry(
            "Proofs.A",
            "Proofs/A/certificate.npcert",
            ONE_HASH,
            TWO_HASH,
            THREE_HASH,
            FOUR_HASH,
            vec![
                import("Proofs.B", SIX_HASH, EIGHT_HASH),
                import("Std.Logic.Eq", A_HASH, B_HASH),
            ],
        ),
    ])
}

fn checker_summary(
    module: &str,
    mode: PackageCheckerMode,
    status: &str,
    export_hash: &str,
    axiom_report_hash: &str,
    certificate_hash: &str,
) -> PackageCheckerSummary {
    PackageCheckerSummary {
        module: name(module),
        checker: match mode {
            PackageCheckerMode::Fast => "fast-kernel-certificate-verifier",
            PackageCheckerMode::Reference => "npa-checker-ref",
        }
        .to_owned(),
        profile: match mode {
            PackageCheckerMode::Fast => "fast-kernel",
            PackageCheckerMode::Reference => "npa.checker.reference.v0.1",
        }
        .to_owned(),
        mode,
        status: status.to_owned(),
        export_hash: hash(export_hash),
        certificate_hash: hash(certificate_hash),
        axiom_report_hash: hash(axiom_report_hash),
    }
}

fn checker_summaries() -> Vec<PackageCheckerSummary> {
    vec![
        checker_summary(
            "Proofs.A",
            PackageCheckerMode::Fast,
            "passed",
            TWO_HASH,
            THREE_HASH,
            FOUR_HASH,
        ),
        checker_summary(
            "Proofs.A",
            PackageCheckerMode::Reference,
            "passed",
            TWO_HASH,
            THREE_HASH,
            FOUR_HASH,
        ),
        checker_summary(
            "Proofs.B",
            PackageCheckerMode::Reference,
            "passed",
            SIX_HASH,
            SEVEN_HASH,
            EIGHT_HASH,
        ),
        checker_summary(
            "Std.Logic.Eq",
            PackageCheckerMode::Reference,
            "passed",
            A_HASH,
            NINE_HASH,
            B_HASH,
        ),
    ]
}

fn seed_input<'a>(
    manifest: &'a npa_package::PackageManifest,
    package_lock: &'a PackageLockManifest,
    checker_summaries: &'a [PackageCheckerSummary],
) -> PackageRegistryModuleSeedInput<'a> {
    PackageRegistryModuleSeedInput {
        manifest,
        package_lock,
        checker_summaries,
        artifact_hashes: npa_package::PackageRegistryArtifactHashes {
            package_lock_file_hash: hash(ONE_HASH),
            axiom_report_file_hash: hash(TWO_HASH),
            theorem_index_file_hash: hash(THREE_HASH),
        },
    }
}

fn assert_artifact_error(
    error: PackageArtifactError,
    kind: PackageArtifactErrorKind,
    reason: PackageArtifactErrorReason,
    field: Option<&str>,
) {
    assert_eq!(error.kind, kind);
    assert_eq!(error.reason_code, reason);
    assert_eq!(error.field.as_deref(), field);
}

#[test]
fn registry_module_builds_local_entries_with_import_identities_and_artifact_hashes() {
    let validated = parse_and_validate_manifest_str(&manifest_source()).unwrap();
    let lock = package_lock();
    let summaries = checker_summaries();

    let entries =
        build_package_registry_modules(seed_input(validated.manifest(), &lock, &summaries))
            .unwrap();

    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].module.as_dotted(), "Proofs.A");
    assert_eq!(entries[1].module.as_dotted(), "Proofs.B");
    assert!(entries
        .iter()
        .all(|entry| entry.module.as_dotted() != "Std.Logic.Eq"));

    let proofs_a = &entries[0];
    assert_eq!(proofs_a.imports.len(), 2);
    assert_eq!(proofs_a.imports[0].module.as_dotted(), "Proofs.B");
    assert_eq!(proofs_a.imports[0].origin, PackageArtifactOrigin::Local);
    assert!(proofs_a.imports[0].package.is_none());
    assert!(proofs_a.imports[0].version.is_none());
    assert_eq!(proofs_a.imports[0].export_hash, hash(SIX_HASH));
    assert_eq!(proofs_a.imports[0].certificate_hash, hash(EIGHT_HASH));
    assert_eq!(proofs_a.imports[1].module.as_dotted(), "Std.Logic.Eq");
    assert_eq!(proofs_a.imports[1].origin, PackageArtifactOrigin::External);
    assert_eq!(
        proofs_a.imports[1].package.as_ref().unwrap().as_str(),
        "npa-std"
    );
    assert_eq!(
        proofs_a.imports[1].version.as_ref().unwrap().as_str(),
        "0.1.0"
    );
    assert_eq!(proofs_a.imports[1].export_hash, hash(A_HASH));
    assert_eq!(proofs_a.imports[1].certificate_hash, hash(B_HASH));

    assert_eq!(proofs_a.checker_results.len(), 2);
    assert_eq!(proofs_a.checker_results[0].mode, "fast");
    assert_eq!(
        proofs_a.checker_results[0].status,
        PackageRegistryCheckerStatus::Accepted
    );
    assert_eq!(proofs_a.checker_results[1].mode, "reference");
    assert_eq!(proofs_a.checker_results[1].checker, "npa-checker-ref");
    assert_eq!(
        proofs_a.checker_results[1].status,
        PackageRegistryCheckerStatus::Accepted
    );
    assert_eq!(
        proofs_a.artifact_hashes.package_lock_file_hash,
        hash(ONE_HASH)
    );
    assert_eq!(
        proofs_a.artifact_hashes.axiom_report_file_hash,
        hash(TWO_HASH)
    );
    assert_eq!(
        proofs_a.artifact_hashes.theorem_index_file_hash,
        hash(THREE_HASH)
    );

    let canonical = proofs_a.canonical_json().unwrap();
    let parsed = parse_registry_module_json(&canonical).unwrap();
    assert_eq!(parsed, *proofs_a);
}

#[test]
fn registry_module_rejects_missing_stale_or_rejected_required_checker_result() {
    let validated = parse_and_validate_manifest_str(&manifest_source()).unwrap();
    let lock = package_lock();
    let mut summaries = checker_summaries();

    let mut missing_lock_entry = package_lock();
    missing_lock_entry
        .entries
        .retain(|entry| entry.module.as_dotted() != "Proofs.B");
    assert_artifact_error(
        build_package_registry_modules(seed_input(
            validated.manifest(),
            &missing_lock_entry,
            &summaries,
        ))
        .unwrap_err(),
        PackageArtifactErrorKind::ArtifactSchema,
        PackageArtifactErrorReason::MissingField,
        Some("Proofs.B"),
    );

    summaries.retain(|summary| {
        !(summary.module.as_dotted() == "Proofs.A" && summary.mode == PackageCheckerMode::Reference)
    });
    assert_artifact_error(
        build_package_registry_modules(seed_input(validated.manifest(), &lock, &summaries))
            .unwrap_err(),
        PackageArtifactErrorKind::ArtifactSchema,
        PackageArtifactErrorReason::MissingField,
        Some("reference"),
    );

    let mut summaries = checker_summaries();
    summaries
        .iter_mut()
        .find(|summary| {
            summary.module.as_dotted() == "Proofs.A"
                && summary.mode == PackageCheckerMode::Reference
        })
        .unwrap()
        .export_hash = hash(NINE_HASH);
    assert_artifact_error(
        build_package_registry_modules(seed_input(validated.manifest(), &lock, &summaries))
            .unwrap_err(),
        PackageArtifactErrorKind::Domain,
        PackageArtifactErrorReason::InvalidEnumValue,
        Some("export_hash"),
    );

    let mut summaries = checker_summaries();
    summaries
        .iter_mut()
        .find(|summary| {
            summary.module.as_dotted() == "Proofs.A"
                && summary.mode == PackageCheckerMode::Reference
        })
        .unwrap()
        .profile = "npa.checker.reference.wrong".to_owned();
    assert_artifact_error(
        build_package_registry_modules(seed_input(validated.manifest(), &lock, &summaries))
            .unwrap_err(),
        PackageArtifactErrorKind::Domain,
        PackageArtifactErrorReason::InvalidEnumValue,
        Some("profile"),
    );

    let mut summaries = checker_summaries();
    summaries
        .iter_mut()
        .find(|summary| {
            summary.module.as_dotted() == "Proofs.A"
                && summary.mode == PackageCheckerMode::Reference
        })
        .unwrap()
        .status = "failed".to_owned();
    assert_artifact_error(
        build_package_registry_modules(seed_input(validated.manifest(), &lock, &summaries))
            .unwrap_err(),
        PackageArtifactErrorKind::Domain,
        PackageArtifactErrorReason::InvalidEnumValue,
        Some("status"),
    );
}

#[test]
fn registry_module_import_identity_rejects_module_name_only_match() {
    let validated = parse_and_validate_manifest_str(&manifest_source()).unwrap();
    let mut lock = package_lock();
    lock.entries
        .iter_mut()
        .find(|entry| entry.module.as_dotted() == "Proofs.A")
        .unwrap()
        .imports[1]
        .certificate_hash = hash(NINE_HASH);

    assert_artifact_error(
        build_package_registry_modules(seed_input(
            validated.manifest(),
            &lock,
            &checker_summaries(),
        ))
        .unwrap_err(),
        PackageArtifactErrorKind::Domain,
        PackageArtifactErrorReason::InvalidEnumValue,
        Some("certificate_hash"),
    );
}

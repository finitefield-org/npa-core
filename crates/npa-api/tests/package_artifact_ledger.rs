use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

use npa_api::{
    observe_package_artifacts_with_reference_checker, verify_package_reference_source_free,
    PackageArtifactLedgerCheckerStatus, PackageCertificateArtifact, PackageVerificationErrorReason,
};
use npa_cert::Name;
use npa_package::{
    build_package_lock_from_artifacts_allowing_local_hash_updates, parse_and_validate_manifest_str,
    parse_package_hash, PackageId, PackageLockArtifact, PackageLockErrorReason, PackagePath,
    PackageVersion,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package/proofs")
}

#[test]
fn package_artifact_ledger_observer_checks_selected_closure_without_cache() {
    let root = fixture_root();
    let manifest_bytes = fs::read(root.join("npa-package.toml")).expect("read manifest");
    let manifest_source = std::str::from_utf8(&manifest_bytes).expect("manifest is UTF-8");
    let validated = parse_and_validate_manifest_str(manifest_source).expect("validate manifest");

    let paths = validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.certificate.clone())
        .chain(
            validated
                .manifest()
                .imports
                .iter()
                .flatten()
                .map(|import| import.certificate.clone()),
        )
        .collect::<Vec<_>>();
    let buffers = paths
        .iter()
        .map(|path| fs::read(root.join(path.as_str())).expect("read certificate"))
        .collect::<Vec<_>>();
    let artifacts = || {
        paths
            .iter()
            .zip(&buffers)
            .map(|(path, bytes)| PackageLockArtifact {
                path: path.clone(),
                bytes,
            })
    };
    let observed_lock = build_package_lock_from_artifacts_allowing_local_hash_updates(
        &validated,
        PackagePath::new("npa-package.toml"),
        &manifest_bytes,
        artifacts(),
    )
    .expect("build observed lock");
    let selected = BTreeSet::from([Name::from_dotted("Proofs.Ai.Eq")]);

    let report = observe_package_artifacts_with_reference_checker(
        &validated,
        &observed_lock,
        artifacts(),
        &selected,
    )
    .expect("observe selected closure");

    assert!(report
        .modules
        .iter()
        .all(|module| module.status == PackageArtifactLedgerCheckerStatus::Checked));
    assert_eq!(
        report
            .modules
            .iter()
            .filter(|module| module.selected_for_ledger)
            .map(|module| module.module.clone())
            .collect::<Vec<_>>(),
        [Name::from_dotted("Proofs.Ai.Eq")]
    );
    assert!(report.modules.iter().all(|module| {
        module.export_hash.is_some()
            && module.axiom_report_hash.is_some()
            && module.certificate_hash.is_some()
    }));
}

#[test]
fn package_artifact_ledger_observer_returns_typed_error_for_missing_closure_buffers() {
    let root = fixture_root();
    let manifest_bytes = fs::read(root.join("npa-package.toml")).expect("read manifest");
    let manifest_source = std::str::from_utf8(&manifest_bytes).expect("manifest is UTF-8");
    let validated = parse_and_validate_manifest_str(manifest_source).expect("validate manifest");
    let paths_and_buffers = validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.certificate.clone())
        .chain(
            validated
                .manifest()
                .imports
                .iter()
                .flatten()
                .map(|import| import.certificate.clone()),
        )
        .map(|path| {
            let bytes = fs::read(root.join(path.as_str())).expect("read certificate");
            (path, bytes)
        })
        .collect::<Vec<_>>();
    let artifacts = || {
        paths_and_buffers
            .iter()
            .map(|(path, bytes)| PackageLockArtifact {
                path: path.clone(),
                bytes,
            })
    };
    let observed_lock = build_package_lock_from_artifacts_allowing_local_hash_updates(
        &validated,
        PackagePath::new("npa-package.toml"),
        &manifest_bytes,
        artifacts(),
    )
    .expect("build observed lock");
    let selected_module = Name::from_dotted("Proofs.Ai.Eq");
    let selected_certificate = validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == selected_module)
        .expect("selected module exists")
        .certificate
        .clone();
    let support_certificate = validated
        .manifest()
        .imports
        .iter()
        .flatten()
        .find(|import| import.module == Name::from_dotted("Std.Logic.Eq"))
        .expect("selected module support import exists")
        .certificate
        .clone();

    for missing_certificate in [selected_certificate, support_certificate] {
        let incomplete_artifacts = paths_and_buffers
            .iter()
            .filter(|(path, _)| path != &missing_certificate)
            .map(|(path, bytes)| PackageLockArtifact {
                path: path.clone(),
                bytes,
            });

        let error = observe_package_artifacts_with_reference_checker(
            &validated,
            &observed_lock,
            incomplete_artifacts,
            &BTreeSet::from([selected_module.clone()]),
        )
        .expect_err("missing closure buffer must return a typed error");

        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::CertificateArtifactMissing
        );
        assert_eq!(
            error.expected_value.as_deref(),
            Some(missing_certificate.as_str())
        );
    }
}

#[test]
fn package_artifact_ledger_observer_allows_local_pin_drift_but_not_external_drift() {
    let root = fixture_root();
    let original = fs::read_to_string(root.join("npa-package.toml")).expect("read manifest");
    let paths_and_buffers = {
        let validated = parse_and_validate_manifest_str(&original).expect("validate manifest");
        validated
            .manifest()
            .modules
            .iter()
            .map(|module| module.certificate.clone())
            .chain(
                validated
                    .manifest()
                    .imports
                    .iter()
                    .flatten()
                    .map(|import| import.certificate.clone()),
            )
            .map(|path| {
                let bytes = fs::read(root.join(path.as_str())).expect("read certificate");
                (path, bytes)
            })
            .collect::<Vec<_>>()
    };
    let artifacts = || {
        paths_and_buffers
            .iter()
            .map(|(path, bytes)| PackageLockArtifact {
                path: path.clone(),
                bytes,
            })
    };

    let local_marker = "expected_export_hash = \"";
    let module_start = original.find("module = \"Proofs.Ai.Basic\"").unwrap();
    let hash_start =
        original[module_start..].find(local_marker).unwrap() + module_start + local_marker.len();
    let hash_end = original[hash_start..].find('"').unwrap() + hash_start;
    let mut local_drift = original.clone();
    local_drift.replace_range(hash_start..hash_end, ZERO_HASH);
    let validated = parse_and_validate_manifest_str(&local_drift).expect("validate local drift");
    let observed_lock = build_package_lock_from_artifacts_allowing_local_hash_updates(
        &validated,
        PackagePath::new("npa-package.toml"),
        local_drift.as_bytes(),
        artifacts(),
    )
    .expect("local manifest pin drift is observational");
    let selected = BTreeSet::from([Name::from_dotted("Proofs.Ai.Basic")]);
    let report = observe_package_artifacts_with_reference_checker(
        &validated,
        &observed_lock,
        artifacts(),
        &selected,
    )
    .expect("observe through local pin drift");
    assert_eq!(
        report.modules.last().map(|module| module.status),
        Some(PackageArtifactLedgerCheckerStatus::Checked)
    );
    let strict_error = verify_package_reference_source_free(
        &validated,
        &observed_lock,
        paths_and_buffers
            .iter()
            .map(|(path, bytes)| PackageCertificateArtifact {
                path: path.clone(),
                bytes,
            }),
    )
    .expect_err("ordinary verification must retain local manifest hash pins");
    assert_eq!(
        strict_error.reason_code,
        PackageVerificationErrorReason::LockGraphInvalid
    );

    enum IdentityDrift {
        LocalCertificate,
        ExternalPackage,
        ExternalVersion,
        ExternalCertificate,
    }
    let external = Name::from_dotted("Std.Logic.Eq");
    for drift in [
        IdentityDrift::LocalCertificate,
        IdentityDrift::ExternalPackage,
        IdentityDrift::ExternalVersion,
        IdentityDrift::ExternalCertificate,
    ] {
        let mut tampered_lock = observed_lock.clone();
        let entry = match drift {
            IdentityDrift::LocalCertificate => tampered_lock
                .entries
                .iter_mut()
                .find(|entry| entry.module == Name::from_dotted("Proofs.Ai.Basic"))
                .unwrap(),
            _ => tampered_lock
                .entries
                .iter_mut()
                .find(|entry| entry.module == external)
                .unwrap(),
        };
        match drift {
            IdentityDrift::LocalCertificate => {
                entry.certificate = PackagePath::new("moved/local-certificate.npcert");
            }
            IdentityDrift::ExternalPackage => {
                entry.package = Some(PackageId::new("different-package"));
            }
            IdentityDrift::ExternalVersion => {
                entry.version = Some(PackageVersion::new("9.9.9"));
            }
            IdentityDrift::ExternalCertificate => {
                entry.certificate = PackagePath::new("moved/external-certificate.npcert");
            }
        }

        let error = observe_package_artifacts_with_reference_checker(
            &validated,
            &tampered_lock,
            artifacts(),
            &selected,
        )
        .expect_err("observer must reject manifest/lock identity drift");
        assert_eq!(
            error.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
    }

    let mut tampered_lock = observed_lock.clone();
    let zero = parse_package_hash(ZERO_HASH, "test").unwrap();
    tampered_lock
        .entries
        .iter_mut()
        .filter(|entry| entry.module == external)
        .for_each(|entry| entry.export_hash = zero);
    tampered_lock
        .entries
        .iter_mut()
        .flat_map(|entry| &mut entry.imports)
        .filter(|import| import.module == external)
        .for_each(|import| import.export_hash = zero);
    let error = observe_package_artifacts_with_reference_checker(
        &validated,
        &tampered_lock,
        artifacts(),
        &selected,
    )
    .expect_err("observer must reject a coherent lock with drifted external pins");
    assert_eq!(
        error.reason_code,
        PackageVerificationErrorReason::LockGraphInvalid
    );

    let external_marker = "export_hash = \"";
    let import_start = original.find("[[imports]]").unwrap();
    let hash_start = original[import_start..].find(external_marker).unwrap()
        + import_start
        + external_marker.len();
    let hash_end = original[hash_start..].find('"').unwrap() + hash_start;
    let mut external_drift = original;
    external_drift.replace_range(hash_start..hash_end, ZERO_HASH);
    let validated =
        parse_and_validate_manifest_str(&external_drift).expect("validate external drift");
    let error = build_package_lock_from_artifacts_allowing_local_hash_updates(
        &validated,
        PackagePath::new("npa-package.toml"),
        external_drift.as_bytes(),
        artifacts(),
    )
    .expect_err("external manifest pin drift must remain strict");
    assert_eq!(
        error.reason_code,
        PackageLockErrorReason::ExportHashMismatch
    );
}

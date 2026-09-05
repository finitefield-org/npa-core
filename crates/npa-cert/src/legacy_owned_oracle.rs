//! Test-only semantic oracle for the pre-shared owned representations.
//!
//! This module deliberately reconstructs the audited owned certificate,
//! verified-module, and session algorithms field by field. It must remain
//! private and `cfg(test)`-only until the two-release-cycle removal condition
//! in the VMSP rollout plan has been satisfied.

use std::collections::BTreeMap;

use npa_kernel::{Decl, Expr, Level, Reducibility};

use super::{
    AxiomPolicy, AxiomReport, CertError, CoreModule, DeclCert, ExportBlock, Hash, ImportEntry,
    ImportKey, LevelNode, ModuleCert, ModuleCertParts, Name, StructuralClosureSummary, TermNode,
    TrustMode, VerifiedModule, VerifierSession,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LegacyOwnedModuleCertOracle {
    parts: ModuleCertParts,
}

impl LegacyOwnedModuleCertOracle {
    pub(super) fn from_certificate(certificate: &ModuleCert) -> Self {
        Self {
            parts: ModuleCertParts {
                header: certificate.header().clone(),
                imports: certificate.imports().to_vec(),
                name_table: certificate.name_table().to_vec(),
                level_table: certificate.level_table().to_vec(),
                term_table: certificate.term_table().to_vec(),
                declarations: certificate.declarations().to_vec(),
                export_block: certificate.export_block().to_vec(),
                axiom_report: certificate.axiom_report().clone(),
                hashes: certificate.hashes().clone(),
            },
        }
    }

    fn matches_certificate(&self, certificate: &ModuleCert) -> bool {
        self.parts.header == *certificate.header()
            && self.parts.imports == certificate.imports()
            && self.parts.name_table == certificate.name_table()
            && self.parts.level_table == certificate.level_table()
            && self.parts.term_table == certificate.term_table()
            && self.parts.declarations == certificate.declarations()
            && self.parts.export_block == certificate.export_block()
            && self.parts.axiom_report == *certificate.axiom_report()
            && self.parts.hashes == *certificate.hashes()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LegacyOwnedVerifiedModuleOracle {
    certificate_format: String,
    core_spec: String,
    module: Name,
    imports: Vec<ImportEntry>,
    name_table: Vec<Name>,
    level_table: Vec<LevelNode>,
    term_table: Vec<TermNode>,
    declarations: Vec<DeclCert>,
    export_hash: Hash,
    certificate_hash: Hash,
    export_block: ExportBlock,
    axiom_report: AxiomReport,
    structural_closure: StructuralClosureSummary,
}

impl LegacyOwnedVerifiedModuleOracle {
    pub(super) fn from_verified(module: &VerifiedModule) -> Self {
        Self {
            certificate_format: module.certificate_format().to_owned(),
            core_spec: module.core_spec().to_owned(),
            module: module.module().clone(),
            imports: module.imports().to_vec(),
            name_table: module.name_table().to_vec(),
            level_table: module.level_table().to_vec(),
            term_table: module.term_table().to_vec(),
            declarations: module.declarations().to_vec(),
            export_hash: module.export_hash(),
            certificate_hash: module.certificate_hash(),
            export_block: module.export_block().to_vec(),
            axiom_report: module.axiom_report().clone(),
            structural_closure: module.structural_closure().clone(),
        }
    }

    fn matches_verified(&self, module: &VerifiedModule) -> bool {
        self.certificate_format == module.certificate_format()
            && self.core_spec == module.core_spec()
            && self.module == *module.module()
            && self.imports == module.imports()
            && self.name_table == module.name_table()
            && self.level_table == module.level_table()
            && self.term_table == module.term_table()
            && self.declarations == module.declarations()
            && self.export_hash == module.export_hash()
            && self.certificate_hash == module.certificate_hash()
            && self.export_block == module.export_block()
            && self.axiom_report == *module.axiom_report()
            && self.structural_closure == *module.structural_closure()
    }
}

#[derive(Clone, Debug)]
struct LegacyOwnedSessionEntryOracle {
    module: LegacyOwnedVerifiedModuleOracle,
    mode: TrustMode,
}

#[derive(Clone, Debug, Default)]
pub(super) struct LegacyOwnedSessionOracle {
    checked: BTreeMap<ImportKey, LegacyOwnedSessionEntryOracle>,
}

impl LegacyOwnedSessionOracle {
    pub(super) fn register_verified_module_with_trust(
        &mut self,
        module: LegacyOwnedVerifiedModuleOracle,
        mode: TrustMode,
    ) {
        let key = ImportKey {
            module: module.module.clone(),
            export_hash: module.export_hash,
            certificate_hash: Some(module.certificate_hash),
        };
        let entry = LegacyOwnedSessionEntryOracle { module, mode };
        match self.checked.get_mut(&key) {
            Some(existing) if existing.mode == TrustMode::HighTrust => {
                if mode == TrustMode::HighTrust {
                    *existing = entry;
                }
            }
            Some(existing) => *existing = entry,
            None => {
                self.checked.insert(key, entry);
            }
        }
    }

    pub(super) fn find_import(
        &self,
        entry: &ImportEntry,
        mode: TrustMode,
    ) -> Result<&LegacyOwnedVerifiedModuleOracle, CertError> {
        let module_export_matches = self.checked.values().any(|checked| {
            checked.module.module == entry.module && checked.module.export_hash == entry.export_hash
        });
        let high_trust_module_export_matches = self.checked.values().any(|checked| {
            checked.mode == TrustMode::HighTrust
                && checked.module.module == entry.module
                && checked.module.export_hash == entry.export_hash
        });

        let found = self.checked.values().find(|checked| {
            (mode == TrustMode::Normal || checked.mode == TrustMode::HighTrust)
                && checked.module.module == entry.module
                && checked.module.export_hash == entry.export_hash
                && match (mode, entry.certificate_hash) {
                    (TrustMode::Normal, None) => true,
                    (_, Some(hash)) => checked.module.certificate_hash == hash,
                    (TrustMode::HighTrust, None) => false,
                }
        });

        if let Some(checked) = found {
            return Ok(&checked.module);
        }

        if mode == TrustMode::HighTrust && !high_trust_module_export_matches {
            return Err(CertError::ImportNotVerifiedInSession {
                module: entry.module.clone(),
            });
        }

        if entry.certificate_hash.is_some() && module_export_matches {
            return Err(CertError::ImportCertificateHashMismatch {
                module: entry.module.clone(),
            });
        }

        Err(CertError::ImportHashMismatch {
            module: entry.module.clone(),
        })
    }

    fn mode_for(&self, module: &LegacyOwnedVerifiedModuleOracle) -> Option<TrustMode> {
        self.checked
            .values()
            .find(|entry| {
                entry.module.module == module.module
                    && entry.module.export_hash == module.export_hash
                    && entry.module.certificate_hash == module.certificate_hash
            })
            .map(|entry| entry.mode)
    }
}

fn identity_module() -> CoreModule {
    let identity_type = Expr::pi(
        "A",
        Expr::sort(Level::param("u")),
        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
    );
    let identity_value = Expr::lam(
        "A",
        Expr::sort(Level::param("u")),
        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
    );
    CoreModule {
        name: Name::from_dotted("Test.LegacyOwnedOracle"),
        declarations: vec![Decl::Def {
            name: "id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: identity_type,
            value: identity_value,
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn assert_lookup_matches(
    oracle: &LegacyOwnedSessionOracle,
    shared: &VerifierSession,
    import: &ImportEntry,
    mode: TrustMode,
) {
    match (
        oracle.find_import(import, mode),
        shared.find_import(import, mode),
    ) {
        (Ok(legacy), Ok(current)) => assert!(legacy.matches_verified(current)),
        (Err(legacy), Err(current)) => assert_eq!(legacy, current),
        (legacy, current) => panic!("legacy/shared lookup mismatch: {legacy:?} != {current:?}"),
    }
}

#[test]
fn legacy_owned_deep_copy_oracle_matches_shared_value_hash_and_trust() {
    let certificate = super::build_module_cert(identity_module(), &[]).unwrap();
    let bytes = super::encode_module_cert(&certificate).unwrap();
    let decoded = super::decode_module_cert(&bytes).unwrap();
    let module_oracle = LegacyOwnedModuleCertOracle::from_certificate(&decoded);

    assert!(module_oracle.matches_certificate(&certificate));
    assert_eq!(
        module_oracle.parts.hashes.export_hash,
        certificate.hashes().export_hash
    );
    assert_eq!(
        module_oracle.parts.hashes.axiom_report_hash,
        certificate.hashes().axiom_report_hash
    );
    assert_eq!(
        module_oracle.parts.hashes.certificate_hash,
        certificate.hashes().certificate_hash
    );
    assert_eq!(super::encode_module_cert(&decoded).unwrap(), bytes);

    let verified =
        super::verify_module_cert_with_import_refs(&bytes, &[], &AxiomPolicy::normal()).unwrap();
    let verified_oracle = LegacyOwnedVerifiedModuleOracle::from_verified(&verified);
    assert!(verified_oracle.matches_verified(&verified));

    let exact_import = ImportEntry {
        module: verified.module().clone(),
        export_hash: verified.export_hash(),
        certificate_hash: Some(verified.certificate_hash()),
    };
    let normal_import = ImportEntry {
        certificate_hash: None,
        ..exact_import.clone()
    };
    let wrong_certificate_import = ImportEntry {
        certificate_hash: Some([0x51; 32]),
        ..exact_import.clone()
    };
    let wrong_export_import = ImportEntry {
        export_hash: [0x52; 32],
        ..exact_import.clone()
    };

    let mut legacy_session = LegacyOwnedSessionOracle::default();
    let mut shared_session = VerifierSession::new();
    legacy_session.register_verified_module_with_trust(verified_oracle.clone(), TrustMode::Normal);
    shared_session.register_verified_module_with_trust(verified.clone(), TrustMode::Normal);

    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &normal_import,
        TrustMode::Normal,
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &exact_import,
        TrustMode::HighTrust,
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &wrong_certificate_import,
        TrustMode::Normal,
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &wrong_export_import,
        TrustMode::Normal,
    );

    legacy_session
        .register_verified_module_with_trust(verified_oracle.clone(), TrustMode::HighTrust);
    shared_session.register_verified_module_with_trust(verified.clone(), TrustMode::HighTrust);
    assert_eq!(
        legacy_session.mode_for(&verified_oracle),
        Some(TrustMode::HighTrust)
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &exact_import,
        TrustMode::HighTrust,
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &wrong_certificate_import,
        TrustMode::HighTrust,
    );

    legacy_session.register_verified_module_with_trust(verified_oracle.clone(), TrustMode::Normal);
    shared_session.register_verified_module_with_trust(verified.clone(), TrustMode::Normal);
    assert_eq!(
        legacy_session.mode_for(&verified_oracle),
        Some(TrustMode::HighTrust)
    );
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &exact_import,
        TrustMode::HighTrust,
    );

    legacy_session.register_verified_module_with_trust(verified_oracle, TrustMode::HighTrust);
    shared_session.register_verified_module_with_trust(verified, TrustMode::HighTrust);
    assert_lookup_matches(
        &legacy_session,
        &shared_session,
        &exact_import,
        TrustMode::HighTrust,
    );
}

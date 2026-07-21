use std::collections::{BTreeMap, BTreeSet};

use crate::*;

/// Manifest-qualified identity of the certificate that is eligible for import rebinding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleCertRebindExpectedIdentity {
    /// Expected module name.
    pub module: Name,
    /// Expected public export hash.
    pub export_hash: Hash,
    /// Expected axiom-report hash.
    pub axiom_report_hash: Hash,
    /// Expected full certificate hash before rebinding.
    pub certificate_hash: Hash,
}

/// Package origin of an exact verified import supplied to certificate rebinding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleCertRebindImportOrigin {
    /// A module owned by the package being refreshed. Its certificate hash may be rebound.
    Local,
    /// An external package module. Its complete encoded identity must remain unchanged.
    External,
}

/// One exact verified import available to certificate rebinding.
#[derive(Clone, Copy, Debug)]
pub struct ModuleCertRebindImport<'a> {
    /// Live-verified module that must resolve the matching certificate import.
    pub verified: &'a VerifiedModule,
    /// Whether the import is local and therefore eligible for certificate-hash rebinding.
    pub origin: ModuleCertRebindImportOrigin,
}

/// Successful classification produced by import-certificate-hash rebinding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleCertImportRebindOutcome {
    /// The certificate format is valid but not enabled for structural rebinding.
    IneligibleFormat {
        /// Certificate format string.
        format: String,
        /// Core specification string.
        core_spec: String,
    },
    /// A local import changed its public export and requires a source rebuild.
    ExportChanged {
        /// Local imported module whose export changed.
        module: Name,
        /// Export hash encoded by the previous certificate.
        expected: Hash,
        /// Export hash of the newly verified local module.
        actual: Hash,
    },
    /// Every strict import identity already matched and the old bytes live-verified unchanged.
    Unchanged {
        /// Qualified canonical certificate decoded from the old bytes.
        certificate: ModuleCert,
        /// Module live-verified against the supplied exact imports.
        verified: VerifiedModule,
    },
    /// Local strict certificate pins were updated and the new bytes live-verified.
    Rebound {
        /// Rebound canonical certificate.
        certificate: ModuleCert,
        /// Canonically encoded rebound certificate bytes.
        bytes: Vec<u8>,
        /// Module live-verified against the supplied exact imports.
        verified: VerifiedModule,
        /// Local import modules whose certificate hashes changed, in certificate-table order.
        changed_imports: Vec<Name>,
    },
}

/// Structural or verification failure while qualifying or executing certificate rebinding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleCertImportRebindError {
    /// Canonical decode, stored-hash validation, or live verification failed.
    Certificate(CertError),
    /// The decoded certificate module did not match the qualified manifest identity.
    ModuleMismatch {
        /// Expected module.
        expected: Name,
        /// Decoded module.
        actual: Name,
    },
    /// A qualified manifest hash did not match the decoded certificate.
    IdentityHashMismatch {
        /// Hash role that mismatched.
        object: HashObject,
        /// Qualified manifest hash.
        expected: Hash,
        /// Decoded certificate hash.
        actual: Hash,
    },
    /// More than one supplied exact import used the same module name.
    DuplicateMappedImport {
        /// Duplicated mapped module.
        module: Name,
    },
    /// The canonical certificate contained more than one import for the same module.
    DuplicateCertificateImport {
        /// Duplicated certificate import module.
        module: Name,
    },
    /// No exact verified import was supplied for a certificate import.
    MissingMappedImport {
        /// Unresolved certificate import module.
        module: Name,
    },
    /// A package certificate import omitted its mandatory strict certificate hash.
    MissingStrictCertificateHash {
        /// Import missing the strict pin.
        module: Name,
    },
    /// An external import's exact identity differed from the encoded identity.
    ExternalIdentityChanged {
        /// External module whose identity differed.
        module: Name,
    },
    /// Re-encoding changed certificate structure outside the permitted mask.
    StructuralAuditMismatch,
    /// Live verification returned a module or stable hash different from the qualified baseline.
    VerifiedIdentityMismatch,
}

impl From<CertError> for ModuleCertImportRebindError {
    fn from(value: CertError) -> Self {
        Self::Certificate(value)
    }
}

/// Rebind strict certificate hashes for export-stable local imports of one canonical certificate.
///
/// The operation accepts only current-format canonical bytes with manifest-qualified module,
/// export, axiom-report, and old certificate hashes. Every certificate import must have one exact
/// live-verified mapping. External identities are immutable; local export changes are returned as
/// a source-rebuild outcome. Rebound bytes are structurally audited and live source-free verified
/// before they are returned.
pub fn rebind_module_cert_import_certificate_hashes(
    previous_bytes: &[u8],
    expected: &ModuleCertRebindExpectedIdentity,
    imports: &[ModuleCertRebindImport<'_>],
    policy: &AxiomPolicy,
) -> std::result::Result<ModuleCertImportRebindOutcome, ModuleCertImportRebindError> {
    let previous = verify_module_cert_hashes(previous_bytes)?;
    if certificate_format_version(&previous.header)? != CertificateFormatVersion::Current {
        return Ok(ModuleCertImportRebindOutcome::IneligibleFormat {
            format: previous.header.format,
            core_spec: previous.header.core_spec,
        });
    }
    qualify_expected_identity(&previous, expected)?;

    let mut certificate_import_modules = BTreeSet::new();
    for import in &previous.imports {
        if !certificate_import_modules.insert(import.module.clone()) {
            return Err(ModuleCertImportRebindError::DuplicateCertificateImport {
                module: import.module.clone(),
            });
        }
        if import.certificate_hash.is_none() {
            return Err(ModuleCertImportRebindError::MissingStrictCertificateHash {
                module: import.module.clone(),
            });
        }
    }

    let mut imports_by_module = BTreeMap::new();
    for import in imports {
        let module = import.verified.module().clone();
        if imports_by_module.insert(module.clone(), *import).is_some() {
            return Err(ModuleCertImportRebindError::DuplicateMappedImport { module });
        }
    }

    let mut local_export_change = None;
    for import in &previous.imports {
        let encoded_certificate_hash = import
            .certificate_hash
            .expect("strict import pin was checked before rebinding");
        let Some(mapped) = imports_by_module.get(&import.module) else {
            return Err(ModuleCertImportRebindError::MissingMappedImport {
                module: import.module.clone(),
            });
        };
        match mapped.origin {
            ModuleCertRebindImportOrigin::External => {
                if mapped.verified.export_hash() != import.export_hash
                    || mapped.verified.certificate_hash() != encoded_certificate_hash
                {
                    return Err(ModuleCertImportRebindError::ExternalIdentityChanged {
                        module: import.module.clone(),
                    });
                }
            }
            ModuleCertRebindImportOrigin::Local => {
                if mapped.verified.export_hash() != import.export_hash {
                    local_export_change.get_or_insert_with(|| {
                        (
                            import.module.clone(),
                            import.export_hash,
                            mapped.verified.export_hash(),
                        )
                    });
                }
            }
        }
    }
    if let Some((module, expected, actual)) = local_export_change {
        return Ok(ModuleCertImportRebindOutcome::ExportChanged {
            module,
            expected,
            actual,
        });
    }

    let mut rebound = previous.clone();
    let mut changed_imports = Vec::new();
    for import in &mut rebound.imports {
        let encoded_certificate_hash = import
            .certificate_hash
            .expect("strict import pin was checked before rebinding");
        let mapped = imports_by_module
            .get(&import.module)
            .expect("complete import mapping was checked before rebinding");
        if mapped.origin == ModuleCertRebindImportOrigin::Local {
            let current_certificate_hash = mapped.verified.certificate_hash();
            if current_certificate_hash != encoded_certificate_hash {
                import.certificate_hash = Some(current_certificate_hash);
                changed_imports.push(import.module.clone());
            }
        }
    }

    let exact_imports = imports
        .iter()
        .map(|import| import.verified)
        .collect::<Vec<_>>();
    if changed_imports.is_empty() {
        let verified = verify_module_cert_with_import_refs(previous_bytes, &exact_imports, policy)?;
        qualify_verified_identity(&verified, expected)?;
        return Ok(ModuleCertImportRebindOutcome::Unchanged {
            certificate: previous,
            verified,
        });
    }

    rebound.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&rebound),
    );
    if !matches_rebind_structural_mask(&previous, &rebound, &changed_imports) {
        return Err(ModuleCertImportRebindError::StructuralAuditMismatch);
    }
    let rebound_bytes = encode_module_cert(&rebound)?;
    let decoded = decode_module_cert(&rebound_bytes)?;
    if decoded != rebound || !matches_rebind_structural_mask(&previous, &decoded, &changed_imports)
    {
        return Err(ModuleCertImportRebindError::StructuralAuditMismatch);
    }
    let verified = verify_module_cert_with_import_refs(&rebound_bytes, &exact_imports, policy)?;
    qualify_verified_identity(&verified, expected)?;
    Ok(ModuleCertImportRebindOutcome::Rebound {
        certificate: rebound,
        bytes: rebound_bytes,
        verified,
        changed_imports,
    })
}

fn matches_rebind_structural_mask(
    previous: &ModuleCert,
    rebound: &ModuleCert,
    changed_imports: &[Name],
) -> bool {
    if previous.imports.len() != rebound.imports.len() {
        return false;
    }
    let changed_imports = changed_imports.iter().collect::<BTreeSet<_>>();
    let mut masked = rebound.clone();
    masked.hashes.certificate_hash = previous.hashes.certificate_hash;
    for (old_import, new_import) in previous.imports.iter().zip(&mut masked.imports) {
        if changed_imports.contains(&new_import.module) {
            new_import.certificate_hash = old_import.certificate_hash;
        }
    }
    masked == *previous
}

fn qualify_expected_identity(
    certificate: &ModuleCert,
    expected: &ModuleCertRebindExpectedIdentity,
) -> std::result::Result<(), ModuleCertImportRebindError> {
    if certificate.header.module != expected.module {
        return Err(ModuleCertImportRebindError::ModuleMismatch {
            expected: expected.module.clone(),
            actual: certificate.header.module.clone(),
        });
    }
    for (object, expected_hash, actual_hash) in [
        (
            HashObject::ExportBlock,
            expected.export_hash,
            certificate.hashes.export_hash,
        ),
        (
            HashObject::AxiomReport,
            expected.axiom_report_hash,
            certificate.hashes.axiom_report_hash,
        ),
        (
            HashObject::ModuleCertificate,
            expected.certificate_hash,
            certificate.hashes.certificate_hash,
        ),
    ] {
        if expected_hash != actual_hash {
            return Err(ModuleCertImportRebindError::IdentityHashMismatch {
                object,
                expected: expected_hash,
                actual: actual_hash,
            });
        }
    }
    Ok(())
}

fn qualify_verified_identity(
    verified: &VerifiedModule,
    expected: &ModuleCertRebindExpectedIdentity,
) -> std::result::Result<(), ModuleCertImportRebindError> {
    let verified_axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(verified.axiom_report()),
    );
    if verified.module() != &expected.module
        || verified.export_hash() != expected.export_hash
        || verified_axiom_report_hash != expected.axiom_report_hash
    {
        return Err(ModuleCertImportRebindError::VerifiedIdentityMismatch);
    }
    Ok(())
}

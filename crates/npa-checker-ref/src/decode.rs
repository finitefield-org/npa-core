use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use sha2::{Digest, Sha256};

use crate::{
    reference_name_component_is_canonical, ReferenceAxiomDependency,
    ReferenceCertificateFormatVersion, ReferenceCertificateHeader, ReferenceCertificateSection,
    ReferenceCheckError, ReferenceCheckErrorKind, ReferenceCheckReason, ReferenceCheckedModule,
    ReferenceCheckerPolicy, ReferenceCoreExpr, ReferenceCoreFeature, ReferenceCoreGlobalRef,
    ReferenceCoreLevel, ReferenceDecodedCertificate, ReferenceDecodedCertificateCounts,
    ReferenceExportKind, ReferenceHash, ReferenceHashObject, ReferenceImportEntry,
    ReferenceImportEnvironment, ReferenceImportStore, ReferenceModuleHashes, ReferenceModuleName,
    ReferencePublicEnvironment, ReferencePublicExport, ReferenceResolvedImport, ReferenceTrustMode,
    REFERENCE_CERTIFICATE_FORMAT, REFERENCE_CORE_SPEC, REFERENCE_LEGACY_CERTIFICATE_FORMAT,
    REFERENCE_LEGACY_CORE_SPEC, REFERENCE_LEGACY_MODULE_CERT_DOMAIN,
    REFERENCE_LEGACY_MODULE_EXPORT_DOMAIN, REFERENCE_MODULE_CERT_DOMAIN,
    REFERENCE_MODULE_EXPORT_DOMAIN, REFERENCE_PREVIOUS_CERTIFICATE_FORMAT,
    REFERENCE_PREVIOUS_CORE_SPEC, REFERENCE_PREVIOUS_MODULE_CERT_DOMAIN,
    REFERENCE_PREVIOUS_MODULE_EXPORT_DOMAIN,
};

type DecodeResult<T> = Result<T, ReferenceCheckError>;
const HUMAN_UNIVERSE_META_PREFIX: &str = "__npa_internal_human_universe_meta#";
const PUBLIC_SELF_IMPORT_INDEX: usize = usize::MAX;
const MODULE_HASH_TRAILER_LEN: usize = 32 * 3;
const CORE_FEATURE_REPORT_TAG: &str = "core_features";
#[allow(dead_code)]
pub(crate) const MAX_UNIVERSE_CONTEXT_NODES: usize = 65;
#[allow(dead_code)]
pub(crate) const MAX_UNIVERSE_ATOM_INEQUALITIES: usize = 1024;

fn reference_certificate_format_version(
    header: &ReferenceCertificateHeader,
) -> Option<ReferenceCertificateFormatVersion> {
    if header.format == REFERENCE_CERTIFICATE_FORMAT && header.core_spec == REFERENCE_CORE_SPEC {
        Some(ReferenceCertificateFormatVersion::Current)
    } else if header.format == REFERENCE_PREVIOUS_CERTIFICATE_FORMAT
        && header.core_spec == REFERENCE_PREVIOUS_CORE_SPEC
    {
        Some(ReferenceCertificateFormatVersion::Previous)
    } else if header.format == REFERENCE_LEGACY_CERTIFICATE_FORMAT
        && header.core_spec == REFERENCE_LEGACY_CORE_SPEC
    {
        Some(ReferenceCertificateFormatVersion::Legacy)
    } else {
        None
    }
}

pub(crate) fn decode_certificate_impl(bytes: &[u8]) -> DecodeResult<ReferenceDecodedCertificate> {
    decode_module_certificate(bytes).map(DecodedModuleCertificate::summary)
}

pub(crate) fn verify_certificate_hashes_impl(
    bytes: &[u8],
) -> DecodeResult<ReferenceDecodedCertificate> {
    let cert = decode_module_certificate(bytes)?;
    cert.verify_hashes(bytes)?;
    Ok(cert.summary())
}

pub(crate) fn import_entry_from_source_free_certificate_impl(
    bytes: &[u8],
) -> DecodeResult<ReferenceImportEntry> {
    let cert = decode_module_certificate(bytes)?;
    cert.verify_hashes(bytes)?;
    cert.import_entry(false)
}

pub(crate) fn build_import_environment_impl(
    bytes: &[u8],
    import_store: &ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
) -> DecodeResult<ReferenceImportEnvironment> {
    let cert = decode_module_certificate(bytes)?;
    cert.verify_hashes(bytes)?;
    cert.enforce_core_feature_policy(policy)?;
    cert.build_import_environment(import_store, policy)
}

pub(crate) fn check_certificate_impl(
    bytes: &[u8],
    import_store: &ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
) -> DecodeResult<ReferenceCheckedModule> {
    let cert = decode_module_certificate(bytes)?;
    cert.verify_hashes(bytes)?;
    cert.enforce_core_feature_policy(policy)?;
    let imports = cert.build_import_environment(import_store, policy)?;
    cert.verify_axiom_report(&imports, policy)?;
    cert.type_check(&imports)
}

fn decode_module_certificate(bytes: &[u8]) -> DecodeResult<DecodedModuleCertificate> {
    if bytes.is_empty() {
        return Err(ReferenceCheckError::empty());
    }

    let mut decoder = Decoder::new(bytes);
    let cert = decoder.module_certificate()?;
    if !decoder.is_done() {
        return Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::FullCertificate,
            decoder.offset(),
            ReferenceCheckReason::TrailingBytes,
        ));
    }
    cert.validate()?;
    Ok(cert)
}

#[derive(Clone, Debug)]
struct Located<T> {
    value: T,
    offset: usize,
}

#[derive(Clone, Debug)]
struct DecodedModuleCertificate {
    header: ReferenceCertificateHeader,
    imports: Vec<Located<ImportEntry>>,
    name_table: Vec<Located<ReferenceModuleName>>,
    level_table: Vec<Located<LevelNode>>,
    term_table: Vec<Located<TermNode>>,
    declarations: Vec<Located<DeclCert>>,
    export_block: Vec<Located<ExportEntry>>,
    axiom_report: AxiomReport,
    hashes: ReferenceModuleHashes,
    hash_offsets: ModuleHashOffsets,
}

impl DecodedModuleCertificate {
    fn validate(&self) -> DecodeResult<()> {
        self.validate_import_order()?;
        self.validate_name_table_order()?;
        let level_hashes = self.validate_level_table()?;
        self.validate_term_table(&level_hashes)?;
        let mut used = UsedTables::new();
        self.collect_name_roots(&mut used)?;
        self.collect_decl_roots(&mut used)?;
        self.collect_export_roots(&mut used)?;
        self.collect_axiom_report_roots(&mut used)?;
        self.collect_reachable_terms(&mut used)?;
        self.collect_reachable_levels(&mut used)?;
        self.validate_decl_universe_contexts()?;
        self.validate_declaration_order()?;
        self.validate_vector_orders()?;
        self.validate_used_names(&used.names)?;
        self.validate_used_levels(&used.levels)?;
        self.validate_used_terms(&used.terms)?;
        Ok(())
    }

    fn summary(self) -> ReferenceDecodedCertificate {
        ReferenceDecodedCertificate::new(
            self.header,
            ReferenceDecodedCertificateCounts {
                imports_len: self.imports.len(),
                name_table_len: self.name_table.len(),
                level_table_len: self.level_table.len(),
                term_table_len: self.term_table.len(),
                declarations_len: self.declarations.len(),
                export_block_len: self.export_block.len(),
            },
            self.hashes,
        )
    }

    fn import_entry(
        &self,
        checked_by_reference_checker: bool,
    ) -> DecodeResult<ReferenceImportEntry> {
        Ok(ReferenceImportEntry::new(
            self.header.module.clone(),
            self.hashes.export_hash,
            self.hashes.axiom_report_hash,
            self.hashes.certificate_hash,
            Arc::new(self.public_environment()?),
            checked_by_reference_checker,
        ))
    }

    fn checked_module(&self) -> DecodeResult<ReferenceCheckedModule> {
        Ok(ReferenceCheckedModule::new(
            self.header.module.clone(),
            self.hashes.export_hash,
            self.hashes.axiom_report_hash,
            self.hashes.certificate_hash,
            Arc::new(self.public_environment()?),
        ))
    }

    fn public_environment(&self) -> DecodeResult<ReferencePublicEnvironment> {
        let core_levels = self.core_levels()?;
        let core_terms = self.core_terms(&core_levels)?;
        let imports = self
            .imports
            .iter()
            .map(|import| (import.value.module.clone(), import.value.export_hash))
            .collect();
        let exports = self
            .export_block
            .iter()
            .map(|entry| {
                let entry = &entry.value;
                Ok(ReferencePublicExport {
                    name: self.name_table[entry.name].value.clone(),
                    kind: match entry.kind {
                        ExportKind::Axiom => ReferenceExportKind::Axiom,
                        ExportKind::Def => ReferenceExportKind::Def,
                        ExportKind::Theorem => ReferenceExportKind::Theorem,
                        ExportKind::Inductive => ReferenceExportKind::Inductive,
                        ExportKind::Constructor => ReferenceExportKind::Constructor,
                        ExportKind::Recursor => ReferenceExportKind::Recursor,
                    },
                    decl_interface_hash: entry.decl_interface_hash,
                    axiom_dependencies: self.public_axiom_dependencies(&entry.axiom_dependencies),
                    universe_params: self.name_ids_to_names(&entry.universe_params),
                    universe_constraints: self
                        .public_universe_constraints(&core_levels, &entry.universe_constraints)?,
                    ty: self.public_expr(&core_terms[entry.ty])?,
                    body: entry
                        .body
                        .map(|body| self.public_expr(&core_terms[body]))
                        .transpose()?,
                })
            })
            .collect::<DecodeResult<Vec<_>>>()?;
        Ok(ReferencePublicEnvironment::new(
            imports,
            exports,
            self.public_axiom_dependencies(&self.axiom_report.module_axioms),
            self.axiom_report.core_features.clone(),
        ))
    }

    fn public_universe_constraints(
        &self,
        core_levels: &[ReferenceCoreLevel],
        constraints: &[UniverseConstraintSpec],
    ) -> DecodeResult<Vec<ReferenceUniverseConstraint>> {
        constraints
            .iter()
            .map(|constraint| {
                Ok(ReferenceUniverseConstraint {
                    lhs: core_levels.get(constraint.lhs).cloned().ok_or_else(|| {
                        ReferenceCheckError::malformed(
                            ReferenceCertificateSection::ExportBlock,
                            0,
                            ReferenceCheckReason::DanglingReference,
                        )
                    })?,
                    relation: constraint.relation,
                    rhs: core_levels.get(constraint.rhs).cloned().ok_or_else(|| {
                        ReferenceCheckError::malformed(
                            ReferenceCertificateSection::ExportBlock,
                            0,
                            ReferenceCheckReason::DanglingReference,
                        )
                    })?,
                })
            })
            .collect()
    }

    fn public_expr(&self, expr: &ReferenceCoreExpr) -> DecodeResult<ReferenceCoreExpr> {
        Ok(match expr {
            ReferenceCoreExpr::Sort(level) => ReferenceCoreExpr::Sort(level.clone()),
            ReferenceCoreExpr::BVar(index) => ReferenceCoreExpr::BVar(*index),
            ReferenceCoreExpr::Const { global_ref, levels } => ReferenceCoreExpr::Const {
                global_ref: self.public_global_ref(global_ref)?,
                levels: levels.clone(),
            },
            ReferenceCoreExpr::App(fun, arg) => ReferenceCoreExpr::App(
                Arc::new(self.public_expr(fun)?),
                Arc::new(self.public_expr(arg)?),
            ),
            ReferenceCoreExpr::Lam { ty, body } => ReferenceCoreExpr::Lam {
                ty: Arc::new(self.public_expr(ty)?),
                body: Arc::new(self.public_expr(body)?),
            },
            ReferenceCoreExpr::Pi { ty, body } => ReferenceCoreExpr::Pi {
                ty: Arc::new(self.public_expr(ty)?),
                body: Arc::new(self.public_expr(body)?),
            },
            ReferenceCoreExpr::Let { ty, value, body } => ReferenceCoreExpr::Let {
                ty: Arc::new(self.public_expr(ty)?),
                value: Arc::new(self.public_expr(value)?),
                body: Arc::new(self.public_expr(body)?),
            },
        })
    }

    fn public_global_ref(
        &self,
        global_ref: &ReferenceCoreGlobalRef,
    ) -> DecodeResult<ReferenceCoreGlobalRef> {
        Ok(match global_ref {
            ReferenceCoreGlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => ReferenceCoreGlobalRef::Builtin {
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            ReferenceCoreGlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => ReferenceCoreGlobalRef::Imported {
                import_index: *import_index,
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            ReferenceCoreGlobalRef::Local { decl_index } => {
                let (name, decl_interface_hash) = self.local_public_ref(*decl_index)?;
                ReferenceCoreGlobalRef::Imported {
                    import_index: PUBLIC_SELF_IMPORT_INDEX,
                    name,
                    decl_interface_hash,
                }
            }
            ReferenceCoreGlobalRef::LocalGenerated { decl_index, name } => {
                let declaration = self.declarations.get(*decl_index).ok_or_else(|| {
                    ReferenceCheckError::malformed(
                        ReferenceCertificateSection::Declarations,
                        0,
                        ReferenceCheckReason::DanglingReference,
                    )
                })?;
                ReferenceCoreGlobalRef::Imported {
                    import_index: PUBLIC_SELF_IMPORT_INDEX,
                    name: name.clone(),
                    decl_interface_hash: declaration.value.hashes.decl_interface_hash,
                }
            }
        })
    }

    fn local_public_ref(
        &self,
        decl_index: usize,
    ) -> DecodeResult<(ReferenceModuleName, ReferenceHash)> {
        let declaration = self.declarations.get(decl_index).ok_or_else(|| {
            ReferenceCheckError::malformed(
                ReferenceCertificateSection::Declarations,
                0,
                ReferenceCheckReason::DanglingReference,
            )
        })?;
        let name = match &declaration.value.decl {
            DeclPayload::Axiom { name, .. }
            | DeclPayload::AxiomConstrained { name, .. }
            | DeclPayload::Def { name, .. }
            | DeclPayload::DefConstrained { name, .. }
            | DeclPayload::Theorem { name, .. }
            | DeclPayload::TheoremConstrained { name, .. }
            | DeclPayload::Inductive { name, .. }
            | DeclPayload::InductiveConstrained { name, .. }
            | DeclPayload::MutualInductiveBlock { name, .. } => {
                self.name_table[*name].value.clone()
            }
        };
        Ok((name, declaration.value.hashes.decl_interface_hash))
    }

    fn public_axiom_dependencies(&self, axioms: &[AxiomRef]) -> Vec<ReferenceAxiomDependency> {
        axioms
            .iter()
            .map(|axiom| ReferenceAxiomDependency {
                name: self.name_table[axiom.name].value.clone(),
                decl_interface_hash: axiom.decl_interface_hash,
            })
            .collect()
    }

    fn name_ids_to_names(&self, names: &[usize]) -> Vec<ReferenceModuleName> {
        names
            .iter()
            .map(|name| self.name_table[*name].value.clone())
            .collect()
    }

    fn build_import_environment(
        &self,
        import_store: &ReferenceImportStore,
        policy: &ReferenceCheckerPolicy,
    ) -> DecodeResult<ReferenceImportEnvironment> {
        let mut resolved = Vec::with_capacity(self.imports.len());
        for requested in &self.imports {
            let entry = resolve_import(requested, import_store, policy)?;
            resolved.push(ReferenceResolvedImport {
                module: entry.module().clone(),
                export_hash: *entry.export_hash(),
                certificate_hash: *entry.certificate_hash(),
                public_environment: Arc::clone(&entry.public_environment),
            });
        }
        Ok(ReferenceImportEnvironment::new(resolved))
    }

    fn enforce_core_feature_policy(&self, policy: &ReferenceCheckerPolicy) -> DecodeResult<()> {
        enforce_core_feature_policy(
            &self.axiom_report.core_features,
            self.axiom_report.core_features_offset,
            policy,
        )
    }

    fn type_check(
        &self,
        imports: &ReferenceImportEnvironment,
    ) -> DecodeResult<ReferenceCheckedModule> {
        TypeChecker::new(self, imports)?.check_declarations()?;
        self.checked_module()
    }

    fn verify_axiom_report(
        &self,
        imports: &ReferenceImportEnvironment,
        policy: &ReferenceCheckerPolicy,
    ) -> DecodeResult<()> {
        let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::with_capacity(self.declarations.len());
        let mut transitive_by_decl: Vec<Vec<AxiomRef>> =
            Vec::with_capacity(self.declarations.len());

        if self.axiom_report.per_declaration.len() != self.declarations.len() {
            return Err(ReferenceCheckError::axiom_report(
                ReferenceCertificateSection::AxiomReport,
                self.axiom_report.module_axioms_offset,
            ));
        }

        for (decl_index, declaration) in self.declarations.iter().enumerate() {
            let expected_dependencies = self.expected_dependencies_for_decl(
                imports,
                decl_index,
                &declaration.value.decl,
                declaration.offset,
            )?;
            if expected_dependencies != declaration.value.dependencies {
                return Err(ReferenceCheckError::axiom_report(
                    ReferenceCertificateSection::Declarations,
                    declaration.offset,
                ));
            }

            let (direct_axioms, transitive_axioms) = self.expected_axioms_for_decl(
                imports,
                decl_index,
                &declaration.value.decl,
                &expected_dependencies,
                &previous_axioms,
                declaration.offset,
            )?;
            if transitive_axioms != declaration.value.axiom_dependencies {
                return Err(ReferenceCheckError::axiom_report(
                    ReferenceCertificateSection::Declarations,
                    declaration.offset,
                ));
            }

            let actual = &self.axiom_report.per_declaration[decl_index];
            if actual.decl_index != decl_index
                || actual.direct_axioms != direct_axioms
                || actual.transitive_axioms != transitive_axioms
            {
                return Err(ReferenceCheckError::axiom_report(
                    ReferenceCertificateSection::AxiomReport,
                    actual.offset,
                ));
            }

            previous_axioms.push(transitive_axioms.clone());
            transitive_by_decl.push(transitive_axioms);
        }

        let expected_module_axioms = union_axioms(
            transitive_by_decl
                .iter()
                .flat_map(|axioms| axioms.iter().cloned()),
        );
        if expected_module_axioms != self.axiom_report.module_axioms {
            return Err(ReferenceCheckError::axiom_report(
                ReferenceCertificateSection::AxiomReport,
                self.axiom_report.module_axioms_offset,
            ));
        }
        let expected_features = self.expected_core_features()?;
        if expected_features != self.axiom_report.core_features {
            return Err(ReferenceCheckError::axiom_report(
                ReferenceCertificateSection::AxiomReport,
                self.axiom_report.core_features_offset,
            ));
        }

        self.enforce_axiom_policy(imports, policy, &expected_module_axioms)
    }

    fn verify_hashes(&self, bytes: &[u8]) -> DecodeResult<()> {
        let level_hashes = self.compute_level_hashes()?;
        let term_hashes = self.compute_term_hashes(&level_hashes)?;
        for declaration in &self.declarations {
            let expected = compute_decl_hashes(
                &declaration.value.decl,
                &declaration.value.dependencies,
                &declaration.value.axiom_dependencies,
                &self.term_table,
                &level_hashes,
                &term_hashes,
                &self.name_table,
            )?;
            if expected.decl_interface_hash != declaration.value.hashes.decl_interface_hash {
                return Err(ReferenceCheckError::hash_mismatch(
                    ReferenceCertificateSection::Declarations,
                    declaration.value.hashes.decl_interface_hash_offset,
                    ReferenceHashObject::DeclInterface,
                ));
            }
            if expected.decl_certificate_hash != declaration.value.hashes.decl_certificate_hash {
                return Err(ReferenceCheckError::hash_mismatch(
                    ReferenceCertificateSection::Declarations,
                    declaration.value.hashes.decl_certificate_hash_offset,
                    ReferenceHashObject::DeclCertificate,
                ));
            }
        }

        let expected_export_block = self.build_export_block(&term_hashes)?;
        let actual_export_block = self
            .export_block
            .iter()
            .map(|entry| entry.value.clone())
            .collect::<Vec<_>>();
        let version = reference_certificate_format_version(&self.header).ok_or_else(|| {
            ReferenceCheckError::malformed(
                ReferenceCertificateSection::HeaderFormat,
                0,
                ReferenceCheckReason::FormatMismatch,
            )
        })?;
        self.verify_export_format_compatibility(&expected_export_block, version)?;
        let (export_domain, export_bytes, cert_domain) = match version {
            ReferenceCertificateFormatVersion::Current => (
                REFERENCE_MODULE_EXPORT_DOMAIN,
                encode_export_block(&expected_export_block),
                REFERENCE_MODULE_CERT_DOMAIN,
            ),
            ReferenceCertificateFormatVersion::Previous => (
                REFERENCE_PREVIOUS_MODULE_EXPORT_DOMAIN,
                encode_export_block_previous(&expected_export_block),
                REFERENCE_PREVIOUS_MODULE_CERT_DOMAIN,
            ),
            ReferenceCertificateFormatVersion::Legacy => (
                REFERENCE_LEGACY_MODULE_EXPORT_DOMAIN,
                encode_export_block_legacy(&expected_export_block),
                REFERENCE_LEGACY_MODULE_CERT_DOMAIN,
            ),
        };
        let expected_export_hash = hash_with_domain(export_domain, &export_bytes);
        if expected_export_block != actual_export_block
            || expected_export_hash != self.hashes.export_hash
        {
            return Err(ReferenceCheckError::hash_mismatch(
                ReferenceCertificateSection::Hashes,
                self.hash_offsets.export_hash_offset,
                ReferenceHashObject::ExportBlock,
            ));
        }

        let expected_axiom_report_hash = hash_with_domain(
            b"NPA-AXIOM-REPORT-0.1",
            &encode_axiom_report(&self.axiom_report),
        );
        if expected_axiom_report_hash != self.hashes.axiom_report_hash {
            return Err(ReferenceCheckError::hash_mismatch(
                ReferenceCertificateSection::Hashes,
                self.hash_offsets.axiom_report_hash_offset,
                ReferenceHashObject::AxiomReport,
            ));
        }

        let hash_input = bytes
            .get(..self.hash_offsets.certificate_hash_offset)
            .ok_or_else(|| {
                ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Hashes,
                    self.hash_offsets.certificate_hash_offset,
                    ReferenceCheckReason::UnexpectedEof,
                )
            })?;
        let expected_certificate_hash = hash_with_domain(cert_domain, hash_input);
        if expected_certificate_hash != self.hashes.certificate_hash {
            return Err(ReferenceCheckError::hash_mismatch(
                ReferenceCertificateSection::Hashes,
                self.hash_offsets.certificate_hash_offset,
                ReferenceHashObject::ModuleCertificate,
            ));
        }

        Ok(())
    }

    fn verify_export_format_compatibility(
        &self,
        expected_export_block: &[ExportEntry],
        version: ReferenceCertificateFormatVersion,
    ) -> DecodeResult<()> {
        if version == ReferenceCertificateFormatVersion::Legacy
            && expected_export_block
                .iter()
                .any(|entry| !entry.universe_constraints.is_empty())
        {
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::ExportBlock,
                0,
                ReferenceCheckReason::ConstrainedExportRequiresFormatUpgrade,
            ));
        }
        Ok(())
    }

    fn expected_dependencies_for_decl(
        &self,
        imports: &ReferenceImportEnvironment,
        decl_index: usize,
        decl: &DeclPayload,
        offset: usize,
    ) -> DecodeResult<Vec<DependencyEntry>> {
        let mut refs = BTreeSet::new();
        for term in decl_term_ids(decl) {
            collect_global_refs_from_term(&self.term_table, term, &mut refs)?;
        }

        let allow_self_reference = matches!(
            decl,
            DeclPayload::Inductive { .. }
                | DeclPayload::InductiveConstrained { .. }
                | DeclPayload::MutualInductiveBlock { .. }
        );
        refs.into_iter()
            .filter(|global_ref| {
                !matches!(
                    global_ref,
                    GlobalRef::Local {
                        decl_index: referenced_decl_index,
                    } | GlobalRef::LocalGenerated {
                        decl_index: referenced_decl_index,
                        ..
                    } if allow_self_reference && *referenced_decl_index == decl_index
                )
            })
            .map(|global_ref| {
                let decl_interface_hash =
                    self.interface_hash_for_global_ref(imports, decl_index, &global_ref, offset)?;
                Ok(DependencyEntry {
                    global_ref,
                    decl_interface_hash,
                })
            })
            .collect()
    }

    fn expected_core_features(&self) -> DecodeResult<Vec<ReferenceCoreFeature>> {
        for term in &self.term_table {
            let TermNode::Const {
                global_ref:
                    GlobalRef::Builtin {
                        name,
                        decl_interface_hash,
                    },
                ..
            } = &term.value
            else {
                continue;
            };
            let name_value = &self.name_table[*name].value;
            if builtin_decl_interface_hash(name_value) != Some(*decl_interface_hash) {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::TermTable,
                    term.offset,
                    ReferenceCheckReason::UnknownReference,
                ));
            }
        }
        Ok(Vec::new())
    }

    fn expected_axioms_for_decl(
        &self,
        imports: &ReferenceImportEnvironment,
        decl_index: usize,
        decl: &DeclPayload,
        dependencies: &[DependencyEntry],
        previous_axioms: &[Vec<AxiomRef>],
        offset: usize,
    ) -> DecodeResult<(Vec<AxiomRef>, Vec<AxiomRef>)> {
        let mut direct = BTreeSet::new();
        let mut transitive = BTreeSet::new();

        for dependency in dependencies {
            match &dependency.global_ref {
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => {
                    let name_value = &self.name_table[*name].value;
                    if builtin_is_axiom(name_value) {
                        let axiom = AxiomRef {
                            global_ref: dependency.global_ref.clone(),
                            name: *name,
                            decl_interface_hash: *decl_interface_hash,
                        };
                        direct.insert(axiom.clone());
                        transitive.insert(axiom);
                    }
                }
                GlobalRef::Local {
                    decl_index: dependency_index,
                } => {
                    let dep_axioms = previous_axioms.get(*dependency_index).ok_or_else(|| {
                        ReferenceCheckError::axiom_report(
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )
                    })?;
                    if let Some(axiom) = local_axiom_ref_for_decl(*dependency_index, dep_axioms) {
                        direct.insert(axiom);
                    }
                    transitive.extend(dep_axioms.iter().cloned());
                }
                GlobalRef::LocalGenerated {
                    decl_index: dependency_index,
                    ..
                } => {
                    let dep_axioms = previous_axioms.get(*dependency_index).ok_or_else(|| {
                        ReferenceCheckError::axiom_report(
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )
                    })?;
                    transitive.extend(dep_axioms.iter().cloned());
                }
                GlobalRef::Imported {
                    name,
                    decl_interface_hash,
                    ..
                } => {
                    let export = self.imported_export_for_global_ref(
                        imports,
                        &dependency.global_ref,
                        offset,
                    )?;
                    if export.kind == ReferenceExportKind::Axiom {
                        direct.insert(AxiomRef {
                            global_ref: dependency.global_ref.clone(),
                            name: *name,
                            decl_interface_hash: *decl_interface_hash,
                        });
                    }
                    for axiom in &export.axiom_dependencies {
                        transitive
                            .insert(self.remap_imported_axiom_dependency(imports, axiom, offset)?);
                    }
                }
            }
        }

        if let DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } = decl {
            let self_ref = AxiomRef {
                global_ref: GlobalRef::Local { decl_index },
                name: *name,
                decl_interface_hash: self.declarations[decl_index]
                    .value
                    .hashes
                    .decl_interface_hash,
            };
            direct.insert(self_ref.clone());
            transitive.insert(self_ref);
        }

        Ok((
            direct.into_iter().collect(),
            transitive.into_iter().collect(),
        ))
    }

    fn interface_hash_for_global_ref(
        &self,
        imports: &ReferenceImportEnvironment,
        current_decl_index: usize,
        global_ref: &GlobalRef,
        offset: usize,
    ) -> DecodeResult<ReferenceHash> {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                let name_value = &self.name_table[*name].value;
                if builtin_decl_interface_hash(name_value) == Some(*decl_interface_hash) {
                    Ok(*decl_interface_hash)
                } else {
                    Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UnknownReference,
                    ))
                }
            }
            GlobalRef::Imported {
                decl_interface_hash,
                ..
            } => {
                self.imported_export_for_global_ref(imports, global_ref, offset)?;
                Ok(*decl_interface_hash)
            }
            GlobalRef::Local { decl_index } => {
                if *decl_index >= current_decl_index {
                    return Err(ReferenceCheckError::axiom_report(
                        ReferenceCertificateSection::Declarations,
                        offset,
                    ));
                }
                Ok(self.declarations[*decl_index]
                    .value
                    .hashes
                    .decl_interface_hash)
            }
            GlobalRef::LocalGenerated { decl_index, name } => {
                if *decl_index >= current_decl_index
                    || !self.local_generated_entry_exists(*decl_index, *name)?
                {
                    return Err(ReferenceCheckError::axiom_report(
                        ReferenceCertificateSection::Declarations,
                        offset,
                    ));
                }
                Ok(self.declarations[*decl_index]
                    .value
                    .hashes
                    .decl_interface_hash)
            }
        }
    }

    fn imported_export_for_global_ref(
        &self,
        imports: &ReferenceImportEnvironment,
        global_ref: &GlobalRef,
        offset: usize,
    ) -> DecodeResult<ReferencePublicExport> {
        let GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } = global_ref
        else {
            return Err(ReferenceCheckError::axiom_report(
                ReferenceCertificateSection::Declarations,
                offset,
            ));
        };
        let import = imports.imports().get(*import_index).ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::UnknownReference,
            )
        })?;
        let name_value = &self.name_table[*name].value;
        import
            .public_environment
            .exports()
            .iter()
            .find(|export| {
                export.name == *name_value && export.decl_interface_hash == *decl_interface_hash
            })
            .cloned()
            .ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnknownReference,
                )
            })
    }

    fn remap_imported_axiom_dependency(
        &self,
        imports: &ReferenceImportEnvironment,
        axiom: &ReferenceAxiomDependency,
        offset: usize,
    ) -> DecodeResult<AxiomRef> {
        let name = self.name_id_for_value(&axiom.name, offset)?;
        if let Some(import_index) =
            import_index_exporting_axiom(imports, &axiom.name, axiom.decl_interface_hash)
        {
            return Ok(AxiomRef {
                global_ref: GlobalRef::Imported {
                    import_index,
                    name,
                    decl_interface_hash: axiom.decl_interface_hash,
                },
                name,
                decl_interface_hash: axiom.decl_interface_hash,
            });
        }
        if builtin_is_axiom(&axiom.name)
            && builtin_decl_interface_hash(&axiom.name) == Some(axiom.decl_interface_hash)
        {
            return Ok(AxiomRef {
                global_ref: GlobalRef::Builtin {
                    name,
                    decl_interface_hash: axiom.decl_interface_hash,
                },
                name,
                decl_interface_hash: axiom.decl_interface_hash,
            });
        }
        Err(ReferenceCheckError::axiom_report(
            ReferenceCertificateSection::AxiomReport,
            offset,
        ))
    }

    fn name_id_for_value(&self, name: &ReferenceModuleName, offset: usize) -> DecodeResult<usize> {
        self.name_table
            .iter()
            .position(|candidate| candidate.value == *name)
            .ok_or_else(|| {
                ReferenceCheckError::axiom_report(ReferenceCertificateSection::AxiomReport, offset)
            })
    }

    fn local_generated_entry_exists(&self, decl_index: usize, name: usize) -> DecodeResult<bool> {
        let declaration = self.declarations.get(decl_index).ok_or_else(|| {
            ReferenceCheckError::axiom_report(ReferenceCertificateSection::Declarations, 0)
        })?;
        Ok(match &declaration.value.decl {
            DeclPayload::Inductive {
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                constructors,
                recursor,
                ..
            } => {
                constructors
                    .iter()
                    .any(|constructor| constructor.name == name)
                    || recursor
                        .as_ref()
                        .is_some_and(|recursor| recursor.name == name)
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                inductives.iter().any(|inductive| {
                    inductive.name == name
                        || inductive
                            .constructors
                            .iter()
                            .any(|constructor| constructor.name == name)
                        || inductive
                            .recursor
                            .as_ref()
                            .is_some_and(|recursor| recursor.name == name)
                })
            }
            _ => false,
        })
    }

    fn enforce_axiom_policy(
        &self,
        imports: &ReferenceImportEnvironment,
        policy: &ReferenceCheckerPolicy,
        module_axioms: &[AxiomRef],
    ) -> DecodeResult<()> {
        for (import_index, import) in imports.imports().iter().enumerate() {
            let offset = self
                .imports
                .get(import_index)
                .map_or(0, |located| located.offset);
            for axiom in import.public_environment.module_axioms() {
                self.enforce_axiom_dependency_policy(
                    imports,
                    policy,
                    &import.module,
                    axiom,
                    offset,
                )?;
            }
        }

        for axiom in module_axioms {
            self.enforce_axiom_ref_policy(imports, policy, axiom)?;
        }
        Ok(())
    }

    fn enforce_axiom_ref_policy(
        &self,
        imports: &ReferenceImportEnvironment,
        policy: &ReferenceCheckerPolicy,
        axiom: &AxiomRef,
    ) -> DecodeResult<()> {
        let raw_name = self.name_table[axiom.name].value.dotted();
        let qualified_name = match &axiom.global_ref {
            GlobalRef::Imported { import_index, .. } => imports
                .imports()
                .get(*import_index)
                .map(|import| qualify_name(&import.module, &raw_name)),
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {
                Some(qualify_name(&self.header.module, &raw_name))
            }
            GlobalRef::Builtin { .. } => None,
        };
        let is_standard_exception = match &axiom.global_ref {
            GlobalRef::Builtin { .. } => raw_name == "Eq.rec",
            GlobalRef::Imported { .. }
            | GlobalRef::Local { .. }
            | GlobalRef::LocalGenerated { .. } => {
                qualified_name.as_deref() == Some("Std.Logic.Eq.rec")
            }
        };
        let offset = self.axiom_report.module_axioms_offset;
        enforce_axiom_policy_name(
            policy,
            &raw_name,
            qualified_name.as_deref(),
            is_standard_exception,
            ReferenceCertificateSection::AxiomReport,
            offset,
        )
    }

    fn enforce_axiom_dependency_policy(
        &self,
        imports: &ReferenceImportEnvironment,
        policy: &ReferenceCheckerPolicy,
        module: &ReferenceModuleName,
        axiom: &ReferenceAxiomDependency,
        offset: usize,
    ) -> DecodeResult<()> {
        let raw_name = axiom.name.dotted();
        let qualified_name =
            import_index_exporting_axiom(imports, &axiom.name, axiom.decl_interface_hash)
                .and_then(|import_index| imports.imports().get(import_index))
                .map(|source| qualify_name(&source.module, &raw_name))
                .unwrap_or_else(|| qualify_name(module, &raw_name));
        enforce_axiom_policy_name(
            policy,
            &raw_name,
            Some(&qualified_name),
            qualified_name == "Std.Logic.Eq.rec",
            ReferenceCertificateSection::Imports,
            offset,
        )
    }

    fn compute_level_hashes(&self) -> DecodeResult<Vec<ReferenceHash>> {
        let mut hashes = Vec::with_capacity(self.level_table.len());
        for located in &self.level_table {
            let key = level_node_key(&located.value, &hashes, &self.name_table)?;
            hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &key));
        }
        Ok(hashes)
    }

    fn compute_term_hashes(
        &self,
        level_hashes: &[ReferenceHash],
    ) -> DecodeResult<Vec<ReferenceHash>> {
        let mut hashes = Vec::with_capacity(self.term_table.len());
        for located in &self.term_table {
            let key = term_node_key(&located.value, &hashes, level_hashes)?;
            hashes.push(hash_with_domain(b"NPA-TERM-0.1", &key));
        }
        Ok(hashes)
    }

    fn core_levels(&self) -> DecodeResult<Vec<ReferenceCoreLevel>> {
        let mut levels: Vec<ReferenceCoreLevel> = Vec::with_capacity(self.level_table.len());
        for located in &self.level_table {
            levels.push(match &located.value {
                LevelNode::Zero => ReferenceCoreLevel::Zero,
                LevelNode::Succ(inner) => {
                    ReferenceCoreLevel::Succ(Arc::new(levels[*inner].clone()))
                }
                LevelNode::Max(lhs, rhs) => ReferenceCoreLevel::Max(
                    Arc::new(levels[*lhs].clone()),
                    Arc::new(levels[*rhs].clone()),
                ),
                LevelNode::IMax(lhs, rhs) => ReferenceCoreLevel::IMax(
                    Arc::new(levels[*lhs].clone()),
                    Arc::new(levels[*rhs].clone()),
                ),
                LevelNode::Param(name) => {
                    ReferenceCoreLevel::Param(self.name_table[*name].value.clone())
                }
            });
        }
        Ok(levels)
    }

    fn core_terms(
        &self,
        core_levels: &[ReferenceCoreLevel],
    ) -> DecodeResult<Vec<ReferenceCoreExpr>> {
        let mut terms: Vec<ReferenceCoreExpr> = Vec::with_capacity(self.term_table.len());
        for located in &self.term_table {
            terms.push(match &located.value {
                TermNode::Sort(level) => ReferenceCoreExpr::Sort(core_levels[*level].clone()),
                TermNode::BVar(index) => ReferenceCoreExpr::BVar(*index),
                TermNode::Const {
                    global_ref,
                    levels: level_ids,
                } => ReferenceCoreExpr::Const {
                    global_ref: self.core_global_ref(global_ref),
                    levels: level_ids
                        .iter()
                        .map(|level| core_levels[*level].clone())
                        .collect(),
                },
                TermNode::App(fun, arg) => ReferenceCoreExpr::App(
                    Arc::new(terms[*fun].clone()),
                    Arc::new(terms[*arg].clone()),
                ),
                TermNode::Lam { ty, body } => ReferenceCoreExpr::Lam {
                    ty: Arc::new(terms[*ty].clone()),
                    body: Arc::new(terms[*body].clone()),
                },
                TermNode::Pi { ty, body } => ReferenceCoreExpr::Pi {
                    ty: Arc::new(terms[*ty].clone()),
                    body: Arc::new(terms[*body].clone()),
                },
                TermNode::Let { ty, value, body } => ReferenceCoreExpr::Let {
                    ty: Arc::new(terms[*ty].clone()),
                    value: Arc::new(terms[*value].clone()),
                    body: Arc::new(terms[*body].clone()),
                },
            });
        }
        Ok(terms)
    }

    fn core_global_ref(&self, global_ref: &GlobalRef) -> ReferenceCoreGlobalRef {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => ReferenceCoreGlobalRef::Builtin {
                name: self.name_table[*name].value.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => ReferenceCoreGlobalRef::Imported {
                import_index: *import_index,
                name: self.name_table[*name].value.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            GlobalRef::Local { decl_index } => ReferenceCoreGlobalRef::Local {
                decl_index: *decl_index,
            },
            GlobalRef::LocalGenerated { decl_index, name } => {
                ReferenceCoreGlobalRef::LocalGenerated {
                    decl_index: *decl_index,
                    name: self.name_table[*name].value.clone(),
                }
            }
        }
    }

    fn build_export_block(&self, term_hashes: &[ReferenceHash]) -> DecodeResult<Vec<ExportEntry>> {
        let mut entries = Vec::new();
        for located in &self.declarations {
            let decl = &located.value;
            let export_constraints = decl_universe_constraints(&decl.decl);
            match &decl.decl {
                DeclPayload::Axiom {
                    name,
                    universe_params,
                    ty,
                }
                | DeclPayload::AxiomConstrained {
                    name,
                    universe_params,
                    ty,
                    ..
                } => entries.push(ExportEntry {
                    name: *name,
                    kind: ExportKind::Axiom,
                    universe_params: universe_params.clone(),
                    universe_constraints: export_constraints.to_vec(),
                    ty: *ty,
                    body: None,
                    type_hash: term_hashes[*ty],
                    body_hash: None,
                    reducibility: None,
                    opacity: None,
                    decl_interface_hash: decl.hashes.decl_interface_hash,
                    axiom_dependencies: decl.axiom_dependencies.clone(),
                }),
                DeclPayload::Def {
                    name,
                    universe_params,
                    ty,
                    value,
                    reducibility,
                }
                | DeclPayload::DefConstrained {
                    name,
                    universe_params,
                    ty,
                    value,
                    reducibility,
                    ..
                } => entries.push(ExportEntry {
                    name: *name,
                    kind: ExportKind::Def,
                    universe_params: universe_params.clone(),
                    universe_constraints: export_constraints.to_vec(),
                    ty: *ty,
                    body: (*reducibility == CertReducibility::Reducible).then_some(*value),
                    type_hash: term_hashes[*ty],
                    body_hash: (*reducibility == CertReducibility::Reducible)
                        .then_some(term_hashes[*value]),
                    reducibility: Some(*reducibility),
                    opacity: None,
                    decl_interface_hash: decl.hashes.decl_interface_hash,
                    axiom_dependencies: decl.axiom_dependencies.clone(),
                }),
                DeclPayload::Theorem {
                    name,
                    universe_params,
                    ty,
                    ..
                }
                | DeclPayload::TheoremConstrained {
                    name,
                    universe_params,
                    ty,
                    ..
                } => entries.push(ExportEntry {
                    name: *name,
                    kind: ExportKind::Theorem,
                    universe_params: universe_params.clone(),
                    universe_constraints: export_constraints.to_vec(),
                    ty: *ty,
                    body: None,
                    type_hash: term_hashes[*ty],
                    body_hash: None,
                    reducibility: None,
                    opacity: Some(Opacity::Opaque),
                    decl_interface_hash: decl.hashes.decl_interface_hash,
                    axiom_dependencies: decl.axiom_dependencies.clone(),
                }),
                DeclPayload::Inductive {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                }
                | DeclPayload::InductiveConstrained {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                    ..
                } => {
                    let ty =
                        inductive_export_type_term_id(&self.term_table, params, indices, *sort)?;
                    entries.push(ExportEntry {
                        name: *name,
                        kind: ExportKind::Inductive,
                        universe_params: universe_params.clone(),
                        universe_constraints: export_constraints.to_vec(),
                        ty,
                        body: None,
                        type_hash: term_hashes[ty],
                        body_hash: None,
                        reducibility: None,
                        opacity: None,
                        decl_interface_hash: decl.hashes.decl_interface_hash,
                        axiom_dependencies: decl.axiom_dependencies.clone(),
                    });
                    for constructor in constructors {
                        entries.push(ExportEntry {
                            name: constructor.name,
                            kind: ExportKind::Constructor,
                            universe_params: universe_params.clone(),
                            universe_constraints: export_constraints.to_vec(),
                            ty: constructor.ty,
                            body: None,
                            type_hash: term_hashes[constructor.ty],
                            body_hash: None,
                            reducibility: None,
                            opacity: None,
                            decl_interface_hash: decl.hashes.decl_interface_hash,
                            axiom_dependencies: decl.axiom_dependencies.clone(),
                        });
                    }
                    if let Some(recursor) = recursor {
                        entries.push(ExportEntry {
                            name: recursor.name,
                            kind: ExportKind::Recursor,
                            universe_params: recursor.universe_params.clone(),
                            universe_constraints: export_constraints.to_vec(),
                            ty: recursor.ty,
                            body: None,
                            type_hash: term_hashes[recursor.ty],
                            body_hash: None,
                            reducibility: None,
                            opacity: None,
                            decl_interface_hash: decl.hashes.decl_interface_hash,
                            axiom_dependencies: decl.axiom_dependencies.clone(),
                        });
                    }
                }
                DeclPayload::MutualInductiveBlock {
                    universe_params,
                    inductives,
                    ..
                } => {
                    for inductive in inductives {
                        let ty = inductive_export_type_term_id(
                            &self.term_table,
                            &inductive.params,
                            &inductive.indices,
                            inductive.sort,
                        )?;
                        entries.push(ExportEntry {
                            name: inductive.name,
                            kind: ExportKind::Inductive,
                            universe_params: universe_params.clone(),
                            universe_constraints: export_constraints.to_vec(),
                            ty,
                            body: None,
                            type_hash: term_hashes[ty],
                            body_hash: None,
                            reducibility: None,
                            opacity: None,
                            decl_interface_hash: decl.hashes.decl_interface_hash,
                            axiom_dependencies: decl.axiom_dependencies.clone(),
                        });
                        for constructor in &inductive.constructors {
                            entries.push(ExportEntry {
                                name: constructor.name,
                                kind: ExportKind::Constructor,
                                universe_params: universe_params.clone(),
                                universe_constraints: export_constraints.to_vec(),
                                ty: constructor.ty,
                                body: None,
                                type_hash: term_hashes[constructor.ty],
                                body_hash: None,
                                reducibility: None,
                                opacity: None,
                                decl_interface_hash: decl.hashes.decl_interface_hash,
                                axiom_dependencies: decl.axiom_dependencies.clone(),
                            });
                        }
                        if let Some(recursor) = &inductive.recursor {
                            entries.push(ExportEntry {
                                name: recursor.name,
                                kind: ExportKind::Recursor,
                                universe_params: recursor.universe_params.clone(),
                                universe_constraints: export_constraints.to_vec(),
                                ty: recursor.ty,
                                body: None,
                                type_hash: term_hashes[recursor.ty],
                                body_hash: None,
                                reducibility: None,
                                opacity: None,
                                decl_interface_hash: decl.hashes.decl_interface_hash,
                                axiom_dependencies: decl.axiom_dependencies.clone(),
                            });
                        }
                    }
                }
            }
        }
        entries.sort_by_key(|entry| entry.name);
        Ok(entries)
    }

    fn validate_import_order(&self) -> DecodeResult<()> {
        let mut seen = BTreeSet::new();
        for import in &self.imports {
            if !seen.insert((import.value.module.clone(), import.value.export_hash)) {
                return Err(ReferenceCheckError::import_resolution(
                    ReferenceCertificateSection::Imports,
                    import.offset,
                    ReferenceCheckReason::DuplicateImport,
                ));
            }
        }
        for pair in self.imports.windows(2) {
            let previous = import_order_key(&pair[0].value);
            let current = import_order_key(&pair[1].value);
            if previous >= current {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Imports,
                    pair[1].offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
        }
        Ok(())
    }

    fn validate_decl_universe_contexts(&self) -> DecodeResult<()> {
        let levels = self.core_levels()?;
        for located in &self.declarations {
            let params = self.name_ids_to_names(decl_universe_params(&located.value.decl));
            if params.iter().any(is_unresolved_universe_meta_name) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    located.offset,
                    ReferenceCheckReason::UnresolvedMetavariable,
                ));
            }
            if !params.windows(2).all(|pair| pair[0] < pair[1]) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    located.offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
            ensure_unique_names(&params, located.offset)?;
            let constraints = decl_universe_constraints(&located.value.decl);
            if decl_has_empty_constrained_universe_payload(&located.value.decl) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    located.offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
            let semantic_constraints = constraints
                .iter()
                .map(|constraint| {
                    (
                        levels[constraint.lhs].clone(),
                        constraint.relation,
                        levels[constraint.rhs].clone(),
                    )
                })
                .collect::<Vec<_>>();
            if !semantic_constraints
                .windows(2)
                .all(|pair| pair[0] < pair[1])
            {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    located.offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
            for (lhs, _, rhs) in &semantic_constraints {
                ensure_level_wf(lhs, &params, located.offset)?;
                ensure_level_wf(rhs, &params, located.offset)?;
            }
        }
        Ok(())
    }

    fn validate_name_table_order(&self) -> DecodeResult<()> {
        for pair in self.name_table.windows(2) {
            if pair[0].value == pair[1].value {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::NameTable,
                    pair[1].offset,
                    ReferenceCheckReason::DuplicateName,
                ));
            }
            if pair[0].value > pair[1].value {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::NameTable,
                    pair[1].offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
        }
        Ok(())
    }

    fn validate_level_table(&self) -> DecodeResult<Vec<ReferenceHash>> {
        let mut hashes = Vec::with_capacity(self.level_table.len());
        let mut keys = Vec::with_capacity(self.level_table.len());
        let mut raw_levels = Vec::with_capacity(self.level_table.len());
        for (index, located) in self.level_table.iter().enumerate() {
            self.validate_level_refs(index, located)?;
            let raw = raw_level_from_node(&located.value, &raw_levels, &self.name_table)?;
            if normalize_level(raw.clone()) != raw {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::LevelTable,
                    located.offset,
                    ReferenceCheckReason::NonNormalizedLevel,
                ));
            }
            let key = level_node_key(&located.value, &hashes, &self.name_table)?;
            let hash = hash_with_domain(b"NPA-LEVEL-0.1", &key);
            keys.push((level_node_height(&located.value, &self.level_table)?, key));
            hashes.push(hash);
            raw_levels.push(raw);
        }
        for (index, pair) in keys.windows(2).enumerate() {
            if pair[0] >= pair[1] {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::LevelTable,
                    self.level_table[index + 1].offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
        }
        Ok(hashes)
    }

    fn validate_level_refs(&self, index: usize, located: &Located<LevelNode>) -> DecodeResult<()> {
        match &located.value {
            LevelNode::Zero => Ok(()),
            LevelNode::Succ(inner) => self.require_previous_level(index, *inner, located.offset),
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                self.require_previous_level(index, *lhs, located.offset)?;
                self.require_previous_level(index, *rhs, located.offset)
            }
            LevelNode::Param(name) => self.require_name(
                *name,
                ReferenceCertificateSection::LevelTable,
                located.offset,
            ),
        }
    }

    fn validate_term_table(&self, level_hashes: &[ReferenceHash]) -> DecodeResult<()> {
        let mut hashes = Vec::with_capacity(self.term_table.len());
        let mut keys = Vec::with_capacity(self.term_table.len());
        for (index, located) in self.term_table.iter().enumerate() {
            self.validate_term_refs(index, located)?;
            let key = term_node_key(&located.value, &hashes, level_hashes)?;
            keys.push((
                term_node_height(&located.value, &self.term_table)?,
                key.clone(),
            ));
            hashes.push(hash_with_domain(b"NPA-TERM-0.1", &key));
        }
        for (index, pair) in keys.windows(2).enumerate() {
            if pair[0] >= pair[1] {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::TermTable,
                    self.term_table[index + 1].offset,
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
        }
        Ok(())
    }

    fn validate_term_refs(&self, index: usize, located: &Located<TermNode>) -> DecodeResult<()> {
        match &located.value {
            TermNode::Sort(level) => self.require_level(
                *level,
                ReferenceCertificateSection::TermTable,
                located.offset,
            ),
            TermNode::BVar(_) => Ok(()),
            TermNode::Const { global_ref, levels } => {
                self.require_global_ref(
                    global_ref,
                    ReferenceCertificateSection::TermTable,
                    located.offset,
                )?;
                for level in levels {
                    self.require_level(
                        *level,
                        ReferenceCertificateSection::TermTable,
                        located.offset,
                    )?;
                }
                Ok(())
            }
            TermNode::App(fun, arg) => {
                self.require_previous_term(index, *fun, located.offset)?;
                self.require_previous_term(index, *arg, located.offset)
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                self.require_previous_term(index, *ty, located.offset)?;
                self.require_previous_term(index, *body, located.offset)
            }
            TermNode::Let { ty, value, body } => {
                self.require_previous_term(index, *ty, located.offset)?;
                self.require_previous_term(index, *value, located.offset)?;
                self.require_previous_term(index, *body, located.offset)
            }
        }
    }

    fn collect_name_roots(&self, used: &mut UsedTables) -> DecodeResult<()> {
        used.names.insert(self.header.module.clone());
        for import in &self.imports {
            used.names.insert(import.value.module.clone());
        }
        Ok(())
    }

    fn collect_decl_roots(&self, used: &mut UsedTables) -> DecodeResult<()> {
        for located in &self.declarations {
            self.collect_decl_payload(&located.value.decl, used, located.offset)?;
            self.collect_dependency_entries(&located.value.dependencies, used, located.offset)?;
            self.collect_axiom_refs(
                &located.value.axiom_dependencies,
                used,
                ReferenceCertificateSection::Declarations,
                located.offset,
            )?;
        }
        Ok(())
    }

    fn collect_export_roots(&self, used: &mut UsedTables) -> DecodeResult<()> {
        for located in &self.export_block {
            let entry = &located.value;
            self.collect_name_id(
                entry.name,
                used,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
            self.collect_name_ids(
                &entry.universe_params,
                used,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
            self.collect_universe_constraints(
                &entry.universe_constraints,
                used,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
            self.collect_term_root(
                entry.ty,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
            used.terms.insert(entry.ty);
            if let Some(body) = entry.body {
                self.collect_term_root(
                    body,
                    ReferenceCertificateSection::ExportBlock,
                    located.offset,
                )?;
                used.terms.insert(body);
            }
            self.collect_axiom_refs(
                &entry.axiom_dependencies,
                used,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
        }
        Ok(())
    }

    fn collect_axiom_report_roots(&self, used: &mut UsedTables) -> DecodeResult<()> {
        for report in &self.axiom_report.per_declaration {
            if report.decl_index >= self.declarations.len() {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::AxiomReport,
                    report.offset,
                    ReferenceCheckReason::DanglingReference,
                ));
            }
            self.collect_axiom_refs(
                &report.direct_axioms,
                used,
                ReferenceCertificateSection::AxiomReport,
                report.offset,
            )?;
            self.collect_axiom_refs(
                &report.transitive_axioms,
                used,
                ReferenceCertificateSection::AxiomReport,
                report.offset,
            )?;
        }
        self.collect_axiom_refs(
            &self.axiom_report.module_axioms,
            used,
            ReferenceCertificateSection::AxiomReport,
            self.axiom_report.module_axioms_offset,
        )
    }

    fn collect_decl_payload(
        &self,
        decl: &DeclPayload,
        used: &mut UsedTables,
        offset: usize,
    ) -> DecodeResult<()> {
        match decl {
            DeclPayload::Axiom {
                name,
                universe_params,
                ty,
            }
            | DeclPayload::AxiomConstrained {
                name,
                universe_params,
                ty,
                ..
            } => {
                self.collect_name_id(
                    *name,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_name_ids(
                    universe_params,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_universe_constraints(
                    decl_universe_constraints(decl),
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_term_root(*ty, ReferenceCertificateSection::Declarations, offset)?;
                used.terms.insert(*ty);
            }
            DeclPayload::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility: _,
            }
            | DeclPayload::DefConstrained {
                name,
                universe_params,
                ty,
                value,
                ..
            } => {
                self.collect_name_id(
                    *name,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_name_ids(
                    universe_params,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_universe_constraints(
                    decl_universe_constraints(decl),
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_term_root(*ty, ReferenceCertificateSection::Declarations, offset)?;
                self.collect_term_root(*value, ReferenceCertificateSection::Declarations, offset)?;
                used.terms.insert(*ty);
                used.terms.insert(*value);
            }
            DeclPayload::Theorem {
                name,
                universe_params,
                ty,
                proof,
                opacity: _,
            }
            | DeclPayload::TheoremConstrained {
                name,
                universe_params,
                ty,
                proof,
                ..
            } => {
                self.collect_name_id(
                    *name,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_name_ids(
                    universe_params,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_universe_constraints(
                    decl_universe_constraints(decl),
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_term_root(*ty, ReferenceCertificateSection::Declarations, offset)?;
                self.collect_term_root(*proof, ReferenceCertificateSection::Declarations, offset)?;
                used.terms.insert(*ty);
                used.terms.insert(*proof);
            }
            DeclPayload::Inductive {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
            }
            | DeclPayload::InductiveConstrained {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            } => {
                self.collect_name_id(
                    *name,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_name_ids(
                    universe_params,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_universe_constraints(
                    decl_universe_constraints(decl),
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.require_level(*sort, ReferenceCertificateSection::Declarations, offset)?;
                used.levels.insert(*sort);
                for binder in params.iter().chain(indices) {
                    self.collect_term_root(
                        binder.ty,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    used.terms.insert(binder.ty);
                }
                for constructor in constructors {
                    self.collect_name_id(
                        constructor.name,
                        used,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    self.collect_term_root(
                        constructor.ty,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    used.terms.insert(constructor.ty);
                }
                if let Some(recursor) = recursor {
                    self.collect_name_id(
                        recursor.name,
                        used,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    self.collect_name_ids(
                        &recursor.universe_params,
                        used,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    self.collect_term_root(
                        recursor.ty,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    used.terms.insert(recursor.ty);
                    let _ = recursor.rules;
                }
            }
            DeclPayload::MutualInductiveBlock {
                name,
                universe_params,
                inductives,
                ..
            } => {
                self.collect_name_id(
                    *name,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_name_ids(
                    universe_params,
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                self.collect_universe_constraints(
                    decl_universe_constraints(decl),
                    used,
                    ReferenceCertificateSection::Declarations,
                    offset,
                )?;
                for inductive in inductives {
                    self.collect_name_id(
                        inductive.name,
                        used,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    self.require_level(
                        inductive.sort,
                        ReferenceCertificateSection::Declarations,
                        offset,
                    )?;
                    used.levels.insert(inductive.sort);
                    for binder in inductive.params.iter().chain(&inductive.indices) {
                        self.collect_term_root(
                            binder.ty,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        used.terms.insert(binder.ty);
                    }
                    for constructor in &inductive.constructors {
                        self.collect_name_id(
                            constructor.name,
                            used,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        self.collect_term_root(
                            constructor.ty,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        used.terms.insert(constructor.ty);
                    }
                    if let Some(recursor) = &inductive.recursor {
                        self.collect_name_id(
                            recursor.name,
                            used,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        self.collect_name_ids(
                            &recursor.universe_params,
                            used,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        self.collect_term_root(
                            recursor.ty,
                            ReferenceCertificateSection::Declarations,
                            offset,
                        )?;
                        used.terms.insert(recursor.ty);
                        let _ = recursor.rules;
                    }
                }
            }
        }
        Ok(())
    }

    fn collect_universe_constraints(
        &self,
        constraints: &[UniverseConstraintSpec],
        used: &mut UsedTables,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        for constraint in constraints {
            self.require_level(constraint.lhs, section, offset)?;
            self.require_level(constraint.rhs, section, offset)?;
            used.levels.insert(constraint.lhs);
            used.levels.insert(constraint.rhs);
        }
        Ok(())
    }

    fn collect_dependency_entries(
        &self,
        entries: &[DependencyEntry],
        used: &mut UsedTables,
        offset: usize,
    ) -> DecodeResult<()> {
        for entry in entries {
            self.collect_global_ref(
                &entry.global_ref,
                used,
                ReferenceCertificateSection::Declarations,
                offset,
            )?;
        }
        Ok(())
    }

    fn collect_axiom_refs(
        &self,
        axioms: &[AxiomRef],
        used: &mut UsedTables,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        for axiom in axioms {
            self.collect_global_ref(&axiom.global_ref, used, section, offset)?;
            self.collect_name_id(axiom.name, used, section, offset)?;
        }
        Ok(())
    }

    fn collect_reachable_terms(&self, used: &mut UsedTables) -> DecodeResult<()> {
        let mut stack = used.terms.iter().copied().collect::<Vec<_>>();
        while let Some(term_id) = stack.pop() {
            let located = self.term_table.get(term_id).ok_or_else(|| {
                ReferenceCheckError::malformed(
                    ReferenceCertificateSection::TermTable,
                    self.term_table.last().map_or(0, |entry| entry.offset),
                    ReferenceCheckReason::DanglingReference,
                )
            })?;
            let term = &located.value;
            match term {
                TermNode::Sort(level) => {
                    used.levels.insert(*level);
                }
                TermNode::BVar(_) => {}
                TermNode::Const { global_ref, levels } => {
                    self.collect_global_ref(
                        global_ref,
                        used,
                        ReferenceCertificateSection::TermTable,
                        located.offset,
                    )?;
                    used.levels.extend(levels.iter().copied());
                }
                TermNode::App(fun, arg) => {
                    push_term(*fun, used, &mut stack);
                    push_term(*arg, used, &mut stack);
                }
                TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                    push_term(*ty, used, &mut stack);
                    push_term(*body, used, &mut stack);
                }
                TermNode::Let { ty, value, body } => {
                    push_term(*ty, used, &mut stack);
                    push_term(*value, used, &mut stack);
                    push_term(*body, used, &mut stack);
                }
            }
        }
        Ok(())
    }

    fn collect_reachable_levels(&self, used: &mut UsedTables) -> DecodeResult<()> {
        let mut stack = used.levels.iter().copied().collect::<Vec<_>>();
        while let Some(level_id) = stack.pop() {
            let level = &self
                .level_table
                .get(level_id)
                .ok_or_else(|| {
                    ReferenceCheckError::malformed(
                        ReferenceCertificateSection::LevelTable,
                        self.level_table.last().map_or(0, |entry| entry.offset),
                        ReferenceCheckReason::DanglingReference,
                    )
                })?
                .value;
            match level {
                LevelNode::Zero => {}
                LevelNode::Succ(inner) => push_level(*inner, used, &mut stack),
                LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                    push_level(*lhs, used, &mut stack);
                    push_level(*rhs, used, &mut stack);
                }
                LevelNode::Param(name) => {
                    self.collect_name_id(*name, used, ReferenceCertificateSection::LevelTable, 0)?;
                }
            }
        }
        Ok(())
    }

    fn validate_declaration_order(&self) -> DecodeResult<()> {
        let mut local_names = Vec::with_capacity(self.declarations.len());
        let mut seen = BTreeSet::new();
        for located in &self.declarations {
            let name_id = located.value.decl.name_id();
            self.require_name(
                name_id,
                ReferenceCertificateSection::Declarations,
                located.offset,
            )?;
            let name = self.name_table[name_id].value.clone();
            if !seen.insert(name.clone()) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    located.offset,
                    ReferenceCheckReason::DuplicateDeclarationName,
                ));
            }
            local_names.push(name);
        }

        let dependencies = self
            .declarations
            .iter()
            .enumerate()
            .map(|(decl_index, located)| {
                let mut deps = BTreeSet::new();
                for dependency in &located.value.dependencies {
                    match &dependency.global_ref {
                        GlobalRef::Local {
                            decl_index: dependency_index,
                        }
                        | GlobalRef::LocalGenerated {
                            decl_index: dependency_index,
                            ..
                        } => {
                            if *dependency_index >= decl_index {
                                return Err(ReferenceCheckError::malformed(
                                    ReferenceCertificateSection::Declarations,
                                    located.offset,
                                    ReferenceCheckReason::NonCanonicalOrder,
                                ));
                            }
                            deps.insert(*dependency_index);
                        }
                        GlobalRef::Builtin { .. } | GlobalRef::Imported { .. } => {}
                    }
                }
                Ok(deps)
            })
            .collect::<DecodeResult<Vec<_>>>()?;

        let mut emitted = BTreeSet::new();
        let mut remaining = (0..self.declarations.len()).collect::<BTreeSet<_>>();
        let mut expected = Vec::with_capacity(self.declarations.len());
        while !remaining.is_empty() {
            let mut ready = remaining
                .iter()
                .copied()
                .filter(|index| dependencies[*index].is_subset(&emitted))
                .collect::<Vec<_>>();
            if ready.is_empty() {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    self.declarations.first().map_or(0, |entry| entry.offset),
                    ReferenceCheckReason::NonCanonicalOrder,
                ));
            }
            ready.sort_by_key(|index| local_names[*index].clone());
            for index in ready {
                remaining.remove(&index);
                emitted.insert(index);
                expected.push(index);
            }
        }
        if expected != (0..self.declarations.len()).collect::<Vec<_>>() {
            let bad_index = expected
                .iter()
                .zip(0..self.declarations.len())
                .find_map(|(actual, expected)| (*actual != expected).then_some(expected))
                .unwrap_or(0);
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::Declarations,
                self.declarations
                    .get(bad_index)
                    .map_or(0, |entry| entry.offset),
                ReferenceCheckReason::NonCanonicalOrder,
            ));
        }
        Ok(())
    }

    fn validate_vector_orders(&self) -> DecodeResult<()> {
        for located in &self.declarations {
            ensure_strict_order(
                &located.value.dependencies,
                ReferenceCertificateSection::Declarations,
                located.offset,
            )?;
            ensure_strict_order(
                &located.value.axiom_dependencies,
                ReferenceCertificateSection::Declarations,
                located.offset,
            )?;
        }
        for located in &self.export_block {
            ensure_strict_order(
                &located.value.axiom_dependencies,
                ReferenceCertificateSection::ExportBlock,
                located.offset,
            )?;
        }
        for report in &self.axiom_report.per_declaration {
            ensure_strict_order(
                &report.direct_axioms,
                ReferenceCertificateSection::AxiomReport,
                report.offset,
            )?;
            ensure_strict_order(
                &report.transitive_axioms,
                ReferenceCertificateSection::AxiomReport,
                report.offset,
            )?;
        }
        ensure_strict_order(
            &self.axiom_report.module_axioms,
            ReferenceCertificateSection::AxiomReport,
            self.axiom_report.module_axioms_offset,
        )
    }

    fn validate_used_names(&self, used_names: &BTreeSet<ReferenceModuleName>) -> DecodeResult<()> {
        let actual = self
            .name_table
            .iter()
            .map(|entry| entry.value.clone())
            .collect::<Vec<_>>();
        let expected = used_names.iter().cloned().collect::<Vec<_>>();
        if actual == expected {
            return Ok(());
        }
        for entry in &self.name_table {
            if !used_names.contains(&entry.value) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::NameTable,
                    entry.offset,
                    ReferenceCheckReason::UnusedTableEntry,
                ));
            }
        }
        Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::NameTable,
            self.name_table.first().map_or(0, |entry| entry.offset),
            ReferenceCheckReason::NonCanonicalOrder,
        ))
    }

    fn validate_used_levels(&self, used_levels: &BTreeSet<usize>) -> DecodeResult<()> {
        for (index, entry) in self.level_table.iter().enumerate() {
            if !used_levels.contains(&index) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::LevelTable,
                    entry.offset,
                    ReferenceCheckReason::UnusedTableEntry,
                ));
            }
        }
        Ok(())
    }

    fn validate_used_terms(&self, used_terms: &BTreeSet<usize>) -> DecodeResult<()> {
        for (index, entry) in self.term_table.iter().enumerate() {
            if !used_terms.contains(&index) {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::TermTable,
                    entry.offset,
                    ReferenceCheckReason::UnusedTableEntry,
                ));
            }
        }
        Ok(())
    }

    fn collect_name_id(
        &self,
        id: usize,
        used: &mut UsedTables,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        let name = self
            .name_table
            .get(id)
            .ok_or_else(|| {
                ReferenceCheckError::malformed(
                    section,
                    offset,
                    ReferenceCheckReason::DanglingReference,
                )
            })?
            .value
            .clone();
        used.names.insert(name);
        Ok(())
    }

    fn collect_name_ids(
        &self,
        ids: &[usize],
        used: &mut UsedTables,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        for id in ids {
            self.collect_name_id(*id, used, section, offset)?;
        }
        Ok(())
    }

    fn collect_term_root(
        &self,
        id: usize,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        self.require_term(id, section, offset)
    }

    fn collect_global_ref(
        &self,
        global_ref: &GlobalRef,
        used: &mut UsedTables,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        self.require_global_ref(global_ref, section, offset)?;
        match global_ref {
            GlobalRef::Builtin { name, .. }
            | GlobalRef::Imported { name, .. }
            | GlobalRef::LocalGenerated { name, .. } => {
                self.collect_name_id(*name, used, section, offset)?;
            }
            GlobalRef::Local { .. } => {}
        }
        Ok(())
    }

    fn require_name(
        &self,
        id: usize,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        if id < self.name_table.len() {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }

    fn require_level(
        &self,
        id: usize,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        if id < self.level_table.len() {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }

    fn require_term(
        &self,
        id: usize,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        if id < self.term_table.len() {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }

    fn require_previous_level(&self, index: usize, id: usize, offset: usize) -> DecodeResult<()> {
        if id < index {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::LevelTable,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }

    fn require_previous_term(&self, index: usize, id: usize, offset: usize) -> DecodeResult<()> {
        if id < index {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::TermTable,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }

    fn require_global_ref(
        &self,
        global_ref: &GlobalRef,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        match global_ref {
            GlobalRef::Builtin { name, .. } => self.require_name(*name, section, offset),
            GlobalRef::Imported {
                import_index, name, ..
            } => {
                if *import_index >= self.imports.len() {
                    return Err(ReferenceCheckError::malformed(
                        section,
                        offset,
                        ReferenceCheckReason::DanglingReference,
                    ));
                }
                self.require_name(*name, section, offset)
            }
            GlobalRef::Local { decl_index } => self.require_decl(*decl_index, section, offset),
            GlobalRef::LocalGenerated { decl_index, name } => {
                self.require_decl(*decl_index, section, offset)?;
                self.require_name(*name, section, offset)
            }
        }
    }

    fn require_decl(
        &self,
        id: usize,
        section: ReferenceCertificateSection,
        offset: usize,
    ) -> DecodeResult<()> {
        if id < self.declarations.len() {
            Ok(())
        } else {
            Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::DanglingReference,
            ))
        }
    }
}

fn resolve_import<'a>(
    requested: &Located<ImportEntry>,
    import_store: &'a ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
) -> DecodeResult<&'a ReferenceImportEntry> {
    let same_module = import_store
        .entries()
        .iter()
        .filter(|entry| entry.module() == &requested.value.module)
        .collect::<Vec<_>>();
    if same_module.is_empty() {
        return Err(ReferenceCheckError::import_resolution(
            ReferenceCertificateSection::Imports,
            requested.offset,
            ReferenceCheckReason::MissingImport,
        ));
    }

    let same_export = same_module
        .into_iter()
        .filter(|entry| *entry.export_hash() == requested.value.export_hash)
        .collect::<Vec<_>>();
    if same_export.is_empty() {
        return Err(ReferenceCheckError::import_resolution(
            ReferenceCertificateSection::Imports,
            requested.offset,
            ReferenceCheckReason::ImportExportHashMismatch,
        ));
    }
    if same_export.len() > 1 {
        return Err(ReferenceCheckError::import_resolution(
            ReferenceCertificateSection::Imports,
            requested.offset,
            ReferenceCheckReason::DuplicateImport,
        ));
    }

    let entry = same_export[0];
    enforce_core_feature_policy(
        entry.public_environment().core_features(),
        requested.offset,
        policy,
    )?;
    if let Some(certificate_hash) = requested.value.certificate_hash {
        if *entry.certificate_hash() != certificate_hash {
            return Err(ReferenceCheckError::import_resolution(
                ReferenceCertificateSection::Imports,
                requested.offset,
                ReferenceCheckReason::ImportCertificateHashMismatch,
            ));
        }
    }

    if policy.trust_mode == ReferenceTrustMode::HighTrust {
        let Some(certificate_hash) = requested.value.certificate_hash else {
            return Err(ReferenceCheckError::import_resolution(
                ReferenceCertificateSection::Imports,
                requested.offset,
                ReferenceCheckReason::MissingImportCertificateHash,
            ));
        };
        if *entry.certificate_hash() != certificate_hash {
            return Err(ReferenceCheckError::import_resolution(
                ReferenceCertificateSection::Imports,
                requested.offset,
                ReferenceCheckReason::ImportCertificateHashMismatch,
            ));
        }
        if !entry.checked_by_reference_checker() {
            return Err(ReferenceCheckError::import_resolution(
                ReferenceCertificateSection::Imports,
                requested.offset,
                ReferenceCheckReason::UncheckedImport,
            ));
        }
    }

    Ok(entry)
}

fn enforce_core_feature_policy(
    features: &[ReferenceCoreFeature],
    offset: usize,
    policy: &ReferenceCheckerPolicy,
) -> DecodeResult<()> {
    let supported = policy
        .supported_core_features
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    for feature in features {
        if !supported.contains(feature) {
            return Err(ReferenceCheckError::unsupported_core_feature(offset));
        }
    }
    Ok(())
}

struct TypeChecker<'a> {
    cert: &'a DecodedModuleCertificate,
    imports: &'a ReferenceImportEnvironment,
    levels: Vec<ReferenceCoreLevel>,
    terms: Vec<ReferenceCoreExpr>,
    locals: Vec<Arc<TypeSignature>>,
    generated: BTreeMap<GeneratedKey, Arc<TypeSignature>>,
    builtin_signatures: RefCell<BTreeMap<ReferenceModuleName, Arc<TypeSignature>>>,
    imported_signatures:
        RefCell<BTreeMap<(usize, ReferenceModuleName, ReferenceHash), Arc<TypeSignature>>>,
    inductives: BTreeMap<usize, ReferenceInductiveSignature>,
    mutual_inductives: BTreeMap<GeneratedKey, ReferenceInductiveSignature>,
    recursors: BTreeMap<GeneratedKey, ReferenceRecursorRuntime>,
    imported_recursors: BTreeMap<ImportedRecursorKey, ReferenceImportedRecursorRuntime>,
}

impl<'a> TypeChecker<'a> {
    // Deterministic resource bounds for large source-free package certificates.
    const WHNF_FUEL: usize = 5_000_000;
    const DEFEQ_FUEL: usize = 5_000_000;

    fn new(
        cert: &'a DecodedModuleCertificate,
        imports: &'a ReferenceImportEnvironment,
    ) -> DecodeResult<Self> {
        let levels = cert.core_levels()?;
        let terms = cert.core_terms(&levels)?;
        let mut checker = Self {
            cert,
            imports,
            levels,
            terms,
            locals: Vec::new(),
            generated: BTreeMap::new(),
            builtin_signatures: RefCell::new(BTreeMap::new()),
            imported_signatures: RefCell::new(BTreeMap::new()),
            inductives: BTreeMap::new(),
            mutual_inductives: BTreeMap::new(),
            recursors: BTreeMap::new(),
            imported_recursors: BTreeMap::new(),
        };
        checker.imported_recursors = checker.imported_recursors(0)?;
        Ok(checker)
    }

    fn check_declarations(&mut self) -> DecodeResult<()> {
        for located in &self.cert.declarations {
            let ctx = TypeContext::default();
            match &located.value.decl {
                DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
                    let universe_context =
                        self.declaration_universe_context(&located.value.decl, located.offset)?;
                    self.expect_sort(&ctx, &universe_context, &self.terms[*ty], located.offset)?;
                    self.locals
                        .push(Arc::new(self.signature_for_decl(&located.value)?));
                }
                DeclPayload::Def { ty, value, .. }
                | DeclPayload::DefConstrained { ty, value, .. } => {
                    let universe_context =
                        self.declaration_universe_context(&located.value.decl, located.offset)?;
                    self.expect_sort(&ctx, &universe_context, &self.terms[*ty], located.offset)?;
                    self.check(
                        &ctx,
                        &universe_context,
                        &self.terms[*value],
                        &self.terms[*ty],
                        located.offset,
                    )?;
                    self.locals
                        .push(Arc::new(self.signature_for_decl(&located.value)?));
                }
                DeclPayload::Theorem { ty, proof, .. }
                | DeclPayload::TheoremConstrained { ty, proof, .. } => {
                    let universe_context =
                        self.declaration_universe_context(&located.value.decl, located.offset)?;
                    self.expect_sort(&ctx, &universe_context, &self.terms[*ty], located.offset)?;
                    self.check(
                        &ctx,
                        &universe_context,
                        &self.terms[*proof],
                        &self.terms[*ty],
                        located.offset,
                    )?;
                    self.locals
                        .push(Arc::new(self.signature_for_decl(&located.value)?));
                }
                DeclPayload::Inductive { .. } | DeclPayload::InductiveConstrained { .. } => {
                    self.check_inductive_decl(&located.value, located.offset)?;
                }
                DeclPayload::MutualInductiveBlock { .. } => {
                    self.check_mutual_inductive_decl(&located.value, located.offset)?;
                }
            }
        }
        Ok(())
    }

    fn declaration_universe_params(&self, decl: &DeclPayload) -> Vec<ReferenceModuleName> {
        let params = match decl {
            DeclPayload::Axiom {
                universe_params, ..
            }
            | DeclPayload::AxiomConstrained {
                universe_params, ..
            }
            | DeclPayload::Def {
                universe_params, ..
            }
            | DeclPayload::DefConstrained {
                universe_params, ..
            }
            | DeclPayload::Theorem {
                universe_params, ..
            }
            | DeclPayload::TheoremConstrained {
                universe_params, ..
            }
            | DeclPayload::Inductive {
                universe_params, ..
            }
            | DeclPayload::InductiveConstrained {
                universe_params, ..
            }
            | DeclPayload::MutualInductiveBlock {
                universe_params, ..
            } => universe_params,
        };
        self.cert.name_ids_to_names(params)
    }

    fn signature_for_decl(&self, decl: &DeclCert) -> DecodeResult<TypeSignature> {
        Ok(match &decl.decl {
            DeclPayload::Axiom {
                name: _,
                universe_params,
                ty,
            }
            | DeclPayload::AxiomConstrained {
                universe_params,
                ty,
                ..
            } => TypeSignature {
                universe_params: self.cert.name_ids_to_names(universe_params),
                universe_constraints: self.signature_universe_constraints(&decl.decl)?,
                ty: self.terms[*ty].clone(),
                value: None,
            },
            DeclPayload::Def {
                universe_params,
                ty,
                value,
                reducibility,
                ..
            }
            | DeclPayload::DefConstrained {
                universe_params,
                ty,
                value,
                reducibility,
                ..
            } => TypeSignature {
                universe_params: self.cert.name_ids_to_names(universe_params),
                universe_constraints: self.signature_universe_constraints(&decl.decl)?,
                ty: self.terms[*ty].clone(),
                value: (*reducibility == CertReducibility::Reducible)
                    .then(|| self.terms[*value].clone()),
            },
            DeclPayload::Theorem {
                universe_params,
                ty,
                ..
            }
            | DeclPayload::TheoremConstrained {
                universe_params,
                ty,
                ..
            } => TypeSignature {
                universe_params: self.cert.name_ids_to_names(universe_params),
                universe_constraints: self.signature_universe_constraints(&decl.decl)?,
                ty: self.terms[*ty].clone(),
                value: None,
            },
            DeclPayload::Inductive {
                universe_params,
                params,
                indices,
                sort,
                ..
            }
            | DeclPayload::InductiveConstrained {
                universe_params,
                params,
                indices,
                sort,
                ..
            } => TypeSignature {
                universe_params: self.cert.name_ids_to_names(universe_params),
                universe_constraints: self.signature_universe_constraints(&decl.decl)?,
                ty: self.inductive_type(params, indices, *sort),
                value: None,
            },
            DeclPayload::MutualInductiveBlock { .. } => unreachable!(
                "mutual inductive blocks are exported through generated family entries"
            ),
        })
    }

    fn signature_universe_constraints(
        &self,
        decl: &DeclPayload,
    ) -> DecodeResult<Vec<ReferenceUniverseConstraint>> {
        self.universe_constraints_from_specs(decl_universe_constraints(decl))
    }

    fn universe_constraints_from_specs(
        &self,
        constraints: &[UniverseConstraintSpec],
    ) -> DecodeResult<Vec<ReferenceUniverseConstraint>> {
        constraints
            .iter()
            .map(|constraint| {
                Ok(ReferenceUniverseConstraint {
                    lhs: self.levels.get(constraint.lhs).cloned().ok_or_else(|| {
                        ReferenceCheckError::malformed(
                            ReferenceCertificateSection::Declarations,
                            0,
                            ReferenceCheckReason::DanglingReference,
                        )
                    })?,
                    relation: constraint.relation,
                    rhs: self.levels.get(constraint.rhs).cloned().ok_or_else(|| {
                        ReferenceCheckError::malformed(
                            ReferenceCertificateSection::Declarations,
                            0,
                            ReferenceCheckReason::DanglingReference,
                        )
                    })?,
                })
            })
            .collect()
    }

    fn universe_context_from_specs(
        &self,
        params: Vec<ReferenceModuleName>,
        constraints: &[UniverseConstraintSpec],
        offset: usize,
    ) -> DecodeResult<ReferenceUniverseContext> {
        ReferenceUniverseContext::new(
            params,
            self.universe_constraints_from_specs(constraints)?,
            offset,
        )
    }

    fn declaration_universe_context(
        &self,
        decl: &DeclPayload,
        offset: usize,
    ) -> DecodeResult<ReferenceUniverseContext> {
        ReferenceUniverseContext::new(
            self.declaration_universe_params(decl),
            self.signature_universe_constraints(decl)?,
            offset,
        )
    }

    fn recursor_universe_context(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        offset: usize,
    ) -> DecodeResult<ReferenceUniverseContext> {
        self.universe_context_from_specs(
            recursor.universe_params.clone(),
            &data.universe_constraints,
            offset,
        )
    }

    fn imported_recursors(
        &self,
        offset: usize,
    ) -> DecodeResult<BTreeMap<ImportedRecursorKey, ReferenceImportedRecursorRuntime>> {
        let mut recursors = BTreeMap::new();
        for (import_index, import) in self.imports.imports().iter().enumerate() {
            let groups = imported_inductive_export_groups(import.public_environment.exports());
            for group in groups.values() {
                let Some((key, runtime)) = self.imported_single_recursor_runtime(
                    import_index,
                    &import.public_environment,
                    group,
                    offset,
                )?
                else {
                    continue;
                };
                recursors.insert(key, runtime);
            }
        }
        Ok(recursors)
    }

    fn imported_single_recursor_runtime(
        &self,
        import_index: usize,
        environment: &ReferencePublicEnvironment,
        group: &ImportedInductiveExportGroup<'_>,
        offset: usize,
    ) -> DecodeResult<Option<(ImportedRecursorKey, ReferenceImportedRecursorRuntime)>> {
        let [inductive] = group.inductives.as_slice() else {
            return Ok(None);
        };
        let [recursor_export] = group.recursors.as_slice() else {
            return Ok(None);
        };

        let family_ty =
            self.instantiate_public_expr(import_index, environment, &inductive.ty, offset)?;
        let (family_domains, family_result) = peel_pi_domains(&family_ty);
        let ReferenceCoreExpr::Sort(sort) = family_result else {
            return Ok(None);
        };
        let recursor_ty =
            self.instantiate_public_expr(import_index, environment, &recursor_export.ty, offset)?;
        let (recursor_domains, recursor_result) = peel_pi_domains(&recursor_ty);
        let constructor_count = group.constructors.len();
        if recursor_domains.len() != family_domains.len() + constructor_count + 2 {
            return Ok(None);
        }

        let constructors = group
            .constructors
            .iter()
            .map(|constructor| {
                Ok(ReferenceConstructorSignature {
                    name: constructor.name.clone(),
                    ty: self.instantiate_public_expr(
                        import_index,
                        environment,
                        &constructor.ty,
                        offset,
                    )?,
                })
            })
            .collect::<DecodeResult<Vec<_>>>()?;

        for param_count in 0..=family_domains.len() {
            let index_count = family_domains.len() - param_count;
            let rules = RecursorRulesSpec {
                minor_start: param_count + 1,
                major_index: param_count + 1 + constructor_count + index_count,
            };
            let recursor = ReferenceRecursorSignature {
                name: recursor_export.name.clone(),
                universe_params: recursor_export.universe_params.clone(),
                ty: recursor_ty.clone(),
                rules,
            };
            let mut data = ReferenceInductiveSignature {
                decl_index: usize::MAX,
                global_ref: ReferenceCoreGlobalRef::Imported {
                    import_index,
                    name: inductive.name.clone(),
                    decl_interface_hash: inductive.decl_interface_hash,
                },
                universe_params: inductive.universe_params.clone(),
                universe_constraints: Vec::new(),
                params: family_domains[..param_count].to_vec(),
                indices: family_domains[param_count..].to_vec(),
                sort: sort.clone(),
                constructors: constructors.clone(),
                recursor: None,
            };

            if !self.imported_recursor_shape_matches(
                &data,
                &recursor,
                &recursor_domains,
                &recursor_result,
                offset,
            )? {
                continue;
            }
            let Some(ordered_constructors) = self.order_imported_constructors(
                &data,
                &recursor,
                &recursor_domains,
                &constructors,
                offset,
            )?
            else {
                continue;
            };
            data.constructors = ordered_constructors;
            data.recursor = Some(recursor.clone());

            let expected_ty = expected_recursor_type(&data, &recursor, offset)?;
            if recursor.ty != expected_ty {
                continue;
            }

            let key = ImportedRecursorKey {
                import_index,
                name: recursor_export.name.clone(),
                decl_interface_hash: recursor_export.decl_interface_hash,
            };
            return Ok(Some((
                key,
                ReferenceImportedRecursorRuntime { data, recursor },
            )));
        }

        Ok(None)
    }

    fn imported_recursor_shape_matches(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        result: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<bool> {
        if recursor.rules.major_index + 1 != domains.len() {
            return Ok(false);
        }
        let ok = self.imported_recursor_shape_result(data, recursor, domains, result, offset);
        match ok {
            Ok(()) => Ok(true),
            Err(error) if error.kind == ReferenceCheckErrorKind::TypeCheck => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn imported_recursor_shape_result(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        result: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let universe_context =
            ReferenceUniverseContext::from_params(recursor.universe_params.clone(), offset)?;
        self.check_recursor_params(data, &universe_context, domains, offset)?;
        let motive_domain = domains.get(data.params.len()).ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMotive,
            )
        })?;
        self.check_motive_domain(data, recursor, motive_domain, offset)?;
        self.check_recursor_indices(data, recursor, domains, offset)?;
        self.check_recursor_target(
            data,
            &domains[recursor.rules.major_index],
            ReferenceCheckReason::BadRecursorMajor,
            recursor.rules.major_index,
            recursor.rules.minor_start + data.constructors.len(),
            offset,
        )?;
        self.check_recursor_result(data, recursor, domains, result, offset)
    }

    fn order_imported_constructors(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        constructors: &[ReferenceConstructorSignature],
        offset: usize,
    ) -> DecodeResult<Option<Vec<ReferenceConstructorSignature>>> {
        let mut remaining = constructors.to_vec();
        let mut ordered = Vec::with_capacity(constructors.len());
        if self.order_imported_constructors_from(
            data,
            recursor,
            domains,
            offset,
            &mut remaining,
            &mut ordered,
        )? {
            Ok(Some(ordered))
        } else {
            Ok(None)
        }
    }

    fn order_imported_constructors_from(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        offset: usize,
        remaining: &mut Vec<ReferenceConstructorSignature>,
        ordered: &mut Vec<ReferenceConstructorSignature>,
    ) -> DecodeResult<bool> {
        if remaining.is_empty() {
            return Ok(true);
        }

        let constructor_index = ordered.len();
        let minor_index = recursor.rules.minor_start + constructor_index;
        let Some(actual_minor) = domains.get(minor_index) else {
            return Ok(false);
        };
        let prefix_ctx = recursor_prefix_ctx(&domains[..minor_index]);
        for index in 0..remaining.len() {
            let constructor = remaining.remove(index);
            let expected_minor =
                expected_minor_type(data, &constructor, constructor_index, offset)?;
            let matches = self.is_defeq(
                &prefix_ctx,
                &recursor.universe_params,
                actual_minor,
                &expected_minor,
                offset,
            )?;
            if matches {
                ordered.push(constructor.clone());
                if self.order_imported_constructors_from(
                    data, recursor, domains, offset, remaining, ordered,
                )? {
                    return Ok(true);
                }
                ordered.pop();
            }
            remaining.insert(index, constructor);
        }
        Ok(false)
    }

    fn check_inductive_decl(&mut self, decl: &DeclCert, offset: usize) -> DecodeResult<()> {
        let (universe_params, params, indices, sort, constructors) = match &decl.decl {
            DeclPayload::Inductive {
                universe_params,
                params,
                indices,
                sort,
                constructors,
                ..
            }
            | DeclPayload::InductiveConstrained {
                universe_params,
                params,
                indices,
                sort,
                constructors,
                ..
            } => (universe_params, params, indices, *sort, constructors),
            _ => return Err(ReferenceCheckError::unsupported(offset)),
        };

        let decl_index = self.locals.len();
        let universe_params = self.cert.name_ids_to_names(universe_params);
        ensure_unique_names(&universe_params, offset)?;
        let universe_context = self.universe_context_from_specs(
            universe_params.clone(),
            decl_universe_constraints(&decl.decl),
            offset,
        )?;
        ensure_level_wf(&self.levels[sort], &universe_context.params, offset)?;

        let family_ty = self.inductive_type(params, indices, sort);
        self.expect_sort(
            &TypeContext::default(),
            &universe_context,
            &family_ty,
            offset,
        )?;

        let data = self.inductive_signature(decl_index, universe_params.clone(), &decl.decl);

        self.locals.push(Arc::new(TypeSignature {
            universe_params: universe_params.clone(),
            universe_constraints: self
                .universe_constraints_from_specs(&data.universe_constraints)?,
            ty: family_ty,
            value: None,
        }));
        self.inductives.insert(decl_index, data.clone());

        for (constructor_index, constructor) in constructors.iter().enumerate() {
            self.check_constructor_decl(
                &data,
                &universe_context,
                constructor_index,
                constructor,
                offset,
            )?;
        }

        for constructor in &data.constructors {
            self.generated.insert(
                GeneratedKey::new(decl_index, constructor.name.clone()),
                Arc::new(TypeSignature {
                    universe_params: data.universe_params.clone(),
                    universe_constraints: self
                        .universe_constraints_from_specs(&data.universe_constraints)?,
                    ty: constructor.ty.clone(),
                    value: None,
                }),
            );
        }

        if let Some(recursor) = &data.recursor {
            ensure_unique_names(&recursor.universe_params, offset)?;
            let recursor_universe_context =
                self.recursor_universe_context(&data, recursor, offset)?;
            self.expect_sort(
                &TypeContext::default(),
                &recursor_universe_context,
                &recursor.ty,
                offset,
            )?;
            self.check_recursor_decl(&data, &recursor_universe_context, recursor, offset)?;
            let key = GeneratedKey::new(decl_index, recursor.name.clone());
            self.generated.insert(
                key.clone(),
                Arc::new(TypeSignature {
                    universe_params: recursor.universe_params.clone(),
                    universe_constraints: self
                        .universe_constraints_from_specs(&data.universe_constraints)?,
                    ty: recursor.ty.clone(),
                    value: None,
                }),
            );
            self.recursors.insert(
                key,
                ReferenceRecursorRuntime {
                    inductive_decl_index: decl_index,
                    target_key: None,
                    target_constructor_offset: 0,
                    family_recursors: BTreeMap::new(),
                    rules: recursor.rules,
                },
            );
        }

        Ok(())
    }

    fn check_mutual_inductive_decl(&mut self, decl: &DeclCert, offset: usize) -> DecodeResult<()> {
        let DeclPayload::MutualInductiveBlock {
            universe_params,
            universe_constraints,
            inductives,
            ..
        } = &decl.decl
        else {
            return Err(ReferenceCheckError::unsupported(offset));
        };
        if inductives.is_empty() {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadConstructorResult,
            ));
        }

        let decl_index = self.locals.len();
        let universe_params = self.cert.name_ids_to_names(universe_params);
        ensure_unique_names(&universe_params, offset)?;
        let universe_context = self.universe_context_from_specs(
            universe_params.clone(),
            universe_constraints,
            offset,
        )?;
        let shared_params = inductives[0].params.clone();
        let mut generated_names = BTreeSet::new();
        generated_names.insert(decl.decl.name_id());
        for inductive in inductives {
            if inductive.params != shared_params {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadConstructorResult,
                ));
            }
            if !generated_names.insert(inductive.name) {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::DuplicateDeclarationName,
                ));
            }
            for constructor in &inductive.constructors {
                if !generated_names.insert(constructor.name) {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::DuplicateDeclarationName,
                    ));
                }
            }
            if let Some(recursor) = &inductive.recursor {
                if !generated_names.insert(recursor.name) {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::DuplicateDeclarationName,
                    ));
                }
            }
        }

        self.locals.push(Arc::new(TypeSignature {
            universe_params: universe_params.clone(),
            universe_constraints: Vec::new(),
            ty: ReferenceCoreExpr::Sort(ReferenceCoreLevel::Zero),
            value: None,
        }));

        let mut signatures = Vec::with_capacity(inductives.len());
        for inductive in inductives {
            ensure_level_wf(
                &self.levels[inductive.sort],
                &universe_context.params,
                offset,
            )?;
            let family_ty =
                self.inductive_type(&inductive.params, &inductive.indices, inductive.sort);
            self.expect_sort(
                &TypeContext::default(),
                &universe_context,
                &family_ty,
                offset,
            )?;
            let data = self.mutual_inductive_signature(
                decl_index,
                universe_params.clone(),
                universe_constraints,
                inductive,
            );
            let key = GeneratedKey::new(decl_index, data.generated_family_name());
            self.generated.insert(
                key.clone(),
                Arc::new(TypeSignature {
                    universe_params: universe_params.clone(),
                    universe_constraints: self
                        .universe_constraints_from_specs(&data.universe_constraints)?,
                    ty: family_ty,
                    value: None,
                }),
            );
            self.mutual_inductives.insert(key, data.clone());
            signatures.push(data);
        }

        for data in &signatures {
            for (constructor_index, constructor) in data.constructors.iter().enumerate() {
                self.check_mutual_constructor_decl(
                    &signatures,
                    data,
                    &universe_context,
                    constructor_index,
                    constructor,
                    offset,
                )?;
            }
        }

        for data in &signatures {
            for constructor in &data.constructors {
                self.generated.insert(
                    GeneratedKey::new(decl_index, constructor.name.clone()),
                    Arc::new(TypeSignature {
                        universe_params: data.universe_params.clone(),
                        universe_constraints: self
                            .universe_constraints_from_specs(&data.universe_constraints)?,
                        ty: constructor.ty.clone(),
                        value: None,
                    }),
                );
            }
        }

        let mut family_recursors = BTreeMap::new();
        for data in &signatures {
            if let Some(recursor) = &data.recursor {
                family_recursors.insert(
                    GeneratedKey::new(decl_index, data.generated_family_name()),
                    recursor.name.clone(),
                );
            }
        }
        for (target_index, data) in signatures.iter().enumerate() {
            if let Some(recursor) = &data.recursor {
                let target_constructor_offset = signatures[..target_index]
                    .iter()
                    .map(|signature| signature.constructors.len())
                    .sum();
                ensure_unique_names(&recursor.universe_params, offset)?;
                let recursor_universe_context =
                    self.recursor_universe_context(data, recursor, offset)?;
                self.expect_sort(
                    &TypeContext::default(),
                    &recursor_universe_context,
                    &recursor.ty,
                    offset,
                )?;
                self.check_mutual_recursor_decl(
                    &signatures,
                    target_index,
                    &recursor_universe_context,
                    recursor,
                    offset,
                )?;
                let key = GeneratedKey::new(decl_index, recursor.name.clone());
                self.generated.insert(
                    key.clone(),
                    Arc::new(TypeSignature {
                        universe_params: recursor.universe_params.clone(),
                        universe_constraints: self
                            .universe_constraints_from_specs(&data.universe_constraints)?,
                        ty: recursor.ty.clone(),
                        value: None,
                    }),
                );
                self.recursors.insert(
                    key,
                    ReferenceRecursorRuntime {
                        inductive_decl_index: decl_index,
                        target_key: Some(GeneratedKey::new(
                            decl_index,
                            data.generated_family_name(),
                        )),
                        target_constructor_offset,
                        family_recursors: family_recursors.clone(),
                        rules: recursor.rules,
                    },
                );
            } else {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorRule,
                ));
            }
        }
        Ok(())
    }

    fn mutual_inductive_signature(
        &self,
        decl_index: usize,
        universe_params: Vec<ReferenceModuleName>,
        universe_constraints: &[UniverseConstraintSpec],
        inductive: &MutualInductiveSpec,
    ) -> ReferenceInductiveSignature {
        let name = self.cert.name_table[inductive.name].value.clone();
        ReferenceInductiveSignature {
            decl_index,
            global_ref: ReferenceCoreGlobalRef::LocalGenerated { decl_index, name },
            universe_params,
            universe_constraints: universe_constraints.to_vec(),
            params: inductive
                .params
                .iter()
                .map(|binder| self.terms[binder.ty].clone())
                .collect(),
            indices: inductive
                .indices
                .iter()
                .map(|binder| self.terms[binder.ty].clone())
                .collect(),
            sort: self.levels[inductive.sort].clone(),
            constructors: inductive
                .constructors
                .iter()
                .map(|constructor| ReferenceConstructorSignature {
                    name: self.cert.name_table[constructor.name].value.clone(),
                    ty: self.terms[constructor.ty].clone(),
                })
                .collect(),
            recursor: inductive
                .recursor
                .as_ref()
                .map(|recursor| ReferenceRecursorSignature {
                    name: self.cert.name_table[recursor.name].value.clone(),
                    universe_params: self.cert.name_ids_to_names(&recursor.universe_params),
                    ty: self.terms[recursor.ty].clone(),
                    rules: recursor.rules,
                }),
        }
    }

    fn inductive_signature(
        &self,
        decl_index: usize,
        universe_params: Vec<ReferenceModuleName>,
        decl: &DeclPayload,
    ) -> ReferenceInductiveSignature {
        let (universe_constraints, params, indices, sort, constructors, recursor) = match decl {
            DeclPayload::Inductive {
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            } => (&[][..], params, indices, *sort, constructors, recursor),
            DeclPayload::InductiveConstrained {
                universe_constraints,
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            } => (
                universe_constraints.as_slice(),
                params,
                indices,
                *sort,
                constructors,
                recursor,
            ),
            _ => unreachable!("inductive_signature is only called for inductive declarations"),
        };
        ReferenceInductiveSignature {
            decl_index,
            global_ref: ReferenceCoreGlobalRef::Local { decl_index },
            universe_params,
            universe_constraints: universe_constraints.to_vec(),
            params: params
                .iter()
                .map(|binder| self.terms[binder.ty].clone())
                .collect(),
            indices: indices
                .iter()
                .map(|binder| self.terms[binder.ty].clone())
                .collect(),
            sort: self.levels[sort].clone(),
            constructors: constructors
                .iter()
                .map(|constructor| ReferenceConstructorSignature {
                    name: self.cert.name_table[constructor.name].value.clone(),
                    ty: self.terms[constructor.ty].clone(),
                })
                .collect(),
            recursor: recursor
                .as_ref()
                .map(|recursor| ReferenceRecursorSignature {
                    name: self.cert.name_table[recursor.name].value.clone(),
                    universe_params: self.cert.name_ids_to_names(&recursor.universe_params),
                    ty: self.terms[recursor.ty].clone(),
                    rules: recursor.rules,
                }),
        }
    }

    fn inductive_type(
        &self,
        params: &[BinderType],
        indices: &[BinderType],
        sort: usize,
    ) -> ReferenceCoreExpr {
        let body = ReferenceCoreExpr::Sort(self.levels[sort].clone());
        params
            .iter()
            .chain(indices)
            .rev()
            .fold(body, |body, binder| ReferenceCoreExpr::Pi {
                ty: Arc::new(self.terms[binder.ty].clone()),
                body: Arc::new(body),
            })
    }

    fn check_constructor_decl(
        &self,
        data: &ReferenceInductiveSignature,
        universe_context: &ReferenceUniverseContext,
        constructor_index: usize,
        constructor: &ConstructorSpec,
        offset: usize,
    ) -> DecodeResult<()> {
        let constructor_sig = &data.constructors[constructor_index];
        let ty = &self.terms[constructor.ty];
        self.expect_sort(&TypeContext::default(), universe_context, ty, offset)?;
        let (domains, result) = peel_pi_domains(ty);
        for (domain_index, domain) in domains.iter().enumerate() {
            self.check_constructor_domain_positive(
                data,
                constructor_sig,
                domain_index,
                domain,
                offset,
            )?;
        }
        let result = self.whnf(
            &TypeContext::default(),
            &universe_context.params,
            &result,
            offset,
        )?;
        self.check_constructor_result(data, constructor_sig, domains.len(), result, offset)
    }

    fn check_mutual_constructor_decl(
        &self,
        block: &[ReferenceInductiveSignature],
        data: &ReferenceInductiveSignature,
        universe_context: &ReferenceUniverseContext,
        _constructor_index: usize,
        constructor: &ReferenceConstructorSignature,
        offset: usize,
    ) -> DecodeResult<()> {
        let ty = &constructor.ty;
        self.expect_sort(&TypeContext::default(), universe_context, ty, offset)?;
        let (domains, result) = peel_pi_domains(ty);
        for (domain_index, domain) in domains.iter().enumerate() {
            let allowed = domain_index >= data.params.len()
                && mutual_recursive_occurrences_strictly_positive(
                    self.cert,
                    &self.inductives,
                    block,
                    domain,
                    domain_index,
                    offset,
                )?;
            if !allowed && contains_any_inductive_const(domain, block) {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::NonPositiveOccurrence,
                ));
            }
        }
        let result = self.whnf(
            &TypeContext::default(),
            &universe_context.params,
            &result,
            offset,
        )?;
        self.check_constructor_result(data, constructor, domains.len(), result, offset)
    }

    fn check_constructor_domain_positive(
        &self,
        data: &ReferenceInductiveSignature,
        constructor: &ReferenceConstructorSignature,
        domain_index: usize,
        domain: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let allowed = domain_index >= data.params.len()
            && recursive_occurrences_strictly_positive(
                self.cert,
                &self.inductives,
                data,
                domain,
                domain_index,
                offset,
            )?;
        if !allowed && contains_inductive_const(domain, data) {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::NonPositiveOccurrence,
            ));
        }
        let _ = constructor;
        Ok(())
    }

    fn check_constructor_result(
        &self,
        data: &ReferenceInductiveSignature,
        constructor: &ReferenceConstructorSignature,
        domain_count: usize,
        result: ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let (head, args) = collect_apps(&result);
        let levels = match head {
            ReferenceCoreExpr::Const { global_ref, levels } if global_ref == &data.global_ref => {
                levels
            }
            _ => {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadConstructorResult,
                ));
            }
        };

        let expected_levels: Vec<_> = data
            .universe_params
            .iter()
            .map(|param| ReferenceCoreLevel::Param(param.clone()))
            .collect();
        if *levels != expected_levels
            || args.len() != data.params.len() + data.indices.len()
            || domain_count < data.params.len()
        {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadConstructorResult,
            ));
        }

        for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
            let expected = bvar_for_abs(domain_count, param_index, offset)?;
            if arg != &expected {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadConstructorResult,
                ));
            }
        }

        let _ = constructor;
        Ok(())
    }

    fn check_recursor_decl(
        &self,
        data: &ReferenceInductiveSignature,
        universe_context: &ReferenceUniverseContext,
        recursor: &ReferenceRecursorSignature,
        offset: usize,
    ) -> DecodeResult<()> {
        if recursor.rules.minor_start != data.params.len() + 1 {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }
        if recursor.rules.major_index
            != recursor.rules.minor_start + data.constructors.len() + data.indices.len()
        {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }

        let (domains, result) = peel_pi_domains(&recursor.ty);
        if domains.len() <= recursor.rules.major_index
            || domains.len() != recursor.rules.major_index + 1
        {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }

        self.check_recursor_params(data, universe_context, &domains, offset)?;

        let motive_domain = domains.get(data.params.len()).ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMotive,
            )
        })?;
        self.check_motive_domain(data, recursor, motive_domain, offset)?;

        self.check_recursor_indices(data, recursor, &domains, offset)?;

        let major_domain = &domains[recursor.rules.major_index];
        self.check_recursor_target(
            data,
            major_domain,
            ReferenceCheckReason::BadRecursorMajor,
            recursor.rules.major_index,
            recursor.rules.minor_start + data.constructors.len(),
            offset,
        )?;
        self.check_recursor_result(data, recursor, &domains, &result, offset)?;

        for (constructor_index, constructor) in data.constructors.iter().enumerate() {
            let minor_index = recursor.rules.minor_start + constructor_index;
            let minor_domain = &domains[minor_index];
            let expected_minor = expected_minor_type(data, constructor, constructor_index, offset)?;
            let prefix_ctx = recursor_prefix_ctx(&domains[..minor_index]);
            if !self.is_defeq(
                &prefix_ctx,
                &universe_context.params,
                minor_domain,
                &expected_minor,
                offset,
            )? {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorMinor,
                ));
            }
        }

        let expected_ty = expected_recursor_type(data, recursor, offset)?;
        if recursor.ty != expected_ty {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorType,
            ));
        }

        Ok(())
    }

    fn check_mutual_recursor_decl(
        &self,
        block: &[ReferenceInductiveSignature],
        target_index: usize,
        universe_context: &ReferenceUniverseContext,
        recursor: &ReferenceRecursorSignature,
        offset: usize,
    ) -> DecodeResult<()> {
        let target = block.get(target_index).ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            )
        })?;
        let total_constructors = mutual_constructor_count(block);
        let expected_minor_start = target.params.len() + block.len();
        if recursor.rules.minor_start != expected_minor_start
            || recursor.rules.major_index
                != expected_minor_start + total_constructors + target.indices.len()
        {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }
        let (domains, result) = peel_pi_domains(&recursor.ty);
        if domains.len() <= recursor.rules.major_index
            || domains.len() != recursor.rules.major_index + 1
        {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }

        self.check_recursor_params(target, universe_context, &domains, offset)?;
        for (family_index, family) in block.iter().enumerate() {
            let motive_domain =
                domains
                    .get(target.params.len() + family_index)
                    .ok_or_else(|| {
                        ReferenceCheckError::type_check(
                            ReferenceCertificateSection::Declarations,
                            offset,
                            ReferenceCheckReason::BadRecursorMotive,
                        )
                    })?;
            self.check_motive_domain(family, recursor, motive_domain, offset)?;
        }

        let index_start = recursor.rules.minor_start + total_constructors;
        self.check_recursor_indices_at(target, recursor, &domains, index_start, offset)?;
        self.check_recursor_target(
            target,
            &domains[recursor.rules.major_index],
            ReferenceCheckReason::BadRecursorMajor,
            recursor.rules.major_index,
            index_start,
            offset,
        )?;
        self.check_mutual_recursor_result(MutualRecursorResultCheck {
            target,
            target_index,
            recursor,
            domains: &domains,
            result: &result,
            index_start,
            offset,
        })?;

        let mut constructor_index = 0usize;
        for (family_index, family) in block.iter().enumerate() {
            for constructor in &family.constructors {
                let minor_index = recursor.rules.minor_start + constructor_index;
                let minor_domain = &domains[minor_index];
                let expected_minor = expected_mutual_minor_type(
                    block,
                    family_index,
                    constructor,
                    constructor_index,
                    offset,
                )?;
                let prefix_ctx = recursor_prefix_ctx(&domains[..minor_index]);
                if !self.is_defeq(
                    &prefix_ctx,
                    &universe_context.params,
                    minor_domain,
                    &expected_minor,
                    offset,
                )? {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::BadRecursorMinor,
                    ));
                }
                constructor_index += 1;
            }
        }

        let expected_ty = expected_mutual_recursor_type(block, target_index, recursor, offset)?;
        if recursor.ty != expected_ty {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorType,
            ));
        }
        Ok(())
    }

    fn check_recursor_params(
        &self,
        data: &ReferenceInductiveSignature,
        universe_context: &ReferenceUniverseContext,
        domains: &[ReferenceCoreExpr],
        offset: usize,
    ) -> DecodeResult<()> {
        if domains.len() < data.params.len() {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorRule,
            ));
        }

        let mut ctx = TypeContext::default();
        for (param_index, param_ty) in data.params.iter().enumerate() {
            self.expect_sort(&ctx, universe_context, param_ty, offset)?;
            if !self.is_defeq(
                &ctx,
                &universe_context.params,
                &domains[param_index],
                param_ty,
                offset,
            )? {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorParam,
                ));
            }
            ctx.push_assumption(param_ty.clone());
        }

        Ok(())
    }

    fn check_motive_domain(
        &self,
        data: &ReferenceInductiveSignature,
        _recursor: &ReferenceRecursorSignature,
        motive_domain: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let (motive_domains, motive_result) = peel_pi_domains(motive_domain);
        if motive_domains.len() != data.indices.len() + 1 {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMotive,
            ));
        }
        let mut source_to_target = (0..data.params.len()).collect::<Vec<_>>();
        for (index, expected) in data.indices.iter().enumerate() {
            let source_ctx_len = data.params.len() + index;
            let target_ctx_len = data.params.len() + index;
            let expected_ty = remap_bvars(
                expected,
                source_ctx_len,
                target_ctx_len,
                &source_to_target,
                offset,
            )?;
            if motive_domains[index] != expected_ty {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorMotive,
                ));
            }
            source_to_target.push(target_ctx_len);
        }
        self.check_recursor_target(
            data,
            &motive_domains[data.indices.len()],
            ReferenceCheckReason::BadRecursorMotive,
            data.params.len() + data.indices.len(),
            data.params.len(),
            offset,
        )?;
        match motive_result {
            ReferenceCoreExpr::Sort(level) => {
                if data.sort == ReferenceCoreLevel::Zero && level != ReferenceCoreLevel::Zero {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::BadRecursorMotive,
                    ));
                }
            }
            _ => {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorMotive,
                ));
            }
        }
        Ok(())
    }

    fn check_recursor_indices(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        offset: usize,
    ) -> DecodeResult<()> {
        let index_start = recursor.rules.minor_start + data.constructors.len();
        self.check_recursor_indices_at(data, recursor, domains, index_start, offset)
    }

    fn check_recursor_indices_at(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        index_start: usize,
        offset: usize,
    ) -> DecodeResult<()> {
        let mut source_to_target = (0..data.params.len()).collect::<Vec<_>>();
        for (index, expected) in data.indices.iter().enumerate() {
            let domain_index = index_start + index;
            let actual = domains.get(domain_index).ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorRule,
                )
            })?;
            let source_ctx_len = data.params.len() + index;
            let target_ctx_len = domain_index;
            let expected_ty = remap_bvars(
                expected,
                source_ctx_len,
                target_ctx_len,
                &source_to_target,
                offset,
            )?;
            let ctx = recursor_prefix_ctx(&domains[..domain_index]);
            if !self.is_defeq(
                &ctx,
                &recursor.universe_params,
                actual,
                &expected_ty,
                offset,
            )? {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::BadRecursorParam,
                ));
            }
            source_to_target.push(domain_index);
        }
        Ok(())
    }

    fn check_recursor_target(
        &self,
        data: &ReferenceInductiveSignature,
        target: &ReferenceCoreExpr,
        reason: ReferenceCheckReason,
        ctx_len: usize,
        index_abs_start: usize,
        offset: usize,
    ) -> DecodeResult<()> {
        let (head, args) = collect_apps(target);
        let levels = match head {
            ReferenceCoreExpr::Const {
                global_ref, levels, ..
            } if global_ref == &data.global_ref => levels,
            _ => {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    reason,
                ));
            }
        };
        let expected_levels: Vec<_> = data
            .universe_params
            .iter()
            .map(|param| ReferenceCoreLevel::Param(param.clone()))
            .collect();
        if *levels != expected_levels || args.len() != data.params.len() + data.indices.len() {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                reason,
            ));
        }
        for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
            if arg != &bvar_for_abs(ctx_len, param_index, offset)? {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    reason,
                ));
            }
        }
        for (index_index, arg) in args.iter().skip(data.params.len()).enumerate() {
            if arg != &bvar_for_abs(ctx_len, index_abs_start + index_index, offset)? {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    reason,
                ));
            }
        }
        Ok(())
    }

    fn check_recursor_result(
        &self,
        data: &ReferenceInductiveSignature,
        recursor: &ReferenceRecursorSignature,
        domains: &[ReferenceCoreExpr],
        result: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let index_start = recursor.rules.minor_start + data.constructors.len();
        let index_args = (0..data.indices.len())
            .map(|index| bvar_for_abs(domains.len(), index_start + index, offset))
            .collect::<DecodeResult<Vec<_>>>()?;
        let expected = motive_app(
            domains.len(),
            data.params.len(),
            index_args,
            bvar_for_abs(domains.len(), recursor.rules.major_index, offset)?,
            offset,
        )?;
        let result_ctx = recursor_prefix_ctx(domains);
        if self.is_defeq(
            &result_ctx,
            &recursor.universe_params,
            result,
            &expected,
            offset,
        )? {
            Ok(())
        } else {
            Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorResult,
            ))
        }
    }

    fn check_mutual_recursor_result(
        &self,
        check: MutualRecursorResultCheck<'_>,
    ) -> DecodeResult<()> {
        let index_args = (0..check.target.indices.len())
            .map(|index| bvar_for_abs(check.domains.len(), check.index_start + index, check.offset))
            .collect::<DecodeResult<Vec<_>>>()?;
        let expected = motive_app(
            check.domains.len(),
            check.target.params.len() + check.target_index,
            index_args,
            bvar_for_abs(
                check.domains.len(),
                check.recursor.rules.major_index,
                check.offset,
            )?,
            check.offset,
        )?;
        let result_ctx = recursor_prefix_ctx(check.domains);
        if self.is_defeq(
            &result_ctx,
            &check.recursor.universe_params,
            check.result,
            &expected,
            check.offset,
        )? {
            Ok(())
        } else {
            Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                check.offset,
                ReferenceCheckReason::BadRecursorResult,
            ))
        }
    }

    fn infer(
        &self,
        ctx: &TypeContext,
        universe_context: &ReferenceUniverseContext,
        term: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<ReferenceCoreExpr> {
        let delta = &universe_context.params;
        match term {
            ReferenceCoreExpr::Sort(level) => {
                ensure_level_wf(level, delta, offset)?;
                Ok(ReferenceCoreExpr::Sort(ReferenceCoreLevel::Succ(Arc::new(
                    level.clone(),
                ))))
            }
            ReferenceCoreExpr::BVar(index) => ctx.lookup_type(*index, offset),
            ReferenceCoreExpr::Const { global_ref, levels } => {
                for level in levels {
                    ensure_level_wf(level, delta, offset)?;
                }
                let signature = self.resolve_signature(global_ref, offset)?;
                if signature.universe_params.len() != levels.len() {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::BadUniverseArity,
                    ));
                }
                enforce_signature_universe_constraints(
                    universe_context,
                    &signature,
                    levels,
                    offset,
                )?;
                Ok(subst_levels_expr(
                    &signature.ty,
                    &signature.universe_params,
                    levels,
                ))
            }
            ReferenceCoreExpr::Pi { ty, body } => {
                let domain_sort = self.expect_sort(ctx, universe_context, ty, offset)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption((**ty).clone());
                let body_sort = self.expect_sort(&body_ctx, universe_context, body, offset)?;
                Ok(ReferenceCoreExpr::Sort(ReferenceCoreLevel::IMax(
                    Arc::new(domain_sort),
                    Arc::new(body_sort),
                )))
            }
            ReferenceCoreExpr::Lam { ty, body } => {
                self.expect_sort(ctx, universe_context, ty, offset)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption((**ty).clone());
                let body_ty = self.infer(&body_ctx, universe_context, body, offset)?;
                Ok(ReferenceCoreExpr::Pi {
                    ty: ty.clone(),
                    body: Arc::new(body_ty),
                })
            }
            ReferenceCoreExpr::App(fun, arg) => {
                let fun_ty = self.infer(ctx, universe_context, fun, offset)?;
                match self.whnf(ctx, delta, &fun_ty, offset)? {
                    ReferenceCoreExpr::Pi { ty, body } => {
                        self.check(ctx, universe_context, arg, &ty, offset)?;
                        instantiate(&body, arg, offset)
                    }
                    _ => Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::ExpectedFunction,
                    )),
                }
            }
            ReferenceCoreExpr::Let { ty, value, body } => {
                self.expect_sort(ctx, universe_context, ty, offset)?;
                self.check(ctx, universe_context, value, ty, offset)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition((**ty).clone(), (**value).clone());
                let body_ty = self.infer(&body_ctx, universe_context, body, offset)?;
                instantiate(&body_ty, value, offset)
            }
        }
    }

    fn check(
        &self,
        ctx: &TypeContext,
        universe_context: &ReferenceUniverseContext,
        term: &ReferenceCoreExpr,
        expected: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<()> {
        let actual = self.infer(ctx, universe_context, term, offset)?;
        if self.is_defeq(ctx, &universe_context.params, &actual, expected, offset)? {
            Ok(())
        } else {
            Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::TypeMismatch,
            ))
        }
    }

    fn expect_sort(
        &self,
        ctx: &TypeContext,
        universe_context: &ReferenceUniverseContext,
        term: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<ReferenceCoreLevel> {
        let ty = self.infer(ctx, universe_context, term, offset)?;
        match self.whnf(ctx, &universe_context.params, &ty, offset)? {
            ReferenceCoreExpr::Sort(level) => Ok(level),
            _ => Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::ExpectedSort,
            )),
        }
    }

    fn resolve_signature(
        &self,
        global_ref: &ReferenceCoreGlobalRef,
        offset: usize,
    ) -> DecodeResult<Arc<TypeSignature>> {
        match global_ref {
            ReferenceCoreGlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                if let Some(signature) = self.builtin_signatures.borrow().get(name) {
                    return Ok(Arc::clone(signature));
                }
                let signature = reference_builtin_signature(name, *decl_interface_hash)
                    .map(Arc::new)
                    .ok_or_else(|| {
                        ReferenceCheckError::type_check(
                            ReferenceCertificateSection::Declarations,
                            offset,
                            ReferenceCheckReason::UnknownReference,
                        )
                    })?;
                self.builtin_signatures
                    .borrow_mut()
                    .insert(name.clone(), Arc::clone(&signature));
                Ok(signature)
            }
            ReferenceCoreGlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let cache_key = (*import_index, name.clone(), *decl_interface_hash);
                if let Some(signature) = self.imported_signatures.borrow().get(&cache_key) {
                    return Ok(Arc::clone(signature));
                }
                let import = self.imports.imports().get(*import_index).ok_or_else(|| {
                    ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UnknownReference,
                    )
                })?;
                let export = import
                    .public_environment
                    .exports()
                    .iter()
                    .find(|export| {
                        export.name == *name && export.decl_interface_hash == *decl_interface_hash
                    })
                    .ok_or_else(|| {
                        ReferenceCheckError::type_check(
                            ReferenceCertificateSection::Declarations,
                            offset,
                            ReferenceCheckReason::UnknownReference,
                        )
                    })?;
                let signature = Arc::new(TypeSignature {
                    universe_params: export.universe_params.clone(),
                    universe_constraints: export.universe_constraints.clone(),
                    ty: self.instantiate_public_expr(
                        *import_index,
                        &import.public_environment,
                        &export.ty,
                        offset,
                    )?,
                    value: export
                        .body
                        .as_ref()
                        .map(|body| {
                            self.instantiate_public_expr(
                                *import_index,
                                &import.public_environment,
                                body,
                                offset,
                            )
                        })
                        .transpose()?,
                });
                self.ensure_signature_constraints_carried(&signature, offset)?;
                self.imported_signatures
                    .borrow_mut()
                    .insert(cache_key, Arc::clone(&signature));
                Ok(signature)
            }
            ReferenceCoreGlobalRef::Local { decl_index } => {
                if self.cert.declarations.get(*decl_index).is_some_and(|decl| {
                    matches!(decl.value.decl, DeclPayload::MutualInductiveBlock { .. })
                }) {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UnknownReference,
                    ));
                }
                self.locals.get(*decl_index).cloned().ok_or_else(|| {
                    ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UnknownReference,
                    )
                })
            }
            ReferenceCoreGlobalRef::LocalGenerated { decl_index, name } => self
                .generated
                .get(&GeneratedKey::new(*decl_index, name.clone()))
                .cloned()
                .ok_or_else(|| {
                    ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UnknownReference,
                    )
                }),
        }
    }

    fn ensure_signature_constraints_carried(
        &self,
        signature: &TypeSignature,
        offset: usize,
    ) -> DecodeResult<()> {
        if signature.universe_constraints.len() > MAX_UNIVERSE_ATOM_INEQUALITIES {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::ResourceLimit,
            ));
        }
        Ok(())
    }

    fn instantiate_public_expr(
        &self,
        owner_import_index: usize,
        owner_environment: &ReferencePublicEnvironment,
        expr: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<ReferenceCoreExpr> {
        Ok(match expr {
            ReferenceCoreExpr::Sort(level) => ReferenceCoreExpr::Sort(level.clone()),
            ReferenceCoreExpr::BVar(index) => ReferenceCoreExpr::BVar(*index),
            ReferenceCoreExpr::Const { global_ref, levels } => ReferenceCoreExpr::Const {
                global_ref: self.instantiate_public_global_ref(
                    owner_import_index,
                    owner_environment,
                    global_ref,
                    offset,
                )?,
                levels: levels.clone(),
            },
            ReferenceCoreExpr::App(fun, arg) => ReferenceCoreExpr::App(
                Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    fun,
                    offset,
                )?),
                Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    arg,
                    offset,
                )?),
            ),
            ReferenceCoreExpr::Lam { ty, body } => ReferenceCoreExpr::Lam {
                ty: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    ty,
                    offset,
                )?),
                body: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    body,
                    offset,
                )?),
            },
            ReferenceCoreExpr::Pi { ty, body } => ReferenceCoreExpr::Pi {
                ty: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    ty,
                    offset,
                )?),
                body: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    body,
                    offset,
                )?),
            },
            ReferenceCoreExpr::Let { ty, value, body } => ReferenceCoreExpr::Let {
                ty: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    ty,
                    offset,
                )?),
                value: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    value,
                    offset,
                )?),
                body: Arc::new(self.instantiate_public_expr(
                    owner_import_index,
                    owner_environment,
                    body,
                    offset,
                )?),
            },
        })
    }

    fn instantiate_public_global_ref(
        &self,
        owner_import_index: usize,
        owner_environment: &ReferencePublicEnvironment,
        global_ref: &ReferenceCoreGlobalRef,
        offset: usize,
    ) -> DecodeResult<ReferenceCoreGlobalRef> {
        Ok(match global_ref {
            ReferenceCoreGlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => ReferenceCoreGlobalRef::Builtin {
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            ReferenceCoreGlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } if *import_index == PUBLIC_SELF_IMPORT_INDEX => ReferenceCoreGlobalRef::Imported {
                import_index: owner_import_index,
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            ReferenceCoreGlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let source = owner_environment
                    .imports
                    .get(*import_index)
                    .ok_or_else(|| {
                        ReferenceCheckError::type_check(
                            ReferenceCertificateSection::Declarations,
                            offset,
                            ReferenceCheckReason::UnknownReference,
                        )
                    })?;
                let remapped = self
                    .imports
                    .imports()
                    .iter()
                    .position(|import| {
                        import.module == source.module && import.export_hash == source.export_hash
                    })
                    .ok_or_else(|| {
                        ReferenceCheckError::type_check(
                            ReferenceCertificateSection::Declarations,
                            offset,
                            ReferenceCheckReason::UnknownReference,
                        )
                    })?;
                ReferenceCoreGlobalRef::Imported {
                    import_index: remapped,
                    name: name.clone(),
                    decl_interface_hash: *decl_interface_hash,
                }
            }
            ReferenceCoreGlobalRef::Local { .. }
            | ReferenceCoreGlobalRef::LocalGenerated { .. } => {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnknownReference,
                ));
            }
        })
    }

    fn whnf(
        &self,
        ctx: &TypeContext,
        delta: &[ReferenceModuleName],
        term: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<ReferenceCoreExpr> {
        let mut fuel = Self::WHNF_FUEL;
        self.whnf_with_fuel(ctx, delta, term, offset, &mut fuel)
    }

    fn whnf_with_fuel(
        &self,
        ctx: &TypeContext,
        delta: &[ReferenceModuleName],
        term: &ReferenceCoreExpr,
        offset: usize,
        fuel: &mut usize,
    ) -> DecodeResult<ReferenceCoreExpr> {
        let mut current = term.clone();
        loop {
            spend_fuel(fuel, offset)?;

            match current {
                ReferenceCoreExpr::BVar(index) => {
                    if let Some(value) = ctx.lookup_value(index, offset)? {
                        current = value;
                    } else {
                        return Ok(ReferenceCoreExpr::BVar(index));
                    }
                }
                ReferenceCoreExpr::Const {
                    ref global_ref,
                    ref levels,
                } => {
                    let signature = self.resolve_signature(global_ref, offset)?;
                    if let Some(value) = signature.value.as_ref() {
                        current = subst_levels_expr(value, &signature.universe_params, levels);
                    } else {
                        return Ok(current);
                    }
                }
                ReferenceCoreExpr::App(fun, arg) => {
                    let fun_whnf = self.whnf_with_fuel(ctx, delta, &fun, offset, fuel)?;
                    if let ReferenceCoreExpr::Lam { body, .. } = fun_whnf {
                        current = instantiate(&body, &arg, offset)?;
                        continue;
                    }

                    let app = ReferenceCoreExpr::App(Arc::new(fun_whnf), arg);
                    if let Some(reduced) = self.reduce_recursor(ctx, delta, &app, offset, fuel)? {
                        current = reduced;
                        continue;
                    }
                    return Ok(app);
                }
                ReferenceCoreExpr::Let { value, body, .. } => {
                    current = instantiate(&body, &value, offset)?;
                }
                _ => return Ok(current),
            }
            ensure_levels_wf_in_expr(&current, delta, offset)?;
        }
    }

    fn reduce_recursor(
        &self,
        ctx: &TypeContext,
        delta: &[ReferenceModuleName],
        term: &ReferenceCoreExpr,
        offset: usize,
        fuel: &mut usize,
    ) -> DecodeResult<Option<ReferenceCoreExpr>> {
        let (head, args) = collect_apps(term);
        let ReferenceCoreExpr::Const { global_ref, levels } = head else {
            return Ok(None);
        };
        let mut request = RecursorReductionRequest {
            ctx,
            delta,
            levels,
            args: &args,
            offset,
            fuel,
        };
        match global_ref {
            ReferenceCoreGlobalRef::LocalGenerated {
                decl_index,
                name: recursor_name,
            } => self.reduce_local_recursor(&mut request, *decl_index, recursor_name),
            ReferenceCoreGlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => self.reduce_imported_recursor(
                &mut request,
                ImportedRecursorKey {
                    import_index: *import_index,
                    name: name.clone(),
                    decl_interface_hash: *decl_interface_hash,
                },
                name,
            ),
            ReferenceCoreGlobalRef::Builtin { .. } | ReferenceCoreGlobalRef::Local { .. } => {
                Ok(None)
            }
        }
    }

    fn reduce_local_recursor(
        &self,
        request: &mut RecursorReductionRequest<'_>,
        decl_index: usize,
        recursor_name: &ReferenceModuleName,
    ) -> DecodeResult<Option<ReferenceCoreExpr>> {
        let recursor_key = GeneratedKey::new(decl_index, recursor_name.clone());
        let Some(recursor) = self.recursors.get(&recursor_key) else {
            return Ok(None);
        };
        if request.args.len() <= recursor.rules.major_index {
            return Ok(None);
        }

        let major = request.args[recursor.rules.major_index].clone();
        let rest = request.args[recursor.rules.major_index + 1..].to_vec();
        let major_whnf = self.whnf_with_fuel(
            request.ctx,
            request.delta,
            &major,
            request.offset,
            &mut *request.fuel,
        )?;
        let (ctor_head, ctor_args) = collect_apps(&major_whnf);
        let ReferenceCoreExpr::Const {
            global_ref:
                ReferenceCoreGlobalRef::LocalGenerated {
                    decl_index: ctor_decl_index,
                    name: constructor_name,
                },
            ..
        } = ctor_head
        else {
            return Ok(None);
        };
        if *ctor_decl_index != recursor.inductive_decl_index {
            return Ok(None);
        }
        let data = match &recursor.target_key {
            Some(key) => self.mutual_inductives.get(key),
            None => self.inductives.get(&recursor.inductive_decl_index),
        };
        let Some(data) = data else { return Ok(None) };
        let Some(ctor_index) = data
            .constructors
            .iter()
            .position(|constructor| constructor.name == *constructor_name)
        else {
            return Ok(None);
        };
        let Some(minor) = request
            .args
            .get(recursor.rules.minor_start + recursor.target_constructor_offset + ctor_index)
            .cloned()
        else {
            return Ok(None);
        };

        let constructor = &data.constructors[ctor_index];
        let (domains, _) = peel_pi_domains(&constructor.ty);
        let param_count = data.params.len();
        if ctor_args.len() < param_count {
            return Ok(None);
        }
        let index_start = recursor.rules.major_index - data.indices.len();
        let field_args = &ctor_args[param_count..];
        let field_domains = &domains[param_count..];
        if field_args.len() < field_domains.len() {
            return Ok(None);
        }

        let mut reduced = minor;
        for (field_index, (field_arg, field_domain)) in
            field_args.iter().zip(field_domains).enumerate()
        {
            reduced = ReferenceCoreExpr::App(Arc::new(reduced), Arc::new(field_arg.clone()));
            if recursor.target_key.is_none()
                && is_direct_recursive_domain(
                    data,
                    field_domain,
                    param_count + field_index,
                    request.offset,
                )?
            {
                let source_ctx_len = param_count + field_index;
                let source_args = &ctor_args[..source_ctx_len];
                let mut recursive_args = request.args[..index_start].to_vec();
                for index_arg in
                    direct_recursive_index_args(data, field_domain, source_ctx_len, request.offset)?
                {
                    recursive_args.push(instantiate_constructor_args(
                        &index_arg,
                        source_args,
                        request.offset,
                    )?);
                }
                recursive_args.push(field_arg.clone());
                let recursive_call = apps(
                    ReferenceCoreExpr::Const {
                        global_ref: ReferenceCoreGlobalRef::LocalGenerated {
                            decl_index,
                            name: recursor_name.clone(),
                        },
                        levels: request.levels.to_vec(),
                    },
                    recursive_args,
                );
                reduced = ReferenceCoreExpr::App(Arc::new(reduced), Arc::new(recursive_call));
            } else if let Some((field_key, field_recursor_name, index_args)) = self
                .direct_mutual_recursive_index_args(
                    &recursor.family_recursors,
                    field_domain,
                    param_count + field_index,
                    request.offset,
                )?
            {
                let source_ctx_len = param_count + field_index;
                let source_args = &ctor_args[..source_ctx_len];
                let mut recursive_args = request.args[..index_start].to_vec();
                for index_arg in index_args {
                    recursive_args.push(instantiate_constructor_args(
                        &index_arg,
                        source_args,
                        request.offset,
                    )?);
                }
                recursive_args.push(field_arg.clone());
                let recursive_call = apps(
                    ReferenceCoreExpr::Const {
                        global_ref: ReferenceCoreGlobalRef::LocalGenerated {
                            decl_index: field_key.decl_index,
                            name: field_recursor_name,
                        },
                        levels: request.levels.to_vec(),
                    },
                    recursive_args,
                );
                reduced = ReferenceCoreExpr::App(Arc::new(reduced), Arc::new(recursive_call));
            }
        }

        Ok(Some(apps(reduced, rest)))
    }

    fn reduce_imported_recursor(
        &self,
        request: &mut RecursorReductionRequest<'_>,
        recursor_key: ImportedRecursorKey,
        recursor_name: &ReferenceModuleName,
    ) -> DecodeResult<Option<ReferenceCoreExpr>> {
        let Some(recursor) = self.imported_recursors.get(&recursor_key) else {
            return Ok(None);
        };
        if request.args.len() <= recursor.recursor.rules.major_index {
            return Ok(None);
        }

        let major = request.args[recursor.recursor.rules.major_index].clone();
        let rest = request.args[recursor.recursor.rules.major_index + 1..].to_vec();
        let major_whnf = self.whnf_with_fuel(
            request.ctx,
            request.delta,
            &major,
            request.offset,
            &mut *request.fuel,
        )?;
        let (ctor_head, ctor_args) = collect_apps(&major_whnf);
        let ReferenceCoreExpr::Const {
            global_ref:
                ReferenceCoreGlobalRef::Imported {
                    import_index: constructor_import_index,
                    name: constructor_name,
                    decl_interface_hash: constructor_decl_interface_hash,
                },
            ..
        } = ctor_head
        else {
            return Ok(None);
        };
        if *constructor_import_index != recursor_key.import_index
            || *constructor_decl_interface_hash != recursor_key.decl_interface_hash
        {
            return Ok(None);
        }

        let data = &recursor.data;
        let Some(ctor_index) = data
            .constructors
            .iter()
            .position(|constructor| constructor.name == *constructor_name)
        else {
            return Ok(None);
        };
        let Some(minor) = request
            .args
            .get(recursor.recursor.rules.minor_start + ctor_index)
            .cloned()
        else {
            return Ok(None);
        };

        let constructor = &data.constructors[ctor_index];
        let (domains, _) = peel_pi_domains(&constructor.ty);
        let param_count = data.params.len();
        if ctor_args.len() < param_count {
            return Ok(None);
        }
        let index_start = recursor.recursor.rules.major_index - data.indices.len();
        let field_args = &ctor_args[param_count..];
        let field_domains = &domains[param_count..];
        if field_args.len() < field_domains.len() {
            return Ok(None);
        }

        let mut reduced = minor;
        for (field_index, (field_arg, field_domain)) in
            field_args.iter().zip(field_domains).enumerate()
        {
            reduced = ReferenceCoreExpr::App(Arc::new(reduced), Arc::new(field_arg.clone()));
            if is_direct_recursive_domain(
                data,
                field_domain,
                param_count + field_index,
                request.offset,
            )? {
                let source_ctx_len = param_count + field_index;
                let source_args = &ctor_args[..source_ctx_len];
                let mut recursive_args = request.args[..index_start].to_vec();
                for index_arg in
                    direct_recursive_index_args(data, field_domain, source_ctx_len, request.offset)?
                {
                    recursive_args.push(instantiate_constructor_args(
                        &index_arg,
                        source_args,
                        request.offset,
                    )?);
                }
                recursive_args.push(field_arg.clone());
                let recursive_call = apps(
                    ReferenceCoreExpr::Const {
                        global_ref: ReferenceCoreGlobalRef::Imported {
                            import_index: recursor_key.import_index,
                            name: recursor_name.clone(),
                            decl_interface_hash: recursor_key.decl_interface_hash,
                        },
                        levels: request.levels.to_vec(),
                    },
                    recursive_args,
                );
                reduced = ReferenceCoreExpr::App(Arc::new(reduced), Arc::new(recursive_call));
            }
        }

        Ok(Some(apps(reduced, rest)))
    }

    fn direct_mutual_recursive_index_args(
        &self,
        family_recursors: &BTreeMap<GeneratedKey, ReferenceModuleName>,
        domain: &ReferenceCoreExpr,
        ctx_len: usize,
        offset: usize,
    ) -> DecodeResult<Option<(GeneratedKey, ReferenceModuleName, Vec<ReferenceCoreExpr>)>> {
        for (key, recursor_name) in family_recursors {
            let Some(data) = self.mutual_inductives.get(key) else {
                continue;
            };
            if let Ok(indices) = direct_recursive_index_args(data, domain, ctx_len, offset) {
                return Ok(Some((key.clone(), recursor_name.clone(), indices)));
            }
        }
        Ok(None)
    }

    fn is_defeq(
        &self,
        ctx: &TypeContext,
        delta: &[ReferenceModuleName],
        lhs: &ReferenceCoreExpr,
        rhs: &ReferenceCoreExpr,
        offset: usize,
    ) -> DecodeResult<bool> {
        let mut fuel = Self::DEFEQ_FUEL;
        self.is_defeq_with_fuel(ctx, delta, lhs, rhs, offset, &mut fuel)
    }

    fn global_refs_defeq(
        &self,
        lhs: &ReferenceCoreGlobalRef,
        rhs: &ReferenceCoreGlobalRef,
        offset: usize,
    ) -> DecodeResult<bool> {
        if lhs == rhs {
            return Ok(true);
        }
        match (lhs, rhs) {
            (
                ReferenceCoreGlobalRef::Builtin { name, .. },
                ReferenceCoreGlobalRef::Imported { .. },
            ) => self.imported_std_logic_eq_ref_matches_builtin(rhs, name, offset),
            (
                ReferenceCoreGlobalRef::Imported { .. },
                ReferenceCoreGlobalRef::Builtin { name, .. },
            ) => self.imported_std_logic_eq_ref_matches_builtin(lhs, name, offset),
            _ => Ok(false),
        }
    }

    fn imported_std_logic_eq_ref_matches_builtin(
        &self,
        imported_ref: &ReferenceCoreGlobalRef,
        builtin_name: &ReferenceModuleName,
        offset: usize,
    ) -> DecodeResult<bool> {
        let ReferenceCoreGlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } = imported_ref
        else {
            return Ok(false);
        };
        if name != builtin_name
            || !matches!(builtin_name.dotted().as_str(), "Eq" | "Eq.refl" | "Eq.rec")
            || builtin_decl_interface_hash(builtin_name).is_none()
        {
            return Ok(false);
        }
        let import = self.imports.imports().get(*import_index).ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::UnknownReference,
            )
        })?;
        if import.module.dotted() != "Std.Logic.Eq" {
            return Ok(false);
        }
        // Std.Logic.Eq exports are checked declarations, so their interface
        // hashes are not the builtin hashes. Require the dependent certificate
        // to name an actual checked export carrying the exact referenced hash.
        Ok(import.public_environment.exports().iter().any(|export| {
            export.name == *name && export.decl_interface_hash == *decl_interface_hash
        }))
    }

    fn is_defeq_with_fuel(
        &self,
        ctx: &TypeContext,
        delta: &[ReferenceModuleName],
        lhs: &ReferenceCoreExpr,
        rhs: &ReferenceCoreExpr,
        offset: usize,
        fuel: &mut usize,
    ) -> DecodeResult<bool> {
        spend_fuel(fuel, offset)?;

        let lhs = self.whnf_with_fuel(ctx, delta, lhs, offset, fuel)?;
        let rhs = self.whnf_with_fuel(ctx, delta, rhs, offset, fuel)?;

        match (&lhs, &rhs) {
            (ReferenceCoreExpr::Sort(lhs), ReferenceCoreExpr::Sort(rhs)) => {
                Ok(reference_level_defeq(lhs, rhs))
            }
            (ReferenceCoreExpr::BVar(lhs), ReferenceCoreExpr::BVar(rhs)) => Ok(lhs == rhs),
            (
                ReferenceCoreExpr::Const {
                    global_ref: lhs_ref,
                    levels: lhs_levels,
                },
                ReferenceCoreExpr::Const {
                    global_ref: rhs_ref,
                    levels: rhs_levels,
                },
            ) => Ok(reference_levels_defeq(lhs_levels, rhs_levels)
                && self.global_refs_defeq(lhs_ref, rhs_ref, offset)?),
            (ReferenceCoreExpr::App(lhs_f, lhs_a), ReferenceCoreExpr::App(rhs_f, rhs_a)) => Ok(
                self.is_defeq_with_fuel(ctx, delta, lhs_f, rhs_f, offset, fuel)?
                    && self.is_defeq_with_fuel(ctx, delta, lhs_a, rhs_a, offset, fuel)?,
            ),
            (
                ReferenceCoreExpr::Pi {
                    ty: lhs_ty,
                    body: lhs_body,
                },
                ReferenceCoreExpr::Pi {
                    ty: rhs_ty,
                    body: rhs_body,
                },
            ) => {
                if !self.is_defeq_with_fuel(ctx, delta, lhs_ty, rhs_ty, offset, fuel)? {
                    return Ok(false);
                }
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption((**lhs_ty).clone());
                self.is_defeq_with_fuel(&body_ctx, delta, lhs_body, rhs_body, offset, fuel)
            }
            (
                ReferenceCoreExpr::Lam {
                    ty: lhs_ty,
                    body: lhs_body,
                },
                ReferenceCoreExpr::Lam {
                    ty: rhs_ty,
                    body: rhs_body,
                },
            ) => {
                if !self.is_defeq_with_fuel(ctx, delta, lhs_ty, rhs_ty, offset, fuel)? {
                    return Ok(false);
                }
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption((**lhs_ty).clone());
                self.is_defeq_with_fuel(&body_ctx, delta, lhs_body, rhs_body, offset, fuel)
            }
            _ => Ok(false),
        }
    }
}

#[derive(Clone, Debug)]
struct TypeSignature {
    universe_params: Vec<ReferenceModuleName>,
    universe_constraints: Vec<ReferenceUniverseConstraint>,
    ty: ReferenceCoreExpr,
    value: Option<ReferenceCoreExpr>,
}

fn enforce_signature_universe_constraints(
    universe_context: &ReferenceUniverseContext,
    signature: &TypeSignature,
    levels: &[ReferenceCoreLevel],
    offset: usize,
) -> DecodeResult<()> {
    if signature.universe_constraints.is_empty() {
        return Ok(());
    }
    let obligations = universe_context.substitute_constraints(
        &signature.universe_params,
        levels,
        &signature.universe_constraints,
        offset,
    )?;
    universe_context.entails(&obligations, offset)
}

fn reference_builtin_signature(
    name: &ReferenceModuleName,
    decl_interface_hash: ReferenceHash,
) -> Option<TypeSignature> {
    if builtin_decl_interface_hash(name) != Some(decl_interface_hash) {
        return None;
    }
    let dotted = name.dotted();
    let signature = match dotted.as_str() {
        "Nat" => TypeSignature {
            universe_params: Vec::new(),
            universe_constraints: Vec::new(),
            ty: rsort(rtype0()),
            value: None,
        },
        "Nat.zero" => TypeSignature {
            universe_params: Vec::new(),
            universe_constraints: Vec::new(),
            ty: rnat(),
            value: None,
        },
        "Nat.succ" => TypeSignature {
            universe_params: Vec::new(),
            universe_constraints: Vec::new(),
            ty: rpi(rnat(), rnat()),
            value: None,
        },
        "Eq" => TypeSignature {
            universe_params: vec![rname("u")],
            universe_constraints: Vec::new(),
            ty: reference_eq_type(rparam("u")),
            value: None,
        },
        "Eq.refl" => TypeSignature {
            universe_params: vec![rname("u")],
            universe_constraints: Vec::new(),
            ty: reference_eq_refl_type(rparam("u")),
            value: None,
        },
        "Eq.rec" => TypeSignature {
            universe_params: vec![rname("u"), rname("v")],
            universe_constraints: Vec::new(),
            ty: reference_eq_rec_type(rparam("u"), rparam("v")),
            value: None,
        },
        _ => return None,
    };
    Some(signature)
}

fn rname(name: &str) -> ReferenceModuleName {
    ReferenceModuleName::from_dotted(name).expect("builtin reference names are canonical")
}

fn rparam(name: &str) -> ReferenceCoreLevel {
    ReferenceCoreLevel::Param(rname(name))
}

fn rzero() -> ReferenceCoreLevel {
    ReferenceCoreLevel::Zero
}

fn rsucc(level: ReferenceCoreLevel) -> ReferenceCoreLevel {
    ReferenceCoreLevel::Succ(Arc::new(level))
}

fn rtype0() -> ReferenceCoreLevel {
    rsucc(rzero())
}

fn rsort(level: ReferenceCoreLevel) -> ReferenceCoreExpr {
    ReferenceCoreExpr::Sort(level)
}

fn rbvar(index: u32) -> ReferenceCoreExpr {
    ReferenceCoreExpr::BVar(index)
}

fn rpi(ty: ReferenceCoreExpr, body: ReferenceCoreExpr) -> ReferenceCoreExpr {
    ReferenceCoreExpr::Pi {
        ty: Arc::new(ty),
        body: Arc::new(body),
    }
}

fn rbuiltin(name: &str, levels: Vec<ReferenceCoreLevel>) -> ReferenceCoreExpr {
    let name = rname(name);
    let decl_interface_hash =
        builtin_decl_interface_hash(&name).expect("builtin signatures only use known builtins");
    ReferenceCoreExpr::Const {
        global_ref: ReferenceCoreGlobalRef::Builtin {
            name,
            decl_interface_hash,
        },
        levels,
    }
}

fn rnat() -> ReferenceCoreExpr {
    rbuiltin("Nat", Vec::new())
}

fn reference_eq(
    level: ReferenceCoreLevel,
    ty: ReferenceCoreExpr,
    lhs: ReferenceCoreExpr,
    rhs: ReferenceCoreExpr,
) -> ReferenceCoreExpr {
    apps(rbuiltin("Eq", vec![level]), vec![ty, lhs, rhs])
}

fn reference_eq_refl(
    level: ReferenceCoreLevel,
    ty: ReferenceCoreExpr,
    value: ReferenceCoreExpr,
) -> ReferenceCoreExpr {
    apps(rbuiltin("Eq.refl", vec![level]), vec![ty, value])
}

fn reference_eq_type(level: ReferenceCoreLevel) -> ReferenceCoreExpr {
    rpi(rsort(level), rpi(rbvar(0), rpi(rbvar(1), rsort(rzero()))))
}

fn reference_eq_refl_type(level: ReferenceCoreLevel) -> ReferenceCoreExpr {
    rpi(
        rsort(level.clone()),
        rpi(rbvar(0), reference_eq(level, rbvar(1), rbvar(0), rbvar(0))),
    )
}

fn reference_eq_rec_type(
    value_level: ReferenceCoreLevel,
    motive_level: ReferenceCoreLevel,
) -> ReferenceCoreExpr {
    let motive_ty = rpi(
        rbvar(1),
        rpi(
            reference_eq(value_level.clone(), rbvar(2), rbvar(1), rbvar(0)),
            rsort(motive_level),
        ),
    );
    let refl_proof = reference_eq_refl(value_level.clone(), rbvar(2), rbvar(1));
    let minor_ty = apps(rbvar(0), vec![rbvar(1), refl_proof]);
    let major_ty = reference_eq(value_level, rbvar(4), rbvar(3), rbvar(0));
    let result_ty = apps(rbvar(3), vec![rbvar(1), rbvar(0)]);
    rpi(
        rsort(rparam("u")),
        rpi(
            rbvar(0),
            rpi(
                motive_ty,
                rpi(minor_ty, rpi(rbvar(3), rpi(major_ty, result_ty))),
            ),
        ),
    )
}

fn reference_level_defeq(lhs: &ReferenceCoreLevel, rhs: &ReferenceCoreLevel) -> bool {
    normalize_reference_level(lhs.clone()) == normalize_reference_level(rhs.clone())
}

fn reference_levels_defeq(lhs: &[ReferenceCoreLevel], rhs: &[ReferenceCoreLevel]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs)
            .all(|(lhs, rhs)| reference_level_defeq(lhs, rhs))
}

fn normalize_reference_level(level: ReferenceCoreLevel) -> ReferenceCoreLevel {
    match level {
        ReferenceCoreLevel::Zero | ReferenceCoreLevel::Param(_) => level,
        ReferenceCoreLevel::Succ(level) => ReferenceCoreLevel::Succ(Arc::new(
            normalize_reference_level(Arc::unwrap_or_clone(level)),
        )),
        ReferenceCoreLevel::Max(lhs, rhs) => {
            let lhs = normalize_reference_level(Arc::unwrap_or_clone(lhs));
            let rhs = normalize_reference_level(Arc::unwrap_or_clone(rhs));
            if lhs == rhs {
                return lhs;
            }
            if lhs == ReferenceCoreLevel::Zero {
                return rhs;
            }
            if rhs == ReferenceCoreLevel::Zero {
                return lhs;
            }
            match (reference_level_as_nat(&lhs), reference_level_as_nat(&rhs)) {
                (Some(lhs_nat), Some(rhs_nat)) => reference_level_from_nat(lhs_nat.max(rhs_nat)),
                _ if rhs < lhs => ReferenceCoreLevel::Max(Arc::new(rhs), Arc::new(lhs)),
                _ => ReferenceCoreLevel::Max(Arc::new(lhs), Arc::new(rhs)),
            }
        }
        ReferenceCoreLevel::IMax(lhs, rhs) => {
            let lhs = normalize_reference_level(Arc::unwrap_or_clone(lhs));
            let rhs = normalize_reference_level(Arc::unwrap_or_clone(rhs));
            match rhs {
                ReferenceCoreLevel::Zero => ReferenceCoreLevel::Zero,
                ReferenceCoreLevel::Succ(inner) => {
                    normalize_reference_level(ReferenceCoreLevel::Max(
                        Arc::new(lhs),
                        Arc::new(ReferenceCoreLevel::Succ(inner)),
                    ))
                }
                rhs => ReferenceCoreLevel::IMax(Arc::new(lhs), Arc::new(rhs)),
            }
        }
    }
}

fn reference_level_as_nat(level: &ReferenceCoreLevel) -> Option<u32> {
    match level {
        ReferenceCoreLevel::Zero => Some(0),
        ReferenceCoreLevel::Succ(level) => Some(reference_level_as_nat(level)? + 1),
        _ => None,
    }
}

fn reference_level_from_nat(n: u32) -> ReferenceCoreLevel {
    (0..n).fold(ReferenceCoreLevel::Zero, |level, _| {
        ReferenceCoreLevel::Succ(Arc::new(level))
    })
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct GeneratedKey {
    decl_index: usize,
    name: ReferenceModuleName,
}

impl GeneratedKey {
    fn new(decl_index: usize, name: ReferenceModuleName) -> Self {
        Self { decl_index, name }
    }
}

#[derive(Clone, Debug)]
struct ReferenceInductiveSignature {
    decl_index: usize,
    global_ref: ReferenceCoreGlobalRef,
    universe_params: Vec<ReferenceModuleName>,
    universe_constraints: Vec<UniverseConstraintSpec>,
    params: Vec<ReferenceCoreExpr>,
    indices: Vec<ReferenceCoreExpr>,
    sort: ReferenceCoreLevel,
    constructors: Vec<ReferenceConstructorSignature>,
    recursor: Option<ReferenceRecursorSignature>,
}

impl ReferenceInductiveSignature {
    fn generated_family_name(&self) -> ReferenceModuleName {
        match &self.global_ref {
            ReferenceCoreGlobalRef::LocalGenerated { name, .. } => name.clone(),
            ReferenceCoreGlobalRef::Local { .. } => {
                unreachable!("single inductive families are not block-generated")
            }
            ReferenceCoreGlobalRef::Builtin { .. } | ReferenceCoreGlobalRef::Imported { .. } => {
                unreachable!("inductive signatures are local declarations")
            }
        }
    }
}

#[derive(Clone, Debug)]
struct ReferenceConstructorSignature {
    name: ReferenceModuleName,
    ty: ReferenceCoreExpr,
}

#[derive(Clone, Debug)]
struct ReferenceRecursorSignature {
    name: ReferenceModuleName,
    universe_params: Vec<ReferenceModuleName>,
    ty: ReferenceCoreExpr,
    rules: RecursorRulesSpec,
}

struct MutualRecursorResultCheck<'a> {
    target: &'a ReferenceInductiveSignature,
    target_index: usize,
    recursor: &'a ReferenceRecursorSignature,
    domains: &'a [ReferenceCoreExpr],
    result: &'a ReferenceCoreExpr,
    index_start: usize,
    offset: usize,
}

#[derive(Clone, Debug)]
struct ReferenceRecursorRuntime {
    inductive_decl_index: usize,
    target_key: Option<GeneratedKey>,
    target_constructor_offset: usize,
    family_recursors: BTreeMap<GeneratedKey, ReferenceModuleName>,
    rules: RecursorRulesSpec,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportedRecursorKey {
    import_index: usize,
    name: ReferenceModuleName,
    decl_interface_hash: ReferenceHash,
}

#[derive(Clone, Debug)]
struct ReferenceImportedRecursorRuntime {
    data: ReferenceInductiveSignature,
    recursor: ReferenceRecursorSignature,
}

struct RecursorReductionRequest<'a> {
    ctx: &'a TypeContext,
    delta: &'a [ReferenceModuleName],
    levels: &'a [ReferenceCoreLevel],
    args: &'a [ReferenceCoreExpr],
    offset: usize,
    fuel: &'a mut usize,
}

#[derive(Default)]
struct ImportedInductiveExportGroup<'a> {
    inductives: Vec<&'a ReferencePublicExport>,
    constructors: Vec<&'a ReferencePublicExport>,
    recursors: Vec<&'a ReferencePublicExport>,
}

fn imported_inductive_export_groups(
    exports: &[ReferencePublicExport],
) -> BTreeMap<ReferenceHash, ImportedInductiveExportGroup<'_>> {
    let mut groups: BTreeMap<ReferenceHash, ImportedInductiveExportGroup<'_>> = BTreeMap::new();
    for export in exports {
        match export.kind {
            ReferenceExportKind::Inductive => groups
                .entry(export.decl_interface_hash)
                .or_default()
                .inductives
                .push(export),
            ReferenceExportKind::Constructor => groups
                .entry(export.decl_interface_hash)
                .or_default()
                .constructors
                .push(export),
            ReferenceExportKind::Recursor => groups
                .entry(export.decl_interface_hash)
                .or_default()
                .recursors
                .push(export),
            ReferenceExportKind::Axiom
            | ReferenceExportKind::Def
            | ReferenceExportKind::Theorem => {}
        }
    }
    groups
}

#[derive(Clone, Debug, Default)]
struct TypeContext {
    locals: Vec<LocalType>,
}

impl TypeContext {
    fn push_assumption(&mut self, ty: ReferenceCoreExpr) {
        self.locals.push(LocalType { ty, value: None });
    }

    fn push_definition(&mut self, ty: ReferenceCoreExpr, value: ReferenceCoreExpr) {
        self.locals.push(LocalType {
            ty,
            value: Some(value),
        });
    }

    fn lookup_type(&self, index: u32, offset: usize) -> DecodeResult<ReferenceCoreExpr> {
        let index = index as usize;
        let local = self
            .locals
            .get(self.locals.len().checked_sub(index + 1).ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                )
            })?)
            .ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                )
            })?;
        shift(&local.ty, index as i32 + 1, 0, offset)
    }

    fn lookup_value(&self, index: u32, offset: usize) -> DecodeResult<Option<ReferenceCoreExpr>> {
        let index = index as usize;
        let local = self
            .locals
            .get(self.locals.len().checked_sub(index + 1).ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                )
            })?)
            .ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                )
            })?;
        local
            .value
            .as_ref()
            .map(|value| shift(value, index as i32 + 1, 0, offset))
            .transpose()
    }
}

#[derive(Clone, Debug)]
struct LocalType {
    ty: ReferenceCoreExpr,
    value: Option<ReferenceCoreExpr>,
}

fn spend_fuel(fuel: &mut usize, offset: usize) -> DecodeResult<()> {
    if *fuel == 0 {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::ResourceLimit,
        ));
    }
    *fuel -= 1;
    Ok(())
}

fn ensure_level_wf(
    level: &ReferenceCoreLevel,
    delta: &[ReferenceModuleName],
    offset: usize,
) -> DecodeResult<()> {
    match level {
        ReferenceCoreLevel::Zero => Ok(()),
        ReferenceCoreLevel::Succ(inner) => ensure_level_wf(inner, delta, offset),
        ReferenceCoreLevel::Max(lhs, rhs) | ReferenceCoreLevel::IMax(lhs, rhs) => {
            ensure_level_wf(lhs, delta, offset)?;
            ensure_level_wf(rhs, delta, offset)
        }
        ReferenceCoreLevel::Param(name) => {
            if is_unresolved_universe_meta_name(name) {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnresolvedMetavariable,
                ));
            }
            if delta.contains(name) {
                Ok(())
            } else {
                Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnknownReference,
                ))
            }
        }
    }
}

fn ensure_levels_wf_in_expr(
    expr: &ReferenceCoreExpr,
    delta: &[ReferenceModuleName],
    offset: usize,
) -> DecodeResult<()> {
    match expr {
        ReferenceCoreExpr::Sort(level) => ensure_level_wf(level, delta, offset),
        ReferenceCoreExpr::BVar(_) => Ok(()),
        ReferenceCoreExpr::Const { levels, .. } => {
            for level in levels {
                ensure_level_wf(level, delta, offset)?;
            }
            Ok(())
        }
        ReferenceCoreExpr::App(fun, arg) => {
            ensure_levels_wf_in_expr(fun, delta, offset)?;
            ensure_levels_wf_in_expr(arg, delta, offset)
        }
        ReferenceCoreExpr::Lam { ty, body } | ReferenceCoreExpr::Pi { ty, body } => {
            ensure_levels_wf_in_expr(ty, delta, offset)?;
            ensure_levels_wf_in_expr(body, delta, offset)
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            ensure_levels_wf_in_expr(ty, delta, offset)?;
            ensure_levels_wf_in_expr(value, delta, offset)?;
            ensure_levels_wf_in_expr(body, delta, offset)
        }
    }
}

fn is_unresolved_universe_meta_name(name: &ReferenceModuleName) -> bool {
    name.components().iter().any(|component| {
        component.starts_with(HUMAN_UNIVERSE_META_PREFIX) || component.contains('?')
    })
}

fn ensure_unique_names(params: &[ReferenceModuleName], offset: usize) -> DecodeResult<()> {
    let mut seen = BTreeSet::new();
    for param in params {
        if !seen.insert(param) {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::DuplicateUniverseParam,
            ));
        }
    }
    Ok(())
}

#[allow(dead_code)]
fn validate_reference_universe_params(
    params: &[ReferenceModuleName],
    offset: usize,
) -> DecodeResult<()> {
    if params.iter().any(is_unresolved_universe_meta_name) {
        return Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::UnresolvedMetavariable,
        ));
    }
    if !params.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::NonCanonicalOrder,
        ));
    }
    ensure_unique_names(params, offset)
}

#[allow(dead_code)]
fn ensure_reference_universe_constraints_wf(
    params: &[ReferenceModuleName],
    constraints: &[ReferenceUniverseConstraint],
    offset: usize,
) -> DecodeResult<()> {
    for constraint in constraints {
        ensure_reference_canonical_level(&constraint.lhs, params, offset)?;
        ensure_reference_canonical_level(&constraint.rhs, params, offset)?;
    }
    let mut canonical = constraints.to_vec();
    canonical.sort();
    if constraints != canonical.as_slice() {
        return Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::NonCanonicalOrder,
        ));
    }
    if canonical.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::DuplicateUniverseConstraint,
        ));
    }
    Ok(())
}

#[allow(dead_code)]
fn ensure_reference_canonical_level(
    level: &ReferenceCoreLevel,
    params: &[ReferenceModuleName],
    offset: usize,
) -> DecodeResult<()> {
    ensure_level_wf(level, params, offset)?;
    if normalize_reference_level(level.clone()) == *level {
        Ok(())
    } else {
        Err(ReferenceCheckError::malformed(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::NonNormalizedLevel,
        ))
    }
}

#[allow(dead_code)]
fn ensure_reference_universe_node_limit(param_count: usize, offset: usize) -> DecodeResult<()> {
    if param_count + 1 > MAX_UNIVERSE_CONTEXT_NODES {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::ResourceLimit,
        ));
    }
    Ok(())
}

#[allow(dead_code)]
fn ensure_reference_universe_edge_limit(edge_count: usize, offset: usize) -> DecodeResult<()> {
    if edge_count > MAX_UNIVERSE_ATOM_INEQUALITIES {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::ResourceLimit,
        ));
    }
    Ok(())
}

#[allow(dead_code)]
fn reference_universe_param_indices(
    params: &[ReferenceModuleName],
) -> BTreeMap<ReferenceModuleName, usize> {
    params
        .iter()
        .enumerate()
        .map(|(index, param)| (param.clone(), index + 1))
        .collect()
}

#[allow(dead_code)]
fn reference_atom_base_index(
    base: &ReferenceAtomBase,
    params: &BTreeMap<ReferenceModuleName, usize>,
    offset: usize,
) -> DecodeResult<usize> {
    match base {
        ReferenceAtomBase::Zero => Ok(0),
        ReferenceAtomBase::Param(name) => params.get(name).copied().ok_or_else(|| {
            ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::UnknownReference,
            )
        }),
    }
}

#[allow(dead_code)]
fn normalize_reference_constraint(
    constraint: &ReferenceUniverseConstraint,
) -> ReferenceUniverseConstraint {
    ReferenceUniverseConstraint {
        lhs: normalize_reference_level(constraint.lhs.clone()),
        relation: constraint.relation,
        rhs: normalize_reference_level(constraint.rhs.clone()),
    }
}

#[allow(dead_code)]
fn decompose_reference_constraint(
    constraint: &ReferenceUniverseConstraint,
    offset: usize,
) -> DecodeResult<Vec<ReferenceAtomInequality>> {
    let normalized = normalize_reference_constraint(constraint);
    match normalized.relation {
        UniverseConstraintRelation::Le => {
            decompose_reference_le_constraint(normalized.lhs, normalized.rhs, offset)
        }
        UniverseConstraintRelation::Eq => {
            if normalized.lhs == normalized.rhs {
                return Ok(Vec::new());
            }
            let mut inequalities = decompose_reference_le_constraint(
                normalized.lhs.clone(),
                normalized.rhs.clone(),
                offset,
            )?;
            inequalities.extend(decompose_reference_le_constraint(
                normalized.rhs,
                normalized.lhs,
                offset,
            )?);
            Ok(inequalities)
        }
    }
}

#[allow(dead_code)]
fn decompose_reference_le_constraint(
    lhs: ReferenceCoreLevel,
    rhs: ReferenceCoreLevel,
    offset: usize,
) -> DecodeResult<Vec<ReferenceAtomInequality>> {
    let lhs = normalize_reference_level(lhs);
    let rhs = normalize_reference_level(rhs);
    if lhs == rhs {
        return Ok(Vec::new());
    }
    let lhs_atoms = decompose_reference_level_expr(&lhs, offset)?;
    let rhs_atoms = decompose_reference_level_expr(&rhs, offset)?;
    let [rhs_atom] = rhs_atoms.as_slice() else {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::UnsupportedUniverseConstraint,
        ));
    };
    Ok(lhs_atoms
        .into_iter()
        .map(|lhs| ReferenceAtomInequality {
            lhs,
            rhs: rhs_atom.clone(),
        })
        .collect())
}

#[allow(dead_code)]
fn decompose_reference_level_expr(
    level: &ReferenceCoreLevel,
    offset: usize,
) -> DecodeResult<Vec<ReferenceAtom>> {
    match normalize_reference_level(level.clone()) {
        ReferenceCoreLevel::Max(lhs, rhs) => {
            let mut atoms = decompose_reference_level_expr(&lhs, offset)?;
            atoms.extend(decompose_reference_level_expr(&rhs, offset)?);
            atoms.sort();
            atoms.dedup();
            Ok(atoms)
        }
        level => Ok(vec![decompose_reference_atom(&level, offset)?]),
    }
}

#[allow(dead_code)]
fn decompose_reference_atom(
    level: &ReferenceCoreLevel,
    offset: usize,
) -> DecodeResult<ReferenceAtom> {
    match normalize_reference_level(level.clone()) {
        ReferenceCoreLevel::Zero => Ok(ReferenceAtom {
            base: ReferenceAtomBase::Zero,
            offset: 0,
        }),
        ReferenceCoreLevel::Param(name) => Ok(ReferenceAtom {
            base: ReferenceAtomBase::Param(name),
            offset: 0,
        }),
        ReferenceCoreLevel::Succ(inner) => {
            let mut atom = decompose_reference_atom(&inner, offset)?;
            atom.offset = atom.offset.checked_add(1).ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnsupportedUniverseConstraint,
                )
            })?;
            reference_offset_bound(&atom, offset)?;
            Ok(atom)
        }
        _ => Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::UnsupportedUniverseConstraint,
        )),
    }
}

#[allow(dead_code)]
fn reference_offset_bound(atom: &ReferenceAtom, offset: usize) -> DecodeResult<i64> {
    i64::try_from(atom.offset).map_err(|_| {
        ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::UnsupportedUniverseConstraint,
        )
    })
}

#[allow(dead_code)]
fn substitute_reference_level(
    level: &ReferenceCoreLevel,
    params: &[ReferenceModuleName],
    levels: &[ReferenceCoreLevel],
) -> ReferenceCoreLevel {
    match level {
        ReferenceCoreLevel::Zero => ReferenceCoreLevel::Zero,
        ReferenceCoreLevel::Succ(inner) => normalize_reference_level(ReferenceCoreLevel::Succ(
            Arc::new(substitute_reference_level(inner, params, levels)),
        )),
        ReferenceCoreLevel::Max(lhs, rhs) => normalize_reference_level(ReferenceCoreLevel::Max(
            Arc::new(substitute_reference_level(lhs, params, levels)),
            Arc::new(substitute_reference_level(rhs, params, levels)),
        )),
        ReferenceCoreLevel::IMax(lhs, rhs) => normalize_reference_level(ReferenceCoreLevel::IMax(
            Arc::new(substitute_reference_level(lhs, params, levels)),
            Arc::new(substitute_reference_level(rhs, params, levels)),
        )),
        ReferenceCoreLevel::Param(name) => params
            .iter()
            .position(|param| param == name)
            .map(|index| levels[index].clone())
            .unwrap_or_else(|| ReferenceCoreLevel::Param(name.clone())),
    }
}

fn peel_pi_domains(expr: &ReferenceCoreExpr) -> (Vec<ReferenceCoreExpr>, ReferenceCoreExpr) {
    let mut domains = Vec::new();
    let mut current = expr;
    while let ReferenceCoreExpr::Pi { ty, body } = current {
        domains.push((**ty).clone());
        current = body;
    }
    (domains, current.clone())
}

fn collect_apps(expr: &ReferenceCoreExpr) -> (&ReferenceCoreExpr, Vec<ReferenceCoreExpr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ReferenceCoreExpr::App(fun, arg) = current {
        args.push((**arg).clone());
        current = fun;
    }
    args.reverse();
    (current, args)
}

fn apps(head: ReferenceCoreExpr, args: Vec<ReferenceCoreExpr>) -> ReferenceCoreExpr {
    args.into_iter().fold(head, |fun, arg| {
        ReferenceCoreExpr::App(Arc::new(fun), Arc::new(arg))
    })
}

fn bvar_for_abs(ctx_len: usize, abs: usize, offset: usize) -> DecodeResult<ReferenceCoreExpr> {
    if abs >= ctx_len {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::InvalidBVar,
        ));
    }
    Ok(ReferenceCoreExpr::BVar((ctx_len - 1 - abs) as u32))
}

fn motive_app(
    ctx_len: usize,
    motive_abs: usize,
    index_args: Vec<ReferenceCoreExpr>,
    target: ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let mut args = index_args;
    args.push(target);
    Ok(apps(bvar_for_abs(ctx_len, motive_abs, offset)?, args))
}

fn recursor_prefix_ctx(domains: &[ReferenceCoreExpr]) -> TypeContext {
    let mut ctx = TypeContext::default();
    for domain in domains {
        ctx.push_assumption(domain.clone());
    }
    ctx
}

fn expected_recursor_type(
    data: &ReferenceInductiveSignature,
    recursor: &ReferenceRecursorSignature,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let param_count = data.params.len();
    let mut domains = data.params.clone();
    domains.push(motive_domain_expr(
        data,
        expected_motive_level(data, recursor),
        offset,
    )?);

    for (constructor_index, constructor) in data.constructors.iter().enumerate() {
        domains.push(expected_minor_type(
            data,
            constructor,
            constructor_index,
            offset,
        )?);
    }

    let index_start = domains.len();
    append_index_domains(data, &mut domains, offset)?;
    let major_domain = inductive_target_expr(
        data,
        domains.len(),
        param_count,
        index_start,
        data.indices.len(),
        offset,
    )?;
    domains.push(major_domain);
    let index_args = (0..data.indices.len())
        .map(|index| bvar_for_abs(domains.len(), index_start + index, offset))
        .collect::<DecodeResult<Vec<_>>>()?;
    let body = motive_app(
        domains.len(),
        param_count,
        index_args,
        bvar_for_abs(domains.len(), recursor.rules.major_index, offset)?,
        offset,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn expected_mutual_recursor_type(
    block: &[ReferenceInductiveSignature],
    target_index: usize,
    recursor: &ReferenceRecursorSignature,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let target = block.get(target_index).ok_or_else(|| {
        ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorRule,
        )
    })?;
    let param_count = target.params.len();
    let mut domains = target.params.clone();
    for family in block {
        domains.push(motive_domain_expr(
            family,
            expected_motive_level(family, recursor),
            offset,
        )?);
    }
    let mut constructor_index = 0usize;
    for (family_index, family) in block.iter().enumerate() {
        for constructor in &family.constructors {
            domains.push(expected_mutual_minor_type(
                block,
                family_index,
                constructor,
                constructor_index,
                offset,
            )?);
            constructor_index += 1;
        }
    }
    let index_start = domains.len();
    append_index_domains(target, &mut domains, offset)?;
    let major_domain = inductive_target_expr(
        target,
        domains.len(),
        param_count,
        index_start,
        target.indices.len(),
        offset,
    )?;
    domains.push(major_domain);
    let index_args = (0..target.indices.len())
        .map(|index| bvar_for_abs(domains.len(), index_start + index, offset))
        .collect::<DecodeResult<Vec<_>>>()?;
    let body = motive_app(
        domains.len(),
        param_count + target_index,
        index_args,
        bvar_for_abs(domains.len(), recursor.rules.major_index, offset)?,
        offset,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn mutual_constructor_count(block: &[ReferenceInductiveSignature]) -> usize {
    block.iter().map(|data| data.constructors.len()).sum()
}

fn expected_motive_level(
    data: &ReferenceInductiveSignature,
    recursor: &ReferenceRecursorSignature,
) -> ReferenceCoreLevel {
    if data.sort == ReferenceCoreLevel::Zero {
        return ReferenceCoreLevel::Zero;
    }
    if let Some(param) = recursor
        .universe_params
        .iter()
        .rev()
        .find(|param| !data.universe_params.contains(*param))
    {
        return ReferenceCoreLevel::Param(param.clone());
    }
    recursor
        .universe_params
        .last()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .unwrap_or_else(|| data.sort.clone())
}

fn inductive_target_expr(
    data: &ReferenceInductiveSignature,
    ctx_len: usize,
    param_count: usize,
    index_abs_start: usize,
    index_count: usize,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let levels = data
        .universe_params
        .iter()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .collect();
    let args = (0..param_count)
        .map(|param_abs| bvar_for_abs(ctx_len, param_abs, offset))
        .chain((0..index_count).map(|index| bvar_for_abs(ctx_len, index_abs_start + index, offset)))
        .collect::<DecodeResult<Vec<_>>>()?;
    Ok(apps(
        ReferenceCoreExpr::Const {
            global_ref: data.global_ref.clone(),
            levels,
        },
        args,
    ))
}

fn motive_domain_expr(
    data: &ReferenceInductiveSignature,
    motive_level: ReferenceCoreLevel,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let param_count = data.params.len();
    let mut domains = Vec::new();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in data.indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = param_count + index;
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
            offset,
        )?);
        source_to_target.push(target_ctx_len);
    }
    let target = inductive_target_expr(
        data,
        param_count + data.indices.len(),
        param_count,
        param_count,
        data.indices.len(),
        offset,
    )?;
    let body = ReferenceCoreExpr::Pi {
        ty: Arc::new(target),
        body: Arc::new(ReferenceCoreExpr::Sort(motive_level)),
    };
    Ok(mk_pi_from_domains(domains, body))
}

fn append_index_domains(
    data: &ReferenceInductiveSignature,
    domains: &mut Vec<ReferenceCoreExpr>,
    offset: usize,
) -> DecodeResult<()> {
    let param_count = data.params.len();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in data.indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = domains.len();
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
            offset,
        )?);
        source_to_target.push(target_ctx_len);
    }
    Ok(())
}

fn mk_pi_from_domains(
    domains: Vec<ReferenceCoreExpr>,
    body: ReferenceCoreExpr,
) -> ReferenceCoreExpr {
    domains
        .into_iter()
        .rev()
        .fold(body, |body, domain| ReferenceCoreExpr::Pi {
            ty: Arc::new(domain),
            body: Arc::new(body),
        })
}

fn constructor_global_ref(
    data: &ReferenceInductiveSignature,
    name: &ReferenceModuleName,
) -> ReferenceCoreGlobalRef {
    match &data.global_ref {
        ReferenceCoreGlobalRef::Local { .. } | ReferenceCoreGlobalRef::LocalGenerated { .. } => {
            ReferenceCoreGlobalRef::LocalGenerated {
                decl_index: data.decl_index,
                name: name.clone(),
            }
        }
        ReferenceCoreGlobalRef::Imported {
            import_index,
            decl_interface_hash,
            ..
        } => ReferenceCoreGlobalRef::Imported {
            import_index: *import_index,
            name: name.clone(),
            decl_interface_hash: *decl_interface_hash,
        },
        ReferenceCoreGlobalRef::Builtin { .. } => {
            unreachable!("inductive constructor signatures are not builtin global refs")
        }
    }
}

fn expected_minor_type(
    data: &ReferenceInductiveSignature,
    constructor: &ReferenceConstructorSignature,
    constructor_index: usize,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor.ty);
    let param_count = data.params.len();
    if constructor_domains.len() < param_count {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        ));
    }
    let constructor_result_indices =
        constructor_result_index_args(data, &constructor_result, offset)?;

    let prefix_len = param_count + 1 + constructor_index;
    let motive_abs = param_count;
    let mut source_to_target: Vec<usize> = (0..param_count).collect();
    let mut target_ctx_len = prefix_len;
    let mut expected_domains = Vec::new();
    let mut field_abs = Vec::new();

    for (field_index, field_domain) in constructor_domains[param_count..].iter().enumerate() {
        let source_ctx_len = param_count + field_index;
        expected_domains.push(remap_bvars(
            field_domain,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
            offset,
        )?);

        source_to_target.push(target_ctx_len);
        field_abs.push(target_ctx_len);
        target_ctx_len += 1;

        if is_direct_recursive_domain(data, field_domain, source_ctx_len, offset)? {
            let index_args =
                direct_recursive_index_args(data, field_domain, source_ctx_len, offset)?
                    .into_iter()
                    .map(|arg| {
                        remap_bvars(
                            &arg,
                            source_ctx_len,
                            target_ctx_len,
                            &source_to_target,
                            offset,
                        )
                    })
                    .collect::<DecodeResult<Vec<_>>>()?;
            expected_domains.push(motive_app(
                target_ctx_len,
                motive_abs,
                index_args,
                ReferenceCoreExpr::BVar(0),
                offset,
            )?);
            target_ctx_len += 1;
        }
    }

    let mut constructor_args = Vec::with_capacity(param_count + field_abs.len());
    for param_abs in 0..param_count {
        constructor_args.push(bvar_for_abs(target_ctx_len, param_abs, offset)?);
    }
    for field_abs in field_abs {
        constructor_args.push(bvar_for_abs(target_ctx_len, field_abs, offset)?);
    }

    let levels = data
        .universe_params
        .iter()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .collect();
    let constructor_value = apps(
        ReferenceCoreExpr::Const {
            global_ref: constructor_global_ref(data, &constructor.name),
            levels,
        },
        constructor_args,
    );
    let result_index_args = constructor_result_indices
        .iter()
        .map(|arg| {
            remap_bvars(
                arg,
                constructor_domains.len(),
                target_ctx_len,
                &source_to_target,
                offset,
            )
        })
        .collect::<DecodeResult<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs,
        result_index_args,
        constructor_value,
        offset,
    )?;

    Ok(mk_pi_from_domains(expected_domains, result))
}

fn expected_mutual_minor_type(
    block: &[ReferenceInductiveSignature],
    family_index: usize,
    constructor: &ReferenceConstructorSignature,
    constructor_index: usize,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    let owner = block.get(family_index).ok_or_else(|| {
        ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        )
    })?;
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor.ty);
    let param_count = owner.params.len();
    if constructor_domains.len() < param_count {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        ));
    }
    let constructor_result_indices =
        constructor_result_index_args(owner, &constructor_result, offset)?;

    let prefix_len = param_count + block.len() + constructor_index;
    let motive_abs_start = param_count;
    let mut source_to_target: Vec<usize> = (0..param_count).collect();
    let mut target_ctx_len = prefix_len;
    let mut expected_domains = Vec::new();
    let mut field_abs = Vec::new();

    for (field_index, field_domain) in constructor_domains[param_count..].iter().enumerate() {
        let source_ctx_len = param_count + field_index;
        expected_domains.push(remap_bvars(
            field_domain,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
            offset,
        )?);

        source_to_target.push(target_ctx_len);
        field_abs.push(target_ctx_len);
        target_ctx_len += 1;

        if let Some((field_family_index, index_args)) =
            direct_mutual_recursive_index_args(block, field_domain, source_ctx_len, offset)?
        {
            let index_args = index_args
                .into_iter()
                .map(|arg| {
                    remap_bvars(
                        &arg,
                        source_ctx_len,
                        target_ctx_len,
                        &source_to_target,
                        offset,
                    )
                })
                .collect::<DecodeResult<Vec<_>>>()?;
            expected_domains.push(motive_app(
                target_ctx_len,
                motive_abs_start + field_family_index,
                index_args,
                ReferenceCoreExpr::BVar(0),
                offset,
            )?);
            target_ctx_len += 1;
        }
    }

    let mut constructor_args = Vec::with_capacity(param_count + field_abs.len());
    for param_abs in 0..param_count {
        constructor_args.push(bvar_for_abs(target_ctx_len, param_abs, offset)?);
    }
    for field_abs in field_abs {
        constructor_args.push(bvar_for_abs(target_ctx_len, field_abs, offset)?);
    }

    let levels = owner
        .universe_params
        .iter()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .collect();
    let constructor_value = apps(
        ReferenceCoreExpr::Const {
            global_ref: constructor_global_ref(owner, &constructor.name),
            levels,
        },
        constructor_args,
    );
    let result_index_args = constructor_result_indices
        .iter()
        .map(|arg| {
            remap_bvars(
                arg,
                constructor_domains.len(),
                target_ctx_len,
                &source_to_target,
                offset,
            )
        })
        .collect::<DecodeResult<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs_start + family_index,
        result_index_args,
        constructor_value,
        offset,
    )?;
    Ok(mk_pi_from_domains(expected_domains, result))
}

fn remap_bvars(
    expr: &ReferenceCoreExpr,
    source_ctx_len: usize,
    target_ctx_len: usize,
    source_to_target: &[usize],
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    match expr {
        ReferenceCoreExpr::Sort(level) => Ok(ReferenceCoreExpr::Sort(level.clone())),
        ReferenceCoreExpr::BVar(index) => {
            let index = *index as usize;
            if index >= source_ctx_len {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                ));
            }
            let source_abs = source_ctx_len - 1 - index;
            let target_abs = source_to_target.get(source_abs).copied().ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                )
            })?;
            bvar_for_abs(target_ctx_len, target_abs, offset)
        }
        ReferenceCoreExpr::Const { global_ref, levels } => Ok(ReferenceCoreExpr::Const {
            global_ref: global_ref.clone(),
            levels: levels.clone(),
        }),
        ReferenceCoreExpr::App(fun, arg) => Ok(ReferenceCoreExpr::App(
            Arc::new(remap_bvars(
                fun,
                source_ctx_len,
                target_ctx_len,
                source_to_target,
                offset,
            )?),
            Arc::new(remap_bvars(
                arg,
                source_ctx_len,
                target_ctx_len,
                source_to_target,
                offset,
            )?),
        )),
        ReferenceCoreExpr::Lam { ty, body } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(ReferenceCoreExpr::Lam {
                ty: Arc::new(remap_bvars(
                    ty,
                    source_ctx_len,
                    target_ctx_len,
                    source_to_target,
                    offset,
                )?),
                body: Arc::new(remap_bvars(
                    body,
                    source_ctx_len + 1,
                    target_ctx_len + 1,
                    &body_map,
                    offset,
                )?),
            })
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(ReferenceCoreExpr::Pi {
                ty: Arc::new(remap_bvars(
                    ty,
                    source_ctx_len,
                    target_ctx_len,
                    source_to_target,
                    offset,
                )?),
                body: Arc::new(remap_bvars(
                    body,
                    source_ctx_len + 1,
                    target_ctx_len + 1,
                    &body_map,
                    offset,
                )?),
            })
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(ReferenceCoreExpr::Let {
                ty: Arc::new(remap_bvars(
                    ty,
                    source_ctx_len,
                    target_ctx_len,
                    source_to_target,
                    offset,
                )?),
                value: Arc::new(remap_bvars(
                    value,
                    source_ctx_len,
                    target_ctx_len,
                    source_to_target,
                    offset,
                )?),
                body: Arc::new(remap_bvars(
                    body,
                    source_ctx_len + 1,
                    target_ctx_len + 1,
                    &body_map,
                    offset,
                )?),
            })
        }
    }
}

fn is_direct_recursive_domain(
    data: &ReferenceInductiveSignature,
    domain: &ReferenceCoreExpr,
    ctx_len: usize,
    offset: usize,
) -> DecodeResult<bool> {
    Ok(direct_recursive_index_args(data, domain, ctx_len, offset).is_ok())
}

fn recursive_occurrences_strictly_positive(
    cert: &DecodedModuleCertificate,
    inductives: &BTreeMap<usize, ReferenceInductiveSignature>,
    data: &ReferenceInductiveSignature,
    domain: &ReferenceCoreExpr,
    ctx_len: usize,
    offset: usize,
) -> DecodeResult<bool> {
    if direct_recursive_index_args(data, domain, ctx_len, offset).is_ok() {
        return Ok(true);
    }
    Ok(match domain {
        ReferenceCoreExpr::Sort(_) | ReferenceCoreExpr::BVar(_) => true,
        ReferenceCoreExpr::Const { global_ref, .. } => global_ref != &data.global_ref,
        ReferenceCoreExpr::App(_, _) => {
            let (head, args) = collect_apps(domain);
            let ReferenceCoreExpr::Const { global_ref, .. } = head else {
                return Ok(!contains_inductive_const(domain, data));
            };
            let Some(functor) = approved_nested_functor(cert, inductives, global_ref, args.len())
            else {
                return Ok(!contains_inductive_const(domain, data));
            };
            let mut allowed = true;
            for (index, arg) in args.iter().enumerate() {
                if functor.positive_args.contains(&index) {
                    allowed &= recursive_occurrences_strictly_positive(
                        cert, inductives, data, arg, ctx_len, offset,
                    )?;
                } else {
                    allowed &= !contains_inductive_const(arg, data);
                }
            }
            allowed
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            !contains_inductive_const(ty, data)
                && recursive_occurrences_strictly_positive(
                    cert,
                    inductives,
                    data,
                    body,
                    ctx_len + 1,
                    offset,
                )?
        }
        ReferenceCoreExpr::Lam { .. } | ReferenceCoreExpr::Let { .. } => {
            !contains_inductive_const(domain, data)
        }
    })
}

fn mutual_recursive_occurrences_strictly_positive(
    cert: &DecodedModuleCertificate,
    inductives: &BTreeMap<usize, ReferenceInductiveSignature>,
    block: &[ReferenceInductiveSignature],
    domain: &ReferenceCoreExpr,
    ctx_len: usize,
    offset: usize,
) -> DecodeResult<bool> {
    if direct_mutual_recursive_index_args(block, domain, ctx_len, offset)?.is_some() {
        return Ok(true);
    }
    Ok(match domain {
        ReferenceCoreExpr::Sort(_) | ReferenceCoreExpr::BVar(_) => true,
        ReferenceCoreExpr::Const { global_ref, .. } => block
            .iter()
            .all(|inductive| global_ref != &inductive.global_ref),
        ReferenceCoreExpr::App(_, _) => {
            let (head, args) = collect_apps(domain);
            let ReferenceCoreExpr::Const { global_ref, .. } = head else {
                return Ok(!contains_any_inductive_const(domain, block));
            };
            let Some(functor) = approved_nested_functor(cert, inductives, global_ref, args.len())
            else {
                return Ok(!contains_any_inductive_const(domain, block));
            };
            let mut allowed = true;
            for (index, arg) in args.iter().enumerate() {
                if functor.positive_args.contains(&index) {
                    allowed &= mutual_recursive_occurrences_strictly_positive(
                        cert, inductives, block, arg, ctx_len, offset,
                    )?;
                } else {
                    allowed &= !contains_any_inductive_const(arg, block);
                }
            }
            allowed
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            !contains_any_inductive_const(ty, block)
                && mutual_recursive_occurrences_strictly_positive(
                    cert,
                    inductives,
                    block,
                    body,
                    ctx_len + 1,
                    offset,
                )?
        }
        ReferenceCoreExpr::Lam { .. } | ReferenceCoreExpr::Let { .. } => {
            !contains_any_inductive_const(domain, block)
        }
    })
}

struct ReferenceApprovedNestedFunctor {
    name: &'static str,
    arity: usize,
    positive_args: &'static [usize],
}

const REFERENCE_UNARY_POSITIVE_ARGS: &[usize] = &[0];
const REFERENCE_BINARY_POSITIVE_ARGS: &[usize] = &[0, 1];
const REFERENCE_APPROVED_NESTED_FUNCTORS: &[ReferenceApprovedNestedFunctor] = &[
    ReferenceApprovedNestedFunctor {
        name: "List",
        arity: 1,
        positive_args: REFERENCE_UNARY_POSITIVE_ARGS,
    },
    ReferenceApprovedNestedFunctor {
        name: "Option",
        arity: 1,
        positive_args: REFERENCE_UNARY_POSITIVE_ARGS,
    },
    ReferenceApprovedNestedFunctor {
        name: "Prod",
        arity: 2,
        positive_args: REFERENCE_BINARY_POSITIVE_ARGS,
    },
];

fn approved_nested_functor(
    cert: &DecodedModuleCertificate,
    inductives: &BTreeMap<usize, ReferenceInductiveSignature>,
    global_ref: &ReferenceCoreGlobalRef,
    arity: usize,
) -> Option<&'static ReferenceApprovedNestedFunctor> {
    let (name, data) = match global_ref {
        ReferenceCoreGlobalRef::Local { decl_index } => {
            cert.declarations.get(*decl_index).and_then(|decl| {
                inductives.get(decl_index).map(|data| {
                    (
                        cert.name_table[decl.value.decl.name_id()].value.dotted(),
                        data,
                    )
                })
            })?
        }
        ReferenceCoreGlobalRef::Builtin { .. }
        | ReferenceCoreGlobalRef::Imported { .. }
        | ReferenceCoreGlobalRef::LocalGenerated { .. } => return None,
    };
    let functor = REFERENCE_APPROVED_NESTED_FUNCTORS
        .iter()
        .find(|functor| functor.name == name && functor.arity == arity)?;
    reference_approved_functor_decl_is_valid(data, functor.name).then_some(functor)
}

fn reference_approved_functor_decl_is_valid(
    data: &ReferenceInductiveSignature,
    name: &str,
) -> bool {
    match name {
        "List" => reference_approved_list_decl(data),
        "Option" => reference_approved_option_decl(data),
        "Prod" => reference_approved_prod_decl(data),
        _ => false,
    }
}

fn reference_level_param(data: &ReferenceInductiveSignature) -> Option<ReferenceCoreLevel> {
    data.universe_params
        .first()
        .cloned()
        .map(ReferenceCoreLevel::Param)
}

fn reference_const_app(
    data: &ReferenceInductiveSignature,
    level: ReferenceCoreLevel,
    args: Vec<ReferenceCoreExpr>,
) -> ReferenceCoreExpr {
    apps(
        ReferenceCoreExpr::Const {
            global_ref: data.global_ref.clone(),
            levels: vec![level],
        },
        args,
    )
}

fn reference_sort(level: ReferenceCoreLevel) -> ReferenceCoreExpr {
    ReferenceCoreExpr::Sort(level)
}

fn reference_pi(ty: ReferenceCoreExpr, body: ReferenceCoreExpr) -> ReferenceCoreExpr {
    ReferenceCoreExpr::Pi {
        ty: Arc::new(ty),
        body: Arc::new(body),
    }
}

fn reference_name_eq(name: &ReferenceModuleName, dotted: &str) -> bool {
    name.dotted() == dotted
}

fn reference_approved_list_decl(data: &ReferenceInductiveSignature) -> bool {
    let Some(u) = reference_level_param(data) else {
        return false;
    };
    data.universe_params.len() == 1
        && data.universe_constraints.is_empty()
        && data.params == [reference_sort(u.clone())]
        && data.indices.is_empty()
        && data.sort == u
        && data.constructors.len() == 2
        && reference_name_eq(&data.constructors[0].name, "List.nil")
        && data.constructors[0].ty
            == reference_pi(
                reference_sort(u.clone()),
                reference_const_app(data, u.clone(), vec![ReferenceCoreExpr::BVar(0)]),
            )
        && reference_name_eq(&data.constructors[1].name, "List.cons")
        && data.constructors[1].ty
            == reference_pi(
                reference_sort(u.clone()),
                reference_pi(
                    ReferenceCoreExpr::BVar(0),
                    reference_pi(
                        reference_const_app(data, u.clone(), vec![ReferenceCoreExpr::BVar(1)]),
                        reference_const_app(data, u, vec![ReferenceCoreExpr::BVar(2)]),
                    ),
                ),
            )
}

fn reference_approved_option_decl(data: &ReferenceInductiveSignature) -> bool {
    let Some(u) = reference_level_param(data) else {
        return false;
    };
    data.universe_params.len() == 1
        && data.universe_constraints.is_empty()
        && data.params == [reference_sort(u.clone())]
        && data.indices.is_empty()
        && data.sort == u
        && data.constructors.len() == 2
        && reference_name_eq(&data.constructors[0].name, "Option.none")
        && data.constructors[0].ty
            == reference_pi(
                reference_sort(u.clone()),
                reference_const_app(data, u.clone(), vec![ReferenceCoreExpr::BVar(0)]),
            )
        && reference_name_eq(&data.constructors[1].name, "Option.some")
        && data.constructors[1].ty
            == reference_pi(
                reference_sort(u.clone()),
                reference_pi(
                    ReferenceCoreExpr::BVar(0),
                    reference_const_app(data, u, vec![ReferenceCoreExpr::BVar(1)]),
                ),
            )
}

fn reference_approved_prod_decl(data: &ReferenceInductiveSignature) -> bool {
    let Some(u) = reference_level_param(data) else {
        return false;
    };
    data.universe_params.len() == 1
        && data.universe_constraints.is_empty()
        && data.params == [reference_sort(u.clone()), reference_sort(u.clone())]
        && data.indices.is_empty()
        && data.sort == u
        && data.constructors.len() == 1
        && reference_name_eq(&data.constructors[0].name, "Prod.mk")
        && data.constructors[0].ty
            == reference_pi(
                reference_sort(u.clone()),
                reference_pi(
                    reference_sort(u.clone()),
                    reference_pi(
                        ReferenceCoreExpr::BVar(1),
                        reference_pi(
                            ReferenceCoreExpr::BVar(1),
                            reference_const_app(
                                data,
                                u,
                                vec![ReferenceCoreExpr::BVar(3), ReferenceCoreExpr::BVar(2)],
                            ),
                        ),
                    ),
                ),
            )
}

fn direct_recursive_index_args(
    data: &ReferenceInductiveSignature,
    domain: &ReferenceCoreExpr,
    ctx_len: usize,
    offset: usize,
) -> DecodeResult<Vec<ReferenceCoreExpr>> {
    let (head, args) = collect_apps(domain);
    let levels = match head {
        ReferenceCoreExpr::Const { global_ref, levels } if global_ref == &data.global_ref => levels,
        _ => {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMinor,
            ));
        }
    };

    let expected_levels: Vec<_> = data
        .universe_params
        .iter()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .collect();
    if *levels != expected_levels || args.len() != data.params.len() + data.indices.len() {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        ));
    }

    for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
        let expected = bvar_for_abs(ctx_len, param_index, offset)?;
        if arg != &expected {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMinor,
            ));
        }
    }

    if args.iter().all(|arg| !contains_inductive_const(arg, data)) {
        Ok(args[data.params.len()..].to_vec())
    } else {
        Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        ))
    }
}

fn direct_mutual_recursive_index_args(
    block: &[ReferenceInductiveSignature],
    domain: &ReferenceCoreExpr,
    ctx_len: usize,
    offset: usize,
) -> DecodeResult<Option<(usize, Vec<ReferenceCoreExpr>)>> {
    for (family_index, data) in block.iter().enumerate() {
        if let Ok(indices) = direct_recursive_index_args(data, domain, ctx_len, offset) {
            return Ok(Some((family_index, indices)));
        }
    }
    Ok(None)
}

fn constructor_result_index_args(
    data: &ReferenceInductiveSignature,
    result: &ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<Vec<ReferenceCoreExpr>> {
    let (head, args) = collect_apps(result);
    let levels = match head {
        ReferenceCoreExpr::Const { global_ref, levels } if global_ref == &data.global_ref => levels,
        _ => {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadRecursorMinor,
            ));
        }
    };
    let expected_levels: Vec<_> = data
        .universe_params
        .iter()
        .map(|param| ReferenceCoreLevel::Param(param.clone()))
        .collect();
    if *levels != expected_levels || args.len() != data.params.len() + data.indices.len() {
        return Err(ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            offset,
            ReferenceCheckReason::BadRecursorMinor,
        ));
    }
    Ok(args[data.params.len()..].to_vec())
}

fn instantiate_constructor_args(
    expr: &ReferenceCoreExpr,
    args_by_abs: &[ReferenceCoreExpr],
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    instantiate_constructor_args_at(expr, args_by_abs, 0, offset)
}

fn instantiate_constructor_args_at(
    expr: &ReferenceCoreExpr,
    args_by_abs: &[ReferenceCoreExpr],
    depth: u32,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    match expr {
        ReferenceCoreExpr::Sort(level) => Ok(ReferenceCoreExpr::Sort(level.clone())),
        ReferenceCoreExpr::BVar(index) => {
            if *index < depth {
                return Ok(ReferenceCoreExpr::BVar(*index));
            }
            let outer_index = (*index - depth) as usize;
            if outer_index >= args_by_abs.len() {
                return Err(ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::InvalidBVar,
                ));
            }
            let source_abs = args_by_abs.len() - 1 - outer_index;
            shift(&args_by_abs[source_abs], depth as i32, 0, offset)
        }
        ReferenceCoreExpr::Const { global_ref, levels } => Ok(ReferenceCoreExpr::Const {
            global_ref: global_ref.clone(),
            levels: levels.clone(),
        }),
        ReferenceCoreExpr::App(fun, arg) => Ok(ReferenceCoreExpr::App(
            Arc::new(instantiate_constructor_args_at(
                fun,
                args_by_abs,
                depth,
                offset,
            )?),
            Arc::new(instantiate_constructor_args_at(
                arg,
                args_by_abs,
                depth,
                offset,
            )?),
        )),
        ReferenceCoreExpr::Lam { ty, body } => Ok(ReferenceCoreExpr::Lam {
            ty: Arc::new(instantiate_constructor_args_at(
                ty,
                args_by_abs,
                depth,
                offset,
            )?),
            body: Arc::new(instantiate_constructor_args_at(
                body,
                args_by_abs,
                depth + 1,
                offset,
            )?),
        }),
        ReferenceCoreExpr::Pi { ty, body } => Ok(ReferenceCoreExpr::Pi {
            ty: Arc::new(instantiate_constructor_args_at(
                ty,
                args_by_abs,
                depth,
                offset,
            )?),
            body: Arc::new(instantiate_constructor_args_at(
                body,
                args_by_abs,
                depth + 1,
                offset,
            )?),
        }),
        ReferenceCoreExpr::Let { ty, value, body } => Ok(ReferenceCoreExpr::Let {
            ty: Arc::new(instantiate_constructor_args_at(
                ty,
                args_by_abs,
                depth,
                offset,
            )?),
            value: Arc::new(instantiate_constructor_args_at(
                value,
                args_by_abs,
                depth,
                offset,
            )?),
            body: Arc::new(instantiate_constructor_args_at(
                body,
                args_by_abs,
                depth + 1,
                offset,
            )?),
        }),
    }
}

fn contains_inductive_const(expr: &ReferenceCoreExpr, data: &ReferenceInductiveSignature) -> bool {
    match expr {
        ReferenceCoreExpr::Sort(_) | ReferenceCoreExpr::BVar(_) => false,
        ReferenceCoreExpr::Const { global_ref, .. } => global_ref == &data.global_ref,
        ReferenceCoreExpr::App(fun, arg) => {
            contains_inductive_const(fun, data) || contains_inductive_const(arg, data)
        }
        ReferenceCoreExpr::Lam { ty, body } | ReferenceCoreExpr::Pi { ty, body } => {
            contains_inductive_const(ty, data) || contains_inductive_const(body, data)
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            contains_inductive_const(ty, data)
                || contains_inductive_const(value, data)
                || contains_inductive_const(body, data)
        }
    }
}

fn contains_any_inductive_const(
    expr: &ReferenceCoreExpr,
    inductives: &[ReferenceInductiveSignature],
) -> bool {
    inductives
        .iter()
        .any(|inductive| contains_inductive_const(expr, inductive))
}

fn subst_levels_expr(
    expr: &ReferenceCoreExpr,
    params: &[ReferenceModuleName],
    levels: &[ReferenceCoreLevel],
) -> ReferenceCoreExpr {
    if params.is_empty() {
        return expr.clone();
    }
    subst_levels_expr_changed(expr, params, levels).unwrap_or_else(|| expr.clone())
}

fn subst_levels_expr_rc(
    expr: &Arc<ReferenceCoreExpr>,
    params: &[ReferenceModuleName],
    levels: &[ReferenceCoreLevel],
) -> Option<Arc<ReferenceCoreExpr>> {
    subst_levels_expr_changed(expr, params, levels).map(Arc::new)
}

fn subst_levels_expr_changed(
    expr: &ReferenceCoreExpr,
    params: &[ReferenceModuleName],
    levels: &[ReferenceCoreLevel],
) -> Option<ReferenceCoreExpr> {
    match expr {
        ReferenceCoreExpr::Sort(level) => {
            subst_level_changed(level, params, levels).map(ReferenceCoreExpr::Sort)
        }
        ReferenceCoreExpr::BVar(_) => None,
        ReferenceCoreExpr::Const {
            global_ref,
            levels: expr_levels,
        } => {
            let mut changed = false;
            let substituted = expr_levels
                .iter()
                .map(|level| match subst_level_changed(level, params, levels) {
                    Some(level) => {
                        changed = true;
                        level
                    }
                    None => level.clone(),
                })
                .collect::<Vec<_>>();
            changed.then(|| ReferenceCoreExpr::Const {
                global_ref: global_ref.clone(),
                levels: substituted,
            })
        }
        ReferenceCoreExpr::App(fun, arg) => {
            let new_fun = subst_levels_expr_rc(fun, params, levels);
            let new_arg = subst_levels_expr_rc(arg, params, levels);
            if new_fun.is_none() && new_arg.is_none() {
                return None;
            }
            Some(ReferenceCoreExpr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            ))
        }
        ReferenceCoreExpr::Lam { ty, body } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_body.is_none() {
                return None;
            }
            Some(ReferenceCoreExpr::Lam {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_body.is_none() {
                return None;
            }
            Some(ReferenceCoreExpr::Pi {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_value = subst_levels_expr_rc(value, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return None;
            }
            Some(ReferenceCoreExpr::Let {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
    }
}

fn subst_level_changed(
    level: &ReferenceCoreLevel,
    params: &[ReferenceModuleName],
    levels: &[ReferenceCoreLevel],
) -> Option<ReferenceCoreLevel> {
    match level {
        ReferenceCoreLevel::Zero => None,
        ReferenceCoreLevel::Succ(inner) => subst_level_changed(inner, params, levels)
            .map(|inner| ReferenceCoreLevel::Succ(Arc::new(inner))),
        ReferenceCoreLevel::Max(lhs, rhs) => {
            let new_lhs = subst_level_changed(lhs, params, levels);
            let new_rhs = subst_level_changed(rhs, params, levels);
            if new_lhs.is_none() && new_rhs.is_none() {
                return None;
            }
            Some(ReferenceCoreLevel::Max(
                new_lhs.map(Arc::new).unwrap_or_else(|| Arc::clone(lhs)),
                new_rhs.map(Arc::new).unwrap_or_else(|| Arc::clone(rhs)),
            ))
        }
        ReferenceCoreLevel::IMax(lhs, rhs) => {
            let new_lhs = subst_level_changed(lhs, params, levels);
            let new_rhs = subst_level_changed(rhs, params, levels);
            if new_lhs.is_none() && new_rhs.is_none() {
                return None;
            }
            Some(ReferenceCoreLevel::IMax(
                new_lhs.map(Arc::new).unwrap_or_else(|| Arc::clone(lhs)),
                new_rhs.map(Arc::new).unwrap_or_else(|| Arc::clone(rhs)),
            ))
        }
        ReferenceCoreLevel::Param(name) => params
            .iter()
            .position(|param| param == name)
            .map(|index| levels[index].clone()),
    }
}

fn shift(
    expr: &ReferenceCoreExpr,
    amount: i32,
    cutoff: u32,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    if amount == 0 {
        return Ok(expr.clone());
    }
    Ok(shift_changed(expr, amount, cutoff, offset)?.unwrap_or_else(|| expr.clone()))
}

fn shift_rc(
    expr: &Arc<ReferenceCoreExpr>,
    amount: i32,
    cutoff: u32,
    offset: usize,
) -> DecodeResult<Option<Arc<ReferenceCoreExpr>>> {
    Ok(shift_changed(expr, amount, cutoff, offset)?.map(Arc::new))
}

fn shift_changed(
    expr: &ReferenceCoreExpr,
    amount: i32,
    cutoff: u32,
    offset: usize,
) -> DecodeResult<Option<ReferenceCoreExpr>> {
    match expr {
        ReferenceCoreExpr::Sort(_) | ReferenceCoreExpr::Const { .. } => Ok(None),
        ReferenceCoreExpr::BVar(index) => {
            if *index < cutoff {
                Ok(None)
            } else {
                let shifted = *index as i32 + amount;
                if shifted < 0 {
                    Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::InvalidBVar,
                    ))
                } else {
                    Ok(Some(ReferenceCoreExpr::BVar(shifted as u32)))
                }
            }
        }
        ReferenceCoreExpr::App(fun, arg) => {
            let new_fun = shift_rc(fun, amount, cutoff, offset)?;
            let new_arg = shift_rc(arg, amount, cutoff, offset)?;
            if new_fun.is_none() && new_arg.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            )))
        }
        ReferenceCoreExpr::Lam { ty, body } => {
            let new_ty = shift_rc(ty, amount, cutoff, offset)?;
            let new_body = shift_rc(body, amount, cutoff + 1, offset)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Lam {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            let new_ty = shift_rc(ty, amount, cutoff, offset)?;
            let new_body = shift_rc(body, amount, cutoff + 1, offset)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Pi {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            let new_ty = shift_rc(ty, amount, cutoff, offset)?;
            let new_value = shift_rc(value, amount, cutoff, offset)?;
            let new_body = shift_rc(body, amount, cutoff + 1, offset)?;
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Let {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
    }
}

fn substitute(
    expr: &ReferenceCoreExpr,
    target: u32,
    replacement: &ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    Ok(substitute_changed(expr, target, replacement, offset)?.unwrap_or_else(|| expr.clone()))
}

fn substitute_rc(
    expr: &Arc<ReferenceCoreExpr>,
    target: u32,
    replacement: &ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<Option<Arc<ReferenceCoreExpr>>> {
    Ok(substitute_changed(expr, target, replacement, offset)?.map(Arc::new))
}

fn substitute_changed(
    expr: &ReferenceCoreExpr,
    target: u32,
    replacement: &ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<Option<ReferenceCoreExpr>> {
    match expr {
        ReferenceCoreExpr::Sort(_) | ReferenceCoreExpr::Const { .. } => Ok(None),
        ReferenceCoreExpr::BVar(index) if *index == target => {
            shift(replacement, target as i32, 0, offset).map(Some)
        }
        ReferenceCoreExpr::BVar(index) if *index > target => {
            Ok(Some(ReferenceCoreExpr::BVar(index - 1)))
        }
        ReferenceCoreExpr::BVar(_) => Ok(None),
        ReferenceCoreExpr::App(fun, arg) => {
            let new_fun = substitute_rc(fun, target, replacement, offset)?;
            let new_arg = substitute_rc(arg, target, replacement, offset)?;
            if new_fun.is_none() && new_arg.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            )))
        }
        ReferenceCoreExpr::Lam { ty, body } => {
            let new_ty = substitute_rc(ty, target, replacement, offset)?;
            let new_body = substitute_rc(body, target + 1, replacement, offset)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Lam {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        ReferenceCoreExpr::Pi { ty, body } => {
            let new_ty = substitute_rc(ty, target, replacement, offset)?;
            let new_body = substitute_rc(body, target + 1, replacement, offset)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Pi {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        ReferenceCoreExpr::Let { ty, value, body } => {
            let new_ty = substitute_rc(ty, target, replacement, offset)?;
            let new_value = substitute_rc(value, target, replacement, offset)?;
            let new_body = substitute_rc(body, target + 1, replacement, offset)?;
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(ReferenceCoreExpr::Let {
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
    }
}

fn instantiate(
    body: &ReferenceCoreExpr,
    value: &ReferenceCoreExpr,
    offset: usize,
) -> DecodeResult<ReferenceCoreExpr> {
    substitute(body, 0, value, offset)
}

#[derive(Default)]
struct UsedTables {
    names: BTreeSet<ReferenceModuleName>,
    levels: BTreeSet<usize>,
    terms: BTreeSet<usize>,
}

impl UsedTables {
    fn new() -> Self {
        Self::default()
    }
}

fn push_term(term: usize, used: &mut UsedTables, stack: &mut Vec<usize>) {
    if used.terms.insert(term) {
        stack.push(term);
    }
}

fn push_level(level: usize, used: &mut UsedTables, stack: &mut Vec<usize>) {
    if used.levels.insert(level) {
        stack.push(level);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportEntry {
    module: ReferenceModuleName,
    export_hash: ReferenceHash,
    certificate_hash: Option<ReferenceHash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LevelNode {
    Zero,
    Succ(usize),
    Max(usize, usize),
    IMax(usize, usize),
    Param(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TermNode {
    Sort(usize),
    BVar(u32),
    Const {
        global_ref: GlobalRef,
        levels: Vec<usize>,
    },
    App(usize, usize),
    Lam {
        ty: usize,
        body: usize,
    },
    Pi {
        ty: usize,
        body: usize,
    },
    Let {
        ty: usize,
        value: usize,
        body: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GlobalRef {
    Builtin {
        name: usize,
        decl_interface_hash: ReferenceHash,
    },
    Imported {
        import_index: usize,
        name: usize,
        decl_interface_hash: ReferenceHash,
    },
    Local {
        decl_index: usize,
    },
    LocalGenerated {
        decl_index: usize,
        name: usize,
    },
}

impl Ord for GlobalRef {
    fn cmp(&self, other: &Self) -> Ordering {
        global_ref_order_key(self).cmp(&global_ref_order_key(other))
    }
}

impl PartialOrd for GlobalRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug)]
struct DeclCert {
    decl: DeclPayload,
    dependencies: Vec<DependencyEntry>,
    axiom_dependencies: Vec<AxiomRef>,
    hashes: DeclHashes,
}

#[derive(Clone, Debug)]
enum DeclPayload {
    Axiom {
        name: usize,
        universe_params: Vec<usize>,
        ty: usize,
    },
    AxiomConstrained {
        name: usize,
        universe_params: Vec<usize>,
        universe_constraints: Vec<UniverseConstraintSpec>,
        ty: usize,
    },
    Def {
        name: usize,
        universe_params: Vec<usize>,
        ty: usize,
        value: usize,
        reducibility: CertReducibility,
    },
    DefConstrained {
        name: usize,
        universe_params: Vec<usize>,
        universe_constraints: Vec<UniverseConstraintSpec>,
        ty: usize,
        value: usize,
        reducibility: CertReducibility,
    },
    Theorem {
        name: usize,
        universe_params: Vec<usize>,
        ty: usize,
        proof: usize,
        opacity: Opacity,
    },
    TheoremConstrained {
        name: usize,
        universe_params: Vec<usize>,
        universe_constraints: Vec<UniverseConstraintSpec>,
        ty: usize,
        proof: usize,
        opacity: Opacity,
    },
    Inductive {
        name: usize,
        universe_params: Vec<usize>,
        params: Vec<BinderType>,
        indices: Vec<BinderType>,
        sort: usize,
        constructors: Vec<ConstructorSpec>,
        recursor: Option<RecursorSpec>,
    },
    InductiveConstrained {
        name: usize,
        universe_params: Vec<usize>,
        universe_constraints: Vec<UniverseConstraintSpec>,
        params: Vec<BinderType>,
        indices: Vec<BinderType>,
        sort: usize,
        constructors: Vec<ConstructorSpec>,
        recursor: Option<RecursorSpec>,
    },
    MutualInductiveBlock {
        name: usize,
        universe_params: Vec<usize>,
        universe_constraints: Vec<UniverseConstraintSpec>,
        inductives: Vec<MutualInductiveSpec>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum UniverseConstraintRelation {
    Le,
    Eq,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ReferenceUniverseConstraint {
    pub(crate) lhs: ReferenceCoreLevel,
    pub(crate) relation: UniverseConstraintRelation,
    pub(crate) rhs: ReferenceCoreLevel,
}

#[allow(dead_code)]
impl ReferenceUniverseConstraint {
    pub(crate) fn le(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> Self {
        Self {
            lhs,
            relation: UniverseConstraintRelation::Le,
            rhs,
        }
    }

    pub(crate) fn eq(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> Self {
        Self {
            lhs,
            relation: UniverseConstraintRelation::Eq,
            rhs,
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReferenceUniverseContext {
    pub(crate) params: Vec<ReferenceModuleName>,
    pub(crate) constraints: Vec<ReferenceUniverseConstraint>,
    closure: ReferenceUniverseConstraintClosure,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct ReferenceUniverseConstraintClosure {
    dist: Vec<Vec<Option<i128>>>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ReferenceAtomBase {
    Zero,
    Param(ReferenceModuleName),
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReferenceAtom {
    base: ReferenceAtomBase,
    offset: u64,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct ReferenceAtomInequality {
    lhs: ReferenceAtom,
    rhs: ReferenceAtom,
}

#[allow(dead_code)]
impl ReferenceUniverseContext {
    pub(crate) fn new(
        params: Vec<ReferenceModuleName>,
        constraints: Vec<ReferenceUniverseConstraint>,
        offset: usize,
    ) -> DecodeResult<Self> {
        if constraints.is_empty() {
            return Self::from_params(params, offset);
        }
        validate_reference_universe_params(&params, offset)?;
        ensure_reference_universe_node_limit(params.len(), offset)?;
        ensure_reference_universe_constraints_wf(&params, &constraints, offset)?;

        let param_indices = reference_universe_param_indices(&params);
        let mut edge_count = params.len();
        let mut closure = ReferenceUniverseConstraintClosure::with_lower_bounds(params.len());
        for constraint in &constraints {
            let inequalities = decompose_reference_constraint(constraint, offset)?;
            edge_count = edge_count.checked_add(inequalities.len()).ok_or_else(|| {
                ReferenceCheckError::type_check(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::ResourceLimit,
                )
            })?;
            ensure_reference_universe_edge_limit(edge_count, offset)?;
            for inequality in inequalities {
                let from = reference_atom_base_index(&inequality.rhs.base, &param_indices, offset)?;
                let to = reference_atom_base_index(&inequality.lhs.base, &param_indices, offset)?;
                let weight = i128::from(reference_offset_bound(&inequality.rhs, offset)?)
                    - i128::from(reference_offset_bound(&inequality.lhs, offset)?);
                closure.add_edge(from, to, weight);
            }
        }
        closure.close(offset)?;
        Ok(Self {
            params,
            constraints,
            closure,
        })
    }

    pub(crate) fn from_params(
        params: Vec<ReferenceModuleName>,
        offset: usize,
    ) -> DecodeResult<Self> {
        validate_reference_universe_params(&params, offset)?;
        ensure_reference_universe_node_limit(params.len(), offset)?;
        ensure_reference_universe_edge_limit(params.len(), offset)?;
        let param_count = params.len();
        Ok(Self {
            params,
            constraints: Vec::new(),
            closure: ReferenceUniverseConstraintClosure::with_lower_bounds(param_count),
        })
    }

    pub(crate) fn empty() -> Self {
        Self {
            params: Vec::new(),
            constraints: Vec::new(),
            closure: ReferenceUniverseConstraintClosure::with_lower_bounds(0),
        }
    }

    pub(crate) fn ensure_satisfiable(&self) -> DecodeResult<()> {
        Ok(())
    }

    pub(crate) fn entails(
        &self,
        obligations: &[ReferenceUniverseConstraint],
        offset: usize,
    ) -> DecodeResult<()> {
        if obligations.is_empty() {
            return Ok(());
        }
        ensure_reference_universe_constraints_wf(&self.params, obligations, offset)?;
        let param_indices = reference_universe_param_indices(&self.params);
        for obligation in obligations {
            for inequality in decompose_reference_constraint(obligation, offset)? {
                let from = reference_atom_base_index(&inequality.rhs.base, &param_indices, offset)?;
                let to = reference_atom_base_index(&inequality.lhs.base, &param_indices, offset)?;
                let bound = i128::from(reference_offset_bound(&inequality.rhs, offset)?)
                    - i128::from(reference_offset_bound(&inequality.lhs, offset)?);
                if !self.closure.entails(from, to, bound) {
                    return Err(ReferenceCheckError::type_check(
                        ReferenceCertificateSection::Declarations,
                        offset,
                        ReferenceCheckReason::UniverseConstraintViolation,
                    ));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn substitute_constraints(
        &self,
        params: &[ReferenceModuleName],
        levels: &[ReferenceCoreLevel],
        constraints: &[ReferenceUniverseConstraint],
        offset: usize,
    ) -> DecodeResult<Vec<ReferenceUniverseConstraint>> {
        if params.len() != levels.len() {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::BadUniverseArity,
            ));
        }
        validate_reference_universe_params(params, offset)?;
        ensure_reference_universe_constraints_wf(params, constraints, offset)?;
        for level in levels {
            ensure_level_wf(level, &self.params, offset)?;
        }
        let mut obligations = constraints
            .iter()
            .map(|constraint| ReferenceUniverseConstraint {
                lhs: substitute_reference_level(&constraint.lhs, params, levels),
                relation: constraint.relation,
                rhs: substitute_reference_level(&constraint.rhs, params, levels),
            })
            .collect::<Vec<_>>();
        obligations.sort();
        obligations.dedup();
        Ok(obligations)
    }
}

#[allow(dead_code)]
impl ReferenceUniverseConstraintClosure {
    fn with_lower_bounds(param_count: usize) -> Self {
        let node_count = param_count + 1;
        let mut dist = vec![vec![None; node_count]; node_count];
        for (index, row) in dist.iter_mut().enumerate() {
            row[index] = Some(0);
        }
        for row in dist.iter_mut().take(node_count).skip(1) {
            row[0] = Some(0);
        }
        Self { dist }
    }

    fn add_edge(&mut self, from: usize, to: usize, weight: i128) {
        let current = &mut self.dist[from][to];
        if current.is_none_or(|old| weight < old) {
            *current = Some(weight);
        }
    }

    fn close(&mut self, offset: usize) -> DecodeResult<()> {
        let len = self.dist.len();
        for k in 0..len {
            for i in 0..len {
                let Some(ik) = self.dist[i][k] else {
                    continue;
                };
                for j in 0..len {
                    let Some(kj) = self.dist[k][j] else {
                        continue;
                    };
                    let candidate = ik + kj;
                    if self.dist[i][j].is_none_or(|old| candidate < old) {
                        self.dist[i][j] = Some(candidate);
                    }
                }
            }
        }
        if (0..len).any(|index| self.dist[index][index].is_some_and(|bound| bound < 0)) {
            return Err(ReferenceCheckError::type_check(
                ReferenceCertificateSection::Declarations,
                offset,
                ReferenceCheckReason::UnsatisfiableUniverseConstraints,
            ));
        }
        Ok(())
    }

    fn entails(&self, from: usize, to: usize, bound: i128) -> bool {
        self.dist[from][to].is_some_and(|actual| actual <= bound)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct UniverseConstraintSpec {
    lhs: usize,
    relation: UniverseConstraintRelation,
    rhs: usize,
}

impl DeclPayload {
    fn name_id(&self) -> usize {
        match self {
            Self::Axiom { name, .. }
            | Self::AxiomConstrained { name, .. }
            | Self::Def { name, .. }
            | Self::DefConstrained { name, .. }
            | Self::Theorem { name, .. }
            | Self::TheoremConstrained { name, .. }
            | Self::Inductive { name, .. }
            | Self::InductiveConstrained { name, .. }
            | Self::MutualInductiveBlock { name, .. } => *name,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BinderType {
    ty: usize,
}

#[derive(Clone, Copy, Debug)]
struct ConstructorSpec {
    name: usize,
    ty: usize,
}

#[derive(Clone, Debug)]
struct MutualInductiveSpec {
    name: usize,
    params: Vec<BinderType>,
    indices: Vec<BinderType>,
    sort: usize,
    constructors: Vec<ConstructorSpec>,
    recursor: Option<RecursorSpec>,
}

#[derive(Clone, Debug)]
struct RecursorSpec {
    name: usize,
    universe_params: Vec<usize>,
    ty: usize,
    rules: RecursorRulesSpec,
}

#[derive(Clone, Copy, Debug)]
struct RecursorRulesSpec {
    minor_start: usize,
    major_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CertReducibility {
    Reducible,
    Opaque,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Opacity {
    Opaque,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DependencyEntry {
    global_ref: GlobalRef,
    decl_interface_hash: ReferenceHash,
}

impl Ord for DependencyEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        dependency_entry_order_key(self).cmp(&dependency_entry_order_key(other))
    }
}

impl PartialOrd for DependencyEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AxiomRef {
    global_ref: GlobalRef,
    name: usize,
    decl_interface_hash: ReferenceHash,
}

impl Ord for AxiomRef {
    fn cmp(&self, other: &Self) -> Ordering {
        axiom_ref_order_key(self).cmp(&axiom_ref_order_key(other))
    }
}

impl PartialOrd for AxiomRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug)]
struct DeclHashes {
    decl_interface_hash: ReferenceHash,
    decl_certificate_hash: ReferenceHash,
    decl_interface_hash_offset: usize,
    decl_certificate_hash_offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExportEntry {
    name: usize,
    kind: ExportKind,
    universe_params: Vec<usize>,
    universe_constraints: Vec<UniverseConstraintSpec>,
    ty: usize,
    body: Option<usize>,
    type_hash: ReferenceHash,
    body_hash: Option<ReferenceHash>,
    reducibility: Option<CertReducibility>,
    opacity: Option<Opacity>,
    decl_interface_hash: ReferenceHash,
    axiom_dependencies: Vec<AxiomRef>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExportKind {
    Axiom,
    Def,
    Theorem,
    Inductive,
    Constructor,
    Recursor,
}

#[derive(Clone, Debug)]
struct AxiomReport {
    per_declaration: Vec<DeclAxiomReport>,
    module_axioms: Vec<AxiomRef>,
    module_axioms_offset: usize,
    core_features: Vec<ReferenceCoreFeature>,
    core_features_offset: usize,
}

#[derive(Clone, Debug)]
struct DeclAxiomReport {
    decl_index: usize,
    direct_axioms: Vec<AxiomRef>,
    transitive_axioms: Vec<AxiomRef>,
    offset: usize,
}

#[derive(Clone, Copy, Debug)]
struct ModuleHashOffsets {
    export_hash_offset: usize,
    axiom_report_hash_offset: usize,
    certificate_hash_offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum RawLevel {
    Zero,
    Succ(Box<RawLevel>),
    Max(Box<RawLevel>, Box<RawLevel>),
    IMax(Box<RawLevel>, Box<RawLevel>),
    Param(String),
}

fn normalize_level(level: RawLevel) -> RawLevel {
    match level {
        RawLevel::Zero | RawLevel::Param(_) => level,
        RawLevel::Succ(inner) => RawLevel::Succ(Box::new(normalize_level(*inner))),
        RawLevel::Max(lhs, rhs) => {
            let lhs = normalize_level(*lhs);
            let rhs = normalize_level(*rhs);
            if lhs == rhs {
                return lhs;
            }
            if lhs == RawLevel::Zero {
                return rhs;
            }
            if rhs == RawLevel::Zero {
                return lhs;
            }
            match (level_as_nat(&lhs), level_as_nat(&rhs)) {
                (Some(lhs_nat), Some(rhs_nat)) => level_from_nat(lhs_nat.max(rhs_nat)),
                _ if rhs < lhs => RawLevel::Max(Box::new(rhs), Box::new(lhs)),
                _ => RawLevel::Max(Box::new(lhs), Box::new(rhs)),
            }
        }
        RawLevel::IMax(lhs, rhs) => {
            let lhs = normalize_level(*lhs);
            let rhs = normalize_level(*rhs);
            match rhs {
                RawLevel::Zero => RawLevel::Zero,
                RawLevel::Succ(inner) => normalize_level(RawLevel::Max(
                    Box::new(lhs),
                    Box::new(RawLevel::Succ(inner)),
                )),
                rhs => RawLevel::IMax(Box::new(lhs), Box::new(rhs)),
            }
        }
    }
}

fn level_as_nat(level: &RawLevel) -> Option<u32> {
    match level {
        RawLevel::Zero => Some(0),
        RawLevel::Succ(inner) => Some(level_as_nat(inner)? + 1),
        RawLevel::Max(_, _) | RawLevel::IMax(_, _) | RawLevel::Param(_) => None,
    }
}

fn level_from_nat(n: u32) -> RawLevel {
    (0..n).fold(RawLevel::Zero, |level, _| RawLevel::Succ(Box::new(level)))
}

fn raw_level_from_node(
    node: &LevelNode,
    previous: &[RawLevel],
    names: &[Located<ReferenceModuleName>],
) -> DecodeResult<RawLevel> {
    Ok(match node {
        LevelNode::Zero => RawLevel::Zero,
        LevelNode::Succ(inner) => RawLevel::Succ(Box::new(previous[*inner].clone())),
        LevelNode::Max(lhs, rhs) => RawLevel::Max(
            Box::new(previous[*lhs].clone()),
            Box::new(previous[*rhs].clone()),
        ),
        LevelNode::IMax(lhs, rhs) => RawLevel::IMax(
            Box::new(previous[*lhs].clone()),
            Box::new(previous[*rhs].clone()),
        ),
        LevelNode::Param(name) => RawLevel::Param(
            names
                .get(*name)
                .ok_or_else(|| {
                    ReferenceCheckError::malformed(
                        ReferenceCertificateSection::LevelTable,
                        0,
                        ReferenceCheckReason::DanglingReference,
                    )
                })?
                .value
                .dotted(),
        ),
    })
}

struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Decoder<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    const fn offset(&self) -> usize {
        self.offset
    }

    fn is_done(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn remaining_len(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    fn has_core_feature_report(&self) -> bool {
        let feature_report_len = self.remaining_len().saturating_sub(MODULE_HASH_TRAILER_LEN);
        let tag = CORE_FEATURE_REPORT_TAG.as_bytes();
        feature_report_len > tag.len()
            && self.bytes.get(self.offset) == Some(&(tag.len() as u8))
            && self.bytes.get(self.offset + 1..self.offset + 1 + tag.len()) == Some(tag)
    }

    fn module_certificate(&mut self) -> DecodeResult<DecodedModuleCertificate> {
        let header = self.header()?;
        let version = reference_certificate_format_version(&header).ok_or_else(|| {
            ReferenceCheckError::malformed(
                ReferenceCertificateSection::HeaderFormat,
                0,
                ReferenceCheckReason::FormatMismatch,
            )
        })?;
        let imports = self.imports()?;
        let name_table = self.name_table()?;
        let level_table = self.level_table()?;
        let term_table = self.term_table()?;
        let declarations = self.declarations()?;
        let export_block = self.export_block(version)?;
        let mut axiom_report = self.axiom_report()?;
        if self.has_core_feature_report() {
            let offset = self.offset;
            axiom_report.core_features = self.core_features()?;
            axiom_report.core_features_offset = offset;
        }
        let export_hash_offset = self.offset;
        let export_hash = self.hash(ReferenceCertificateSection::Hashes)?;
        let axiom_report_hash_offset = self.offset;
        let axiom_report_hash = self.hash(ReferenceCertificateSection::Hashes)?;
        let certificate_hash_offset = self.offset;
        let certificate_hash = self.hash(ReferenceCertificateSection::Hashes)?;
        let hashes = ReferenceModuleHashes {
            export_hash,
            axiom_report_hash,
            certificate_hash,
        };
        let hash_offsets = ModuleHashOffsets {
            export_hash_offset,
            axiom_report_hash_offset,
            certificate_hash_offset,
        };
        Ok(DecodedModuleCertificate {
            header,
            imports,
            name_table,
            level_table,
            term_table,
            declarations,
            export_block,
            axiom_report,
            hashes,
            hash_offsets,
        })
    }

    fn header(&mut self) -> DecodeResult<ReferenceCertificateHeader> {
        let format = self.string(ReferenceCertificateSection::HeaderFormat)?;
        let format_offset = self.offset;
        if format != REFERENCE_CERTIFICATE_FORMAT
            && format != REFERENCE_PREVIOUS_CERTIFICATE_FORMAT
            && format != REFERENCE_LEGACY_CERTIFICATE_FORMAT
        {
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::HeaderFormat,
                format_offset,
                ReferenceCheckReason::FormatMismatch,
            ));
        }
        let core_spec = self.string(ReferenceCertificateSection::HeaderCoreSpec)?;
        let core_matches_current =
            format == REFERENCE_CERTIFICATE_FORMAT && core_spec == REFERENCE_CORE_SPEC;
        let core_matches_previous = format == REFERENCE_PREVIOUS_CERTIFICATE_FORMAT
            && core_spec == REFERENCE_PREVIOUS_CORE_SPEC;
        let core_matches_legacy = format == REFERENCE_LEGACY_CERTIFICATE_FORMAT
            && core_spec == REFERENCE_LEGACY_CORE_SPEC;
        if !core_matches_current && !core_matches_previous && !core_matches_legacy {
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::HeaderCoreSpec,
                self.offset,
                ReferenceCheckReason::CoreSpecMismatch,
            ));
        }
        let module = self.name(ReferenceCertificateSection::HeaderModule)?;
        Ok(ReferenceCertificateHeader {
            format,
            core_spec,
            module,
        })
    }

    fn imports(&mut self) -> DecodeResult<Vec<Located<ImportEntry>>> {
        let len = self.bounded_len(ReferenceCertificateSection::Imports)?;
        let mut imports = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            imports.push(Located {
                value: ImportEntry {
                    module: self.name(ReferenceCertificateSection::Imports)?,
                    export_hash: self.hash(ReferenceCertificateSection::Imports)?,
                    certificate_hash: self.option_hash(ReferenceCertificateSection::Imports)?,
                },
                offset,
            });
        }
        Ok(imports)
    }

    fn name_table(&mut self) -> DecodeResult<Vec<Located<ReferenceModuleName>>> {
        let len = self.bounded_len(ReferenceCertificateSection::NameTable)?;
        let mut names = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            names.push(Located {
                value: self.name(ReferenceCertificateSection::NameTable)?,
                offset,
            });
        }
        Ok(names)
    }

    fn level_table(&mut self) -> DecodeResult<Vec<Located<LevelNode>>> {
        let len = self.bounded_len(ReferenceCertificateSection::LevelTable)?;
        let mut levels = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            let tag = self.byte(ReferenceCertificateSection::LevelTable)?;
            let value = match tag {
                0x00 => LevelNode::Zero,
                0x01 => LevelNode::Succ(self.usize(ReferenceCertificateSection::LevelTable)?),
                0x02 => LevelNode::Max(
                    self.usize(ReferenceCertificateSection::LevelTable)?,
                    self.usize(ReferenceCertificateSection::LevelTable)?,
                ),
                0x03 => LevelNode::IMax(
                    self.usize(ReferenceCertificateSection::LevelTable)?,
                    self.usize(ReferenceCertificateSection::LevelTable)?,
                ),
                0x04 => LevelNode::Param(self.usize(ReferenceCertificateSection::LevelTable)?),
                tag => {
                    return Err(ReferenceCheckError::malformed(
                        ReferenceCertificateSection::LevelTable,
                        offset,
                        ReferenceCheckReason::UnknownTag { tag },
                    ));
                }
            };
            levels.push(Located { value, offset });
        }
        Ok(levels)
    }

    fn term_table(&mut self) -> DecodeResult<Vec<Located<TermNode>>> {
        let len = self.bounded_len(ReferenceCertificateSection::TermTable)?;
        let mut terms = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            let tag = self.byte(ReferenceCertificateSection::TermTable)?;
            let value = match tag {
                0x00 => TermNode::Sort(self.usize(ReferenceCertificateSection::TermTable)?),
                0x01 => TermNode::BVar(self.u32(ReferenceCertificateSection::TermTable)?),
                0x02 => TermNode::Const {
                    global_ref: self.global_ref(ReferenceCertificateSection::TermTable)?,
                    levels: self.usize_vec(ReferenceCertificateSection::TermTable)?,
                },
                0x03 => TermNode::App(
                    self.usize(ReferenceCertificateSection::TermTable)?,
                    self.usize(ReferenceCertificateSection::TermTable)?,
                ),
                0x04 => TermNode::Lam {
                    ty: self.usize(ReferenceCertificateSection::TermTable)?,
                    body: self.usize(ReferenceCertificateSection::TermTable)?,
                },
                0x05 => TermNode::Pi {
                    ty: self.usize(ReferenceCertificateSection::TermTable)?,
                    body: self.usize(ReferenceCertificateSection::TermTable)?,
                },
                0x06 => TermNode::Let {
                    ty: self.usize(ReferenceCertificateSection::TermTable)?,
                    value: self.usize(ReferenceCertificateSection::TermTable)?,
                    body: self.usize(ReferenceCertificateSection::TermTable)?,
                },
                tag => {
                    return Err(ReferenceCheckError::malformed(
                        ReferenceCertificateSection::TermTable,
                        offset,
                        ReferenceCheckReason::UnknownTag { tag },
                    ));
                }
            };
            terms.push(Located { value, offset });
        }
        Ok(terms)
    }

    fn declarations(&mut self) -> DecodeResult<Vec<Located<DeclCert>>> {
        let len = self.bounded_len(ReferenceCertificateSection::Declarations)?;
        let mut declarations = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            let decl = self.decl_payload()?;
            let dependencies =
                self.dependency_entries(ReferenceCertificateSection::Declarations)?;
            let axiom_dependencies = self.axiom_refs(ReferenceCertificateSection::Declarations)?;
            let decl_interface_hash_offset = self.offset;
            let decl_interface_hash = self.hash(ReferenceCertificateSection::Declarations)?;
            let decl_certificate_hash_offset = self.offset;
            let decl_certificate_hash = self.hash(ReferenceCertificateSection::Declarations)?;
            declarations.push(Located {
                value: DeclCert {
                    decl,
                    dependencies,
                    axiom_dependencies,
                    hashes: DeclHashes {
                        decl_interface_hash,
                        decl_certificate_hash,
                        decl_interface_hash_offset,
                        decl_certificate_hash_offset,
                    },
                },
                offset,
            });
        }
        Ok(declarations)
    }

    fn decl_payload(&mut self) -> DecodeResult<DeclPayload> {
        let offset = self.offset;
        let tag = self.byte(ReferenceCertificateSection::Declarations)?;
        Ok(match tag {
            0x00 => DeclPayload::Axiom {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
            },
            0x10 => DeclPayload::AxiomConstrained {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
            },
            0x01 => DeclPayload::Def {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
                value: self.usize(ReferenceCertificateSection::Declarations)?,
                reducibility: self.reducibility(ReferenceCertificateSection::Declarations)?,
            },
            0x11 => DeclPayload::DefConstrained {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
                value: self.usize(ReferenceCertificateSection::Declarations)?,
                reducibility: self.reducibility(ReferenceCertificateSection::Declarations)?,
            },
            0x02 => DeclPayload::Theorem {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
                proof: self.usize(ReferenceCertificateSection::Declarations)?,
                opacity: self.opacity(ReferenceCertificateSection::Declarations)?,
            },
            0x12 => DeclPayload::TheoremConstrained {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
                proof: self.usize(ReferenceCertificateSection::Declarations)?,
                opacity: self.opacity(ReferenceCertificateSection::Declarations)?,
            },
            0x03 => {
                let name = self.usize(ReferenceCertificateSection::Declarations)?;
                let universe_params = self.usize_vec(ReferenceCertificateSection::Declarations)?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize(ReferenceCertificateSection::Declarations)?;
                let constructors_len =
                    self.bounded_len(ReferenceCertificateSection::Declarations)?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize(ReferenceCertificateSection::Declarations)?,
                        ty: self.usize(ReferenceCertificateSection::Declarations)?,
                    });
                }
                let recursor_offset = self.offset;
                let recursor = match self.byte(ReferenceCertificateSection::Declarations)? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize(ReferenceCertificateSection::Declarations)?,
                        universe_params: self
                            .usize_vec(ReferenceCertificateSection::Declarations)?,
                        ty: self.usize(ReferenceCertificateSection::Declarations)?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize(ReferenceCertificateSection::Declarations)?,
                            major_index: self.usize(ReferenceCertificateSection::Declarations)?,
                        },
                    }),
                    tag => {
                        return Err(ReferenceCheckError::malformed(
                            ReferenceCertificateSection::Declarations,
                            recursor_offset,
                            ReferenceCheckReason::UnknownTag { tag },
                        ));
                    }
                };
                DeclPayload::Inductive {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                }
            }
            0x13 => {
                let name = self.usize(ReferenceCertificateSection::Declarations)?;
                let universe_params = self.usize_vec(ReferenceCertificateSection::Declarations)?;
                let universe_constraints = self.universe_constraint_specs()?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize(ReferenceCertificateSection::Declarations)?;
                let constructors_len =
                    self.bounded_len(ReferenceCertificateSection::Declarations)?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize(ReferenceCertificateSection::Declarations)?,
                        ty: self.usize(ReferenceCertificateSection::Declarations)?,
                    });
                }
                let recursor_offset = self.offset;
                let recursor = match self.byte(ReferenceCertificateSection::Declarations)? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize(ReferenceCertificateSection::Declarations)?,
                        universe_params: self
                            .usize_vec(ReferenceCertificateSection::Declarations)?,
                        ty: self.usize(ReferenceCertificateSection::Declarations)?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize(ReferenceCertificateSection::Declarations)?,
                            major_index: self.usize(ReferenceCertificateSection::Declarations)?,
                        },
                    }),
                    tag => {
                        return Err(ReferenceCheckError::malformed(
                            ReferenceCertificateSection::Declarations,
                            recursor_offset,
                            ReferenceCheckReason::UnknownTag { tag },
                        ));
                    }
                };
                DeclPayload::InductiveConstrained {
                    name,
                    universe_params,
                    universe_constraints,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                }
            }
            0x04 => {
                let name = self.usize(ReferenceCertificateSection::Declarations)?;
                let universe_params = self.usize_vec(ReferenceCertificateSection::Declarations)?;
                let universe_constraints = self.universe_constraint_specs()?;
                let len = self.bounded_len(ReferenceCertificateSection::Declarations)?;
                let mut inductives = Vec::with_capacity(len);
                for _ in 0..len {
                    inductives.push(MutualInductiveSpec {
                        name: self.usize(ReferenceCertificateSection::Declarations)?,
                        params: self.binder_types()?,
                        indices: self.binder_types()?,
                        sort: self.usize(ReferenceCertificateSection::Declarations)?,
                        constructors: self.constructor_specs()?,
                        recursor: self.recursor_spec()?,
                    });
                }
                DeclPayload::MutualInductiveBlock {
                    name,
                    universe_params,
                    universe_constraints,
                    inductives,
                }
            }
            tag => {
                return Err(ReferenceCheckError::malformed(
                    ReferenceCertificateSection::Declarations,
                    offset,
                    ReferenceCheckReason::UnknownTag { tag },
                ));
            }
        })
    }

    fn universe_constraint_specs(&mut self) -> DecodeResult<Vec<UniverseConstraintSpec>> {
        self.universe_constraint_specs_in_section(ReferenceCertificateSection::Declarations)
    }

    fn universe_constraint_specs_in_section(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Vec<UniverseConstraintSpec>> {
        let len = self.bounded_len(section)?;
        (0..len)
            .map(|_| {
                let lhs = self.usize(section)?;
                let offset = self.offset;
                let relation = match self.byte(section)? {
                    0x00 => UniverseConstraintRelation::Le,
                    0x01 => UniverseConstraintRelation::Eq,
                    tag => {
                        return Err(ReferenceCheckError::malformed(
                            section,
                            offset,
                            ReferenceCheckReason::UnknownTag { tag },
                        ));
                    }
                };
                Ok(UniverseConstraintSpec {
                    lhs,
                    relation,
                    rhs: self.usize(section)?,
                })
            })
            .collect()
    }

    fn binder_types(&mut self) -> DecodeResult<Vec<BinderType>> {
        let len = self.bounded_len(ReferenceCertificateSection::Declarations)?;
        let mut binders = Vec::with_capacity(len);
        for _ in 0..len {
            binders.push(BinderType {
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
            });
        }
        Ok(binders)
    }

    fn constructor_specs(&mut self) -> DecodeResult<Vec<ConstructorSpec>> {
        let len = self.bounded_len(ReferenceCertificateSection::Declarations)?;
        let mut constructors = Vec::with_capacity(len);
        for _ in 0..len {
            constructors.push(ConstructorSpec {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
            });
        }
        Ok(constructors)
    }

    fn recursor_spec(&mut self) -> DecodeResult<Option<RecursorSpec>> {
        let recursor_offset = self.offset;
        match self.byte(ReferenceCertificateSection::Declarations)? {
            0x00 => Ok(None),
            0x01 => Ok(Some(RecursorSpec {
                name: self.usize(ReferenceCertificateSection::Declarations)?,
                universe_params: self.usize_vec(ReferenceCertificateSection::Declarations)?,
                ty: self.usize(ReferenceCertificateSection::Declarations)?,
                rules: RecursorRulesSpec {
                    minor_start: self.usize(ReferenceCertificateSection::Declarations)?,
                    major_index: self.usize(ReferenceCertificateSection::Declarations)?,
                },
            })),
            tag => Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::Declarations,
                recursor_offset,
                ReferenceCheckReason::UnknownTag { tag },
            )),
        }
    }

    fn export_block(
        &mut self,
        version: ReferenceCertificateFormatVersion,
    ) -> DecodeResult<Vec<Located<ExportEntry>>> {
        let len = self.bounded_len(ReferenceCertificateSection::ExportBlock)?;
        let mut exports = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            let name = self.usize(ReferenceCertificateSection::ExportBlock)?;
            let kind_offset = self.offset;
            let kind = match self.byte(ReferenceCertificateSection::ExportBlock)? {
                0x00 => ExportKind::Axiom,
                0x01 => ExportKind::Def,
                0x02 => ExportKind::Theorem,
                0x03 => ExportKind::Inductive,
                0x04 => ExportKind::Constructor,
                0x05 => ExportKind::Recursor,
                tag => {
                    return Err(ReferenceCheckError::malformed(
                        ReferenceCertificateSection::ExportBlock,
                        kind_offset,
                        ReferenceCheckReason::UnknownTag { tag },
                    ));
                }
            };
            exports.push(Located {
                value: ExportEntry {
                    name,
                    kind,
                    universe_params: self.usize_vec(ReferenceCertificateSection::ExportBlock)?,
                    universe_constraints: if version.encodes_export_universe_constraints() {
                        self.universe_constraint_specs_in_section(
                            ReferenceCertificateSection::ExportBlock,
                        )?
                    } else {
                        Vec::new()
                    },
                    ty: self.usize(ReferenceCertificateSection::ExportBlock)?,
                    body: self.option_usize(ReferenceCertificateSection::ExportBlock)?,
                    type_hash: self.hash(ReferenceCertificateSection::ExportBlock)?,
                    body_hash: self.option_hash(ReferenceCertificateSection::ExportBlock)?,
                    reducibility: self
                        .option_reducibility(ReferenceCertificateSection::ExportBlock)?,
                    opacity: self.option_opacity(ReferenceCertificateSection::ExportBlock)?,
                    decl_interface_hash: self.hash(ReferenceCertificateSection::ExportBlock)?,
                    axiom_dependencies: self
                        .axiom_refs(ReferenceCertificateSection::ExportBlock)?,
                },
                offset,
            });
        }
        Ok(exports)
    }

    fn axiom_report(&mut self) -> DecodeResult<AxiomReport> {
        let len = self.bounded_len(ReferenceCertificateSection::AxiomReport)?;
        let mut per_declaration = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.offset;
            per_declaration.push(DeclAxiomReport {
                decl_index: self.usize(ReferenceCertificateSection::AxiomReport)?,
                direct_axioms: self.axiom_refs(ReferenceCertificateSection::AxiomReport)?,
                transitive_axioms: self.axiom_refs(ReferenceCertificateSection::AxiomReport)?,
                offset,
            });
        }
        let module_axioms_offset = self.offset;
        let module_axioms = self.axiom_refs(ReferenceCertificateSection::AxiomReport)?;
        Ok(AxiomReport {
            per_declaration,
            module_axioms,
            module_axioms_offset,
            core_features: Vec::new(),
            core_features_offset: module_axioms_offset,
        })
    }

    fn core_features(&mut self) -> DecodeResult<Vec<ReferenceCoreFeature>> {
        let offset = self.offset;
        let tag = self.string(ReferenceCertificateSection::AxiomReport)?;
        if tag != CORE_FEATURE_REPORT_TAG {
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::AxiomReport,
                offset,
                ReferenceCheckReason::NonCanonicalOrder,
            ));
        }
        let len = self.bounded_len(ReferenceCertificateSection::AxiomReport)?;
        if len == 0 {
            return Err(ReferenceCheckError::malformed(
                ReferenceCertificateSection::AxiomReport,
                offset,
                ReferenceCheckReason::NonCanonicalOrder,
            ));
        }
        let mut features = Vec::with_capacity(len);
        for _ in 0..len {
            let feature = self.string(ReferenceCertificateSection::AxiomReport)?;
            let Some(feature) = ReferenceCoreFeature::from_name(&feature) else {
                return Err(ReferenceCheckError::unsupported_core_feature(offset));
            };
            features.push(feature);
        }
        ensure_strict_order(&features, ReferenceCertificateSection::AxiomReport, offset)?;
        Ok(features)
    }

    fn dependency_entries(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Vec<DependencyEntry>> {
        let len = self.bounded_len(section)?;
        let mut entries = Vec::with_capacity(len);
        for _ in 0..len {
            entries.push(DependencyEntry {
                global_ref: self.global_ref(section)?,
                decl_interface_hash: self.hash(section)?,
            });
        }
        Ok(entries)
    }

    fn axiom_refs(&mut self, section: ReferenceCertificateSection) -> DecodeResult<Vec<AxiomRef>> {
        let len = self.bounded_len(section)?;
        let mut axioms = Vec::with_capacity(len);
        for _ in 0..len {
            axioms.push(AxiomRef {
                global_ref: self.global_ref(section)?,
                name: self.usize(section)?,
                decl_interface_hash: self.hash(section)?,
            });
        }
        Ok(axioms)
    }

    fn global_ref(&mut self, section: ReferenceCertificateSection) -> DecodeResult<GlobalRef> {
        let offset = self.offset;
        let tag = self.byte(section)?;
        Ok(match tag {
            0x03 => GlobalRef::Builtin {
                name: self.usize(section)?,
                decl_interface_hash: self.hash(section)?,
            },
            0x00 => GlobalRef::Imported {
                import_index: self.usize(section)?,
                name: self.usize(section)?,
                decl_interface_hash: self.hash(section)?,
            },
            0x01 => GlobalRef::Local {
                decl_index: self.usize(section)?,
            },
            0x02 => GlobalRef::LocalGenerated {
                decl_index: self.usize(section)?,
                name: self.usize(section)?,
            },
            tag => {
                return Err(ReferenceCheckError::malformed(
                    section,
                    offset,
                    ReferenceCheckReason::UnknownTag { tag },
                ));
            }
        })
    }

    fn reducibility(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<CertReducibility> {
        let offset = self.offset;
        Ok(match self.byte(section)? {
            0x00 => CertReducibility::Reducible,
            0x01 => CertReducibility::Opaque,
            tag => {
                return Err(ReferenceCheckError::malformed(
                    section,
                    offset,
                    ReferenceCheckReason::UnknownTag { tag },
                ));
            }
        })
    }

    fn option_reducibility(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Option<CertReducibility>> {
        let offset = self.offset;
        match self.byte(section)? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.reducibility(section)?)),
            tag => Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::UnknownTag { tag },
            )),
        }
    }

    fn opacity(&mut self, section: ReferenceCertificateSection) -> DecodeResult<Opacity> {
        let offset = self.offset;
        Ok(match self.byte(section)? {
            0x00 => Opacity::Opaque,
            tag => {
                return Err(ReferenceCheckError::malformed(
                    section,
                    offset,
                    ReferenceCheckReason::UnknownTag { tag },
                ));
            }
        })
    }

    fn option_opacity(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Option<Opacity>> {
        let offset = self.offset;
        match self.byte(section)? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.opacity(section)?)),
            tag => Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::UnknownTag { tag },
            )),
        }
    }

    fn name(&mut self, section: ReferenceCertificateSection) -> DecodeResult<ReferenceModuleName> {
        let len = self.bounded_len(section)?;
        if len == 0 {
            return Err(ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::EmptyModuleName,
            ));
        }
        let mut components = Vec::with_capacity(len);
        for _ in 0..len {
            let component = self.string(section)?;
            if component.is_empty() {
                return Err(ReferenceCheckError::malformed(
                    section,
                    self.offset,
                    ReferenceCheckReason::EmptyModuleNameComponent,
                ));
            }
            if component.contains('.') {
                return Err(ReferenceCheckError::malformed(
                    section,
                    self.offset,
                    ReferenceCheckReason::DottedNameComponent,
                ));
            }
            if !reference_name_component_is_canonical(&component) {
                return Err(ReferenceCheckError::malformed(
                    section,
                    self.offset,
                    ReferenceCheckReason::InvalidNameComponent,
                ));
            }
            components.push(component);
        }
        ReferenceModuleName::new(components).map_err(|_| {
            ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::EmptyModuleName,
            )
        })
    }

    fn string(&mut self, section: ReferenceCertificateSection) -> DecodeResult<String> {
        let len = self.usize(section)?;
        let start = self.offset;
        let bytes = self.take(len, section)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| {
            ReferenceCheckError::malformed(section, start, ReferenceCheckReason::InvalidUtf8)
        })
    }

    fn usize_vec(&mut self, section: ReferenceCertificateSection) -> DecodeResult<Vec<usize>> {
        let len = self.bounded_len(section)?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.usize(section)?);
        }
        Ok(values)
    }

    fn option_usize(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Option<usize>> {
        let offset = self.offset;
        match self.byte(section)? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.usize(section)?)),
            tag => Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::UnknownTag { tag },
            )),
        }
    }

    fn option_hash(
        &mut self,
        section: ReferenceCertificateSection,
    ) -> DecodeResult<Option<ReferenceHash>> {
        let offset = self.offset;
        match self.byte(section)? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.hash(section)?)),
            tag => Err(ReferenceCheckError::malformed(
                section,
                offset,
                ReferenceCheckReason::UnknownTag { tag },
            )),
        }
    }

    fn hash(&mut self, section: ReferenceCertificateSection) -> DecodeResult<ReferenceHash> {
        let bytes = self.take(32, section)?;
        let mut hash = [0; 32];
        hash.copy_from_slice(bytes);
        Ok(hash)
    }

    fn bounded_len(&mut self, section: ReferenceCertificateSection) -> DecodeResult<usize> {
        let len = self.usize(section)?;
        let remaining = self.bytes.len().saturating_sub(self.offset);
        if len > remaining {
            return Err(ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::UnexpectedEof,
            ));
        }
        Ok(len)
    }

    fn u32(&mut self, section: ReferenceCertificateSection) -> DecodeResult<u32> {
        let offset = self.offset;
        let value = self.uvar(section)?;
        u32::try_from(value).map_err(|_| {
            ReferenceCheckError::malformed(section, offset, ReferenceCheckReason::LengthOverflow)
        })
    }

    fn usize(&mut self, section: ReferenceCertificateSection) -> DecodeResult<usize> {
        let offset = self.offset;
        let value = self.uvar(section)?;
        usize::try_from(value).map_err(|_| {
            ReferenceCheckError::malformed(section, offset, ReferenceCheckReason::LengthOverflow)
        })
    }

    fn uvar(&mut self, section: ReferenceCertificateSection) -> DecodeResult<u64> {
        let start = self.offset;
        let mut shift = 0u32;
        let mut value = 0u64;
        loop {
            let byte = self.byte(section)?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                if encode_uvar(value) != self.bytes[start..self.offset] {
                    return Err(ReferenceCheckError::malformed(
                        section,
                        start,
                        ReferenceCheckReason::NonCanonicalUvar,
                    ));
                }
                return Ok(value);
            }
            shift += 7;
            if shift >= 64 {
                return Err(ReferenceCheckError::malformed(
                    section,
                    start,
                    ReferenceCheckReason::UvarOverflow,
                ));
            }
        }
    }

    fn byte(&mut self, section: ReferenceCertificateSection) -> DecodeResult<u8> {
        let byte = *self.bytes.get(self.offset).ok_or_else(|| {
            ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::UnexpectedEof,
            )
        })?;
        self.offset += 1;
        Ok(byte)
    }

    fn take(&mut self, len: usize, section: ReferenceCertificateSection) -> DecodeResult<&'a [u8]> {
        let end = self.offset.checked_add(len).ok_or_else(|| {
            ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::LengthOverflow,
            )
        })?;
        let bytes = self.bytes.get(self.offset..end).ok_or_else(|| {
            ReferenceCheckError::malformed(
                section,
                self.offset,
                ReferenceCheckReason::UnexpectedEof,
            )
        })?;
        self.offset = end;
        Ok(bytes)
    }
}

fn import_order_key(
    import: &ImportEntry,
) -> (ReferenceModuleName, ReferenceHash, Option<ReferenceHash>) {
    (
        import.module.clone(),
        import.export_hash,
        import.certificate_hash,
    )
}

fn dependency_entry_order_key(entry: &DependencyEntry) -> Vec<u8> {
    let mut out = global_ref_order_key(&entry.global_ref);
    out.extend(entry.decl_interface_hash);
    out
}

fn axiom_ref_order_key(axiom: &AxiomRef) -> Vec<u8> {
    let mut out = global_ref_order_key(&axiom.global_ref);
    encode_order_uvar_to(&mut out, axiom.name);
    out.extend(axiom.decl_interface_hash);
    out
}

fn global_ref_order_key(global_ref: &GlobalRef) -> Vec<u8> {
    let mut out = Vec::new();
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_order_uvar_to(&mut out, *import_index);
            encode_order_uvar_to(&mut out, *name);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_order_uvar_to(&mut out, *decl_index);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_order_uvar_to(&mut out, *decl_index);
            encode_order_uvar_to(&mut out, *name);
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_order_uvar_to(&mut out, *name);
            out.extend(decl_interface_hash);
        }
    }
    out
}

fn encode_order_uvar_to(out: &mut Vec<u8>, mut value: usize) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn ensure_strict_order<T: Ord>(
    values: &[T],
    section: ReferenceCertificateSection,
    offset: usize,
) -> DecodeResult<()> {
    if values.windows(2).all(|pair| pair[0] < pair[1]) {
        Ok(())
    } else {
        Err(ReferenceCheckError::malformed(
            section,
            offset,
            ReferenceCheckReason::NonCanonicalOrder,
        ))
    }
}

fn level_node_height(node: &LevelNode, levels: &[Located<LevelNode>]) -> DecodeResult<usize> {
    Ok(match node {
        LevelNode::Zero | LevelNode::Param(_) => 0,
        LevelNode::Succ(inner) => level_node_height(&levels[*inner].value, levels)? + 1,
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            level_node_height(&levels[*lhs].value, levels)?
                .max(level_node_height(&levels[*rhs].value, levels)?)
                + 1
        }
    })
}

fn term_node_height(node: &TermNode, terms: &[Located<TermNode>]) -> DecodeResult<usize> {
    Ok(match node {
        TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
        TermNode::App(fun, arg) => {
            term_node_height(&terms[*fun].value, terms)?
                .max(term_node_height(&terms[*arg].value, terms)?)
                + 1
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            term_node_height(&terms[*ty].value, terms)?
                .max(term_node_height(&terms[*body].value, terms)?)
                + 1
        }
        TermNode::Let { ty, value, body } => {
            term_node_height(&terms[*ty].value, terms)?
                .max(term_node_height(&terms[*value].value, terms)?)
                .max(term_node_height(&terms[*body].value, terms)?)
                + 1
        }
    })
}

fn level_node_key(
    level: &LevelNode,
    child_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) -> DecodeResult<Vec<u8>> {
    let mut payload = Vec::new();
    match level {
        LevelNode::Zero => payload.push(0x00),
        LevelNode::Succ(inner) => {
            payload.push(0x01);
            payload.extend(child_hashes[*inner]);
        }
        LevelNode::Max(lhs, rhs) => {
            payload.push(0x02);
            payload.extend(child_hashes[*lhs]);
            payload.extend(child_hashes[*rhs]);
        }
        LevelNode::IMax(lhs, rhs) => {
            payload.push(0x03);
            payload.extend(child_hashes[*lhs]);
            payload.extend(child_hashes[*rhs]);
        }
        LevelNode::Param(name) => {
            payload.push(0x04);
            encode_name_to(&mut payload, &names[*name].value);
        }
    }
    Ok(payload)
}

fn term_node_key(
    term: &TermNode,
    child_hashes: &[ReferenceHash],
    level_hashes: &[ReferenceHash],
) -> DecodeResult<Vec<u8>> {
    let mut payload = Vec::new();
    match term {
        TermNode::Sort(level) => {
            payload.push(0x00);
            payload.extend(level_hashes[*level]);
        }
        TermNode::BVar(index) => {
            payload.push(0x01);
            encode_uvar_to(&mut payload, u64::from(*index));
        }
        TermNode::Const { global_ref, levels } => {
            payload.push(0x02);
            encode_global_ref_to(&mut payload, global_ref);
            encode_uvar_to(&mut payload, levels.len() as u64);
            for level in levels {
                payload.extend(level_hashes[*level]);
            }
        }
        TermNode::App(fun, arg) => {
            payload.push(0x03);
            payload.extend(child_hashes[*fun]);
            payload.extend(child_hashes[*arg]);
        }
        TermNode::Lam { ty, body } => {
            payload.push(0x04);
            payload.extend(child_hashes[*ty]);
            payload.extend(child_hashes[*body]);
        }
        TermNode::Pi { ty, body } => {
            payload.push(0x05);
            payload.extend(child_hashes[*ty]);
            payload.extend(child_hashes[*body]);
        }
        TermNode::Let { ty, value, body } => {
            payload.push(0x06);
            payload.extend(child_hashes[*ty]);
            payload.extend(child_hashes[*value]);
            payload.extend(child_hashes[*body]);
        }
    }
    Ok(payload)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ComputedDeclHashes {
    decl_interface_hash: ReferenceHash,
    decl_certificate_hash: ReferenceHash,
}

fn compute_decl_hashes(
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    term_table: &[Located<TermNode>],
    level_hashes: &[ReferenceHash],
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) -> DecodeResult<ComputedDeclHashes> {
    let interface_dependencies = interface_dependencies_for_decl(decl, dependencies, term_table)?;
    let interface_hash = hash_with_domain(
        b"NPA-DECL-IFACE-0.1",
        &decl_interface_payload(
            decl,
            &interface_dependencies,
            axiom_dependencies,
            level_hashes,
            term_hashes,
            names,
        )?,
    );
    let certificate_hash = hash_with_domain(
        b"NPA-DECL-CERT-0.1",
        &decl_certificate_payload(
            decl,
            interface_hash,
            dependencies,
            axiom_dependencies,
            term_hashes,
        )?,
    );
    Ok(ComputedDeclHashes {
        decl_interface_hash: interface_hash,
        decl_certificate_hash: certificate_hash,
    })
}

fn decl_interface_payload(
    decl: &DeclPayload,
    interface_dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    level_hashes: &[ReferenceHash],
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) -> DecodeResult<Vec<u8>> {
    let mut out = Vec::new();
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => {
            out.push(0x00);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            out.extend(term_hashes[*ty]);
            encode_dependency_entries_to(&mut out, interface_dependencies);
        }
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            out.push(0x10);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes);
            out.extend(term_hashes[*ty]);
            encode_dependency_entries_to(&mut out, interface_dependencies);
        }
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => {
            out.push(0x01);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            out.extend(term_hashes[*ty]);
            encode_reducibility_to(&mut out, *reducibility);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
            if *reducibility == CertReducibility::Reducible {
                out.extend(term_hashes[*value]);
            }
        }
        DeclPayload::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => {
            out.push(0x11);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes);
            out.extend(term_hashes[*ty]);
            encode_reducibility_to(&mut out, *reducibility);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
            if *reducibility == CertReducibility::Reducible {
                out.extend(term_hashes[*value]);
            }
        }
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            opacity,
            ..
        } => {
            out.push(0x02);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            out.extend(term_hashes[*ty]);
            encode_opacity_to(&mut out, *opacity);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            opacity,
            ..
        } => {
            out.push(0x12);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes);
            out.extend(term_hashes[*ty]);
            encode_opacity_to(&mut out, *opacity);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::Inductive {
            name,
            universe_params,
            params,
            indices,
            sort,
            constructors,
            recursor,
        } => {
            out.push(0x03);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_uvar_to(&mut out, params.len() as u64);
            for param in params {
                out.extend(term_hashes[param.ty]);
            }
            encode_uvar_to(&mut out, indices.len() as u64);
            for index in indices {
                out.extend(term_hashes[index.ty]);
            }
            out.extend(level_hashes[*sort]);
            encode_constructor_specs_to(&mut out, constructors, term_hashes, names);
            out.extend(generated_recursor_signature_hash(
                recursor.as_ref(),
                term_hashes,
                names,
            ));
            out.extend(generated_computation_rule_hash(recursor.as_ref()));
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::InductiveConstrained {
            name,
            universe_params,
            universe_constraints,
            params,
            indices,
            sort,
            constructors,
            recursor,
        } => {
            out.push(0x13);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes);
            encode_uvar_to(&mut out, params.len() as u64);
            for param in params {
                out.extend(term_hashes[param.ty]);
            }
            encode_uvar_to(&mut out, indices.len() as u64);
            for index in indices {
                out.extend(term_hashes[index.ty]);
            }
            out.extend(level_hashes[*sort]);
            encode_constructor_specs_to(&mut out, constructors, term_hashes, names);
            out.extend(generated_recursor_signature_hash(
                recursor.as_ref(),
                term_hashes,
                names,
            ));
            out.extend(generated_computation_rule_hash(recursor.as_ref()));
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => {
            out.push(0x04);
            encode_name_id_to(&mut out, names, *name);
            encode_name_ids_to(&mut out, names, universe_params);
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes);
            encode_mutual_inductive_specs_to(
                &mut out,
                inductives,
                level_hashes,
                term_hashes,
                names,
            );
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
    }
    Ok(out)
}

fn encode_mutual_inductive_specs_to(
    out: &mut Vec<u8>,
    inductives: &[MutualInductiveSpec],
    level_hashes: &[ReferenceHash],
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) {
    encode_uvar_to(out, inductives.len() as u64);
    for inductive in inductives {
        encode_name_id_to(out, names, inductive.name);
        encode_uvar_to(out, inductive.params.len() as u64);
        for param in &inductive.params {
            out.extend(term_hashes[param.ty]);
        }
        encode_uvar_to(out, inductive.indices.len() as u64);
        for index in &inductive.indices {
            out.extend(term_hashes[index.ty]);
        }
        out.extend(level_hashes[inductive.sort]);
        encode_constructor_specs_to(out, &inductive.constructors, term_hashes, names);
        out.extend(generated_recursor_signature_hash(
            inductive.recursor.as_ref(),
            term_hashes,
            names,
        ));
        out.extend(generated_computation_rule_hash(inductive.recursor.as_ref()));
    }
}

fn encode_universe_constraint_specs_to(
    out: &mut Vec<u8>,
    constraints: &[UniverseConstraintSpec],
    level_hashes: &[ReferenceHash],
) {
    encode_uvar_to(out, constraints.len() as u64);
    for constraint in constraints {
        out.extend(level_hashes[constraint.lhs]);
        out.push(match constraint.relation {
            UniverseConstraintRelation::Le => 0x00,
            UniverseConstraintRelation::Eq => 0x01,
        });
        out.extend(level_hashes[constraint.rhs]);
    }
}

fn encode_universe_constraint_spec_ids_to(
    out: &mut Vec<u8>,
    constraints: &[UniverseConstraintSpec],
) {
    encode_uvar_to(out, constraints.len() as u64);
    for constraint in constraints {
        encode_uvar_to(out, constraint.lhs as u64);
        out.push(match constraint.relation {
            UniverseConstraintRelation::Le => 0x00,
            UniverseConstraintRelation::Eq => 0x01,
        });
        encode_uvar_to(out, constraint.rhs as u64);
    }
}

fn decl_certificate_payload(
    decl: &DeclPayload,
    interface_hash: ReferenceHash,
    dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    term_hashes: &[ReferenceHash],
) -> DecodeResult<Vec<u8>> {
    let mut out = Vec::new();
    out.extend(interface_hash);
    match decl {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => {
            encode_axiom_refs_to(&mut out, axiom_dependencies)
        }
        DeclPayload::Def { value, .. } | DeclPayload::DefConstrained { value, .. } => {
            out.extend(term_hashes[*value]);
            encode_dependency_entries_to(&mut out, dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::Inductive { .. } | DeclPayload::InductiveConstrained { .. } => {
            encode_dependency_entries_to(&mut out, dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::MutualInductiveBlock { .. } => {
            encode_dependency_entries_to(&mut out, dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::Theorem { proof, .. } | DeclPayload::TheoremConstrained { proof, .. } => {
            out.extend(term_hashes[*proof]);
            encode_dependency_entries_to(&mut out, dependencies);
        }
    }
    Ok(out)
}

fn interface_dependencies_for_decl(
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    term_table: &[Located<TermNode>],
) -> DecodeResult<Vec<DependencyEntry>> {
    let mut refs = BTreeSet::new();
    for term in interface_term_ids(decl) {
        collect_global_refs_from_term(term_table, term, &mut refs)?;
    }
    Ok(dependencies
        .iter()
        .filter(|dependency| refs.contains(&dependency.global_ref))
        .cloned()
        .collect())
}

fn interface_term_ids(decl: &DeclPayload) -> Vec<usize> {
    match decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => vec![*ty],
        DeclPayload::Def {
            ty,
            value,
            reducibility,
            ..
        }
        | DeclPayload::DefConstrained {
            ty,
            value,
            reducibility,
            ..
        } => {
            let mut terms = vec![*ty];
            if *reducibility == CertReducibility::Reducible {
                terms.push(*value);
            }
            terms
        }
        DeclPayload::Theorem { ty, .. } | DeclPayload::TheoremConstrained { ty, .. } => vec![*ty],
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => params
            .iter()
            .map(|param| param.ty)
            .chain(indices.iter().map(|index| index.ty))
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .map(|param| param.ty)
                    .chain(inductive.indices.iter().map(|index| index.ty))
                    .chain(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    )
                    .chain(inductive.recursor.iter().map(|recursor| recursor.ty))
            })
            .collect(),
    }
}

fn decl_term_ids(decl: &DeclPayload) -> Vec<usize> {
    match decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => vec![*ty],
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            vec![*ty, *value]
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => vec![*ty, *proof],
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => params
            .iter()
            .map(|param| param.ty)
            .chain(indices.iter().map(|index| index.ty))
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .map(|param| param.ty)
                    .chain(inductive.indices.iter().map(|index| index.ty))
                    .chain(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    )
                    .chain(inductive.recursor.iter().map(|recursor| recursor.ty))
            })
            .collect(),
    }
}

fn decl_universe_params(decl: &DeclPayload) -> &[usize] {
    match decl {
        DeclPayload::Axiom {
            universe_params, ..
        }
        | DeclPayload::AxiomConstrained {
            universe_params, ..
        }
        | DeclPayload::Def {
            universe_params, ..
        }
        | DeclPayload::DefConstrained {
            universe_params, ..
        }
        | DeclPayload::Theorem {
            universe_params, ..
        }
        | DeclPayload::TheoremConstrained {
            universe_params, ..
        }
        | DeclPayload::Inductive {
            universe_params, ..
        }
        | DeclPayload::InductiveConstrained {
            universe_params, ..
        }
        | DeclPayload::MutualInductiveBlock {
            universe_params, ..
        } => universe_params,
    }
}

fn decl_universe_constraints(decl: &DeclPayload) -> &[UniverseConstraintSpec] {
    match decl {
        DeclPayload::AxiomConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::InductiveConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::MutualInductiveBlock {
            universe_constraints,
            ..
        } => universe_constraints,
        DeclPayload::Axiom { .. }
        | DeclPayload::Def { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::Inductive { .. } => &[],
    }
}

fn decl_has_empty_constrained_universe_payload(decl: &DeclPayload) -> bool {
    match decl {
        DeclPayload::AxiomConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::InductiveConstrained {
            universe_constraints,
            ..
        } => universe_constraints.is_empty(),
        DeclPayload::Axiom { .. }
        | DeclPayload::Def { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::Inductive { .. }
        | DeclPayload::MutualInductiveBlock { .. } => false,
    }
}

fn collect_global_refs_from_term(
    terms: &[Located<TermNode>],
    term: usize,
    refs: &mut BTreeSet<GlobalRef>,
) -> DecodeResult<()> {
    match &terms[term].value {
        TermNode::Sort(_) | TermNode::BVar(_) => {}
        TermNode::Const { global_ref, .. } => {
            refs.insert(global_ref.clone());
        }
        TermNode::App(fun, arg) => {
            collect_global_refs_from_term(terms, *fun, refs)?;
            collect_global_refs_from_term(terms, *arg, refs)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_global_refs_from_term(terms, *ty, refs)?;
            collect_global_refs_from_term(terms, *body, refs)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_global_refs_from_term(terms, *ty, refs)?;
            collect_global_refs_from_term(terms, *value, refs)?;
            collect_global_refs_from_term(terms, *body, refs)?;
        }
    }
    Ok(())
}

fn local_axiom_ref_for_decl(decl_index: usize, axioms: &[AxiomRef]) -> Option<AxiomRef> {
    axioms
        .iter()
        .find(|axiom| {
            matches!(
                axiom.global_ref,
                GlobalRef::Local { decl_index: axiom_decl_index }
                    if axiom_decl_index == decl_index
            )
        })
        .cloned()
}

fn import_index_exporting_axiom(
    imports: &ReferenceImportEnvironment,
    name: &ReferenceModuleName,
    decl_interface_hash: ReferenceHash,
) -> Option<usize> {
    imports
        .imports()
        .iter()
        .enumerate()
        .find_map(|(import_index, import)| {
            import
                .public_environment
                .exports()
                .iter()
                .any(|export| {
                    export.kind == ReferenceExportKind::Axiom
                        && export.name == *name
                        && export.decl_interface_hash == decl_interface_hash
                })
                .then_some(import_index)
        })
}

fn union_axioms(axioms: impl IntoIterator<Item = AxiomRef>) -> Vec<AxiomRef> {
    axioms
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

pub(crate) fn builtin_decl_interface_hash(name: &ReferenceModuleName) -> Option<ReferenceHash> {
    let tag = match name.dotted().as_str() {
        "Nat" => "npa.machine-tactic.builtin.nat.v1",
        "Nat.zero" => "npa.machine-tactic.builtin.nat.zero.v1",
        "Nat.succ" => "npa.machine-tactic.builtin.nat.succ.v1",
        "Nat.rec" => "npa.machine-tactic.builtin.nat.rec.v1",
        "Eq" => "npa.machine-tactic.builtin.eq.v1",
        "Eq.refl" => "npa.machine-tactic.builtin.eq.refl.v1",
        "Eq.rec" => "npa.machine-tactic.builtin.eq.rec.v1",
        _ => return None,
    };
    Some(hash_with_domain(
        b"NPA-BUILTIN-INTERFACE-0.1",
        tag.as_bytes(),
    ))
}

fn builtin_is_axiom(name: &ReferenceModuleName) -> bool {
    name.dotted() == "Eq.rec"
}

fn qualify_name(module: &ReferenceModuleName, raw_name: &str) -> String {
    format!("{}.{}", module.dotted(), raw_name)
}

fn enforce_axiom_policy_name(
    policy: &ReferenceCheckerPolicy,
    raw_name: &str,
    qualified_name: Option<&str>,
    is_standard_exception: bool,
    section: ReferenceCertificateSection,
    offset: usize,
) -> DecodeResult<()> {
    if policy.deny_sorry
        && (raw_name.contains("sorry") || qualified_name.is_some_and(|name| name.contains("sorry")))
    {
        return Err(ReferenceCheckError::axiom_policy(
            section,
            offset,
            ReferenceCheckReason::SorryDenied,
        ));
    }

    let require_allowlist = policy.deny_custom_axioms
        || policy.trust_mode == ReferenceTrustMode::HighTrust
        || !policy.allowed_axioms.is_empty();
    if !require_allowlist || is_standard_exception {
        return Ok(());
    }

    if policy.allowed_axioms.iter().any(|allowed| {
        allowed == raw_name || qualified_name.is_some_and(|qualified| allowed == qualified)
    }) {
        return Ok(());
    }

    Err(ReferenceCheckError::axiom_policy(
        section,
        offset,
        ReferenceCheckReason::ForbiddenAxiom,
    ))
}

fn inductive_export_type_term_id(
    term_table: &[Located<TermNode>],
    params: &[BinderType],
    indices: &[BinderType],
    sort: usize,
) -> DecodeResult<usize> {
    let mut body = term_table
        .iter()
        .position(|term| matches!(term.value, TermNode::Sort(level) if level == sort))
        .ok_or_else(|| {
            ReferenceCheckError::malformed(
                ReferenceCertificateSection::TermTable,
                term_table.last().map_or(0, |entry| entry.offset),
                ReferenceCheckReason::DanglingReference,
            )
        })?;
    for binder in params.iter().chain(indices).rev() {
        body = term_table
            .iter()
            .position(|term| {
                matches!(
                    term.value,
                    TermNode::Pi { ty, body: pi_body } if ty == binder.ty && pi_body == body
                )
            })
            .ok_or_else(|| {
                ReferenceCheckError::malformed(
                    ReferenceCertificateSection::TermTable,
                    term_table.last().map_or(0, |entry| entry.offset),
                    ReferenceCheckReason::DanglingReference,
                )
            })?;
    }
    Ok(body)
}

fn encode_constructor_specs_to(
    out: &mut Vec<u8>,
    constructors: &[ConstructorSpec],
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) {
    encode_uvar_to(out, constructors.len() as u64);
    for constructor in constructors {
        encode_name_id_to(out, names, constructor.name);
        out.extend(term_hashes[constructor.ty]);
    }
}

fn generated_recursor_signature_hash(
    recursor: Option<&RecursorSpec>,
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) -> ReferenceHash {
    hash_with_domain(
        b"NPA-GEN-REC-SIG-0.1",
        &generated_recursor_signature_payload(recursor, term_hashes, names),
    )
}

fn generated_recursor_signature_payload(
    recursor: Option<&RecursorSpec>,
    term_hashes: &[ReferenceHash],
    names: &[Located<ReferenceModuleName>],
) -> Vec<u8> {
    let mut out = Vec::new();
    match recursor {
        Some(recursor) => {
            out.push(0x01);
            encode_name_id_to(&mut out, names, recursor.name);
            encode_name_ids_to(&mut out, names, &recursor.universe_params);
            out.extend(term_hashes[recursor.ty]);
        }
        None => out.push(0x00),
    }
    out
}

fn generated_computation_rule_hash(recursor: Option<&RecursorSpec>) -> ReferenceHash {
    hash_with_domain(
        b"NPA-GEN-COMP-RULE-0.1",
        &generated_computation_rule_payload(recursor),
    )
}

fn generated_computation_rule_payload(recursor: Option<&RecursorSpec>) -> Vec<u8> {
    let mut out = Vec::new();
    match recursor {
        Some(recursor) => {
            out.push(0x01);
            encode_recursor_rules_to(&mut out, &recursor.rules);
        }
        None => out.push(0x00),
    }
    out
}

fn encode_recursor_rules_to(out: &mut Vec<u8>, rules: &RecursorRulesSpec) {
    encode_uvar_to(out, rules.minor_start as u64);
    encode_uvar_to(out, rules.major_index as u64);
}

fn encode_export_block(block: &[ExportEntry]) -> Vec<u8> {
    encode_export_block_with_format(block, ReferenceCertificateFormatVersion::Current)
}

fn encode_export_block_legacy(block: &[ExportEntry]) -> Vec<u8> {
    encode_export_block_with_format(block, ReferenceCertificateFormatVersion::Legacy)
}

fn encode_export_block_previous(block: &[ExportEntry]) -> Vec<u8> {
    encode_export_block_with_format(block, ReferenceCertificateFormatVersion::Previous)
}

fn encode_export_block_with_format(
    block: &[ExportEntry],
    version: ReferenceCertificateFormatVersion,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, block.len() as u64);
    for entry in block {
        encode_uvar_to(&mut out, entry.name as u64);
        out.push(match entry.kind {
            ExportKind::Axiom => 0x00,
            ExportKind::Def => 0x01,
            ExportKind::Theorem => 0x02,
            ExportKind::Inductive => 0x03,
            ExportKind::Constructor => 0x04,
            ExportKind::Recursor => 0x05,
        });
        encode_usize_vec(&mut out, &entry.universe_params);
        if version.encodes_export_universe_constraints() {
            encode_universe_constraint_spec_ids_to(&mut out, &entry.universe_constraints);
        }
        encode_uvar_to(&mut out, entry.ty as u64);
        encode_option_usize_to(&mut out, entry.body);
        out.extend(entry.type_hash);
        encode_option_hash_to(&mut out, entry.body_hash.as_ref());
        encode_option_reducibility_to(&mut out, entry.reducibility);
        encode_option_opacity_to(&mut out, entry.opacity);
        out.extend(entry.decl_interface_hash);
        encode_axiom_refs_to(&mut out, &entry.axiom_dependencies);
    }
    out
}

fn encode_axiom_report(report: &AxiomReport) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, report.per_declaration.len() as u64);
    for entry in &report.per_declaration {
        encode_uvar_to(&mut out, entry.decl_index as u64);
        encode_axiom_refs_to(&mut out, &entry.direct_axioms);
        encode_axiom_refs_to(&mut out, &entry.transitive_axioms);
    }
    encode_axiom_refs_to(&mut out, &report.module_axioms);
    if !report.core_features.is_empty() {
        encode_string_to(&mut out, CORE_FEATURE_REPORT_TAG);
        encode_uvar_to(&mut out, report.core_features.len() as u64);
        for feature in &report.core_features {
            encode_string_to(&mut out, feature.as_str());
        }
    }
    out
}

fn encode_dependency_entries_to(out: &mut Vec<u8>, entries: &[DependencyEntry]) {
    encode_uvar_to(out, entries.len() as u64);
    for entry in entries {
        encode_global_ref_to(out, &entry.global_ref);
        out.extend(entry.decl_interface_hash);
    }
}

fn encode_axiom_refs_to(out: &mut Vec<u8>, axioms: &[AxiomRef]) {
    encode_uvar_to(out, axioms.len() as u64);
    for axiom in axioms {
        encode_global_ref_to(out, &axiom.global_ref);
        encode_uvar_to(out, axiom.name as u64);
        out.extend(axiom.decl_interface_hash);
    }
}

fn encode_name_id_to(out: &mut Vec<u8>, names: &[Located<ReferenceModuleName>], name: usize) {
    encode_name_to(out, &names[name].value);
}

fn encode_name_ids_to(out: &mut Vec<u8>, names: &[Located<ReferenceModuleName>], values: &[usize]) {
    encode_uvar_to(out, values.len() as u64);
    for value in values {
        encode_name_id_to(out, names, *value);
    }
}

fn encode_usize_vec(out: &mut Vec<u8>, values: &[usize]) {
    encode_uvar_to(out, values.len() as u64);
    for value in values {
        encode_uvar_to(out, *value as u64);
    }
}

fn encode_reducibility_to(out: &mut Vec<u8>, value: CertReducibility) {
    out.push(match value {
        CertReducibility::Reducible => 0x00,
        CertReducibility::Opaque => 0x01,
    });
}

fn encode_option_reducibility_to(out: &mut Vec<u8>, value: Option<CertReducibility>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_reducibility_to(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_opacity_to(out: &mut Vec<u8>, value: Opacity) {
    match value {
        Opacity::Opaque => out.push(0x00),
    }
}

fn encode_option_opacity_to(out: &mut Vec<u8>, value: Option<Opacity>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_opacity_to(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_option_usize_to(out: &mut Vec<u8>, value: Option<usize>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_uvar_to(out, value as u64);
        }
        None => out.push(0x00),
    }
}

fn encode_option_hash_to(out: &mut Vec<u8>, hash: Option<&ReferenceHash>) {
    match hash {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
}

fn encode_global_ref_to(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar_to(out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar_to(out, *import_index as u64);
            encode_uvar_to(out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar_to(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar_to(out, *decl_index as u64);
            encode_uvar_to(out, *name as u64);
        }
    }
}

fn encode_name_to(out: &mut Vec<u8>, name: &ReferenceModuleName) {
    encode_uvar_to(out, name.components().len() as u64);
    for component in name.components() {
        encode_uvar_to(out, component.len() as u64);
        out.extend(component.as_bytes());
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_uvar_to(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> ReferenceHash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn encode_uvar(value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, value);
    out
}

fn encode_uvar_to(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn param(name: &str) -> ReferenceCoreLevel {
        ReferenceCoreLevel::Param(rname(name))
    }

    fn succ(level: ReferenceCoreLevel) -> ReferenceCoreLevel {
        ReferenceCoreLevel::Succ(Arc::new(level))
    }

    #[test]
    fn signature_universe_constraints_are_checked_against_current_context() {
        let signature = TypeSignature {
            universe_params: vec![rname("u"), rname("v"), rname("w")],
            universe_constraints: vec![ReferenceUniverseConstraint::le(
                ReferenceCoreLevel::Max(Arc::new(param("u")), Arc::new(param("v"))),
                param("w"),
            )],
            ty: ReferenceCoreExpr::Sort(ReferenceCoreLevel::Zero),
            value: None,
        };
        let context = ReferenceUniverseContext::empty();

        enforce_signature_universe_constraints(
            &context,
            &signature,
            &[
                ReferenceCoreLevel::Zero,
                ReferenceCoreLevel::Zero,
                succ(ReferenceCoreLevel::Zero),
            ],
            0,
        )
        .expect("supported constrained instantiation is accepted");

        let error = enforce_signature_universe_constraints(
            &context,
            &signature,
            &[
                succ(ReferenceCoreLevel::Zero),
                ReferenceCoreLevel::Zero,
                ReferenceCoreLevel::Zero,
            ],
            0,
        )
        .expect_err("unsatisfied constrained instantiation is rejected");

        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::UniverseConstraintViolation)
        );
    }

    #[test]
    fn signature_universe_constraints_use_current_context_assumptions() {
        let signature = TypeSignature {
            universe_params: vec![rname("u"), rname("w")],
            universe_constraints: vec![ReferenceUniverseConstraint::le(param("u"), param("w"))],
            ty: ReferenceCoreExpr::Sort(ReferenceCoreLevel::Zero),
            value: None,
        };
        let context = ReferenceUniverseContext::new(
            vec![rname("a"), rname("b")],
            vec![ReferenceUniverseConstraint::le(param("a"), param("b"))],
            0,
        )
        .expect("context is satisfiable");

        enforce_signature_universe_constraints(&context, &signature, &[param("a"), param("b")], 0)
            .expect("context entails substituted obligation");

        let error = enforce_signature_universe_constraints(
            &context,
            &signature,
            &[param("b"), param("a")],
            0,
        )
        .expect_err("context does not entail reversed obligation");

        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::UniverseConstraintViolation)
        );
    }
}

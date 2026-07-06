use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{
    AxiomRef, BinderType, CertReducibility, ConstructorSpec, DeclPayload, GlobalRef, Hash, LevelId,
    LevelNode, MutualInductiveSpec, Name, NameId, Opacity, RecursorRulesSpec, RecursorSpec, TermId,
    TermNode, UniverseConstraintSpec,
};
use npa_kernel::{
    level::normalize_level, Binder, ConstructorDecl, Decl, Expr, InductiveDecl, Level,
    MutualInductiveBlock, RecursorDecl, UniverseConstraint,
};
#[cfg(test)]
use npa_tactic::check_current_decl_for_machine_tactic_from_verified_imports;
use npa_tactic::{
    check_current_decl_for_machine_tactic_from_verified_imports_with_kernel_profile,
    checked_decl_signature_canonical_bytes, CheckedCurrentDecl, MachineKernelProfile,
    MachineTacticDiagnostic, MachineTacticDiagnosticKind, VerifiedImportRef,
};
use sha2::{Digest, Sha256};

use crate::{MachineImportCertificateContext, VerifiedModuleContextEntry};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedCurrentDeclPackageInput<'bytes> {
    pub bytes: &'bytes [u8],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineCheckedCurrentDeclContext {
    checked_current_decls: Vec<CheckedCurrentDecl>,
    decl_index_table: Vec<CurrentDeclIndexEntry>,
    generated_decl_table: Vec<CurrentGeneratedDeclEntry>,
}

impl MachineCheckedCurrentDeclContext {
    pub fn empty() -> Self {
        Self {
            checked_current_decls: Vec::new(),
            decl_index_table: Vec::new(),
            generated_decl_table: Vec::new(),
        }
    }

    pub fn checked_current_decls(&self) -> &[CheckedCurrentDecl] {
        &self.checked_current_decls
    }

    pub fn decl_index_table(&self) -> &[CurrentDeclIndexEntry] {
        &self.decl_index_table
    }

    pub fn generated_decl_table(&self) -> &[CurrentGeneratedDeclEntry] {
        &self.generated_decl_table
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentDeclIndexEntry {
    pub source_index: u64,
    pub package_bytes: Vec<u8>,
    pub signature: MachineCheckedDeclSignature,
    pub core_decl: Decl,
    pub core_decl_hash: Hash,
    pub dependency_report: CurrentDeclDependencyReport,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentGeneratedDeclEntry {
    pub module: Name,
    pub parent_source_index: u64,
    pub parent_name: Name,
    pub parent_decl_interface_hash: Hash,
    pub generated_name: Name,
    pub generated_decl_interface_hash: Hash,
    pub kind: CurrentGeneratedDeclKind,
    pub ty: Expr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CurrentGeneratedDeclKind {
    Constructor,
    Recursor,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineCheckedDeclSignature {
    pub name: Name,
    pub universe_params: Vec<String>,
    pub ty: Expr,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentDeclDependencyReport {
    pub direct_dependency_entries: Vec<CurrentDeclDependencyEntry>,
    pub axiom_dependencies: Vec<MachineAxiomRefWire>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentDeclDependencyEntry {
    pub dependency_ref: MachineDependencyRefWire,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDependencyRefWire {
    Imported {
        module: Name,
        name: Name,
        export_hash: Hash,
    },
    CurrentModule {
        module: Name,
        name: Name,
        source_index: u64,
    },
    CurrentGenerated {
        module: Name,
        generated_name: Name,
        parent_source_index: u64,
    },
    Builtin {
        name: Name,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineAxiomRefWire {
    Imported {
        module: Name,
        name: Name,
        export_hash: Hash,
        decl_interface_hash: Hash,
    },
    CurrentModule {
        module: Name,
        name: Name,
        source_index: u64,
        decl_interface_hash: Hash,
    },
    Builtin {
        name: Name,
        decl_interface_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckedCurrentDeclProjectionError {
    DecodeFailed {
        reason: &'static str,
    },
    NonCanonicalPackage,
    DuplicateSourceIndex {
        source_index: u64,
    },
    InvalidSourceIndexPrefix {
        expected: u64,
        actual: Option<u64>,
    },
    SourceIndexOutOfRange {
        source_index: u64,
        root_source_index: u64,
    },
    ModulePrefixMismatch {
        module: Name,
        name: Name,
    },
    DependencyReportMismatch {
        source_index: u64,
    },
    SignatureMismatch {
        source_index: u64,
    },
    PriorChainFingerprintMismatch {
        source_index: u64,
    },
    CheckedEnvFingerprintMismatch {
        source_index: u64,
    },
    MissingImportedDependency {
        source_index: u64,
        import_index: usize,
    },
    MissingImportedExport {
        source_index: u64,
        module: Name,
        name: Name,
        decl_interface_hash: Hash,
    },
    MissingCurrentDependency {
        source_index: u64,
        dependency_source_index: u64,
    },
    MissingCurrentGeneratedDependency {
        source_index: u64,
        parent_source_index: u64,
        generated_name: Name,
    },
    InvalidFutureDependency {
        source_index: u64,
        dependency_source_index: u64,
    },
    InvalidBuiltinDependency {
        source_index: u64,
        name: Name,
    },
    InvalidAxiomRef {
        source_index: u64,
        name: Name,
    },
    MachineTacticRejected {
        source_index: u64,
        diagnostic: Box<MachineTacticDiagnostic>,
    },
}

pub fn project_checked_current_decl_context(
    root_module: &Name,
    root_source_index: u64,
    imports: &MachineImportCertificateContext,
    packages: &[CheckedCurrentDeclPackageInput<'_>],
) -> Result<MachineCheckedCurrentDeclContext, CheckedCurrentDeclProjectionError> {
    project_checked_current_decl_context_with_kernel_profile(
        MachineKernelProfile::BuiltinNatEqRec,
        root_module,
        root_source_index,
        imports,
        packages,
    )
}

pub fn project_checked_current_decl_context_with_kernel_profile(
    kernel_profile: MachineKernelProfile,
    root_module: &Name,
    root_source_index: u64,
    imports: &MachineImportCertificateContext,
    packages: &[CheckedCurrentDeclPackageInput<'_>],
) -> Result<MachineCheckedCurrentDeclContext, CheckedCurrentDeclProjectionError> {
    let mut decoded_by_index = BTreeMap::new();
    for input in packages {
        let decoded = decode_checked_current_decl_package(input.bytes)?;
        if decoded.canonical_bytes != input.bytes {
            return Err(CheckedCurrentDeclProjectionError::NonCanonicalPackage);
        }
        if decoded.source_index >= root_source_index {
            return Err(CheckedCurrentDeclProjectionError::SourceIndexOutOfRange {
                source_index: decoded.source_index,
                root_source_index,
            });
        }
        let source_index = decoded.source_index;
        if decoded_by_index.insert(source_index, decoded).is_some() {
            return Err(CheckedCurrentDeclProjectionError::DuplicateSourceIndex { source_index });
        }
    }

    for expected in 0..root_source_index {
        if !decoded_by_index.contains_key(&expected) {
            return Err(
                CheckedCurrentDeclProjectionError::InvalidSourceIndexPrefix {
                    expected,
                    actual: decoded_by_index
                        .range(expected..)
                        .next()
                        .map(|(index, _)| *index),
                },
            );
        }
    }
    if decoded_by_index.len() != root_source_index as usize {
        return Err(
            CheckedCurrentDeclProjectionError::InvalidSourceIndexPrefix {
                expected: root_source_index,
                actual: decoded_by_index
                    .keys()
                    .find(|index| **index >= root_source_index)
                    .copied(),
            },
        );
    }

    let direct_import_entries = imports.direct_import_entries();
    let machine_tactic_imports =
        machine_tactic_import_refs_from_context(imports).map_err(|diagnostic| {
            CheckedCurrentDeclProjectionError::MachineTacticRejected {
                source_index: 0,
                diagnostic: Box::new(diagnostic),
            }
        })?;

    let mut checked_current_decls = Vec::new();
    let mut decl_index_table = Vec::new();
    let mut generated_decl_table = Vec::new();
    for source_index in 0..root_source_index {
        let decoded = decoded_by_index
            .remove(&source_index)
            .expect("prefix check guarantees decoded package exists");
        ensure_name_has_module_prefix(root_module, &decoded.signature.name)?;

        let core_decl = decoded.core_package.to_kernel_decl(
            root_module,
            source_index,
            &decl_index_table,
            &generated_decl_table,
        )?;
        if let Decl::Axiom { name, .. } = &core_decl {
            return Err(CheckedCurrentDeclProjectionError::MachineTacticRejected {
                source_index,
                diagnostic: Box::new(MachineTacticDiagnostic::new(
                    MachineTacticDiagnosticKind::UncheckedCurrentDecl,
                    format!(
                        "current declaration {name} is an axiom; checked current declarations must carry a kernel-checkable body"
                    ),
                )),
            });
        }
        let recomputed_report = derive_dependency_report(
            root_module,
            source_index,
            imports,
            &direct_import_entries,
            &decoded.core_package,
            &decl_index_table,
            &generated_decl_table,
        )?;
        if recomputed_report != decoded.dependency_report {
            return Err(
                CheckedCurrentDeclProjectionError::DependencyReportMismatch { source_index },
            );
        }

        let checked =
            check_current_decl_for_machine_tactic_from_verified_imports_with_kernel_profile(
                kernel_profile,
                &machine_tactic_imports,
                &checked_current_decls,
                source_index,
                core_decl.clone(),
            )
            .map_err(|diagnostic| {
                CheckedCurrentDeclProjectionError::MachineTacticRejected {
                    source_index,
                    diagnostic: Box::new(diagnostic),
                }
            })?;
        if decoded.signature_canonical_bytes
            != checked_decl_signature_canonical_bytes(checked.signature())
        {
            return Err(CheckedCurrentDeclProjectionError::SignatureMismatch { source_index });
        }
        if decoded.prior_chain_fingerprint != checked.prior_chain_fingerprint() {
            return Err(
                CheckedCurrentDeclProjectionError::PriorChainFingerprintMismatch { source_index },
            );
        }
        if decoded.checked_env_fingerprint != checked.checked_env_fingerprint() {
            return Err(
                CheckedCurrentDeclProjectionError::CheckedEnvFingerprintMismatch { source_index },
            );
        }

        let signature = decoded.signature;
        let core_decl_hash = checked.core_decl_hash();
        let new_generated = project_current_generated_decl_table(
            root_module,
            source_index,
            &signature,
            &core_decl,
        )?;
        let entry = CurrentDeclIndexEntry {
            source_index,
            package_bytes: decoded.canonical_bytes,
            signature,
            core_decl,
            core_decl_hash,
            dependency_report: recomputed_report,
        };
        checked_current_decls.push(checked);
        decl_index_table.push(entry);
        generated_decl_table.extend(new_generated);
    }

    Ok(MachineCheckedCurrentDeclContext {
        checked_current_decls,
        decl_index_table,
        generated_decl_table,
    })
}

pub(crate) fn validate_checked_current_decl_package_bytes(
    bytes: &[u8],
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let decoded = decode_checked_current_decl_package(bytes)?;
    if decoded.canonical_bytes != bytes {
        return Err(CheckedCurrentDeclProjectionError::NonCanonicalPackage);
    }
    Ok(())
}

pub(crate) fn machine_tactic_import_refs_from_context(
    imports: &MachineImportCertificateContext,
) -> Result<Vec<VerifiedImportRef>, MachineTacticDiagnostic> {
    let direct_keys = imports
        .direct_import_keys()
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    imports
        .verified_modules()
        .iter()
        .map(|entry| {
            if direct_keys.contains(&entry.key) {
                VerifiedImportRef::from_verified_module(&entry.verified_module)
            } else {
                VerifiedImportRef::from_verified_module_env_only(&entry.verified_module)
            }
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DecodedCheckedCurrentDeclPackage {
    source_index: u64,
    signature: MachineCheckedDeclSignature,
    signature_canonical_bytes: Vec<u8>,
    core_package: CoreDeclPackage,
    dependency_report: CurrentDeclDependencyReport,
    prior_chain_fingerprint: Hash,
    checked_env_fingerprint: Hash,
    canonical_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CoreDeclPackage {
    name_table: Vec<Name>,
    level_table: Vec<LevelNode>,
    term_table: Vec<TermNode>,
    root_decl: DeclPayload,
}

fn decode_checked_current_decl_package(
    bytes: &[u8],
) -> Result<DecodedCheckedCurrentDeclPackage, CheckedCurrentDeclProjectionError> {
    let mut decoder = PackageDecoder::new(bytes);
    decoder.tag("npa.machine-api.checked-current-decl-package.v5")?;
    let source_index = decoder.u64()?;
    let signature_start = decoder.offset();
    let signature = decoder.checked_decl_signature()?;
    let signature_canonical_bytes = bytes[signature_start..decoder.offset()].to_vec();
    let core_package = decoder.core_decl_package()?;
    let dependency_report = decoder.current_decl_dependency_report()?;
    let prior_chain_fingerprint = decoder.hash()?;
    let checked_env_fingerprint = decoder.hash()?;
    if !decoder.is_done() {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "trailing bytes",
        });
    }
    let decoded = DecodedCheckedCurrentDeclPackage {
        source_index,
        signature,
        signature_canonical_bytes,
        core_package,
        dependency_report,
        prior_chain_fingerprint,
        checked_env_fingerprint,
        canonical_bytes: bytes.to_vec(),
    };
    if encode_checked_current_decl_package(&decoded) != bytes {
        return Err(CheckedCurrentDeclProjectionError::NonCanonicalPackage);
    }
    Ok(decoded)
}

impl CoreDeclPackage {
    fn to_kernel_decl(
        &self,
        root_module: &Name,
        source_index: u64,
        prior_decls: &[CurrentDeclIndexEntry],
        generated: &[CurrentGeneratedDeclEntry],
    ) -> Result<Decl, CheckedCurrentDeclProjectionError> {
        Ok(match &self.root_decl {
            DeclPayload::Axiom {
                name,
                universe_params,
                ty,
            } => Decl::Axiom {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
            },
            DeclPayload::AxiomConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
            } => Decl::AxiomConstrained {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                universe_constraints: self.universe_constraints(universe_constraints)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
            },
            DeclPayload::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            } => Decl::Def {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                value: self.expr_from_term(
                    root_module,
                    source_index,
                    prior_decls,
                    generated,
                    *value,
                )?,
                reducibility: (*reducibility).into(),
            },
            DeclPayload::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            } => Decl::DefConstrained {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                universe_constraints: self.universe_constraints(universe_constraints)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                value: self.expr_from_term(
                    root_module,
                    source_index,
                    prior_decls,
                    generated,
                    *value,
                )?,
                reducibility: (*reducibility).into(),
            },
            DeclPayload::Theorem {
                name,
                universe_params,
                ty,
                proof,
                ..
            } => Decl::Theorem {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                proof: self.expr_from_term(
                    root_module,
                    source_index,
                    prior_decls,
                    generated,
                    *proof,
                )?,
            },
            DeclPayload::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
                ..
            } => Decl::TheoremConstrained {
                name: self.name_string(*name)?,
                universe_params: self.universe_names(universe_params)?,
                universe_constraints: self.universe_constraints(universe_constraints)?,
                ty: self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                proof: self.expr_from_term(
                    root_module,
                    source_index,
                    prior_decls,
                    generated,
                    *proof,
                )?,
            },
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
                let inductive_name = self.name_string(*name)?;
                let universe_params = self.universe_names(universe_params)?;
                let params = params
                    .iter()
                    .enumerate()
                    .map(|(index, binder)| {
                        Ok(Binder::new(
                            format!("p{index}"),
                            self.expr_from_term(
                                root_module,
                                source_index,
                                prior_decls,
                                generated,
                                binder.ty,
                            )?,
                        ))
                    })
                    .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                let indices = indices
                    .iter()
                    .enumerate()
                    .map(|(index, binder)| {
                        Ok(Binder::new(
                            format!("i{index}"),
                            self.expr_from_term(
                                root_module,
                                source_index,
                                prior_decls,
                                generated,
                                binder.ty,
                            )?,
                        ))
                    })
                    .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                let sort_level = self.level_from_node(*sort)?;
                let constructors = constructors
                    .iter()
                    .map(|constructor| {
                        Ok(ConstructorDecl::new(
                            self.name_string(constructor.name)?,
                            self.expr_from_term(
                                root_module,
                                source_index,
                                prior_decls,
                                generated,
                                constructor.ty,
                            )?,
                        ))
                    })
                    .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                let recursor = recursor
                    .as_ref()
                    .map(|recursor| {
                        Ok::<_, CheckedCurrentDeclProjectionError>(RecursorDecl::with_rules(
                            self.name_string(recursor.name)?,
                            self.universe_names(&recursor.universe_params)?,
                            self.expr_from_term(
                                root_module,
                                source_index,
                                prior_decls,
                                generated,
                                recursor.ty,
                            )?,
                            npa_kernel::RecursorRules::new(
                                recursor.rules.minor_start,
                                recursor.rules.major_index,
                            ),
                        ))
                    })
                    .transpose()?;
                let data = InductiveDecl::new(
                    inductive_name.clone(),
                    universe_params.clone(),
                    params.clone(),
                    indices.clone(),
                    sort_level.clone(),
                    constructors,
                    recursor,
                )
                .with_universe_constraints(
                    self.universe_constraints(root_decl_universe_constraints(&self.root_decl))?,
                );
                Decl::Inductive {
                    name: inductive_name,
                    universe_params,
                    ty: inductive_type(&params, &indices, sort_level),
                    data: Box::new(data),
                }
            }
            DeclPayload::MutualInductiveBlock {
                name,
                universe_params,
                universe_constraints,
                inductives,
            } => {
                let block_name = self.name_string(*name)?;
                let universe_params = self.universe_names(universe_params)?;
                let inductives = inductives
                    .iter()
                    .map(|inductive| {
                        let inductive_name = self.name_string(inductive.name)?;
                        let params = inductive
                            .params
                            .iter()
                            .enumerate()
                            .map(|(index, binder)| {
                                Ok(Binder::new(
                                    format!("p{index}"),
                                    self.expr_from_term(
                                        root_module,
                                        source_index,
                                        prior_decls,
                                        generated,
                                        binder.ty,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                        let indices = inductive
                            .indices
                            .iter()
                            .enumerate()
                            .map(|(index, binder)| {
                                Ok(Binder::new(
                                    format!("i{index}"),
                                    self.expr_from_term(
                                        root_module,
                                        source_index,
                                        prior_decls,
                                        generated,
                                        binder.ty,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                        let sort_level = self.level_from_node(inductive.sort)?;
                        let constructors = inductive
                            .constructors
                            .iter()
                            .map(|constructor| {
                                Ok(ConstructorDecl::new(
                                    self.name_string(constructor.name)?,
                                    self.expr_from_term(
                                        root_module,
                                        source_index,
                                        prior_decls,
                                        generated,
                                        constructor.ty,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                        let recursor = inductive
                            .recursor
                            .as_ref()
                            .map(|recursor| {
                                Ok::<_, CheckedCurrentDeclProjectionError>(
                                    RecursorDecl::with_rules(
                                        self.name_string(recursor.name)?,
                                        self.universe_names(&recursor.universe_params)?,
                                        self.expr_from_term(
                                            root_module,
                                            source_index,
                                            prior_decls,
                                            generated,
                                            recursor.ty,
                                        )?,
                                        npa_kernel::RecursorRules::new(
                                            recursor.rules.minor_start,
                                            recursor.rules.major_index,
                                        ),
                                    ),
                                )
                            })
                            .transpose()?;
                        Ok(InductiveDecl::new(
                            inductive_name,
                            universe_params.clone(),
                            params,
                            indices,
                            sort_level,
                            constructors,
                            recursor,
                        ))
                    })
                    .collect::<Result<Vec<_>, CheckedCurrentDeclProjectionError>>()?;
                let mut data = MutualInductiveBlock::new(
                    block_name.clone(),
                    universe_params.clone(),
                    inductives,
                );
                data.universe_constraints = self.universe_constraints(universe_constraints)?;
                Decl::MutualInductiveBlock {
                    name: block_name,
                    universe_params,
                    data: Box::new(data),
                }
            }
        })
    }

    fn expr_from_term(
        &self,
        root_module: &Name,
        source_index: u64,
        prior_decls: &[CurrentDeclIndexEntry],
        generated: &[CurrentGeneratedDeclEntry],
        term: TermId,
    ) -> Result<Expr, CheckedCurrentDeclProjectionError> {
        Ok(
            match self.term_table.get(term).ok_or({
                CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "term id out of range",
                }
            })? {
                TermNode::Sort(level) => Expr::sort(self.level_from_node(*level)?),
                TermNode::BVar(index) => Expr::bvar(*index),
                TermNode::Const { global_ref, levels } => Expr::konst(
                    self.global_ref_name(
                        root_module,
                        source_index,
                        prior_decls,
                        generated,
                        global_ref,
                    )?,
                    levels
                        .iter()
                        .map(|level| self.level_from_node(*level))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                TermNode::App(fun, arg) => Expr::app(
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *fun)?,
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *arg)?,
                ),
                TermNode::Lam { ty, body } => Expr::lam(
                    "_",
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *body)?,
                ),
                TermNode::Pi { ty, body } => Expr::pi(
                    "_",
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *body)?,
                ),
                TermNode::Let { ty, value, body } => Expr::let_in(
                    "_",
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *ty)?,
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *value)?,
                    self.expr_from_term(root_module, source_index, prior_decls, generated, *body)?,
                ),
            },
        )
    }

    fn global_ref_name(
        &self,
        _root_module: &Name,
        source_index: u64,
        prior_decls: &[CurrentDeclIndexEntry],
        generated: &[CurrentGeneratedDeclEntry],
        global_ref: &GlobalRef,
    ) -> Result<String, CheckedCurrentDeclProjectionError> {
        match global_ref {
            GlobalRef::Builtin { name, .. } | GlobalRef::Imported { name, .. } => {
                self.name_string(*name)
            }
            GlobalRef::Local { decl_index } if *decl_index == source_index as usize => {
                self.root_decl_name().map(|name| name.as_dotted())
            }
            GlobalRef::Local { decl_index } => prior_decls
                .iter()
                .find(|entry| entry.source_index == *decl_index as u64)
                .map(|entry| entry.signature.name.as_dotted())
                .ok_or(
                    CheckedCurrentDeclProjectionError::MissingCurrentDependency {
                        source_index,
                        dependency_source_index: *decl_index as u64,
                    },
                ),
            GlobalRef::LocalGenerated { decl_index, name } => {
                let generated_name = self.name(*name)?.clone();
                if *decl_index == source_index as usize {
                    return Ok(generated_name.as_dotted());
                }
                generated
                    .iter()
                    .find(|entry| {
                        entry.parent_source_index == *decl_index as u64
                            && entry.generated_name == generated_name
                    })
                    .map(|entry| entry.generated_name.as_dotted())
                    .ok_or({
                        CheckedCurrentDeclProjectionError::MissingCurrentGeneratedDependency {
                            source_index,
                            parent_source_index: *decl_index as u64,
                            generated_name,
                        }
                    })
            }
        }
    }

    fn level_from_node(&self, level: LevelId) -> Result<Level, CheckedCurrentDeclProjectionError> {
        Ok(
            match self.level_table.get(level).ok_or({
                CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "level id out of range",
                }
            })? {
                LevelNode::Zero => Level::zero(),
                LevelNode::Succ(inner) => Level::succ(self.level_from_node(*inner)?),
                LevelNode::Max(lhs, rhs) => {
                    Level::max(self.level_from_node(*lhs)?, self.level_from_node(*rhs)?)
                }
                LevelNode::IMax(lhs, rhs) => {
                    Level::imax(self.level_from_node(*lhs)?, self.level_from_node(*rhs)?)
                }
                LevelNode::Param(name) => Level::param(self.name_string(*name)?),
            },
        )
    }

    fn universe_names(
        &self,
        names: &[NameId],
    ) -> Result<Vec<String>, CheckedCurrentDeclProjectionError> {
        names.iter().map(|name| self.name_string(*name)).collect()
    }

    fn universe_constraints(
        &self,
        constraints: &[UniverseConstraintSpec],
    ) -> Result<Vec<UniverseConstraint>, CheckedCurrentDeclProjectionError> {
        constraints
            .iter()
            .map(|constraint| {
                Ok(UniverseConstraint {
                    lhs: self.level_from_node(constraint.lhs)?,
                    relation: constraint.relation,
                    rhs: self.level_from_node(constraint.rhs)?,
                })
            })
            .collect()
    }

    fn root_decl_name(&self) -> Result<Name, CheckedCurrentDeclProjectionError> {
        let name = match &self.root_decl {
            DeclPayload::Axiom { name, .. }
            | DeclPayload::AxiomConstrained { name, .. }
            | DeclPayload::Def { name, .. }
            | DeclPayload::DefConstrained { name, .. }
            | DeclPayload::Theorem { name, .. }
            | DeclPayload::TheoremConstrained { name, .. }
            | DeclPayload::Inductive { name, .. }
            | DeclPayload::InductiveConstrained { name, .. }
            | DeclPayload::MutualInductiveBlock { name, .. } => *name,
        };
        self.name(name).cloned()
    }

    fn name_string(&self, name: NameId) -> Result<String, CheckedCurrentDeclProjectionError> {
        Ok(self.name(name)?.as_dotted())
    }

    fn name(&self, name: NameId) -> Result<&Name, CheckedCurrentDeclProjectionError> {
        self.name_table
            .get(name)
            .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "name id out of range",
            })
    }
}

fn inductive_type(params: &[Binder], indices: &[Binder], sort: Level) -> Expr {
    params
        .iter()
        .chain(indices.iter())
        .rev()
        .fold(Expr::sort(sort), |body, binder| {
            Expr::pi(binder.name.clone(), binder.ty.clone(), body)
        })
}

struct PackageDecoder<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> PackageDecoder<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn is_done(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn tag(&mut self, expected: &'static str) -> Result<(), CheckedCurrentDeclProjectionError> {
        let actual = self.string()?;
        if actual == expected {
            Ok(())
        } else {
            Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "tag mismatch",
            })
        }
    }

    fn checked_decl_signature(
        &mut self,
    ) -> Result<MachineCheckedDeclSignature, CheckedCurrentDeclProjectionError> {
        self.tag("npa.machine-tactic.checked-decl-signature.v1")?;
        let name = self.name()?;
        let param_len = self.bounded_len()?;
        let universe_params = (0..param_len)
            .map(|_| self.string())
            .collect::<Result<Vec<_>, _>>()?;
        let ty = self.core_expr()?;
        let decl_interface_hash = self.hash()?;
        Ok(MachineCheckedDeclSignature {
            name,
            universe_params,
            ty,
            decl_interface_hash,
        })
    }

    fn core_decl_package(&mut self) -> Result<CoreDeclPackage, CheckedCurrentDeclProjectionError> {
        self.tag("npa.machine-api.current-core-decl-package.v1")?;
        self.tag("npa.machine-api.current-core-decl-package.name-table.v1")?;
        let name_table = self.name_table()?;
        self.tag("npa.machine-api.current-core-decl-package.level-table.v1")?;
        let level_table = self.level_table()?;
        self.tag("npa.machine-api.current-core-decl-package.term-table.v1")?;
        let term_table = self.term_table()?;
        self.tag("npa.machine-api.current-core-decl-package.root-decl.v1")?;
        let root_decl = self.decl_payload()?;
        let package = CoreDeclPackage {
            name_table,
            level_table,
            term_table,
            root_decl,
        };
        validate_core_decl_package(&package)?;
        Ok(package)
    }

    fn current_decl_dependency_report(
        &mut self,
    ) -> Result<CurrentDeclDependencyReport, CheckedCurrentDeclProjectionError> {
        self.tag("npa.machine-api.current-decl-dependency-report.v4")?;
        let dep_len = self.bounded_len()?;
        let mut direct_dependency_entries = Vec::with_capacity(dep_len);
        for _ in 0..dep_len {
            self.tag("npa.machine-api.current-decl-dependency-entry.v1")?;
            direct_dependency_entries.push(CurrentDeclDependencyEntry {
                dependency_ref: self.machine_dependency_ref_wire()?,
                decl_interface_hash: self.hash()?,
            });
        }
        let axiom_len = self.bounded_len()?;
        let mut axiom_dependencies = Vec::with_capacity(axiom_len);
        for _ in 0..axiom_len {
            axiom_dependencies.push(self.machine_axiom_ref_wire()?);
        }
        validate_dependency_entries_order(&direct_dependency_entries)?;
        validate_axiom_refs_order(&axiom_dependencies)?;
        Ok(CurrentDeclDependencyReport {
            direct_dependency_entries,
            axiom_dependencies,
        })
    }

    fn machine_dependency_ref_wire(
        &mut self,
    ) -> Result<MachineDependencyRefWire, CheckedCurrentDeclProjectionError> {
        self.tag("npa.machine-api.dependency-ref-wire.v2")?;
        Ok(match self.byte()? {
            0x00 => MachineDependencyRefWire::Imported {
                module: self.name()?,
                name: self.name()?,
                export_hash: self.hash()?,
            },
            0x01 => MachineDependencyRefWire::CurrentModule {
                module: self.name()?,
                name: self.name()?,
                source_index: self.u64()?,
            },
            0x02 => MachineDependencyRefWire::CurrentGenerated {
                module: self.name()?,
                generated_name: self.name()?,
                parent_source_index: self.u64()?,
            },
            0x03 => MachineDependencyRefWire::Builtin { name: self.name()? },
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown dependency ref tag",
                });
            }
        })
    }

    fn machine_axiom_ref_wire(
        &mut self,
    ) -> Result<MachineAxiomRefWire, CheckedCurrentDeclProjectionError> {
        self.tag("npa.machine-api.axiom-ref-wire.v1")?;
        Ok(match self.byte()? {
            0x00 => MachineAxiomRefWire::Imported {
                module: self.name()?,
                name: self.name()?,
                export_hash: self.hash()?,
                decl_interface_hash: self.hash()?,
            },
            0x01 => MachineAxiomRefWire::CurrentModule {
                module: self.name()?,
                name: self.name()?,
                source_index: self.u64()?,
                decl_interface_hash: self.hash()?,
            },
            0x02 => MachineAxiomRefWire::Builtin {
                name: self.name()?,
                decl_interface_hash: self.hash()?,
            },
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown axiom ref tag",
                });
            }
        })
    }

    fn name_table(&mut self) -> Result<Vec<Name>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len).map(|_| self.name()).collect()
    }

    fn level_table(&mut self) -> Result<Vec<LevelNode>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(match self.byte()? {
                    0x00 => LevelNode::Zero,
                    0x01 => LevelNode::Succ(self.usize()?),
                    0x02 => LevelNode::Max(self.usize()?, self.usize()?),
                    0x03 => LevelNode::IMax(self.usize()?, self.usize()?),
                    0x04 => LevelNode::Param(self.usize()?),
                    _ => {
                        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                            reason: "unknown level tag",
                        });
                    }
                })
            })
            .collect()
    }

    fn term_table(&mut self) -> Result<Vec<TermNode>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(match self.byte()? {
                    0x00 => TermNode::Sort(self.usize()?),
                    0x01 => TermNode::BVar(self.u32()?),
                    0x02 => TermNode::Const {
                        global_ref: self.global_ref()?,
                        levels: self.usize_vec()?,
                    },
                    0x03 => TermNode::App(self.usize()?, self.usize()?),
                    0x04 => TermNode::Lam {
                        ty: self.usize()?,
                        body: self.usize()?,
                    },
                    0x05 => TermNode::Pi {
                        ty: self.usize()?,
                        body: self.usize()?,
                    },
                    0x06 => TermNode::Let {
                        ty: self.usize()?,
                        value: self.usize()?,
                        body: self.usize()?,
                    },
                    _ => {
                        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                            reason: "unknown term tag",
                        });
                    }
                })
            })
            .collect()
    }

    fn decl_payload(&mut self) -> Result<DeclPayload, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x00 => DeclPayload::Axiom {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
            },
            0x10 => DeclPayload::AxiomConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
            },
            0x01 => DeclPayload::Def {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
                value: self.usize()?,
                reducibility: self.reducibility()?,
            },
            0x11 => DeclPayload::DefConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
                value: self.usize()?,
                reducibility: self.reducibility()?,
            },
            0x02 => DeclPayload::Theorem {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
                proof: self.usize()?,
                opacity: self.opacity()?,
            },
            0x12 => DeclPayload::TheoremConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
                proof: self.usize()?,
                opacity: self.opacity()?,
            },
            0x03 => {
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize()?;
                let constructors_len = self.bounded_len()?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize()?,
                        ty: self.usize()?,
                    });
                }
                let recursor = match self.byte()? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize()?,
                        universe_params: self.usize_vec()?,
                        ty: self.usize()?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize()?,
                            major_index: self.usize()?,
                        },
                    }),
                    _ => {
                        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                            reason: "unknown recursor option tag",
                        });
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
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let universe_constraints = self.universe_constraint_specs()?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize()?;
                let constructors_len = self.bounded_len()?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize()?,
                        ty: self.usize()?,
                    });
                }
                let recursor = match self.byte()? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize()?,
                        universe_params: self.usize_vec()?,
                        ty: self.usize()?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize()?,
                            major_index: self.usize()?,
                        },
                    }),
                    _ => {
                        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                            reason: "unknown recursor option tag",
                        });
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
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let universe_constraints = self.universe_constraint_specs()?;
                let inductive_len = self.bounded_len()?;
                let mut inductives = Vec::with_capacity(inductive_len);
                for _ in 0..inductive_len {
                    let inductive_name = self.usize()?;
                    let params = self.binder_types()?;
                    let indices = self.binder_types()?;
                    let sort = self.usize()?;
                    let constructors_len = self.bounded_len()?;
                    let mut constructors = Vec::with_capacity(constructors_len);
                    for _ in 0..constructors_len {
                        constructors.push(ConstructorSpec {
                            name: self.usize()?,
                            ty: self.usize()?,
                        });
                    }
                    let recursor = match self.byte()? {
                        0x00 => None,
                        0x01 => Some(RecursorSpec {
                            name: self.usize()?,
                            universe_params: self.usize_vec()?,
                            ty: self.usize()?,
                            rules: RecursorRulesSpec {
                                minor_start: self.usize()?,
                                major_index: self.usize()?,
                            },
                        }),
                        _ => {
                            return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                                reason: "unknown recursor option tag",
                            });
                        }
                    };
                    inductives.push(MutualInductiveSpec {
                        name: inductive_name,
                        params,
                        indices,
                        sort,
                        constructors,
                        recursor,
                    });
                }
                DeclPayload::MutualInductiveBlock {
                    name,
                    universe_params,
                    universe_constraints,
                    inductives,
                }
            }
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown declaration tag",
                });
            }
        })
    }

    fn universe_constraint_specs(
        &mut self,
    ) -> Result<Vec<UniverseConstraintSpec>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                let lhs = self.usize()?;
                let relation = match self.byte()? {
                    0x00 => npa_kernel::UniverseConstraintRelation::Le,
                    0x01 => npa_kernel::UniverseConstraintRelation::Eq,
                    _ => {
                        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                            reason: "unknown universe constraint relation tag",
                        });
                    }
                };
                Ok(UniverseConstraintSpec {
                    lhs,
                    relation,
                    rhs: self.usize()?,
                })
            })
            .collect()
    }

    fn binder_types(&mut self) -> Result<Vec<BinderType>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| Ok(BinderType { ty: self.usize()? }))
            .collect()
    }

    fn global_ref(&mut self) -> Result<GlobalRef, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x03 => GlobalRef::Builtin {
                name: self.usize()?,
                decl_interface_hash: self.hash()?,
            },
            0x00 => GlobalRef::Imported {
                import_index: self.usize()?,
                name: self.usize()?,
                decl_interface_hash: self.hash()?,
            },
            0x01 => GlobalRef::Local {
                decl_index: self.usize()?,
            },
            0x02 => GlobalRef::LocalGenerated {
                decl_index: self.usize()?,
                name: self.usize()?,
            },
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown global ref tag",
                });
            }
        })
    }

    fn core_expr(&mut self) -> Result<Expr, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x00 => Expr::sort(self.core_level()?),
            0x01 => Expr::bvar(self.u32()?),
            0x02 => {
                let name = self.name()?.as_dotted();
                let levels = self.usize()?;
                let levels = (0..levels)
                    .map(|_| self.core_level())
                    .collect::<Result<Vec<_>, _>>()?;
                Expr::konst(name, levels)
            }
            0x03 => Expr::app(self.core_expr()?, self.core_expr()?),
            0x04 => Expr::lam("_", self.core_expr()?, self.core_expr()?),
            0x05 => Expr::pi("_", self.core_expr()?, self.core_expr()?),
            0x06 => Expr::let_in("_", self.core_expr()?, self.core_expr()?, self.core_expr()?),
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown core expr tag",
                });
            }
        })
    }

    fn core_level(&mut self) -> Result<Level, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x00 => Level::zero(),
            0x01 => Level::succ(self.core_level()?),
            0x02 => Level::max(self.core_level()?, self.core_level()?),
            0x03 => Level::imax(self.core_level()?, self.core_level()?),
            0x04 => Level::param(self.name()?.as_dotted()),
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown core level tag",
                });
            }
        })
    }

    fn name(&mut self) -> Result<Name, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        if len == 0 {
            return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "empty name",
            });
        }
        let mut components = Vec::with_capacity(len);
        for _ in 0..len {
            let component = self.string()?;
            if component.is_empty() || component.contains('.') {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "non-canonical name",
                });
            }
            components.push(component);
        }
        Ok(Name(components))
    }

    fn reducibility(&mut self) -> Result<CertReducibility, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x00 => CertReducibility::Reducible,
            0x01 => CertReducibility::Opaque,
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown reducibility tag",
                });
            }
        })
    }

    fn opacity(&mut self) -> Result<Opacity, CheckedCurrentDeclProjectionError> {
        Ok(match self.byte()? {
            0x00 => Opacity::Opaque,
            _ => {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "unknown opacity tag",
                });
            }
        })
    }

    fn usize_vec(&mut self) -> Result<Vec<usize>, CheckedCurrentDeclProjectionError> {
        let len = self.bounded_len()?;
        (0..len).map(|_| self.usize()).collect()
    }

    fn hash(&mut self) -> Result<Hash, CheckedCurrentDeclProjectionError> {
        let bytes = self.take(32)?;
        let mut hash = [0; 32];
        hash.copy_from_slice(bytes);
        Ok(hash)
    }

    fn string(&mut self) -> Result<String, CheckedCurrentDeclProjectionError> {
        let len = self.usize()?;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| {
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "non-utf8 string",
            }
        })
    }

    fn bounded_len(&mut self) -> Result<usize, CheckedCurrentDeclProjectionError> {
        let len = self.usize()?;
        let remaining = self.bytes.len().saturating_sub(self.offset);
        if len > remaining {
            return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "length exceeds remaining bytes",
            });
        }
        Ok(len)
    }

    fn usize(&mut self) -> Result<usize, CheckedCurrentDeclProjectionError> {
        usize::try_from(self.u64()?).map_err(|_| CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "integer too large",
        })
    }

    fn u32(&mut self) -> Result<u32, CheckedCurrentDeclProjectionError> {
        u32::try_from(self.u64()?).map_err(|_| CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "integer too large",
        })
    }

    fn u64(&mut self) -> Result<u64, CheckedCurrentDeclProjectionError> {
        let start = self.offset;
        let mut shift = 0;
        let mut value = 0u64;
        loop {
            let byte = self.byte()?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                let mut canonical = Vec::new();
                encode_uvar(&mut canonical, value);
                if canonical != self.bytes[start..self.offset] {
                    return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                        reason: "non-canonical integer",
                    });
                }
                return Ok(value);
            }
            shift += 7;
            if shift >= 64 {
                return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "integer too large",
                });
            }
        }
    }

    fn byte(&mut self) -> Result<u8, CheckedCurrentDeclProjectionError> {
        let byte = *self.bytes.get(self.offset).ok_or(
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "unexpected eof",
            },
        )?;
        self.offset += 1;
        Ok(byte)
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], CheckedCurrentDeclProjectionError> {
        let end = self.offset.checked_add(len).ok_or(
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "length overflow",
            },
        )?;
        let bytes = self.bytes.get(self.offset..end).ok_or(
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "unexpected eof",
            },
        )?;
        self.offset = end;
        Ok(bytes)
    }
}

fn validate_core_decl_package(
    package: &CoreDeclPackage,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let mut names = BTreeSet::new();
    let mut levels = BTreeSet::new();
    let mut terms = BTreeSet::new();
    collect_decl_refs(
        &package.root_decl,
        &package.level_table,
        &package.term_table,
        &mut names,
        &mut levels,
        &mut terms,
    )?;
    ensure_full_table_reachability("name table", package.name_table.len(), &names)?;
    ensure_full_table_reachability("level table", package.level_table.len(), &levels)?;
    ensure_full_table_reachability("term table", package.term_table.len(), &terms)?;
    ensure_name_table_order(&package.name_table)?;
    ensure_level_table_order(&package.name_table, &package.level_table)?;
    ensure_level_table_normalized(&package.name_table, &package.level_table)?;
    ensure_term_table_order(package)?;

    ensure_no_duplicate_encoded_nodes(
        package.level_table.iter().map(encode_level_node_for_key),
        "duplicate level node",
    )?;
    ensure_no_duplicate_encoded_nodes(
        package.term_table.iter().map(encode_term_node_for_key),
        "duplicate term node",
    )?;
    Ok(())
}

fn ensure_name_table_order(names: &[Name]) -> Result<(), CheckedCurrentDeclProjectionError> {
    if names.windows(2).all(|window| window[0] < window[1]) {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "non-canonical name table order",
        })
    }
}

fn ensure_level_table_order(
    names: &[Name],
    levels: &[LevelNode],
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let keys = (0..levels.len())
        .map(|index| level_table_sort_key(index, names, levels))
        .collect::<Result<Vec<_>, _>>()?;
    if keys.windows(2).all(|window| window[0] < window[1]) {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "non-canonical level table order",
        })
    }
}

fn ensure_term_table_order(
    package: &CoreDeclPackage,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let keys = (0..package.term_table.len())
        .map(|index| term_table_sort_key(index, package))
        .collect::<Result<Vec<_>, _>>()?;
    if keys.windows(2).all(|window| window[0] < window[1]) {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "non-canonical term table order",
        })
    }
}

fn ensure_level_table_normalized(
    names: &[Name],
    levels: &[LevelNode],
) -> Result<(), CheckedCurrentDeclProjectionError> {
    for index in 0..levels.len() {
        let raw = raw_level_from_node(index, names, levels, &mut BTreeSet::new())?;
        if normalize_level(raw.clone()) != raw {
            return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "non-normalized level table entry",
            });
        }
    }
    Ok(())
}

fn ensure_full_table_reachability(
    table: &'static str,
    len: usize,
    used: &BTreeSet<usize>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    if used.len() == len && used.iter().copied().eq(0..len) {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed { reason: table })
    }
}

fn ensure_no_duplicate_encoded_nodes(
    nodes: impl Iterator<Item = Vec<u8>>,
    reason: &'static str,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let mut seen = BTreeSet::new();
    for node in nodes {
        if !seen.insert(node) {
            return Err(CheckedCurrentDeclProjectionError::DecodeFailed { reason });
        }
    }
    Ok(())
}

fn level_table_sort_key(
    index: usize,
    names: &[Name],
    levels: &[LevelNode],
) -> Result<(usize, Vec<u8>), CheckedCurrentDeclProjectionError> {
    Ok((
        level_height(index, levels, &mut BTreeSet::new())?,
        level_canonical_key(index, names, levels, &mut BTreeSet::new())?,
    ))
}

fn term_table_sort_key(
    index: usize,
    package: &CoreDeclPackage,
) -> Result<(usize, Vec<u8>), CheckedCurrentDeclProjectionError> {
    Ok((
        term_height(index, package, &mut BTreeSet::new())?,
        term_canonical_key(index, package, &mut BTreeSet::new())?,
    ))
}

fn level_height(
    index: usize,
    levels: &[LevelNode],
    visiting: &mut BTreeSet<usize>,
) -> Result<usize, CheckedCurrentDeclProjectionError> {
    if !visiting.insert(index) {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "cyclic level table",
        });
    }
    let height = match levels
        .get(index)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "level id out of range",
        })? {
        LevelNode::Zero | LevelNode::Param(_) => 0,
        LevelNode::Succ(inner) => level_height(*inner, levels, visiting)? + 1,
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            level_height(*lhs, levels, visiting)?.max(level_height(*rhs, levels, visiting)?) + 1
        }
    };
    visiting.remove(&index);
    Ok(height)
}

fn raw_level_from_node(
    index: usize,
    names: &[Name],
    levels: &[LevelNode],
    visiting: &mut BTreeSet<usize>,
) -> Result<Level, CheckedCurrentDeclProjectionError> {
    if !visiting.insert(index) {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "cyclic level table",
        });
    }
    let level = match levels
        .get(index)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "level id out of range",
        })? {
        LevelNode::Zero => Level::Zero,
        LevelNode::Succ(inner) => Level::Succ(Box::new(raw_level_from_node(
            *inner, names, levels, visiting,
        )?)),
        LevelNode::Max(lhs, rhs) => Level::Max(
            Box::new(raw_level_from_node(*lhs, names, levels, visiting)?),
            Box::new(raw_level_from_node(*rhs, names, levels, visiting)?),
        ),
        LevelNode::IMax(lhs, rhs) => Level::IMax(
            Box::new(raw_level_from_node(*lhs, names, levels, visiting)?),
            Box::new(raw_level_from_node(*rhs, names, levels, visiting)?),
        ),
        LevelNode::Param(name) => Level::Param(
            names
                .get(*name)
                .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
                    reason: "name id out of range",
                })?
                .as_dotted(),
        ),
    };
    visiting.remove(&index);
    Ok(level)
}

fn term_height(
    index: usize,
    package: &CoreDeclPackage,
    visiting: &mut BTreeSet<usize>,
) -> Result<usize, CheckedCurrentDeclProjectionError> {
    if !visiting.insert(index) {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "cyclic term table",
        });
    }
    let height = match package.term_table.get(index).ok_or(
        CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "term id out of range",
        },
    )? {
        TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
        TermNode::App(fun, arg) => {
            term_height(*fun, package, visiting)?.max(term_height(*arg, package, visiting)?) + 1
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            term_height(*ty, package, visiting)?.max(term_height(*body, package, visiting)?) + 1
        }
        TermNode::Let { ty, value, body } => {
            term_height(*ty, package, visiting)?
                .max(term_height(*value, package, visiting)?)
                .max(term_height(*body, package, visiting)?)
                + 1
        }
    };
    visiting.remove(&index);
    Ok(height)
}

fn level_canonical_key(
    index: usize,
    names: &[Name],
    levels: &[LevelNode],
    visiting: &mut BTreeSet<usize>,
) -> Result<Vec<u8>, CheckedCurrentDeclProjectionError> {
    if !visiting.insert(index) {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "cyclic level table",
        });
    }
    let mut out = Vec::new();
    match levels
        .get(index)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "level id out of range",
        })? {
        LevelNode::Zero => out.push(0x00),
        LevelNode::Succ(inner) => {
            out.push(0x01);
            out.extend(level_canonical_hash(*inner, names, levels, visiting)?);
        }
        LevelNode::Max(lhs, rhs) => {
            out.push(0x02);
            out.extend(level_canonical_hash(*lhs, names, levels, visiting)?);
            out.extend(level_canonical_hash(*rhs, names, levels, visiting)?);
        }
        LevelNode::IMax(lhs, rhs) => {
            out.push(0x03);
            out.extend(level_canonical_hash(*lhs, names, levels, visiting)?);
            out.extend(level_canonical_hash(*rhs, names, levels, visiting)?);
        }
        LevelNode::Param(name) => {
            out.push(0x04);
            encode_name(
                &mut out,
                names
                    .get(*name)
                    .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
                        reason: "name id out of range",
                    })?,
            );
        }
    }
    visiting.remove(&index);
    Ok(out)
}

fn level_canonical_hash(
    index: usize,
    names: &[Name],
    levels: &[LevelNode],
    visiting: &mut BTreeSet<usize>,
) -> Result<Hash, CheckedCurrentDeclProjectionError> {
    Ok(hash_with_domain(
        b"NPA-LEVEL-0.1",
        &level_canonical_key(index, names, levels, visiting)?,
    ))
}

fn term_canonical_key(
    index: usize,
    package: &CoreDeclPackage,
    visiting: &mut BTreeSet<usize>,
) -> Result<Vec<u8>, CheckedCurrentDeclProjectionError> {
    if !visiting.insert(index) {
        return Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "cyclic term table",
        });
    }
    let mut out = Vec::new();
    match package
        .term_table
        .get(index)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "term id out of range",
        })? {
        TermNode::Sort(level) => {
            out.push(0x00);
            out.extend(level_canonical_hash(
                *level,
                &package.name_table,
                &package.level_table,
                &mut BTreeSet::new(),
            )?);
        }
        TermNode::BVar(index) => {
            out.push(0x01);
            encode_uvar(&mut out, u64::from(*index));
        }
        TermNode::Const { global_ref, levels } => {
            out.push(0x02);
            encode_global_ref(&mut out, global_ref);
            encode_uvar(&mut out, levels.len() as u64);
            for level in levels {
                out.extend(level_canonical_hash(
                    *level,
                    &package.name_table,
                    &package.level_table,
                    &mut BTreeSet::new(),
                )?);
            }
        }
        TermNode::App(fun, arg) => {
            out.push(0x03);
            out.extend(term_canonical_hash(*fun, package, visiting)?);
            out.extend(term_canonical_hash(*arg, package, visiting)?);
        }
        TermNode::Lam { ty, body } => {
            out.push(0x04);
            out.extend(term_canonical_hash(*ty, package, visiting)?);
            out.extend(term_canonical_hash(*body, package, visiting)?);
        }
        TermNode::Pi { ty, body } => {
            out.push(0x05);
            out.extend(term_canonical_hash(*ty, package, visiting)?);
            out.extend(term_canonical_hash(*body, package, visiting)?);
        }
        TermNode::Let { ty, value, body } => {
            out.push(0x06);
            out.extend(term_canonical_hash(*ty, package, visiting)?);
            out.extend(term_canonical_hash(*value, package, visiting)?);
            out.extend(term_canonical_hash(*body, package, visiting)?);
        }
    }
    visiting.remove(&index);
    Ok(out)
}

fn term_canonical_hash(
    index: usize,
    package: &CoreDeclPackage,
    visiting: &mut BTreeSet<usize>,
) -> Result<Hash, CheckedCurrentDeclProjectionError> {
    Ok(hash_with_domain(
        b"NPA-TERM-0.1",
        &term_canonical_key(index, package, visiting)?,
    ))
}

fn collect_decl_refs(
    decl: &DeclPayload,
    levels: &[LevelNode],
    terms: &[TermNode],
    names: &mut BTreeSet<usize>,
    level_refs: &mut BTreeSet<usize>,
    term_refs: &mut BTreeSet<usize>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
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
            names.insert(*name);
            names.extend(universe_params);
            collect_universe_constraint_refs(
                root_decl_universe_constraints(decl),
                levels,
                names,
                level_refs,
            )?;
            collect_term_refs(*ty, levels, terms, names, level_refs, term_refs)?;
        }
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            ..
        }
        | DeclPayload::DefConstrained {
            name,
            universe_params,
            ty,
            value,
            ..
        } => {
            names.insert(*name);
            names.extend(universe_params);
            collect_universe_constraint_refs(
                root_decl_universe_constraints(decl),
                levels,
                names,
                level_refs,
            )?;
            collect_term_refs(*ty, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*value, levels, terms, names, level_refs, term_refs)?;
        }
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        }
        | DeclPayload::TheoremConstrained {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => {
            names.insert(*name);
            names.extend(universe_params);
            collect_universe_constraint_refs(
                root_decl_universe_constraints(decl),
                levels,
                names,
                level_refs,
            )?;
            collect_term_refs(*ty, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*proof, levels, terms, names, level_refs, term_refs)?;
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
            names.insert(*name);
            names.extend(universe_params);
            collect_universe_constraint_refs(
                root_decl_universe_constraints(decl),
                levels,
                names,
                level_refs,
            )?;
            collect_level_refs(*sort, levels, names, level_refs)?;
            let inductive_ty = inductive_export_type_term_id(params, indices, *sort, terms)?;
            collect_term_refs(inductive_ty, levels, terms, names, level_refs, term_refs)?;
            for binder in params.iter().chain(indices) {
                collect_term_refs(binder.ty, levels, terms, names, level_refs, term_refs)?;
            }
            for constructor in constructors {
                names.insert(constructor.name);
                collect_term_refs(constructor.ty, levels, terms, names, level_refs, term_refs)?;
            }
            if let Some(recursor) = recursor {
                names.insert(recursor.name);
                names.extend(&recursor.universe_params);
                collect_term_refs(recursor.ty, levels, terms, names, level_refs, term_refs)?;
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => {
            names.insert(*name);
            names.extend(universe_params);
            collect_universe_constraint_refs(universe_constraints, levels, names, level_refs)?;
            for inductive in inductives {
                names.insert(inductive.name);
                collect_level_refs(inductive.sort, levels, names, level_refs)?;
                let inductive_ty = inductive_export_type_term_id(
                    &inductive.params,
                    &inductive.indices,
                    inductive.sort,
                    terms,
                )?;
                collect_term_refs(inductive_ty, levels, terms, names, level_refs, term_refs)?;
                for binder in inductive.params.iter().chain(&inductive.indices) {
                    collect_term_refs(binder.ty, levels, terms, names, level_refs, term_refs)?;
                }
                for constructor in &inductive.constructors {
                    names.insert(constructor.name);
                    collect_term_refs(constructor.ty, levels, terms, names, level_refs, term_refs)?;
                }
                if let Some(recursor) = &inductive.recursor {
                    names.insert(recursor.name);
                    names.extend(&recursor.universe_params);
                    collect_term_refs(recursor.ty, levels, terms, names, level_refs, term_refs)?;
                }
            }
        }
    }
    Ok(())
}

fn root_decl_universe_constraints(decl: &DeclPayload) -> &[UniverseConstraintSpec] {
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

fn collect_universe_constraint_refs(
    constraints: &[UniverseConstraintSpec],
    levels: &[LevelNode],
    names: &mut BTreeSet<usize>,
    level_refs: &mut BTreeSet<usize>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    for constraint in constraints {
        collect_level_refs(constraint.lhs, levels, names, level_refs)?;
        collect_level_refs(constraint.rhs, levels, names, level_refs)?;
    }
    Ok(())
}

fn inductive_export_type_term_id(
    params: &[BinderType],
    indices: &[BinderType],
    sort: LevelId,
    terms: &[TermNode],
) -> Result<TermId, CheckedCurrentDeclProjectionError> {
    let mut body = find_term_node(terms, &TermNode::Sort(sort))?;
    for binder in params.iter().chain(indices).rev() {
        body = find_term_node(
            terms,
            &TermNode::Pi {
                ty: binder.ty,
                body,
            },
        )?;
    }
    Ok(body)
}

fn find_term_node(
    terms: &[TermNode],
    needle: &TermNode,
) -> Result<TermId, CheckedCurrentDeclProjectionError> {
    terms.iter().position(|term| term == needle).ok_or(
        CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "missing inductive export type term",
        },
    )
}

fn collect_term_refs(
    term: TermId,
    levels: &[LevelNode],
    terms: &[TermNode],
    names: &mut BTreeSet<usize>,
    level_refs: &mut BTreeSet<usize>,
    term_refs: &mut BTreeSet<usize>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    if !term_refs.insert(term) {
        return Ok(());
    }
    match terms
        .get(term)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "term id out of range",
        })? {
        TermNode::Sort(level) => collect_level_refs(*level, levels, names, level_refs)?,
        TermNode::BVar(_) => {}
        TermNode::Const {
            global_ref,
            levels: level_args,
        } => {
            collect_global_ref_names(global_ref, names);
            for level in level_args {
                collect_level_refs(*level, levels, names, level_refs)?;
            }
        }
        TermNode::App(fun, arg) => {
            collect_term_refs(*fun, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*arg, levels, terms, names, level_refs, term_refs)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_term_refs(*ty, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*body, levels, terms, names, level_refs, term_refs)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_term_refs(*ty, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*value, levels, terms, names, level_refs, term_refs)?;
            collect_term_refs(*body, levels, terms, names, level_refs, term_refs)?;
        }
    }
    Ok(())
}

fn collect_level_refs(
    level: LevelId,
    levels: &[LevelNode],
    names: &mut BTreeSet<usize>,
    level_refs: &mut BTreeSet<usize>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    if !level_refs.insert(level) {
        return Ok(());
    }
    match levels
        .get(level)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "level id out of range",
        })? {
        LevelNode::Zero => {}
        LevelNode::Succ(inner) => collect_level_refs(*inner, levels, names, level_refs)?,
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            collect_level_refs(*lhs, levels, names, level_refs)?;
            collect_level_refs(*rhs, levels, names, level_refs)?;
        }
        LevelNode::Param(name) => {
            names.insert(*name);
        }
    }
    Ok(())
}

fn collect_global_ref_names(global_ref: &GlobalRef, names: &mut BTreeSet<usize>) {
    match global_ref {
        GlobalRef::Builtin { name, .. } | GlobalRef::Imported { name, .. } => {
            names.insert(*name);
        }
        GlobalRef::Local { .. } => {}
        GlobalRef::LocalGenerated { name, .. } => {
            names.insert(*name);
        }
    }
}

fn validate_dependency_entries_order(
    entries: &[CurrentDeclDependencyEntry],
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let original = entries
        .iter()
        .map(encode_current_decl_dependency_entry)
        .collect::<Vec<_>>();
    let mut sorted = original.clone();
    sorted.sort();
    sorted.dedup();
    if original == sorted {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "non-canonical dependency report order",
        })
    }
}

fn validate_axiom_refs_order(
    entries: &[MachineAxiomRefWire],
) -> Result<(), CheckedCurrentDeclProjectionError> {
    let original = entries
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<Vec<_>>();
    let mut sorted = original.clone();
    sorted.sort();
    sorted.dedup();
    if original == sorted {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "non-canonical axiom report order",
        })
    }
}

fn sort_dedup_dependency_entries(entries: &mut Vec<CurrentDeclDependencyEntry>) {
    entries.sort_by_key(encode_current_decl_dependency_entry);
    entries.dedup_by(|lhs, rhs| {
        encode_current_decl_dependency_entry(lhs) == encode_current_decl_dependency_entry(rhs)
    });
}

fn sort_dedup_axiom_refs(entries: &mut Vec<MachineAxiomRefWire>) {
    entries.sort_by_key(encode_machine_axiom_ref_wire);
    entries.dedup_by(|lhs, rhs| {
        encode_machine_axiom_ref_wire(lhs) == encode_machine_axiom_ref_wire(rhs)
    });
}

fn encode_checked_current_decl_package(package: &DecodedCheckedCurrentDeclPackage) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.checked-current-decl-package.v5");
    encode_uvar(&mut out, package.source_index);
    out.extend(encode_checked_decl_signature(&package.signature));
    encode_core_decl_package_to(&mut out, &package.core_package);
    encode_current_decl_dependency_report_to(&mut out, &package.dependency_report);
    out.extend(package.prior_chain_fingerprint);
    out.extend(package.checked_env_fingerprint);
    out
}

fn encode_checked_decl_signature(signature: &MachineCheckedDeclSignature) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-tactic.checked-decl-signature.v1");
    encode_name(&mut out, &signature.name);
    encode_uvar(&mut out, signature.universe_params.len() as u64);
    for param in &signature.universe_params {
        encode_string(&mut out, param);
    }
    out.extend(npa_cert::core_expr_canonical_bytes(&signature.ty));
    out.extend(signature.decl_interface_hash);
    out
}

fn encode_core_decl_package_to(out: &mut Vec<u8>, package: &CoreDeclPackage) {
    encode_string(out, "npa.machine-api.current-core-decl-package.v1");
    encode_string(
        out,
        "npa.machine-api.current-core-decl-package.name-table.v1",
    );
    encode_name_table_to(out, &package.name_table);
    encode_string(
        out,
        "npa.machine-api.current-core-decl-package.level-table.v1",
    );
    encode_level_table_to(out, &package.level_table);
    encode_string(
        out,
        "npa.machine-api.current-core-decl-package.term-table.v1",
    );
    encode_term_table_to(out, &package.term_table);
    encode_string(
        out,
        "npa.machine-api.current-core-decl-package.root-decl.v1",
    );
    encode_decl_payload_to(out, &package.root_decl);
}

fn encode_current_decl_dependency_report_to(
    out: &mut Vec<u8>,
    report: &CurrentDeclDependencyReport,
) {
    encode_string(out, "npa.machine-api.current-decl-dependency-report.v4");
    encode_uvar(out, report.direct_dependency_entries.len() as u64);
    for entry in &report.direct_dependency_entries {
        out.extend(encode_current_decl_dependency_entry(entry));
    }
    encode_uvar(out, report.axiom_dependencies.len() as u64);
    for axiom in &report.axiom_dependencies {
        out.extend(encode_machine_axiom_ref_wire(axiom));
    }
}

fn encode_current_decl_dependency_entry(entry: &CurrentDeclDependencyEntry) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.current-decl-dependency-entry.v1");
    out.extend(encode_machine_dependency_ref_wire(&entry.dependency_ref));
    out.extend(entry.decl_interface_hash);
    out
}

fn encode_machine_dependency_ref_wire(value: &MachineDependencyRefWire) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.dependency-ref-wire.v2");
    match value {
        MachineDependencyRefWire::Imported {
            module,
            name,
            export_hash,
        } => {
            out.push(0x00);
            encode_name(&mut out, module);
            encode_name(&mut out, name);
            out.extend(export_hash);
        }
        MachineDependencyRefWire::CurrentModule {
            module,
            name,
            source_index,
        } => {
            out.push(0x01);
            encode_name(&mut out, module);
            encode_name(&mut out, name);
            encode_uvar(&mut out, *source_index);
        }
        MachineDependencyRefWire::CurrentGenerated {
            module,
            generated_name,
            parent_source_index,
        } => {
            out.push(0x02);
            encode_name(&mut out, module);
            encode_name(&mut out, generated_name);
            encode_uvar(&mut out, *parent_source_index);
        }
        MachineDependencyRefWire::Builtin { name } => {
            out.push(0x03);
            encode_name(&mut out, name);
        }
    }
    out
}

pub(crate) fn encode_machine_axiom_ref_wire(value: &MachineAxiomRefWire) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.axiom-ref-wire.v1");
    match value {
        MachineAxiomRefWire::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_name(&mut out, module);
            encode_name(&mut out, name);
            out.extend(export_hash);
            out.extend(decl_interface_hash);
        }
        MachineAxiomRefWire::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
        } => {
            out.push(0x01);
            encode_name(&mut out, module);
            encode_name(&mut out, name);
            encode_uvar(&mut out, *source_index);
            out.extend(decl_interface_hash);
        }
        MachineAxiomRefWire::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x02);
            encode_name(&mut out, name);
            out.extend(decl_interface_hash);
        }
    }
    out
}

fn encode_name_table_to(out: &mut Vec<u8>, names: &[Name]) {
    encode_uvar(out, names.len() as u64);
    for name in names {
        encode_name(out, name);
    }
}

fn encode_level_table_to(out: &mut Vec<u8>, levels: &[LevelNode]) {
    encode_uvar(out, levels.len() as u64);
    for level in levels {
        encode_level_node_to(out, level);
    }
}

fn encode_term_table_to(out: &mut Vec<u8>, terms: &[TermNode]) {
    encode_uvar(out, terms.len() as u64);
    for term in terms {
        encode_term_node_to(out, term);
    }
}

fn encode_decl_payload_to(out: &mut Vec<u8>, decl: &DeclPayload) {
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => {
            out.push(0x00);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar(out, *ty as u64);
        }
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            out.push(0x10);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs(out, universe_constraints);
            encode_uvar(out, *ty as u64);
        }
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => {
            out.push(0x01);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *value as u64);
            encode_reducibility(out, *reducibility);
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
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs(out, universe_constraints);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *value as u64);
            encode_reducibility(out, *reducibility);
        }
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            opacity,
        } => {
            out.push(0x02);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *proof as u64);
            encode_opacity(out, *opacity);
        }
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
            opacity,
        } => {
            out.push(0x12);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs(out, universe_constraints);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *proof as u64);
            encode_opacity(out, *opacity);
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
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar(out, params.len() as u64);
            for param in params {
                encode_uvar(out, param.ty as u64);
            }
            encode_uvar(out, indices.len() as u64);
            for index in indices {
                encode_uvar(out, index.ty as u64);
            }
            encode_uvar(out, *sort as u64);
            encode_uvar(out, constructors.len() as u64);
            for constructor in constructors {
                encode_uvar(out, constructor.name as u64);
                encode_uvar(out, constructor.ty as u64);
            }
            match recursor {
                Some(recursor) => {
                    out.push(0x01);
                    encode_uvar(out, recursor.name as u64);
                    encode_usize_vec(out, &recursor.universe_params);
                    encode_uvar(out, recursor.ty as u64);
                    encode_uvar(out, recursor.rules.minor_start as u64);
                    encode_uvar(out, recursor.rules.major_index as u64);
                }
                None => out.push(0x00),
            }
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
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs(out, universe_constraints);
            encode_uvar(out, params.len() as u64);
            for param in params {
                encode_uvar(out, param.ty as u64);
            }
            encode_uvar(out, indices.len() as u64);
            for index in indices {
                encode_uvar(out, index.ty as u64);
            }
            encode_uvar(out, *sort as u64);
            encode_uvar(out, constructors.len() as u64);
            for constructor in constructors {
                encode_uvar(out, constructor.name as u64);
                encode_uvar(out, constructor.ty as u64);
            }
            match recursor {
                Some(recursor) => {
                    out.push(0x01);
                    encode_uvar(out, recursor.name as u64);
                    encode_usize_vec(out, &recursor.universe_params);
                    encode_uvar(out, recursor.ty as u64);
                    encode_uvar(out, recursor.rules.minor_start as u64);
                    encode_uvar(out, recursor.rules.major_index as u64);
                }
                None => out.push(0x00),
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => {
            out.push(0x04);
            encode_uvar(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs(out, universe_constraints);
            encode_uvar(out, inductives.len() as u64);
            for inductive in inductives {
                encode_uvar(out, inductive.name as u64);
                encode_uvar(out, inductive.params.len() as u64);
                for param in &inductive.params {
                    encode_uvar(out, param.ty as u64);
                }
                encode_uvar(out, inductive.indices.len() as u64);
                for index in &inductive.indices {
                    encode_uvar(out, index.ty as u64);
                }
                encode_uvar(out, inductive.sort as u64);
                encode_uvar(out, inductive.constructors.len() as u64);
                for constructor in &inductive.constructors {
                    encode_uvar(out, constructor.name as u64);
                    encode_uvar(out, constructor.ty as u64);
                }
                match &inductive.recursor {
                    Some(recursor) => {
                        out.push(0x01);
                        encode_uvar(out, recursor.name as u64);
                        encode_usize_vec(out, &recursor.universe_params);
                        encode_uvar(out, recursor.ty as u64);
                        encode_uvar(out, recursor.rules.minor_start as u64);
                        encode_uvar(out, recursor.rules.major_index as u64);
                    }
                    None => out.push(0x00),
                }
            }
        }
    }
}

fn encode_universe_constraint_specs(out: &mut Vec<u8>, constraints: &[UniverseConstraintSpec]) {
    encode_uvar(out, constraints.len() as u64);
    for constraint in constraints {
        encode_uvar(out, constraint.lhs as u64);
        out.push(match constraint.relation {
            npa_kernel::UniverseConstraintRelation::Le => 0x00,
            npa_kernel::UniverseConstraintRelation::Eq => 0x01,
        });
        encode_uvar(out, constraint.rhs as u64);
    }
}

fn encode_level_node_for_key(level: &LevelNode) -> Vec<u8> {
    let mut out = Vec::new();
    encode_level_node_to(&mut out, level);
    out
}

fn encode_level_node_to(out: &mut Vec<u8>, level: &LevelNode) {
    match level {
        LevelNode::Zero => out.push(0x00),
        LevelNode::Succ(inner) => {
            out.push(0x01);
            encode_uvar(out, *inner as u64);
        }
        LevelNode::Max(lhs, rhs) => {
            out.push(0x02);
            encode_uvar(out, *lhs as u64);
            encode_uvar(out, *rhs as u64);
        }
        LevelNode::IMax(lhs, rhs) => {
            out.push(0x03);
            encode_uvar(out, *lhs as u64);
            encode_uvar(out, *rhs as u64);
        }
        LevelNode::Param(name) => {
            out.push(0x04);
            encode_uvar(out, *name as u64);
        }
    }
}

fn encode_term_node_for_key(term: &TermNode) -> Vec<u8> {
    let mut out = Vec::new();
    encode_term_node_to(&mut out, term);
    out
}

fn encode_term_node_to(out: &mut Vec<u8>, term: &TermNode) {
    match term {
        TermNode::Sort(level) => {
            out.push(0x00);
            encode_uvar(out, *level as u64);
        }
        TermNode::BVar(index) => {
            out.push(0x01);
            encode_uvar(out, u64::from(*index));
        }
        TermNode::Const { global_ref, levels } => {
            out.push(0x02);
            encode_global_ref(out, global_ref);
            encode_usize_vec(out, levels);
        }
        TermNode::App(fun, arg) => {
            out.push(0x03);
            encode_uvar(out, *fun as u64);
            encode_uvar(out, *arg as u64);
        }
        TermNode::Lam { ty, body } => {
            out.push(0x04);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *body as u64);
        }
        TermNode::Pi { ty, body } => {
            out.push(0x05);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *body as u64);
        }
        TermNode::Let { ty, value, body } => {
            out.push(0x06);
            encode_uvar(out, *ty as u64);
            encode_uvar(out, *value as u64);
            encode_uvar(out, *body as u64);
        }
    }
}

fn encode_global_ref(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar(out, *import_index as u64);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar(out, *decl_index as u64);
            encode_uvar(out, *name as u64);
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
    }
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn encode_usize_vec(out: &mut Vec<u8>, values: &[usize]) {
    encode_uvar(out, values.len() as u64);
    for value in values {
        encode_uvar(out, *value as u64);
    }
}

fn encode_reducibility(out: &mut Vec<u8>, reducibility: CertReducibility) {
    out.push(match reducibility {
        CertReducibility::Reducible => 0x00,
        CertReducibility::Opaque => 0x01,
    });
}

fn encode_opacity(out: &mut Vec<u8>, _opacity: Opacity) {
    out.push(0x00);
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
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

fn derive_dependency_report(
    root_module: &Name,
    source_index: u64,
    imports: &MachineImportCertificateContext,
    direct_import_entries: &[&VerifiedModuleContextEntry],
    package: &CoreDeclPackage,
    prior_decls: &[CurrentDeclIndexEntry],
    generated: &[CurrentGeneratedDeclEntry],
) -> Result<CurrentDeclDependencyReport, CheckedCurrentDeclProjectionError> {
    let mut direct_dependency_entries = Vec::new();
    for global_ref in root_decl_global_refs(package)? {
        if is_inductive_bundle_internal_ref(package, source_index, &global_ref) {
            continue;
        }
        direct_dependency_entries.push(global_ref_to_dependency_entry(
            root_module,
            source_index,
            direct_import_entries,
            package,
            prior_decls,
            generated,
            &global_ref,
        )?);
    }
    sort_dedup_dependency_entries(&mut direct_dependency_entries);

    let mut axiom_dependencies = Vec::new();
    for entry in &direct_dependency_entries {
        match &entry.dependency_ref {
            MachineDependencyRefWire::Imported {
                module,
                name,
                export_hash,
            } => {
                let import_entry = direct_import_entries
                    .iter()
                    .find(|entry| {
                        entry.key.module == *module && entry.key.export_hash == *export_hash
                    })
                    .ok_or_else(
                        || CheckedCurrentDeclProjectionError::MissingImportedExport {
                            source_index,
                            module: module.clone(),
                            name: name.clone(),
                            decl_interface_hash: entry.decl_interface_hash,
                        },
                    )?;
                let export =
                    imported_export_by_name_hash(import_entry, name, &entry.decl_interface_hash)
                        .ok_or_else(|| {
                            CheckedCurrentDeclProjectionError::MissingImportedExport {
                                source_index,
                                module: module.clone(),
                                name: name.clone(),
                                decl_interface_hash: entry.decl_interface_hash,
                            }
                        })?;
                for axiom in &export.axiom_dependencies {
                    axiom_dependencies.push(imported_axiom_ref_to_wire(
                        source_index,
                        imports,
                        import_entry,
                        axiom,
                    )?);
                }
            }
            MachineDependencyRefWire::CurrentModule {
                source_index: dependency_source_index,
                ..
            } => {
                let prior = prior_decls
                    .iter()
                    .find(|decl| decl.source_index == *dependency_source_index)
                    .ok_or(
                        CheckedCurrentDeclProjectionError::MissingCurrentDependency {
                            source_index,
                            dependency_source_index: *dependency_source_index,
                        },
                    )?;
                axiom_dependencies.extend(prior.dependency_report.axiom_dependencies.clone());
            }
            MachineDependencyRefWire::CurrentGenerated {
                parent_source_index,
                generated_name,
                ..
            } => {
                let parent = prior_decls
                    .iter()
                    .find(|decl| decl.source_index == *parent_source_index)
                    .ok_or_else(|| {
                        CheckedCurrentDeclProjectionError::MissingCurrentGeneratedDependency {
                            source_index,
                            parent_source_index: *parent_source_index,
                            generated_name: generated_name.clone(),
                        }
                    })?;
                axiom_dependencies.extend(parent.dependency_report.axiom_dependencies.clone());
            }
            MachineDependencyRefWire::Builtin { name } => {
                if let Some(axiom) =
                    builtin_axiom_ref_to_wire(source_index, name, entry.decl_interface_hash)?
                {
                    axiom_dependencies.push(axiom);
                }
            }
        }
    }
    sort_dedup_axiom_refs(&mut axiom_dependencies);

    Ok(CurrentDeclDependencyReport {
        direct_dependency_entries,
        axiom_dependencies,
    })
}

fn root_decl_global_refs(
    package: &CoreDeclPackage,
) -> Result<Vec<GlobalRef>, CheckedCurrentDeclProjectionError> {
    let mut refs = Vec::new();
    match &package.root_decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
            collect_global_refs_from_term(package, *ty, &mut refs)?;
        }
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            collect_global_refs_from_term(package, *ty, &mut refs)?;
            collect_global_refs_from_term(package, *value, &mut refs)?;
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => {
            collect_global_refs_from_term(package, *ty, &mut refs)?;
            collect_global_refs_from_term(package, *proof, &mut refs)?;
        }
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
        } => {
            for binder in params.iter().chain(indices) {
                collect_global_refs_from_term(package, binder.ty, &mut refs)?;
            }
            for constructor in constructors {
                collect_global_refs_from_term(package, constructor.ty, &mut refs)?;
            }
            if let Some(recursor) = recursor {
                collect_global_refs_from_term(package, recursor.ty, &mut refs)?;
            }
        }
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                for binder in inductive.params.iter().chain(&inductive.indices) {
                    collect_global_refs_from_term(package, binder.ty, &mut refs)?;
                }
                for constructor in &inductive.constructors {
                    collect_global_refs_from_term(package, constructor.ty, &mut refs)?;
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_global_refs_from_term(package, recursor.ty, &mut refs)?;
                }
            }
        }
    }
    Ok(refs)
}

fn collect_global_refs_from_term(
    package: &CoreDeclPackage,
    term: TermId,
    refs: &mut Vec<GlobalRef>,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    match package
        .term_table
        .get(term)
        .ok_or(CheckedCurrentDeclProjectionError::DecodeFailed {
            reason: "term id out of range",
        })? {
        TermNode::Sort(_) | TermNode::BVar(_) => {}
        TermNode::Const { global_ref, .. } => refs.push(global_ref.clone()),
        TermNode::App(fun, arg) => {
            collect_global_refs_from_term(package, *fun, refs)?;
            collect_global_refs_from_term(package, *arg, refs)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_global_refs_from_term(package, *ty, refs)?;
            collect_global_refs_from_term(package, *body, refs)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_global_refs_from_term(package, *ty, refs)?;
            collect_global_refs_from_term(package, *value, refs)?;
            collect_global_refs_from_term(package, *body, refs)?;
        }
    }
    Ok(())
}

fn is_inductive_bundle_internal_ref(
    package: &CoreDeclPackage,
    source_index: u64,
    global_ref: &GlobalRef,
) -> bool {
    matches!(
        package.root_decl,
        DeclPayload::Inductive { .. } | DeclPayload::InductiveConstrained { .. }
    ) && match global_ref {
        GlobalRef::Local { decl_index } => *decl_index == source_index as usize,
        GlobalRef::LocalGenerated { decl_index, .. } => *decl_index == source_index as usize,
        _ => false,
    }
}

fn global_ref_to_dependency_entry(
    root_module: &Name,
    source_index: u64,
    direct_import_entries: &[&VerifiedModuleContextEntry],
    package: &CoreDeclPackage,
    prior_decls: &[CurrentDeclIndexEntry],
    generated: &[CurrentGeneratedDeclEntry],
    global_ref: &GlobalRef,
) -> Result<CurrentDeclDependencyEntry, CheckedCurrentDeclProjectionError> {
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let import_entry = direct_import_entries.get(*import_index).ok_or(
                CheckedCurrentDeclProjectionError::MissingImportedDependency {
                    source_index,
                    import_index: *import_index,
                },
            )?;
            let name = package.name(*name)?.clone();
            imported_export_by_name_hash(import_entry, &name, decl_interface_hash).ok_or_else(
                || CheckedCurrentDeclProjectionError::MissingImportedExport {
                    source_index,
                    module: import_entry.key.module.clone(),
                    name: name.clone(),
                    decl_interface_hash: *decl_interface_hash,
                },
            )?;
            Ok(CurrentDeclDependencyEntry {
                dependency_ref: MachineDependencyRefWire::Imported {
                    module: import_entry.key.module.clone(),
                    name,
                    export_hash: import_entry.key.export_hash,
                },
                decl_interface_hash: *decl_interface_hash,
            })
        }
        GlobalRef::Local { decl_index } if *decl_index < source_index as usize => {
            let prior = prior_decls
                .iter()
                .find(|decl| decl.source_index == *decl_index as u64)
                .ok_or(
                    CheckedCurrentDeclProjectionError::MissingCurrentDependency {
                        source_index,
                        dependency_source_index: *decl_index as u64,
                    },
                )?;
            Ok(CurrentDeclDependencyEntry {
                dependency_ref: MachineDependencyRefWire::CurrentModule {
                    module: root_module.clone(),
                    name: prior.signature.name.clone(),
                    source_index: prior.source_index,
                },
                decl_interface_hash: prior.signature.decl_interface_hash,
            })
        }
        GlobalRef::Local { decl_index } => {
            Err(CheckedCurrentDeclProjectionError::InvalidFutureDependency {
                source_index,
                dependency_source_index: *decl_index as u64,
            })
        }
        GlobalRef::LocalGenerated { decl_index, name } if *decl_index < source_index as usize => {
            let generated_name = package.name(*name)?.clone();
            let generated = generated
                .iter()
                .find(|entry| {
                    entry.parent_source_index == *decl_index as u64
                        && entry.generated_name == generated_name
                })
                .ok_or_else(|| {
                    CheckedCurrentDeclProjectionError::MissingCurrentGeneratedDependency {
                        source_index,
                        parent_source_index: *decl_index as u64,
                        generated_name: generated_name.clone(),
                    }
                })?;
            Ok(CurrentDeclDependencyEntry {
                dependency_ref: MachineDependencyRefWire::CurrentGenerated {
                    module: root_module.clone(),
                    generated_name,
                    parent_source_index: generated.parent_source_index,
                },
                decl_interface_hash: generated.parent_decl_interface_hash,
            })
        }
        GlobalRef::LocalGenerated { decl_index, name } => Err(
            CheckedCurrentDeclProjectionError::MissingCurrentGeneratedDependency {
                source_index,
                parent_source_index: *decl_index as u64,
                generated_name: package
                    .name(*name)
                    .cloned()
                    .unwrap_or_else(|_| Name(vec!["<invalid>".to_owned()])),
            },
        ),
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = package.name(*name)?.clone();
            ensure_builtin_ref(source_index, &name, *decl_interface_hash)?;
            Ok(CurrentDeclDependencyEntry {
                dependency_ref: MachineDependencyRefWire::Builtin { name },
                decl_interface_hash: *decl_interface_hash,
            })
        }
    }
}

fn imported_export_by_name_hash<'a>(
    entry: &'a VerifiedModuleContextEntry,
    name: &Name,
    decl_interface_hash: &Hash,
) -> Option<&'a npa_cert::ExportEntry> {
    let name_id = entry
        .decoded_name_table
        .iter()
        .position(|candidate| candidate == name)?;
    entry
        .export_block
        .iter()
        .find(|export| export.name == name_id && &export.decl_interface_hash == decl_interface_hash)
}

pub(crate) fn imported_axiom_ref_to_wire(
    source_index: u64,
    imports: &MachineImportCertificateContext,
    owner: &VerifiedModuleContextEntry,
    axiom: &AxiomRef,
) -> Result<MachineAxiomRefWire, CheckedCurrentDeclProjectionError> {
    match &axiom.global_ref {
        GlobalRef::Local { decl_index } => {
            let decl = owner.decl_index_table.get(*decl_index).ok_or_else(|| {
                CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: owner.key.module.clone(),
                }
            })?;
            if !matches!(
                decl.decl,
                DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. }
            ) {
                return Err(CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: decl.name.clone(),
                });
            }
            Ok(MachineAxiomRefWire::Imported {
                module: owner.key.module.clone(),
                name: decl.name.clone(),
                export_hash: owner.key.export_hash,
                decl_interface_hash: decl.hashes.decl_interface_hash,
            })
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let key = owner
                .certificate_import_table
                .get(*import_index)
                .ok_or_else(|| CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: owner.key.module.clone(),
                })?;
            let transitive = imports
                .verified_modules()
                .iter()
                .find(|entry| &entry.key == key)
                .ok_or_else(|| CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: key.module.clone(),
                })?;
            let axiom_name = owner
                .decoded_name_table
                .get(*name)
                .cloned()
                .ok_or_else(|| CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: owner.key.module.clone(),
                })?;
            let decl = transitive
                .decl_index_table
                .iter()
                .find(|decl| {
                    decl.name == axiom_name
                        && decl.hashes.decl_interface_hash == *decl_interface_hash
                })
                .ok_or_else(|| CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: axiom_name.clone(),
                })?;
            if !matches!(
                decl.decl,
                DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. }
            ) {
                return Err(CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: axiom_name,
                });
            }
            Ok(MachineAxiomRefWire::Imported {
                module: key.module.clone(),
                name: decl.name.clone(),
                export_hash: key.export_hash,
                decl_interface_hash: *decl_interface_hash,
            })
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = owner
                .decoded_name_table
                .get(*name)
                .cloned()
                .ok_or_else(|| CheckedCurrentDeclProjectionError::InvalidAxiomRef {
                    source_index,
                    name: owner.key.module.clone(),
                })?;
            builtin_axiom_ref_to_wire(source_index, &name, *decl_interface_hash)?
                .ok_or(CheckedCurrentDeclProjectionError::InvalidAxiomRef { source_index, name })
        }
        GlobalRef::LocalGenerated { name, .. } => {
            let name = owner
                .decoded_name_table
                .get(*name)
                .cloned()
                .unwrap_or_else(|| owner.key.module.clone());
            Err(CheckedCurrentDeclProjectionError::InvalidAxiomRef { source_index, name })
        }
    }
}

fn builtin_axiom_ref_to_wire(
    source_index: u64,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<Option<MachineAxiomRefWire>, CheckedCurrentDeclProjectionError> {
    ensure_builtin_ref(source_index, name, decl_interface_hash)?;
    if is_builtin_axiom_name(name) {
        Ok(Some(MachineAxiomRefWire::Builtin {
            name: name.clone(),
            decl_interface_hash,
        }))
    } else {
        Ok(None)
    }
}

fn ensure_builtin_ref(
    source_index: u64,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    if npa_cert::builtin_decl_interface_hash(name) == Some(decl_interface_hash) {
        Ok(())
    } else {
        Err(
            CheckedCurrentDeclProjectionError::InvalidBuiltinDependency {
                source_index,
                name: name.clone(),
            },
        )
    }
}

fn is_builtin_axiom_name(name: &Name) -> bool {
    name.as_dotted() == "Eq.rec"
}

fn project_current_generated_decl_table(
    root_module: &Name,
    source_index: u64,
    signature: &MachineCheckedDeclSignature,
    decl: &Decl,
) -> Result<Vec<CurrentGeneratedDeclEntry>, CheckedCurrentDeclProjectionError> {
    let Decl::Inductive { data, .. } = decl else {
        return Ok(Vec::new());
    };
    let mut entries = Vec::new();
    for constructor in &data.constructors {
        let generated_name = Name::from_dotted(&constructor.name);
        ensure_name_has_module_prefix(root_module, &generated_name)?;
        entries.push(CurrentGeneratedDeclEntry {
            module: root_module.clone(),
            parent_source_index: source_index,
            parent_name: signature.name.clone(),
            parent_decl_interface_hash: signature.decl_interface_hash,
            generated_name,
            generated_decl_interface_hash: signature.decl_interface_hash,
            kind: CurrentGeneratedDeclKind::Constructor,
            ty: constructor.ty.clone(),
        });
    }
    if let Some(recursor) = &data.recursor {
        let generated_name = Name::from_dotted(&recursor.name);
        ensure_name_has_module_prefix(root_module, &generated_name)?;
        entries.push(CurrentGeneratedDeclEntry {
            module: root_module.clone(),
            parent_source_index: source_index,
            parent_name: signature.name.clone(),
            parent_decl_interface_hash: signature.decl_interface_hash,
            generated_name,
            generated_decl_interface_hash: signature.decl_interface_hash,
            kind: CurrentGeneratedDeclKind::Recursor,
            ty: recursor.ty.clone(),
        });
    }
    Ok(entries)
}

fn ensure_name_has_module_prefix(
    module: &Name,
    name: &Name,
) -> Result<(), CheckedCurrentDeclProjectionError> {
    if name.0.starts_with(&module.0) && name.0.len() > module.0.len() {
        Ok(())
    } else {
        Err(CheckedCurrentDeclProjectionError::ModulePrefixMismatch {
            module: module.clone(),
            name: name.clone(),
        })
    }
}

#[cfg(test)]
pub(crate) fn encode_checked_current_decl_package_for_test(
    root_module: &Name,
    source_index: u64,
    decl: Decl,
) -> Vec<u8> {
    let cert = npa_cert::build_module_cert(
        npa_cert::CoreModule {
            name: root_module.clone(),
            declarations: vec![decl.clone()],
        },
        &[],
    )
    .expect("test current declaration should build as a standalone certificate");
    let root_decl = cert
        .declarations
        .into_iter()
        .next()
        .expect("test certificate should contain the current declaration")
        .decl;
    let core_package = canonicalize_core_decl_package_tables_for_test(CoreDeclPackage {
        name_table: cert.name_table,
        level_table: cert.level_table,
        term_table: cert.term_table,
        root_decl,
    });
    let checked =
        check_current_decl_for_machine_tactic_from_verified_imports(&[], &[], source_index, decl)
            .expect("test current declaration should pass machine tactic current checking");
    let imports = MachineImportCertificateContext::empty();
    let dependency_report = derive_dependency_report(
        root_module,
        source_index,
        &imports,
        &[],
        &core_package,
        &[],
        &[],
    )
    .expect("test current declaration dependency report should be derivable");
    let decoded = DecodedCheckedCurrentDeclPackage {
        source_index,
        signature: MachineCheckedDeclSignature {
            name: checked.signature().name().clone(),
            universe_params: checked.signature().universe_params().to_vec(),
            ty: checked.signature().ty().clone(),
            decl_interface_hash: checked.signature().decl_interface_hash(),
        },
        signature_canonical_bytes: checked_decl_signature_canonical_bytes(checked.signature()),
        core_package,
        dependency_report,
        prior_chain_fingerprint: checked.prior_chain_fingerprint(),
        checked_env_fingerprint: checked.checked_env_fingerprint(),
        canonical_bytes: Vec::new(),
    };
    encode_checked_current_decl_package(&decoded)
}

#[cfg(test)]
fn canonicalize_core_decl_package_tables_for_test(package: CoreDeclPackage) -> CoreDeclPackage {
    let mut name_refs = BTreeSet::new();
    let mut level_refs = BTreeSet::new();
    let mut term_refs = BTreeSet::new();
    collect_decl_refs(
        &package.root_decl,
        &package.level_table,
        &package.term_table,
        &mut name_refs,
        &mut level_refs,
        &mut term_refs,
    )
    .expect("test current declaration package refs should be collectable");

    let name_map = retained_index_map(package.name_table.len(), &name_refs);
    let level_map = retained_index_map(package.level_table.len(), &level_refs);
    let term_map = retained_index_map(package.term_table.len(), &term_refs);
    let remapped = CoreDeclPackage {
        name_table: name_refs
            .iter()
            .map(|index| package.name_table[*index].clone())
            .collect(),
        level_table: level_refs
            .iter()
            .map(|index| {
                remap_level_node_for_test(&package.level_table[*index], &name_map, &level_map)
            })
            .collect(),
        term_table: term_refs
            .iter()
            .map(|index| {
                remap_term_node_for_test(
                    &package.term_table[*index],
                    &name_map,
                    &level_map,
                    &term_map,
                )
            })
            .collect(),
        root_decl: remap_decl_payload_for_test(
            &package.root_decl,
            &name_map,
            &level_map,
            &term_map,
        ),
    };
    validate_core_decl_package(&remapped)
        .expect("test current declaration package should be canonical after trimming");
    remapped
}

#[cfg(test)]
fn retained_index_map(len: usize, retained: &BTreeSet<usize>) -> Vec<Option<usize>> {
    let mut map = vec![None; len];
    for (new_index, old_index) in retained.iter().copied().enumerate() {
        map[old_index] = Some(new_index);
    }
    map
}

#[cfg(test)]
fn remap_index_for_test(map: &[Option<usize>], index: usize) -> usize {
    map.get(index)
        .and_then(|mapped| *mapped)
        .expect("test package should only reference retained table entries")
}

#[cfg(test)]
fn remap_level_node_for_test(
    level: &LevelNode,
    name_map: &[Option<usize>],
    level_map: &[Option<usize>],
) -> LevelNode {
    match level {
        LevelNode::Zero => LevelNode::Zero,
        LevelNode::Succ(inner) => LevelNode::Succ(remap_index_for_test(level_map, *inner)),
        LevelNode::Max(lhs, rhs) => LevelNode::Max(
            remap_index_for_test(level_map, *lhs),
            remap_index_for_test(level_map, *rhs),
        ),
        LevelNode::IMax(lhs, rhs) => LevelNode::IMax(
            remap_index_for_test(level_map, *lhs),
            remap_index_for_test(level_map, *rhs),
        ),
        LevelNode::Param(name) => LevelNode::Param(remap_index_for_test(name_map, *name)),
    }
}

#[cfg(test)]
fn remap_term_node_for_test(
    term: &TermNode,
    name_map: &[Option<usize>],
    level_map: &[Option<usize>],
    term_map: &[Option<usize>],
) -> TermNode {
    match term {
        TermNode::Sort(level) => TermNode::Sort(remap_index_for_test(level_map, *level)),
        TermNode::BVar(index) => TermNode::BVar(*index),
        TermNode::Const { global_ref, levels } => TermNode::Const {
            global_ref: remap_global_ref_for_test(global_ref, name_map),
            levels: levels
                .iter()
                .map(|level| remap_index_for_test(level_map, *level))
                .collect(),
        },
        TermNode::App(fun, arg) => TermNode::App(
            remap_index_for_test(term_map, *fun),
            remap_index_for_test(term_map, *arg),
        ),
        TermNode::Lam { ty, body } => TermNode::Lam {
            ty: remap_index_for_test(term_map, *ty),
            body: remap_index_for_test(term_map, *body),
        },
        TermNode::Pi { ty, body } => TermNode::Pi {
            ty: remap_index_for_test(term_map, *ty),
            body: remap_index_for_test(term_map, *body),
        },
        TermNode::Let { ty, value, body } => TermNode::Let {
            ty: remap_index_for_test(term_map, *ty),
            value: remap_index_for_test(term_map, *value),
            body: remap_index_for_test(term_map, *body),
        },
    }
}

#[cfg(test)]
fn remap_global_ref_for_test(global_ref: &GlobalRef, name_map: &[Option<usize>]) -> GlobalRef {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => GlobalRef::Builtin {
            name: remap_index_for_test(name_map, *name),
            decl_interface_hash: *decl_interface_hash,
        },
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => GlobalRef::Imported {
            import_index: *import_index,
            name: remap_index_for_test(name_map, *name),
            decl_interface_hash: *decl_interface_hash,
        },
        GlobalRef::Local { decl_index } => GlobalRef::Local {
            decl_index: *decl_index,
        },
        GlobalRef::LocalGenerated { decl_index, name } => GlobalRef::LocalGenerated {
            decl_index: *decl_index,
            name: remap_index_for_test(name_map, *name),
        },
    }
}

#[cfg(test)]
fn remap_decl_payload_for_test(
    decl: &DeclPayload,
    name_map: &[Option<usize>],
    level_map: &[Option<usize>],
    term_map: &[Option<usize>],
) -> DeclPayload {
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => DeclPayload::Axiom {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            ty: remap_index_for_test(term_map, *ty),
        },
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => DeclPayload::AxiomConstrained {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            universe_constraints: remap_universe_constraints_for_test(
                universe_constraints,
                level_map,
            ),
            ty: remap_index_for_test(term_map, *ty),
        },
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => DeclPayload::Def {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            ty: remap_index_for_test(term_map, *ty),
            value: remap_index_for_test(term_map, *value),
            reducibility: *reducibility,
        },
        DeclPayload::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => DeclPayload::DefConstrained {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            universe_constraints: remap_universe_constraints_for_test(
                universe_constraints,
                level_map,
            ),
            ty: remap_index_for_test(term_map, *ty),
            value: remap_index_for_test(term_map, *value),
            reducibility: *reducibility,
        },
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            opacity,
        } => DeclPayload::Theorem {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            ty: remap_index_for_test(term_map, *ty),
            proof: remap_index_for_test(term_map, *proof),
            opacity: *opacity,
        },
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
            opacity,
        } => DeclPayload::TheoremConstrained {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            universe_constraints: remap_universe_constraints_for_test(
                universe_constraints,
                level_map,
            ),
            ty: remap_index_for_test(term_map, *ty),
            proof: remap_index_for_test(term_map, *proof),
            opacity: *opacity,
        },
        DeclPayload::Inductive {
            name,
            universe_params,
            params,
            indices,
            sort,
            constructors,
            recursor,
        } => DeclPayload::Inductive {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            params: params
                .iter()
                .map(|binder| BinderType {
                    ty: remap_index_for_test(term_map, binder.ty),
                })
                .collect(),
            indices: indices
                .iter()
                .map(|binder| BinderType {
                    ty: remap_index_for_test(term_map, binder.ty),
                })
                .collect(),
            sort: remap_index_for_test(level_map, *sort),
            constructors: constructors
                .iter()
                .map(|constructor| ConstructorSpec {
                    name: remap_index_for_test(name_map, constructor.name),
                    ty: remap_index_for_test(term_map, constructor.ty),
                })
                .collect(),
            recursor: recursor.as_ref().map(|recursor| RecursorSpec {
                name: remap_index_for_test(name_map, recursor.name),
                universe_params: remap_name_ids_for_test(&recursor.universe_params, name_map),
                ty: remap_index_for_test(term_map, recursor.ty),
                rules: recursor.rules,
            }),
        },
        DeclPayload::InductiveConstrained {
            name,
            universe_params,
            universe_constraints,
            params,
            indices,
            sort,
            constructors,
            recursor,
        } => DeclPayload::InductiveConstrained {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            universe_constraints: remap_universe_constraints_for_test(
                universe_constraints,
                level_map,
            ),
            params: params
                .iter()
                .map(|binder| BinderType {
                    ty: remap_index_for_test(term_map, binder.ty),
                })
                .collect(),
            indices: indices
                .iter()
                .map(|binder| BinderType {
                    ty: remap_index_for_test(term_map, binder.ty),
                })
                .collect(),
            sort: remap_index_for_test(level_map, *sort),
            constructors: constructors
                .iter()
                .map(|constructor| ConstructorSpec {
                    name: remap_index_for_test(name_map, constructor.name),
                    ty: remap_index_for_test(term_map, constructor.ty),
                })
                .collect(),
            recursor: recursor.as_ref().map(|recursor| RecursorSpec {
                name: remap_index_for_test(name_map, recursor.name),
                universe_params: remap_name_ids_for_test(&recursor.universe_params, name_map),
                ty: remap_index_for_test(term_map, recursor.ty),
                rules: recursor.rules,
            }),
        },
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => DeclPayload::MutualInductiveBlock {
            name: remap_index_for_test(name_map, *name),
            universe_params: remap_name_ids_for_test(universe_params, name_map),
            universe_constraints: remap_universe_constraints_for_test(
                universe_constraints,
                level_map,
            ),
            inductives: inductives
                .iter()
                .map(|inductive| MutualInductiveSpec {
                    name: remap_index_for_test(name_map, inductive.name),
                    params: inductive
                        .params
                        .iter()
                        .map(|binder| BinderType {
                            ty: remap_index_for_test(term_map, binder.ty),
                        })
                        .collect(),
                    indices: inductive
                        .indices
                        .iter()
                        .map(|binder| BinderType {
                            ty: remap_index_for_test(term_map, binder.ty),
                        })
                        .collect(),
                    sort: remap_index_for_test(level_map, inductive.sort),
                    constructors: inductive
                        .constructors
                        .iter()
                        .map(|constructor| ConstructorSpec {
                            name: remap_index_for_test(name_map, constructor.name),
                            ty: remap_index_for_test(term_map, constructor.ty),
                        })
                        .collect(),
                    recursor: inductive.recursor.as_ref().map(|recursor| RecursorSpec {
                        name: remap_index_for_test(name_map, recursor.name),
                        universe_params: remap_name_ids_for_test(
                            &recursor.universe_params,
                            name_map,
                        ),
                        ty: remap_index_for_test(term_map, recursor.ty),
                        rules: recursor.rules,
                    }),
                })
                .collect(),
        },
    }
}

#[cfg(test)]
fn remap_universe_constraints_for_test(
    constraints: &[UniverseConstraintSpec],
    level_map: &[Option<usize>],
) -> Vec<UniverseConstraintSpec> {
    constraints
        .iter()
        .map(|constraint| UniverseConstraintSpec {
            lhs: remap_index_for_test(level_map, constraint.lhs),
            relation: constraint.relation,
            rhs: remap_index_for_test(level_map, constraint.rhs),
        })
        .collect()
}

#[cfg(test)]
fn remap_name_ids_for_test(ids: &[usize], name_map: &[Option<usize>]) -> Vec<usize> {
    ids.iter()
        .map(|id| remap_index_for_test(name_map, *id))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project_import_certificate_context;
    use crate::{VerifiedImportKey, VerifiedModuleCertificateInput};
    use npa_cert::{build_module_cert, encode_module_cert, AxiomPolicy, CoreModule, TrustMode};
    use npa_kernel::Reducibility;

    fn root_module() -> Name {
        Name::from_dotted("M")
    }

    fn empty_import_context() -> MachineImportCertificateContext {
        project_import_certificate_context(
            &[],
            &[],
            &AxiomPolicy {
                mode: TrustMode::HighTrust,
                allowlisted_axioms: BTreeSet::new(),
                deny_sorry: true,
                supported_core_features: BTreeSet::new(),
            },
        )
        .unwrap()
    }

    fn id_type_expr() -> Expr {
        Expr::pi(
            "A",
            Expr::sort(Level::zero()),
            Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn id_value_expr() -> Expr {
        Expr::lam(
            "A",
            Expr::sort(Level::zero()),
            Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
        )
    }

    fn id_decl(name: &str) -> Decl {
        Decl::Def {
            name: name.to_owned(),
            universe_params: Vec::new(),
            ty: id_type_expr(),
            value: id_value_expr(),
            reducibility: Reducibility::Reducible,
        }
    }

    fn alias_decl() -> Decl {
        Decl::Def {
            name: "M.alias".to_owned(),
            universe_params: Vec::new(),
            ty: id_type_expr(),
            value: Expr::konst("M.id", Vec::new()),
            reducibility: Reducibility::Reducible,
        }
    }

    fn imported_axiom_theorem_decl() -> Decl {
        Decl::Theorem {
            name: "M.uses_import".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "x",
                Expr::konst("A.T", Vec::new()),
                Expr::konst("A.T", Vec::new()),
            ),
            proof: Expr::lam("x", Expr::konst("A.T", Vec::new()), Expr::bvar(0)),
        }
    }

    fn builtin_nat_zero_decl() -> Decl {
        Decl::Def {
            name: "M.nat_zero".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::konst("Nat", Vec::new()),
            value: Expr::konst("Nat.zero", Vec::new()),
            reducibility: Reducibility::Reducible,
        }
    }

    fn id_core_package(name: &str) -> CoreDeclPackage {
        CoreDeclPackage {
            name_table: vec![Name::from_dotted(name)],
            level_table: vec![LevelNode::Zero],
            term_table: vec![
                TermNode::Sort(0),
                TermNode::BVar(0),
                TermNode::BVar(1),
                TermNode::Lam { ty: 1, body: 1 },
                TermNode::Pi { ty: 1, body: 2 },
                TermNode::Lam { ty: 0, body: 3 },
                TermNode::Pi { ty: 0, body: 4 },
            ],
            root_decl: DeclPayload::Def {
                name: 0,
                universe_params: Vec::new(),
                ty: 6,
                value: 5,
                reducibility: CertReducibility::Reducible,
            },
        }
    }

    fn builtin_nat_zero_core_package() -> CoreDeclPackage {
        let nat_hash = npa_cert::builtin_decl_interface_hash(&Name::from_dotted("Nat")).unwrap();
        let zero_hash =
            npa_cert::builtin_decl_interface_hash(&Name::from_dotted("Nat.zero")).unwrap();
        CoreDeclPackage {
            name_table: vec![
                Name::from_dotted("M.nat_zero"),
                Name::from_dotted("Nat"),
                Name::from_dotted("Nat.zero"),
            ],
            level_table: Vec::new(),
            term_table: vec![
                TermNode::Const {
                    global_ref: GlobalRef::Builtin {
                        name: 1,
                        decl_interface_hash: nat_hash,
                    },
                    levels: Vec::new(),
                },
                TermNode::Const {
                    global_ref: GlobalRef::Builtin {
                        name: 2,
                        decl_interface_hash: zero_hash,
                    },
                    levels: Vec::new(),
                },
            ],
            root_decl: DeclPayload::Def {
                name: 0,
                universe_params: Vec::new(),
                ty: 0,
                value: 1,
                reducibility: CertReducibility::Reducible,
            },
        }
    }

    fn alias_core_package() -> CoreDeclPackage {
        CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.alias")],
            level_table: vec![LevelNode::Zero],
            term_table: vec![
                TermNode::Sort(0),
                TermNode::BVar(0),
                TermNode::BVar(1),
                TermNode::Const {
                    global_ref: GlobalRef::Local { decl_index: 0 },
                    levels: Vec::new(),
                },
                TermNode::Pi { ty: 1, body: 2 },
                TermNode::Pi { ty: 0, body: 4 },
            ],
            root_decl: DeclPayload::Def {
                name: 0,
                universe_params: Vec::new(),
                ty: 5,
                value: 3,
                reducibility: CertReducibility::Reducible,
            },
        }
    }

    fn imported_axiom_theorem_core_package(imported_hash: Hash) -> CoreDeclPackage {
        CoreDeclPackage {
            name_table: vec![Name::from_dotted("A.T"), Name::from_dotted("M.uses_import")],
            level_table: Vec::new(),
            term_table: vec![
                TermNode::BVar(0),
                TermNode::Const {
                    global_ref: GlobalRef::Imported {
                        import_index: 0,
                        name: 0,
                        decl_interface_hash: imported_hash,
                    },
                    levels: Vec::new(),
                },
                TermNode::Lam { ty: 1, body: 0 },
                TermNode::Pi { ty: 1, body: 1 },
            ],
            root_decl: DeclPayload::Theorem {
                name: 1,
                universe_params: Vec::new(),
                ty: 3,
                proof: 2,
                opacity: Opacity::Opaque,
            },
        }
    }

    fn signature_from_checked(checked: &CheckedCurrentDecl) -> MachineCheckedDeclSignature {
        MachineCheckedDeclSignature {
            name: checked.signature().name().clone(),
            universe_params: checked.signature().universe_params().to_vec(),
            ty: checked.signature().ty().clone(),
            decl_interface_hash: checked.signature().decl_interface_hash(),
        }
    }

    fn package_bytes(
        source_index: u64,
        core_package: CoreDeclPackage,
        decl: Decl,
        imports: &MachineImportCertificateContext,
        prior_context: Option<&MachineCheckedCurrentDeclContext>,
    ) -> Vec<u8> {
        let root = root_module();
        let machine_tactic_imports = imports
            .direct_import_entries()
            .iter()
            .map(|entry| VerifiedImportRef::from_verified_module(&entry.verified_module))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let checked_prior = prior_context
            .map(|context| context.checked_current_decls().to_vec())
            .unwrap_or_default();
        let checked = check_current_decl_for_machine_tactic_from_verified_imports(
            &machine_tactic_imports,
            &checked_prior,
            source_index,
            decl,
        )
        .unwrap();
        let empty_decls = Vec::new();
        let empty_generated = Vec::new();
        let prior_decls = prior_context
            .map(|context| context.decl_index_table())
            .unwrap_or(empty_decls.as_slice());
        let generated = prior_context
            .map(|context| context.generated_decl_table())
            .unwrap_or(empty_generated.as_slice());
        let direct_import_entries = imports.direct_import_entries();
        let dependency_report = derive_dependency_report(
            &root,
            source_index,
            imports,
            &direct_import_entries,
            &core_package,
            prior_decls,
            generated,
        )
        .unwrap();
        let decoded = DecodedCheckedCurrentDeclPackage {
            source_index,
            signature: signature_from_checked(&checked),
            signature_canonical_bytes: checked_decl_signature_canonical_bytes(checked.signature()),
            core_package,
            dependency_report,
            prior_chain_fingerprint: checked.prior_chain_fingerprint(),
            checked_env_fingerprint: checked.checked_env_fingerprint(),
            canonical_bytes: Vec::new(),
        };
        encode_checked_current_decl_package(&decoded)
    }

    fn imported_axiom_context() -> (MachineImportCertificateContext, Hash, Hash) {
        let module = CoreModule {
            name: Name::from_dotted("A"),
            declarations: vec![Decl::Axiom {
                name: "A.T".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            }],
        };
        let cert = build_module_cert(module, &[]).unwrap();
        let cert_bytes = encode_module_cert(&cert).unwrap();
        let key = VerifiedImportKey::new(
            Name::from_dotted("A"),
            cert.hashes.export_hash,
            cert.hashes.certificate_hash,
        );
        let mut allowlisted_axioms = BTreeSet::new();
        allowlisted_axioms.insert(Name::from_dotted("A.T"));
        let context = project_import_certificate_context(
            &[VerifiedModuleCertificateInput {
                module: &key.module,
                expected_export_hash: key.export_hash,
                expected_certificate_hash: key.certificate_hash,
                certificate_bytes: &cert_bytes,
            }],
            std::slice::from_ref(&key),
            &AxiomPolicy {
                mode: TrustMode::HighTrust,
                allowlisted_axioms,
                deny_sorry: true,
                supported_core_features: BTreeSet::new(),
            },
        )
        .unwrap();
        let imported_hash = {
            let direct = context.direct_import_entries();
            imported_export_by_name_hash(
                direct[0],
                &Name::from_dotted("A.T"),
                &cert.declarations[0].hashes.decl_interface_hash,
            )
            .unwrap()
            .decl_interface_hash
        };
        (context, imported_hash, cert.hashes.export_hash)
    }

    fn imported_eq_rec_alias_context() -> MachineImportCertificateContext {
        let u = Level::param("u");
        let v = Level::param("v");
        let module = CoreModule {
            name: Name::from_dotted("A"),
            declarations: vec![Decl::Def {
                name: "A.eq_rec_alias".to_owned(),
                universe_params: vec!["u".to_owned(), "v".to_owned()],
                ty: npa_kernel::eq_rec_type(u.clone(), v.clone()),
                value: Expr::konst("Eq.rec", vec![u, v]),
                reducibility: Reducibility::Reducible,
            }],
        };
        let cert = build_module_cert(module, &[]).unwrap();
        let cert_bytes = encode_module_cert(&cert).unwrap();
        let key = VerifiedImportKey::new(
            Name::from_dotted("A"),
            cert.hashes.export_hash,
            cert.hashes.certificate_hash,
        );
        let mut allowlisted_axioms = BTreeSet::new();
        allowlisted_axioms.insert(Name::from_dotted("Eq.rec"));
        project_import_certificate_context(
            &[VerifiedModuleCertificateInput {
                module: &key.module,
                expected_export_hash: key.export_hash,
                expected_certificate_hash: key.certificate_hash,
                certificate_bytes: &cert_bytes,
            }],
            std::slice::from_ref(&key),
            &AxiomPolicy {
                mode: TrustMode::HighTrust,
                allowlisted_axioms,
                deny_sorry: true,
                supported_core_features: BTreeSet::new(),
            },
        )
        .unwrap()
    }

    fn param_succ_core_package(level_table: Vec<LevelNode>, ty_level: LevelId) -> CoreDeclPackage {
        CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.A"), Name::from_dotted("u")],
            level_table,
            term_table: vec![TermNode::Sort(ty_level)],
            root_decl: DeclPayload::Axiom {
                name: 0,
                universe_params: vec![1],
                ty: 0,
            },
        }
    }

    fn inductive_sort_core_package(term_table: Vec<TermNode>) -> CoreDeclPackage {
        CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.I")],
            level_table: vec![LevelNode::Zero],
            term_table,
            root_decl: DeclPayload::Inductive {
                name: 0,
                universe_params: Vec::new(),
                params: Vec::new(),
                indices: Vec::new(),
                sort: 0,
                constructors: Vec::new(),
                recursor: None,
            },
        }
    }

    #[test]
    fn inductive_type_orders_params_before_indices() {
        let param_ty = Expr::sort(Level::zero());
        let index_ty = Expr::sort(Level::succ(Level::zero()));
        let params = vec![Binder::new("p", param_ty.clone())];
        let indices = vec![Binder::new("i", index_ty.clone())];

        let ty = inductive_type(&params, &indices, Level::zero());

        assert_eq!(
            ty,
            Expr::pi(
                "p",
                param_ty,
                Expr::pi("i", index_ty, Expr::sort(Level::zero())),
            )
        );
    }

    #[test]
    fn accepts_certificate_height_first_level_table_order() {
        let package = param_succ_core_package(vec![LevelNode::Param(1), LevelNode::Succ(0)], 1);

        validate_core_decl_package(&package).unwrap();
    }

    #[test]
    fn rejects_tag_sorted_but_not_height_sorted_level_table() {
        let package = param_succ_core_package(vec![LevelNode::Succ(1), LevelNode::Param(1)], 0);

        let err = validate_core_decl_package(&package).unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "non-canonical level table order",
            }
        );
    }

    #[test]
    fn rejects_non_normalized_level_table_entry() {
        let package = param_succ_core_package(
            vec![LevelNode::Zero, LevelNode::Param(1), LevelNode::Max(0, 1)],
            2,
        );

        let err = validate_core_decl_package(&package).unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "non-normalized level table entry",
            }
        );
    }

    #[test]
    fn accepts_inductive_export_type_term_as_reachable() {
        let package = inductive_sort_core_package(vec![TermNode::Sort(0)]);

        validate_core_decl_package(&package).unwrap();
    }

    #[test]
    fn rejects_inductive_package_missing_export_type_term() {
        let package = inductive_sort_core_package(Vec::new());

        let err = validate_core_decl_package(&package).unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "missing inductive export type term",
            }
        );
    }

    #[test]
    fn accepts_certificate_height_first_term_table_order() {
        let package = CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.term")],
            level_table: Vec::new(),
            term_table: vec![
                TermNode::BVar(0),
                TermNode::Lam { ty: 0, body: 0 },
                TermNode::App(1, 0),
            ],
            root_decl: DeclPayload::Axiom {
                name: 0,
                universe_params: Vec::new(),
                ty: 2,
            },
        };

        validate_core_decl_package(&package).unwrap();
    }

    #[test]
    fn rejects_tag_sorted_but_not_height_sorted_term_table() {
        let package = CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.term")],
            level_table: Vec::new(),
            term_table: vec![
                TermNode::BVar(0),
                TermNode::App(2, 0),
                TermNode::Lam { ty: 0, body: 0 },
            ],
            root_decl: DeclPayload::Axiom {
                name: 0,
                universe_params: Vec::new(),
                ty: 1,
            },
        };

        let err = validate_core_decl_package(&package).unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::DecodeFailed {
                reason: "non-canonical term table order",
            }
        );
    }

    #[test]
    fn projects_checked_current_decl_package() {
        let imports = empty_import_context();
        let bytes = package_bytes(0, id_core_package("M.id"), id_decl("M.id"), &imports, None);

        let context = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap();

        assert_eq!(context.checked_current_decls().len(), 1);
        assert_eq!(context.decl_index_table()[0].source_index, 0);
        assert_eq!(
            context.decl_index_table()[0].signature.name,
            Name::from_dotted("M.id")
        );
        assert!(context.decl_index_table()[0]
            .dependency_report
            .direct_dependency_entries
            .is_empty());
    }

    #[test]
    fn rejects_current_axiom_package_as_unchecked_current_decl() {
        let imports = empty_import_context();
        let package = CoreDeclPackage {
            name_table: vec![Name::from_dotted("M.bad")],
            level_table: vec![LevelNode::Zero],
            term_table: vec![TermNode::Sort(0)],
            root_decl: DeclPayload::Axiom {
                name: 0,
                universe_params: Vec::new(),
                ty: 0,
            },
        };
        let decoded = DecodedCheckedCurrentDeclPackage {
            source_index: 0,
            signature: MachineCheckedDeclSignature {
                name: Name::from_dotted("M.bad"),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
                decl_interface_hash: [0; 32],
            },
            signature_canonical_bytes: Vec::new(),
            core_package: package,
            dependency_report: CurrentDeclDependencyReport {
                direct_dependency_entries: Vec::new(),
                axiom_dependencies: Vec::new(),
            },
            prior_chain_fingerprint: [0; 32],
            checked_env_fingerprint: [0; 32],
            canonical_bytes: Vec::new(),
        };
        let bytes = encode_checked_current_decl_package(&decoded);

        let err = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap_err();

        match err {
            CheckedCurrentDeclProjectionError::MachineTacticRejected {
                source_index,
                diagnostic,
            } => {
                assert_eq!(source_index, 0);
                assert_eq!(
                    diagnostic.kind,
                    MachineTacticDiagnosticKind::UncheckedCurrentDecl
                );
            }
            other => {
                panic!("expected MachineTacticRejected for current axiom package, got {other:?}")
            }
        }
    }

    #[test]
    fn revalidates_builtin_dependency_report() {
        let imports = empty_import_context();
        let bytes = package_bytes(
            0,
            builtin_nat_zero_core_package(),
            builtin_nat_zero_decl(),
            &imports,
            None,
        );

        let context = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap();

        let deps = &context.decl_index_table()[0]
            .dependency_report
            .direct_dependency_entries;
        assert_eq!(
            deps,
            &[
                CurrentDeclDependencyEntry {
                    dependency_ref: MachineDependencyRefWire::Builtin {
                        name: Name::from_dotted("Nat"),
                    },
                    decl_interface_hash: npa_cert::builtin_decl_interface_hash(&Name::from_dotted(
                        "Nat"
                    ))
                    .unwrap(),
                },
                CurrentDeclDependencyEntry {
                    dependency_ref: MachineDependencyRefWire::Builtin {
                        name: Name::from_dotted("Nat.zero"),
                    },
                    decl_interface_hash: npa_cert::builtin_decl_interface_hash(&Name::from_dotted(
                        "Nat.zero"
                    ))
                    .unwrap(),
                },
            ]
        );
        assert!(context.decl_index_table()[0]
            .dependency_report
            .axiom_dependencies
            .is_empty());
    }

    #[test]
    fn revalidates_prior_source_dependency_report() {
        let imports = empty_import_context();
        let id_bytes = package_bytes(0, id_core_package("M.id"), id_decl("M.id"), &imports, None);
        let prior_context = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &id_bytes }],
        )
        .unwrap();
        let alias_bytes = package_bytes(
            1,
            alias_core_package(),
            alias_decl(),
            &imports,
            Some(&prior_context),
        );

        let context = project_checked_current_decl_context(
            &root_module(),
            2,
            &imports,
            &[
                CheckedCurrentDeclPackageInput { bytes: &id_bytes },
                CheckedCurrentDeclPackageInput {
                    bytes: &alias_bytes,
                },
            ],
        )
        .unwrap();

        let deps = &context.decl_index_table()[1]
            .dependency_report
            .direct_dependency_entries;
        assert_eq!(deps.len(), 1);
        assert_eq!(
            deps[0].dependency_ref,
            MachineDependencyRefWire::CurrentModule {
                module: root_module(),
                name: Name::from_dotted("M.id"),
                source_index: 0,
            }
        );
    }

    #[test]
    fn revalidates_imported_axiom_dependency_report() {
        let (imports, imported_hash, export_hash) = imported_axiom_context();
        let bytes = package_bytes(
            0,
            imported_axiom_theorem_core_package(imported_hash),
            imported_axiom_theorem_decl(),
            &imports,
            None,
        );

        let context = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap();

        let report = &context.decl_index_table()[0].dependency_report;
        assert_eq!(report.direct_dependency_entries.len(), 1);
        assert_eq!(
            report.direct_dependency_entries[0].dependency_ref,
            MachineDependencyRefWire::Imported {
                module: Name::from_dotted("A"),
                name: Name::from_dotted("A.T"),
                export_hash,
            }
        );
        assert_eq!(
            report.axiom_dependencies,
            vec![MachineAxiomRefWire::Imported {
                module: Name::from_dotted("A"),
                name: Name::from_dotted("A.T"),
                export_hash,
                decl_interface_hash: imported_hash,
            }]
        );
    }

    #[test]
    fn converts_imported_builtin_axiom_dependency() {
        let imports = imported_eq_rec_alias_context();
        let direct = imports.direct_import_entries();
        let export = direct[0]
            .export_block
            .iter()
            .find(|export| {
                direct[0].decoded_name_table[export.name] == Name::from_dotted("A.eq_rec_alias")
            })
            .unwrap();

        assert_eq!(
            export
                .axiom_dependencies
                .iter()
                .map(|axiom| imported_axiom_ref_to_wire(0, &imports, direct[0], axiom).unwrap())
                .collect::<Vec<_>>(),
            vec![MachineAxiomRefWire::Builtin {
                name: Name::from_dotted("Eq.rec"),
                decl_interface_hash: npa_cert::builtin_decl_interface_hash(&Name::from_dotted(
                    "Eq.rec"
                ))
                .unwrap(),
            }]
        );
    }

    #[test]
    fn rejects_stale_prior_chain_fingerprint() {
        let imports = empty_import_context();
        let mut bytes = package_bytes(0, id_core_package("M.id"), id_decl("M.id"), &imports, None);
        let prior_chain_start = bytes.len() - 64;
        bytes[prior_chain_start] ^= 0x01;

        let err = project_checked_current_decl_context(
            &root_module(),
            1,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::PriorChainFingerprintMismatch { source_index: 0 }
        );
    }

    #[test]
    fn rejects_gap_in_source_index_prefix() {
        let imports = empty_import_context();
        let bytes = package_bytes(0, id_core_package("M.id"), id_decl("M.id"), &imports, None);

        let err = project_checked_current_decl_context(
            &root_module(),
            2,
            &imports,
            &[CheckedCurrentDeclPackageInput { bytes: &bytes }],
        )
        .unwrap_err();

        assert_eq!(
            err,
            CheckedCurrentDeclProjectionError::InvalidSourceIndexPrefix {
                expected: 1,
                actual: None
            }
        );
    }
}

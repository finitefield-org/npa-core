use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use npa_kernel::{Decl, Env, Expr, Level, UniverseConstraint, UniverseConstraintRelation};

use crate::local_authoring::CertificateImportView;
use crate::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CanonLevel {
    Zero,
    Succ(Box<CanonLevel>),
    Max(Box<CanonLevel>, Box<CanonLevel>),
    IMax(Box<CanonLevel>, Box<CanonLevel>),
    Param(NameId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonUniverseConstraint {
    lhs: CanonLevel,
    relation: UniverseConstraintRelation,
    rhs: CanonLevel,
}

// Children are `Arc` so that node clones into the canonical term tables and
// hash memo maps stay cheap; canonical terms are immutable once built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CanonTerm {
    Sort(CanonLevel),
    BVar(u32),
    Const {
        global_ref: GlobalRef,
        levels: Vec<CanonLevel>,
    },
    App(Arc<CanonTerm>, Arc<CanonTerm>),
    Lam {
        ty: Arc<CanonTerm>,
        body: Arc<CanonTerm>,
    },
    Pi {
        ty: Arc<CanonTerm>,
        body: Arc<CanonTerm>,
    },
}

#[derive(Clone)]
pub(crate) struct CanonDecl {
    decl: CanonDeclPayload,
    dependencies: Vec<DependencyEntry>,
}

#[derive(Clone)]
pub(crate) enum CanonDeclPayload {
    Axiom {
        name: NameId,
        universe_params: Vec<NameId>,
        universe_constraints: Vec<CanonUniverseConstraint>,
        ty: CanonTerm,
    },
    Def {
        name: NameId,
        universe_params: Vec<NameId>,
        universe_constraints: Vec<CanonUniverseConstraint>,
        ty: CanonTerm,
        value: CanonTerm,
        reducibility: CertReducibility,
    },
    Theorem {
        name: NameId,
        universe_params: Vec<NameId>,
        universe_constraints: Vec<CanonUniverseConstraint>,
        ty: CanonTerm,
        proof: CanonTerm,
    },
    Inductive {
        name: NameId,
        universe_params: Vec<NameId>,
        universe_constraints: Vec<CanonUniverseConstraint>,
        params: Vec<CanonTerm>,
        indices: Vec<CanonTerm>,
        sort: CanonLevel,
        constructors: Vec<(NameId, CanonTerm)>,
        recursor: Option<(NameId, Vec<NameId>, CanonTerm, RecursorRulesSpec)>,
    },
    MutualInductiveBlock {
        name: NameId,
        universe_params: Vec<NameId>,
        universe_constraints: Vec<CanonUniverseConstraint>,
        inductives: Vec<CanonMutualInductive>,
    },
}

#[derive(Clone)]
pub(crate) struct CanonMutualInductive {
    name: NameId,
    params: Vec<CanonTerm>,
    indices: Vec<CanonTerm>,
    sort: CanonLevel,
    constructors: Vec<(NameId, CanonTerm)>,
    recursor: Option<(NameId, Vec<NameId>, CanonTerm, RecursorRulesSpec)>,
}

pub(crate) fn build_module_cert_observed_impl(
    module: CoreModule,
    imports: &[VerifiedModule],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    let imports = imports.iter().collect::<Vec<_>>();
    build_module_cert_from_import_refs_with_preferred_imports_observed_impl(
        module,
        &imports,
        &BTreeMap::new(),
        observation,
    )
}

pub(crate) fn build_module_cert_from_import_refs_observed_impl(
    module: CoreModule,
    imports: &[&VerifiedModule],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    build_module_cert_from_import_refs_with_preferred_imports_observed_impl(
        module,
        imports,
        &BTreeMap::new(),
        observation,
    )
}

pub(crate) fn build_module_cert_from_import_refs_with_preferred_imports_observed_impl(
    module: CoreModule,
    imports: &[&VerifiedModule],
    preferred_imports: &BTreeMap<Name, ImportEntry>,
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    let imports = imports
        .iter()
        .map(|module| *module as &dyn CertificateImportView)
        .collect::<Vec<_>>();
    build_module_cert_from_context_refs_with_preferred_imports_observed_impl(
        module,
        &imports,
        preferred_imports,
        observation,
    )
}

pub(crate) fn build_module_cert_from_context_refs_with_preferred_imports_impl(
    module: CoreModule,
    imports: &[&dyn CertificateImportView],
    preferred_imports: &BTreeMap<Name, ImportEntry>,
) -> Result<ModuleCert> {
    build_module_cert_from_context_refs_with_preferred_imports_observed_impl(
        module,
        imports,
        preferred_imports,
        None,
    )
}

fn build_module_cert_from_context_refs_with_preferred_imports_observed_impl(
    module: CoreModule,
    imports: &[&dyn CertificateImportView],
    preferred_imports: &BTreeMap<Name, ImportEntry>,
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    build_module_cert_from_import_refs_with_preferred_imports_for_version(
        module,
        imports,
        preferred_imports,
        CertificateFormatVersion::V0_4_0,
        observation,
    )
}

fn build_module_cert_from_import_refs_with_preferred_imports_for_version(
    module: CoreModule,
    imports: &[&dyn CertificateImportView],
    preferred_imports: &BTreeMap<Name, ImportEntry>,
    version: CertificateFormatVersion,
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    let mut module = module;
    module.declarations = canonical_declaration_order(module.declarations)?;

    let mut imports = imports.to_vec();
    imports.sort_by_key(|module| {
        (
            module.module().clone(),
            module.export_hash(),
            Some(module.certificate_hash()),
        )
    });
    imports.dedup_by(|lhs, rhs| {
        lhs.module() == rhs.module()
            && lhs.export_hash() == rhs.export_hash()
            && lhs.certificate_hash() == rhs.certificate_hash()
    });

    let local_names: Vec<Name> = module
        .declarations
        .iter()
        .map(|decl| Name::from_dotted(decl.name()))
        .collect();
    let mut local_public_names = local_names.clone();
    let mut local_generated_name_to_index = BTreeMap::new();
    for (decl_index, decl) in module.declarations.iter().enumerate() {
        if let Decl::Inductive { data, .. } = decl {
            for constructor in &data.constructors {
                let name = Name::from_dotted(&constructor.name);
                local_generated_name_to_index.insert(name.clone(), decl_index);
                local_public_names.push(name);
            }
            if let Some(recursor) = &data.recursor {
                let name = Name::from_dotted(&recursor.name);
                local_generated_name_to_index.insert(name.clone(), decl_index);
                local_public_names.push(name);
            }
        } else if let Decl::MutualInductiveBlock { data, .. } = decl {
            for inductive in &data.inductives {
                let name = Name::from_dotted(&inductive.name);
                local_generated_name_to_index.insert(name.clone(), decl_index);
                local_public_names.push(name);
                for constructor in &inductive.constructors {
                    let name = Name::from_dotted(&constructor.name);
                    local_generated_name_to_index.insert(name.clone(), decl_index);
                    local_public_names.push(name);
                }
                if let Some(recursor) = &inductive.recursor {
                    let name = Name::from_dotted(&recursor.name);
                    local_generated_name_to_index.insert(name.clone(), decl_index);
                    local_public_names.push(name);
                }
            }
        }
    }
    ensure_unique_names(&local_public_names)?;
    for name in &local_public_names {
        if reserved_core_primitive_name(name) {
            return Err(CertError::ReservedCorePrimitive { name: name.clone() });
        }
    }
    let local_name_to_index: BTreeMap<_, _> = local_names
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect();

    let mut names = BTreeSet::new();
    collect_name(&mut names, &module.name);
    for import in &imports {
        collect_name(&mut names, import.module());
    }
    for decl in &module.declarations {
        collect_names_from_decl(&mut names, decl);
    }
    let directly_referenced_names =
        referenced_imported_export_names(&module.declarations, &imports, &local_public_names)?;
    collect_imported_axiom_names_for_referenced_exports(
        &mut names,
        &imports,
        &directly_referenced_names,
    )?;
    let name_table: Vec<_> = names.into_iter().collect();
    ensure_canonical_names(&name_table)?;
    let name_index: BTreeMap<_, _> = name_table
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect();

    let imports_entries: Vec<_> = imports
        .iter()
        .map(|module| ImportEntry {
            module: module.module().clone(),
            export_hash: module.export_hash(),
            certificate_hash: Some(module.certificate_hash()),
        })
        .collect();
    let imported_decls = imported_decl_map(
        &imports,
        &name_index,
        &directly_referenced_names,
        preferred_imports,
    )?;
    let referenced_builtins =
        referenced_builtin_names(&module.declarations, &imports, &local_public_names)?;
    let reference_bindings = build_reference_bindings(
        &local_name_to_index,
        &local_generated_name_to_index,
        &imported_decls,
        &referenced_builtins,
    )?;
    let selected_import_exports = imported_decls
        .iter()
        .map(|(name, info)| (info.import_index, name.clone(), info.decl_interface_hash))
        .collect::<Vec<_>>();

    let mut env = Env::new();
    add_selected_import_exports_to_env(&mut env, &imports, &selected_import_exports)?;
    add_referenced_builtins_to_env(&mut env, &referenced_builtins)?;

    let mut canon_decls = Vec::new();
    let canon_term_memo = std::cell::RefCell::new(CanonTermMemo::default());
    for (decl_index, decl) in module.declarations.iter().cloned().enumerate() {
        add_current_module_decl_to_env(&mut env, decl.clone(), version)?;
        let allow_self = matches!(
            decl,
            Decl::Inductive { .. }
                | Decl::MutualInductiveBlock { .. }
                | Decl::Axiom { .. }
                | Decl::AxiomConstrained { .. }
        );
        let resolver = Resolver {
            current_decl_index: decl_index,
            allow_self,
            reference_bindings: &reference_bindings,
            name_index: &name_index,
            canon_term_memo: &canon_term_memo,
        };
        let canon_decl = canonicalize_decl(decl.clone(), decl_index, &resolver)?;
        canon_decls.push(canon_decl);
    }

    let mut collector = CanonNodeCollector::new(&name_table);
    for decl in &canon_decls {
        collect_canon_decl_nodes(decl, &mut collector)?;
    }
    let CanonBuiltTables {
        level_table,
        level_hashes,
        term_table,
        term_hashes,
        node_ids,
    } = collector.build_tables()?;

    let mut declarations: Vec<DeclCert> = Vec::new();
    let mut per_declaration = Vec::new();
    let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::new();
    let mut interface_hashes: Vec<Hash> = Vec::new();
    let mut local_transparency_budget = LocalTransparencyBudget::default();
    for (decl_index, canon_decl) in canon_decls.iter().enumerate() {
        let local_transparency = Some(CanonLocalTransparencyContext {
            previous_declarations: &declarations,
            budget: &mut local_transparency_budget,
        });
        let finalized = finalize_canon_decl(
            decl_index,
            canon_decl,
            CanonDeclFinalizeContext {
                version,
                node_ids: &node_ids,
                interface_hashes: &interface_hashes,
                previous_axioms: &previous_axioms,
                imported_decls: &imported_decls,
                name_table: &name_table,
                term_table: &term_table,
                level_hashes: &level_hashes,
                term_hashes: &term_hashes,
                include_direct_axioms: true,
                local_transparency,
            },
        )?;
        interface_hashes.push(finalized.hashes.decl_interface_hash);
        previous_axioms.push(finalized.axiom_dependencies.clone());
        declarations.push(DeclCert {
            decl: finalized.payload,
            dependencies: finalized.dependencies,
            axiom_dependencies: finalized.axiom_dependencies.clone(),
            hashes: finalized.hashes,
        });
        per_declaration.push(DeclAxiomReport {
            decl_index,
            direct_axioms: finalized.direct_axioms,
            transitive_axioms: finalized.axiom_dependencies,
        });
    }

    let export_block = build_export_block(&declarations, &term_table, &term_hashes)?;
    let module_axioms = union_axioms(
        per_declaration
            .iter()
            .flat_map(|report| report.transitive_axioms.iter().cloned()),
    );
    let axiom_report = AxiomReport {
        per_declaration,
        module_axioms,
        core_features: core_features_from_builtins(&referenced_builtins),
    };

    let export_hash = hash_with_domain(MODULE_EXPORT_DOMAIN, &encode_export_block(&export_block));
    let axiom_report_hash =
        hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &encode_axiom_report(&axiom_report));

    let mut parts = ModuleCertParts {
        header: CertHeader {
            format: FORMAT.to_owned(),
            core_spec: CORE_SPEC.to_owned(),
            module: module.name,
        },
        imports: imports_entries,
        name_table,
        level_table,
        term_table,
        declarations,
        export_block,
        axiom_report,
        hashes: ModuleHashes {
            export_hash,
            axiom_report_hash,
            certificate_hash: [0; 32],
        },
    };
    audit_emitted_reference_origins(&parts, &reference_bindings)?;
    parts.hashes.certificate_hash = hash_with_domain(
        version.module_certificate_domain(),
        &encode_module_cert_parts_without_certificate_hash_for_header(&parts)?,
    );
    Ok(ModuleCert::from_parts_observed(parts, observation))
}

fn canonicalize_decl(decl: Decl, decl_index: usize, resolver: &Resolver<'_>) -> Result<CanonDecl> {
    let input_universe_constraints = decl.universe_constraints().to_vec();
    match decl {
        Decl::Axiom {
            name,
            universe_params,
            ty,
        }
        | Decl::AxiomConstrained {
            name,
            universe_params,
            ty,
            ..
        } => {
            let name_id = resolver.name_id(&Name::from_dotted(&name))?;
            let ty = canonicalize_expr(&ty, resolver)?;
            let deps = dependencies_from_terms([&ty]);
            let universe_constraints = canonicalize_universe_constraints(
                &universe_params,
                &input_universe_constraints,
                resolver,
            )?;
            Ok(CanonDecl {
                decl: CanonDeclPayload::Axiom {
                    name: name_id,
                    universe_params: universe_param_ids(&universe_params, resolver)?,
                    universe_constraints,
                    ty,
                },
                dependencies: deps,
            })
        }
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        }
        | Decl::DefConstrained {
            name,
            universe_params,
            ty,
            value,
            reducibility,
            ..
        } => {
            let ty = canonicalize_expr(&ty, resolver)?;
            let value = canonicalize_expr(&value, resolver)?;
            let deps = dependencies_from_terms([&ty, &value]);
            let universe_constraints = canonicalize_universe_constraints(
                &universe_params,
                &input_universe_constraints,
                resolver,
            )?;
            Ok(CanonDecl {
                decl: CanonDeclPayload::Def {
                    name: resolver.name_id(&Name::from_dotted(&name))?,
                    universe_params: universe_param_ids(&universe_params, resolver)?,
                    universe_constraints,
                    ty,
                    value,
                    reducibility: CertReducibility::from(&reducibility),
                },
                dependencies: deps,
            })
        }
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        }
        | Decl::TheoremConstrained {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => {
            let ty = canonicalize_expr(&ty, resolver)?;
            let proof = canonicalize_expr(&proof, resolver)?;
            let deps = dependencies_from_terms([&ty, &proof]);
            let universe_constraints = canonicalize_universe_constraints(
                &universe_params,
                &input_universe_constraints,
                resolver,
            )?;
            Ok(CanonDecl {
                decl: CanonDeclPayload::Theorem {
                    name: resolver.name_id(&Name::from_dotted(&name))?,
                    universe_params: universe_param_ids(&universe_params, resolver)?,
                    universe_constraints,
                    ty,
                    proof,
                },
                dependencies: deps,
            })
        }
        Decl::Inductive {
            name,
            universe_params,
            ty,
            data,
        } => {
            if name != data.name || universe_params != data.universe_params {
                return Err(CertError::InductiveWrapperMismatch {
                    name: Name::from_dotted(&name),
                });
            }
            let universe_constraints = canonicalize_universe_constraints(
                &universe_params,
                &input_universe_constraints,
                resolver,
            )?;
            let mut terms = Vec::new();
            let ty = canonicalize_expr(&ty, resolver)?;
            let params = data
                .params
                .iter()
                .map(|binder| canonicalize_expr(&binder.ty, resolver))
                .collect::<Result<Vec<_>>>()?;
            terms.extend(params.iter().cloned());
            let indices = data
                .indices
                .iter()
                .map(|binder| canonicalize_expr(&binder.ty, resolver))
                .collect::<Result<Vec<_>>>()?;
            terms.extend(indices.iter().cloned());
            let constructors = data
                .constructors
                .iter()
                .map(|constructor| {
                    let ty = canonicalize_expr(&constructor.ty, resolver)?;
                    terms.push(ty.clone());
                    Ok((resolver.name_id(&Name::from_dotted(&constructor.name))?, ty))
                })
                .collect::<Result<Vec<_>>>()?;
            let recursor = data
                .recursor
                .as_ref()
                .map(|recursor| {
                    let ty = canonicalize_expr(&recursor.ty, resolver)?;
                    terms.push(ty.clone());
                    Ok::<_, CertError>((
                        resolver.name_id(&Name::from_dotted(&recursor.name))?,
                        universe_param_ids(&recursor.universe_params, resolver)?,
                        ty,
                        recursor
                            .rules
                            .as_ref()
                            .map(|rules| RecursorRulesSpec {
                                minor_start: rules.minor_start,
                                major_index: rules.major_index,
                            })
                            .unwrap_or_else(|| RecursorRulesSpec {
                                minor_start: data.params.len() + 1,
                                major_index: data.params.len() + 1 + data.constructors.len(),
                            }),
                    ))
                })
                .transpose()?;
            let sort = canonicalize_level(&data.sort, resolver)?;
            if ty != inductive_type_canon_term(&params, &indices, &sort) {
                return Err(CertError::InductiveWrapperMismatch {
                    name: Name::from_dotted(&name),
                });
            }
            let mut deps = dependencies_from_terms(terms.iter());
            remove_self_dependency(&mut deps, decl_index);
            Ok(CanonDecl {
                decl: CanonDeclPayload::Inductive {
                    name: resolver.name_id(&Name::from_dotted(&name))?,
                    universe_params: universe_param_ids(&universe_params, resolver)?,
                    universe_constraints,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                },
                dependencies: deps,
            })
        }
        Decl::MutualInductiveBlock {
            name,
            universe_params,
            data,
        } => {
            if name != data.name || universe_params != data.universe_params {
                return Err(CertError::InductiveWrapperMismatch {
                    name: Name::from_dotted(&name),
                });
            }
            let universe_constraints = canonicalize_universe_constraints(
                &universe_params,
                &input_universe_constraints,
                resolver,
            )?;
            let mut terms = Vec::new();
            let inductives = data
                .inductives
                .iter()
                .map(|inductive| {
                    let params = inductive
                        .params
                        .iter()
                        .map(|binder| canonicalize_expr(&binder.ty, resolver))
                        .collect::<Result<Vec<_>>>()?;
                    terms.extend(params.iter().cloned());
                    let indices = inductive
                        .indices
                        .iter()
                        .map(|binder| canonicalize_expr(&binder.ty, resolver))
                        .collect::<Result<Vec<_>>>()?;
                    terms.extend(indices.iter().cloned());
                    let constructors = inductive
                        .constructors
                        .iter()
                        .map(|constructor| {
                            let ty = canonicalize_expr(&constructor.ty, resolver)?;
                            terms.push(ty.clone());
                            Ok((resolver.name_id(&Name::from_dotted(&constructor.name))?, ty))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let recursor = inductive
                        .recursor
                        .as_ref()
                        .map(|recursor| {
                            let ty = canonicalize_expr(&recursor.ty, resolver)?;
                            terms.push(ty.clone());
                            Ok::<_, CertError>((
                                resolver.name_id(&Name::from_dotted(&recursor.name))?,
                                universe_param_ids(&recursor.universe_params, resolver)?,
                                ty,
                                recursor
                                    .rules
                                    .as_ref()
                                    .map(|rules| RecursorRulesSpec {
                                        minor_start: rules.minor_start,
                                        major_index: rules.major_index,
                                    })
                                    .unwrap_or_else(|| RecursorRulesSpec {
                                        minor_start: inductive.params.len() + data.inductives.len(),
                                        major_index: inductive.params.len()
                                            + data.inductives.len()
                                            + data
                                                .inductives
                                                .iter()
                                                .map(|data| data.constructors.len())
                                                .sum::<usize>()
                                            + inductive.indices.len(),
                                    }),
                            ))
                        })
                        .transpose()?;
                    let sort = canonicalize_level(&inductive.sort, resolver)?;
                    Ok(CanonMutualInductive {
                        name: resolver.name_id(&Name::from_dotted(&inductive.name))?,
                        params,
                        indices,
                        sort,
                        constructors,
                        recursor,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let mut deps = dependencies_from_terms(terms.iter());
            remove_self_dependency(&mut deps, decl_index);
            Ok(CanonDecl {
                decl: CanonDeclPayload::MutualInductiveBlock {
                    name: resolver.name_id(&Name::from_dotted(&name))?,
                    universe_params: universe_param_ids(&universe_params, resolver)?,
                    universe_constraints,
                    inductives,
                },
                dependencies: deps,
            })
        }
        Decl::Constructor { name, .. } | Decl::Recursor { name, .. } => {
            Err(CertError::UnknownDependency {
                name: Name::from_dotted(name),
            })
        }
    }
}

pub(crate) fn canonical_producer_checked_decl_interface(
    decl: &Decl,
    lookup_env: &ProducerLookupEnv,
) -> Result<ProducerCheckedDeclInterface> {
    Ok(canonical_producer_checked_decl_hashes(decl, lookup_env)?.0)
}

pub(crate) fn canonical_producer_checked_decl_hashes(
    decl: &Decl,
    lookup_env: &ProducerLookupEnv,
) -> Result<(ProducerCheckedDeclInterface, DeclHashes)> {
    let resolved = canonical_producer_checked_decl_for_version(
        decl,
        lookup_env,
        CertificateFormatVersion::V0_4_0,
        &[],
    )?;
    Ok((resolved.interface, resolved.hashes))
}

pub(crate) struct CanonicalProducerCheckedDecl {
    pub(crate) interface: ProducerCheckedDeclInterface,
    pub(crate) hashes: DeclHashes,
    pub(crate) dependencies: Vec<DependencyEntry>,
}

pub(crate) fn canonical_producer_checked_decl_for_version(
    decl: &Decl,
    lookup_env: &ProducerLookupEnv,
    version: CertificateFormatVersion,
    local_implementation_dependencies: &[DependencyEntry],
) -> Result<CanonicalProducerCheckedDecl> {
    let current_decl_index = lookup_env.checked_decls.len();
    let mut names = BTreeSet::new();
    for import in &lookup_env.import_exports {
        collect_name(&mut names, &import.module);
    }
    collect_names_from_decl(&mut names, decl);
    let referenced_imports =
        producer_referenced_imported_export_names(decl, &lookup_env.imported_export_names);
    producer_collect_imported_axiom_names_for_referenced_exports(
        &mut names,
        &lookup_env.import_exports,
        &referenced_imports,
    )?;
    let name_table: Vec<_> = names.into_iter().collect();
    ensure_canonical_names(&name_table)?;
    let name_index: BTreeMap<_, _> = name_table
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect();
    let imported_decls =
        producer_imported_decl_map(&lookup_env.import_exports, &name_index, &referenced_imports)?;
    let referenced_builtins = name_index
        .keys()
        .filter(|name| {
            !lookup_env.checked_decl_name_to_index.contains_key(*name)
                && !lookup_env
                    .checked_generated_name_to_index
                    .contains_key(*name)
                && !imported_decls.contains_key(*name)
                && builtin_decl_interface_hash(name).is_some()
        })
        .cloned()
        .collect();
    let reference_bindings = build_reference_bindings(
        &lookup_env.checked_decl_name_to_index,
        &lookup_env.checked_generated_name_to_index,
        &imported_decls,
        &referenced_builtins,
    )?;
    let canon_term_memo = std::cell::RefCell::new(CanonTermMemo::default());
    let resolver = Resolver {
        current_decl_index,
        allow_self: matches!(
            decl,
            Decl::Inductive { .. } | Decl::Axiom { .. } | Decl::AxiomConstrained { .. }
        ),
        reference_bindings: &reference_bindings,
        name_index: &name_index,
        canon_term_memo: &canon_term_memo,
    };
    let previous_axioms: Vec<_> = lookup_env
        .checked_decls
        .iter()
        .map(|interface| union_axioms(interface.axiom_dependencies.iter().cloned()))
        .collect();
    let canon_decl = canonicalize_decl(decl.clone(), current_decl_index, &resolver)?;

    let mut collector = CanonNodeCollector::new(&name_table);
    collect_canon_decl_nodes(&canon_decl, &mut collector)?;
    let CanonBuiltTables {
        level_table: _,
        level_hashes,
        term_table,
        term_hashes,
        node_ids,
    } = collector.build_tables()?;
    let interface_hashes: Vec<_> = lookup_env
        .checked_decls
        .iter()
        .map(|interface| interface.decl_interface_hash)
        .collect();
    let finalized = finalize_canon_decl(
        current_decl_index,
        &canon_decl,
        CanonDeclFinalizeContext {
            version,
            node_ids: &node_ids,
            interface_hashes: &interface_hashes,
            previous_axioms: &previous_axioms,
            imported_decls: &imported_decls,
            name_table: &name_table,
            term_table: &term_table,
            level_hashes: &level_hashes,
            term_hashes: &term_hashes,
            include_direct_axioms: false,
            local_transparency: None,
        },
    )?;
    let mut dependencies = finalized.dependencies.clone();
    if version == CertificateFormatVersion::V0_4_0 {
        let opaque_targets = local_implementation_dependencies
            .iter()
            .map(|dependency| match dependency.global_ref() {
                GlobalRef::Local { decl_index }
                    if dependency.kind() == DependencyEntryKind::LocalImplementation =>
                {
                    Ok(*decl_index)
                }
                _ => Err(CertError::DecodeError),
            })
            .collect::<Result<BTreeSet<_>>>()?;
        dependencies.retain(|dependency| {
            !matches!(
                dependency.global_ref(),
                GlobalRef::Local { decl_index }
                    if dependency.kind() == DependencyEntryKind::Interface
                        && opaque_targets.contains(decl_index)
            )
        });
        dependencies.extend(local_implementation_dependencies.iter().cloned());
        dependencies.sort();
        dependencies.dedup();
    } else if !local_implementation_dependencies.is_empty() {
        return Err(CertError::LocalImplementationDependencyRequiresFormatUpgrade);
    }
    let hashes = if dependencies == finalized.dependencies {
        finalized.hashes
    } else {
        compute_decl_hashes(
            version,
            &finalized.payload,
            &dependencies,
            &finalized.axiom_dependencies,
            DeclHashTables {
                terms: &term_table,
                level_hashes: &level_hashes,
                term_hashes: &term_hashes,
                names: &name_table,
            },
        )?
    };
    let interface = ProducerCheckedDeclInterface {
        decl_interface_hash: hashes.decl_interface_hash,
        axiom_dependencies: finalized.axiom_dependencies,
    };
    Ok(CanonicalProducerCheckedDecl {
        interface,
        hashes,
        dependencies,
    })
}

struct Resolver<'a> {
    current_decl_index: usize,
    allow_self: bool,
    reference_bindings: &'a BTreeMap<Name, ResolvedReferenceBinding>,
    name_index: &'a BTreeMap<Name, usize>,
    // Canonicalization memo keyed by kernel `Arc<Expr>` pointer identity,
    // shared across every declaration of one module build. The anchored
    // `Arc<Expr>` keeps each key's node alive so a pointer can never be
    // reused while its entry exists. Sharing across declarations is sound
    // because a successful `resolve_const` only ever yields indices that
    // point backward, so an entry produced under an earlier declaration
    // stays valid under every later one (`index < current_decl_index` can
    // only relax as the index grows); failures are never memoized. Reusing
    // one `Arc<CanonTerm>` per shared kernel subtree preserves sharing,
    // which both skips re-canonicalizing the subtree and lets
    // `CanonTerm::cmp` short-circuit on pointer-equal children.
    canon_term_memo: &'a std::cell::RefCell<CanonTermMemo>,
}

type CanonTermMemo = HashMap<usize, (Arc<Expr>, Arc<CanonTerm>)>;

#[derive(Clone, Debug)]
struct ImportedDeclInfo {
    import_index: usize,
    decl_interface_hash: Hash,
    kind: ExportKind,
    axiom_dependencies: Vec<AxiomRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ResolvedReferenceBinding {
    LocalDeclaration {
        decl_index: usize,
    },
    LocalGenerated {
        owner_decl_index: usize,
        name: Name,
    },
    ImportedExport {
        import_index: usize,
        name: Name,
        decl_interface_hash: Hash,
        export_kind: ExportKind,
    },
    Builtin {
        name: Name,
        decl_interface_hash: Hash,
    },
}

fn build_reference_bindings(
    local_declarations: &BTreeMap<Name, usize>,
    local_generated: &BTreeMap<Name, usize>,
    imported_decls: &BTreeMap<Name, ImportedDeclInfo>,
    referenced_builtins: &BTreeSet<Name>,
) -> Result<BTreeMap<Name, ResolvedReferenceBinding>> {
    let mut bindings = BTreeMap::new();

    for name in referenced_builtins {
        let decl_interface_hash = builtin_decl_interface_hash(name)
            .ok_or_else(|| CertError::UnknownDependency { name: name.clone() })?;
        bindings.insert(
            name.clone(),
            ResolvedReferenceBinding::Builtin {
                name: name.clone(),
                decl_interface_hash,
            },
        );
    }
    for (name, info) in imported_decls {
        let binding = ResolvedReferenceBinding::ImportedExport {
            import_index: info.import_index,
            name: name.clone(),
            decl_interface_hash: info.decl_interface_hash,
            export_kind: info.kind,
        };
        if let Some(previous) = bindings.insert(name.clone(), binding.clone()) {
            if !matches!(previous, ResolvedReferenceBinding::Builtin { .. }) && previous != binding
            {
                return Err(reference_origin_mismatch(
                    name.clone(),
                    "unique imported export identity",
                    "ambiguous imported export identity",
                ));
            }
        }
    }
    for (name, decl_index) in local_declarations {
        bindings.insert(
            name.clone(),
            ResolvedReferenceBinding::LocalDeclaration {
                decl_index: *decl_index,
            },
        );
    }
    for (name, owner_decl_index) in local_generated {
        let replaced = bindings.insert(
            name.clone(),
            ResolvedReferenceBinding::LocalGenerated {
                owner_decl_index: *owner_decl_index,
                name: name.clone(),
            },
        );
        if matches!(
            replaced,
            Some(
                ResolvedReferenceBinding::LocalDeclaration { .. }
                    | ResolvedReferenceBinding::LocalGenerated { .. }
            )
        ) {
            return Err(CertError::DuplicateName { name: name.clone() });
        }
    }

    Ok(bindings)
}

struct FinalizedCanonDecl {
    payload: DeclPayload,
    dependencies: Vec<DependencyEntry>,
    axiom_dependencies: Vec<AxiomRef>,
    direct_axioms: Vec<AxiomRef>,
    hashes: DeclHashes,
}

struct CanonDeclFinalizeContext<'a> {
    version: CertificateFormatVersion,
    node_ids: &'a CanonNodeIds<'a>,
    interface_hashes: &'a [Hash],
    previous_axioms: &'a [Vec<AxiomRef>],
    imported_decls: &'a BTreeMap<Name, ImportedDeclInfo>,
    name_table: &'a [Name],
    term_table: &'a [TermNode],
    level_hashes: &'a [Hash],
    term_hashes: &'a [Hash],
    include_direct_axioms: bool,
    local_transparency: Option<CanonLocalTransparencyContext<'a>>,
}

struct CanonLocalTransparencyContext<'a> {
    previous_declarations: &'a [DeclCert],
    budget: &'a mut LocalTransparencyBudget,
}

// Shared by trusted certificate construction and producer token checking. Keep declaration
// dependency, transitive axiom, and hash finalization here so the two paths cannot drift.
fn finalize_canon_decl(
    decl_index: usize,
    canon_decl: &CanonDecl,
    mut context: CanonDeclFinalizeContext<'_>,
) -> Result<FinalizedCanonDecl> {
    let payload = materialize_decl_payload(&canon_decl.decl, context.node_ids)?;
    let dependencies = match context.local_transparency.as_mut() {
        Some(local_transparency) => {
            let closure = local_transparency_dependencies(
                context.version,
                decl_index,
                &payload,
                local_transparency.previous_declarations,
                context.term_table,
                local_transparency.budget,
            )?;
            complete_local_transparency_dependencies(
                &closure,
                decl_index,
                local_transparency.previous_declarations,
            )?
        }
        None => fill_local_dependency_hashes(&canon_decl.dependencies, context.interface_hashes)?,
    };
    let mut axiom_dependencies = axiom_dependencies_from_final_deps(
        &dependencies,
        context.previous_axioms,
        context.imported_decls,
        context.name_table,
    )?;
    let mut direct_axioms = if context.include_direct_axioms {
        direct_axioms_from_final_deps(
            &dependencies,
            context.previous_axioms,
            context.imported_decls,
            context.name_table,
        )?
    } else {
        Vec::new()
    };

    if let DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } = &payload {
        let preliminary = compute_decl_hashes(
            context.version,
            &payload,
            &dependencies,
            &[],
            DeclHashTables {
                terms: context.term_table,
                level_hashes: context.level_hashes,
                term_hashes: context.term_hashes,
                names: context.name_table,
            },
        )?;
        let self_ref = AxiomRef {
            global_ref: GlobalRef::Local { decl_index },
            name: *name,
            decl_interface_hash: preliminary.decl_interface_hash,
        };
        axiom_dependencies = union_axioms(axiom_dependencies.into_iter().chain([self_ref.clone()]));
        if context.include_direct_axioms {
            direct_axioms = union_axioms(direct_axioms.into_iter().chain([self_ref]));
        }
    }

    let hashes = compute_decl_hashes(
        context.version,
        &payload,
        &dependencies,
        &axiom_dependencies,
        DeclHashTables {
            terms: context.term_table,
            level_hashes: context.level_hashes,
            term_hashes: context.term_hashes,
            names: context.name_table,
        },
    )?;

    Ok(FinalizedCanonDecl {
        payload,
        dependencies,
        axiom_dependencies,
        direct_axioms,
        hashes,
    })
}

pub(crate) fn canonical_declaration_order(declarations: Vec<Decl>) -> Result<Vec<Decl>> {
    let local_names: Vec<_> = declarations
        .iter()
        .map(|decl| Name::from_dotted(decl.name()))
        .collect();
    ensure_unique_names(&local_names)?;
    let local_name_to_index: BTreeMap<_, _> = local_names
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect();

    let mut generated_name_to_index = BTreeMap::new();
    let mut public_names = local_names.clone();
    for (decl_index, decl) in declarations.iter().enumerate() {
        if let Decl::Inductive { data, .. } = decl {
            for constructor in &data.constructors {
                let name = Name::from_dotted(&constructor.name);
                generated_name_to_index.insert(name.clone(), decl_index);
                public_names.push(name);
            }
            if let Some(recursor) = &data.recursor {
                let name = Name::from_dotted(&recursor.name);
                generated_name_to_index.insert(name.clone(), decl_index);
                public_names.push(name);
            }
        } else if let Decl::MutualInductiveBlock { data, .. } = decl {
            for inductive in &data.inductives {
                let name = Name::from_dotted(&inductive.name);
                generated_name_to_index.insert(name.clone(), decl_index);
                public_names.push(name);
                for constructor in &inductive.constructors {
                    let name = Name::from_dotted(&constructor.name);
                    generated_name_to_index.insert(name.clone(), decl_index);
                    public_names.push(name);
                }
                if let Some(recursor) = &inductive.recursor {
                    let name = Name::from_dotted(&recursor.name);
                    generated_name_to_index.insert(name.clone(), decl_index);
                    public_names.push(name);
                }
            }
        }
    }
    ensure_unique_names(&public_names)?;
    for name in &public_names {
        if reserved_core_primitive_name(name) {
            return Err(CertError::ReservedCorePrimitive { name: name.clone() });
        }
    }

    let dependencies = declarations
        .iter()
        .enumerate()
        .map(|(decl_index, decl)| {
            let mut names = BTreeSet::new();
            collect_const_names_from_decl(&mut names, decl);
            Ok(names
                .into_iter()
                .filter_map(|name| {
                    local_name_to_index
                        .get(&name)
                        .or_else(|| generated_name_to_index.get(&name))
                        .copied()
                })
                .filter(|dependency| *dependency != decl_index)
                .collect::<BTreeSet<_>>())
        })
        .collect::<Result<Vec<_>>>()?;

    let mut emitted = BTreeSet::new();
    let mut remaining: BTreeSet<_> = (0..declarations.len()).collect();
    let mut ordered = Vec::with_capacity(declarations.len());
    while !remaining.is_empty() {
        let mut ready: Vec<_> = remaining
            .iter()
            .copied()
            .filter(|index| dependencies[*index].is_subset(&emitted))
            .collect();
        if ready.is_empty() {
            let index = *remaining.iter().next().ok_or(CertError::DecodeError)?;
            return Err(CertError::DependencyCycle {
                name: local_names[index].clone(),
            });
        }
        ready.sort_by_key(|index| local_names[*index].clone());
        for index in ready {
            remaining.remove(&index);
            emitted.insert(index);
            ordered.push(declarations[index].clone());
        }
    }

    Ok(ordered)
}

impl Resolver<'_> {
    fn name_id(&self, name: &Name) -> Result<NameId> {
        self.name_index
            .get(name)
            .copied()
            .ok_or_else(|| CertError::UnknownDependency { name: name.clone() })
    }

    fn resolve_const(&self, name: &Name) -> Result<GlobalRef> {
        let binding = self
            .reference_bindings
            .get(name)
            .ok_or_else(|| CertError::UnknownDependency { name: name.clone() })?;
        match binding {
            ResolvedReferenceBinding::LocalDeclaration { decl_index } => {
                self.resolve_local(name, *decl_index)?;
                Ok(GlobalRef::Local {
                    decl_index: *decl_index,
                })
            }
            ResolvedReferenceBinding::LocalGenerated {
                owner_decl_index, ..
            } => {
                self.resolve_local(name, *owner_decl_index)?;
                Ok(GlobalRef::LocalGenerated {
                    decl_index: *owner_decl_index,
                    name: self.name_id(name)?,
                })
            }
            ResolvedReferenceBinding::ImportedExport {
                import_index,
                decl_interface_hash,
                ..
            } => Ok(GlobalRef::Imported {
                import_index: *import_index,
                name: self.name_id(name)?,
                decl_interface_hash: *decl_interface_hash,
            }),
            ResolvedReferenceBinding::Builtin {
                decl_interface_hash,
                ..
            } => Ok(GlobalRef::Builtin {
                name: self.name_id(name)?,
                decl_interface_hash: *decl_interface_hash,
            }),
        }
    }

    fn resolve_local(&self, name: &Name, decl_index: usize) -> Result<()> {
        if decl_index < self.current_decl_index
            || (self.allow_self && decl_index == self.current_decl_index)
        {
            Ok(())
        } else {
            Err(CertError::DependencyCycle { name: name.clone() })
        }
    }
}

fn audit_emitted_reference_origins(
    parts: &ModuleCertParts,
    bindings: &BTreeMap<Name, ResolvedReferenceBinding>,
) -> Result<()> {
    for node in &parts.term_table {
        if let TermNode::Const { global_ref, .. } = node {
            audit_global_ref_origin(parts, bindings, global_ref)?;
        }
    }
    for declaration in &parts.declarations {
        for dependency in &declaration.dependencies {
            let (name, expected_hash) =
                audit_global_ref_origin(parts, bindings, dependency.global_ref())?;
            if dependency.decl_interface_hash() != expected_hash {
                return Err(reference_origin_mismatch(
                    name,
                    "binding interface hash",
                    "dependency interface hash",
                ));
            }
        }
        audit_axiom_ref_origins(parts, bindings, &declaration.axiom_dependencies)?;
    }
    for export in &parts.export_block {
        let name = parts
            .name_table
            .get(export.name)
            .ok_or(CertError::DecodeError)?;
        let owner_decl_index = match bindings.get(name) {
            Some(ResolvedReferenceBinding::LocalDeclaration { decl_index }) => *decl_index,
            Some(ResolvedReferenceBinding::LocalGenerated {
                owner_decl_index, ..
            }) => *owner_decl_index,
            Some(ResolvedReferenceBinding::ImportedExport { .. }) => {
                return Err(reference_origin_mismatch(
                    name.clone(),
                    "local export",
                    "imported export",
                ))
            }
            Some(ResolvedReferenceBinding::Builtin { .. }) | None => {
                return Err(reference_origin_mismatch(
                    name.clone(),
                    "local export",
                    "builtin or unknown export",
                ))
            }
        };
        let expected_hash = parts
            .declarations
            .get(owner_decl_index)
            .ok_or(CertError::DecodeError)?
            .hashes
            .decl_interface_hash;
        if export.decl_interface_hash != expected_hash {
            return Err(reference_origin_mismatch(
                name.clone(),
                "owner declaration interface hash",
                "export interface hash",
            ));
        }
        audit_axiom_ref_origins(parts, bindings, &export.axiom_dependencies)?;
    }
    audit_axiom_ref_origins(parts, bindings, &parts.axiom_report.module_axioms)?;
    Ok(())
}

fn audit_axiom_ref_origins(
    parts: &ModuleCertParts,
    bindings: &BTreeMap<Name, ResolvedReferenceBinding>,
    axioms: &[AxiomRef],
) -> Result<()> {
    for axiom in axioms {
        let (name, expected_hash) = audit_axiom_ref_origin(parts, bindings, &axiom.global_ref)?;
        let reported_name = parts
            .name_table
            .get(axiom.name)
            .ok_or(CertError::DecodeError)?;
        if reported_name != &name {
            return Err(reference_origin_mismatch(
                name,
                "reference name",
                "axiom dependency name",
            ));
        }
        if axiom.decl_interface_hash != expected_hash {
            return Err(reference_origin_mismatch(
                name,
                "binding interface hash",
                "axiom interface hash",
            ));
        }
    }
    Ok(())
}

fn audit_axiom_ref_origin(
    parts: &ModuleCertParts,
    bindings: &BTreeMap<Name, ResolvedReferenceBinding>,
    global_ref: &GlobalRef,
) -> Result<(Name, Hash)> {
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            parts
                .imports
                .get(*import_index)
                .ok_or(CertError::DecodeError)?;
            let name = parts
                .name_table
                .get(*name)
                .cloned()
                .ok_or(CertError::DecodeError)?;
            Ok((name, *decl_interface_hash))
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = parts
                .name_table
                .get(*name)
                .cloned()
                .ok_or(CertError::DecodeError)?;
            if builtin_decl_interface_hash(&name) != Some(*decl_interface_hash) {
                return Err(reference_origin_mismatch(
                    name,
                    "builtin axiom identity",
                    "builtin axiom with mismatched identity",
                ));
            }
            Ok((name, *decl_interface_hash))
        }
        GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {
            audit_global_ref_origin(parts, bindings, global_ref)
        }
    }
}

fn audit_global_ref_origin(
    parts: &ModuleCertParts,
    bindings: &BTreeMap<Name, ResolvedReferenceBinding>,
    global_ref: &GlobalRef,
) -> Result<(Name, Hash)> {
    match global_ref {
        GlobalRef::Local { decl_index } => {
            let declaration = parts
                .declarations
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?;
            let name = parts
                .name_table
                .get(decl_payload_name_id(&declaration.decl))
                .cloned()
                .ok_or(CertError::DecodeError)?;
            if bindings.get(&name)
                != Some(&ResolvedReferenceBinding::LocalDeclaration {
                    decl_index: *decl_index,
                })
            {
                return Err(reference_origin_mismatch(
                    name,
                    "local declaration",
                    "local declaration with mismatched owner",
                ));
            }
            Ok((name, declaration.hashes.decl_interface_hash))
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            let name = parts
                .name_table
                .get(*name)
                .cloned()
                .ok_or(CertError::DecodeError)?;
            if bindings.get(&name)
                != Some(&ResolvedReferenceBinding::LocalGenerated {
                    owner_decl_index: *decl_index,
                    name: name.clone(),
                })
            {
                return Err(reference_origin_mismatch(
                    name,
                    "local generated declaration",
                    "local generated declaration with mismatched owner",
                ));
            }
            let hash = parts
                .declarations
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash;
            Ok((name, hash))
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let name = parts
                .name_table
                .get(*name)
                .cloned()
                .ok_or(CertError::DecodeError)?;
            let matches = matches!(
                bindings.get(&name),
                Some(ResolvedReferenceBinding::ImportedExport {
                    import_index: expected_import,
                    name: expected_name,
                    decl_interface_hash: expected_hash,
                    export_kind: _,
                }) if expected_import == import_index
                    && expected_name == &name
                    && expected_hash == decl_interface_hash
            );
            if !matches {
                return Err(reference_origin_mismatch(
                    name,
                    "imported export identity",
                    "imported reference with mismatched identity",
                ));
            }
            Ok((name, *decl_interface_hash))
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = parts
                .name_table
                .get(*name)
                .cloned()
                .ok_or(CertError::DecodeError)?;
            if bindings.get(&name)
                != Some(&ResolvedReferenceBinding::Builtin {
                    name: name.clone(),
                    decl_interface_hash: *decl_interface_hash,
                })
            {
                return Err(reference_origin_mismatch(
                    name,
                    "builtin identity",
                    "builtin reference with mismatched identity",
                ));
            }
            Ok((name, *decl_interface_hash))
        }
    }
}

fn decl_payload_name_id(payload: &DeclPayload) -> NameId {
    match payload {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn reference_origin_mismatch(
    name: Name,
    expected: &'static str,
    actual: &'static str,
) -> CertError {
    CertError::ReferenceOriginMismatch {
        name,
        expected,
        actual,
    }
}

fn universe_param_ids(params: &[String], resolver: &Resolver<'_>) -> Result<Vec<NameId>> {
    params
        .iter()
        .map(|param| resolver.name_id(&Name::from_dotted(param)))
        .collect()
}

fn canonicalize_expr(expr: &Expr, resolver: &Resolver<'_>) -> Result<CanonTerm> {
    Ok(match expr {
        Expr::Sort(level) => CanonTerm::Sort(canonicalize_level(level, resolver)?),
        Expr::BVar(index) => CanonTerm::BVar(*index),
        Expr::Const { name, levels } => {
            let name = Name::from_dotted(name);
            CanonTerm::Const {
                global_ref: resolver.resolve_const(&name)?,
                levels: levels
                    .iter()
                    .map(|level| canonicalize_level(level, resolver))
                    .collect::<Result<Vec<_>>>()?,
            }
        }
        Expr::App(fun, arg) => CanonTerm::App(
            canonicalize_expr_rc(fun, resolver)?,
            canonicalize_expr_rc(arg, resolver)?,
        ),
        Expr::Lam { ty, body, .. } => CanonTerm::Lam {
            ty: canonicalize_expr_rc(ty, resolver)?,
            body: canonicalize_expr_rc(body, resolver)?,
        },
        Expr::Pi { ty, body, .. } => CanonTerm::Pi {
            ty: canonicalize_expr_rc(ty, resolver)?,
            body: canonicalize_expr_rc(body, resolver)?,
        },
    })
}

fn canonicalize_expr_rc(expr: &Arc<Expr>, resolver: &Resolver<'_>) -> Result<Arc<CanonTerm>> {
    let root_key = Arc::as_ptr(expr) as usize;
    if let Some((_, canon)) = resolver.canon_term_memo.borrow().get(&root_key) {
        return Ok(Arc::clone(canon));
    }

    let mut pending = vec![(Arc::clone(expr), false)];
    while let Some((expr, exiting)) = pending.pop() {
        let key = Arc::as_ptr(&expr) as usize;
        if resolver.canon_term_memo.borrow().contains_key(&key) {
            continue;
        }
        if !exiting {
            pending.push((Arc::clone(&expr), true));
            match expr.as_ref() {
                Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => {}
                Expr::App(fun, arg)
                | Expr::Lam {
                    ty: fun, body: arg, ..
                }
                | Expr::Pi {
                    ty: fun, body: arg, ..
                } => {
                    pending.push((Arc::clone(arg), false));
                    pending.push((Arc::clone(fun), false));
                }
            }
            continue;
        }
        let canon = Arc::new(canonicalize_expr(&expr, resolver)?);
        resolver
            .canon_term_memo
            .borrow_mut()
            .insert(key, (expr, canon));
    }

    resolver
        .canon_term_memo
        .borrow()
        .get(&root_key)
        .map(|(_, canon)| Arc::clone(canon))
        .ok_or(CertError::DecodeError)
}

fn canonicalize_level(level: &Level, resolver: &Resolver<'_>) -> Result<CanonLevel> {
    enum Frame {
        Visit(Level),
        Succ,
        Max,
        IMax,
    }

    let mut pending = vec![Frame::Visit(npa_kernel::level::normalize_level(
        level.clone(),
    ))];
    let mut values = Vec::<CanonLevel>::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Visit(Level::Zero) => values.push(CanonLevel::Zero),
            Frame::Visit(Level::Param(name)) => values.push(CanonLevel::Param(
                resolver.name_id(&Name::from_dotted(name))?,
            )),
            Frame::Visit(Level::Succ(inner)) => {
                pending.push(Frame::Succ);
                pending.push(Frame::Visit(*inner));
            }
            Frame::Visit(Level::Max(lhs, rhs)) => {
                pending.push(Frame::Max);
                pending.push(Frame::Visit(*rhs));
                pending.push(Frame::Visit(*lhs));
            }
            Frame::Visit(Level::IMax(lhs, rhs)) => {
                pending.push(Frame::IMax);
                pending.push(Frame::Visit(*rhs));
                pending.push(Frame::Visit(*lhs));
            }
            Frame::Succ => {
                let inner = values.pop().ok_or(CertError::DecodeError)?;
                values.push(CanonLevel::Succ(Box::new(inner)));
            }
            Frame::Max => {
                let rhs = values.pop().ok_or(CertError::DecodeError)?;
                let lhs = values.pop().ok_or(CertError::DecodeError)?;
                values.push(CanonLevel::Max(Box::new(lhs), Box::new(rhs)));
            }
            Frame::IMax => {
                let rhs = values.pop().ok_or(CertError::DecodeError)?;
                let lhs = values.pop().ok_or(CertError::DecodeError)?;
                values.push(CanonLevel::IMax(Box::new(lhs), Box::new(rhs)));
            }
        }
    }
    values.pop().ok_or(CertError::DecodeError)
}

fn canonicalize_universe_constraints(
    universe_params: &[String],
    constraints: &[UniverseConstraint],
    resolver: &Resolver<'_>,
) -> Result<Vec<CanonUniverseConstraint>> {
    let delta =
        npa_kernel::level::validate_universe_params(universe_params).map_err(CertError::Kernel)?;
    npa_kernel::level::ensure_universe_constraints_wf(&delta, constraints)
        .map_err(CertError::Kernel)?;
    constraints
        .iter()
        .map(|constraint| {
            Ok(CanonUniverseConstraint {
                lhs: canonicalize_level(&constraint.lhs, resolver)?,
                relation: constraint.relation,
                rhs: canonicalize_level(&constraint.rhs, resolver)?,
            })
        })
        .collect()
}

fn dependencies_from_terms<'a>(
    terms: impl IntoIterator<Item = &'a CanonTerm>,
) -> Vec<DependencyEntry> {
    let mut deps = BTreeSet::new();
    for term in terms {
        collect_dependencies(term, &mut deps);
    }
    deps.into_iter().collect()
}

fn remove_self_dependency(deps: &mut Vec<DependencyEntry>, current_decl_index: usize) {
    deps.retain(|dependency| {
        !matches!(
            dependency.global_ref(),
            GlobalRef::Local { decl_index } | GlobalRef::LocalGenerated { decl_index, .. }
                if *decl_index == current_decl_index
        )
    });
}

fn collect_dependencies(term: &CanonTerm, deps: &mut BTreeSet<DependencyEntry>) {
    match term {
        CanonTerm::Sort(_) | CanonTerm::BVar(_) => {}
        CanonTerm::Const { global_ref, .. } => {
            let decl_interface_hash = match global_ref {
                GlobalRef::Builtin {
                    decl_interface_hash,
                    ..
                } => *decl_interface_hash,
                GlobalRef::Imported {
                    decl_interface_hash,
                    ..
                } => *decl_interface_hash,
                GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => [0; 32],
            };
            deps.insert(
                DependencyEntry::checked_interface(global_ref.clone(), decl_interface_hash)
                    .expect("canonical global-reference hashes must agree"),
            );
        }
        CanonTerm::App(fun, arg) => {
            collect_dependencies(fun, deps);
            collect_dependencies(arg, deps);
        }
        CanonTerm::Lam { ty, body } | CanonTerm::Pi { ty, body } => {
            collect_dependencies(ty, deps);
            collect_dependencies(body, deps);
        }
    }
}

pub(crate) fn fill_local_dependency_hashes(
    dependencies: &[DependencyEntry],
    interface_hashes: &[Hash],
) -> Result<Vec<DependencyEntry>> {
    dependencies
        .iter()
        .map(|dependency| {
            let decl_interface_hash = match dependency.global_ref() {
                GlobalRef::Local { decl_index } => {
                    *interface_hashes
                        .get(*decl_index)
                        .ok_or(CertError::DependencyCycle {
                            name: Name::from_dotted(format!("local.{decl_index}")),
                        })?
                }
                GlobalRef::LocalGenerated { decl_index, .. } => *interface_hashes
                    .get(*decl_index)
                    .ok_or(CertError::DependencyCycle {
                        name: Name::from_dotted(format!("local.{decl_index}")),
                    })?,
                GlobalRef::Imported {
                    decl_interface_hash,
                    ..
                } => *decl_interface_hash,
                GlobalRef::Builtin {
                    decl_interface_hash,
                    ..
                } => *decl_interface_hash,
            };
            DependencyEntry::checked_interface(dependency.global_ref().clone(), decl_interface_hash)
        })
        .collect()
}

fn axiom_dependencies_from_final_deps(
    dependencies: &[DependencyEntry],
    previous_axioms: &[Vec<AxiomRef>],
    imported_decls: &BTreeMap<Name, ImportedDeclInfo>,
    name_table: &[Name],
) -> Result<Vec<AxiomRef>> {
    let mut axioms = BTreeSet::new();
    for dependency in dependencies {
        match dependency.global_ref() {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                let name_value = name_table.get(*name).ok_or(CertError::DecodeError)?;
                if builtin_is_axiom(name_value) {
                    axioms.insert(AxiomRef {
                        global_ref: dependency.global_ref().clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    });
                }
            }
            GlobalRef::Local { decl_index } | GlobalRef::LocalGenerated { decl_index, .. } => {
                if let Some(dep_axioms) = previous_axioms.get(*decl_index) {
                    axioms.extend(dep_axioms.iter().cloned());
                }
            }
            GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let name = name_table.get(*name).ok_or(CertError::DecodeError)?;
                let info = imported_decls
                    .get(name)
                    .filter(|info| {
                        info.import_index == *import_index
                            && info.decl_interface_hash == *decl_interface_hash
                    })
                    .ok_or_else(|| CertError::UnknownDependency { name: name.clone() })?;
                axioms.extend(info.axiom_dependencies.iter().cloned());
            }
        }
    }
    Ok(axioms.into_iter().collect())
}

fn local_axiom_ref_for_decl(decl_index: usize, dep_axioms: &[AxiomRef]) -> Option<AxiomRef> {
    dep_axioms
        .iter()
        .find(|axiom| {
            matches!(
                axiom.global_ref,
                GlobalRef::Local { decl_index: axiom_index } if axiom_index == decl_index
            )
        })
        .cloned()
}

fn direct_axioms_from_final_deps(
    dependencies: &[DependencyEntry],
    previous_axioms: &[Vec<AxiomRef>],
    imported_decls: &BTreeMap<Name, ImportedDeclInfo>,
    name_table: &[Name],
) -> Result<Vec<AxiomRef>> {
    let mut axioms = BTreeSet::new();
    for dependency in dependencies {
        match dependency.global_ref() {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                let name_value = name_table.get(*name).ok_or(CertError::DecodeError)?;
                if builtin_is_axiom(name_value) {
                    axioms.insert(AxiomRef {
                        global_ref: dependency.global_ref().clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    });
                }
            }
            GlobalRef::Local { decl_index } => {
                if let Some(axiom) = previous_axioms
                    .get(*decl_index)
                    .and_then(|dep_axioms| local_axiom_ref_for_decl(*decl_index, dep_axioms))
                {
                    axioms.insert(axiom);
                }
            }
            GlobalRef::LocalGenerated { .. } => {}
            GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let imported_name = name_table.get(*name).ok_or(CertError::DecodeError)?;
                let info = imported_decls
                    .get(imported_name)
                    .filter(|info| {
                        info.import_index == *import_index
                            && info.decl_interface_hash == *decl_interface_hash
                    })
                    .ok_or_else(|| CertError::UnknownDependency {
                        name: imported_name.clone(),
                    })?;
                if info.kind == ExportKind::Axiom {
                    axioms.insert(AxiomRef {
                        global_ref: dependency.global_ref().clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    });
                }
            }
        }
    }
    Ok(axioms.into_iter().collect())
}

pub(crate) fn collect_canon_decl_nodes(
    decl: &CanonDecl,
    collector: &mut CanonNodeCollector<'_>,
) -> Result<()> {
    match &decl.decl {
        CanonDeclPayload::Axiom {
            universe_constraints,
            ty,
            ..
        } => {
            collect_constraint_level_nodes(universe_constraints, collector)?;
            collector.collect_term(ty)?;
        }
        CanonDeclPayload::Def {
            universe_constraints,
            ty,
            value,
            ..
        } => {
            collect_constraint_level_nodes(universe_constraints, collector)?;
            collector.collect_term(ty)?;
            collector.collect_term(value)?;
        }
        CanonDeclPayload::Theorem {
            universe_constraints,
            ty,
            proof,
            ..
        } => {
            collect_constraint_level_nodes(universe_constraints, collector)?;
            collector.collect_term(ty)?;
            collector.collect_term(proof)?;
        }
        CanonDeclPayload::Inductive {
            universe_constraints,
            params,
            indices,
            sort,
            constructors,
            recursor,
            ..
        } => {
            collect_constraint_level_nodes(universe_constraints, collector)?;
            collector.collect_level(sort)?;
            collector.collect_term(&inductive_type_canon_term(params, indices, sort))?;
            for term in params.iter().chain(indices) {
                collector.collect_term(term)?;
            }
            for (_, term) in constructors {
                collector.collect_term(term)?;
            }
            if let Some((_, _, ty, _)) = recursor {
                collector.collect_term(ty)?;
            }
        }
        CanonDeclPayload::MutualInductiveBlock {
            universe_constraints,
            inductives,
            ..
        } => {
            collect_constraint_level_nodes(universe_constraints, collector)?;
            for inductive in inductives {
                collector.collect_level(&inductive.sort)?;
                collector.collect_term(&inductive_type_canon_term(
                    &inductive.params,
                    &inductive.indices,
                    &inductive.sort,
                ))?;
                for term in inductive.params.iter().chain(&inductive.indices) {
                    collector.collect_term(term)?;
                }
                for (_, term) in &inductive.constructors {
                    collector.collect_term(term)?;
                }
                if let Some((_, _, ty, _)) = &inductive.recursor {
                    collector.collect_term(ty)?;
                }
            }
        }
    }
    Ok(())
}

fn collect_constraint_level_nodes(
    constraints: &[CanonUniverseConstraint],
    collector: &mut CanonNodeCollector<'_>,
) -> Result<()> {
    for constraint in constraints {
        collector.collect_level(&constraint.lhs)?;
        collector.collect_level(&constraint.rhs)?;
    }
    Ok(())
}

fn inductive_type_canon_term(
    params: &[CanonTerm],
    indices: &[CanonTerm],
    sort: &CanonLevel,
) -> CanonTerm {
    params
        .iter()
        .chain(indices)
        .rev()
        .fold(CanonTerm::Sort(sort.clone()), |body, ty| CanonTerm::Pi {
            ty: Arc::new(ty.clone()),
            body: Arc::new(body),
        })
}

/// Deduplicates the canonical level/term nodes of one certificate build and
/// assigns table ids, keyed by the nodes' canonical (domain-separated
/// sha256) hashes instead of ordered structural comparisons. The final
/// table order is the same `(height, key bytes)` sort as before — that key
/// embeds child hashes, so distinct nodes can only tie by colliding sha256
/// hashes, which the certificate format already assumes away. One term hash
/// memo (pointer-keyed, see `TermHashMemo`) and one level hash memo are
/// shared across collection, table building, and payload materialization so
/// every node is hashed once per build.
pub(crate) struct CanonNodeCollector<'n> {
    names: &'n [Name],
    term_memo: TermHashMemo,
    level_memo: LevelHashMemo,
    seen_levels: HashSet<Hash>,
    levels: Vec<(usize, Vec<u8>, Hash, CanonLevel)>,
    seen_terms: HashSet<Hash>,
    terms: Vec<(usize, Vec<u8>, Hash, CanonTerm)>,
}

impl<'n> CanonNodeCollector<'n> {
    pub(crate) fn new(names: &'n [Name]) -> Self {
        Self {
            names,
            term_memo: TermHashMemo::new(),
            level_memo: LevelHashMemo::new(),
            seen_levels: HashSet::new(),
            levels: Vec::new(),
            seen_terms: HashSet::new(),
            terms: Vec::new(),
        }
    }

    fn collect_term(&mut self, term: &CanonTerm) -> Result<()> {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            let (height, key) = canon_term_height_and_key(
                term,
                self.names,
                &mut self.term_memo,
                &mut self.level_memo,
            )?;
            let hash = canon_term_hash_from_key(&key);
            // A seen hash implies every subterm (and its levels) has already
            // been collected, matching the old structural-set invariant.
            if !self.seen_terms.insert(hash) {
                continue;
            }
            self.terms.push((height, key, hash, term.clone()));
            match term {
                CanonTerm::Sort(level) => self.collect_level(level)?,
                CanonTerm::BVar(_) => {}
                CanonTerm::Const { levels, .. } => {
                    for level in levels {
                        self.collect_level(level)?;
                    }
                }
                CanonTerm::App(fun, arg) => {
                    pending.push(arg);
                    pending.push(fun);
                }
                CanonTerm::Lam { ty, body } | CanonTerm::Pi { ty, body } => {
                    pending.push(body);
                    pending.push(ty);
                }
            }
        }
        Ok(())
    }

    fn collect_level(&mut self, level: &CanonLevel) -> Result<()> {
        let mut pending = vec![level];
        while let Some(level) = pending.pop() {
            let hash = canon_level_hash(level, self.names, &mut self.level_memo)?;
            // A seen hash implies every sub-level has already been collected.
            if !self.seen_levels.insert(hash) {
                continue;
            }
            let key = canon_level_key(level, self.names, &mut self.level_memo)?;
            self.levels
                .push((level_height(level), key, hash, level.clone()));
            match level {
                CanonLevel::Zero | CanonLevel::Param(_) => {}
                CanonLevel::Succ(inner) => pending.push(inner),
                CanonLevel::Max(lhs, rhs) | CanonLevel::IMax(lhs, rhs) => {
                    pending.push(rhs);
                    pending.push(lhs);
                }
            }
        }
        Ok(())
    }

    /// Builds the sorted level/term tables together with their per-entry
    /// canonical hashes. The hash vectors are byte-identical to what
    /// `compute_level_hashes`/`compute_term_hashes` would recompute over
    /// the returned tables — the collector already hashed every node with
    /// the same domain separation and key encoding — so certificate
    /// construction needs no second hashing pass.
    pub(crate) fn build_tables(self) -> Result<CanonBuiltTables<'n>> {
        let Self {
            names,
            mut term_memo,
            mut level_memo,
            seen_levels: _,
            mut levels,
            seen_terms: _,
            mut terms,
        } = self;

        levels.sort_by(|lhs, rhs| (lhs.0, &lhs.1).cmp(&(rhs.0, &rhs.1)));
        let level_ids: HashMap<Hash, LevelId> = levels
            .iter()
            .enumerate()
            .map(|(index, (_, _, hash, _))| (*hash, index))
            .collect();
        let level_table = levels
            .iter()
            .map(|(_, _, _, level)| {
                Ok(match level {
                    CanonLevel::Zero => LevelNode::Zero,
                    CanonLevel::Succ(inner) => LevelNode::Succ(
                        level_ids[&canon_level_hash(inner, names, &mut level_memo)?],
                    ),
                    CanonLevel::Max(lhs, rhs) => LevelNode::Max(
                        level_ids[&canon_level_hash(lhs, names, &mut level_memo)?],
                        level_ids[&canon_level_hash(rhs, names, &mut level_memo)?],
                    ),
                    CanonLevel::IMax(lhs, rhs) => LevelNode::IMax(
                        level_ids[&canon_level_hash(lhs, names, &mut level_memo)?],
                        level_ids[&canon_level_hash(rhs, names, &mut level_memo)?],
                    ),
                    CanonLevel::Param(name) => LevelNode::Param(*name),
                })
            })
            .collect::<Result<Vec<_>>>()?;

        terms.sort_by(|lhs, rhs| (lhs.0, &lhs.1).cmp(&(rhs.0, &rhs.1)));
        let term_ids: HashMap<Hash, TermId> = terms
            .iter()
            .enumerate()
            .map(|(index, (_, _, hash, _))| (*hash, index))
            .collect();
        let term_id_rc = |term: &Arc<CanonTerm>,
                          term_memo: &mut TermHashMemo,
                          level_memo: &mut LevelHashMemo|
         -> Result<TermId> {
            let (_, hash) = canon_term_height_and_hash(term, names, term_memo, level_memo)?;
            Ok(term_ids[&hash])
        };
        let term_table = terms
            .iter()
            .map(|(_, _, _, term)| {
                Ok(match term {
                    CanonTerm::Sort(level) => {
                        TermNode::Sort(level_ids[&canon_level_hash(level, names, &mut level_memo)?])
                    }
                    CanonTerm::BVar(index) => TermNode::BVar(*index),
                    CanonTerm::Const { global_ref, levels } => TermNode::Const {
                        global_ref: global_ref.clone(),
                        levels: levels
                            .iter()
                            .map(|level| {
                                Ok(level_ids[&canon_level_hash(level, names, &mut level_memo)?])
                            })
                            .collect::<Result<Vec<_>>>()?,
                    },
                    CanonTerm::App(fun, arg) => TermNode::App(
                        term_id_rc(fun, &mut term_memo, &mut level_memo)?,
                        term_id_rc(arg, &mut term_memo, &mut level_memo)?,
                    ),
                    CanonTerm::Lam { ty, body } => TermNode::Lam {
                        ty: term_id_rc(ty, &mut term_memo, &mut level_memo)?,
                        body: term_id_rc(body, &mut term_memo, &mut level_memo)?,
                    },
                    CanonTerm::Pi { ty, body } => TermNode::Pi {
                        ty: term_id_rc(ty, &mut term_memo, &mut level_memo)?,
                        body: term_id_rc(body, &mut term_memo, &mut level_memo)?,
                    },
                })
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(CanonBuiltTables {
            level_table,
            level_hashes: levels.iter().map(|(_, _, hash, _)| *hash).collect(),
            term_table,
            term_hashes: terms.iter().map(|(_, _, hash, _)| *hash).collect(),
            node_ids: CanonNodeIds {
                names,
                level_ids,
                term_ids,
                term_memo: std::cell::RefCell::new(term_memo),
                level_memo: std::cell::RefCell::new(level_memo),
            },
        })
    }
}

pub(crate) struct CanonBuiltTables<'n> {
    pub(crate) level_table: Vec<LevelNode>,
    pub(crate) level_hashes: Vec<Hash>,
    pub(crate) term_table: Vec<TermNode>,
    pub(crate) term_hashes: Vec<Hash>,
    pub(crate) node_ids: CanonNodeIds<'n>,
}

/// Hash-keyed replacement for the old `BTreeMap<CanonTerm, TermId>` /
/// `BTreeMap<CanonLevel, LevelId>` id maps. Lookups hash the node (children
/// through the shared memos, so this is shallow for already-seen subtrees)
/// and index by the canonical hash; a missing entry panics exactly like the
/// old map indexing did.
pub(crate) struct CanonNodeIds<'n> {
    names: &'n [Name],
    level_ids: HashMap<Hash, LevelId>,
    term_ids: HashMap<Hash, TermId>,
    term_memo: std::cell::RefCell<TermHashMemo>,
    level_memo: std::cell::RefCell<LevelHashMemo>,
}

impl CanonNodeIds<'_> {
    fn level_id(&self, level: &CanonLevel) -> Result<LevelId> {
        let hash = canon_level_hash(level, self.names, &mut self.level_memo.borrow_mut())?;
        Ok(self.level_ids[&hash])
    }

    fn term_id(&self, term: &CanonTerm) -> Result<TermId> {
        let (_, key) = canon_term_height_and_key(
            term,
            self.names,
            &mut self.term_memo.borrow_mut(),
            &mut self.level_memo.borrow_mut(),
        )?;
        Ok(self.term_ids[&canon_term_hash_from_key(&key)])
    }
}

pub(crate) fn materialize_decl_payload(
    decl: &CanonDeclPayload,
    node_ids: &CanonNodeIds<'_>,
) -> Result<DeclPayload> {
    Ok(match decl {
        CanonDeclPayload::Axiom {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            let universe_constraints =
                materialize_universe_constraints(universe_constraints, node_ids)?;
            if universe_constraints.is_empty() {
                DeclPayload::Axiom {
                    name: *name,
                    universe_params: universe_params.clone(),
                    ty: node_ids.term_id(ty)?,
                }
            } else {
                DeclPayload::AxiomConstrained {
                    name: *name,
                    universe_params: universe_params.clone(),
                    universe_constraints,
                    ty: node_ids.term_id(ty)?,
                }
            }
        }
        CanonDeclPayload::Def {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => {
            let universe_constraints =
                materialize_universe_constraints(universe_constraints, node_ids)?;
            if universe_constraints.is_empty() {
                DeclPayload::Def {
                    name: *name,
                    universe_params: universe_params.clone(),
                    ty: node_ids.term_id(ty)?,
                    value: node_ids.term_id(value)?,
                    reducibility: *reducibility,
                }
            } else {
                DeclPayload::DefConstrained {
                    name: *name,
                    universe_params: universe_params.clone(),
                    universe_constraints,
                    ty: node_ids.term_id(ty)?,
                    value: node_ids.term_id(value)?,
                    reducibility: *reducibility,
                }
            }
        }
        CanonDeclPayload::Theorem {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
        } => {
            let universe_constraints =
                materialize_universe_constraints(universe_constraints, node_ids)?;
            if universe_constraints.is_empty() {
                DeclPayload::Theorem {
                    name: *name,
                    universe_params: universe_params.clone(),
                    ty: node_ids.term_id(ty)?,
                    proof: node_ids.term_id(proof)?,
                    opacity: Opacity::Opaque,
                }
            } else {
                DeclPayload::TheoremConstrained {
                    name: *name,
                    universe_params: universe_params.clone(),
                    universe_constraints,
                    ty: node_ids.term_id(ty)?,
                    proof: node_ids.term_id(proof)?,
                    opacity: Opacity::Opaque,
                }
            }
        }
        CanonDeclPayload::Inductive {
            name,
            universe_params,
            universe_constraints,
            params,
            indices,
            sort,
            constructors,
            recursor,
        } => {
            let universe_constraints =
                materialize_universe_constraints(universe_constraints, node_ids)?;
            let params: Vec<_> = params
                .iter()
                .map(|ty| {
                    Ok(BinderType {
                        ty: node_ids.term_id(ty)?,
                    })
                })
                .collect::<Result<_>>()?;
            let indices: Vec<_> = indices
                .iter()
                .map(|ty| {
                    Ok(BinderType {
                        ty: node_ids.term_id(ty)?,
                    })
                })
                .collect::<Result<_>>()?;
            let constructors: Vec<_> = constructors
                .iter()
                .map(|(name, ty)| {
                    Ok(ConstructorSpec {
                        name: *name,
                        ty: node_ids.term_id(ty)?,
                    })
                })
                .collect::<Result<_>>()?;
            let recursor = recursor
                .as_ref()
                .map(|(name, params, ty, rules)| -> Result<RecursorSpec> {
                    Ok(RecursorSpec {
                        name: *name,
                        universe_params: params.clone(),
                        ty: node_ids.term_id(ty)?,
                        rules: *rules,
                    })
                })
                .transpose()?;
            if universe_constraints.is_empty() {
                DeclPayload::Inductive {
                    name: *name,
                    universe_params: universe_params.clone(),
                    params,
                    indices,
                    sort: node_ids.level_id(sort)?,
                    constructors,
                    recursor,
                }
            } else {
                DeclPayload::InductiveConstrained {
                    name: *name,
                    universe_params: universe_params.clone(),
                    universe_constraints,
                    params,
                    indices,
                    sort: node_ids.level_id(sort)?,
                    constructors,
                    recursor,
                }
            }
        }
        CanonDeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => {
            let universe_constraints =
                materialize_universe_constraints(universe_constraints, node_ids)?;
            let inductives = inductives
                .iter()
                .map(|inductive| {
                    Ok(MutualInductiveSpec {
                        name: inductive.name,
                        params: inductive
                            .params
                            .iter()
                            .map(|ty| {
                                Ok(BinderType {
                                    ty: node_ids.term_id(ty)?,
                                })
                            })
                            .collect::<Result<_>>()?,
                        indices: inductive
                            .indices
                            .iter()
                            .map(|ty| {
                                Ok(BinderType {
                                    ty: node_ids.term_id(ty)?,
                                })
                            })
                            .collect::<Result<_>>()?,
                        sort: node_ids.level_id(&inductive.sort)?,
                        constructors: inductive
                            .constructors
                            .iter()
                            .map(|(name, ty)| {
                                Ok(ConstructorSpec {
                                    name: *name,
                                    ty: node_ids.term_id(ty)?,
                                })
                            })
                            .collect::<Result<_>>()?,
                        recursor: inductive
                            .recursor
                            .as_ref()
                            .map(|(name, params, ty, rules)| -> Result<RecursorSpec> {
                                Ok(RecursorSpec {
                                    name: *name,
                                    universe_params: params.clone(),
                                    ty: node_ids.term_id(ty)?,
                                    rules: *rules,
                                })
                            })
                            .transpose()?,
                    })
                })
                .collect::<Result<_>>()?;
            DeclPayload::MutualInductiveBlock {
                name: *name,
                universe_params: universe_params.clone(),
                universe_constraints,
                inductives,
            }
        }
    })
}

fn materialize_universe_constraints(
    constraints: &[CanonUniverseConstraint],
    node_ids: &CanonNodeIds<'_>,
) -> Result<Vec<UniverseConstraintSpec>> {
    constraints
        .iter()
        .map(|constraint| {
            Ok(UniverseConstraintSpec {
                lhs: node_ids.level_id(&constraint.lhs)?,
                relation: constraint.relation,
                rhs: node_ids.level_id(&constraint.rhs)?,
            })
        })
        .collect()
}

fn collect_name(names: &mut BTreeSet<Name>, name: &Name) {
    names.insert(name.clone());
}

fn collect_names_from_decl(names: &mut BTreeSet<Name>, decl: &Decl) {
    collect_name(names, &Name::from_dotted(decl.name()));
    for param in decl.universe_params() {
        collect_name(names, &Name::from_dotted(param));
    }
    for constraint in decl.universe_constraints() {
        collect_names_from_level(names, &constraint.lhs);
        collect_names_from_level(names, &constraint.rhs);
    }
    if !matches!(decl, Decl::MutualInductiveBlock { .. }) {
        collect_names_from_expr(names, decl.ty());
    }
    match decl {
        Decl::Def { value, .. } | Decl::DefConstrained { value, .. } => {
            collect_names_from_expr(names, value)
        }
        Decl::Theorem { proof, .. } | Decl::TheoremConstrained { proof, .. } => {
            collect_names_from_expr(names, proof)
        }
        Decl::Inductive { data, .. } => {
            for param in &data.params {
                collect_names_from_expr(names, &param.ty);
            }
            for index in &data.indices {
                collect_names_from_expr(names, &index.ty);
            }
            collect_name(names, &Name::from_dotted(&data.name));
            for constructor in &data.constructors {
                collect_name(names, &Name::from_dotted(&constructor.name));
                collect_names_from_expr(names, &constructor.ty);
            }
            if let Some(recursor) = &data.recursor {
                collect_name(names, &Name::from_dotted(&recursor.name));
                for param in &recursor.universe_params {
                    collect_name(names, &Name::from_dotted(param));
                }
                collect_names_from_expr(names, &recursor.ty);
            }
        }
        Decl::MutualInductiveBlock { data, .. } => {
            collect_name(names, &Name::from_dotted(&data.name));
            for inductive in &data.inductives {
                collect_name(names, &Name::from_dotted(&inductive.name));
                for param in &inductive.params {
                    collect_names_from_expr(names, &param.ty);
                }
                for index in &inductive.indices {
                    collect_names_from_expr(names, &index.ty);
                }
                for constructor in &inductive.constructors {
                    collect_name(names, &Name::from_dotted(&constructor.name));
                    collect_names_from_expr(names, &constructor.ty);
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_name(names, &Name::from_dotted(&recursor.name));
                    for param in &recursor.universe_params {
                        collect_name(names, &Name::from_dotted(param));
                    }
                    collect_names_from_expr(names, &recursor.ty);
                }
            }
        }
        _ => {}
    }
}

fn collect_const_names_from_decl(names: &mut BTreeSet<Name>, decl: &Decl) {
    if !matches!(decl, Decl::MutualInductiveBlock { .. }) {
        collect_const_names_from_expr(names, decl.ty());
    }
    match decl {
        Decl::Def { value, .. } | Decl::DefConstrained { value, .. } => {
            collect_const_names_from_expr(names, value)
        }
        Decl::Theorem { proof, .. } | Decl::TheoremConstrained { proof, .. } => {
            collect_const_names_from_expr(names, proof)
        }
        Decl::Inductive { data, .. } => {
            for param in &data.params {
                collect_const_names_from_expr(names, &param.ty);
            }
            for index in &data.indices {
                collect_const_names_from_expr(names, &index.ty);
            }
            for constructor in &data.constructors {
                collect_const_names_from_expr(names, &constructor.ty);
            }
            if let Some(recursor) = &data.recursor {
                collect_const_names_from_expr(names, &recursor.ty);
            }
        }
        Decl::MutualInductiveBlock { data, .. } => {
            for inductive in &data.inductives {
                for param in &inductive.params {
                    collect_const_names_from_expr(names, &param.ty);
                }
                for index in &inductive.indices {
                    collect_const_names_from_expr(names, &index.ty);
                }
                for constructor in &inductive.constructors {
                    collect_const_names_from_expr(names, &constructor.ty);
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_const_names_from_expr(names, &recursor.ty);
                }
            }
        }
        Decl::Axiom { .. }
        | Decl::AxiomConstrained { .. }
        | Decl::Constructor { .. }
        | Decl::Recursor { .. } => {}
    }
}

fn collect_const_names_from_expr(names: &mut BTreeSet<Name>, expr: &Expr) {
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(expr) as usize) {
            continue;
        }
        match expr {
            Expr::Sort(_) | Expr::BVar(_) => {}
            Expr::Const { name, .. } => {
                collect_name(names, &Name::from_dotted(name));
            }
            Expr::App(fun, arg)
            | Expr::Lam {
                ty: fun, body: arg, ..
            }
            | Expr::Pi {
                ty: fun, body: arg, ..
            } => {
                pending.push(arg);
                pending.push(fun);
            }
        }
    }
}

fn collect_names_from_expr(names: &mut BTreeSet<Name>, expr: &Expr) {
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(expr) as usize) {
            continue;
        }
        match expr {
            Expr::Sort(level) => collect_names_from_level(names, level),
            Expr::BVar(_) => {}
            Expr::Const { name, levels } => {
                collect_name(names, &Name::from_dotted(name));
                for level in levels {
                    collect_names_from_level(names, level);
                }
            }
            Expr::App(fun, arg)
            | Expr::Lam {
                ty: fun, body: arg, ..
            }
            | Expr::Pi {
                ty: fun, body: arg, ..
            } => {
                pending.push(arg);
                pending.push(fun);
            }
        }
    }
}

fn collect_names_from_level(names: &mut BTreeSet<Name>, level: &Level) {
    let mut pending = vec![level];
    while let Some(level) = pending.pop() {
        match level {
            Level::Zero => {}
            Level::Succ(inner) => pending.push(inner),
            Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
                pending.push(rhs);
                pending.push(lhs);
            }
            Level::Param(name) => collect_name(names, &Name::from_dotted(name)),
        }
    }
}

pub(crate) fn ensure_unique_names(names: &[Name]) -> Result<()> {
    let mut seen = BTreeSet::new();
    for name in names {
        if !seen.insert(name.clone()) {
            return Err(CertError::DuplicateName { name: name.clone() });
        }
    }
    Ok(())
}

fn ensure_canonical_names(names: &[Name]) -> Result<()> {
    if names.iter().all(Name::is_canonical) {
        Ok(())
    } else {
        Err(CertError::NonCanonicalEncoding { object: "Name" })
    }
}

fn imported_decl_map(
    imports: &[&dyn CertificateImportView],
    name_index: &BTreeMap<Name, usize>,
    referenced_names: &BTreeSet<Name>,
    preferred_imports: &BTreeMap<Name, ImportEntry>,
) -> Result<BTreeMap<Name, ImportedDeclInfo>> {
    let mut map = BTreeMap::new();
    for (import_index, import) in imports.iter().enumerate() {
        for entry in import.export_block() {
            let name = import
                .name_table()
                .get(entry.name)
                .ok_or(CertError::DecodeError)?;
            if import_export_uses_builtin_eq_rec(*import, entry)? {
                continue;
            }
            if !referenced_names.contains(name) || !name_index.contains_key(name) {
                continue;
            }
            if preferred_imports
                .get(name)
                .is_some_and(|preferred| !import_view_matches_import_entry(*import, preferred))
            {
                continue;
            }
            let axiom_dependencies = entry
                .axiom_dependencies
                .iter()
                .map(|axiom| remap_imported_axiom_ref(imports, *import, axiom, name_index))
                .collect::<Result<Vec<_>>>()?;
            let old = map.insert(
                name.clone(),
                ImportedDeclInfo {
                    import_index,
                    decl_interface_hash: entry.decl_interface_hash,
                    kind: entry.kind,
                    axiom_dependencies,
                },
            );
            if old.is_some() {
                return Err(CertError::DuplicateName { name: name.clone() });
            }
        }
    }
    Ok(map)
}

fn import_view_matches_import_entry(
    module: &dyn CertificateImportView,
    entry: &ImportEntry,
) -> bool {
    module.module() == &entry.module
        && module.export_hash() == entry.export_hash
        && entry
            .certificate_hash
            .is_none_or(|hash| module.certificate_hash() == hash)
}

fn producer_imported_decl_map(
    imports: &[ProducerImportExportView],
    name_index: &BTreeMap<Name, usize>,
    referenced_names: &BTreeSet<Name>,
) -> Result<BTreeMap<Name, ImportedDeclInfo>> {
    let mut map = BTreeMap::new();
    for (import_index, import) in imports.iter().enumerate() {
        for entry in &import.exports {
            let name = import
                .name_table
                .get(entry.name)
                .ok_or(CertError::DecodeError)?;
            if !referenced_names.contains(name) || !name_index.contains_key(name) {
                continue;
            }
            let axiom_dependencies = entry
                .axiom_dependencies
                .iter()
                .map(|axiom| remap_producer_imported_axiom_ref(imports, import, axiom, name_index))
                .collect::<Result<Vec<_>>>()?;
            let old = map.insert(
                name.clone(),
                ImportedDeclInfo {
                    import_index,
                    decl_interface_hash: entry.decl_interface_hash,
                    kind: entry.kind,
                    axiom_dependencies,
                },
            );
            if old.is_some() {
                return Err(CertError::DuplicateName { name: name.clone() });
            }
        }
    }
    Ok(map)
}

fn remap_imported_axiom_ref(
    imports: &[&dyn CertificateImportView],
    import: &dyn CertificateImportView,
    axiom: &AxiomRef,
    name_index: &BTreeMap<Name, usize>,
) -> Result<AxiomRef> {
    let axiom_name = import
        .name_table()
        .get(axiom.name)
        .ok_or(CertError::DecodeError)?;
    let name = *name_index.get(axiom_name).ok_or(CertError::DecodeError)?;
    if let GlobalRef::Builtin {
        decl_interface_hash,
        ..
    } = &axiom.global_ref
    {
        if builtin_decl_interface_hash(axiom_name) != Some(*decl_interface_hash) {
            return Err(CertError::UnknownDependency {
                name: axiom_name.clone(),
            });
        }
        return Ok(AxiomRef {
            global_ref: GlobalRef::Builtin {
                name,
                decl_interface_hash: *decl_interface_hash,
            },
            name,
            decl_interface_hash: *decl_interface_hash,
        });
    }
    let import_index =
        import_index_exporting_axiom(imports, axiom_name, axiom.decl_interface_hash)?;
    Ok(AxiomRef {
        global_ref: GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash: axiom.decl_interface_hash,
        },
        name,
        decl_interface_hash: axiom.decl_interface_hash,
    })
}

fn remap_producer_imported_axiom_ref(
    imports: &[ProducerImportExportView],
    import: &ProducerImportExportView,
    axiom: &AxiomRef,
    name_index: &BTreeMap<Name, usize>,
) -> Result<AxiomRef> {
    let axiom_name = import
        .name_table
        .get(axiom.name)
        .ok_or(CertError::DecodeError)?;
    let name = *name_index.get(axiom_name).ok_or(CertError::DecodeError)?;
    if let GlobalRef::Builtin {
        decl_interface_hash,
        ..
    } = &axiom.global_ref
    {
        if builtin_decl_interface_hash(axiom_name) != Some(*decl_interface_hash) {
            return Err(CertError::UnknownDependency {
                name: axiom_name.clone(),
            });
        }
        return Ok(AxiomRef {
            global_ref: GlobalRef::Builtin {
                name,
                decl_interface_hash: *decl_interface_hash,
            },
            name,
            decl_interface_hash: *decl_interface_hash,
        });
    }
    let import_index =
        producer_import_index_exporting_axiom(imports, axiom_name, axiom.decl_interface_hash)?;
    Ok(AxiomRef {
        global_ref: GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash: axiom.decl_interface_hash,
        },
        name,
        decl_interface_hash: axiom.decl_interface_hash,
    })
}

fn referenced_imported_export_names(
    declarations: &[Decl],
    imports: &[&dyn CertificateImportView],
    local_public_names: &[Name],
) -> Result<BTreeSet<Name>> {
    let mut referenced_names = BTreeSet::new();
    for decl in declarations {
        collect_const_names_from_decl(&mut referenced_names, decl);
    }

    let mut local_public_names = local_public_names.iter().cloned().collect::<BTreeSet<_>>();
    for decl in declarations {
        if let Decl::Inductive { data, .. } = decl {
            local_public_names.insert(Name::from_dotted(&data.name));
        }
    }
    referenced_names.retain(|name| !local_public_names.contains(name));

    let mut imported_exports = BTreeSet::new();
    for import in imports {
        for entry in import.export_block() {
            if import_export_uses_builtin_eq_rec(*import, entry)? {
                continue;
            }
            imported_exports.insert(
                import
                    .name_table()
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            );
        }
    }
    referenced_names.retain(|name| imported_exports.contains(name));

    Ok(referenced_names)
}

fn producer_referenced_imported_export_names(
    decl: &Decl,
    imported_export_names: &BTreeSet<Name>,
) -> BTreeSet<Name> {
    let mut referenced_names = BTreeSet::new();
    collect_const_names_from_decl(&mut referenced_names, decl);
    referenced_names.retain(|name| imported_export_names.contains(name));
    referenced_names
}

fn referenced_builtin_names(
    declarations: &[Decl],
    imports: &[&dyn CertificateImportView],
    local_public_names: &[Name],
) -> Result<BTreeSet<Name>> {
    let mut referenced_names = BTreeSet::new();
    for decl in declarations {
        collect_const_names_from_decl(&mut referenced_names, decl);
    }

    let mut local_public_names = local_public_names.iter().cloned().collect::<BTreeSet<_>>();
    for decl in declarations {
        if let Decl::Inductive { data, .. } = decl {
            local_public_names.insert(Name::from_dotted(&data.name));
        }
    }
    referenced_names.retain(|name| !local_public_names.contains(name));

    let mut imported_exports = BTreeSet::new();
    for import in imports {
        for entry in import.export_block() {
            if import_export_uses_builtin_eq_rec(*import, entry)? {
                continue;
            }
            imported_exports.insert(
                import
                    .name_table()
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            );
        }
    }
    referenced_names.retain(|name| {
        !imported_exports.contains(name) && builtin_decl_interface_hash(name).is_some()
    });

    Ok(referenced_names)
}

fn import_export_uses_builtin_eq_rec(
    import: &dyn CertificateImportView,
    entry: &ExportEntry,
) -> Result<bool> {
    let Some(entry_name) = import.name_table().get(entry.name) else {
        return Err(CertError::DecodeError);
    };
    if entry_name.as_dotted() != "Eq.rec" {
        return Ok(false);
    }

    for candidate in import.export_block() {
        let Some(candidate_name) = import.name_table().get(candidate.name) else {
            return Err(CertError::DecodeError);
        };
        if candidate.kind == ExportKind::Inductive && candidate_name.as_dotted() == "Eq" {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_imported_axiom_names_for_referenced_exports(
    names: &mut BTreeSet<Name>,
    imports: &[&dyn CertificateImportView],
    referenced_names: &BTreeSet<Name>,
) -> Result<()> {
    for import in imports {
        for entry in import.export_block() {
            let entry_name = import
                .name_table()
                .get(entry.name)
                .ok_or(CertError::DecodeError)?;
            if !referenced_names.contains(entry_name) {
                continue;
            }
            for axiom in &entry.axiom_dependencies {
                let axiom_name = import
                    .name_table()
                    .get(axiom.name)
                    .ok_or(CertError::DecodeError)?;
                collect_name(names, axiom_name);
            }
        }
    }
    Ok(())
}

fn producer_collect_imported_axiom_names_for_referenced_exports(
    names: &mut BTreeSet<Name>,
    imports: &[ProducerImportExportView],
    referenced_names: &BTreeSet<Name>,
) -> Result<()> {
    for import in imports {
        for entry in &import.exports {
            let entry_name = import
                .name_table
                .get(entry.name)
                .ok_or(CertError::DecodeError)?;
            if !referenced_names.contains(entry_name) {
                continue;
            }
            for axiom in &entry.axiom_dependencies {
                let axiom_name = import
                    .name_table
                    .get(axiom.name)
                    .ok_or(CertError::DecodeError)?;
                collect_name(names, axiom_name);
            }
        }
    }
    Ok(())
}

fn import_index_exporting_axiom(
    imports: &[&dyn CertificateImportView],
    axiom_name: &Name,
    decl_interface_hash: Hash,
) -> Result<usize> {
    imports
        .iter()
        .enumerate()
        .find_map(|(import_index, import)| {
            import
                .export_block()
                .iter()
                .any(|entry| {
                    entry.kind == ExportKind::Axiom
                        && entry.decl_interface_hash == decl_interface_hash
                        && import
                            .name_table()
                            .get(entry.name)
                            .is_some_and(|name| name == axiom_name)
                })
                .then_some(import_index)
        })
        .ok_or_else(|| CertError::UnknownDependency {
            name: axiom_name.clone(),
        })
}

fn producer_import_index_exporting_axiom(
    imports: &[ProducerImportExportView],
    axiom_name: &Name,
    decl_interface_hash: Hash,
) -> Result<usize> {
    imports
        .iter()
        .enumerate()
        .find_map(|(import_index, import)| {
            import
                .exports
                .iter()
                .any(|entry| {
                    entry.kind == ExportKind::Axiom
                        && entry.decl_interface_hash == decl_interface_hash
                        && import
                            .name_table
                            .get(entry.name)
                            .is_some_and(|name| name == axiom_name)
                })
                .then_some(import_index)
        })
        .ok_or_else(|| CertError::UnknownDependency {
            name: axiom_name.clone(),
        })
}

pub(crate) fn union_axioms(axioms: impl IntoIterator<Item = AxiomRef>) -> Vec<AxiomRef> {
    axioms
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[cfg(test)]
mod reference_binding_tests {
    use super::*;

    #[test]
    fn raw_name_collection_is_stack_safe_and_memoizes_shared_dags() {
        let mut expr = Arc::new(Expr::konst("Fixture.leaf", Vec::new()));
        for _ in 0..8_192 {
            expr = Arc::new(Expr::App(Arc::clone(&expr), Arc::clone(&expr)));
        }
        let mut names = BTreeSet::new();
        collect_names_from_expr(&mut names, &expr);
        assert_eq!(names, BTreeSet::from([Name::from_dotted("Fixture.leaf")]));
        names.clear();
        collect_const_names_from_expr(&mut names, &expr);
        assert_eq!(names, BTreeSet::from([Name::from_dotted("Fixture.leaf")]));
        std::mem::forget(expr);

        let mut level = Level::param("u");
        for _ in 0..8_192 {
            level = Level::succ(level);
        }
        names.clear();
        collect_names_from_level(&mut names, &level);
        assert_eq!(names, BTreeSet::from([Name::from_dotted("u")]));
        std::mem::forget(level);
    }

    #[test]
    fn reference_binding_table_records_each_origin_before_emission() {
        let local = Name::from_dotted("Fixture.local");
        let generated = Name::from_dotted("Fixture.local.mk");
        let imported = Name::from_dotted("Fixture.imported");
        let builtin = Name::from_dotted("Nat");
        let imported_hash = [0x51; 32];
        let builtin_hash = builtin_decl_interface_hash(&builtin).unwrap();
        let bindings = build_reference_bindings(
            &BTreeMap::from([(local.clone(), 2)]),
            &BTreeMap::from([(generated.clone(), 2)]),
            &BTreeMap::from([(
                imported.clone(),
                ImportedDeclInfo {
                    import_index: 1,
                    decl_interface_hash: imported_hash,
                    kind: ExportKind::Constructor,
                    axiom_dependencies: Vec::new(),
                },
            )]),
            &BTreeSet::from([builtin.clone()]),
        )
        .unwrap();

        assert_eq!(
            bindings.get(&local),
            Some(&ResolvedReferenceBinding::LocalDeclaration { decl_index: 2 })
        );
        assert_eq!(
            bindings.get(&generated),
            Some(&ResolvedReferenceBinding::LocalGenerated {
                owner_decl_index: 2,
                name: generated,
            })
        );
        assert_eq!(
            bindings.get(&imported),
            Some(&ResolvedReferenceBinding::ImportedExport {
                import_index: 1,
                name: imported,
                decl_interface_hash: imported_hash,
                export_kind: ExportKind::Constructor,
            })
        );
        assert_eq!(
            bindings.get(&builtin),
            Some(&ResolvedReferenceBinding::Builtin {
                name: builtin,
                decl_interface_hash: builtin_hash,
            })
        );
    }

    #[test]
    fn reference_binding_table_rejects_duplicate_local_and_generated_names() {
        let collision = Name::from_dotted("Fixture.collision");
        let error = build_reference_bindings(
            &BTreeMap::from([(collision.clone(), 0)]),
            &BTreeMap::from([(collision.clone(), 0)]),
            &BTreeMap::new(),
            &BTreeSet::new(),
        )
        .unwrap_err();

        assert_eq!(error, CertError::DuplicateName { name: collision });
    }
}

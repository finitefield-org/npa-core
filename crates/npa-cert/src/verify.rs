use std::collections::BTreeSet;

use npa_kernel::{
    expr::collect_apps, level::level_eq, level::levels_eq, Binder, ConstructorDecl, Env, Expr,
    InductiveDecl, Level, MutualInductiveBlock,
};

use crate::*;

pub(crate) fn verify_module_cert_impl(
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    let cert = decode_module_cert(bytes)?;
    let verified = verify_owned_module_cert_with_import_resolver(cert, bytes, policy, |cert| {
        resolve_imports(cert, session, policy)
    })?;
    session.insert_verified(verified.clone(), policy.mode);
    Ok(verified)
}

pub(crate) fn verify_module_cert_hashes_impl(bytes: &[u8]) -> Result<ModuleCert> {
    let cert = decode_module_cert(bytes)?;
    verify_canonical_encoding(&cert, bytes)?;
    verify_pre_import_checks(&cert)?;
    Ok(cert)
}

pub(crate) fn verify_decoded_module_cert_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    let verified = verify_decoded_module_cert_with_import_resolver(cert, bytes, policy, |cert| {
        resolve_imports(cert, session, policy)
    })?;
    session.insert_verified(verified.clone(), policy.mode);
    Ok(verified)
}

pub(crate) fn verify_module_cert_with_import_refs_impl(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    let cert = decode_module_cert(bytes)?;
    verify_owned_module_cert_with_import_resolver(cert, bytes, policy, |cert| {
        resolve_import_refs(cert, imports, policy)
    })
}

pub(crate) fn verify_decoded_module_cert_with_import_refs_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_resolver(cert, bytes, policy, |cert| {
        resolve_import_refs(cert, imports, policy)
    })
}

pub(crate) fn verify_built_module_cert_with_import_refs_impl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_after_encoding_check(cert, policy, |cert| {
        resolve_import_refs(cert, imports, policy)
    })
}

fn verify_decoded_module_cert_with_import_resolver<'a>(
    cert: &ModuleCert,
    bytes: &[u8],
    policy: &AxiomPolicy,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a VerifiedModule>>,
) -> Result<VerifiedModule> {
    verify_canonical_encoding(cert, bytes)?;
    verify_decoded_module_cert_after_encoding_check(cert, policy, resolve_imports)
}

fn verify_owned_module_cert_with_import_resolver<'a>(
    cert: ModuleCert,
    bytes: &[u8],
    policy: &AxiomPolicy,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a VerifiedModule>>,
) -> Result<VerifiedModule> {
    verify_canonical_encoding(&cert, bytes)?;
    verify_decoded_module_cert_checks(&cert, policy, resolve_imports)?;
    Ok(verified_module_from_owned_cert(cert))
}

fn verify_canonical_encoding(cert: &ModuleCert, bytes: &[u8]) -> Result<()> {
    let canonical = encode_module_cert_full_for_header(cert)?;
    if canonical != bytes {
        return Err(CertError::NonCanonicalEncoding {
            object: "ModuleCert",
        });
    }
    Ok(())
}

fn verify_decoded_module_cert_after_encoding_check<'a>(
    cert: &ModuleCert,
    policy: &AxiomPolicy,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a VerifiedModule>>,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_checks(cert, policy, resolve_imports)?;
    Ok(verified_module_from_cert(cert))
}

fn verify_decoded_module_cert_checks<'a>(
    cert: &ModuleCert,
    policy: &AxiomPolicy,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a VerifiedModule>>,
) -> Result<()> {
    verify_hash_and_table_checks(cert)?;
    enforce_core_feature_policy(&cert.axiom_report, policy)?;
    verify_declaration_order(cert)?;
    verify_inductive_generated_artifacts(cert)?;

    let imports = resolve_imports(cert)?;
    verify_dependencies_and_axioms(cert, &imports)?;
    enforce_axiom_policy(cert, policy)?;
    enforce_import_axiom_policy(&imports, policy)?;

    let mut env = Env::new();
    let builtin_refs = referenced_builtins_from_cert(cert)?;
    add_referenced_imports_to_env(&mut env, cert, &imports)?;
    add_referenced_builtins_to_env(&mut env, &builtin_refs)?;

    for decl in &cert.declarations {
        add_decl_to_env(&mut env, cert_decl_to_kernel_decl(cert, decl)?)?;
    }
    drop(env);

    Ok(())
}

fn verify_pre_import_checks(cert: &ModuleCert) -> Result<()> {
    verify_hash_and_table_checks(cert)?;
    verify_declaration_order(cert)?;
    verify_inductive_generated_artifacts(cert)?;
    Ok(())
}

fn verify_hash_and_table_checks(cert: &ModuleCert) -> Result<()> {
    verify_header(&cert.header)?;
    verify_tables(cert)?;
    verify_hashes(cert)?;
    Ok(())
}

fn verified_module_from_cert(cert: &ModuleCert) -> VerifiedModule {
    VerifiedModule {
        module: cert.header.module.clone(),
        imports: cert.imports.clone(),
        name_table: cert.name_table.clone(),
        level_table: cert.level_table.clone(),
        term_table: cert.term_table.clone(),
        declarations: cert.declarations.clone(),
        export_hash: cert.hashes.export_hash,
        certificate_hash: cert.hashes.certificate_hash,
        export_block: cert.export_block.clone(),
        axiom_report: cert.axiom_report.clone(),
    }
}

fn verified_module_from_owned_cert(cert: ModuleCert) -> VerifiedModule {
    let ModuleCert {
        header,
        imports,
        name_table,
        level_table,
        term_table,
        declarations,
        export_block,
        axiom_report,
        hashes,
    } = cert;
    VerifiedModule {
        module: header.module,
        imports,
        name_table,
        level_table,
        term_table,
        declarations,
        export_hash: hashes.export_hash,
        certificate_hash: hashes.certificate_hash,
        export_block,
        axiom_report,
    }
}
fn verify_header(header: &CertHeader) -> Result<()> {
    certificate_format_version(header).map(|_| ())
}

fn verify_tables(cert: &ModuleCert) -> Result<()> {
    if !cert.imports.windows(2).all(|pair| {
        (
            pair[0].module.clone(),
            pair[0].export_hash,
            pair[0].certificate_hash,
        ) < (
            pair[1].module.clone(),
            pair[1].export_hash,
            pair[1].certificate_hash,
        )
    }) {
        return Err(CertError::NonCanonicalEncoding { object: "Imports" });
    }
    if !cert.name_table.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(CertError::NonCanonicalEncoding {
            object: "NameTable",
        });
    }
    for (index, level) in cert.level_table.iter().enumerate() {
        let ok = match level {
            LevelNode::Zero | LevelNode::Param(_) => true,
            LevelNode::Succ(inner) => *inner < index,
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => *lhs < index && *rhs < index,
        };
        let name_ok = match level {
            LevelNode::Param(name) => *name < cert.name_table.len(),
            _ => true,
        };
        if !ok || !name_ok {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
        if !level_node_is_normalized(cert, index)? {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
    }
    let level_hashes = compute_level_hashes(&cert.level_table, &cert.name_table)?;
    let level_heights = level_node_heights(&cert.level_table)?;
    let mut previous_level_key = None;
    for (index, level) in cert.level_table.iter().enumerate() {
        let current_key = (
            level_heights[index],
            level_node_key(level, &level_hashes, &cert.name_table)?,
        );
        if let Some(previous_key) = &previous_level_key {
            if previous_key >= &current_key {
                return Err(CertError::NonCanonicalEncoding {
                    object: "LevelTable",
                });
            }
        }
        previous_level_key = Some(current_key);
    }

    for (index, term) in cert.term_table.iter().enumerate() {
        let ok = match term {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => true,
            TermNode::App(fun, arg) => *fun < index && *arg < index,
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => *ty < index && *body < index,
            TermNode::Let { ty, value, body } => *ty < index && *value < index && *body < index,
        };
        let refs_ok = match term {
            TermNode::Sort(level) => *level < cert.level_table.len(),
            TermNode::Const { global_ref, levels } => {
                global_ref_is_in_range(cert, global_ref)
                    && levels.iter().all(|level| *level < cert.level_table.len())
            }
            _ => true,
        };
        if !ok || !refs_ok {
            return Err(CertError::NonCanonicalEncoding {
                object: "TermTable",
            });
        }
    }
    let term_hashes = compute_term_hashes(&cert.term_table, &level_hashes)?;
    let term_heights = term_node_heights(&cert.term_table)?;
    let mut previous_term_key = None;
    for (index, term) in cert.term_table.iter().enumerate() {
        let current_key = (
            term_heights[index],
            term_node_key(term, &term_hashes, &level_hashes)?,
        );
        if let Some(previous_key) = &previous_term_key {
            if previous_key >= &current_key {
                return Err(CertError::NonCanonicalEncoding {
                    object: "TermTable",
                });
            }
        }
        previous_term_key = Some(current_key);
    }
    verify_decl_universe_contexts(cert)?;
    verify_reachable_tables_and_bvars(cert)?;
    verify_name_table_reachable(cert)?;
    Ok(())
}

fn verify_name_table_reachable(cert: &ModuleCert) -> Result<()> {
    let mut names = BTreeSet::new();
    names.insert(cert.header.module.clone());
    for import in &cert.imports {
        names.insert(import.module.clone());
    }

    for level in &cert.level_table {
        collect_level_node_names(cert, level, &mut names)?;
    }
    for term in &cert.term_table {
        collect_term_node_names(cert, term, &mut names)?;
    }
    for decl in &cert.declarations {
        collect_decl_payload_names(cert, &decl.decl, &mut names)?;
        collect_dependency_entry_names(cert, &decl.dependencies, &mut names)?;
        collect_axiom_ref_names(cert, &decl.axiom_dependencies, &mut names)?;
    }
    for entry in &cert.export_block {
        collect_name_id(cert, entry.name, &mut names)?;
        collect_name_ids(cert, &entry.universe_params, &mut names)?;
        collect_universe_constraint_names(cert, &entry.universe_constraints, &mut names)?;
        collect_axiom_ref_names(cert, &entry.axiom_dependencies, &mut names)?;
    }
    for report in &cert.axiom_report.per_declaration {
        collect_axiom_ref_names(cert, &report.direct_axioms, &mut names)?;
        collect_axiom_ref_names(cert, &report.transitive_axioms, &mut names)?;
    }
    collect_axiom_ref_names(cert, &cert.axiom_report.module_axioms, &mut names)?;

    let expected = names.into_iter().collect::<Vec<_>>();
    if expected != cert.name_table {
        return Err(CertError::NonCanonicalEncoding {
            object: "NameTable",
        });
    }
    Ok(())
}

fn verify_decl_universe_contexts(cert: &ModuleCert) -> Result<()> {
    for decl in &cert.declarations {
        let params = decl_universe_params(&decl.decl);
        let constraints = decl_universe_constraints(&decl.decl);
        if decl_has_empty_constrained_universe_payload(&decl.decl) {
            return Err(CertError::NonCanonicalEncoding {
                object: "UniverseConstraints",
            });
        }
        let param_names = universe_names(cert, params)?;
        let delta =
            npa_kernel::level::validate_universe_params(&param_names).map_err(CertError::Kernel)?;
        let kernel_constraints = constraints
            .iter()
            .map(|constraint| {
                Ok(npa_kernel::UniverseConstraint {
                    lhs: level_from_node(cert, constraint.lhs)?,
                    relation: constraint.relation,
                    rhs: level_from_node(cert, constraint.rhs)?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        npa_kernel::level::ensure_universe_constraints_wf(&delta, &kernel_constraints)
            .map_err(CertError::Kernel)?;
    }
    Ok(())
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

fn collect_level_node_names(
    cert: &ModuleCert,
    level: &LevelNode,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    if let LevelNode::Param(name) = level {
        collect_name_id(cert, *name, names)?;
    }
    Ok(())
}

fn collect_term_node_names(
    cert: &ModuleCert,
    term: &TermNode,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    if let TermNode::Const { global_ref, .. } = term {
        collect_global_ref_names(cert, global_ref, names)?;
    }
    Ok(())
}

fn collect_decl_payload_names(
    cert: &ModuleCert,
    decl: &DeclPayload,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ..
        }
        | DeclPayload::AxiomConstrained {
            name,
            universe_params,
            ..
        }
        | DeclPayload::Def {
            name,
            universe_params,
            ..
        }
        | DeclPayload::DefConstrained {
            name,
            universe_params,
            ..
        }
        | DeclPayload::Theorem {
            name,
            universe_params,
            ..
        }
        | DeclPayload::TheoremConstrained {
            name,
            universe_params,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
        }
        DeclPayload::Inductive {
            name,
            universe_params,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            name,
            universe_params,
            constructors,
            recursor,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
            for constructor in constructors {
                collect_name_id(cert, constructor.name, names)?;
            }
            if let Some(recursor) = recursor {
                collect_name_id(cert, recursor.name, names)?;
                collect_name_ids(cert, &recursor.universe_params, names)?;
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            inductives,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
            for inductive in inductives {
                collect_name_id(cert, inductive.name, names)?;
                for constructor in &inductive.constructors {
                    collect_name_id(cert, constructor.name, names)?;
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_name_id(cert, recursor.name, names)?;
                    collect_name_ids(cert, &recursor.universe_params, names)?;
                }
            }
        }
    }
    Ok(())
}

fn collect_dependency_entry_names(
    cert: &ModuleCert,
    dependencies: &[DependencyEntry],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for dependency in dependencies {
        collect_global_ref_names(cert, &dependency.global_ref, names)?;
    }
    Ok(())
}

fn collect_axiom_ref_names(
    cert: &ModuleCert,
    axioms: &[AxiomRef],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for axiom in axioms {
        collect_global_ref_names(cert, &axiom.global_ref, names)?;
        collect_name_id(cert, axiom.name, names)?;
    }
    Ok(())
}

fn collect_global_ref_names(
    cert: &ModuleCert,
    global_ref: &GlobalRef,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    match global_ref {
        GlobalRef::Builtin { name, .. }
        | GlobalRef::Imported { name, .. }
        | GlobalRef::LocalGenerated { name, .. } => {
            collect_name_id(cert, *name, names)?;
        }
        GlobalRef::Local { .. } => {}
    }
    Ok(())
}

fn collect_name_ids(cert: &ModuleCert, ids: &[NameId], names: &mut BTreeSet<Name>) -> Result<()> {
    for id in ids {
        collect_name_id(cert, *id, names)?;
    }
    Ok(())
}

fn collect_universe_constraint_names(
    cert: &ModuleCert,
    constraints: &[UniverseConstraintSpec],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for constraint in constraints {
        collect_level_names_from_level_id(cert, constraint.lhs, names)?;
        collect_level_names_from_level_id(cert, constraint.rhs, names)?;
    }
    Ok(())
}

fn collect_level_names_from_level_id(
    cert: &ModuleCert,
    level: LevelId,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    match cert.level_table.get(level).ok_or(CertError::DecodeError)? {
        LevelNode::Zero => {}
        LevelNode::Succ(inner) => collect_level_names_from_level_id(cert, *inner, names)?,
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            collect_level_names_from_level_id(cert, *lhs, names)?;
            collect_level_names_from_level_id(cert, *rhs, names)?;
        }
        LevelNode::Param(name) => collect_name_id(cert, *name, names)?,
    }
    Ok(())
}

fn collect_name_id(cert: &ModuleCert, id: NameId, names: &mut BTreeSet<Name>) -> Result<()> {
    names.insert(
        cert.name_table
            .get(id)
            .cloned()
            .ok_or(CertError::DecodeError)?,
    );
    Ok(())
}

fn verify_reachable_tables_and_bvars(cert: &ModuleCert) -> Result<()> {
    // Child indices precede parent indices in the term table (verified by the
    // table encoding pass before this function runs), so one forward pass
    // yields every node's loose-bvar upper bound, and per-root verification
    // is an O(1) bound check plus a single-visit reachability walk — the old
    // per-(term, depth) depth-first search re-visited shared subtrees once
    // per distinct depth. The rare failing root replays the original search
    // so the reported error is identical.
    let bounds = term_node_loose_bvar_bounds(&cert.term_table)?;
    let mut reachable_terms = vec![false; cert.term_table.len()];

    let mut verify_root = |root: TermId| -> Result<()> {
        if root >= cert.term_table.len() {
            return Err(CertError::DecodeError);
        }
        if bounds[root] > 0 {
            // Cold path: a loose bvar escapes this root. Replay the
            // depth-tracking search to surface the same first error.
            let mut seen_term_depths = BTreeSet::new();
            let mut reachable = BTreeSet::new();
            verify_term_scope(cert, root, 0, &mut seen_term_depths, &mut reachable)?;
        }
        mark_term_reachable(&cert.term_table, root, &mut reachable_terms);
        Ok(())
    };

    for decl in &cert.declarations {
        match &decl.decl {
            DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
                verify_root(*ty)?;
            }
            DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
                verify_root(*ty)?;
                verify_root(*value)?;
            }
            DeclPayload::Theorem { ty, proof, .. }
            | DeclPayload::TheoremConstrained { ty, proof, .. } => {
                verify_root(*ty)?;
                verify_root(*proof)?;
            }
            DeclPayload::Inductive {
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            } => {
                let ty = inductive_export_type_term_id(&cert.term_table, params, indices, *sort)?;
                verify_root(ty)?;
                for constructor in constructors {
                    verify_root(constructor.ty)?;
                }
                if let Some(recursor) = recursor {
                    verify_root(recursor.ty)?;
                }
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    let ty = inductive_export_type_term_id(
                        &cert.term_table,
                        &inductive.params,
                        &inductive.indices,
                        inductive.sort,
                    )?;
                    verify_root(ty)?;
                    for constructor in &inductive.constructors {
                        verify_root(constructor.ty)?;
                    }
                    if let Some(recursor) = &inductive.recursor {
                        verify_root(recursor.ty)?;
                    }
                }
            }
        }
    }

    if reachable_terms.iter().filter(|seen| **seen).count() != cert.term_table.len() {
        return Err(CertError::NonCanonicalEncoding {
            object: "TermTable",
        });
    }

    // Every term node is reachable past this point, so level reachability
    // can scan the term table directly.
    let mut reachable_levels = vec![false; cert.level_table.len()];
    for term in &cert.term_table {
        match term {
            TermNode::Sort(level) => collect_level_reachable(cert, *level, &mut reachable_levels)?,
            TermNode::Const { levels, .. } => {
                for level in levels {
                    collect_level_reachable(cert, *level, &mut reachable_levels)?;
                }
            }
            TermNode::BVar(_)
            | TermNode::App(_, _)
            | TermNode::Lam { .. }
            | TermNode::Pi { .. }
            | TermNode::Let { .. } => {}
        }
    }
    for decl in &cert.declarations {
        for constraint in decl_universe_constraints(&decl.decl) {
            collect_level_reachable(cert, constraint.lhs, &mut reachable_levels)?;
            collect_level_reachable(cert, constraint.rhs, &mut reachable_levels)?;
        }
    }
    for entry in &cert.export_block {
        for constraint in &entry.universe_constraints {
            collect_level_reachable(cert, constraint.lhs, &mut reachable_levels)?;
            collect_level_reachable(cert, constraint.rhs, &mut reachable_levels)?;
        }
    }
    if reachable_levels.iter().filter(|seen| **seen).count() != cert.level_table.len() {
        return Err(CertError::NonCanonicalEncoding {
            object: "LevelTable",
        });
    }

    Ok(())
}

/// Loose-bvar upper bound per table node in one forward pass; children
/// always precede parents in the canonical table, which the encoding pass
/// has verified before this is called.
fn term_node_loose_bvar_bounds(terms: &[TermNode]) -> Result<Vec<u32>> {
    fn child(bounds: &[u32], index: usize) -> Result<u32> {
        bounds.get(index).copied().ok_or(CertError::DecodeError)
    }
    let mut bounds = Vec::with_capacity(terms.len());
    for term in terms {
        let bound = match term {
            TermNode::Sort(_) | TermNode::Const { .. } => 0,
            TermNode::BVar(index) => index.saturating_add(1),
            TermNode::App(fun, arg) => child(&bounds, *fun)?.max(child(&bounds, *arg)?),
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                child(&bounds, *ty)?.max(child(&bounds, *body)?.saturating_sub(1))
            }
            TermNode::Let { ty, value, body } => child(&bounds, *ty)?
                .max(child(&bounds, *value)?)
                .max(child(&bounds, *body)?.saturating_sub(1)),
        };
        bounds.push(bound);
    }
    Ok(bounds)
}

fn mark_term_reachable(terms: &[TermNode], root: TermId, reachable: &mut [bool]) {
    if reachable[root] {
        return;
    }
    reachable[root] = true;
    match &terms[root] {
        TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
        TermNode::App(fun, arg) => {
            mark_term_reachable(terms, *fun, reachable);
            mark_term_reachable(terms, *arg, reachable);
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            mark_term_reachable(terms, *ty, reachable);
            mark_term_reachable(terms, *body, reachable);
        }
        TermNode::Let { ty, value, body } => {
            mark_term_reachable(terms, *ty, reachable);
            mark_term_reachable(terms, *value, reachable);
            mark_term_reachable(terms, *body, reachable);
        }
    }
}

fn verify_term_scope(
    cert: &ModuleCert,
    term: TermId,
    depth: u32,
    seen: &mut BTreeSet<(TermId, u32)>,
    reachable_terms: &mut BTreeSet<TermId>,
) -> Result<()> {
    if !seen.insert((term, depth)) {
        reachable_terms.insert(term);
        return Ok(());
    }
    reachable_terms.insert(term);
    match cert.term_table.get(term).ok_or(CertError::DecodeError)? {
        TermNode::Sort(_) | TermNode::Const { .. } => {}
        TermNode::BVar(index) => {
            if *index >= depth {
                return Err(CertError::InvalidBVar { index: *index });
            }
        }
        TermNode::App(fun, arg) => {
            verify_term_scope(cert, *fun, depth, seen, reachable_terms)?;
            verify_term_scope(cert, *arg, depth, seen, reachable_terms)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            verify_term_scope(cert, *ty, depth, seen, reachable_terms)?;
            verify_term_scope(cert, *body, depth + 1, seen, reachable_terms)?;
        }
        TermNode::Let { ty, value, body } => {
            verify_term_scope(cert, *ty, depth, seen, reachable_terms)?;
            verify_term_scope(cert, *value, depth, seen, reachable_terms)?;
            verify_term_scope(cert, *body, depth + 1, seen, reachable_terms)?;
        }
    }
    Ok(())
}

fn collect_level_reachable(
    cert: &ModuleCert,
    level: LevelId,
    reachable_levels: &mut [bool],
) -> Result<()> {
    let node = cert.level_table.get(level).ok_or(CertError::DecodeError)?;
    if reachable_levels[level] {
        return Ok(());
    }
    reachable_levels[level] = true;
    match node {
        LevelNode::Zero | LevelNode::Param(_) => {}
        LevelNode::Succ(inner) => collect_level_reachable(cert, *inner, reachable_levels)?,
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            collect_level_reachable(cert, *lhs, reachable_levels)?;
            collect_level_reachable(cert, *rhs, reachable_levels)?;
        }
    }
    Ok(())
}

fn verify_hashes(cert: &ModuleCert) -> Result<()> {
    let level_hashes = compute_level_hashes(&cert.level_table, &cert.name_table)?;
    let term_hashes = compute_term_hashes(&cert.term_table, &level_hashes)?;
    for decl in &cert.declarations {
        let expected = compute_decl_hashes(
            &decl.decl,
            &decl.dependencies,
            &decl.axiom_dependencies,
            &cert.term_table,
            &level_hashes,
            &term_hashes,
            &cert.name_table,
        )?;
        if expected.decl_interface_hash != decl.hashes.decl_interface_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclInterface,
                expected: decl.hashes.decl_interface_hash,
                actual: expected.decl_interface_hash,
            });
        }
        if expected.decl_certificate_hash != decl.hashes.decl_certificate_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclCertificate,
                expected: decl.hashes.decl_certificate_hash,
                actual: expected.decl_certificate_hash,
            });
        }
    }

    let expected_export_block =
        build_export_block(&cert.declarations, &cert.term_table, &term_hashes)?;
    let version = certificate_format_version(&cert.header)?;
    verify_export_format_compatibility(cert, &expected_export_block, version)?;
    let (export_domain, export_bytes, cert_domain, cert_bytes) = match version {
        CertificateFormatVersion::Current => (
            MODULE_EXPORT_DOMAIN,
            encode_export_block(&expected_export_block),
            MODULE_CERT_DOMAIN,
            encode_module_cert_without_certificate_hash(cert),
        ),
        CertificateFormatVersion::Previous => (
            PREVIOUS_MODULE_EXPORT_DOMAIN,
            encode_export_block_previous(&expected_export_block),
            PREVIOUS_MODULE_CERT_DOMAIN,
            encode_module_cert_without_certificate_hash_for_header(cert)?,
        ),
        CertificateFormatVersion::Legacy => (
            LEGACY_MODULE_EXPORT_DOMAIN,
            encode_export_block_legacy(&expected_export_block),
            LEGACY_MODULE_CERT_DOMAIN,
            encode_module_cert_without_certificate_hash_for_header(cert)?,
        ),
    };
    let expected_export = hash_with_domain(export_domain, &export_bytes);
    if expected_export_block != cert.export_block || expected_export != cert.hashes.export_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::ExportBlock,
            expected: cert.hashes.export_hash,
            actual: expected_export,
        });
    }

    let expected_axioms = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(&cert.axiom_report),
    );
    if expected_axioms != cert.hashes.axiom_report_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::AxiomReport,
            expected: cert.hashes.axiom_report_hash,
            actual: expected_axioms,
        });
    }

    let expected_cert = hash_with_domain(cert_domain, &cert_bytes);
    if expected_cert != cert.hashes.certificate_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected: cert.hashes.certificate_hash,
            actual: expected_cert,
        });
    }

    Ok(())
}

fn verify_export_format_compatibility(
    cert: &ModuleCert,
    expected_export_block: &ExportBlock,
    version: CertificateFormatVersion,
) -> Result<()> {
    if version == CertificateFormatVersion::Legacy {
        if let Some(entry) = expected_export_block
            .iter()
            .find(|entry| !entry.universe_constraints.is_empty())
        {
            return Err(CertError::ConstrainedExportRequiresFormatUpgrade {
                name: cert
                    .name_table
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            });
        }
    }
    Ok(())
}

fn verify_declaration_order(cert: &ModuleCert) -> Result<()> {
    let local_names = (0..cert.declarations.len())
        .map(|index| decl_name_as_name(cert, index))
        .collect::<Result<Vec<_>>>()?;
    ensure_unique_names(&local_names)?;
    for name in &local_names {
        if reserved_core_primitive_name(name) {
            return Err(CertError::ReservedCorePrimitive { name: name.clone() });
        }
    }

    let dependencies = cert
        .declarations
        .iter()
        .enumerate()
        .map(|(decl_index, decl)| {
            let mut deps = BTreeSet::new();
            for dependency in &decl.dependencies {
                match &dependency.global_ref {
                    GlobalRef::Local {
                        decl_index: dependency_index,
                    } => {
                        if *dependency_index >= decl_index {
                            return Err(CertError::DependencyCycle {
                                name: local_names[decl_index].clone(),
                            });
                        }
                        deps.insert(*dependency_index);
                    }
                    GlobalRef::LocalGenerated {
                        decl_index: dependency_index,
                        name,
                    } => {
                        if *dependency_index >= decl_index {
                            return Err(CertError::DependencyCycle {
                                name: local_names[decl_index].clone(),
                            });
                        }
                        if !local_generated_entry_exists(cert, *dependency_index, *name)? {
                            return Err(CertError::UnknownDependency {
                                name: cert
                                    .name_table
                                    .get(*name)
                                    .cloned()
                                    .ok_or(CertError::DecodeError)?,
                            });
                        }
                        deps.insert(*dependency_index);
                    }
                    GlobalRef::Builtin { .. } | GlobalRef::Imported { .. } => {}
                }
            }
            Ok(deps)
        })
        .collect::<Result<Vec<_>>>()?;

    let mut emitted = BTreeSet::new();
    let mut remaining: BTreeSet<_> = (0..cert.declarations.len()).collect();
    let mut expected = Vec::with_capacity(cert.declarations.len());
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
            expected.push(index);
        }
    }

    if expected != (0..cert.declarations.len()).collect::<Vec<_>>() {
        return Err(CertError::NonCanonicalEncoding {
            object: "Declarations",
        });
    }

    Ok(())
}

fn global_ref_is_in_range(cert: &ModuleCert, global_ref: &GlobalRef) -> bool {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => cert
            .name_table
            .get(*name)
            .is_some_and(|name| builtin_decl_interface_hash(name) == Some(*decl_interface_hash)),
        GlobalRef::Imported {
            import_index, name, ..
        } => *import_index < cert.imports.len() && *name < cert.name_table.len(),
        GlobalRef::Local { decl_index } => *decl_index < cert.declarations.len(),
        GlobalRef::LocalGenerated { decl_index, name } => {
            *decl_index < cert.declarations.len() && *name < cert.name_table.len()
        }
    }
}

fn level_node_is_normalized(cert: &ModuleCert, index: usize) -> Result<bool> {
    let raw = raw_level_from_node(cert, index)?;
    Ok(npa_kernel::level::normalize_level(raw.clone()) == raw)
}

fn raw_level_from_node(cert: &ModuleCert, index: usize) -> Result<Level> {
    Ok(
        match cert.level_table.get(index).ok_or(CertError::DecodeError)? {
            LevelNode::Zero => Level::Zero,
            LevelNode::Succ(inner) => Level::Succ(Box::new(raw_level_from_node(cert, *inner)?)),
            LevelNode::Max(lhs, rhs) => Level::Max(
                Box::new(raw_level_from_node(cert, *lhs)?),
                Box::new(raw_level_from_node(cert, *rhs)?),
            ),
            LevelNode::IMax(lhs, rhs) => Level::IMax(
                Box::new(raw_level_from_node(cert, *lhs)?),
                Box::new(raw_level_from_node(cert, *rhs)?),
            ),
            LevelNode::Param(name) => Level::Param(
                cert.name_table
                    .get(*name)
                    .ok_or(CertError::DecodeError)?
                    .as_dotted(),
            ),
        },
    )
}

/// Computes every level node's height in one forward pass. Children always
/// precede their parents in a canonically encoded table (verified by the
/// caller before the heights are needed), so each height is derived from
/// already-computed child heights.
fn level_node_heights(levels: &[LevelNode]) -> Result<Vec<usize>> {
    fn child(heights: &[usize], index: usize) -> Result<usize> {
        heights.get(index).copied().ok_or(CertError::DecodeError)
    }
    let mut heights = Vec::with_capacity(levels.len());
    for level in levels {
        let height = match level {
            LevelNode::Zero | LevelNode::Param(_) => 0,
            LevelNode::Succ(inner) => child(&heights, *inner)? + 1,
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                child(&heights, *lhs)?.max(child(&heights, *rhs)?) + 1
            }
        };
        heights.push(height);
    }
    Ok(heights)
}

/// Computes every term node's height in one forward pass; same
/// child-precedes-parent reasoning as [`level_node_heights`].
fn term_node_heights(terms: &[TermNode]) -> Result<Vec<usize>> {
    fn child(heights: &[usize], index: usize) -> Result<usize> {
        heights.get(index).copied().ok_or(CertError::DecodeError)
    }
    let mut heights = Vec::with_capacity(terms.len());
    for term in terms {
        let height = match term {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
            TermNode::App(fun, arg) => child(&heights, *fun)?.max(child(&heights, *arg)?) + 1,
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                child(&heights, *ty)?.max(child(&heights, *body)?) + 1
            }
            TermNode::Let { ty, value, body } => {
                child(&heights, *ty)?
                    .max(child(&heights, *value)?)
                    .max(child(&heights, *body)?)
                    + 1
            }
        };
        heights.push(height);
    }
    Ok(heights)
}

fn resolve_imports<'a>(
    cert: &ModuleCert,
    session: &'a VerifierSession,
    policy: &AxiomPolicy,
) -> Result<Vec<&'a VerifiedModule>> {
    let mut imports = Vec::new();
    for entry in &cert.imports {
        if policy.mode == TrustMode::HighTrust && entry.certificate_hash.is_none() {
            return Err(CertError::MissingImportCertificateHash {
                module: entry.module.clone(),
            });
        }
        imports.push(session.find_import(entry, policy.mode)?);
    }
    Ok(imports)
}

fn resolve_import_refs<'a>(
    cert: &ModuleCert,
    available_imports: &'a [&'a VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<Vec<&'a VerifiedModule>> {
    let mut imports = Vec::new();
    for entry in &cert.imports {
        if policy.mode == TrustMode::HighTrust && entry.certificate_hash.is_none() {
            return Err(CertError::MissingImportCertificateHash {
                module: entry.module.clone(),
            });
        }
        imports.push(find_import_ref(available_imports, entry, policy.mode)?);
    }
    Ok(imports)
}

fn find_import_ref<'a>(
    available_imports: &'a [&'a VerifiedModule],
    entry: &ImportEntry,
    mode: TrustMode,
) -> Result<&'a VerifiedModule> {
    let module_export_matches = available_imports
        .iter()
        .any(|module| module.module == entry.module && module.export_hash == entry.export_hash);

    let found = available_imports.iter().copied().find(|module| {
        module.module == entry.module
            && module.export_hash == entry.export_hash
            && match (mode, entry.certificate_hash) {
                (TrustMode::Normal, None) => true,
                (_, Some(hash)) => module.certificate_hash == hash,
                (TrustMode::HighTrust, None) => false,
            }
    });

    if let Some(module) = found {
        return Ok(module);
    }

    if mode == TrustMode::HighTrust && !module_export_matches {
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

fn add_referenced_imports_to_env(
    env: &mut Env,
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut refs = BTreeSet::new();
    for decl in &cert.declarations {
        for dependency in &decl.dependencies {
            refs.insert(dependency.global_ref.clone());
        }
    }
    for global_ref in refs {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => add_builtin_ref_to_env(env, &cert.name_table, name, decl_interface_hash)?,
            GlobalRef::Imported { .. } => {
                loader.load_imported_global_ref_from_cert(env, cert, &global_ref)?;
            }
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {}
        }
    }
    Ok(())
}

pub(crate) fn add_verified_module_referenced_imports_to_env(
    env: &mut Env,
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut refs = BTreeSet::new();
    for decl in &module.declarations {
        for dependency in &decl.dependencies {
            refs.insert(dependency.global_ref.clone());
        }
    }
    for global_ref in refs {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => add_builtin_ref_to_env(env, &module.name_table, name, decl_interface_hash)?,
            GlobalRef::Imported { .. } => {
                loader.load_imported_global_ref_from_module(env, module, &global_ref)?;
            }
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {}
        }
    }
    Ok(())
}

pub(crate) fn add_selected_import_exports_to_env(
    env: &mut Env,
    imports: &[&VerifiedModule],
    exports: &[(usize, Name, Hash)],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut exports = exports.to_vec();
    exports.sort();
    exports.dedup();
    for (import_index, name, decl_interface_hash) in exports {
        let module = imports
            .get(import_index)
            .copied()
            .ok_or(CertError::DecodeError)?;
        let entry = imported_export_entry_by_name(module, &name, decl_interface_hash)?;
        loader.load_module_export_entry(env, module, entry)?;
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportedDeclKey {
    module: Name,
    certificate_hash: Hash,
    decl_index: usize,
}

struct ReferencedImportLoader<'a> {
    imports: &'a [&'a VerifiedModule],
    loaded: BTreeSet<ImportedDeclKey>,
    loading: BTreeSet<ImportedDeclKey>,
}

impl<'a> ReferencedImportLoader<'a> {
    fn load_imported_global_ref_from_cert(
        &mut self,
        env: &mut Env,
        cert: &ModuleCert,
        global_ref: &GlobalRef,
    ) -> Result<()> {
        let GlobalRef::Imported { import_index, .. } = global_ref else {
            return Err(CertError::DecodeError);
        };
        let module = self
            .imports
            .get(*import_index)
            .copied()
            .ok_or(CertError::DecodeError)?;
        let entry = imported_export_entry_for_global_ref(cert, self.imports, global_ref)?;
        self.load_module_export_entry(env, module, entry)
    }

    fn load_imported_global_ref_from_module(
        &mut self,
        env: &mut Env,
        module: &'a VerifiedModule,
        global_ref: &GlobalRef,
    ) -> Result<()> {
        let GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } = global_ref
        else {
            return Err(CertError::DecodeError);
        };
        let import_entry = module
            .imports
            .get(*import_index)
            .ok_or(CertError::DecodeError)?;
        let imported = self.find_available_import(import_entry)?;
        let wanted_name = module.name_table.get(*name).ok_or(CertError::DecodeError)?;
        let entry = imported_export_entry_by_name(imported, wanted_name, *decl_interface_hash)?;
        self.load_module_export_entry(env, imported, entry)
    }

    fn load_module_export_entry(
        &mut self,
        env: &mut Env,
        module: &'a VerifiedModule,
        entry: &ExportEntry,
    ) -> Result<()> {
        let decl_index = source_decl_index_for_export_entry(module, entry)?;
        self.load_module_decl_for_export(env, module, decl_index, entry)
    }

    fn load_module_decl_for_export(
        &mut self,
        env: &mut Env,
        module: &'a VerifiedModule,
        decl_index: usize,
        entry: &ExportEntry,
    ) -> Result<()> {
        let key = ImportedDeclKey {
            module: module.module.clone(),
            certificate_hash: module.certificate_hash,
            decl_index,
        };
        if self.loaded.contains(&key) {
            return Ok(());
        }
        if !self.loading.insert(key.clone()) {
            return Err(CertError::DependencyCycle {
                name: module
                    .name_table
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            });
        }

        let mut refs = BTreeSet::new();
        collect_imported_kernel_refs_for_export(module, entry, &mut refs)?;
        for global_ref in refs {
            match global_ref {
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => add_builtin_ref_to_env(env, &module.name_table, name, decl_interface_hash)?,
                GlobalRef::Imported { .. } => {
                    self.load_imported_global_ref_from_module(env, module, &global_ref)?;
                }
                GlobalRef::Local { decl_index } => {
                    let local_entry = export_entry_for_local_decl(module, decl_index)?;
                    self.load_module_export_entry(env, module, local_entry)?;
                }
                GlobalRef::LocalGenerated {
                    decl_index, name, ..
                } => {
                    let local_entry =
                        export_entry_for_local_generated_decl(module, decl_index, name)?;
                    self.load_module_export_entry(env, module, local_entry)?;
                }
            }
        }

        let decl = verified_module_export_entry_to_kernel_decl(module, entry)?;
        let decl_name = decl.name().to_owned();
        let is_builtin_decl = builtin_decl_interface_hash(&Name::from_dotted(&decl_name)).is_some();
        if env.decl(&decl_name).is_none() || !is_builtin_decl {
            add_decl_to_env(env, decl)?;
        }
        self.loading.remove(&key);
        self.loaded.insert(key);
        Ok(())
    }

    fn find_available_import(&self, entry: &ImportEntry) -> Result<&'a VerifiedModule> {
        find_import_ref(self.imports, entry, TrustMode::Normal)
    }
}

fn add_builtin_ref_to_env(
    env: &mut Env,
    name_table: &[Name],
    name: NameId,
    decl_interface_hash: Hash,
) -> Result<()> {
    let name_value = name_table.get(name).ok_or(CertError::DecodeError)?;
    if builtin_decl_interface_hash(name_value) != Some(decl_interface_hash) {
        return Err(CertError::UnknownDependency {
            name: name_value.clone(),
        });
    }
    add_referenced_builtins_to_env(env, &BTreeSet::from([name_value.clone()]))
}

fn imported_export_entry_by_name<'a>(
    module: &'a VerifiedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<&'a ExportEntry> {
    module
        .export_block
        .iter()
        .find(|entry| {
            entry.decl_interface_hash == decl_interface_hash
                && module
                    .name_table
                    .get(entry.name)
                    .is_some_and(|candidate| candidate == name)
        })
        .ok_or_else(|| CertError::ImportHashMismatch {
            module: module.module.clone(),
        })
}

fn export_entry_for_local_decl(module: &VerifiedModule, decl_index: usize) -> Result<&ExportEntry> {
    let decl = module
        .declarations
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    let name = decl_primary_name(&decl.decl);
    module
        .export_block
        .iter()
        .find(|entry| {
            entry.name == name && entry.decl_interface_hash == decl.hashes.decl_interface_hash
        })
        .ok_or(CertError::DecodeError)
}

fn export_entry_for_local_generated_decl(
    module: &VerifiedModule,
    decl_index: usize,
    name: NameId,
) -> Result<&ExportEntry> {
    let decl = module
        .declarations
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    module
        .export_block
        .iter()
        .find(|entry| {
            entry.name == name && entry.decl_interface_hash == decl.hashes.decl_interface_hash
        })
        .ok_or(CertError::DecodeError)
}

fn decl_primary_name(decl: &DeclPayload) -> NameId {
    match decl {
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

fn collect_imported_kernel_refs_for_export(
    module: &VerifiedModule,
    entry: &ExportEntry,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    match entry.kind {
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)?;
            let decl = module
                .declarations
                .get(decl_index)
                .ok_or(CertError::DecodeError)?;
            for term in decl_term_ids(&decl.decl) {
                collect_global_refs_from_verified_term(module, term, refs)?;
            }
            refs.retain(|global_ref| {
                !matches!(
                    global_ref,
                    GlobalRef::Local {
                        decl_index: local_decl_index
                    } | GlobalRef::LocalGenerated {
                        decl_index: local_decl_index,
                        ..
                    } if *local_decl_index == decl_index
                )
            });
        }
        ExportKind::Axiom | ExportKind::Theorem | ExportKind::Def => {
            collect_global_refs_from_verified_term(module, entry.ty, refs)?;
            if let Some(body) = entry.body {
                collect_global_refs_from_verified_term(module, body, refs)?;
            }
        }
    }
    Ok(())
}

fn collect_global_refs_from_verified_term(
    module: &VerifiedModule,
    term: TermId,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    collect_global_refs_from_term_table(&module.term_table, term, refs)
}

#[allow(dead_code)]
pub(crate) fn add_imports_to_env(env: &mut Env, imports: &[&VerifiedModule]) -> Result<()> {
    let ordered = import_kernel_order(imports)?;
    let mut referenced_builtins = BTreeSet::new();
    for import in &ordered {
        referenced_builtins.extend(verified_module_referenced_builtin_names(import)?);
    }
    let imports_export_eq = verified_modules_export_builtin_eq(&ordered)?;
    let imports_export_eq_rec = verified_modules_export_builtin_eq_rec(&ordered)?;
    let mut loaded_imports = vec![false; ordered.len()];
    if imports_export_eq {
        for (index, import) in ordered.iter().enumerate() {
            if verified_module_exports_builtin_eq(import)? {
                for decl in verified_module_to_kernel_decls(import)? {
                    add_decl_to_env(env, decl)?;
                }
                loaded_imports[index] = true;
            }
        }
    }
    let mut pre_import_builtins = referenced_builtins.clone();
    if imports_export_eq {
        pre_import_builtins
            .retain(|name| !matches!(name.as_dotted().as_str(), "Eq" | "Eq.refl" | "Eq.rec"));
    }
    add_referenced_builtins_to_env(env, &pre_import_builtins)?;
    let needs_builtin_eq_rec = referenced_builtins
        .iter()
        .any(|name| name.as_dotted() == "Eq.rec");
    if (imports_export_eq_rec || needs_builtin_eq_rec) && env.decl("Eq.rec").is_none() {
        let referenced = BTreeSet::from([Name::from_dotted("Eq"), Name::from_dotted("Eq.rec")]);
        add_referenced_builtins_to_env(env, &referenced)?;
    }
    for (index, import) in ordered.into_iter().enumerate() {
        if loaded_imports[index] {
            continue;
        }
        for decl in verified_module_to_kernel_decls(import)? {
            add_decl_to_env(env, decl)?;
        }
    }
    Ok(())
}

fn verified_modules_export_builtin_eq(imports: &[&VerifiedModule]) -> Result<bool> {
    for import in imports {
        if verified_module_exports_builtin_eq(import)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verified_module_exports_builtin_eq(import: &VerifiedModule) -> Result<bool> {
    for entry in &import.export_block {
        let Some(entry_name) = import.name_table.get(entry.name) else {
            return Err(CertError::DecodeError);
        };
        // `Eq` is globally named in the kernel environment. If an import provides it,
        // load that declaration before adding builtins that depend on it.
        if entry.kind == ExportKind::Inductive && entry_name.as_dotted() == "Eq" {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verified_modules_export_builtin_eq_rec(imports: &[&VerifiedModule]) -> Result<bool> {
    for import in imports {
        for entry in &import.export_block {
            if verified_module_export_uses_builtin_eq_rec(import, entry)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn verified_module_export_uses_builtin_eq_rec(
    import: &VerifiedModule,
    entry: &ExportEntry,
) -> Result<bool> {
    let Some(entry_name) = import.name_table.get(entry.name) else {
        return Err(CertError::DecodeError);
    };
    if entry_name.as_dotted() != "Eq.rec" {
        return Ok(false);
    }
    for candidate in &import.export_block {
        let Some(candidate_name) = import.name_table.get(candidate.name) else {
            return Err(CertError::DecodeError);
        };
        if candidate.kind == ExportKind::Inductive && candidate_name.as_dotted() == "Eq" {
            return Ok(true);
        }
    }
    Ok(false)
}

fn import_kernel_order<'a>(imports: &[&'a VerifiedModule]) -> Result<Vec<&'a VerifiedModule>> {
    let mut added = vec![false; imports.len()];
    let mut order = Vec::with_capacity(imports.len());

    while order.len() < imports.len() {
        let mut progressed = false;
        for (index, import) in imports.iter().enumerate() {
            if added[index] || !import_dependencies_satisfied(import, imports, &added)? {
                continue;
            }
            added[index] = true;
            order.push(*import);
            progressed = true;
        }

        if !progressed {
            let name = imports
                .iter()
                .enumerate()
                .find_map(|(index, import)| (!added[index]).then(|| import.module.clone()))
                .ok_or(CertError::DecodeError)?;
            return Err(CertError::DependencyCycle { name });
        }
    }

    Ok(order)
}

fn import_dependencies_satisfied(
    import: &VerifiedModule,
    imports: &[&VerifiedModule],
    added: &[bool],
) -> Result<bool> {
    for (dep_name, decl_interface_hash) in imported_dependency_targets(import)? {
        let mut found = false;
        let mut satisfied = false;
        for (index, candidate) in imports.iter().enumerate() {
            if module_exports_dependency(candidate, &dep_name, decl_interface_hash)? {
                found = true;
                satisfied |= added[index];
            }
        }
        if !found {
            return Err(CertError::UnknownDependency { name: dep_name });
        }
        if !satisfied {
            return Ok(false);
        }
    }
    Ok(true)
}

fn imported_dependency_targets(module: &VerifiedModule) -> Result<BTreeSet<(Name, Hash)>> {
    let mut deps = BTreeSet::new();
    for entry in &module.export_block {
        collect_imported_dependency_targets_from_term(module, entry.ty, &mut deps)?;
        if let Some(body) = entry.body {
            collect_imported_dependency_targets_from_term(module, body, &mut deps)?;
        }
    }
    Ok(deps)
}

fn collect_imported_dependency_targets_from_term(
    module: &VerifiedModule,
    term: TermId,
    deps: &mut BTreeSet<(Name, Hash)>,
) -> Result<()> {
    match module.term_table.get(term).ok_or(CertError::DecodeError)? {
        TermNode::Sort(_) | TermNode::BVar(_) => {}
        TermNode::Const { global_ref, .. } => {
            if let GlobalRef::Imported {
                name,
                decl_interface_hash,
                ..
            } = global_ref
            {
                let name = module
                    .name_table
                    .get(*name)
                    .ok_or(CertError::DecodeError)?
                    .clone();
                deps.insert((name, *decl_interface_hash));
            }
        }
        TermNode::App(fun, arg) => {
            collect_imported_dependency_targets_from_term(module, *fun, deps)?;
            collect_imported_dependency_targets_from_term(module, *arg, deps)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_imported_dependency_targets_from_term(module, *ty, deps)?;
            collect_imported_dependency_targets_from_term(module, *body, deps)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_imported_dependency_targets_from_term(module, *ty, deps)?;
            collect_imported_dependency_targets_from_term(module, *value, deps)?;
            collect_imported_dependency_targets_from_term(module, *body, deps)?;
        }
    }
    Ok(())
}

fn module_exports_dependency(
    module: &VerifiedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<bool> {
    for entry in &module.export_block {
        let entry_name = module
            .name_table
            .get(entry.name)
            .ok_or(CertError::DecodeError)?;
        if entry_name == name && entry.decl_interface_hash == decl_interface_hash {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verify_dependencies_and_axioms(cert: &ModuleCert, imports: &[&VerifiedModule]) -> Result<()> {
    let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::new();
    let mut expected_reports = Vec::new();

    for (decl_index, decl) in cert.declarations.iter().enumerate() {
        let expected_deps = expected_dependencies_for_decl(cert, imports, decl_index, &decl.decl)?;
        if expected_deps != decl.dependencies {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        let (direct_axioms, transitive_axioms) = expected_axioms_for_decl(
            cert,
            imports,
            decl_index,
            &decl.decl,
            &expected_deps,
            &previous_axioms,
        )?;
        if transitive_axioms != decl.axiom_dependencies {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        let expected_report = DeclAxiomReport {
            decl_index,
            direct_axioms,
            transitive_axioms,
        };
        if cert.axiom_report.per_declaration.get(decl_index) != Some(&expected_report) {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        previous_axioms.push(expected_report.transitive_axioms.clone());
        expected_reports.push(expected_report);
    }

    if cert.axiom_report.per_declaration.len() != expected_reports.len() {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }

    let expected_module_axioms = union_axioms(
        expected_reports
            .iter()
            .flat_map(|report| report.transitive_axioms.iter().cloned()),
    );
    if expected_module_axioms != cert.axiom_report.module_axioms {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }
    let expected_features = core_features_from_builtins(&referenced_builtins_from_cert(cert)?);
    if expected_features != cert.axiom_report.core_features {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }

    Ok(())
}

fn verify_inductive_generated_artifacts(cert: &ModuleCert) -> Result<()> {
    for decl in &cert.declarations {
        let (name, universe_params, params, indices, sort, constructors, recursor) =
            match &decl.decl {
                DeclPayload::Inductive {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor: Some(recursor),
                    ..
                }
                | DeclPayload::InductiveConstrained {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor: Some(recursor),
                    ..
                } => (
                    *name,
                    universe_params.as_slice(),
                    params.as_slice(),
                    indices.as_slice(),
                    *sort,
                    constructors.as_slice(),
                    recursor,
                ),
                DeclPayload::MutualInductiveBlock {
                    name,
                    universe_params,
                    universe_constraints,
                    inductives,
                } => {
                    verify_mutual_inductive_generated_artifacts(
                        cert,
                        *name,
                        universe_params,
                        universe_constraints,
                        inductives,
                    )?;
                    continue;
                }
                _ => continue,
            };

        let expected_rules = RecursorRulesSpec {
            minor_start: params.len() + 1,
            major_index: params.len() + 1 + constructors.len() + indices.len(),
        };
        if recursor.rules != expected_rules {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: cert
                    .name_table
                    .get(name)
                    .ok_or(CertError::DecodeError)?
                    .clone(),
            });
        }

        let expected_type = expected_recursor_type_expr(
            cert,
            InductiveRecursorView {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
            },
        )?;
        if expr_from_term(cert, recursor.ty)? != expected_type {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: cert
                    .name_table
                    .get(name)
                    .ok_or(CertError::DecodeError)?
                    .clone(),
            });
        }
    }
    Ok(())
}

fn verify_mutual_inductive_generated_artifacts(
    cert: &ModuleCert,
    name: NameId,
    universe_params: &[NameId],
    universe_constraints: &[UniverseConstraintSpec],
    inductives: &[MutualInductiveSpec],
) -> Result<()> {
    let block_name = name_to_string(cert, name)?;
    let block_universe_params = universe_names(cert, universe_params)?;
    let mut expected_block = MutualInductiveBlock::new(
        block_name.clone(),
        block_universe_params.clone(),
        inductives
            .iter()
            .map(|inductive| {
                Ok(InductiveDecl::new(
                    name_to_string(cert, inductive.name)?,
                    block_universe_params.clone(),
                    inductive
                        .params
                        .iter()
                        .enumerate()
                        .map(|(index, binder)| {
                            Ok(Binder::new(
                                format!("p{index}"),
                                expr_from_term(cert, binder.ty)?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    inductive
                        .indices
                        .iter()
                        .enumerate()
                        .map(|(index, binder)| {
                            Ok(Binder::new(
                                format!("i{index}"),
                                expr_from_term(cert, binder.ty)?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    level_from_node(cert, inductive.sort)?,
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| {
                            Ok(ConstructorDecl::new(
                                name_to_string(cert, constructor.name)?,
                                expr_from_term(cert, constructor.ty)?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    None,
                ))
            })
            .collect::<Result<Vec<_>>>()?,
    );
    expected_block.universe_constraints = universe_constraints
        .iter()
        .map(|constraint| {
            Ok(npa_kernel::UniverseConstraint {
                lhs: level_from_node(cert, constraint.lhs)?,
                relation: constraint.relation,
                rhs: level_from_node(cert, constraint.rhs)?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let expected_block = generate_mutual_inductive_artifacts_v1(&expected_block)?;

    for (actual, expected) in inductives.iter().zip(expected_block.inductives.iter()) {
        let actual_recursor = actual.recursor.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        let expected_recursor = expected.recursor.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        let expected_rules = expected_recursor.rules.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        if name_to_string(cert, actual_recursor.name)? != expected_recursor.name
            || universe_names(cert, &actual_recursor.universe_params)?
                != expected_recursor.universe_params
            || actual_recursor.rules.minor_start != expected_rules.minor_start
            || actual_recursor.rules.major_index != expected_rules.major_index
            || expr_from_term(cert, actual_recursor.ty)? != expected_recursor.ty
        {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            });
        }
    }
    if inductives.len() != expected_block.inductives.len() {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&block_name),
        });
    }
    Ok(())
}

struct InductiveRecursorView<'a> {
    name: NameId,
    universe_params: &'a [NameId],
    params: &'a [BinderType],
    indices: &'a [BinderType],
    sort: LevelId,
    constructors: &'a [ConstructorSpec],
    recursor: &'a RecursorSpec,
}

fn expected_recursor_type_expr(cert: &ModuleCert, view: InductiveRecursorView<'_>) -> Result<Expr> {
    let inductive_name = name_to_string(cert, view.name)?;
    let inductive_universe_params = universe_names(cert, view.universe_params)?;
    let recursor_universe_params = universe_names(cert, &view.recursor.universe_params)?;
    let param_domains = view
        .params
        .iter()
        .map(|param| expr_from_term(cert, param.ty))
        .collect::<Result<Vec<_>>>()?;
    let index_domains = view
        .indices
        .iter()
        .map(|index| expr_from_term(cert, index.ty))
        .collect::<Result<Vec<_>>>()?;
    let motive_level = expected_motive_level(
        cert,
        view.sort,
        &inductive_universe_params,
        &recursor_universe_params,
    )?;

    let param_count = param_domains.len();
    let index_count = index_domains.len();
    let mut domains = param_domains;
    domains.push(motive_domain_expr(
        &inductive_name,
        &inductive_universe_params,
        param_count,
        &index_domains,
        motive_level,
    )?);

    for (constructor_index, constructor) in view.constructors.iter().enumerate() {
        domains.push(expected_minor_type_expr(
            cert,
            &inductive_name,
            &inductive_universe_params,
            param_count,
            index_count,
            constructor,
            constructor_index,
        )?);
    }

    let index_start = domains.len();
    append_index_domains(param_count, &index_domains, &mut domains)?;
    let major_domain = inductive_target_expr(
        &inductive_name,
        &inductive_universe_params,
        domains.len(),
        param_count,
        index_start,
        index_count,
    )?;
    domains.push(major_domain);
    let index_args = (0..index_count)
        .map(|index| bvar_for_abs(domains.len(), index_start + index))
        .collect::<Result<Vec<_>>>()?;
    let body = motive_app(
        domains.len(),
        param_count,
        index_args,
        bvar_for_abs(domains.len(), view.recursor.rules.major_index)?,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn expected_motive_level(
    cert: &ModuleCert,
    sort: LevelId,
    inductive_universe_params: &[String],
    recursor_universe_params: &[String],
) -> Result<Level> {
    let inductive_sort = level_from_node(cert, sort)?;
    if level_eq(&inductive_sort, &Level::zero()) {
        return Ok(Level::zero());
    }
    if let Some(param) = recursor_universe_params
        .iter()
        .rev()
        .find(|param| !inductive_universe_params.contains(*param))
    {
        return Ok(Level::param(param.clone()));
    }
    Ok(recursor_universe_params
        .last()
        .map(|param| Level::param(param.clone()))
        .unwrap_or(inductive_sort))
}

fn inductive_target_expr(
    inductive_name: &str,
    universe_params: &[String],
    ctx_len: usize,
    param_count: usize,
    index_abs_start: usize,
    index_count: usize,
) -> Result<Expr> {
    let levels = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let args = (0..param_count)
        .map(|param_abs| bvar_for_abs(ctx_len, param_abs))
        .chain((0..index_count).map(|index| bvar_for_abs(ctx_len, index_abs_start + index)))
        .collect::<Result<Vec<_>>>()?;
    Ok(Expr::apps(
        Expr::konst(inductive_name.to_owned(), levels),
        args,
    ))
}

fn motive_domain_expr(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    indices: &[Expr],
    motive_level: Level,
) -> Result<Expr> {
    let mut domains = Vec::new();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = param_count + index;
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    let target = inductive_target_expr(
        inductive_name,
        universe_params,
        param_count + indices.len(),
        param_count,
        param_count,
        indices.len(),
    )?;
    let body = Expr::pi("_", target, Expr::sort(motive_level));
    Ok(mk_pi_from_domains(domains, body))
}

fn append_index_domains(
    param_count: usize,
    index_domains: &[Expr],
    domains: &mut Vec<Expr>,
) -> Result<()> {
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in index_domains.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = domains.len();
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    Ok(())
}

fn expected_minor_type_expr(
    cert: &ModuleCert,
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    constructor: &ConstructorSpec,
    constructor_index: usize,
) -> Result<Expr> {
    let constructor_name = name_to_string(cert, constructor.name)?;
    let constructor_ty = expr_from_term(cert, constructor.ty)?;
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor_ty);
    if constructor_domains.len() < param_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }
    let constructor_result_indices = constructor_result_index_args(
        inductive_name,
        universe_params,
        param_count,
        index_count,
        &constructor_result,
    )?;

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
        )?);

        source_to_target.push(target_ctx_len);
        field_abs.push(target_ctx_len);
        target_ctx_len += 1;

        if is_direct_recursive_domain(
            inductive_name,
            universe_params,
            param_count,
            index_count,
            field_domain,
            source_ctx_len,
        )? {
            let index_args = direct_recursive_index_args(
                inductive_name,
                universe_params,
                param_count,
                index_count,
                field_domain,
                source_ctx_len,
            )?
            .into_iter()
            .map(|arg| remap_bvars(&arg, source_ctx_len, target_ctx_len, &source_to_target))
            .collect::<Result<Vec<_>>>()?;
            expected_domains.push(motive_app(
                target_ctx_len,
                motive_abs,
                index_args,
                Expr::bvar(0),
            )?);
            target_ctx_len += 1;
        }
    }

    let mut constructor_args = Vec::with_capacity(param_count + field_abs.len());
    for param_abs in 0..param_count {
        constructor_args.push(bvar_for_abs(target_ctx_len, param_abs)?);
    }
    for field_abs in field_abs {
        constructor_args.push(bvar_for_abs(target_ctx_len, field_abs)?);
    }

    let levels = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let constructor_value = Expr::apps(Expr::konst(constructor_name, levels), constructor_args);
    let result_index_args = constructor_result_indices
        .iter()
        .map(|arg| {
            remap_bvars(
                arg,
                constructor_domains.len(),
                target_ctx_len,
                &source_to_target,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs,
        result_index_args,
        constructor_value,
    )?;

    Ok(mk_pi_from_domains(expected_domains, result))
}

fn peel_pi_domains(ty: &Expr) -> (Vec<Expr>, Expr) {
    let mut domains = Vec::new();
    let mut current = ty;
    while let Expr::Pi { ty, body, .. } = current {
        domains.push((**ty).clone());
        current = body;
    }
    (domains, current.clone())
}

fn motive_app(
    ctx_len: usize,
    motive_abs: usize,
    index_args: Vec<Expr>,
    target: Expr,
) -> Result<Expr> {
    let mut args = index_args;
    args.push(target);
    Ok(Expr::apps(bvar_for_abs(ctx_len, motive_abs)?, args))
}

fn bvar_for_abs(ctx_len: usize, abs: usize) -> Result<Expr> {
    if abs >= ctx_len {
        return Err(CertError::InvalidBVar { index: abs as u32 });
    }
    Ok(Expr::bvar((ctx_len - 1 - abs) as u32))
}

fn mk_pi_from_domains(domains: Vec<Expr>, body: Expr) -> Expr {
    domains
        .into_iter()
        .rev()
        .fold(body, |body, domain| Expr::pi("_", domain, body))
}

fn remap_bvars(
    expr: &Expr,
    source_ctx_len: usize,
    target_ctx_len: usize,
    source_to_target: &[usize],
) -> Result<Expr> {
    match expr {
        Expr::Sort(level) => Ok(Expr::sort(level.clone())),
        Expr::BVar(index) => {
            let index = *index as usize;
            if index >= source_ctx_len {
                return Err(CertError::InvalidBVar {
                    index: index as u32,
                });
            }
            let source_abs = source_ctx_len - 1 - index;
            let target_abs =
                source_to_target
                    .get(source_abs)
                    .copied()
                    .ok_or(CertError::InvalidBVar {
                        index: index as u32,
                    })?;
            bvar_for_abs(target_ctx_len, target_abs)
        }
        Expr::Const { name, levels } => Ok(Expr::konst(name.clone(), levels.clone())),
        Expr::App(fun, arg) => Ok(Expr::app(
            remap_bvars(fun, source_ctx_len, target_ctx_len, source_to_target)?,
            remap_bvars(arg, source_ctx_len, target_ctx_len, source_to_target)?,
        )),
        Expr::Lam { binder, ty, body } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(Expr::lam(
                binder.clone(),
                remap_bvars(ty, source_ctx_len, target_ctx_len, source_to_target)?,
                remap_bvars(body, source_ctx_len + 1, target_ctx_len + 1, &body_map)?,
            ))
        }
        Expr::Pi { binder, ty, body } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(Expr::pi(
                binder.clone(),
                remap_bvars(ty, source_ctx_len, target_ctx_len, source_to_target)?,
                remap_bvars(body, source_ctx_len + 1, target_ctx_len + 1, &body_map)?,
            ))
        }
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => {
            let mut body_map = source_to_target.to_vec();
            body_map.push(target_ctx_len);
            Ok(Expr::let_in(
                binder.clone(),
                remap_bvars(ty, source_ctx_len, target_ctx_len, source_to_target)?,
                remap_bvars(value, source_ctx_len, target_ctx_len, source_to_target)?,
                remap_bvars(body, source_ctx_len + 1, target_ctx_len + 1, &body_map)?,
            ))
        }
    }
}

fn is_direct_recursive_domain(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    domain: &Expr,
    ctx_len: usize,
) -> Result<bool> {
    Ok(direct_recursive_index_args(
        inductive_name,
        universe_params,
        param_count,
        index_count,
        domain,
        ctx_len,
    )
    .is_ok())
}

fn direct_recursive_index_args(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    domain: &Expr,
    ctx_len: usize,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(domain);
    let levels = match head {
        Expr::Const { name, levels } if name == inductive_name => levels,
        _ => {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    };

    let expected_levels: Vec<_> = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != param_count + index_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }

    for (param_index, arg) in args.iter().take(param_count).enumerate() {
        let expected = bvar_for_abs(ctx_len, param_index)?;
        if arg != &expected {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    }

    if args.iter().all(|arg| !contains_const(arg, inductive_name)) {
        Ok(args[param_count..].to_vec())
    } else {
        Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        })
    }
}

fn constructor_result_index_args(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    result: &Expr,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(result);
    let levels = match head {
        Expr::Const { name, levels } if name == inductive_name => levels,
        _ => {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    };
    let expected_levels: Vec<_> = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != param_count + index_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }
    Ok(args[param_count..].to_vec())
}

fn contains_const(expr: &Expr, needle: &str) -> bool {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => false,
        Expr::Const { name, .. } => name == needle,
        Expr::App(fun, arg) => contains_const(fun, needle) || contains_const(arg, needle),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            contains_const(ty, needle) || contains_const(body, needle)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            contains_const(ty, needle)
                || contains_const(value, needle)
                || contains_const(body, needle)
        }
    }
}

pub(crate) fn expected_dependencies_for_decl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    decl_index: usize,
    decl: &DeclPayload,
) -> Result<Vec<DependencyEntry>> {
    let mut refs = BTreeSet::new();
    for term in decl_term_ids(decl) {
        collect_global_refs_from_term(cert, term, &mut refs)?;
    }

    let current_decl_index = decl_index;
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
                } if allow_self_reference && *referenced_decl_index == current_decl_index
            )
        })
        .map(|global_ref| {
            let decl_interface_hash =
                interface_hash_for_global_ref(cert, imports, decl_index, &global_ref)?;
            Ok(DependencyEntry {
                global_ref,
                decl_interface_hash,
            })
        })
        .collect()
}

pub(crate) fn expected_axioms_for_decl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    decl_index: usize,
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    previous_axioms: &[Vec<AxiomRef>],
) -> Result<(Vec<AxiomRef>, Vec<AxiomRef>)> {
    let mut direct = BTreeSet::new();
    let mut transitive = BTreeSet::new();
    for dependency in dependencies {
        match &dependency.global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                let name_value = cert.name_table.get(*name).ok_or(CertError::DecodeError)?;
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
            GlobalRef::Local { decl_index } => {
                if let Some(dep_axioms) = previous_axioms.get(*decl_index) {
                    if let Some(axiom) = local_axiom_ref_for_decl(*decl_index, dep_axioms) {
                        direct.insert(axiom);
                    }
                    transitive.extend(dep_axioms.iter().cloned());
                }
            }
            GlobalRef::LocalGenerated { decl_index, .. } => {
                if let Some(dep_axioms) = previous_axioms.get(*decl_index) {
                    transitive.extend(dep_axioms.iter().cloned());
                }
            }
            GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let entry =
                    imported_export_entry_for_global_ref(cert, imports, &dependency.global_ref)?;
                if entry.kind == ExportKind::Axiom {
                    direct.insert(AxiomRef {
                        global_ref: dependency.global_ref.clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    });
                }
                let import = imports.get(*import_index).ok_or(CertError::DecodeError)?;
                for axiom in &entry.axiom_dependencies {
                    transitive.insert(remap_axiom_ref_from_cert_import(
                        cert, imports, import, axiom,
                    )?);
                }
            }
        }
    }
    if let DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } = decl {
        let self_ref = AxiomRef {
            global_ref: GlobalRef::Local { decl_index },
            name: *name,
            decl_interface_hash: cert
                .declarations
                .get(decl_index)
                .ok_or(CertError::DecodeError)?
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

fn remap_axiom_ref_from_cert_import(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    import: &VerifiedModule,
    axiom: &AxiomRef,
) -> Result<AxiomRef> {
    let axiom_name = import
        .name_table
        .get(axiom.name)
        .ok_or(CertError::DecodeError)?;
    let name = cert
        .name_table
        .iter()
        .position(|candidate| candidate == axiom_name)
        .ok_or(CertError::DecodeError)?;
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

fn import_index_exporting_axiom(
    imports: &[&VerifiedModule],
    axiom_name: &Name,
    decl_interface_hash: Hash,
) -> Result<usize> {
    imports
        .iter()
        .enumerate()
        .find_map(|(import_index, import)| {
            import
                .export_block
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

fn decl_term_ids(decl: &DeclPayload) -> Vec<TermId> {
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

fn decl_universe_params(decl: &DeclPayload) -> &[NameId] {
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

fn collect_global_refs_from_term(
    cert: &ModuleCert,
    term: TermId,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    collect_global_refs_from_term_table(&cert.term_table, term, refs)
}

fn collect_global_refs_from_term_table(
    term_table: &[TermNode],
    term: TermId,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    match term_table.get(term).ok_or(CertError::DecodeError)? {
        TermNode::Sort(_) | TermNode::BVar(_) => {}
        TermNode::Const { global_ref, .. } => {
            refs.insert(global_ref.clone());
        }
        TermNode::App(fun, arg) => {
            collect_global_refs_from_term_table(term_table, *fun, refs)?;
            collect_global_refs_from_term_table(term_table, *arg, refs)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_global_refs_from_term_table(term_table, *ty, refs)?;
            collect_global_refs_from_term_table(term_table, *body, refs)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_global_refs_from_term_table(term_table, *ty, refs)?;
            collect_global_refs_from_term_table(term_table, *value, refs)?;
            collect_global_refs_from_term_table(term_table, *body, refs)?;
        }
    }
    Ok(())
}

fn referenced_builtins_from_cert(cert: &ModuleCert) -> Result<BTreeSet<Name>> {
    let mut names = BTreeSet::new();
    for term in &cert.term_table {
        if let TermNode::Const {
            global_ref:
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                },
            ..
        } = term
        {
            let name_value = cert.name_table.get(*name).ok_or(CertError::DecodeError)?;
            if builtin_decl_interface_hash(name_value) != Some(*decl_interface_hash) {
                return Err(CertError::UnknownDependency {
                    name: name_value.clone(),
                });
            }
            names.insert(name_value.clone());
        }
    }
    Ok(names)
}

fn interface_hash_for_global_ref(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    current_decl_index: usize,
    global_ref: &GlobalRef,
) -> Result<Hash> {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = cert.name_table.get(*name).ok_or(CertError::DecodeError)?;
            if builtin_decl_interface_hash(name) != Some(*decl_interface_hash) {
                return Err(CertError::UnknownDependency { name: name.clone() });
            }
            Ok(*decl_interface_hash)
        }
        GlobalRef::Local { decl_index } => {
            if *decl_index >= current_decl_index {
                return Err(CertError::DependencyCycle {
                    name: Name::from_dotted(format!("local.{decl_index}")),
                });
            }
            Ok(cert
                .declarations
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash)
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            if *decl_index >= current_decl_index {
                return Err(CertError::DependencyCycle {
                    name: cert
                        .name_table
                        .get(*name)
                        .cloned()
                        .unwrap_or_else(|| Name::from_dotted(format!("local.{decl_index}"))),
                });
            }
            if !local_generated_entry_exists(cert, *decl_index, *name)? {
                return Err(CertError::UnknownDependency {
                    name: cert
                        .name_table
                        .get(*name)
                        .cloned()
                        .ok_or(CertError::DecodeError)?,
                });
            }
            Ok(cert
                .declarations
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash)
        }
        GlobalRef::Imported {
            decl_interface_hash,
            ..
        } => {
            let entry = imported_export_entry_for_global_ref(cert, imports, global_ref)?;
            if entry.decl_interface_hash != *decl_interface_hash {
                return Err(CertError::ImportHashMismatch {
                    module: imported_module_name_for_global_ref(imports, global_ref)?,
                });
            }
            Ok(*decl_interface_hash)
        }
    }
}

fn local_generated_entry_exists(
    cert: &ModuleCert,
    decl_index: usize,
    name: NameId,
) -> Result<bool> {
    let decl = cert
        .declarations
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    Ok(match &decl.decl {
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

fn imported_export_entry_for_global_ref<'a>(
    cert: &ModuleCert,
    imports: &'a [&'a VerifiedModule],
    global_ref: &GlobalRef,
) -> Result<&'a ExportEntry> {
    let GlobalRef::Imported {
        import_index,
        name,
        decl_interface_hash,
    } = global_ref
    else {
        return Err(CertError::DecodeError);
    };
    let imported = imports.get(*import_index).ok_or(CertError::DecodeError)?;
    let wanted_name = cert.name_table.get(*name).ok_or(CertError::DecodeError)?;
    imported
        .export_block
        .iter()
        .find(|entry| {
            imported
                .name_table
                .get(entry.name)
                .is_some_and(|candidate| candidate == wanted_name)
                && entry.decl_interface_hash == *decl_interface_hash
        })
        .ok_or_else(|| CertError::ImportHashMismatch {
            module: imported.module.clone(),
        })
}

fn imported_module_name_for_global_ref(
    imports: &[&VerifiedModule],
    global_ref: &GlobalRef,
) -> Result<ModuleName> {
    let GlobalRef::Imported { import_index, .. } = global_ref else {
        return Err(CertError::DecodeError);
    };
    Ok(imports
        .get(*import_index)
        .ok_or(CertError::DecodeError)?
        .module
        .clone())
}

fn decl_name_as_name(cert: &ModuleCert, decl_index: usize) -> Result<Name> {
    let decl = cert
        .declarations
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    let name = match &decl.decl {
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
    cert.name_table
        .get(name)
        .cloned()
        .ok_or(CertError::DecodeError)
}

fn enforce_axiom_policy(cert: &ModuleCert, policy: &AxiomPolicy) -> Result<()> {
    enforce_axiom_policy_for_report(&cert.name_table, &cert.axiom_report, policy)
}

fn enforce_import_axiom_policy(imports: &[&VerifiedModule], policy: &AxiomPolicy) -> Result<()> {
    for import in imports {
        enforce_core_feature_policy(&import.axiom_report, policy)?;
        enforce_axiom_policy_for_report(&import.name_table, &import.axiom_report, policy)?;
    }
    Ok(())
}

fn enforce_core_feature_policy(axiom_report: &AxiomReport, policy: &AxiomPolicy) -> Result<()> {
    for feature in &axiom_report.core_features {
        if !policy.supported_core_features.contains(feature) {
            return Err(CertError::UnsupportedCoreFeature {
                feature: feature.as_str().to_owned(),
            });
        }
    }
    Ok(())
}

fn enforce_axiom_policy_for_report(
    name_table: &[Name],
    axiom_report: &AxiomReport,
    policy: &AxiomPolicy,
) -> Result<()> {
    for axiom in &axiom_report.module_axioms {
        let name = name_table.get(axiom.name).ok_or(CertError::DecodeError)?;
        let dotted = name.as_dotted();
        if policy.deny_sorry && dotted.contains("sorry") {
            return Err(CertError::SorryDenied {
                axiom: name.clone(),
            });
        }
        let require_allowlist =
            policy.mode == TrustMode::HighTrust || !policy.allowlisted_axioms.is_empty();
        if require_allowlist && !policy.allowlisted_axioms.contains(name) {
            return Err(CertError::ForbiddenAxiom {
                axiom: name.clone(),
            });
        }
    }
    Ok(())
}

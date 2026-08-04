use std::collections::BTreeMap;

use crate::{
    CertError, DeclPayload, GlobalRef, Hash, ImportEntry, LevelId, LevelNode, ModuleCert, Name,
    StructuralLimitKind, TermId, TermNode,
};

/// Maximum encoded certificate length accepted by certificate APIs.
pub const MAX_CERTIFICATE_BYTES: usize = 67_108_864;
/// Maximum direct imports in one certificate.
pub const MAX_IMPORTS: usize = 4_096;
/// Maximum canonical name-table entries in one certificate.
pub const MAX_NAME_TABLE_ENTRIES: usize = 1_048_576;
/// Maximum canonical level-table nodes in one certificate.
pub const MAX_LEVEL_TABLE_NODES: usize = 262_144;
/// Maximum canonical term-table nodes in one certificate.
pub const MAX_TERM_TABLE_NODES: usize = 4_194_304;
/// Maximum declarations in one certificate.
pub const MAX_DECLARATIONS: usize = 262_144;
/// Maximum public exports in one certificate.
pub const MAX_EXPORTS: usize = 1_048_576;
/// Maximum entries in an encoded vector without a more specific limit.
pub const MAX_NESTED_VECTOR_ENTRIES: usize = 262_144;
/// Maximum combined term/level structural depth.
pub const MAX_STRUCTURAL_DEPTH: usize = 8_192;
/// Maximum unfolded nodes requested by one semantic root.
pub const MAX_ROOT_EXPANDED_NODES: usize = 1_048_576;
/// Maximum summed unfolded nodes requested by one certificate.
pub const MAX_CERTIFICATE_EXPANDED_NODES: usize = 16_777_216;
/// Maximum unique certificate identities in a resolved closure, including the root.
pub const MAX_CLOSURE_MODULES: usize = 4_097;
/// Maximum summed certificate expansion in a resolved closure.
pub const MAX_CLOSURE_EXPANDED_NODES: usize = 67_108_864;

/// Non-verifying structural measurements for one decoded certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateStructuralAudit {
    /// Module identity carried by the certificate header.
    pub module: Name,
    /// Stored export hash used to resolve tracked import closures.
    pub export_hash: Hash,
    /// Stored certificate hash used only as report identity.
    pub certificate_hash: Hash,
    /// Direct imports used to resolve tracked import closures.
    pub direct_imports: Vec<CertificateStructuralImportAudit>,
    /// Encoded byte length.
    pub certificate_bytes: usize,
    /// Direct import count.
    pub imports: usize,
    /// Name-table entry count.
    pub name_table_entries: usize,
    /// Level-table node count.
    pub level_table_nodes: usize,
    /// Term-table node count.
    pub term_table_nodes: usize,
    /// Declaration count.
    pub declarations: usize,
    /// Export count.
    pub exports: usize,
    /// Largest nested vector count.
    pub nested_vector_entries: usize,
    /// Largest combined term/level structural depth.
    pub structural_depth: usize,
    /// Largest unfolded semantic-root expansion.
    pub root_expanded_nodes: usize,
    /// Sum of all semantic-root expansions.
    pub certificate_expanded_nodes: usize,
}

/// Import identity exposed to the non-verifying structural corpus audit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateStructuralImportAudit {
    /// Imported module name.
    pub module: Name,
    /// Required export hash.
    pub export_hash: Hash,
    /// Optional exact certificate hash.
    pub certificate_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructuralIdentity {
    pub(crate) module: Name,
    pub(crate) export_hash: Hash,
    pub(crate) certificate_hash: Hash,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct StructuralClosureSummary {
    pub(crate) modules: BTreeMap<StructuralIdentity, usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StructuralCost {
    pub(crate) max_depth: usize,
    pub(crate) max_root_expansion: usize,
    pub(crate) certificate_expansion: usize,
}

struct RootAccumulator {
    max_depth: usize,
    max_root_expansion: usize,
    certificate_expansion: usize,
}

fn exceeded(kind: StructuralLimitKind, limit: usize, observed: usize) -> CertError {
    CertError::StructuralLimitExceeded {
        kind,
        limit,
        observed,
    }
}

pub(crate) fn ensure_certificate_byte_limit(bytes: &[u8]) -> Result<(), CertError> {
    if bytes.len() > MAX_CERTIFICATE_BYTES {
        return Err(exceeded(
            StructuralLimitKind::CertificateBytes,
            MAX_CERTIFICATE_BYTES,
            bytes.len(),
        ));
    }
    Ok(())
}

pub(crate) fn ensure_count_limit(
    kind: StructuralLimitKind,
    limit: usize,
    observed: usize,
) -> Result<(), CertError> {
    if observed > limit {
        return Err(exceeded(kind, limit, observed));
    }
    Ok(())
}

fn nested(observed: usize) -> Result<(), CertError> {
    ensure_count_limit(
        StructuralLimitKind::NestedVectorEntries,
        MAX_NESTED_VECTOR_ENTRIES,
        observed,
    )
}

fn check_name(name: &Name) -> Result<(), CertError> {
    nested(name.0.len())
}

fn check_import(import: &ImportEntry) -> Result<(), CertError> {
    check_name(&import.module)
}

fn validate_counts(cert: &ModuleCert) -> Result<(), CertError> {
    ensure_count_limit(
        StructuralLimitKind::Imports,
        MAX_IMPORTS,
        cert.imports.len(),
    )?;
    ensure_count_limit(
        StructuralLimitKind::NameTableEntries,
        MAX_NAME_TABLE_ENTRIES,
        cert.name_table.len(),
    )?;
    ensure_count_limit(
        StructuralLimitKind::LevelTableNodes,
        MAX_LEVEL_TABLE_NODES,
        cert.level_table.len(),
    )?;
    ensure_count_limit(
        StructuralLimitKind::TermTableNodes,
        MAX_TERM_TABLE_NODES,
        cert.term_table.len(),
    )?;
    ensure_count_limit(
        StructuralLimitKind::Declarations,
        MAX_DECLARATIONS,
        cert.declarations.len(),
    )?;
    ensure_count_limit(
        StructuralLimitKind::Exports,
        MAX_EXPORTS,
        cert.export_block.len(),
    )?;
    check_name(&cert.header.module)?;
    for import in &cert.imports {
        check_import(import)?;
    }
    for name in &cert.name_table {
        check_name(name)?;
    }
    for term in &cert.term_table {
        if let TermNode::Const { levels, .. } = term {
            nested(levels.len())?;
        }
    }
    for declaration in &cert.declarations {
        nested(declaration.dependencies.len())?;
        nested(declaration.axiom_dependencies.len())?;
        check_decl_counts(&declaration.decl)?;
    }
    for export in &cert.export_block {
        nested(export.universe_params.len())?;
        nested(export.universe_constraints.len())?;
        nested(export.axiom_dependencies.len())?;
    }
    ensure_count_limit(
        StructuralLimitKind::Declarations,
        MAX_DECLARATIONS,
        cert.axiom_report.per_declaration.len(),
    )?;
    nested(cert.axiom_report.module_axioms.len())?;
    nested(cert.axiom_report.core_features.len())?;
    for report in &cert.axiom_report.per_declaration {
        nested(report.direct_axioms.len())?;
        nested(report.transitive_axioms.len())?;
    }
    Ok(())
}

fn check_decl_counts(decl: &DeclPayload) -> Result<(), CertError> {
    match decl {
        DeclPayload::Axiom {
            universe_params, ..
        }
        | DeclPayload::Def {
            universe_params, ..
        }
        | DeclPayload::Theorem {
            universe_params, ..
        } => nested(universe_params.len()),
        DeclPayload::AxiomConstrained {
            universe_params,
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_params,
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_params,
            universe_constraints,
            ..
        } => {
            nested(universe_params.len())?;
            nested(universe_constraints.len())
        }
        DeclPayload::Inductive {
            universe_params,
            params,
            indices,
            constructors,
            recursor,
            ..
        } => {
            nested(universe_params.len())?;
            nested(params.len())?;
            nested(indices.len())?;
            nested(constructors.len())?;
            if let Some(recursor) = recursor {
                nested(recursor.universe_params.len())?;
            }
            Ok(())
        }
        DeclPayload::InductiveConstrained {
            universe_params,
            universe_constraints,
            params,
            indices,
            constructors,
            recursor,
            ..
        } => {
            nested(universe_params.len())?;
            nested(universe_constraints.len())?;
            nested(params.len())?;
            nested(indices.len())?;
            nested(constructors.len())?;
            if let Some(recursor) = recursor {
                nested(recursor.universe_params.len())?;
            }
            Ok(())
        }
        DeclPayload::MutualInductiveBlock {
            universe_params,
            universe_constraints,
            inductives,
            ..
        } => {
            nested(universe_params.len())?;
            nested(universe_constraints.len())?;
            nested(inductives.len())?;
            for inductive in inductives {
                nested(inductive.params.len())?;
                nested(inductive.indices.len())?;
                nested(inductive.constructors.len())?;
                if let Some(recursor) = &inductive.recursor {
                    nested(recursor.universe_params.len())?;
                }
            }
            Ok(())
        }
    }
}

fn max_nested_count(cert: &ModuleCert) -> usize {
    let mut maximum = cert.header.module.0.len();
    let mut observe = |value: usize| maximum = maximum.max(value);
    for import in &cert.imports {
        observe(import.module.0.len());
    }
    for name in &cert.name_table {
        observe(name.0.len());
    }
    for term in &cert.term_table {
        if let TermNode::Const { levels, .. } = term {
            observe(levels.len());
        }
    }
    for declaration in &cert.declarations {
        observe(declaration.dependencies.len());
        observe(declaration.axiom_dependencies.len());
        match &declaration.decl {
            DeclPayload::Axiom {
                universe_params, ..
            }
            | DeclPayload::Def {
                universe_params, ..
            }
            | DeclPayload::Theorem {
                universe_params, ..
            } => observe(universe_params.len()),
            DeclPayload::AxiomConstrained {
                universe_params,
                universe_constraints,
                ..
            }
            | DeclPayload::DefConstrained {
                universe_params,
                universe_constraints,
                ..
            }
            | DeclPayload::TheoremConstrained {
                universe_params,
                universe_constraints,
                ..
            } => {
                observe(universe_params.len());
                observe(universe_constraints.len());
            }
            DeclPayload::Inductive {
                universe_params,
                params,
                indices,
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                universe_params,
                params,
                indices,
                constructors,
                recursor,
                ..
            } => {
                observe(universe_params.len());
                observe(params.len());
                observe(indices.len());
                observe(constructors.len());
                if let Some(recursor) = recursor {
                    observe(recursor.universe_params.len());
                }
                if let DeclPayload::InductiveConstrained {
                    universe_constraints,
                    ..
                } = &declaration.decl
                {
                    observe(universe_constraints.len());
                }
            }
            DeclPayload::MutualInductiveBlock {
                universe_params,
                universe_constraints,
                inductives,
                ..
            } => {
                observe(universe_params.len());
                observe(universe_constraints.len());
                observe(inductives.len());
                for inductive in inductives {
                    observe(inductive.params.len());
                    observe(inductive.indices.len());
                    observe(inductive.constructors.len());
                    if let Some(recursor) = &inductive.recursor {
                        observe(recursor.universe_params.len());
                    }
                }
            }
        }
    }
    for export in &cert.export_block {
        observe(export.universe_params.len());
        observe(export.universe_constraints.len());
        observe(export.axiom_dependencies.len());
    }
    for report in &cert.axiom_report.per_declaration {
        observe(report.direct_axioms.len());
        observe(report.transitive_axioms.len());
    }
    observe(cert.axiom_report.module_axioms.len());
    observe(cert.axiom_report.core_features.len());
    maximum
}

fn validate_semantic_root_references(cert: &ModuleCert) -> Result<(), CertError> {
    let level = |root: LevelId| {
        if root < cert.level_table.len() {
            Ok(())
        } else {
            Err(CertError::DecodeError)
        }
    };
    let term = |root: TermId| {
        if root < cert.term_table.len() {
            Ok(())
        } else {
            Err(CertError::DecodeError)
        }
    };
    for declaration in &cert.declarations {
        for constraint in decl_constraints(&declaration.decl) {
            level(constraint.lhs)?;
            level(constraint.rhs)?;
        }
        match &declaration.decl {
            DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
                term(*ty)?;
            }
            DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
                term(*ty)?;
                term(*value)?;
            }
            DeclPayload::Theorem { ty, proof, .. }
            | DeclPayload::TheoremConstrained { ty, proof, .. } => {
                term(*ty)?;
                term(*proof)?;
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
                for binder in params.iter().chain(indices) {
                    term(binder.ty)?;
                }
                level(*sort)?;
                for constructor in constructors {
                    term(constructor.ty)?;
                }
                if let Some(recursor) = recursor {
                    term(recursor.ty)?;
                }
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    for binder in inductive.params.iter().chain(&inductive.indices) {
                        term(binder.ty)?;
                    }
                    level(inductive.sort)?;
                    for constructor in &inductive.constructors {
                        term(constructor.ty)?;
                    }
                    if let Some(recursor) = &inductive.recursor {
                        term(recursor.ty)?;
                    }
                }
            }
        }
    }
    for export in &cert.export_block {
        for constraint in &export.universe_constraints {
            level(constraint.lhs)?;
            level(constraint.rhs)?;
        }
        term(export.ty)?;
        if let Some(body) = export.body {
            term(body)?;
        }
    }
    Ok(())
}

pub(crate) fn structural_audit(
    cert: &ModuleCert,
    certificate_bytes: usize,
    decoded_core_feature_count: usize,
) -> Result<CertificateStructuralAudit, CertError> {
    let cost = structural_preflight(cert)?;
    Ok(CertificateStructuralAudit {
        module: cert.header.module.clone(),
        export_hash: cert.hashes.export_hash,
        certificate_hash: cert.hashes.certificate_hash,
        direct_imports: cert
            .imports
            .iter()
            .map(|import| CertificateStructuralImportAudit {
                module: import.module.clone(),
                export_hash: import.export_hash,
                certificate_hash: import.certificate_hash,
            })
            .collect(),
        certificate_bytes,
        imports: cert.imports.len(),
        name_table_entries: cert.name_table.len(),
        level_table_nodes: cert.level_table.len(),
        term_table_nodes: cert.term_table.len(),
        declarations: cert.declarations.len(),
        exports: cert.export_block.len(),
        nested_vector_entries: max_nested_count(cert).max(decoded_core_feature_count),
        structural_depth: cost.max_depth,
        root_expanded_nodes: cost.max_root_expansion,
        certificate_expanded_nodes: cost.certificate_expansion,
    })
}

fn checked_child<T: Copy>(values: &[T], index: usize) -> Result<T, CertError> {
    values.get(index).copied().ok_or(CertError::DecodeError)
}

fn capped_sum(values: impl IntoIterator<Item = usize>, cap: usize) -> usize {
    values
        .into_iter()
        .fold(0usize, |total, value| total.saturating_add(value).min(cap))
}

pub(crate) fn structural_preflight(cert: &ModuleCert) -> Result<StructuralCost, CertError> {
    validate_counts(cert)?;
    validate_semantic_root_references(cert)?;
    let expansion_cap = MAX_ROOT_EXPANDED_NODES + 1;
    let mut depth_exceeded = false;
    let mut level_depths: Vec<usize> = Vec::new();
    let mut level_expansions: Vec<usize> = Vec::new();
    level_depths
        .try_reserve_exact(cert.level_table.len())
        .map_err(|_| CertError::DecodeError)?;
    level_expansions
        .try_reserve_exact(cert.level_table.len())
        .map_err(|_| CertError::DecodeError)?;
    for (index, level) in cert.level_table.iter().enumerate() {
        let (depth, expansion) = match level {
            LevelNode::Zero => (1, 1),
            LevelNode::Param(name) => {
                if *name >= cert.name_table.len() {
                    return Err(CertError::DecodeError);
                }
                (1, 1)
            }
            LevelNode::Succ(inner) => {
                if *inner >= index {
                    return Err(CertError::DecodeError);
                }
                (
                    checked_child(&level_depths, *inner)?.saturating_add(1),
                    checked_child(&level_expansions, *inner)?
                        .saturating_add(1)
                        .min(expansion_cap),
                )
            }
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                if *lhs >= index || *rhs >= index {
                    return Err(CertError::DecodeError);
                }
                (
                    checked_child(&level_depths, *lhs)?
                        .max(checked_child(&level_depths, *rhs)?)
                        .saturating_add(1),
                    capped_sum(
                        [
                            1,
                            checked_child(&level_expansions, *lhs)?,
                            checked_child(&level_expansions, *rhs)?,
                        ],
                        expansion_cap,
                    ),
                )
            }
        };
        depth_exceeded |= depth > MAX_STRUCTURAL_DEPTH;
        level_depths.push(depth);
        level_expansions.push(expansion);
    }

    let mut term_depths: Vec<usize> = Vec::new();
    let mut term_expansions: Vec<usize> = Vec::new();
    term_depths
        .try_reserve_exact(cert.term_table.len())
        .map_err(|_| CertError::DecodeError)?;
    term_expansions
        .try_reserve_exact(cert.term_table.len())
        .map_err(|_| CertError::DecodeError)?;
    for (index, term) in cert.term_table.iter().enumerate() {
        let mut term_children = [0usize; 3];
        let term_child_count;
        let mut level_children: &[LevelId] = &[];
        match term {
            TermNode::Sort(level) => {
                term_child_count = 0;
                level_children = std::slice::from_ref(level);
            }
            TermNode::BVar(_) => term_child_count = 0,
            TermNode::Const { global_ref, levels } => {
                validate_global_ref_shape(cert, global_ref)?;
                term_child_count = 0;
                level_children = levels;
            }
            TermNode::App(fun, arg) => {
                term_children[..2].copy_from_slice(&[*fun, *arg]);
                term_child_count = 2;
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                term_children[..2].copy_from_slice(&[*ty, *body]);
                term_child_count = 2;
            }
            TermNode::Let { ty, value, body } => {
                term_children.copy_from_slice(&[*ty, *value, *body]);
                term_child_count = 3;
            }
        }
        let term_children = &term_children[..term_child_count];
        if term_children.iter().any(|child| *child >= index) {
            return Err(CertError::DecodeError);
        }
        if level_children
            .iter()
            .any(|level| *level >= cert.level_table.len())
        {
            return Err(CertError::DecodeError);
        }
        let mut child_depth = 0usize;
        for child in term_children {
            child_depth = child_depth.max(checked_child(&term_depths, *child)?);
        }
        for level in level_children {
            child_depth = child_depth.max(checked_child(&level_depths, *level)?);
        }
        let depth = 1usize.saturating_add(child_depth);
        let expansion = capped_sum(
            std::iter::once(1)
                .chain(term_children.iter().map(|child| term_expansions[*child]))
                .chain(level_children.iter().map(|level| level_expansions[*level])),
            expansion_cap,
        );
        depth_exceeded |= depth > MAX_STRUCTURAL_DEPTH;
        term_depths.push(depth);
        term_expansions.push(expansion);
    }
    if depth_exceeded {
        return Err(exceeded(
            StructuralLimitKind::StructuralDepth,
            MAX_STRUCTURAL_DEPTH,
            MAX_STRUCTURAL_DEPTH + 1,
        ));
    }

    let max_depth = level_depths
        .iter()
        .chain(&term_depths)
        .copied()
        .max()
        .unwrap_or(0);
    let mut roots = RootAccumulator {
        max_depth,
        max_root_expansion: 0,
        certificate_expansion: 0,
    };

    for declaration in &cert.declarations {
        for constraint in decl_constraints(&declaration.decl) {
            add_level_root(&mut roots, constraint.lhs, &level_depths, &level_expansions)?;
            add_level_root(&mut roots, constraint.rhs, &level_depths, &level_expansions)?;
        }
        match &declaration.decl {
            DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
                add_term_root(&mut roots, *ty, &term_depths, &term_expansions)?;
            }
            DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
                add_term_root(&mut roots, *ty, &term_depths, &term_expansions)?;
                add_term_root(&mut roots, *value, &term_depths, &term_expansions)?;
            }
            DeclPayload::Theorem { ty, proof, .. }
            | DeclPayload::TheoremConstrained { ty, proof, .. } => {
                add_term_root(&mut roots, *ty, &term_depths, &term_expansions)?;
                add_term_root(&mut roots, *proof, &term_depths, &term_expansions)?;
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
                for binder in params.iter().chain(indices) {
                    add_term_root(&mut roots, binder.ty, &term_depths, &term_expansions)?;
                }
                add_level_root(&mut roots, *sort, &level_depths, &level_expansions)?;
                for constructor in constructors {
                    add_term_root(&mut roots, constructor.ty, &term_depths, &term_expansions)?;
                }
                if let Some(recursor) = recursor {
                    add_term_root(&mut roots, recursor.ty, &term_depths, &term_expansions)?;
                }
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    for binder in inductive.params.iter().chain(&inductive.indices) {
                        add_term_root(&mut roots, binder.ty, &term_depths, &term_expansions)?;
                    }
                    add_level_root(&mut roots, inductive.sort, &level_depths, &level_expansions)?;
                    for constructor in &inductive.constructors {
                        add_term_root(&mut roots, constructor.ty, &term_depths, &term_expansions)?;
                    }
                    if let Some(recursor) = &inductive.recursor {
                        add_term_root(&mut roots, recursor.ty, &term_depths, &term_expansions)?;
                    }
                }
            }
        }
    }
    for export in &cert.export_block {
        for constraint in &export.universe_constraints {
            add_level_root(&mut roots, constraint.lhs, &level_depths, &level_expansions)?;
            add_level_root(&mut roots, constraint.rhs, &level_depths, &level_expansions)?;
        }
        add_term_root(&mut roots, export.ty, &term_depths, &term_expansions)?;
        if let Some(body) = export.body {
            add_term_root(&mut roots, body, &term_depths, &term_expansions)?;
        }
    }

    Ok(StructuralCost {
        max_depth: roots.max_depth,
        max_root_expansion: roots.max_root_expansion,
        certificate_expansion: roots.certificate_expansion,
    })
}

fn validate_global_ref_shape(cert: &ModuleCert, global_ref: &GlobalRef) -> Result<(), CertError> {
    let valid = match global_ref {
        GlobalRef::Builtin { name, .. } => *name < cert.name_table.len(),
        GlobalRef::Imported {
            import_index, name, ..
        } => *import_index < cert.imports.len() && *name < cert.name_table.len(),
        GlobalRef::Local { decl_index } => *decl_index < cert.declarations.len(),
        GlobalRef::LocalGenerated { decl_index, name } => {
            *decl_index < cert.declarations.len() && *name < cert.name_table.len()
        }
    };
    if valid {
        Ok(())
    } else {
        Err(CertError::DecodeError)
    }
}

fn add_level_root(
    roots: &mut RootAccumulator,
    root: LevelId,
    depths: &[usize],
    expansions: &[usize],
) -> Result<(), CertError> {
    roots.max_depth = roots.max_depth.max(checked_child(depths, root)?);
    add_root(roots, checked_child(expansions, root)?)
}

fn add_term_root(
    roots: &mut RootAccumulator,
    root: TermId,
    depths: &[usize],
    expansions: &[usize],
) -> Result<(), CertError> {
    roots.max_depth = roots.max_depth.max(checked_child(depths, root)?);
    add_root(roots, checked_child(expansions, root)?)
}

fn add_root(roots: &mut RootAccumulator, expansion: usize) -> Result<(), CertError> {
    if expansion > MAX_ROOT_EXPANDED_NODES {
        return Err(exceeded(
            StructuralLimitKind::RootExpandedNodes,
            MAX_ROOT_EXPANDED_NODES,
            MAX_ROOT_EXPANDED_NODES + 1,
        ));
    }
    roots.max_root_expansion = roots.max_root_expansion.max(expansion);
    roots.certificate_expansion = roots
        .certificate_expansion
        .saturating_add(expansion)
        .min(MAX_CERTIFICATE_EXPANDED_NODES + 1);
    if roots.certificate_expansion > MAX_CERTIFICATE_EXPANDED_NODES {
        return Err(exceeded(
            StructuralLimitKind::CertificateExpandedNodes,
            MAX_CERTIFICATE_EXPANDED_NODES,
            MAX_CERTIFICATE_EXPANDED_NODES + 1,
        ));
    }
    Ok(())
}

fn decl_constraints(decl: &DeclPayload) -> &[crate::UniverseConstraintSpec] {
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

pub(crate) fn build_closure_summary(
    cert: &ModuleCert,
    cost: StructuralCost,
    imports: &[&crate::VerifiedModule],
) -> Result<StructuralClosureSummary, CertError> {
    let mut summaries = Vec::new();
    summaries
        .try_reserve_exact(imports.len())
        .map_err(|_| CertError::DecodeError)?;
    summaries.extend(imports.iter().map(|import| &import.structural_closure));
    merge_closure_summaries(
        StructuralIdentity {
            module: cert.header.module.clone(),
            export_hash: cert.hashes.export_hash,
            certificate_hash: cert.hashes.certificate_hash,
        },
        cost.certificate_expansion,
        &summaries,
    )
}

fn merge_closure_summaries(
    current: StructuralIdentity,
    current_expansion: usize,
    imports: &[&StructuralClosureSummary],
) -> Result<StructuralClosureSummary, CertError> {
    let mut modules = BTreeMap::new();
    for import in imports {
        for (identity, expansion) in &import.modules {
            if let Some(previous) = modules.insert(identity.clone(), *expansion) {
                if previous != *expansion {
                    return Err(CertError::DecodeError);
                }
            }
        }
    }
    if let Some(previous) = modules.insert(current, current_expansion) {
        if previous != current_expansion {
            return Err(CertError::DecodeError);
        }
    }
    if modules.len() > MAX_CLOSURE_MODULES {
        return Err(exceeded(
            StructuralLimitKind::ClosureModules,
            MAX_CLOSURE_MODULES,
            modules.len(),
        ));
    }
    let total = modules.values().copied().fold(0usize, |sum, expansion| {
        sum.saturating_add(expansion)
            .min(MAX_CLOSURE_EXPANDED_NODES + 1)
    });
    if total > MAX_CLOSURE_EXPANDED_NODES {
        return Err(exceeded(
            StructuralLimitKind::ClosureExpandedNodes,
            MAX_CLOSURE_EXPANDED_NODES,
            MAX_CLOSURE_EXPANDED_NODES + 1,
        ));
    }
    Ok(StructuralClosureSummary { modules })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AxiomReport, CertHeader, DeclCert, DeclHashes, ModuleHashes};

    fn certificate_with_level_root(level_table: Vec<LevelNode>, root: LevelId) -> ModuleCert {
        ModuleCert {
            header: CertHeader {
                format: crate::FORMAT.to_string(),
                core_spec: crate::CORE_SPEC.to_string(),
                module: Name(vec!["StructuralTest".to_string()]),
            },
            imports: vec![],
            name_table: vec![Name(vec!["root".to_string()])],
            level_table,
            term_table: vec![TermNode::Sort(root)],
            declarations: vec![DeclCert {
                decl: DeclPayload::Axiom {
                    name: 0,
                    universe_params: vec![],
                    ty: 0,
                },
                dependencies: vec![],
                axiom_dependencies: vec![],
                hashes: DeclHashes {
                    decl_interface_hash: [0; 32],
                    decl_certificate_hash: [0; 32],
                },
            }],
            export_block: vec![],
            axiom_report: AxiomReport {
                per_declaration: vec![],
                module_axioms: vec![],
                core_features: vec![],
            },
            hashes: ModuleHashes {
                export_hash: [0; 32],
                axiom_report_hash: [0; 32],
                certificate_hash: [0; 32],
            },
        }
    }

    fn doubling_levels(steps: usize) -> Vec<LevelNode> {
        let mut levels = vec![LevelNode::Zero];
        for index in 0..steps {
            levels.push(LevelNode::Max(index, index));
        }
        levels
    }

    #[test]
    fn doubling_dag_rejects_root_expansion_before_materialization() {
        let levels = doubling_levels(20);
        let cert = certificate_with_level_root(levels.clone(), levels.len() - 1);
        assert_eq!(
            structural_preflight(&cert),
            Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::RootExpandedNodes,
                limit: MAX_ROOT_EXPANDED_NODES,
                observed: MAX_ROOT_EXPANDED_NODES + 1,
            })
        );
    }

    #[test]
    fn combined_depth_rejects_limit_plus_one() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut levels = vec![LevelNode::Zero];
                for index in 0..MAX_STRUCTURAL_DEPTH {
                    levels.push(LevelNode::Succ(index));
                }
                let cert = certificate_with_level_root(levels.clone(), levels.len() - 1);
                assert_eq!(
                    structural_preflight(&cert),
                    Err(CertError::StructuralLimitExceeded {
                        kind: StructuralLimitKind::StructuralDepth,
                        limit: MAX_STRUCTURAL_DEPTH,
                        observed: MAX_STRUCTURAL_DEPTH + 1,
                    })
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn dangling_child_precedes_earlier_depth_overage() {
        let mut levels = vec![LevelNode::Zero];
        for index in 0..MAX_STRUCTURAL_DEPTH {
            levels.push(LevelNode::Succ(index));
        }
        levels.push(LevelNode::Succ(levels.len() + 1));
        let cert = certificate_with_level_root(levels, 0);
        assert_eq!(structural_preflight(&cert), Err(CertError::DecodeError));
    }

    #[test]
    fn dangling_term_global_ref_precedes_depth_overage() {
        let mut cert = certificate_with_level_root(vec![LevelNode::Zero], 0);
        let mut terms = vec![TermNode::BVar(0)];
        for index in 0..MAX_STRUCTURAL_DEPTH {
            terms.push(TermNode::Lam { ty: 0, body: index });
        }
        terms.push(TermNode::Const {
            global_ref: GlobalRef::Local {
                decl_index: cert.declarations.len(),
            },
            levels: vec![],
        });
        cert.term_table = terms;
        if let DeclPayload::Axiom { ty, .. } = &mut cert.declarations[0].decl {
            *ty = 0;
        }

        assert_eq!(structural_preflight(&cert), Err(CertError::DecodeError));
    }

    #[test]
    fn repeated_roots_enforce_certificate_total_boundary() {
        let levels = doubling_levels(18);
        let mut cert = certificate_with_level_root(levels.clone(), levels.len() - 1);
        let declaration = cert.declarations[0].clone();
        cert.declarations = vec![declaration.clone(); 32];
        let cost = structural_preflight(&cert).unwrap();
        assert_eq!(cost.certificate_expansion, MAX_CERTIFICATE_EXPANDED_NODES);

        cert.declarations.push(declaration);
        assert_eq!(
            structural_preflight(&cert),
            Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::CertificateExpandedNodes,
                limit: MAX_CERTIFICATE_EXPANDED_NODES,
                observed: MAX_CERTIFICATE_EXPANDED_NODES + 1,
            })
        );
    }

    #[test]
    fn corpus_fixture_freezes_every_profile_limit() {
        let fixture = include_str!("../../../testdata/certificate-structural-limits-maxima.tsv");
        let expected = BTreeMap::from([
            ("certificate_bytes", MAX_CERTIFICATE_BYTES),
            ("imports", MAX_IMPORTS),
            ("name_table_entries", MAX_NAME_TABLE_ENTRIES),
            ("level_table_nodes", MAX_LEVEL_TABLE_NODES),
            ("term_table_nodes", MAX_TERM_TABLE_NODES),
            ("declarations", MAX_DECLARATIONS),
            ("exports", MAX_EXPORTS),
            ("nested_vector_entries", MAX_NESTED_VECTOR_ENTRIES),
            ("structural_depth", MAX_STRUCTURAL_DEPTH),
            ("root_expanded_nodes", MAX_ROOT_EXPANDED_NODES),
            ("certificate_expanded_nodes", MAX_CERTIFICATE_EXPANDED_NODES),
            ("closure_modules", MAX_CLOSURE_MODULES),
            ("closure_expanded_nodes", MAX_CLOSURE_EXPANDED_NODES),
        ]);
        let actual = fixture
            .lines()
            .skip(1)
            .map(|line| {
                let mut columns = line.split('\t');
                let kind = columns.next().unwrap();
                let limit = columns.next().unwrap().parse::<usize>().unwrap();
                (kind, limit)
            })
            .collect::<BTreeMap<_, _>>();

        assert_eq!(actual, expected);
    }

    fn structural_identity(index: usize) -> StructuralIdentity {
        StructuralIdentity {
            module: Name(vec![format!("Closure{index:05}")]),
            export_hash: [index as u8; 32],
            certificate_hash: [(index >> 8) as u8; 32],
        }
    }

    #[test]
    fn closure_module_limit_counts_unique_identities_once() {
        let mut imported = StructuralClosureSummary::default();
        for index in 0..(MAX_CLOSURE_MODULES - 1) {
            imported.modules.insert(structural_identity(index), 0);
        }
        merge_closure_summaries(
            structural_identity(MAX_CLOSURE_MODULES + 1),
            0,
            &[&imported],
        )
        .unwrap();

        imported
            .modules
            .insert(structural_identity(MAX_CLOSURE_MODULES), 0);
        assert_eq!(
            merge_closure_summaries(
                structural_identity(MAX_CLOSURE_MODULES + 1),
                0,
                &[&imported],
            ),
            Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::ClosureModules,
                limit: MAX_CLOSURE_MODULES,
                observed: MAX_CLOSURE_MODULES + 1,
            })
        );
    }

    #[test]
    fn closure_expansion_limit_accepts_exact_and_rejects_plus_one() {
        let mut imported = StructuralClosureSummary::default();
        for index in 0..4 {
            imported
                .modules
                .insert(structural_identity(index), MAX_CERTIFICATE_EXPANDED_NODES);
        }
        merge_closure_summaries(structural_identity(10), 0, &[&imported]).unwrap();
        assert_eq!(
            merge_closure_summaries(structural_identity(10), 1, &[&imported]),
            Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::ClosureExpandedNodes,
                limit: MAX_CLOSURE_EXPANDED_NODES,
                observed: MAX_CLOSURE_EXPANDED_NODES + 1,
            })
        );
    }
}

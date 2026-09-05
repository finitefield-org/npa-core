use std::collections::{BTreeMap, BTreeSet};

use crate::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalTransparencyDependencies {
    pub(crate) interface_dependencies: Vec<DependencyEntry>,
    pub(crate) opaque_definition_indices: BTreeSet<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LocalTransparencyBudget {
    certificate_expanded_nodes: usize,
}

impl LocalTransparencyBudget {
    fn charge(&mut self, root_expanded_nodes: &mut usize, depth: usize) -> Result<()> {
        if depth > MAX_STRUCTURAL_DEPTH {
            return Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::StructuralDepth,
                limit: MAX_STRUCTURAL_DEPTH,
                observed: MAX_STRUCTURAL_DEPTH + 1,
            });
        }
        *root_expanded_nodes = root_expanded_nodes
            .saturating_add(1)
            .min(MAX_ROOT_EXPANDED_NODES + 1);
        if *root_expanded_nodes > MAX_ROOT_EXPANDED_NODES {
            return Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::RootExpandedNodes,
                limit: MAX_ROOT_EXPANDED_NODES,
                observed: MAX_ROOT_EXPANDED_NODES + 1,
            });
        }
        self.certificate_expanded_nodes = self
            .certificate_expanded_nodes
            .saturating_add(1)
            .min(MAX_CERTIFICATE_EXPANDED_NODES + 1);
        if self.certificate_expanded_nodes > MAX_CERTIFICATE_EXPANDED_NODES {
            return Err(CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::CertificateExpandedNodes,
                limit: MAX_CERTIFICATE_EXPANDED_NODES,
                observed: MAX_CERTIFICATE_EXPANDED_NODES + 1,
            });
        }
        Ok(())
    }
}

pub(crate) fn local_transparency_dependencies(
    _version: CertificateFormatVersion,
    current_decl_index: usize,
    root: &DeclPayload,
    declarations: &[DeclCert],
    term_table: &[TermNode],
    budget: &mut LocalTransparencyBudget,
) -> Result<LocalTransparencyDependencies> {
    let mut root_expanded_nodes = 0usize;
    let direct_refs = scan_term_roots(
        root_term_ids(root),
        1,
        term_table,
        budget,
        &mut root_expanded_nodes,
    )?;
    let allow_self = matches!(
        root,
        DeclPayload::Inductive { .. }
            | DeclPayload::InductiveConstrained { .. }
            | DeclPayload::MutualInductiveBlock { .. }
    );
    let direct_refs = direct_refs
        .into_iter()
        .filter(|(global_ref, _)| {
            !matches!(
                global_ref,
                GlobalRef::Local { decl_index }
                    | GlobalRef::LocalGenerated { decl_index, .. }
                    if allow_self && *decl_index == current_decl_index
            )
        })
        .collect::<BTreeMap<_, _>>();

    let mut opaque_definition_indices = BTreeSet::new();
    let mut pending = BTreeMap::new();
    for (global_ref, depth) in &direct_refs {
        queue_local_reference(global_ref, *depth, current_decl_index, &mut pending);
    }
    let mut visited = BTreeSet::new();
    while let Some((decl_index, reference_depth)) =
        pending.iter().next().map(|(index, depth)| (*index, *depth))
    {
        pending.remove(&decl_index);
        if !visited.insert(decl_index) {
            continue;
        }
        let Some(declaration) = declarations.get(decl_index) else {
            continue;
        };
        if is_opaque_definition(&declaration.decl) {
            opaque_definition_indices.insert(decl_index);
        }
        let refs = scan_term_roots(
            referenced_term_ids(&declaration.decl),
            reference_depth.saturating_add(1),
            term_table,
            budget,
            &mut root_expanded_nodes,
        )?;
        for (global_ref, depth) in refs {
            queue_local_reference(&global_ref, depth, current_decl_index, &mut pending);
        }
    }

    let interface_dependencies = direct_refs
        .into_keys()
        .filter(|global_ref| {
            !matches!(
                global_ref,
                GlobalRef::Local { decl_index }
                    if opaque_definition_indices.contains(decl_index)
            )
        })
        .map(|global_ref| {
            let decl_interface_hash = interface_hash_for_reference(&global_ref, declarations)?;
            DependencyEntry::checked_interface(global_ref, decl_interface_hash)
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(LocalTransparencyDependencies {
        interface_dependencies,
        opaque_definition_indices,
    })
}

pub(crate) fn complete_local_transparency_dependencies(
    closure: &LocalTransparencyDependencies,
    current_decl_index: usize,
    declarations: &[DeclCert],
) -> Result<Vec<DependencyEntry>> {
    let mut dependencies = closure
        .interface_dependencies
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    for decl_index in &closure.opaque_definition_indices {
        dependencies.insert(DependencyEntry::checked_local_implementation(
            GlobalRef::Local {
                decl_index: *decl_index,
            },
            current_decl_index,
            declarations,
        )?);
    }
    Ok(dependencies.into_iter().collect())
}

pub(crate) fn validate_local_implementation_entries(
    current_decl_index: usize,
    dependencies: &[DependencyEntry],
    declarations: &[DeclCert],
) -> Result<BTreeSet<usize>> {
    let mut actual = BTreeSet::new();
    for dependency in dependencies
        .iter()
        .filter(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
    {
        let global_ref = dependency.global_ref().clone();
        let GlobalRef::Local { decl_index } = global_ref else {
            return invalid_dependency(
                current_decl_index,
                dependency.global_ref().clone(),
                LocalImplementationDependencyErrorReason::WrongReferenceKind,
            );
        };
        let Some(target) = declarations.get(decl_index) else {
            return invalid_dependency(
                current_decl_index,
                GlobalRef::Local { decl_index },
                LocalImplementationDependencyErrorReason::TargetNotEarlier,
            );
        };
        if decl_index >= current_decl_index {
            return invalid_dependency(
                current_decl_index,
                GlobalRef::Local { decl_index },
                LocalImplementationDependencyErrorReason::TargetNotEarlier,
            );
        }
        if !is_opaque_definition(&target.decl) {
            return invalid_dependency(
                current_decl_index,
                GlobalRef::Local { decl_index },
                LocalImplementationDependencyErrorReason::TargetNotOpaque,
            );
        }
        if dependency.decl_interface_hash() != target.hashes.decl_interface_hash {
            return invalid_dependency(
                current_decl_index,
                GlobalRef::Local { decl_index },
                LocalImplementationDependencyErrorReason::InterfaceHashMismatch,
            );
        }
        if dependency.decl_certificate_hash() != Some(target.hashes.decl_certificate_hash) {
            return invalid_dependency(
                current_decl_index,
                GlobalRef::Local { decl_index },
                LocalImplementationDependencyErrorReason::CertificateHashMismatch,
            );
        }
        actual.insert(decl_index);
    }

    Ok(actual)
}

pub(crate) fn validate_local_implementation_closure(
    current_decl_index: usize,
    actual: &BTreeSet<usize>,
    expected_opaque_definition_indices: &BTreeSet<usize>,
) -> Result<()> {
    if let Some(decl_index) = expected_opaque_definition_indices
        .difference(actual)
        .next()
        .copied()
    {
        return invalid_dependency(
            current_decl_index,
            GlobalRef::Local { decl_index },
            LocalImplementationDependencyErrorReason::MissingImplementationDependency,
        );
    }
    if let Some(decl_index) = actual
        .difference(expected_opaque_definition_indices)
        .next()
        .copied()
    {
        return invalid_dependency(
            current_decl_index,
            GlobalRef::Local { decl_index },
            LocalImplementationDependencyErrorReason::SurplusImplementationDependency,
        );
    }
    Ok(())
}

/// Encode a dependency set for dependency-selective cache identity.
///
/// Entries are sorted and deduplicated canonically. Ordinary edges commit to their reference and
/// interface hash; local implementation edges additionally commit to the target certificate hash.
pub fn dependency_selective_fingerprint_canonical_bytes(
    dependencies: &[DependencyEntry],
) -> Vec<u8> {
    let dependencies = dependencies
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut out = Vec::new();
    encode_dependency_entries_with_format_to(
        &mut out,
        &dependencies,
        CertificateFormatVersion::V0_4_0,
    );
    out
}

fn invalid_dependency<T>(
    decl_index: usize,
    global_ref: GlobalRef,
    reason: LocalImplementationDependencyErrorReason,
) -> Result<T> {
    Err(CertError::InvalidLocalImplementationDependency {
        decl_index,
        global_ref,
        reason,
    })
}

fn queue_local_reference(
    global_ref: &GlobalRef,
    depth: usize,
    current_decl_index: usize,
    pending: &mut BTreeMap<usize, usize>,
) {
    let decl_index = match global_ref {
        GlobalRef::Local { decl_index } | GlobalRef::LocalGenerated { decl_index, .. } => {
            *decl_index
        }
        GlobalRef::Imported { .. } | GlobalRef::Builtin { .. } => return,
    };
    if decl_index >= current_decl_index {
        return;
    }
    pending
        .entry(decl_index)
        .and_modify(|existing| *existing = (*existing).min(depth))
        .or_insert(depth);
}

fn interface_hash_for_reference(global_ref: &GlobalRef, declarations: &[DeclCert]) -> Result<Hash> {
    match global_ref {
        GlobalRef::Builtin {
            decl_interface_hash,
            ..
        }
        | GlobalRef::Imported {
            decl_interface_hash,
            ..
        } => Ok(*decl_interface_hash),
        GlobalRef::Local { decl_index } | GlobalRef::LocalGenerated { decl_index, .. } => {
            declarations
                .get(*decl_index)
                .map(|declaration| declaration.hashes.decl_interface_hash)
                .ok_or_else(|| CertError::DependencyCycle {
                    name: Name::from_dotted(format!("local.{decl_index}")),
                })
        }
    }
}

fn is_opaque_definition(decl: &DeclPayload) -> bool {
    matches!(
        decl,
        DeclPayload::Def {
            reducibility: CertReducibility::Opaque,
            ..
        } | DeclPayload::DefConstrained {
            reducibility: CertReducibility::Opaque,
            ..
        }
    )
}

fn root_term_ids(decl: &DeclPayload) -> Vec<TermId> {
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

fn referenced_term_ids(decl: &DeclPayload) -> Vec<TermId> {
    match decl {
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
            let mut roots = vec![*ty];
            let _ = reducibility;
            roots.push(*value);
            roots
        }
        DeclPayload::Theorem { ty, .. } | DeclPayload::TheoremConstrained { ty, .. } => vec![*ty],
        _ => root_term_ids(decl),
    }
}

fn scan_term_roots(
    roots: Vec<TermId>,
    base_depth: usize,
    term_table: &[TermNode],
    budget: &mut LocalTransparencyBudget,
    root_expanded_nodes: &mut usize,
) -> Result<BTreeMap<GlobalRef, usize>> {
    let mut roots = roots;
    roots.sort_unstable();
    let mut pending = roots
        .into_iter()
        .rev()
        .map(|root| (root, base_depth))
        .collect::<Vec<_>>();
    let mut refs = BTreeMap::new();
    while let Some((term_id, depth)) = pending.pop() {
        budget.charge(root_expanded_nodes, depth)?;
        match term_table.get(term_id).ok_or(CertError::DecodeError)? {
            TermNode::Sort(_) | TermNode::BVar(_) => {}
            TermNode::Const { global_ref, .. } => {
                refs.entry(global_ref.clone())
                    .and_modify(|existing: &mut usize| *existing = (*existing).min(depth))
                    .or_insert(depth);
            }
            TermNode::App(fun, arg) => {
                pending.push((*arg, depth.saturating_add(1)));
                pending.push((*fun, depth.saturating_add(1)));
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                pending.push((*body, depth.saturating_add(1)));
                pending.push((*ty, depth.saturating_add(1)));
            }
        }
    }
    Ok(refs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn definition(value: TermId, reducibility: CertReducibility) -> DeclPayload {
        DeclPayload::Def {
            name: 0,
            universe_params: vec![],
            ty: 0,
            value,
            reducibility,
        }
    }

    fn declaration(value: TermId, reducibility: CertReducibility, hash_byte: u8) -> DeclCert {
        DeclCert {
            decl: definition(value, reducibility),
            dependencies: vec![],
            axiom_dependencies: vec![],
            hashes: DeclHashes {
                decl_interface_hash: [hash_byte; 32],
                decl_certificate_hash: [hash_byte.wrapping_add(1); 32],
            },
        }
    }

    fn linear_reducible_chain(length: usize) -> (Vec<TermNode>, Vec<DeclCert>, DeclPayload) {
        let mut terms = vec![TermNode::Sort(0)];
        let mut declarations = Vec::with_capacity(length);
        declarations.push(declaration(0, CertReducibility::Opaque, 1));
        for decl_index in 1..length {
            terms.push(TermNode::Const {
                global_ref: GlobalRef::Local {
                    decl_index: decl_index - 1,
                },
                levels: vec![],
            });
            declarations.push(declaration(
                decl_index,
                CertReducibility::Reducible,
                decl_index as u8,
            ));
        }
        terms.push(TermNode::Const {
            global_ref: GlobalRef::Local {
                decl_index: length - 1,
            },
            levels: vec![],
        });
        let root = definition(length, CertReducibility::Reducible);
        (terms, declarations, root)
    }

    #[test]
    fn local_transparency_iterative_chain_is_stack_safe_and_deterministic() {
        let (terms, declarations, root) = linear_reducible_chain(4_096);
        let compute = || {
            local_transparency_dependencies(
                CertificateFormatVersion::V0_4_0,
                declarations.len(),
                &root,
                &declarations,
                &terms,
                &mut LocalTransparencyBudget::default(),
            )
            .unwrap()
        };
        let first = compute();
        let second = compute();

        assert_eq!(first, second);
        assert_eq!(first.opaque_definition_indices, [0].into());
        assert_eq!(first.interface_dependencies.len(), 1);
    }

    #[test]
    fn local_transparency_reference_depth_uses_existing_structural_limit() {
        let length = MAX_STRUCTURAL_DEPTH + 2;
        let (terms, declarations, root) = linear_reducible_chain(length);
        let err = local_transparency_dependencies(
            CertificateFormatVersion::V0_4_0,
            declarations.len(),
            &root,
            &declarations,
            &terms,
            &mut LocalTransparencyBudget::default(),
        )
        .unwrap_err();

        assert!(matches!(
            err,
            CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::StructuralDepth,
                limit: MAX_STRUCTURAL_DEPTH,
                observed,
            } if observed == MAX_STRUCTURAL_DEPTH + 1
        ));
    }

    #[test]
    fn local_transparency_expansion_uses_existing_root_and_certificate_limits() {
        let mut budget = LocalTransparencyBudget::default();
        let mut root_expanded_nodes = MAX_ROOT_EXPANDED_NODES;
        let root_err = budget.charge(&mut root_expanded_nodes, 1).unwrap_err();
        assert!(matches!(
            root_err,
            CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::RootExpandedNodes,
                limit: MAX_ROOT_EXPANDED_NODES,
                observed,
            } if observed == MAX_ROOT_EXPANDED_NODES + 1
        ));

        let mut budget = LocalTransparencyBudget {
            certificate_expanded_nodes: MAX_CERTIFICATE_EXPANDED_NODES,
        };
        let mut root_expanded_nodes = 0;
        let certificate_err = budget.charge(&mut root_expanded_nodes, 1).unwrap_err();
        assert!(matches!(
            certificate_err,
            CertError::StructuralLimitExceeded {
                kind: StructuralLimitKind::CertificateExpandedNodes,
                limit: MAX_CERTIFICATE_EXPANDED_NODES,
                observed,
            } if observed == MAX_CERTIFICATE_EXPANDED_NODES + 1
        ));
    }
}

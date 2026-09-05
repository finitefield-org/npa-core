use sha2::{Digest, Sha256};

use npa_kernel::{Expr, Level};

use crate::*;

pub(crate) fn term_hash_impl(cert: &ModuleCert, term: TermId) -> Result<Hash> {
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table())?;
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes)?;
    term_hashes.get(term).copied().ok_or(CertError::DecodeError)
}

pub(crate) fn core_expr_canonical_bytes_impl(expr: &Expr) -> Vec<u8> {
    let mut out = Vec::new();
    encode_core_expr_to(&mut out, expr);
    out
}

pub(crate) fn core_expr_hash_impl(expr: &Expr) -> Hash {
    hash_with_domain(b"NPA-CORE-EXPR-0.1", &core_expr_canonical_bytes_impl(expr))
}

pub(crate) fn universe_constraints_canonical_bytes_impl(
    universe_params: &[String],
    constraints: &[npa_kernel::UniverseConstraint],
) -> Result<Vec<u8>> {
    let delta =
        npa_kernel::level::validate_universe_params(universe_params).map_err(CertError::Kernel)?;
    npa_kernel::level::ensure_universe_constraints_wf(&delta, constraints)
        .map_err(CertError::Kernel)?;
    let mut out = Vec::new();
    encode_uvar_to(&mut out, universe_params.len() as u64);
    for param in universe_params {
        encode_name_to(&mut out, &Name::from_dotted(param));
    }
    encode_uvar_to(&mut out, constraints.len() as u64);
    for constraint in constraints {
        encode_core_level_to(&mut out, &constraint.lhs);
        out.push(match constraint.relation {
            npa_kernel::UniverseConstraintRelation::Le => 0x00,
            npa_kernel::UniverseConstraintRelation::Eq => 0x01,
        });
        encode_core_level_to(&mut out, &constraint.rhs);
    }
    Ok(out)
}

pub(crate) fn universe_constraints_hash_impl(
    universe_params: &[String],
    constraints: &[npa_kernel::UniverseConstraint],
) -> Result<Hash> {
    Ok(hash_with_domain(
        b"NPA-UNIVERSE-CONSTRAINTS-0.1",
        &universe_constraints_canonical_bytes_impl(universe_params, constraints)?,
    ))
}

pub(crate) fn axiom_policy_canonical_bytes_impl(policy: &AxiomPolicy) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"NPA-AXIOM-POLICY-CANONICAL-BYTES-0.1");
    out.push(0x00);
    out.push(match policy.mode {
        TrustMode::Normal => 0x00,
        TrustMode::HighTrust => 0x01,
    });
    out.push(0x01);
    out.push(u8::from(policy.deny_sorry));
    out.push(0x02);
    encode_uvar_to(&mut out, policy.allowlisted_axioms.len() as u64);
    for axiom in &policy.allowlisted_axioms {
        encode_name_to(&mut out, axiom);
    }
    out.push(0x03);
    encode_uvar_to(&mut out, policy.supported_core_features.len() as u64);
    for feature in &policy.supported_core_features {
        encode_policy_string_to(&mut out, feature.as_str());
    }
    out
}

pub(crate) fn axiom_policy_hash_impl(policy: &AxiomPolicy) -> Hash {
    hash_with_domain(
        b"NPA-AXIOM-POLICY-HASH-0.1",
        &axiom_policy_canonical_bytes_impl(policy),
    )
}

fn encode_policy_string_to(out: &mut Vec<u8>, value: &str) {
    encode_uvar_to(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_core_expr_to(out: &mut Vec<u8>, expr: &Expr) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Sort(level) => {
                out.push(0x00);
                encode_core_level_to(out, level);
            }
            Expr::BVar(index) => {
                out.push(0x01);
                encode_uvar_to(out, u64::from(*index));
            }
            Expr::Const { name, levels } => {
                out.push(0x02);
                encode_name_to(out, &Name::from_dotted(name));
                encode_uvar_to(out, levels.len() as u64);
                for level in levels {
                    encode_core_level_to(out, level);
                }
            }
            Expr::App(fun, arg) => {
                out.push(0x03);
                pending.push(arg);
                pending.push(fun);
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                out.push(if matches!(expr, Expr::Lam { .. }) {
                    0x04
                } else {
                    0x05
                });
                pending.push(body);
                pending.push(ty);
            }
        }
    }
}

fn encode_core_level_to(out: &mut Vec<u8>, level: &Level) {
    let mut pending = vec![npa_kernel::level::normalize_level(level.clone())];
    while let Some(level) = pending.pop() {
        match level {
            Level::Zero => out.push(0x00),
            Level::Succ(inner) => {
                out.push(0x01);
                pending.push(*inner);
            }
            Level::Max(lhs, rhs) => {
                out.push(0x02);
                pending.push(*rhs);
                pending.push(*lhs);
            }
            Level::IMax(lhs, rhs) => {
                out.push(0x03);
                pending.push(*rhs);
                pending.push(*lhs);
            }
            Level::Param(name) => {
                out.push(0x04);
                encode_name_to(out, &Name::from_dotted(name));
            }
        }
    }
}
pub(crate) fn build_export_block(
    declarations: &[DeclCert],
    term_table: &[TermNode],
    term_hashes: &[Hash],
) -> Result<ExportBlock> {
    let mut entries = Vec::new();
    for decl in declarations {
        let export_constraints = decl_export_universe_constraints(&decl.decl);
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
                ..
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
                let ty = inductive_export_type_term_id(term_table, params, indices, *sort)?;
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
                        term_table,
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

fn decl_export_universe_constraints(decl: &DeclPayload) -> &[UniverseConstraintSpec] {
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

pub(crate) fn inductive_export_type_term_id(
    term_table: &[TermNode],
    params: &[BinderType],
    indices: &[BinderType],
    sort: LevelId,
) -> Result<TermId> {
    let mut body = term_table
        .iter()
        .position(|term| matches!(term, TermNode::Sort(level) if *level == sort))
        .ok_or(CertError::DecodeError)?;
    for binder in params.iter().chain(indices).rev() {
        body = term_table
            .iter()
            .position(|term| {
                matches!(
                    term,
                    TermNode::Pi { ty, body: pi_body } if *ty == binder.ty && *pi_body == body
                )
            })
            .ok_or(CertError::DecodeError)?;
    }
    Ok(body)
}

pub(crate) struct DeclHashTables<'a> {
    pub(crate) terms: &'a [TermNode],
    pub(crate) level_hashes: &'a [Hash],
    pub(crate) term_hashes: &'a [Hash],
    pub(crate) names: &'a [Name],
}

pub(crate) fn compute_decl_hashes(
    version: CertificateFormatVersion,
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    tables: DeclHashTables<'_>,
) -> Result<DeclHashes> {
    let interface_dependencies = interface_dependencies_for_decl(decl, dependencies, tables.terms)?;
    let iface = hash_with_domain(
        b"NPA-DECL-IFACE-0.1",
        &decl_interface_payload(
            decl,
            &interface_dependencies,
            axiom_dependencies,
            tables.level_hashes,
            tables.term_hashes,
            tables.names,
        )?,
    );
    let cert = hash_with_domain(
        version.declaration_certificate_domain(),
        &decl_certificate_payload(
            version,
            decl,
            iface,
            dependencies,
            axiom_dependencies,
            tables.term_hashes,
        )?,
    );
    Ok(DeclHashes {
        decl_interface_hash: iface,
        decl_certificate_hash: cert,
    })
}

fn decl_interface_payload(
    decl: &DeclPayload,
    interface_dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    level_hashes: &[Hash],
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => {
            out.push(0x00);
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            encode_dependency_entries_to(&mut out, interface_dependencies);
        }
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            out.push(0x10);
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            encode_reducibility_to(&mut out, *reducibility);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
            if *reducibility == CertReducibility::Reducible {
                out.extend(term_hashes.get(*value).ok_or(CertError::DecodeError)?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            encode_reducibility_to(&mut out, *reducibility);
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
            if *reducibility == CertReducibility::Reducible {
                out.extend(term_hashes.get(*value).ok_or(CertError::DecodeError)?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes)?;
            out.extend(term_hashes.get(*ty).ok_or(CertError::DecodeError)?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_uvar_to(&mut out, params.len() as u64);
            for param in params {
                out.extend(term_hashes.get(param.ty).ok_or(CertError::DecodeError)?);
            }
            encode_uvar_to(&mut out, indices.len() as u64);
            for index in indices {
                out.extend(term_hashes.get(index.ty).ok_or(CertError::DecodeError)?);
            }
            out.extend(level_hashes.get(*sort).ok_or(CertError::DecodeError)?);
            encode_constructor_specs_to(&mut out, constructors, term_hashes, names)?;
            out.extend(generated_recursor_signature_hash(
                recursor.as_ref(),
                term_hashes,
                names,
            )?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes)?;
            encode_uvar_to(&mut out, params.len() as u64);
            for param in params {
                out.extend(term_hashes.get(param.ty).ok_or(CertError::DecodeError)?);
            }
            encode_uvar_to(&mut out, indices.len() as u64);
            for index in indices {
                out.extend(term_hashes.get(index.ty).ok_or(CertError::DecodeError)?);
            }
            out.extend(level_hashes.get(*sort).ok_or(CertError::DecodeError)?);
            encode_constructor_specs_to(&mut out, constructors, term_hashes, names)?;
            out.extend(generated_recursor_signature_hash(
                recursor.as_ref(),
                term_hashes,
                names,
            )?);
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
            encode_name_id_to(&mut out, names, *name)?;
            encode_name_ids_to(&mut out, names, universe_params)?;
            encode_universe_constraint_specs_to(&mut out, universe_constraints, level_hashes)?;
            encode_mutual_inductive_specs_to(
                &mut out,
                inductives,
                level_hashes,
                term_hashes,
                names,
            )?;
            encode_dependency_entries_to(&mut out, interface_dependencies);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
    }
    Ok(out)
}

fn encode_mutual_inductive_specs_to(
    out: &mut Vec<u8>,
    inductives: &[MutualInductiveSpec],
    level_hashes: &[Hash],
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<()> {
    encode_uvar_to(out, inductives.len() as u64);
    for inductive in inductives {
        encode_name_id_to(out, names, inductive.name)?;
        encode_uvar_to(out, inductive.params.len() as u64);
        for param in &inductive.params {
            out.extend(term_hashes.get(param.ty).ok_or(CertError::DecodeError)?);
        }
        encode_uvar_to(out, inductive.indices.len() as u64);
        for index in &inductive.indices {
            out.extend(term_hashes.get(index.ty).ok_or(CertError::DecodeError)?);
        }
        out.extend(
            level_hashes
                .get(inductive.sort)
                .ok_or(CertError::DecodeError)?,
        );
        encode_constructor_specs_to(out, &inductive.constructors, term_hashes, names)?;
        out.extend(generated_recursor_signature_hash(
            inductive.recursor.as_ref(),
            term_hashes,
            names,
        )?);
        out.extend(generated_computation_rule_hash(inductive.recursor.as_ref()));
    }
    Ok(())
}

fn encode_universe_constraint_specs_to(
    out: &mut Vec<u8>,
    constraints: &[UniverseConstraintSpec],
    level_hashes: &[Hash],
) -> Result<()> {
    encode_uvar_to(out, constraints.len() as u64);
    for constraint in constraints {
        out.extend(
            level_hashes
                .get(constraint.lhs)
                .ok_or(CertError::DecodeError)?,
        );
        out.push(match constraint.relation {
            npa_kernel::UniverseConstraintRelation::Le => 0x00,
            npa_kernel::UniverseConstraintRelation::Eq => 0x01,
        });
        out.extend(
            level_hashes
                .get(constraint.rhs)
                .ok_or(CertError::DecodeError)?,
        );
    }
    Ok(())
}

fn encode_constructor_specs_to(
    out: &mut Vec<u8>,
    constructors: &[ConstructorSpec],
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<()> {
    encode_uvar_to(out, constructors.len() as u64);
    for constructor in constructors {
        encode_name_id_to(out, names, constructor.name)?;
        out.extend(
            term_hashes
                .get(constructor.ty)
                .ok_or(CertError::DecodeError)?,
        );
    }
    Ok(())
}

pub(crate) fn generated_recursor_signature_hash(
    recursor: Option<&RecursorSpec>,
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<Hash> {
    Ok(hash_with_domain(
        b"NPA-GEN-REC-SIG-0.1",
        &generated_recursor_signature_payload(recursor, term_hashes, names)?,
    ))
}

fn generated_recursor_signature_payload(
    recursor: Option<&RecursorSpec>,
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    match recursor {
        Some(recursor) => {
            out.push(0x01);
            encode_name_id_to(&mut out, names, recursor.name)?;
            encode_name_ids_to(&mut out, names, &recursor.universe_params)?;
            out.extend(term_hashes.get(recursor.ty).ok_or(CertError::DecodeError)?);
        }
        None => out.push(0x00),
    }
    Ok(out)
}

pub(crate) fn generated_computation_rule_hash(recursor: Option<&RecursorSpec>) -> Hash {
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

fn interface_dependencies_for_decl(
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    term_table: &[TermNode],
) -> Result<Vec<DependencyEntry>> {
    let mut refs = std::collections::BTreeSet::new();
    for term in interface_term_ids(decl) {
        collect_global_refs_from_term(term_table, term, &mut refs)?;
    }
    dependencies
        .iter()
        .filter(|dependency| refs.contains(dependency.global_ref()))
        .map(|dependency| {
            DependencyEntry::checked_interface(
                dependency.global_ref().clone(),
                dependency.decl_interface_hash(),
            )
        })
        .collect::<Result<std::collections::BTreeSet<_>>>()
        .map(|dependencies| dependencies.into_iter().collect())
}

fn interface_term_ids(decl: &DeclPayload) -> Vec<TermId> {
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

fn collect_global_refs_from_term(
    terms: &[TermNode],
    term: TermId,
    refs: &mut std::collections::BTreeSet<GlobalRef>,
) -> Result<()> {
    match terms.get(term).ok_or(CertError::DecodeError)? {
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
    }
    Ok(())
}

fn decl_certificate_payload(
    version: CertificateFormatVersion,
    decl: &DeclPayload,
    interface_hash: Hash,
    dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    term_hashes: &[Hash],
) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    out.extend(interface_hash);
    match decl {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => {
            encode_axiom_refs_to(&mut out, axiom_dependencies)
        }
        DeclPayload::Def { value, .. } | DeclPayload::DefConstrained { value, .. } => {
            out.extend(term_hashes.get(*value).ok_or(CertError::DecodeError)?);
            encode_dependency_entries_with_format_to(&mut out, dependencies, version);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::Inductive { .. } | DeclPayload::InductiveConstrained { .. } => {
            encode_dependency_entries_with_format_to(&mut out, dependencies, version);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::MutualInductiveBlock { .. } => {
            encode_dependency_entries_with_format_to(&mut out, dependencies, version);
            encode_axiom_refs_to(&mut out, axiom_dependencies);
        }
        DeclPayload::Theorem { proof, .. } | DeclPayload::TheoremConstrained { proof, .. } => {
            out.extend(term_hashes.get(*proof).ok_or(CertError::DecodeError)?);
            encode_dependency_entries_with_format_to(&mut out, dependencies, version);
        }
    }
    Ok(out)
}

fn encode_name_id_to(out: &mut Vec<u8>, names: &[Name], name: NameId) -> Result<()> {
    encode_name_to(out, names.get(name).ok_or(CertError::DecodeError)?);
    Ok(())
}

fn encode_name_ids_to(out: &mut Vec<u8>, names: &[Name], values: &[NameId]) -> Result<()> {
    encode_uvar_to(out, values.len() as u64);
    for value in values {
        encode_name_id_to(out, names, *value)?;
    }
    Ok(())
}

pub(crate) fn compute_level_hashes(levels: &[LevelNode], names: &[Name]) -> Result<Vec<Hash>> {
    let mut hashes = Vec::with_capacity(levels.len());
    for level in levels {
        let payload = level_node_key(level, &hashes, names)?;
        hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &payload));
    }
    Ok(hashes)
}

pub(crate) fn compute_term_hashes(terms: &[TermNode], level_hashes: &[Hash]) -> Result<Vec<Hash>> {
    let mut hashes = Vec::with_capacity(terms.len());
    for term in terms {
        let payload = term_node_key(term, &hashes, level_hashes)?;
        hashes.push(hash_with_domain(b"NPA-TERM-0.1", &payload));
    }
    Ok(hashes)
}

/// Private byte sink used by canonical table-key encoders.
///
/// Keeping emission independent of allocation lets validation compare and hash
/// one exact encoding without maintaining a second encoder.
pub(crate) trait CanonicalKeySink {
    fn write(&mut self, bytes: &[u8]);
}

impl CanonicalKeySink for Vec<u8> {
    fn write(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

fn encode_uvar_to_key_sink(sink: &mut impl CanonicalKeySink, mut value: u64) {
    let mut bytes = [0_u8; 10];
    let mut len = 0;
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        bytes[len] = byte;
        len += 1;
        if value == 0 {
            break;
        }
    }
    sink.write(&bytes[..len]);
}

fn encode_string_to_key_sink(sink: &mut impl CanonicalKeySink, value: &str) {
    encode_uvar_to_key_sink(sink, value.len() as u64);
    sink.write(value.as_bytes());
}

fn encode_name_to_key_sink(sink: &mut impl CanonicalKeySink, name: &Name) {
    encode_uvar_to_key_sink(sink, name.0.len() as u64);
    for component in &name.0 {
        encode_string_to_key_sink(sink, component);
    }
}

fn encode_global_ref_to_key_sink(sink: &mut impl CanonicalKeySink, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            sink.write(&[0x03]);
            encode_uvar_to_key_sink(sink, *name as u64);
            sink.write(decl_interface_hash);
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            sink.write(&[0x00]);
            encode_uvar_to_key_sink(sink, *import_index as u64);
            encode_uvar_to_key_sink(sink, *name as u64);
            sink.write(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            sink.write(&[0x01]);
            encode_uvar_to_key_sink(sink, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            sink.write(&[0x02]);
            encode_uvar_to_key_sink(sink, *decl_index as u64);
            encode_uvar_to_key_sink(sink, *name as u64);
        }
    }
}

pub(crate) fn encode_level_node_key_to(
    sink: &mut impl CanonicalKeySink,
    level: &LevelNode,
    child_hashes: &[Hash],
    names: &[Name],
) -> Result<()> {
    match level {
        LevelNode::Zero => sink.write(&[0x00]),
        LevelNode::Succ(inner) => {
            sink.write(&[0x01]);
            sink.write(child_hashes.get(*inner).ok_or(CertError::DecodeError)?);
        }
        LevelNode::Max(lhs, rhs) => {
            sink.write(&[0x02]);
            sink.write(child_hashes.get(*lhs).ok_or(CertError::DecodeError)?);
            sink.write(child_hashes.get(*rhs).ok_or(CertError::DecodeError)?);
        }
        LevelNode::IMax(lhs, rhs) => {
            sink.write(&[0x03]);
            sink.write(child_hashes.get(*lhs).ok_or(CertError::DecodeError)?);
            sink.write(child_hashes.get(*rhs).ok_or(CertError::DecodeError)?);
        }
        LevelNode::Param(name) => {
            sink.write(&[0x04]);
            encode_name_to_key_sink(sink, names.get(*name).ok_or(CertError::DecodeError)?);
        }
    }
    Ok(())
}

pub(crate) fn encode_term_node_key_to(
    sink: &mut impl CanonicalKeySink,
    term: &TermNode,
    child_hashes: &[Hash],
    level_hashes: &[Hash],
) -> Result<()> {
    match term {
        TermNode::Sort(level) => {
            sink.write(&[0x00]);
            sink.write(level_hashes.get(*level).ok_or(CertError::DecodeError)?);
        }
        TermNode::BVar(index) => {
            sink.write(&[0x01]);
            encode_uvar_to_key_sink(sink, *index as u64);
        }
        TermNode::Const { global_ref, levels } => {
            sink.write(&[0x02]);
            encode_global_ref_to_key_sink(sink, global_ref);
            encode_uvar_to_key_sink(sink, levels.len() as u64);
            for level in levels {
                sink.write(level_hashes.get(*level).ok_or(CertError::DecodeError)?);
            }
        }
        TermNode::App(fun, arg) => {
            sink.write(&[0x03]);
            sink.write(child_hashes.get(*fun).ok_or(CertError::DecodeError)?);
            sink.write(child_hashes.get(*arg).ok_or(CertError::DecodeError)?);
        }
        TermNode::Lam { ty, body } => {
            sink.write(&[0x04]);
            sink.write(child_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            sink.write(child_hashes.get(*body).ok_or(CertError::DecodeError)?);
        }
        TermNode::Pi { ty, body } => {
            sink.write(&[0x05]);
            sink.write(child_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            sink.write(child_hashes.get(*body).ok_or(CertError::DecodeError)?);
        }
    }
    Ok(())
}

pub(crate) fn level_node_key(
    level: &LevelNode,
    child_hashes: &[Hash],
    names: &[Name],
) -> Result<Vec<u8>> {
    let mut payload = Vec::new();
    encode_level_node_key_to(&mut payload, level, child_hashes, names)?;
    Ok(payload)
}

pub(crate) fn term_node_key(
    term: &TermNode,
    child_hashes: &[Hash],
    level_hashes: &[Hash],
) -> Result<Vec<u8>> {
    let mut payload = Vec::new();
    encode_term_node_key_to(&mut payload, term, child_hashes, level_hashes)?;
    Ok(payload)
}

/// Memo of canonical level hashes keyed by level value. Levels are tiny
/// (`Box` children, no stable pointer identity), so value keying is cheap
/// while still collapsing the many repeated `Sort`/`Const` level hashes one
/// module build performs.
pub(crate) type LevelHashMemo = std::collections::HashMap<CanonLevel, Hash>;

/// Computes the canonical key bytes of `level`, memoizing child hashes.
/// Byte-for-byte identical to the unmemoized recursion: the key encodes
/// child hashes, so reusing memoized child hashes leaves it unchanged.
pub(crate) fn canon_level_key(
    level: &CanonLevel,
    names: &[Name],
    _memo: &mut LevelHashMemo,
) -> Result<Vec<u8>> {
    let root = level as *const CanonLevel as usize;
    let mut hashes = std::collections::HashMap::<usize, Hash>::new();
    let mut pending = vec![(level, false)];
    let mut root_key = None;
    while let Some((level, exiting)) = pending.pop() {
        let pointer = level as *const CanonLevel as usize;
        if hashes.contains_key(&pointer) {
            continue;
        }
        if !exiting {
            pending.push((level, true));
            match level {
                CanonLevel::Zero | CanonLevel::Param(_) => {}
                CanonLevel::Succ(inner) => pending.push((inner, false)),
                CanonLevel::Max(lhs, rhs) | CanonLevel::IMax(lhs, rhs) => {
                    pending.push((rhs, false));
                    pending.push((lhs, false));
                }
            }
            continue;
        }
        let mut payload = Vec::new();
        match level {
            CanonLevel::Zero => payload.push(0x00),
            CanonLevel::Succ(inner) => {
                payload.push(0x01);
                payload.extend(
                    hashes
                        .get(&(inner.as_ref() as *const CanonLevel as usize))
                        .ok_or(CertError::DecodeError)?,
                );
            }
            CanonLevel::Max(lhs, rhs) => {
                payload.push(0x02);
                payload.extend(
                    hashes
                        .get(&(lhs.as_ref() as *const CanonLevel as usize))
                        .ok_or(CertError::DecodeError)?,
                );
                payload.extend(
                    hashes
                        .get(&(rhs.as_ref() as *const CanonLevel as usize))
                        .ok_or(CertError::DecodeError)?,
                );
            }
            CanonLevel::IMax(lhs, rhs) => {
                payload.push(0x03);
                payload.extend(
                    hashes
                        .get(&(lhs.as_ref() as *const CanonLevel as usize))
                        .ok_or(CertError::DecodeError)?,
                );
                payload.extend(
                    hashes
                        .get(&(rhs.as_ref() as *const CanonLevel as usize))
                        .ok_or(CertError::DecodeError)?,
                );
            }
            CanonLevel::Param(name) => {
                payload.push(0x04);
                encode_name_to(
                    &mut payload,
                    names.get(*name).ok_or(CertError::DecodeError)?,
                );
            }
        }
        let hash = canon_level_hash_from_key(&payload);
        if pointer == root {
            root_key = Some(payload);
        }
        hashes.insert(pointer, hash);
    }
    root_key.ok_or(CertError::DecodeError)
}

pub(crate) fn canon_level_hash(
    level: &CanonLevel,
    names: &[Name],
    memo: &mut LevelHashMemo,
) -> Result<Hash> {
    let key = canon_level_key(level, names, memo)?;
    Ok(canon_level_hash_from_key(&key))
}

pub(crate) fn canon_level_hash_from_key(key: &[u8]) -> Hash {
    hash_with_domain(b"NPA-LEVEL-0.1", key)
}

pub(crate) fn canon_term_hash_from_key(key: &[u8]) -> Hash {
    hash_with_domain(b"NPA-TERM-0.1", key)
}

/// Memo of canonical term height and Merkle hash, keyed by `Arc` pointer
/// identity (the anchored `Arc` keeps the key's node alive, so a pointer is
/// never reused while its entry exists). Canonicalization preserves subtree
/// sharing, so pointer identity hits on the same shared nodes a structural
/// key would, without paying a deep comparison per probe. Structurally
/// equal but separately allocated nodes hash twice, to identical results.
pub(crate) type TermHashMemo =
    std::collections::HashMap<usize, (std::sync::Arc<CanonTerm>, usize, Hash)>;

/// Computes the canonical sort key `(height, key bytes)` of `term`,
/// memoizing child heights and hashes. Produces byte-for-byte the same key
/// as the unmemoized recursion: the key encodes child hashes, so reusing
/// memoized child hashes leaves the encoding unchanged.
pub(crate) fn canon_term_height_and_key(
    term: &CanonTerm,
    names: &[Name],
    memo: &mut TermHashMemo,
    level_memo: &mut LevelHashMemo,
) -> Result<(usize, Vec<u8>)> {
    let mut payload = Vec::new();
    let height = match term {
        CanonTerm::Sort(level) => {
            payload.push(0x00);
            payload.extend(canon_level_hash(level, names, level_memo)?);
            0
        }
        CanonTerm::BVar(index) => {
            payload.push(0x01);
            encode_uvar_to(&mut payload, *index as u64);
            0
        }
        CanonTerm::Const { global_ref, levels } => {
            payload.push(0x02);
            encode_global_ref_to(&mut payload, global_ref);
            encode_uvar_to(&mut payload, levels.len() as u64);
            for level in levels {
                payload.extend(canon_level_hash(level, names, level_memo)?);
            }
            0
        }
        CanonTerm::App(fun, arg) => {
            payload.push(0x03);
            let (fun_height, fun_hash) = canon_term_height_and_hash(fun, names, memo, level_memo)?;
            payload.extend(fun_hash);
            let (arg_height, arg_hash) = canon_term_height_and_hash(arg, names, memo, level_memo)?;
            payload.extend(arg_hash);
            fun_height.max(arg_height) + 1
        }
        CanonTerm::Lam { ty, body } => {
            payload.push(0x04);
            let (ty_height, ty_hash) = canon_term_height_and_hash(ty, names, memo, level_memo)?;
            payload.extend(ty_hash);
            let (body_height, body_hash) =
                canon_term_height_and_hash(body, names, memo, level_memo)?;
            payload.extend(body_hash);
            ty_height.max(body_height) + 1
        }
        CanonTerm::Pi { ty, body } => {
            payload.push(0x05);
            let (ty_height, ty_hash) = canon_term_height_and_hash(ty, names, memo, level_memo)?;
            payload.extend(ty_hash);
            let (body_height, body_hash) =
                canon_term_height_and_hash(body, names, memo, level_memo)?;
            payload.extend(body_hash);
            ty_height.max(body_height) + 1
        }
    };
    Ok((height, payload))
}

pub(crate) fn canon_term_height_and_hash(
    term: &std::sync::Arc<CanonTerm>,
    names: &[Name],
    memo: &mut TermHashMemo,
    level_memo: &mut LevelHashMemo,
) -> Result<(usize, Hash)> {
    let root_key = std::sync::Arc::as_ptr(term) as usize;
    if let Some(&(_, height, hash)) = memo.get(&root_key) {
        return Ok((height, hash));
    }
    let mut pending = vec![(std::sync::Arc::clone(term), false)];
    while let Some((node, exiting)) = pending.pop() {
        let key = std::sync::Arc::as_ptr(&node) as usize;
        if memo.contains_key(&key) {
            continue;
        }
        if !exiting {
            pending.push((std::sync::Arc::clone(&node), true));
            match node.as_ref() {
                CanonTerm::Sort(_) | CanonTerm::BVar(_) | CanonTerm::Const { .. } => {}
                CanonTerm::App(fun, arg) => {
                    pending.push((std::sync::Arc::clone(arg), false));
                    pending.push((std::sync::Arc::clone(fun), false));
                }
                CanonTerm::Lam { ty, body } | CanonTerm::Pi { ty, body } => {
                    pending.push((std::sync::Arc::clone(body), false));
                    pending.push((std::sync::Arc::clone(ty), false));
                }
            }
            continue;
        }
        let (height, payload) = canon_term_height_and_key(&node, names, memo, level_memo)?;
        let hash = canon_term_hash_from_key(&payload);
        memo.insert(key, (node, height, hash));
    }
    memo.get(&root_key)
        .map(|(_, height, hash)| (*height, *hash))
        .ok_or(CertError::DecodeError)
}

pub(crate) fn level_height(level: &CanonLevel) -> usize {
    let mut maximum = 0usize;
    let mut pending = vec![(level, 0usize)];
    while let Some((level, height)) = pending.pop() {
        maximum = maximum.max(height);
        match level {
            CanonLevel::Zero | CanonLevel::Param(_) => {}
            CanonLevel::Succ(inner) => pending.push((inner, height.saturating_add(1))),
            CanonLevel::Max(lhs, rhs) | CanonLevel::IMax(lhs, rhs) => {
                let child_height = height.saturating_add(1);
                pending.push((rhs, child_height));
                pending.push((lhs, child_height));
            }
        }
    }
    maximum
}

pub(crate) fn hash_with_domain(domain: &[u8], payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

#[cfg(test)]
mod iterative_hash_tests {
    use super::*;

    #[test]
    fn canonical_term_hash_is_stack_safe_and_memoizes_shared_dag() {
        let leaf = std::sync::Arc::new(CanonTerm::BVar(0));
        let mut term = std::sync::Arc::clone(&leaf);
        for _ in 0..8_192 {
            term = std::sync::Arc::new(CanonTerm::Lam {
                ty: std::sync::Arc::clone(&leaf),
                body: term,
            });
        }
        let mut term_memo = TermHashMemo::new();
        let mut level_memo = LevelHashMemo::new();
        let result = canon_term_height_and_hash(&term, &[], &mut term_memo, &mut level_memo);
        assert_eq!(result.map(|(height, _)| height), Ok(8_192));
        assert_eq!(term_memo.len(), 8_193);

        // Every adversarial node is intentionally anchored in the memo. Keep those anchors alive
        // rather than exercising the standard library's recursive final `Arc` destruction path.
        std::mem::forget(term_memo);
        std::mem::forget(term);
        std::mem::forget(leaf);
    }

    #[test]
    fn canonical_level_hash_is_stack_safe_at_structural_depth_limit() {
        let mut level = CanonLevel::Zero;
        for _ in 0..8_192 {
            level = CanonLevel::Succ(Box::new(level));
        }
        let mut memo = LevelHashMemo::new();
        let result = canon_level_hash(&level, &[], &mut memo);
        assert!(result.is_ok());
        assert_eq!(level_height(&level), 8_192);
        std::mem::forget(level);
    }

    #[test]
    fn raw_core_expr_bytes_and_hash_are_stack_safe_at_structural_depth_limit() {
        let mut expr = Expr::bvar(0);
        for _ in 0..8_192 {
            expr = Expr::lam("_", Expr::bvar(0), expr);
        }

        let bytes = core_expr_canonical_bytes_impl(&expr);
        assert_eq!(bytes.first(), Some(&0x04));
        assert_ne!(core_expr_hash_impl(&expr), [0; 32]);

        // The adversarial Arc spine is intentionally retained; ordinary Arc
        // destruction is outside the canonical walker being exercised.
        std::mem::forget(expr);
    }
}

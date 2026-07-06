use sha2::{Digest, Sha256};

use npa_kernel::{Expr, Level};

use crate::*;

pub(crate) fn term_hash_impl(cert: &ModuleCert, term: TermId) -> Result<Hash> {
    let level_hashes = compute_level_hashes(&cert.level_table, &cert.name_table)?;
    let term_hashes = compute_term_hashes(&cert.term_table, &level_hashes)?;
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
            encode_core_expr_to(out, fun);
            encode_core_expr_to(out, arg);
        }
        Expr::Lam { ty, body, .. } => {
            out.push(0x04);
            encode_core_expr_to(out, ty);
            encode_core_expr_to(out, body);
        }
        Expr::Pi { ty, body, .. } => {
            out.push(0x05);
            encode_core_expr_to(out, ty);
            encode_core_expr_to(out, body);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            out.push(0x06);
            encode_core_expr_to(out, ty);
            encode_core_expr_to(out, value);
            encode_core_expr_to(out, body);
        }
    }
}

fn encode_core_level_to(out: &mut Vec<u8>, level: &Level) {
    match npa_kernel::level::normalize_level(level.clone()) {
        Level::Zero => out.push(0x00),
        Level::Succ(inner) => {
            out.push(0x01);
            encode_core_level_to(out, &inner);
        }
        Level::Max(lhs, rhs) => {
            out.push(0x02);
            encode_core_level_to(out, &lhs);
            encode_core_level_to(out, &rhs);
        }
        Level::IMax(lhs, rhs) => {
            out.push(0x03);
            encode_core_level_to(out, &lhs);
            encode_core_level_to(out, &rhs);
        }
        Level::Param(name) => {
            out.push(0x04);
            encode_name_to(out, &Name::from_dotted(name));
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

pub(crate) fn compute_decl_hashes(
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    axiom_dependencies: &[AxiomRef],
    term_table: &[TermNode],
    level_hashes: &[Hash],
    term_hashes: &[Hash],
    names: &[Name],
) -> Result<DeclHashes> {
    let interface_dependencies = interface_dependencies_for_decl(decl, dependencies, term_table)?;
    let iface = hash_with_domain(
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
    let cert = hash_with_domain(
        b"NPA-DECL-CERT-0.1",
        &decl_certificate_payload(decl, iface, dependencies, axiom_dependencies, term_hashes)?,
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
    Ok(dependencies
        .iter()
        .filter(|dependency| refs.contains(&dependency.global_ref))
        .cloned()
        .collect())
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
        TermNode::Let { ty, value, body } => {
            collect_global_refs_from_term(terms, *ty, refs)?;
            collect_global_refs_from_term(terms, *value, refs)?;
            collect_global_refs_from_term(terms, *body, refs)?;
        }
    }
    Ok(())
}

fn decl_certificate_payload(
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
            out.extend(term_hashes.get(*proof).ok_or(CertError::DecodeError)?);
            encode_dependency_entries_to(&mut out, dependencies);
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

pub(crate) fn level_node_key(
    level: &LevelNode,
    child_hashes: &[Hash],
    names: &[Name],
) -> Result<Vec<u8>> {
    let mut payload = Vec::new();
    match level {
        LevelNode::Zero => payload.push(0x00),
        LevelNode::Succ(inner) => {
            payload.push(0x01);
            payload.extend(child_hashes.get(*inner).ok_or(CertError::DecodeError)?);
        }
        LevelNode::Max(lhs, rhs) => {
            payload.push(0x02);
            payload.extend(child_hashes.get(*lhs).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*rhs).ok_or(CertError::DecodeError)?);
        }
        LevelNode::IMax(lhs, rhs) => {
            payload.push(0x03);
            payload.extend(child_hashes.get(*lhs).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*rhs).ok_or(CertError::DecodeError)?);
        }
        LevelNode::Param(name) => {
            payload.push(0x04);
            encode_name_to(
                &mut payload,
                names.get(*name).ok_or(CertError::DecodeError)?,
            );
        }
    }
    Ok(payload)
}

pub(crate) fn term_node_key(
    term: &TermNode,
    child_hashes: &[Hash],
    level_hashes: &[Hash],
) -> Result<Vec<u8>> {
    let mut payload = Vec::new();
    match term {
        TermNode::Sort(level) => {
            payload.push(0x00);
            payload.extend(level_hashes.get(*level).ok_or(CertError::DecodeError)?);
        }
        TermNode::BVar(index) => {
            payload.push(0x01);
            encode_uvar_to(&mut payload, *index as u64);
        }
        TermNode::Const { global_ref, levels } => {
            payload.push(0x02);
            encode_global_ref_to(&mut payload, global_ref);
            encode_uvar_to(&mut payload, levels.len() as u64);
            for level in levels {
                payload.extend(level_hashes.get(*level).ok_or(CertError::DecodeError)?);
            }
        }
        TermNode::App(fun, arg) => {
            payload.push(0x03);
            payload.extend(child_hashes.get(*fun).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*arg).ok_or(CertError::DecodeError)?);
        }
        TermNode::Lam { ty, body } => {
            payload.push(0x04);
            payload.extend(child_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*body).ok_or(CertError::DecodeError)?);
        }
        TermNode::Pi { ty, body } => {
            payload.push(0x05);
            payload.extend(child_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*body).ok_or(CertError::DecodeError)?);
        }
        TermNode::Let { ty, value, body } => {
            payload.push(0x06);
            payload.extend(child_hashes.get(*ty).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*value).ok_or(CertError::DecodeError)?);
            payload.extend(child_hashes.get(*body).ok_or(CertError::DecodeError)?);
        }
    }
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
    memo: &mut LevelHashMemo,
) -> Result<Vec<u8>> {
    let mut payload = Vec::new();
    match level {
        CanonLevel::Zero => payload.push(0x00),
        CanonLevel::Succ(inner) => {
            payload.push(0x01);
            payload.extend(canon_level_hash(inner, names, memo)?);
        }
        CanonLevel::Max(lhs, rhs) => {
            payload.push(0x02);
            payload.extend(canon_level_hash(lhs, names, memo)?);
            payload.extend(canon_level_hash(rhs, names, memo)?);
        }
        CanonLevel::IMax(lhs, rhs) => {
            payload.push(0x03);
            payload.extend(canon_level_hash(lhs, names, memo)?);
            payload.extend(canon_level_hash(rhs, names, memo)?);
        }
        CanonLevel::Param(name) => {
            payload.push(0x04);
            encode_name_to(
                &mut payload,
                names.get(*name).ok_or(CertError::DecodeError)?,
            );
        }
    }
    Ok(payload)
}

pub(crate) fn canon_level_hash(
    level: &CanonLevel,
    names: &[Name],
    memo: &mut LevelHashMemo,
) -> Result<Hash> {
    if let Some(hash) = memo.get(level) {
        return Ok(*hash);
    }
    let key = canon_level_key(level, names, memo)?;
    let hash = canon_level_hash_from_key(&key);
    memo.insert(level.clone(), hash);
    Ok(hash)
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
        CanonTerm::Let { ty, value, body } => {
            payload.push(0x06);
            let (ty_height, ty_hash) = canon_term_height_and_hash(ty, names, memo, level_memo)?;
            payload.extend(ty_hash);
            let (value_height, value_hash) =
                canon_term_height_and_hash(value, names, memo, level_memo)?;
            payload.extend(value_hash);
            let (body_height, body_hash) =
                canon_term_height_and_hash(body, names, memo, level_memo)?;
            payload.extend(body_hash);
            ty_height.max(value_height).max(body_height) + 1
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
    let key = std::sync::Arc::as_ptr(term) as usize;
    if let Some(&(_, height, hash)) = memo.get(&key) {
        return Ok((height, hash));
    }
    let (height, payload) = canon_term_height_and_key(term, names, memo, level_memo)?;
    let hash = canon_term_hash_from_key(&payload);
    memo.insert(key, (std::sync::Arc::clone(term), height, hash));
    Ok((height, hash))
}

pub(crate) fn level_height(level: &CanonLevel) -> usize {
    match level {
        CanonLevel::Zero | CanonLevel::Param(_) => 0,
        CanonLevel::Succ(inner) => level_height(inner) + 1,
        CanonLevel::Max(lhs, rhs) | CanonLevel::IMax(lhs, rhs) => {
            level_height(lhs).max(level_height(rhs)) + 1
        }
    }
}

pub(crate) fn hash_with_domain(domain: &[u8], payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

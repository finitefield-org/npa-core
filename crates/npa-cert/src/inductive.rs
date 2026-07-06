use npa_kernel::expr::collect_apps;
use npa_kernel::level::{level_eq, levels_eq};
use npa_kernel::positivity::approved_nested_functor;
use npa_kernel::{
    ConstructorDecl, Decl, Expr, InductiveDecl, Level, MutualInductiveBlock, RecursorDecl,
    RecursorRules,
};

use crate::{CertError, CoreModule, DeclPayload, Hash, Name, Result};

/// Result of the deterministic certificate inductive artifact profile classifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveArtifactProfileCheckV1 {
    /// The declaration is in the MVP recursor profile.
    SupportedMvpRecursor,
    /// The declaration needs a recursor profile outside the MVP.
    UnsupportedMvpRecursorProfile(UnsupportedMvpRecursorProfileV1),
}

/// Unsupported recursor profile reason returned by the certificate classifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnsupportedMvpRecursorProfileV1 {
    /// The declaration would require a large-elimination profile.
    LargeEliminationRequired,
    /// The declaration would require mutual or nested recursor generation.
    MutualOrNestedRecursorRequired,
    /// The declaration has an eliminator shape not handled by the MVP generator.
    UnsupportedEliminatorShape,
}

/// Generated inductive artifact hashes committed by canonical certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveGeneratedArtifactHashesV1 {
    /// Hash of the generated recursor signature, when a recursor is present.
    pub recursor_signature_hash: Option<Hash>,
    /// Hash of the generated iota-rule metadata, when a recursor is present.
    pub iota_rules_hash: Option<Hash>,
}

/// Classify whether an inductive declaration is supported by the certificate MVP artifact generator.
pub fn classify_inductive_artifact_profile_v1(
    base: &InductiveDecl,
) -> InductiveArtifactProfileCheckV1 {
    if base.recursor.is_some() {
        return InductiveArtifactProfileCheckV1::UnsupportedMvpRecursorProfile(
            UnsupportedMvpRecursorProfileV1::UnsupportedEliminatorShape,
        );
    }
    for constructor in &base.constructors {
        let (domains, _) = peel_pi_domains(&constructor.ty);
        for (domain_index, domain) in domains.iter().enumerate() {
            let allowed = domain_index >= base.params.len()
                && recursive_occurrences_strictly_positive(
                    &base.name,
                    &base.universe_params,
                    base.params.len(),
                    base.indices.len(),
                    domain,
                    domain_index,
                );
            if !allowed && contains_const(domain, &base.name) {
                return InductiveArtifactProfileCheckV1::UnsupportedMvpRecursorProfile(
                    UnsupportedMvpRecursorProfileV1::MutualOrNestedRecursorRequired,
                );
            }
        }
    }
    InductiveArtifactProfileCheckV1::SupportedMvpRecursor
}

/// Generate the certificate MVP inductive artifacts for a supported base declaration.
pub fn generate_inductive_artifacts_v1(base: &InductiveDecl) -> Result<InductiveDecl> {
    if classify_inductive_artifact_profile_v1(base)
        != InductiveArtifactProfileCheckV1::SupportedMvpRecursor
    {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&base.name),
        });
    }
    let rules = RecursorRules::new(
        base.params.len() + 1,
        base.params.len() + 1 + base.constructors.len() + base.indices.len(),
    );
    let recursor_universe_params = recursor_universe_params(base);
    let recursor_ty = generated_recursor_type(base, &recursor_universe_params, &rules)?;
    let mut final_decl = base.clone();
    final_decl.recursor = Some(RecursorDecl::with_rules(
        format!("{}.rec", base.name),
        recursor_universe_params,
        recursor_ty,
        rules,
    ));
    Ok(final_decl)
}

/// Generate deterministic recursors for a supported mutual inductive block.
pub fn generate_mutual_inductive_artifacts_v1(
    base: &MutualInductiveBlock,
) -> Result<MutualInductiveBlock> {
    if base.inductives.is_empty() || base.inductives.iter().any(|data| data.recursor.is_some()) {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&base.name),
        });
    }
    let param_count = base.inductives[0].params.len();
    for data in &base.inductives {
        if data.universe_params != base.universe_params
            || !data.universe_constraints.is_empty()
            || data.params != base.inductives[0].params
        {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&base.name),
            });
        }
    }
    for data in &base.inductives {
        for constructor in &data.constructors {
            let (domains, _) = peel_pi_domains(&constructor.ty);
            for (domain_index, domain) in domains.iter().enumerate() {
                let allowed = domain_index >= param_count
                    && mutual_recursive_occurrences_strictly_positive(base, domain, domain_index);
                if !allowed
                    && contains_any_const(
                        domain,
                        base.inductives.iter().map(|data| data.name.as_str()),
                    )
                {
                    return Err(CertError::InductiveGeneratedArtifactMismatch {
                        name: Name::from_dotted(&base.name),
                    });
                }
            }
        }
    }

    let mut final_block = base.clone();
    let recursor_universe_params = recursor_universe_params(&base.inductives[0]);
    for index in 0..final_block.inductives.len() {
        let rules = generated_mutual_recursor_rules(&final_block, &final_block.inductives[index]);
        let recursor_ty =
            generated_mutual_recursor_type(&final_block, index, &recursor_universe_params, &rules)?;
        let name = final_block.inductives[index].name.clone();
        final_block.inductives[index].recursor = Some(RecursorDecl::with_rules(
            format!("{name}.rec"),
            recursor_universe_params.clone(),
            recursor_ty,
            rules,
        ));
    }
    Ok(final_block)
}

/// Return the certificate artifact hashes for a generated inductive declaration.
pub fn inductive_generated_artifact_hashes_v1(
    data: &InductiveDecl,
) -> Result<InductiveGeneratedArtifactHashesV1> {
    let final_decl = if data.recursor.is_some() {
        data.clone()
    } else {
        generate_inductive_artifacts_v1(data)?
    };
    let cert = crate::build_module_cert(
        CoreModule {
            name: Name::from_dotted("__Npa.InductiveArtifactProbe"),
            declarations: vec![Decl::Inductive {
                name: final_decl.name.clone(),
                universe_params: final_decl.universe_params.clone(),
                ty: inductive_type(&final_decl),
                data: Box::new(final_decl),
            }],
        },
        &[],
    )?;
    let term_hashes = (0..cert.term_table.len())
        .map(|term| crate::term_hash(&cert, term))
        .collect::<Result<Vec<_>>>()?;

    for decl in &cert.declarations {
        let recursor = match &decl.decl {
            DeclPayload::Inductive { recursor, .. }
            | DeclPayload::InductiveConstrained { recursor, .. } => recursor.as_ref(),
            _ => None,
        };
        if let Some(recursor) = recursor {
            return Ok(InductiveGeneratedArtifactHashesV1 {
                recursor_signature_hash: Some(crate::generated_recursor_signature_hash(
                    Some(recursor),
                    &term_hashes,
                    &cert.name_table,
                )?),
                iota_rules_hash: Some(crate::generated_computation_rule_hash(Some(recursor))),
            });
        }
    }

    Ok(InductiveGeneratedArtifactHashesV1 {
        recursor_signature_hash: None,
        iota_rules_hash: None,
    })
}

pub(crate) fn inductive_type(data: &InductiveDecl) -> Expr {
    let mut term = Expr::sort(data.sort.clone());
    for binder in data.params.iter().chain(&data.indices).rev() {
        term = Expr::pi(binder.name.clone(), binder.ty.clone(), term);
    }
    term
}

fn recursor_universe_params(base: &InductiveDecl) -> Vec<String> {
    let mut params = base.universe_params.clone();
    if level_eq(&base.sort, &Level::zero()) {
        return params;
    }
    let mut index = 0usize;
    loop {
        let candidate = if index == 0 {
            "u".to_owned()
        } else {
            format!("u{index}")
        };
        if !params.iter().any(|param| param == &candidate) {
            params.push(candidate);
            return params;
        }
        index += 1;
    }
}

fn generated_recursor_type(
    base: &InductiveDecl,
    recursor_universe_params: &[String],
    rules: &RecursorRules,
) -> Result<Expr> {
    let param_count = base.params.len();
    let index_count = base.indices.len();
    let mut domains = base
        .params
        .iter()
        .map(|param| param.ty.clone())
        .collect::<Vec<_>>();
    domains.push(motive_domain_expr(
        base,
        expected_motive_level(base, recursor_universe_params),
    )?);

    for (constructor_index, constructor) in base.constructors.iter().enumerate() {
        domains.push(expected_minor_type_expr(
            base,
            param_count,
            index_count,
            constructor,
            constructor_index,
        )?);
    }

    let index_start = domains.len();
    append_index_domains(base, &mut domains)?;
    let major_domain = inductive_target_expr(
        &base.name,
        &base.universe_params,
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
        bvar_for_abs(domains.len(), rules.major_index)?,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn generated_mutual_recursor_type(
    block: &MutualInductiveBlock,
    target_index: usize,
    recursor_universe_params: &[String],
    rules: &RecursorRules,
) -> Result<Expr> {
    let target = block.inductives.get(target_index).ok_or_else(|| {
        CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&block.name),
        }
    })?;
    let param_count = target.params.len();
    let mut domains = target
        .params
        .iter()
        .map(|param| param.ty.clone())
        .collect::<Vec<_>>();

    for family in &block.inductives {
        domains.push(motive_domain_expr(
            family,
            expected_motive_level(family, recursor_universe_params),
        )?);
    }

    let mut constructor_index = 0usize;
    for (family_index, family) in block.inductives.iter().enumerate() {
        for constructor in &family.constructors {
            domains.push(expected_mutual_minor_type_expr(
                block,
                family_index,
                constructor,
                constructor_index,
            )?);
            constructor_index += 1;
        }
    }

    let index_start = domains.len();
    append_index_domains(target, &mut domains)?;
    let major_domain = inductive_target_expr(
        &target.name,
        &target.universe_params,
        domains.len(),
        param_count,
        index_start,
        target.indices.len(),
    )?;
    domains.push(major_domain);
    let index_args = (0..target.indices.len())
        .map(|index| bvar_for_abs(domains.len(), index_start + index))
        .collect::<Result<Vec<_>>>()?;
    let body = motive_app(
        domains.len(),
        param_count + target_index,
        index_args,
        bvar_for_abs(domains.len(), rules.major_index)?,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn generated_mutual_recursor_rules(
    block: &MutualInductiveBlock,
    data: &InductiveDecl,
) -> RecursorRules {
    let minor_start = data.params.len() + block.inductives.len();
    RecursorRules::new(
        minor_start,
        minor_start + mutual_constructor_count(block) + data.indices.len(),
    )
}

fn mutual_constructor_count(block: &MutualInductiveBlock) -> usize {
    block
        .inductives
        .iter()
        .map(|data| data.constructors.len())
        .sum()
}

fn expected_motive_level(base: &InductiveDecl, recursor_universe_params: &[String]) -> Level {
    if level_eq(&base.sort, &Level::zero()) {
        return Level::zero();
    }
    if let Some(param) = recursor_universe_params
        .iter()
        .rev()
        .find(|param| !base.universe_params.contains(*param))
    {
        return Level::param(param.clone());
    }
    recursor_universe_params
        .last()
        .map(|param| Level::param(param.clone()))
        .unwrap_or_else(|| base.sort.clone())
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

fn motive_domain_expr(base: &InductiveDecl, motive_level: Level) -> Result<Expr> {
    let param_count = base.params.len();
    let mut domains = Vec::new();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, binder) in base.indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = param_count + index;
        domains.push(remap_bvars(
            &binder.ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    let target = inductive_target_expr(
        &base.name,
        &base.universe_params,
        param_count + base.indices.len(),
        param_count,
        param_count,
        base.indices.len(),
    )?;
    let body = Expr::pi("_", target, Expr::sort(motive_level));
    Ok(mk_pi_from_domains(domains, body))
}

fn append_index_domains(base: &InductiveDecl, domains: &mut Vec<Expr>) -> Result<()> {
    let param_count = base.params.len();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, binder) in base.indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = domains.len();
        domains.push(remap_bvars(
            &binder.ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    Ok(())
}

fn expected_minor_type_expr(
    base: &InductiveDecl,
    param_count: usize,
    index_count: usize,
    constructor: &ConstructorDecl,
    constructor_index: usize,
) -> Result<Expr> {
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor.ty);
    if constructor_domains.len() < param_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&base.name),
        });
    }
    let constructor_result_indices =
        constructor_result_index_args(base, constructor, &constructor_result)?;

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
            &base.name,
            &base.universe_params,
            param_count,
            index_count,
            field_domain,
            source_ctx_len,
        )? {
            let index_args = direct_recursive_index_args(
                &base.name,
                &base.universe_params,
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

    let levels = base
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let constructor_value = Expr::apps(
        Expr::konst(constructor.name.clone(), levels),
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

fn expected_mutual_minor_type_expr(
    block: &MutualInductiveBlock,
    family_index: usize,
    constructor: &ConstructorDecl,
    constructor_index: usize,
) -> Result<Expr> {
    let owner = block.inductives.get(family_index).ok_or_else(|| {
        CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&block.name),
        }
    })?;
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor.ty);
    let param_count = owner.params.len();
    if constructor_domains.len() < param_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&block.name),
        });
    }
    let constructor_result_indices =
        constructor_result_index_args(owner, constructor, &constructor_result)?;

    let prefix_len = param_count + block.inductives.len() + constructor_index;
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
        )?);

        source_to_target.push(target_ctx_len);
        field_abs.push(target_ctx_len);
        target_ctx_len += 1;

        if let Ok((field_family_index, index_args)) =
            direct_mutual_recursive_index_args(block, field_domain, source_ctx_len)
        {
            let index_args = index_args
                .into_iter()
                .map(|arg| remap_bvars(&arg, source_ctx_len, target_ctx_len, &source_to_target))
                .collect::<Result<Vec<_>>>()?;
            expected_domains.push(motive_app(
                target_ctx_len,
                motive_abs_start + field_family_index,
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

    let levels = owner
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let constructor_value = Expr::apps(
        Expr::konst(constructor.name.clone(), levels),
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
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs_start + family_index,
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

fn recursive_occurrences_strictly_positive(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    domain: &Expr,
    ctx_len: usize,
) -> bool {
    if direct_recursive_index_args(
        inductive_name,
        universe_params,
        param_count,
        index_count,
        domain,
        ctx_len,
    )
    .is_ok()
    {
        return true;
    }
    match domain {
        Expr::Sort(_) | Expr::BVar(_) => true,
        Expr::Const { name, .. } => name != inductive_name,
        Expr::App(_, _) => {
            let (head, args) = collect_apps(domain);
            let Expr::Const { name, .. } = head else {
                return !contains_const(domain, inductive_name);
            };
            let Some(functor) = approved_nested_functor(&name, args.len()) else {
                return !contains_const(domain, inductive_name);
            };
            args.iter().enumerate().all(|(index, arg)| {
                if functor.positive_args.contains(&index) {
                    recursive_occurrences_strictly_positive(
                        inductive_name,
                        universe_params,
                        param_count,
                        index_count,
                        arg,
                        ctx_len,
                    )
                } else {
                    !contains_const(arg, inductive_name)
                }
            })
        }
        Expr::Pi { ty, body, .. } => {
            !contains_const(ty, inductive_name)
                && recursive_occurrences_strictly_positive(
                    inductive_name,
                    universe_params,
                    param_count,
                    index_count,
                    body,
                    ctx_len + 1,
                )
        }
        Expr::Lam { .. } | Expr::Let { .. } => !contains_const(domain, inductive_name),
    }
}

fn mutual_recursive_occurrences_strictly_positive(
    block: &MutualInductiveBlock,
    domain: &Expr,
    ctx_len: usize,
) -> bool {
    if direct_mutual_recursive_index_args(block, domain, ctx_len).is_ok() {
        return true;
    }
    match domain {
        Expr::Sort(_) | Expr::BVar(_) => true,
        Expr::Const { name, .. } => !block.inductives.iter().any(|data| &data.name == name),
        Expr::App(_, _) => {
            let (head, args) = collect_apps(domain);
            let Expr::Const { name, .. } = head else {
                return !contains_any_const(
                    domain,
                    block.inductives.iter().map(|data| data.name.as_str()),
                );
            };
            let Some(functor) = approved_nested_functor(&name, args.len()) else {
                return !contains_any_const(
                    domain,
                    block.inductives.iter().map(|data| data.name.as_str()),
                );
            };
            args.iter().enumerate().all(|(index, arg)| {
                if functor.positive_args.contains(&index) {
                    mutual_recursive_occurrences_strictly_positive(block, arg, ctx_len)
                } else {
                    !contains_any_const(arg, block.inductives.iter().map(|data| data.name.as_str()))
                }
            })
        }
        Expr::Pi { ty, body, .. } => {
            !contains_any_const(ty, block.inductives.iter().map(|data| data.name.as_str()))
                && mutual_recursive_occurrences_strictly_positive(block, body, ctx_len + 1)
        }
        Expr::Lam { .. } | Expr::Let { .. } => !contains_any_const(
            domain,
            block.inductives.iter().map(|data| data.name.as_str()),
        ),
    }
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

fn direct_mutual_recursive_index_args(
    block: &MutualInductiveBlock,
    domain: &Expr,
    ctx_len: usize,
) -> Result<(usize, Vec<Expr>)> {
    for (index, data) in block.inductives.iter().enumerate() {
        if let Ok(indices) = direct_recursive_index_args(
            &data.name,
            &data.universe_params,
            data.params.len(),
            data.indices.len(),
            domain,
            ctx_len,
        ) {
            return Ok((index, indices));
        }
    }
    Err(CertError::InductiveGeneratedArtifactMismatch {
        name: Name::from_dotted(&block.name),
    })
}

fn constructor_result_index_args(
    base: &InductiveDecl,
    constructor: &ConstructorDecl,
    result: &Expr,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(result);
    let levels = match head {
        Expr::Const { name, levels } if name == base.name => levels,
        _ => {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&constructor.name),
            });
        }
    };
    let expected_levels: Vec<_> = base
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != base.params.len() + base.indices.len()
    {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&constructor.name),
        });
    }
    Ok(args[base.params.len()..].to_vec())
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

fn contains_any_const<'a>(expr: &Expr, needles: impl Iterator<Item = &'a str> + Clone) -> bool {
    needles.clone().any(|needle| contains_const(expr, needle))
}

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use npa_kernel::{
    subst::instantiate, Ctx, Env, Error as KernelError, Expr, Level, ResourceLimitKind,
    UniverseContext,
};

use crate::{
    add_decl_to_env, add_verified_module_referenced_imports_to_env, builtin_decl_interface_hash,
    builtin_is_axiom, core_expr_hash, expr_from_term, kernel::universe_constraints_from_specs,
    source_decl_index_for_export_entry, universe_names, verified_module_to_kernel_decls, AxiomRef,
    DeclPayload, ExportEntry, ExportKind, GlobalRef, Hash, ImportEntry, Name, VerifiedModule,
};

/// Fixed resource limits for version 1 theorem-premise analysis.
pub const VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1: VerifiedTheoremPremiseAnalysisLimits =
    VerifiedTheoremPremiseAnalysisLimits {
        telescope_binders_per_theorem: 16_384,
        kernel_whnf_fuel_per_theorem: 1_000_000,
        kernel_conversion_fuel_per_theorem: 1_000_000,
        expression_traversal_states_per_theorem: 1_000_000,
        resolved_global_dependencies_per_theorem: 262_144,
    };

/// Certificate-native structural analysis for one verified public theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTheoremPremiseAnalysis {
    /// Source declaration index inside the verified module.
    pub declaration_index: usize,
    /// Public theorem export name.
    pub export_name: Name,
    /// Verified declaration-interface hash.
    pub decl_interface_hash: Hash,
    /// Structural hash of the complete exported theorem statement.
    pub statement_hash: Hash,
    /// Number of binders in the exposed theorem telescope.
    pub binder_count: usize,
    /// Source-order indices of binders whose domains are sorts.
    pub sort_parameter_indices: Vec<usize>,
    /// Source-order indices of binders that are data parameters.
    pub data_parameter_indices: Vec<usize>,
    /// Proposition-valued premise binders and their checked proof uses.
    pub fact_premises: Vec<VerifiedTheoremFactPremise>,
    /// Structural hash of the exposed theorem conclusion.
    pub conclusion_hash: Hash,
    /// Source-order telescope binders referenced by the conclusion.
    pub conclusion_depends_on_binder_indices: Vec<usize>,
    /// Direct declaration-wide global dependencies.
    pub global_dependencies: Vec<VerifiedTheoremGlobalDependency>,
    /// Verifier-recomputed transitive axiom dependencies.
    pub axiom_dependencies: Vec<AxiomRef>,
}

/// Structural information for one proposition-valued theorem binder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTheoremFactPremise {
    /// Zero-based source-order telescope index.
    pub binder_index: usize,
    /// Structural hash of the reconstructed binder domain.
    pub type_hash: Hash,
    /// Earlier telescope binders referenced by the domain.
    pub depends_on_prior_binder_indices: Vec<usize>,
    /// Distinct checked-proof occurrence kinds in canonical order.
    pub use_sites: Vec<VerifiedTheoremPremiseUseSite>,
}

/// Stable structural position at which a fact premise occurs in a checked proof.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerifiedTheoremPremiseUseSite {
    /// The exposed proof body is exactly the premise variable.
    DirectResult,
    /// The premise variable is the head of the exposed proof application.
    ApplicationHead,
    /// The premise occurs within an application argument.
    ApplicationArgument,
    /// The premise occurs at another proof-term position.
    TermBody,
    /// The premise occurs inside a nested lambda, pi, or let type.
    DependentType,
    /// The premise occurs inside a let-bound value.
    LetValue,
}

/// One direct global dependency of a verified theorem declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTheoremGlobalDependency {
    /// Certificate-native reference to the dependency.
    pub global_ref: GlobalRef,
    /// Expected declaration-interface hash.
    pub decl_interface_hash: Hash,
    /// Resolved declaration kind.
    pub kind: VerifiedTheoremGlobalDependencyKind,
}

/// Stable resolved kind of a direct theorem declaration dependency.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerifiedTheoremGlobalDependencyKind {
    /// Trusted builtin primitive.
    BuiltinPrimitive,
    /// Trusted builtin axiom.
    BuiltinAxiom,
    /// Ordinary definition.
    Definition,
    /// Checked theorem.
    Theorem,
    /// Declared axiom.
    Axiom,
    /// Inductive-family declaration.
    Inductive,
    /// Generated constructor.
    Constructor,
    /// Generated recursor.
    Recursor,
}

/// Deterministic per-theorem analysis limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedTheoremPremiseAnalysisLimits {
    /// Maximum exposed telescope binders.
    pub telescope_binders_per_theorem: usize,
    /// Shared weak-head-reduction fuel.
    pub kernel_whnf_fuel_per_theorem: usize,
    /// Shared definitional-equality fuel.
    pub kernel_conversion_fuel_per_theorem: usize,
    /// Shared reconstructed-expression traversal states.
    pub expression_traversal_states_per_theorem: usize,
    /// Maximum resolved direct global dependencies.
    pub resolved_global_dependencies_per_theorem: usize,
}

/// Stable reason for theorem-premise analysis failure.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedTheoremPremiseAnalysisErrorReason {
    /// The supplied verified imports do not exactly resolve the module import list.
    ImportContextMismatch,
    /// A successfully verified module could not be reconstructed consistently.
    InvalidVerifiedModule,
    /// Telescope binder limit was exhausted.
    TelescopeLimit,
    /// Weak-head-reduction fuel was exhausted.
    WhnfFuelLimit,
    /// Definitional-equality fuel was exhausted.
    ConversionFuelLimit,
    /// Reconstructed-expression traversal limit was exhausted.
    ExpressionTraversalLimit,
    /// Direct global dependency limit was exhausted.
    DependencyLimit,
}

/// Bounded theorem-premise analysis failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTheoremPremiseAnalysisError {
    /// Stable failure reason.
    pub reason: VerifiedTheoremPremiseAnalysisErrorReason,
    /// Source declaration index when the failure is theorem-specific.
    pub declaration_index: Option<usize>,
}

impl fmt::Display for VerifiedTheoremPremiseAnalysisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "verified theorem-premise analysis failed: {:?}",
            self.reason
        )?;
        if let Some(index) = self.declaration_index {
            write!(formatter, " at declaration {index}")?;
        }
        Ok(())
    }
}

impl std::error::Error for VerifiedTheoremPremiseAnalysisError {}

/// Analyze every public local theorem in a verified module.
pub fn analyze_verified_module_theorem_premises(
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    limits: VerifiedTheoremPremiseAnalysisLimits,
) -> std::result::Result<Vec<VerifiedTheoremPremiseAnalysis>, VerifiedTheoremPremiseAnalysisError> {
    let imports = resolve_exact_import_context(module, imports)?;
    let env = analysis_environment(module, &imports)?;
    let mut analyses = Vec::new();

    for export in module
        .export_block
        .iter()
        .filter(|entry| entry.kind == ExportKind::Theorem)
    {
        let declaration_index = source_decl_index_for_export_entry(module, export)
            .map_err(|_| invalid_verified_module(None))?;
        analyses.push(analyze_theorem(
            module,
            &imports,
            &env,
            export,
            declaration_index,
            limits,
        )?);
    }

    analyses.sort_by(|left, right| {
        left.export_name
            .cmp(&right.export_name)
            .then(left.decl_interface_hash.cmp(&right.decl_interface_hash))
    });
    Ok(analyses)
}

fn resolve_exact_import_context<'a>(
    module: &VerifiedModule,
    imports: &[&'a VerifiedModule],
) -> std::result::Result<Vec<&'a VerifiedModule>, VerifiedTheoremPremiseAnalysisError> {
    let mut unique = BTreeSet::new();
    for import in imports {
        if !unique.insert((
            import.module.clone(),
            import.export_hash,
            import.certificate_hash,
        )) {
            return Err(import_context_mismatch());
        }
    }
    if imports.len() != module.imports.len() {
        return Err(import_context_mismatch());
    }

    let mut resolved = Vec::with_capacity(module.imports.len());
    for entry in &module.imports {
        let matches = imports
            .iter()
            .copied()
            .filter(|candidate| import_matches(entry, candidate))
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(import_context_mismatch());
        }
        resolved.push(matches[0]);
    }
    if resolved
        .iter()
        .map(|module| {
            (
                module.module.clone(),
                module.export_hash,
                module.certificate_hash,
            )
        })
        .collect::<BTreeSet<_>>()
        .len()
        != imports.len()
    {
        return Err(import_context_mismatch());
    }
    Ok(resolved)
}

fn import_matches(entry: &ImportEntry, module: &VerifiedModule) -> bool {
    entry.module == module.module
        && entry.export_hash == module.export_hash
        && entry
            .certificate_hash
            .is_none_or(|hash| hash == module.certificate_hash)
}

fn analysis_environment(
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
) -> std::result::Result<Env, VerifiedTheoremPremiseAnalysisError> {
    let mut env = Env::new();
    add_verified_module_referenced_imports_to_env(&mut env, module, imports)
        .map_err(|_| invalid_verified_module(None))?;
    for decl in
        verified_module_to_kernel_decls(module).map_err(|_| invalid_verified_module(None))?
    {
        add_decl_to_env(&mut env, decl).map_err(|_| invalid_verified_module(None))?;
    }
    Ok(env)
}

fn analyze_theorem(
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    env: &Env,
    export: &ExportEntry,
    declaration_index: usize,
    limits: VerifiedTheoremPremiseAnalysisLimits,
) -> std::result::Result<VerifiedTheoremPremiseAnalysis, VerifiedTheoremPremiseAnalysisError> {
    let decl = module
        .declarations
        .get(declaration_index)
        .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
    let (name, universe_params, universe_constraint_specs, ty, proof) = match &decl.decl {
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => (*name, universe_params, &[][..], *ty, *proof),
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
            ..
        } => (
            *name,
            universe_params,
            universe_constraints.as_slice(),
            *ty,
            *proof,
        ),
        _ => return Err(invalid_verified_module(Some(declaration_index))),
    };
    if export.name != name
        || export.decl_interface_hash != decl.hashes.decl_interface_hash
        || export.ty != ty
    {
        return Err(invalid_verified_module(Some(declaration_index)));
    }

    let delta = universe_names(module, universe_params)
        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    let universe_constraints = universe_constraints_from_specs(module, universe_constraint_specs)
        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    let universe_context = UniverseContext::new(delta.clone(), universe_constraints)
        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    let mut whnf_fuel = limits.kernel_whnf_fuel_per_theorem;
    let mut conversion_fuel = limits.kernel_conversion_fuel_per_theorem;
    let mut traversal_states = limits.expression_traversal_states_per_theorem;
    let mut ctx = Ctx::new();
    let mut current =
        expr_from_term(module, ty).map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    let mut domains = Vec::new();
    let mut sort_parameter_indices = Vec::new();
    let mut data_parameter_indices = Vec::new();
    let mut fact_premises = Vec::new();

    loop {
        current = reduce_leading_lets(current, &mut whnf_fuel, declaration_index)?;
        let exposed = env
            .whnf_with_fuel_metered(&ctx, &delta, &current, &mut whnf_fuel)
            .map_err(|error| map_kernel_error(error, declaration_index))?;
        let Expr::Pi { ty, body, .. } = exposed else {
            current = exposed;
            break;
        };
        if domains.len() >= limits.telescope_binders_per_theorem {
            return Err(analysis_error(
                VerifiedTheoremPremiseAnalysisErrorReason::TelescopeLimit,
                Some(declaration_index),
            ));
        }
        let domain = (*ty).clone();
        let binder_index = domains.len();
        let depends_on_prior_binder_indices = collect_outer_binder_indices(
            &domain,
            binder_index,
            &mut traversal_states,
            declaration_index,
        )?;
        let type_hash = core_expr_hash(&domain);
        let domain_whnf = env
            .whnf_with_fuel_metered(&ctx, &delta, &domain, &mut whnf_fuel)
            .map_err(|error| map_kernel_error(error, declaration_index))?;
        if matches!(domain_whnf, Expr::Sort(_)) {
            sort_parameter_indices.push(binder_index);
        } else {
            let inferred = env
                .infer_with_fuel_metered_in_universe_context(
                    &ctx,
                    &universe_context,
                    &domain,
                    &mut whnf_fuel,
                    &mut conversion_fuel,
                )
                .map_err(|error| map_kernel_error(error, declaration_index))?;
            let inferred = env
                .whnf_with_fuel_metered(&ctx, &delta, &inferred, &mut whnf_fuel)
                .map_err(|error| map_kernel_error(error, declaration_index))?;
            if inferred == Expr::Sort(Level::zero()) {
                fact_premises.push(VerifiedTheoremFactPremise {
                    binder_index,
                    type_hash,
                    depends_on_prior_binder_indices,
                    use_sites: Vec::new(),
                });
            } else {
                data_parameter_indices.push(binder_index);
            }
        }
        ctx.push_assumption("_", domain.clone());
        domains.push(domain);
        current = (*body).clone();
    }

    let conclusion_depends_on_binder_indices = collect_outer_binder_indices(
        &current,
        domains.len(),
        &mut traversal_states,
        declaration_index,
    )?;
    let conclusion_hash = core_expr_hash(&current);

    let proof = expr_from_term(module, proof)
        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    let (proof_body, aligned_binders) = align_proof_binders(
        env,
        &delta,
        proof,
        &domains,
        &mut whnf_fuel,
        &mut conversion_fuel,
        declaration_index,
    )?;
    let fact_indices = fact_premises
        .iter()
        .map(|premise| premise.binder_index)
        .collect::<BTreeSet<_>>();
    let uses = collect_fact_premise_uses(
        &proof_body,
        aligned_binders,
        &fact_indices,
        &mut traversal_states,
        declaration_index,
    )?;
    for premise in &mut fact_premises {
        premise.use_sites = uses
            .get(&premise.binder_index)
            .map(|sites| sites.iter().copied().collect())
            .unwrap_or_default();
    }

    if decl.dependencies.len() > limits.resolved_global_dependencies_per_theorem {
        return Err(analysis_error(
            VerifiedTheoremPremiseAnalysisErrorReason::DependencyLimit,
            Some(declaration_index),
        ));
    }
    let global_dependencies = decl
        .dependencies
        .iter()
        .map(|dependency| {
            Ok(VerifiedTheoremGlobalDependency {
                global_ref: dependency.global_ref.clone(),
                decl_interface_hash: dependency.decl_interface_hash,
                kind: resolve_dependency_kind(module, imports, dependency)?,
            })
        })
        .collect::<std::result::Result<Vec<_>, VerifiedTheoremPremiseAnalysisError>>()?;

    if export.axiom_dependencies != decl.axiom_dependencies {
        return Err(invalid_verified_module(Some(declaration_index)));
    }
    let export_name = module
        .name_table
        .get(export.name)
        .cloned()
        .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;

    Ok(VerifiedTheoremPremiseAnalysis {
        declaration_index,
        export_name,
        decl_interface_hash: export.decl_interface_hash,
        statement_hash: export.type_hash,
        binder_count: domains.len(),
        sort_parameter_indices,
        data_parameter_indices,
        fact_premises,
        conclusion_hash,
        conclusion_depends_on_binder_indices,
        global_dependencies,
        axiom_dependencies: export.axiom_dependencies.clone(),
    })
}

fn reduce_leading_lets(
    mut expression: Expr,
    whnf_fuel: &mut usize,
    declaration_index: usize,
) -> std::result::Result<Expr, VerifiedTheoremPremiseAnalysisError> {
    while let Expr::Let { value, body, .. } = expression {
        spend(
            whnf_fuel,
            VerifiedTheoremPremiseAnalysisErrorReason::WhnfFuelLimit,
            declaration_index,
        )?;
        expression = instantiate(&body, &value)
            .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    }
    Ok(expression)
}

fn collect_outer_binder_indices(
    expression: &Expr,
    binder_count: usize,
    traversal_states: &mut usize,
    declaration_index: usize,
) -> std::result::Result<Vec<usize>, VerifiedTheoremPremiseAnalysisError> {
    let mut found = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut stack = vec![(expression, 0_u32)];
    while let Some((current, depth)) = stack.pop() {
        spend(
            traversal_states,
            VerifiedTheoremPremiseAnalysisErrorReason::ExpressionTraversalLimit,
            declaration_index,
        )?;
        let key = (current as *const Expr as usize, depth);
        if !visited.insert(key) {
            continue;
        }
        match current {
            Expr::Sort(_) | Expr::Const { .. } => {}
            Expr::BVar(index) => {
                if *index >= depth {
                    let relative = usize::try_from(*index - depth)
                        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
                    if relative >= binder_count {
                        return Err(invalid_verified_module(Some(declaration_index)));
                    }
                    found.insert(binder_count - 1 - relative);
                }
            }
            Expr::App(function, argument) => {
                stack.push((argument, depth));
                stack.push((function, depth));
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                let nested = depth
                    .checked_add(1)
                    .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
                stack.push((body, nested));
                stack.push((ty, depth));
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                let nested = depth
                    .checked_add(1)
                    .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
                stack.push((body, nested));
                stack.push((value, depth));
                stack.push((ty, depth));
            }
        }
    }
    Ok(found.into_iter().collect())
}

fn align_proof_binders(
    env: &Env,
    delta: &[String],
    mut proof: Expr,
    domains: &[Expr],
    whnf_fuel: &mut usize,
    conversion_fuel: &mut usize,
    declaration_index: usize,
) -> std::result::Result<(Expr, usize), VerifiedTheoremPremiseAnalysisError> {
    let mut ctx = Ctx::new();
    let mut aligned = 0;
    while aligned < domains.len() {
        proof = reduce_leading_lets(proof, whnf_fuel, declaration_index)?;
        let Expr::Lam { ty, body, .. } = proof else {
            break;
        };
        if !env
            .is_defeq_with_fuel_metered(&ctx, delta, &ty, &domains[aligned], conversion_fuel)
            .map_err(|error| map_kernel_error(error, declaration_index))?
        {
            return Err(invalid_verified_module(Some(declaration_index)));
        }
        let ty = (*ty).clone();
        proof = (*body).clone();
        ctx.push_assumption("_", ty);
        aligned += 1;
    }
    proof = reduce_leading_lets(proof, whnf_fuel, declaration_index)?;
    Ok((proof, aligned))
}

fn collect_fact_premise_uses(
    proof_body: &Expr,
    aligned_binders: usize,
    fact_indices: &BTreeSet<usize>,
    traversal_states: &mut usize,
    declaration_index: usize,
) -> std::result::Result<
    BTreeMap<usize, BTreeSet<VerifiedTheoremPremiseUseSite>>,
    VerifiedTheoremPremiseAnalysisError,
> {
    let mut uses = BTreeMap::<usize, BTreeSet<_>>::new();
    let mut reserved = None;
    if let Expr::BVar(index) = proof_body {
        if let Some(binder) =
            theorem_binder_for_bvar(*index, 0, aligned_binders, declaration_index)?
        {
            if fact_indices.contains(&binder) {
                uses.entry(binder)
                    .or_default()
                    .insert(VerifiedTheoremPremiseUseSite::DirectResult);
                reserved = Some((
                    proof_body as *const Expr as usize,
                    0_u32,
                    VerifiedTheoremPremiseUseSite::TermBody,
                ));
            }
        }
    } else if matches!(proof_body, Expr::App(_, _)) {
        let mut head = proof_body;
        while let Expr::App(function, _) = head {
            head = function;
        }
        if let Expr::BVar(index) = head {
            if let Some(binder) =
                theorem_binder_for_bvar(*index, 0, aligned_binders, declaration_index)?
            {
                if fact_indices.contains(&binder) {
                    uses.entry(binder)
                        .or_default()
                        .insert(VerifiedTheoremPremiseUseSite::ApplicationHead);
                    reserved = Some((
                        head as *const Expr as usize,
                        0_u32,
                        VerifiedTheoremPremiseUseSite::TermBody,
                    ));
                }
            }
        }
    }

    let mut visited = BTreeSet::new();
    let mut stack = vec![(proof_body, 0_u32, VerifiedTheoremPremiseUseSite::TermBody)];
    while let Some((current, depth, site)) = stack.pop() {
        spend(
            traversal_states,
            VerifiedTheoremPremiseAnalysisErrorReason::ExpressionTraversalLimit,
            declaration_index,
        )?;
        let key = (current as *const Expr as usize, depth, site);
        if !visited.insert(key) {
            continue;
        }
        match current {
            Expr::Sort(_) | Expr::Const { .. } => {}
            Expr::BVar(index) => {
                if reserved != Some(key) {
                    if let Some(binder) =
                        theorem_binder_for_bvar(*index, depth, aligned_binders, declaration_index)?
                    {
                        if fact_indices.contains(&binder) {
                            uses.entry(binder).or_default().insert(site);
                        }
                    }
                }
            }
            Expr::App(function, argument) => {
                stack.push((
                    argument,
                    depth,
                    VerifiedTheoremPremiseUseSite::ApplicationArgument,
                ));
                stack.push((function, depth, site));
            }
            Expr::Lam { ty, body, .. } => {
                let nested = depth
                    .checked_add(1)
                    .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
                stack.push((body, nested, site));
                stack.push((ty, depth, VerifiedTheoremPremiseUseSite::DependentType));
            }
            Expr::Pi { ty, body, .. } => {
                let nested = depth
                    .checked_add(1)
                    .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
                stack.push((body, nested, VerifiedTheoremPremiseUseSite::DependentType));
                stack.push((ty, depth, VerifiedTheoremPremiseUseSite::DependentType));
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                let nested = depth
                    .checked_add(1)
                    .ok_or_else(|| invalid_verified_module(Some(declaration_index)))?;
                stack.push((body, nested, site));
                stack.push((value, depth, VerifiedTheoremPremiseUseSite::LetValue));
                stack.push((ty, depth, VerifiedTheoremPremiseUseSite::DependentType));
            }
        }
    }
    Ok(uses)
}

fn theorem_binder_for_bvar(
    index: u32,
    depth: u32,
    aligned_binders: usize,
    declaration_index: usize,
) -> std::result::Result<Option<usize>, VerifiedTheoremPremiseAnalysisError> {
    if index < depth {
        return Ok(None);
    }
    let relative = usize::try_from(index - depth)
        .map_err(|_| invalid_verified_module(Some(declaration_index)))?;
    if relative >= aligned_binders {
        return Err(invalid_verified_module(Some(declaration_index)));
    }
    Ok(Some(aligned_binders - 1 - relative))
}

fn resolve_dependency_kind(
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    dependency: &crate::DependencyEntry,
) -> std::result::Result<VerifiedTheoremGlobalDependencyKind, VerifiedTheoremPremiseAnalysisError> {
    match &dependency.global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = module
                .name_table
                .get(*name)
                .ok_or_else(|| invalid_verified_module(None))?;
            if *decl_interface_hash != dependency.decl_interface_hash
                || builtin_decl_interface_hash(name) != Some(*decl_interface_hash)
            {
                return Err(invalid_verified_module(None));
            }
            Ok(if builtin_is_axiom(name) {
                VerifiedTheoremGlobalDependencyKind::BuiltinAxiom
            } else {
                VerifiedTheoremGlobalDependencyKind::BuiltinPrimitive
            })
        }
        GlobalRef::Local { decl_index } => {
            let decl = module
                .declarations
                .get(*decl_index)
                .ok_or_else(|| invalid_verified_module(None))?;
            if decl.hashes.decl_interface_hash != dependency.decl_interface_hash {
                return Err(invalid_verified_module(None));
            }
            Ok(decl_payload_kind(&decl.decl))
        }
        GlobalRef::LocalGenerated { name, .. } => {
            let entry = module
                .export_block
                .iter()
                .find(|entry| {
                    entry.name == *name
                        && entry.decl_interface_hash == dependency.decl_interface_hash
                })
                .ok_or_else(|| invalid_verified_module(None))?;
            export_kind(entry.kind).ok_or_else(|| invalid_verified_module(None))
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            if *decl_interface_hash != dependency.decl_interface_hash {
                return Err(invalid_verified_module(None));
            }
            let imported = imports
                .get(*import_index)
                .copied()
                .ok_or_else(|| invalid_verified_module(None))?;
            let wanted = module
                .name_table
                .get(*name)
                .ok_or_else(|| invalid_verified_module(None))?;
            let entry = imported
                .export_block
                .iter()
                .find(|entry| {
                    entry.decl_interface_hash == *decl_interface_hash
                        && imported
                            .name_table
                            .get(entry.name)
                            .is_some_and(|name| name == wanted)
                })
                .ok_or_else(|| invalid_verified_module(None))?;
            export_kind(entry.kind).ok_or_else(|| invalid_verified_module(None))
        }
    }
}

fn decl_payload_kind(payload: &DeclPayload) -> VerifiedTheoremGlobalDependencyKind {
    match payload {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => {
            VerifiedTheoremGlobalDependencyKind::Axiom
        }
        DeclPayload::Def { .. } | DeclPayload::DefConstrained { .. } => {
            VerifiedTheoremGlobalDependencyKind::Definition
        }
        DeclPayload::Theorem { .. } | DeclPayload::TheoremConstrained { .. } => {
            VerifiedTheoremGlobalDependencyKind::Theorem
        }
        DeclPayload::Inductive { .. }
        | DeclPayload::InductiveConstrained { .. }
        | DeclPayload::MutualInductiveBlock { .. } => {
            VerifiedTheoremGlobalDependencyKind::Inductive
        }
    }
}

fn export_kind(kind: ExportKind) -> Option<VerifiedTheoremGlobalDependencyKind> {
    match kind {
        ExportKind::Axiom => Some(VerifiedTheoremGlobalDependencyKind::Axiom),
        ExportKind::Def => Some(VerifiedTheoremGlobalDependencyKind::Definition),
        ExportKind::Theorem => Some(VerifiedTheoremGlobalDependencyKind::Theorem),
        ExportKind::Inductive => Some(VerifiedTheoremGlobalDependencyKind::Inductive),
        ExportKind::Constructor => Some(VerifiedTheoremGlobalDependencyKind::Constructor),
        ExportKind::Recursor => Some(VerifiedTheoremGlobalDependencyKind::Recursor),
    }
}

fn map_kernel_error(
    error: KernelError,
    declaration_index: usize,
) -> VerifiedTheoremPremiseAnalysisError {
    match error {
        KernelError::ResourceLimit {
            kind: ResourceLimitKind::Whnf,
        } => analysis_error(
            VerifiedTheoremPremiseAnalysisErrorReason::WhnfFuelLimit,
            Some(declaration_index),
        ),
        KernelError::ResourceLimit {
            kind: ResourceLimitKind::Conversion,
        } => analysis_error(
            VerifiedTheoremPremiseAnalysisErrorReason::ConversionFuelLimit,
            Some(declaration_index),
        ),
        _ => invalid_verified_module(Some(declaration_index)),
    }
}

fn spend(
    remaining: &mut usize,
    reason: VerifiedTheoremPremiseAnalysisErrorReason,
    declaration_index: usize,
) -> std::result::Result<(), VerifiedTheoremPremiseAnalysisError> {
    if *remaining == 0 {
        return Err(analysis_error(reason, Some(declaration_index)));
    }
    *remaining -= 1;
    Ok(())
}

fn import_context_mismatch() -> VerifiedTheoremPremiseAnalysisError {
    analysis_error(
        VerifiedTheoremPremiseAnalysisErrorReason::ImportContextMismatch,
        None,
    )
}

fn invalid_verified_module(
    declaration_index: Option<usize>,
) -> VerifiedTheoremPremiseAnalysisError {
    analysis_error(
        VerifiedTheoremPremiseAnalysisErrorReason::InvalidVerifiedModule,
        declaration_index,
    )
}

fn analysis_error(
    reason: VerifiedTheoremPremiseAnalysisErrorReason,
    declaration_index: Option<usize>,
) -> VerifiedTheoremPremiseAnalysisError {
    VerifiedTheoremPremiseAnalysisError {
        reason,
        declaration_index,
    }
}

#[cfg(test)]
mod tests {
    use npa_kernel::{prop, Decl, Expr, Level, UniverseConstraint};

    use super::*;
    use crate::{
        build_module_cert, verify_built_module_cert_with_import_refs, AxiomPolicy, CoreModule,
    };

    fn identity_statement() -> Expr {
        Expr::pi(
            "P",
            Expr::sort(prop()),
            Expr::pi("h", Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn identity_proof() -> Expr {
        Expr::lam(
            "P",
            Expr::sort(prop()),
            Expr::lam("h", Expr::bvar(0), Expr::bvar(0)),
        )
    }

    fn verified_module(declarations: Vec<Decl>) -> VerifiedModule {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Premise.Test"),
                declarations,
            },
            &[],
        )
        .unwrap();
        verify_built_module_cert_with_import_refs(&cert, &[], &AxiomPolicy::normal()).unwrap()
    }

    #[test]
    fn theorem_premise_analysis_distinguishes_sort_and_fact_and_direct_use() {
        let module = verified_module(vec![Decl::Theorem {
            name: "identity".to_owned(),
            universe_params: vec![],
            ty: identity_statement(),
            proof: identity_proof(),
        }]);

        let analyses = analyze_verified_module_theorem_premises(
            &module,
            &[],
            VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1,
        )
        .unwrap();
        assert_eq!(analyses.len(), 1);
        let analysis = &analyses[0];
        assert_eq!(analysis.binder_count, 2);
        assert_eq!(analysis.sort_parameter_indices, vec![0]);
        assert!(analysis.data_parameter_indices.is_empty());
        assert_eq!(analysis.fact_premises.len(), 1);
        assert_eq!(analysis.fact_premises[0].binder_index, 1);
        assert_eq!(
            analysis.fact_premises[0].depends_on_prior_binder_indices,
            vec![0]
        );
        assert_eq!(
            analysis.fact_premises[0].use_sites,
            vec![VerifiedTheoremPremiseUseSite::DirectResult]
        );
        assert_eq!(analysis.conclusion_depends_on_binder_indices, vec![0]);
    }

    #[test]
    fn theorem_premise_analysis_preserves_non_eta_theorem_dependency() {
        let module = verified_module(vec![
            Decl::Theorem {
                name: "identity".to_owned(),
                universe_params: vec![],
                ty: identity_statement(),
                proof: identity_proof(),
            },
            Decl::Theorem {
                name: "identity_again".to_owned(),
                universe_params: vec![],
                ty: identity_statement(),
                proof: Expr::konst("identity", vec![]),
            },
        ]);

        let analyses = analyze_verified_module_theorem_premises(
            &module,
            &[],
            VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1,
        )
        .unwrap();
        let analysis = analyses
            .iter()
            .find(|analysis| analysis.export_name.as_dotted() == "identity_again")
            .unwrap();
        assert!(analysis.fact_premises[0].use_sites.is_empty());
        assert_eq!(analysis.global_dependencies.len(), 1);
        assert_eq!(
            analysis.global_dependencies[0].kind,
            VerifiedTheoremGlobalDependencyKind::Theorem
        );
    }

    #[test]
    fn theorem_premise_analysis_accepts_data_valued_theorems() {
        let universe = Level::param("u");
        let module = verified_module(vec![Decl::Theorem {
            name: "data_identity".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(universe.clone()),
                Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(universe),
                Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
            ),
        }]);

        let analyses = analyze_verified_module_theorem_premises(
            &module,
            &[],
            VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1,
        )
        .unwrap();
        let analysis = &analyses[0];
        assert_eq!(analysis.sort_parameter_indices, vec![0]);
        assert_eq!(analysis.data_parameter_indices, vec![1]);
        assert!(analysis.fact_premises.is_empty());
        assert_eq!(analysis.conclusion_depends_on_binder_indices, vec![0]);
    }

    #[test]
    fn theorem_premise_analysis_preserves_constrained_universe_context() {
        let u = Level::param("u");
        let v = Level::param("v");
        let universe_params = vec!["u".to_owned(), "v".to_owned()];
        let universe_constraints = vec![UniverseConstraint::le(u.clone(), v.clone())];
        let carrier = Expr::konst("ConstrainedCarrier", vec![u, v]);
        let module = verified_module(vec![
            Decl::AxiomConstrained {
                name: "ConstrainedCarrier".to_owned(),
                universe_params: universe_params.clone(),
                universe_constraints: universe_constraints.clone(),
                ty: Expr::sort(Level::param("u")),
            },
            Decl::TheoremConstrained {
                name: "constrained_identity".to_owned(),
                universe_params,
                universe_constraints,
                ty: Expr::pi("value", carrier.clone(), carrier.clone()),
                proof: Expr::lam("value", carrier, Expr::bvar(0)),
            },
        ]);

        let analyses = analyze_verified_module_theorem_premises(
            &module,
            &[],
            VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1,
        )
        .unwrap();
        let analysis = &analyses[0];
        assert_eq!(analysis.data_parameter_indices, vec![0]);
        assert!(analysis.fact_premises.is_empty());
        assert_eq!(analysis.global_dependencies.len(), 1);
        assert_eq!(
            analysis.global_dependencies[0].kind,
            VerifiedTheoremGlobalDependencyKind::Axiom
        );
    }

    #[test]
    fn theorem_premise_analysis_reports_telescope_limit() {
        let module = verified_module(vec![Decl::Theorem {
            name: "identity".to_owned(),
            universe_params: vec![],
            ty: identity_statement(),
            proof: identity_proof(),
        }]);
        let mut limits = VERIFIED_THEOREM_PREMISE_ANALYSIS_LIMITS_V1;
        limits.telescope_binders_per_theorem = 1;
        let error = analyze_verified_module_theorem_premises(&module, &[], limits).unwrap_err();
        assert_eq!(
            error.reason,
            VerifiedTheoremPremiseAnalysisErrorReason::TelescopeLimit
        );
        assert_eq!(error.declaration_index, Some(0));
    }
}

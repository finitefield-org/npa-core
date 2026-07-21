use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::{
    builtins::{eq_inductive, eq_rec_type, nat_inductive},
    context::Ctx,
    decl::{
        ConstructorDecl, Decl, InductiveDecl, MutualInductiveBlock, RecursorDecl, RecursorRules,
        Reducibility,
    },
    diagnostic::{
        DiagnosedKernelError, KernelComparisonOutcome, KernelConversionContext,
        KernelDiagnosticContext, KernelDiagnosticPhase, KernelExprHead,
    },
    error::{Error, ResourceLimitKind, Result},
    expr::{collect_apps, quick_syntactic_eq, Expr},
    level::{
        ensure_level_wf, level_eq, levels_eq, normalize_level, Level, UniverseConstraint,
        UniverseContext,
    },
    memo::{
        DefeqMemoLookup, KernelExecutionOptions, KernelOperationMemo, MemoExprOrigin,
        WhnfMemoLookup,
    },
    name::is_canonical_dotted_name,
    positivity::approved_nested_functor,
    subst::{instantiate, subst_levels_expr},
    work::{KernelWorkCounterSink, KernelWorkCounters},
};

#[cfg(test)]
use crate::memo::KernelMemoLimits;

#[derive(Clone, Debug, Default)]
pub struct Env {
    decls: BTreeMap<String, Decl>,
    mutual_groups: BTreeMap<String, MutualGroupInfo>,
    execution_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MutualGroupInfo {
    inductives: Vec<String>,
    recursors: BTreeMap<String, String>,
    universe_params: Vec<String>,
    universe_constraints: Vec<UniverseConstraint>,
}

struct MutualRecursorResultCheck<'a> {
    data: &'a InductiveDecl,
    recursor: &'a RecursorDecl,
    rules: &'a RecursorRules,
    domains: &'a [Expr],
    result: &'a Expr,
    universe_context: &'a UniverseContext,
    family_index: usize,
    index_start: usize,
}

#[derive(Clone, Copy)]
enum KernelWorkCounter {
    CheckCall,
    InferCall,
    WhnfCall,
    DefeqCall,
    QuickEqualityHit,
    BetaStep,
    DeltaStep,
    IotaStep,
    ZetaStep,
    PhysicalReduction,
    ContextLookup,
    ContextShift,
}

trait KernelWorkMeter {
    fn increment(&mut self, _counter: KernelWorkCounter) {}

    fn record_fuel(&mut self, _spent: usize, _exhausted: bool) {}

    fn merge_counters(&mut self, _counters: KernelWorkCounters) {}
}

struct DisabledKernelWorkMeter;

impl KernelWorkMeter for DisabledKernelWorkMeter {}

impl KernelWorkMeter for KernelWorkCounters {
    fn increment(&mut self, counter: KernelWorkCounter) {
        let value = match counter {
            KernelWorkCounter::CheckCall => &mut self.check_calls,
            KernelWorkCounter::InferCall => &mut self.infer_calls,
            KernelWorkCounter::WhnfCall => &mut self.whnf_calls,
            KernelWorkCounter::DefeqCall => &mut self.defeq_calls,
            KernelWorkCounter::QuickEqualityHit => &mut self.quick_equality_hits,
            KernelWorkCounter::BetaStep => &mut self.beta_steps,
            KernelWorkCounter::DeltaStep => &mut self.delta_steps,
            KernelWorkCounter::IotaStep => &mut self.iota_steps,
            KernelWorkCounter::ZetaStep => &mut self.zeta_steps,
            KernelWorkCounter::PhysicalReduction => &mut self.physical_reductions,
            KernelWorkCounter::ContextLookup => &mut self.context_lookups,
            KernelWorkCounter::ContextShift => &mut self.context_shifts,
        };
        if *value == u64::MAX {
            self.overflowed = true;
        } else {
            *value += 1;
        }
    }

    fn record_fuel(&mut self, spent: usize, exhausted: bool) {
        let spent = u64::try_from(spent).unwrap_or(u64::MAX);
        KernelWorkCounters::add(&mut self.logical_fuel, spent, &mut self.overflowed);
        if exhausted {
            KernelWorkCounters::add(&mut self.exhausted_fuel, spent, &mut self.overflowed);
        } else {
            KernelWorkCounters::add(&mut self.successful_fuel, spent, &mut self.overflowed);
        }
    }

    fn merge_counters(&mut self, counters: KernelWorkCounters) {
        self.merge(counters);
    }
}

struct KernelOperationState {
    memo: KernelOperationMemo,
    counters: KernelWorkCounters,
}

impl KernelOperationState {
    fn new(options: KernelExecutionOptions) -> Self {
        let memo = KernelOperationMemo::new(options)
            .expect("reuse state is created only for memo or repetition probing");
        Self {
            counters: KernelWorkCounters {
                memo_entry_capacity: memo.entry_capacity() as u64,
                memo_retained_bytes: memo.retained_bytes() as u64,
                ..KernelWorkCounters::default()
            },
            memo,
        }
    }

    #[cfg(test)]
    fn with_limits(options: KernelExecutionOptions, limits: KernelMemoLimits) -> Self {
        let memo = KernelOperationMemo::with_limits(options, limits);
        Self {
            counters: KernelWorkCounters {
                memo_entry_capacity: memo.entry_capacity() as u64,
                memo_retained_bytes: memo.retained_bytes() as u64,
                ..KernelWorkCounters::default()
            },
            memo,
        }
    }
}

#[derive(Default)]
struct KernelConversionRecorder {
    comparison: Option<KernelConversionContext>,
}

impl KernelConversionRecorder {
    fn record(&mut self, outcome: KernelComparisonOutcome, lhs: &Expr, rhs: &Expr, depth: u32) {
        let replace = self.comparison.as_ref().is_none_or(|current| {
            depth > current.depth()
                || (depth == current.depth()
                    && outcome == KernelComparisonOutcome::FuelExhausted
                    && current.outcome() == KernelComparisonOutcome::NotDefEq)
        });
        if replace {
            self.comparison = Some(KernelConversionContext::new(
                outcome,
                KernelExprHead::from_expr(lhs),
                KernelExprHead::from_expr(rhs),
                depth,
            ));
        }
    }
}

impl Env {
    const WHNF_FUEL: usize = 100_000;
    // Keep the default conversion ceiling aligned with the independent
    // reference checker. Human elaboration and certificate construction use
    // this default path, so a lower fast-kernel ceiling can reject declarations
    // that the source-free acceptance boundary is deliberately sized to check.
    const DEFEQ_FUEL: usize = 5_000_000;

    pub fn new() -> Self {
        Self::default()
    }

    /// Construct an empty environment with explicit out-of-band execution
    /// options. The environment retains only the mode; every memo remains
    /// operation-local.
    pub fn with_execution_options(execution_options: KernelExecutionOptions) -> Self {
        Self {
            execution_options,
            ..Self::default()
        }
    }

    /// Construct an empty environment that aggregates deterministic work
    /// counters from ordinary nondiagnosed declaration-validation operations.
    pub fn with_execution_options_and_work_counter_sink(
        execution_options: KernelExecutionOptions,
        work_counter_sink: KernelWorkCounterSink,
    ) -> Self {
        Self {
            execution_options,
            work_counter_sink: Some(work_counter_sink),
            ..Self::default()
        }
    }

    /// Return the out-of-band execution selection retained by this
    /// environment.
    pub const fn execution_options(&self) -> KernelExecutionOptions {
        self.execution_options
    }

    fn observes_work_counters(&self) -> bool {
        self.work_counter_sink.is_some()
    }

    fn observe_work_counters(&self, counters: KernelWorkCounters) {
        if let Some(sink) = &self.work_counter_sink {
            sink.observe(counters);
        }
    }

    pub fn with_builtins() -> Result<Self> {
        Self::with_builtins_and_execution_options(KernelExecutionOptions::default())
    }

    /// Construct a built-in environment with explicit out-of-band execution
    /// options. The selected mode is retained, but memo tables are not.
    pub fn with_builtins_and_execution_options(
        execution_options: KernelExecutionOptions,
    ) -> Result<Self> {
        let mut env = Self::with_execution_options(execution_options);
        env.add_inductive(nat_inductive())?;
        env.add_inductive(eq_inductive())?;
        env.add_axiom(
            "Eq.rec",
            vec!["u".to_owned(), "v".to_owned()],
            eq_rec_type(Level::param("u"), Level::param("v")),
        )?;
        Ok(env)
    }

    pub fn decl(&self, name: &str) -> Option<&Decl> {
        self.decls.get(name)
    }

    pub fn add_axiom(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        ty: Expr,
    ) -> Result<()> {
        self.add_axiom_with_universe_constraints(name, universe_params, Vec::new(), ty)
    }

    pub fn add_axiom_with_universe_constraints(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
    ) -> Result<()> {
        let name = name.into();
        self.ensure_fresh(&name)?;
        let universe_context =
            UniverseContext::new(universe_params.clone(), universe_constraints.clone())?;
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)?;
        let decl = if universe_constraints.is_empty() {
            Decl::Axiom {
                name,
                universe_params,
                ty,
            }
        } else {
            Decl::AxiomConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
            }
        };
        self.decls.insert(decl.name().to_owned(), decl);
        Ok(())
    }

    pub fn add_def(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        ty: Expr,
        value: Expr,
        reducibility: Reducibility,
    ) -> Result<()> {
        self.add_def_with_universe_constraints(
            name,
            universe_params,
            Vec::new(),
            ty,
            value,
            reducibility,
        )
    }

    pub fn add_def_with_universe_constraints(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        value: Expr,
        reducibility: Reducibility,
    ) -> Result<()> {
        let name = name.into();
        self.ensure_fresh(&name)?;
        let universe_context =
            UniverseContext::new(universe_params.clone(), universe_constraints.clone())?;
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)?;
        self.check_in_universe_context(&Ctx::new(), &universe_context, &value, &ty)?;
        let decl = if universe_constraints.is_empty() {
            Decl::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            }
        } else {
            Decl::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            }
        };
        self.decls.insert(decl.name().to_owned(), decl);
        Ok(())
    }

    pub fn add_theorem(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        ty: Expr,
        proof: Expr,
    ) -> Result<()> {
        self.add_theorem_with_universe_constraints(name, universe_params, Vec::new(), ty, proof)
    }

    pub fn add_theorem_with_universe_constraints(
        &mut self,
        name: impl Into<String>,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        proof: Expr,
    ) -> Result<()> {
        let name = name.into();
        self.ensure_fresh(&name)?;
        let universe_context =
            UniverseContext::new(universe_params.clone(), universe_constraints.clone())?;
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)?;
        self.check_in_universe_context(&Ctx::new(), &universe_context, &proof, &ty)?;
        let decl = if universe_constraints.is_empty() {
            Decl::Theorem {
                name,
                universe_params,
                ty,
                proof,
            }
        } else {
            Decl::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
            }
        };
        self.decls.insert(decl.name().to_owned(), decl);
        Ok(())
    }

    pub fn add_inductive(&mut self, data: InductiveDecl) -> Result<()> {
        let universe_context = UniverseContext::new(
            data.universe_params.clone(),
            data.universe_constraints.clone(),
        )?;
        ensure_level_wf(&universe_context.params, &data.sort)?;
        self.ensure_inductive_names_fresh(&data)?;

        let ty = inductive_type(&data);
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)?;

        let mut candidate = self.clone();
        candidate.decls.insert(
            data.name.clone(),
            Decl::Inductive {
                name: data.name.clone(),
                universe_params: data.universe_params.clone(),
                ty,
                data: Box::new(data.clone()),
            },
        );

        for constructor in &data.constructors {
            candidate.check_constructor_decl(&data, constructor, &universe_context)?;
            candidate.decls.insert(
                constructor.name.clone(),
                Decl::Constructor {
                    name: constructor.name.clone(),
                    universe_params: data.universe_params.clone(),
                    ty: constructor.ty.clone(),
                    inductive: data.name.clone(),
                },
            );
        }

        if let Some(recursor) = &data.recursor {
            let recursor_context = UniverseContext::new(
                recursor.universe_params.clone(),
                data.universe_constraints.clone(),
            )?;
            candidate.expect_sort_in_universe_context(
                &Ctx::new(),
                &recursor_context,
                &recursor.ty,
            )?;
            let rules = recursor
                .rules
                .clone()
                .unwrap_or_else(|| generated_recursor_rules(&data));
            candidate.check_recursor_decl(&data, recursor, &rules, &recursor_context)?;
            candidate.decls.insert(
                recursor.name.clone(),
                Decl::Recursor {
                    name: recursor.name.clone(),
                    universe_params: recursor.universe_params.clone(),
                    ty: recursor.ty.clone(),
                    inductive: data.name.clone(),
                    rules,
                },
            );
        }

        *self = candidate;
        Ok(())
    }

    pub fn add_mutual_inductive(&mut self, block: MutualInductiveBlock) -> Result<()> {
        if block.inductives.is_empty() {
            return Err(Error::InvalidInductive(format!(
                "{} mutual block must contain at least one inductive",
                block.name
            )));
        }
        let universe_context = UniverseContext::new(
            block.universe_params.clone(),
            block.universe_constraints.clone(),
        )?;
        self.ensure_mutual_inductive_names_fresh(&block)?;

        let param_count = block.inductives[0].params.len();
        for data in &block.inductives {
            if data.universe_params != block.universe_params
                || !data.universe_constraints.is_empty()
                || data.params.len() != param_count
                || data.params != block.inductives[0].params
            {
                return Err(Error::InvalidInductive(format!(
                    "{} mutual block requires shared universe and parameter telescopes",
                    block.name
                )));
            }
            ensure_level_wf(&universe_context.params, &data.sort)?;
        }

        let mut candidate = self.clone();
        for data in &block.inductives {
            let ty = inductive_type(data);
            candidate.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)?;
            candidate.decls.insert(
                data.name.clone(),
                Decl::Inductive {
                    name: data.name.clone(),
                    universe_params: data.universe_params.clone(),
                    ty,
                    data: Box::new(data.clone()),
                },
            );
        }

        for data in &block.inductives {
            for constructor in &data.constructors {
                candidate.check_mutual_constructor_decl(
                    &block,
                    data,
                    constructor,
                    &universe_context,
                )?;
                candidate.decls.insert(
                    constructor.name.clone(),
                    Decl::Constructor {
                        name: constructor.name.clone(),
                        universe_params: data.universe_params.clone(),
                        ty: constructor.ty.clone(),
                        inductive: data.name.clone(),
                    },
                );
            }
        }

        for data in &block.inductives {
            if let Some(recursor) = &data.recursor {
                let recursor_context = UniverseContext::new(
                    recursor.universe_params.clone(),
                    block.universe_constraints.clone(),
                )?;
                candidate.expect_sort_in_universe_context(
                    &Ctx::new(),
                    &recursor_context,
                    &recursor.ty,
                )?;
                let rules = recursor
                    .rules
                    .clone()
                    .unwrap_or_else(|| generated_mutual_recursor_rules(&block, data));
                candidate.check_mutual_recursor_decl(
                    &block,
                    data,
                    recursor,
                    &rules,
                    &recursor_context,
                )?;
                candidate.decls.insert(
                    recursor.name.clone(),
                    Decl::Recursor {
                        name: recursor.name.clone(),
                        universe_params: recursor.universe_params.clone(),
                        ty: recursor.ty.clone(),
                        inductive: data.name.clone(),
                        rules,
                    },
                );
            }
        }

        let recursors = block
            .inductives
            .iter()
            .filter_map(|data| {
                data.recursor
                    .as_ref()
                    .map(|recursor| (data.name.clone(), recursor.name.clone()))
            })
            .collect();
        let group = MutualGroupInfo {
            inductives: block
                .inductives
                .iter()
                .map(|data| data.name.clone())
                .collect(),
            recursors,
            universe_params: block.universe_params.clone(),
            universe_constraints: block.universe_constraints.clone(),
        };
        for name in &group.inductives {
            candidate.mutual_groups.insert(name.clone(), group.clone());
        }

        *self = candidate;
        Ok(())
    }

    pub fn infer(&self, ctx: &Ctx, delta: &[String], term: &Expr) -> Result<Expr> {
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        self.infer_in_universe_context(ctx, &universe_context, term)
    }

    pub fn infer_in_universe_context(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
    ) -> Result<Expr> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.infer_in_universe_context_with_memo(
                ctx,
                universe_context,
                term,
                MemoExprOrigin::Borrowed,
                &mut state,
            );
            self.observe_work_counters(state.counters);
            return result;
        }
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.infer_in_universe_context_with_work(
                ctx,
                universe_context,
                term,
                &mut counters,
            );
            self.observe_work_counters(counters);
            return result;
        }
        self.infer_in_universe_context_with_work(
            ctx,
            universe_context,
            term,
            &mut DisabledKernelWorkMeter,
        )
    }

    fn infer_in_universe_context_with_work(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<Expr> {
        meter.increment(KernelWorkCounter::InferCall);
        match term {
            Expr::Sort(level) => {
                ensure_level_wf(&universe_context.params, level)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            Expr::BVar(index) => {
                meter.increment(KernelWorkCounter::ContextLookup);
                meter.increment(KernelWorkCounter::ContextShift);
                ctx.lookup_type(*index)
            }
            Expr::Const { name, levels } => {
                self.infer_const_type_in_universe_context(universe_context, name, levels)
            }
            Expr::Pi { binder, ty, body } => {
                let domain_sort = self.expect_sort_in_universe_context_with_work(
                    ctx,
                    universe_context,
                    ty,
                    meter,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_sort = self.expect_sort_in_universe_context_with_work(
                    &body_ctx,
                    universe_context,
                    body,
                    meter,
                )?;
                Ok(Expr::sort(Level::imax(domain_sort, body_sort)))
            }
            Expr::Lam { binder, ty, body } => {
                self.expect_sort_in_universe_context_with_work(ctx, universe_context, ty, meter)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_ty = self.infer_in_universe_context_with_work(
                    &body_ctx,
                    universe_context,
                    body,
                    meter,
                )?;
                Ok(Expr::pi(binder.clone(), (**ty).clone(), body_ty))
            }
            Expr::App(fun, arg) => {
                let fun_ty =
                    self.infer_in_universe_context_with_work(ctx, universe_context, fun, meter)?;
                match self.whnf_with_work(ctx, &universe_context.params, &fun_ty, meter)? {
                    Expr::Pi { ty, body, .. } => {
                        self.check_in_universe_context_with_work(
                            ctx,
                            universe_context,
                            arg,
                            &ty,
                            meter,
                        )?;
                        instantiate(&body, arg)
                    }
                    actual => Err(Error::ExpectedPi { actual }),
                }
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                self.expect_sort_in_universe_context_with_work(ctx, universe_context, ty, meter)?;
                self.check_in_universe_context_with_work(ctx, universe_context, value, ty, meter)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition(binder.clone(), (**ty).clone(), (**value).clone());
                let body_ty = self.infer_in_universe_context_with_work(
                    &body_ctx,
                    universe_context,
                    body,
                    meter,
                )?;
                instantiate(&body_ty, value)
            }
        }
    }

    pub fn check(&self, ctx: &Ctx, delta: &[String], term: &Expr, expected: &Expr) -> Result<()> {
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        self.check_in_universe_context(ctx, &universe_context, term, expected)
    }

    pub fn check_in_universe_context(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        expected: &Expr,
    ) -> Result<()> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.check_in_universe_context_with_memo(
                ctx,
                universe_context,
                term,
                MemoExprOrigin::Borrowed,
                expected,
                MemoExprOrigin::Borrowed,
                &mut state,
            );
            self.observe_work_counters(state.counters);
            return result;
        }
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.check_in_universe_context_with_work(
                ctx,
                universe_context,
                term,
                expected,
                &mut counters,
            );
            self.observe_work_counters(counters);
            return result;
        }
        self.check_in_universe_context_with_work(
            ctx,
            universe_context,
            term,
            expected,
            &mut DisabledKernelWorkMeter,
        )
    }

    fn check_in_universe_context_with_work(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        expected: &Expr,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<()> {
        meter.increment(KernelWorkCounter::CheckCall);
        let actual =
            self.infer_in_universe_context_with_work(ctx, universe_context, term, meter)?;
        if self.is_defeq_with_work(ctx, &universe_context.params, &actual, expected, meter)? {
            Ok(())
        } else {
            Err(Error::TypeMismatch {
                expected: expected.clone(),
                actual,
            })
        }
    }

    /// Check a term through the ordinary kernel path and retain one bounded
    /// conversion comparison when checking fails.
    pub fn check_diagnosed(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        expected: &Expr,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        let universe_context =
            UniverseContext::from_params(delta.to_vec()).map_err(DiagnosedKernelError::new)?;
        self.check_in_universe_context_diagnosed(
            ctx,
            &universe_context,
            term,
            expected,
            KernelDiagnosticPhase::TermCheck,
        )
    }

    fn infer_in_universe_context_diagnosed(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        phase: KernelDiagnosticPhase,
    ) -> std::result::Result<Expr, DiagnosedKernelError> {
        match term {
            Expr::Sort(level) => {
                ensure_level_wf(&universe_context.params, level)
                    .map_err(DiagnosedKernelError::new)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            Expr::BVar(index) => ctx.lookup_type(*index).map_err(DiagnosedKernelError::new),
            Expr::Const { name, levels } => self
                .infer_const_type_in_universe_context(universe_context, name, levels)
                .map_err(DiagnosedKernelError::new),
            Expr::Pi { binder, ty, body } => {
                let domain_sort = self.expect_sort_in_universe_context_diagnosed(
                    ctx,
                    universe_context,
                    ty,
                    phase,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_sort = self.expect_sort_in_universe_context_diagnosed(
                    &body_ctx,
                    universe_context,
                    body,
                    phase,
                )?;
                Ok(Expr::sort(Level::imax(domain_sort, body_sort)))
            }
            Expr::Lam { binder, ty, body } => {
                self.expect_sort_in_universe_context_diagnosed(ctx, universe_context, ty, phase)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_ty = self.infer_in_universe_context_diagnosed(
                    &body_ctx,
                    universe_context,
                    body,
                    phase,
                )?;
                Ok(Expr::pi(binder.clone(), (**ty).clone(), body_ty))
            }
            Expr::App(fun, arg) => {
                let fun_ty =
                    self.infer_in_universe_context_diagnosed(ctx, universe_context, fun, phase)?;
                match self
                    .whnf_diagnosed_off(ctx, &universe_context.params, &fun_ty)
                    .map_err(DiagnosedKernelError::new)?
                {
                    Expr::Pi { ty, body, .. } => {
                        self.check_in_universe_context_diagnosed(
                            ctx,
                            universe_context,
                            arg,
                            &ty,
                            phase,
                        )?;
                        instantiate(&body, arg).map_err(DiagnosedKernelError::new)
                    }
                    actual => Err(DiagnosedKernelError::new(Error::ExpectedPi { actual })),
                }
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                self.expect_sort_in_universe_context_diagnosed(ctx, universe_context, ty, phase)?;
                self.check_in_universe_context_diagnosed(ctx, universe_context, value, ty, phase)?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition(binder.clone(), (**ty).clone(), (**value).clone());
                let body_ty = self.infer_in_universe_context_diagnosed(
                    &body_ctx,
                    universe_context,
                    body,
                    phase,
                )?;
                instantiate(&body_ty, value).map_err(DiagnosedKernelError::new)
            }
        }
    }

    fn expect_sort_in_universe_context_diagnosed(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        phase: KernelDiagnosticPhase,
    ) -> std::result::Result<Level, DiagnosedKernelError> {
        let inferred =
            self.infer_in_universe_context_diagnosed(ctx, universe_context, term, phase)?;
        match self
            .whnf_diagnosed_off(ctx, &universe_context.params, &inferred)
            .map_err(DiagnosedKernelError::new)?
        {
            Expr::Sort(level) => Ok(level),
            actual => Err(DiagnosedKernelError::new(Error::ExpectedSort { actual })),
        }
    }

    fn check_in_universe_context_diagnosed(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        expected: &Expr,
        phase: KernelDiagnosticPhase,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        let actual =
            self.infer_in_universe_context_diagnosed(ctx, universe_context, term, phase)?;
        let mut recorder = KernelConversionRecorder::default();
        let mut fuel = Self::DEFEQ_FUEL;
        match self.is_defeq_with_remaining_fuel_diagnosed(
            ctx,
            &universe_context.params,
            &actual,
            expected,
            &mut fuel,
            &mut recorder,
            0,
        ) {
            Ok(true) => Ok(()),
            Ok(false) => Err(DiagnosedKernelError::new(Error::TypeMismatch {
                expected: expected.clone(),
                actual,
            })
            .with_context(KernelDiagnosticContext::new(phase).with_conversion(
                recorder.comparison.unwrap_or_else(|| {
                    KernelConversionContext::new(
                        KernelComparisonOutcome::NotDefEq,
                        KernelExprHead::Unknown,
                        KernelExprHead::Unknown,
                        0,
                    )
                }),
            ))),
            Err(error) => {
                let mut diagnosed = DiagnosedKernelError::new(error);
                if let Some(comparison) = recorder.comparison {
                    diagnosed = diagnosed.with_context(
                        KernelDiagnosticContext::new(phase).with_conversion(comparison),
                    );
                }
                Err(diagnosed)
            }
        }
    }

    /// Add one declaration with bounded authoring context on failure.
    pub fn add_decl_diagnosed(
        &mut self,
        declaration: Decl,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        if self.execution_options.needs_reuse_state() {
            let mut counters = KernelWorkCounters::default();
            KernelWorkCounters::add(
                &mut counters.memo_ineligible_diagnosed,
                1,
                &mut counters.overflowed,
            );
            self.observe_work_counters(counters);
            let execution_options = self.execution_options;
            self.execution_options = KernelExecutionOptions::memo_off();
            let result = self.add_decl_diagnosed_off(declaration);
            self.execution_options = execution_options;
            return result;
        }
        self.add_decl_diagnosed_off(declaration)
    }

    fn add_decl_diagnosed_off(
        &mut self,
        declaration: Decl,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        match declaration {
            Decl::Axiom {
                name,
                universe_params,
                ty,
            } => self
                .add_axiom(name, universe_params, ty)
                .map_err(DiagnosedKernelError::new),
            Decl::AxiomConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
            } => self
                .add_axiom_with_universe_constraints(
                    name,
                    universe_params,
                    universe_constraints,
                    ty,
                )
                .map_err(DiagnosedKernelError::new),
            Decl::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            } => self.add_def_diagnosed(name, universe_params, Vec::new(), ty, value, reducibility),
            Decl::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            } => self.add_def_diagnosed(
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            ),
            Decl::Theorem {
                name,
                universe_params,
                ty,
                proof,
            } => self.add_theorem_diagnosed(name, universe_params, Vec::new(), ty, proof),
            Decl::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
            } => self.add_theorem_diagnosed(name, universe_params, universe_constraints, ty, proof),
            Decl::Inductive { data, .. } => {
                self.add_inductive(*data).map_err(DiagnosedKernelError::new)
            }
            Decl::MutualInductiveBlock { data, .. } => self
                .add_mutual_inductive(*data)
                .map_err(DiagnosedKernelError::new),
            Decl::Constructor { .. } | Decl::Recursor { .. } => Ok(()),
        }
    }

    fn add_def_diagnosed(
        &mut self,
        name: String,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        value: Expr,
        reducibility: Reducibility,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        self.ensure_fresh(&name)
            .map_err(DiagnosedKernelError::new)?;
        let universe_context =
            UniverseContext::new(universe_params.clone(), universe_constraints.clone())
                .map_err(DiagnosedKernelError::new)?;
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)
            .map_err(DiagnosedKernelError::new)?;
        self.check_in_universe_context_diagnosed(
            &Ctx::new(),
            &universe_context,
            &value,
            &ty,
            KernelDiagnosticPhase::DeclarationValue,
        )?;
        let declaration = if universe_constraints.is_empty() {
            Decl::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            }
        } else {
            Decl::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            }
        };
        self.decls
            .insert(declaration.name().to_owned(), declaration);
        Ok(())
    }

    fn add_theorem_diagnosed(
        &mut self,
        name: String,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        proof: Expr,
    ) -> std::result::Result<(), DiagnosedKernelError> {
        self.ensure_fresh(&name)
            .map_err(DiagnosedKernelError::new)?;
        let universe_context =
            UniverseContext::new(universe_params.clone(), universe_constraints.clone())
                .map_err(DiagnosedKernelError::new)?;
        self.expect_sort_in_universe_context(&Ctx::new(), &universe_context, &ty)
            .map_err(DiagnosedKernelError::new)?;
        self.check_in_universe_context_diagnosed(
            &Ctx::new(),
            &universe_context,
            &proof,
            &ty,
            KernelDiagnosticPhase::DeclarationValue,
        )?;
        let declaration = if universe_constraints.is_empty() {
            Decl::Theorem {
                name,
                universe_params,
                ty,
                proof,
            }
        } else {
            Decl::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
            }
        };
        self.decls
            .insert(declaration.name().to_owned(), declaration);
        Ok(())
    }

    pub fn infer_with_fuel_metered(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<Expr> {
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        self.infer_with_fuel_metered_in_universe_context(
            ctx,
            &universe_context,
            term,
            whnf_fuel,
            conversion_fuel,
        )
    }

    pub fn infer_with_fuel_metered_in_universe_context(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<Expr> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            return self.infer_with_remaining_fuel_memo_shared(
                ctx,
                universe_context,
                term,
                MemoExprOrigin::Borrowed,
                whnf_fuel,
                conversion_fuel,
                &mut state,
            );
        }
        self.infer_with_remaining_fuel(ctx, universe_context, term, whnf_fuel, conversion_fuel)
    }

    pub fn check_with_fuel_metered(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        expected: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<()> {
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        self.check_with_fuel_metered_in_universe_context(
            ctx,
            &universe_context,
            term,
            expected,
            whnf_fuel,
            conversion_fuel,
        )
    }

    pub fn check_with_fuel_metered_in_universe_context(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        expected: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<()> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            return self.check_with_remaining_fuel_memo_shared(
                ctx,
                universe_context,
                term,
                MemoExprOrigin::Borrowed,
                expected,
                MemoExprOrigin::Borrowed,
                whnf_fuel,
                conversion_fuel,
                &mut state,
            );
        }
        self.check_with_remaining_fuel(
            ctx,
            universe_context,
            term,
            expected,
            whnf_fuel,
            conversion_fuel,
        )
    }

    pub fn whnf(&self, ctx: &Ctx, delta: &[String], term: &Expr) -> Result<Expr> {
        self.whnf_with_fuel(ctx, delta, term, Self::WHNF_FUEL)
    }

    pub fn is_defeq(&self, ctx: &Ctx, delta: &[String], lhs: &Expr, rhs: &Expr) -> Result<bool> {
        self.is_defeq_with_fuel(ctx, delta, lhs, rhs, Self::DEFEQ_FUEL)
    }

    /// Infer a term while updating an optional operation-scoped work meter.
    pub fn infer_with_work_counters(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        meter: Option<&mut KernelWorkCounters>,
    ) -> Result<Expr> {
        let Some(meter) = meter else {
            return self.infer(ctx, delta, term);
        };
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.infer_in_universe_context_with_memo(
                ctx,
                &universe_context,
                term,
                MemoExprOrigin::Borrowed,
                &mut state,
            );
            let counters = state.counters;
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.infer_in_universe_context_with_work(
                ctx,
                &universe_context,
                term,
                &mut counters,
            );
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        self.infer_in_universe_context_with_work(ctx, &universe_context, term, meter)
    }

    /// Check a term while updating an optional operation-scoped work meter.
    pub fn check_with_work_counters(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        expected: &Expr,
        meter: Option<&mut KernelWorkCounters>,
    ) -> Result<()> {
        let Some(meter) = meter else {
            return self.check(ctx, delta, term, expected);
        };
        let universe_context = UniverseContext::from_params(delta.to_vec())?;
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.check_in_universe_context_with_memo(
                ctx,
                &universe_context,
                term,
                MemoExprOrigin::Borrowed,
                expected,
                MemoExprOrigin::Borrowed,
                &mut state,
            );
            let counters = state.counters;
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.check_in_universe_context_with_work(
                ctx,
                &universe_context,
                term,
                expected,
                &mut counters,
            );
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        self.check_in_universe_context_with_work(ctx, &universe_context, term, expected, meter)
    }

    /// Reduce to WHNF while updating an optional operation-scoped work meter.
    pub fn whnf_with_work_counters(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        meter: Option<&mut KernelWorkCounters>,
    ) -> Result<Expr> {
        let Some(meter) = meter else {
            return self.whnf(ctx, delta, term);
        };
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.whnf_with_work(ctx, delta, term, &mut counters);
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        self.whnf_with_work(ctx, delta, term, meter)
    }

    fn whnf_with_work(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<Expr> {
        let mut fuel = Self::WHNF_FUEL;
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.whnf_with_remaining_fuel_memo(
                ctx,
                delta,
                term,
                MemoExprOrigin::Borrowed,
                &mut fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            );
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            state
                .counters
                .record_fuel(Self::WHNF_FUEL - fuel, exhausted);
            meter.merge_counters(state.counters);
            return result;
        }
        let result = self.whnf_with_remaining_fuel(
            ctx,
            delta,
            term,
            &mut fuel,
            ResourceLimitKind::Whnf,
            meter,
        );
        let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
        meter.record_fuel(Self::WHNF_FUEL - fuel, exhausted);
        result
    }

    /// Compare terms while updating an optional operation-scoped work meter.
    pub fn is_defeq_with_work_counters(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        meter: Option<&mut KernelWorkCounters>,
    ) -> Result<bool> {
        let Some(meter) = meter else {
            return self.is_defeq(ctx, delta, lhs, rhs);
        };
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.is_defeq_with_work(ctx, delta, lhs, rhs, &mut counters);
            meter.merge(counters);
            self.observe_work_counters(counters);
            return result;
        }
        self.is_defeq_with_work(ctx, delta, lhs, rhs, meter)
    }

    fn is_defeq_with_work(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<bool> {
        let mut fuel = Self::DEFEQ_FUEL;
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.is_defeq_with_remaining_fuel_memo(
                ctx,
                delta,
                lhs,
                MemoExprOrigin::Borrowed,
                rhs,
                MemoExprOrigin::Borrowed,
                &mut fuel,
                &mut state,
            );
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            state
                .counters
                .record_fuel(Self::DEFEQ_FUEL - fuel, exhausted);
            meter.merge_counters(state.counters);
            return result;
        }
        let result = self.is_defeq_with_remaining_fuel(ctx, delta, lhs, rhs, &mut fuel, meter);
        let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
        meter.record_fuel(Self::DEFEQ_FUEL - fuel, exhausted);
        result
    }

    fn whnf_diagnosed_off(&self, ctx: &Ctx, delta: &[String], term: &Expr) -> Result<Expr> {
        let mut fuel = Self::WHNF_FUEL;
        self.whnf_with_remaining_fuel(
            ctx,
            delta,
            term,
            &mut fuel,
            ResourceLimitKind::Whnf,
            &mut DisabledKernelWorkMeter,
        )
    }

    /// Compare expressions with explicit fuel and bounded failure context.
    pub fn is_defeq_diagnosed_with_fuel(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: usize,
    ) -> std::result::Result<bool, DiagnosedKernelError> {
        self.is_defeq_diagnosed_with_fuel_and_work_counters(ctx, delta, lhs, rhs, fuel, None)
    }

    /// Compare expressions with diagnosed conversion while recording that the
    /// v1 diagnosed path is deliberately memo-ineligible.
    pub fn is_defeq_diagnosed_with_fuel_and_work_counters(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: usize,
        meter: Option<&mut KernelWorkCounters>,
    ) -> std::result::Result<bool, DiagnosedKernelError> {
        if let Some(meter) = meter {
            if self.execution_options.needs_reuse_state() {
                KernelWorkCounters::add(
                    &mut meter.memo_ineligible_diagnosed,
                    1,
                    &mut meter.overflowed,
                );
            }
        }
        let mut fuel = fuel;
        let mut recorder = KernelConversionRecorder::default();
        match self.is_defeq_with_remaining_fuel_diagnosed(
            ctx,
            delta,
            lhs,
            rhs,
            &mut fuel,
            &mut recorder,
            0,
        ) {
            Ok(true) => Ok(true),
            Ok(false) => Ok(false),
            Err(error) => {
                let mut diagnosed = DiagnosedKernelError::new(error);
                if let Some(comparison) = recorder.comparison {
                    diagnosed = diagnosed.with_context(
                        KernelDiagnosticContext::new(KernelDiagnosticPhase::DefinitionalEquality)
                            .with_conversion(comparison),
                    );
                }
                Err(diagnosed)
            }
        }
    }

    pub fn whnf_with_fuel(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        fuel: usize,
    ) -> Result<Expr> {
        let mut fuel = fuel;
        self.whnf_with_fuel_metered(ctx, delta, term, &mut fuel)
    }

    pub fn whnf_with_fuel_metered(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        fuel: &mut usize,
    ) -> Result<Expr> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let starting_fuel = *fuel;
            let result = self.whnf_with_remaining_fuel_memo(
                ctx,
                delta,
                term,
                MemoExprOrigin::Borrowed,
                fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            );
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            state
                .counters
                .record_fuel(starting_fuel.saturating_sub(*fuel), exhausted);
            self.observe_work_counters(state.counters);
            return result;
        }
        if self.observes_work_counters() {
            let starting_fuel = *fuel;
            let mut counters = KernelWorkCounters::default();
            let result = self.whnf_with_remaining_fuel(
                ctx,
                delta,
                term,
                fuel,
                ResourceLimitKind::Whnf,
                &mut counters,
            );
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            counters.record_fuel(starting_fuel.saturating_sub(*fuel), exhausted);
            self.observe_work_counters(counters);
            return result;
        }
        self.whnf_with_remaining_fuel(
            ctx,
            delta,
            term,
            fuel,
            ResourceLimitKind::Whnf,
            &mut DisabledKernelWorkMeter,
        )
    }

    pub fn is_defeq_with_fuel(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: usize,
    ) -> Result<bool> {
        let mut fuel = fuel;
        self.is_defeq_with_fuel_metered(ctx, delta, lhs, rhs, &mut fuel)
    }

    pub fn is_defeq_with_fuel_metered(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: &mut usize,
    ) -> Result<bool> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let starting_fuel = *fuel;
            let result = self.is_defeq_with_remaining_fuel_memo(
                ctx,
                delta,
                lhs,
                MemoExprOrigin::Borrowed,
                rhs,
                MemoExprOrigin::Borrowed,
                fuel,
                &mut state,
            );
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            state
                .counters
                .record_fuel(starting_fuel.saturating_sub(*fuel), exhausted);
            self.observe_work_counters(state.counters);
            return result;
        }
        if self.observes_work_counters() {
            let starting_fuel = *fuel;
            let mut counters = KernelWorkCounters::default();
            let result =
                self.is_defeq_with_remaining_fuel(ctx, delta, lhs, rhs, fuel, &mut counters);
            let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
            counters.record_fuel(starting_fuel.saturating_sub(*fuel), exhausted);
            self.observe_work_counters(counters);
            return result;
        }
        self.is_defeq_with_remaining_fuel(ctx, delta, lhs, rhs, fuel, &mut DisabledKernelWorkMeter)
    }

    fn ensure_fresh(&self, name: &str) -> Result<()> {
        if !is_canonical_dotted_name(name) {
            return Err(Error::InvalidDeclarationName(name.to_owned()));
        }
        if self.decls.contains_key(name) {
            Err(Error::DuplicateDecl(name.to_owned()))
        } else {
            Ok(())
        }
    }

    fn ensure_inductive_names_fresh(&self, data: &InductiveDecl) -> Result<()> {
        let mut names = BTreeSet::new();
        for name in std::iter::once(&data.name)
            .chain(
                data.constructors
                    .iter()
                    .map(|constructor| &constructor.name),
            )
            .chain(data.recursor.iter().map(|recursor| &recursor.name))
        {
            if !names.insert(name) {
                return Err(Error::DuplicateDecl(name.clone()));
            }
            self.ensure_fresh(name)?;
        }
        Ok(())
    }

    fn ensure_mutual_inductive_names_fresh(&self, block: &MutualInductiveBlock) -> Result<()> {
        let mut names = BTreeSet::new();
        for name in std::iter::once(&block.name)
            .chain(block.inductives.iter().map(|data| &data.name))
            .chain(block.inductives.iter().flat_map(|data| {
                data.constructors
                    .iter()
                    .map(|constructor| &constructor.name)
            }))
            .chain(
                block
                    .inductives
                    .iter()
                    .filter_map(|data| data.recursor.as_ref().map(|recursor| &recursor.name)),
            )
        {
            if !names.insert(name) {
                return Err(Error::DuplicateDecl(name.clone()));
            }
            self.ensure_fresh(name)?;
        }
        Ok(())
    }

    fn expect_sort_in_universe_context(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
    ) -> Result<Level> {
        if self.execution_options.needs_reuse_state() {
            let mut state = KernelOperationState::new(self.execution_options);
            let result = self.expect_sort_in_universe_context_with_memo(
                ctx,
                universe_context,
                term,
                MemoExprOrigin::Borrowed,
                &mut state,
            );
            self.observe_work_counters(state.counters);
            return result;
        }
        if self.observes_work_counters() {
            let mut counters = KernelWorkCounters::default();
            let result = self.expect_sort_in_universe_context_with_work(
                ctx,
                universe_context,
                term,
                &mut counters,
            );
            self.observe_work_counters(counters);
            return result;
        }
        self.expect_sort_in_universe_context_with_work(
            ctx,
            universe_context,
            term,
            &mut DisabledKernelWorkMeter,
        )
    }

    fn expect_sort_in_universe_context_with_work(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<Level> {
        let inferred =
            self.infer_in_universe_context_with_work(ctx, universe_context, term, meter)?;
        match self.whnf_with_work(ctx, &universe_context.params, &inferred, meter)? {
            Expr::Sort(level) => Ok(level),
            actual => Err(Error::ExpectedSort { actual }),
        }
    }

    fn infer_const_type_in_universe_context(
        &self,
        universe_context: &UniverseContext,
        name: &str,
        levels: &[Level],
    ) -> Result<Expr> {
        let decl = self
            .decls
            .get(name)
            .ok_or_else(|| Error::UnknownConstant(name.to_owned()))?;
        let params = decl.universe_params();
        if params.len() != levels.len() {
            return Err(Error::BadUniverseArity {
                name: name.to_owned(),
                expected: params.len(),
                actual: levels.len(),
            });
        }
        for level in levels {
            ensure_level_wf(&universe_context.params, level)?;
        }

        let (constraint_params, constraints) = self.decl_constraint_context(decl)?;
        if !constraints.is_empty() {
            let constraint_levels =
                declaration_constraint_levels(name, params, levels, constraint_params)?;
            let obligations = universe_context.substitute_constraints(
                constraint_params,
                &constraint_levels,
                constraints,
            )?;
            universe_context
                .entails(&obligations)
                .map_err(|err| match err {
                    Error::UniverseConstraintViolation { constraint, .. } => {
                        Error::UniverseConstraintViolation {
                            declaration: name.to_owned(),
                            constraint,
                        }
                    }
                    err => err,
                })?;
        }

        Ok(subst_levels_expr(decl.ty(), params, levels))
    }

    fn decl_constraint_context<'a>(
        &'a self,
        decl: &'a Decl,
    ) -> Result<(&'a [String], &'a [UniverseConstraint])> {
        match decl {
            Decl::Inductive { name, .. } => self.inductive_constraint_context(name),
            Decl::Constructor { inductive, .. } | Decl::Recursor { inductive, .. } => {
                self.inductive_constraint_context(inductive)
            }
            Decl::MutualInductiveBlock { data, .. } => {
                Ok((&data.universe_params, &data.universe_constraints))
            }
            _ => Ok((decl.universe_params(), decl.universe_constraints())),
        }
    }

    fn inductive_constraint_context<'a>(
        &'a self,
        inductive: &str,
    ) -> Result<(&'a [String], &'a [UniverseConstraint])> {
        if let Some(group) = self.mutual_groups.get(inductive) {
            return Ok((&group.universe_params, &group.universe_constraints));
        }
        let Some(Decl::Inductive { data, .. }) = self.decls.get(inductive) else {
            return Err(Error::InvalidInductive(format!(
                "{inductive} constraint context is missing its parent inductive"
            )));
        };
        Ok((&data.universe_params, &data.universe_constraints))
    }

    fn infer_in_universe_context_with_memo(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        _origin: MemoExprOrigin<'_>,
        state: &mut KernelOperationState,
    ) -> Result<Expr> {
        state.counters.increment(KernelWorkCounter::InferCall);
        match term {
            Expr::Sort(level) => {
                ensure_level_wf(&universe_context.params, level)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            Expr::BVar(index) => {
                state.counters.increment(KernelWorkCounter::ContextLookup);
                state.counters.increment(KernelWorkCounter::ContextShift);
                ctx.lookup_type(*index)
            }
            Expr::Const { name, levels } => {
                self.infer_const_type_in_universe_context(universe_context, name, levels)
            }
            Expr::Pi { binder, ty, body } => {
                let domain_sort = self.expect_sort_in_universe_context_with_memo(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_sort = self.expect_sort_in_universe_context_with_memo(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    state,
                )?;
                Ok(Expr::sort(Level::imax(domain_sort, body_sort)))
            }
            Expr::Lam { binder, ty, body } => {
                self.expect_sort_in_universe_context_with_memo(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_ty = self.infer_in_universe_context_with_memo(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    state,
                )?;
                Ok(Expr::pi(binder.clone(), (**ty).clone(), body_ty))
            }
            Expr::App(fun, arg) => {
                let fun_ty = self.infer_in_universe_context_with_memo(
                    ctx,
                    universe_context,
                    fun,
                    MemoExprOrigin::Retained(fun),
                    state,
                )?;
                match self.whnf_with_default_memo(
                    ctx,
                    &universe_context.params,
                    &fun_ty,
                    MemoExprOrigin::Fresh,
                    state,
                )? {
                    Expr::Pi { ty, body, .. } => {
                        self.check_in_universe_context_with_memo(
                            ctx,
                            universe_context,
                            arg,
                            MemoExprOrigin::Retained(arg),
                            &ty,
                            MemoExprOrigin::Retained(&ty),
                            state,
                        )?;
                        instantiate(&body, arg)
                    }
                    actual => Err(Error::ExpectedPi { actual }),
                }
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                self.expect_sort_in_universe_context_with_memo(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    state,
                )?;
                self.check_in_universe_context_with_memo(
                    ctx,
                    universe_context,
                    value,
                    MemoExprOrigin::Retained(value),
                    ty,
                    MemoExprOrigin::Retained(ty),
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition(binder.clone(), (**ty).clone(), (**value).clone());
                let body_ty = self.infer_in_universe_context_with_memo(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    state,
                )?;
                instantiate(&body_ty, value)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_in_universe_context_with_memo(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        term_origin: MemoExprOrigin<'_>,
        expected: &Expr,
        expected_origin: MemoExprOrigin<'_>,
        state: &mut KernelOperationState,
    ) -> Result<()> {
        state.counters.increment(KernelWorkCounter::CheckCall);
        let actual = self.infer_in_universe_context_with_memo(
            ctx,
            universe_context,
            term,
            term_origin,
            state,
        )?;
        if self.is_defeq_with_default_memo(
            ctx,
            &universe_context.params,
            &actual,
            MemoExprOrigin::Fresh,
            expected,
            expected_origin,
            state,
        )? {
            Ok(())
        } else {
            Err(Error::TypeMismatch {
                expected: expected.clone(),
                actual,
            })
        }
    }

    fn expect_sort_in_universe_context_with_memo(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        origin: MemoExprOrigin<'_>,
        state: &mut KernelOperationState,
    ) -> Result<Level> {
        let inferred =
            self.infer_in_universe_context_with_memo(ctx, universe_context, term, origin, state)?;
        match self.whnf_with_default_memo(
            ctx,
            &universe_context.params,
            &inferred,
            MemoExprOrigin::Fresh,
            state,
        )? {
            Expr::Sort(level) => Ok(level),
            actual => Err(Error::ExpectedSort { actual }),
        }
    }

    fn whnf_with_default_memo(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        origin: MemoExprOrigin<'_>,
        state: &mut KernelOperationState,
    ) -> Result<Expr> {
        let mut fuel = Self::WHNF_FUEL;
        let result = self.whnf_with_remaining_fuel_memo(
            ctx,
            delta,
            term,
            origin,
            &mut fuel,
            ResourceLimitKind::Whnf,
            state,
        );
        let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
        state
            .counters
            .record_fuel(Self::WHNF_FUEL - fuel, exhausted);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn is_defeq_with_default_memo(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        lhs_origin: MemoExprOrigin<'_>,
        rhs: &Expr,
        rhs_origin: MemoExprOrigin<'_>,
        state: &mut KernelOperationState,
    ) -> Result<bool> {
        let mut fuel = Self::DEFEQ_FUEL;
        let result = self.is_defeq_with_remaining_fuel_memo(
            ctx, delta, lhs, lhs_origin, rhs, rhs_origin, &mut fuel, state,
        );
        let exhausted = matches!(&result, Err(Error::ResourceLimit { .. }));
        state
            .counters
            .record_fuel(Self::DEFEQ_FUEL - fuel, exhausted);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_with_remaining_fuel_memo_shared(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        _origin: MemoExprOrigin<'_>,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
        state: &mut KernelOperationState,
    ) -> Result<Expr> {
        state.counters.increment(KernelWorkCounter::InferCall);
        match term {
            Expr::Sort(level) => {
                ensure_level_wf(&universe_context.params, level)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            Expr::BVar(index) => {
                state.counters.increment(KernelWorkCounter::ContextLookup);
                state.counters.increment(KernelWorkCounter::ContextShift);
                ctx.lookup_type(*index)
            }
            Expr::Const { name, levels } => {
                self.infer_const_type_in_universe_context(universe_context, name, levels)
            }
            Expr::Pi { binder, ty, body } => {
                let domain_sort = self.expect_sort_with_remaining_fuel_memo_shared(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_sort = self.expect_sort_with_remaining_fuel_memo_shared(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                Ok(Expr::sort(Level::imax(domain_sort, body_sort)))
            }
            Expr::Lam { binder, ty, body } => {
                self.expect_sort_with_remaining_fuel_memo_shared(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_ty = self.infer_with_remaining_fuel_memo_shared(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                Ok(Expr::pi(binder.clone(), (**ty).clone(), body_ty))
            }
            Expr::App(fun, arg) => {
                let fun_ty = self.infer_with_remaining_fuel_memo_shared(
                    ctx,
                    universe_context,
                    fun,
                    MemoExprOrigin::Retained(fun),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                match self.whnf_with_remaining_fuel_memo(
                    ctx,
                    &universe_context.params,
                    &fun_ty,
                    MemoExprOrigin::Fresh,
                    whnf_fuel,
                    ResourceLimitKind::Whnf,
                    state,
                )? {
                    Expr::Pi { ty, body, .. } => {
                        self.check_with_remaining_fuel_memo_shared(
                            ctx,
                            universe_context,
                            arg,
                            MemoExprOrigin::Retained(arg),
                            &ty,
                            MemoExprOrigin::Retained(&ty),
                            whnf_fuel,
                            conversion_fuel,
                            state,
                        )?;
                        instantiate(&body, arg)
                    }
                    actual => Err(Error::ExpectedPi { actual }),
                }
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                self.expect_sort_with_remaining_fuel_memo_shared(
                    ctx,
                    universe_context,
                    ty,
                    MemoExprOrigin::Retained(ty),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                self.check_with_remaining_fuel_memo_shared(
                    ctx,
                    universe_context,
                    value,
                    MemoExprOrigin::Retained(value),
                    ty,
                    MemoExprOrigin::Retained(ty),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition(binder.clone(), (**ty).clone(), (**value).clone());
                let body_ty = self.infer_with_remaining_fuel_memo_shared(
                    &body_ctx,
                    universe_context,
                    body,
                    MemoExprOrigin::Retained(body),
                    whnf_fuel,
                    conversion_fuel,
                    state,
                )?;
                instantiate(&body_ty, value)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_remaining_fuel_memo_shared(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        term_origin: MemoExprOrigin<'_>,
        expected: &Expr,
        expected_origin: MemoExprOrigin<'_>,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
        state: &mut KernelOperationState,
    ) -> Result<()> {
        state.counters.increment(KernelWorkCounter::CheckCall);
        let actual = self.infer_with_remaining_fuel_memo_shared(
            ctx,
            universe_context,
            term,
            term_origin,
            whnf_fuel,
            conversion_fuel,
            state,
        )?;
        if self.is_defeq_with_remaining_fuel_memo(
            ctx,
            &universe_context.params,
            &actual,
            MemoExprOrigin::Fresh,
            expected,
            expected_origin,
            conversion_fuel,
            state,
        )? {
            Ok(())
        } else {
            Err(Error::TypeMismatch {
                expected: expected.clone(),
                actual,
            })
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn expect_sort_with_remaining_fuel_memo_shared(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        origin: MemoExprOrigin<'_>,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
        state: &mut KernelOperationState,
    ) -> Result<Level> {
        let ty = self.infer_with_remaining_fuel_memo_shared(
            ctx,
            universe_context,
            term,
            origin,
            whnf_fuel,
            conversion_fuel,
            state,
        )?;
        match self.whnf_with_remaining_fuel_memo(
            ctx,
            &universe_context.params,
            &ty,
            MemoExprOrigin::Fresh,
            whnf_fuel,
            ResourceLimitKind::Whnf,
            state,
        )? {
            Expr::Sort(level) => Ok(level),
            actual => Err(Error::ExpectedSort { actual }),
        }
    }

    fn infer_with_remaining_fuel(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<Expr> {
        match term {
            Expr::Sort(level) => {
                ensure_level_wf(&universe_context.params, level)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            Expr::BVar(index) => ctx.lookup_type(*index),
            Expr::Const { name, levels } => {
                self.infer_const_type_in_universe_context(universe_context, name, levels)
            }
            Expr::Pi { binder, ty, body } => {
                let domain_sort = self.expect_sort_with_remaining_fuel(
                    ctx,
                    universe_context,
                    ty,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_sort = self.expect_sort_with_remaining_fuel(
                    &body_ctx,
                    universe_context,
                    body,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                Ok(Expr::sort(Level::imax(domain_sort, body_sort)))
            }
            Expr::Lam { binder, ty, body } => {
                self.expect_sort_with_remaining_fuel(
                    ctx,
                    universe_context,
                    ty,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**ty).clone());
                let body_ty = self.infer_with_remaining_fuel(
                    &body_ctx,
                    universe_context,
                    body,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                Ok(Expr::pi(binder.clone(), (**ty).clone(), body_ty))
            }
            Expr::App(fun, arg) => {
                let fun_ty = self.infer_with_remaining_fuel(
                    ctx,
                    universe_context,
                    fun,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                match self.whnf_with_remaining_fuel(
                    ctx,
                    &universe_context.params,
                    &fun_ty,
                    whnf_fuel,
                    ResourceLimitKind::Whnf,
                    &mut DisabledKernelWorkMeter,
                )? {
                    Expr::Pi { ty, body, .. } => {
                        self.check_with_remaining_fuel(
                            ctx,
                            universe_context,
                            arg,
                            &ty,
                            whnf_fuel,
                            conversion_fuel,
                        )?;
                        instantiate(&body, arg)
                    }
                    actual => Err(Error::ExpectedPi { actual }),
                }
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                self.expect_sort_with_remaining_fuel(
                    ctx,
                    universe_context,
                    ty,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                self.check_with_remaining_fuel(
                    ctx,
                    universe_context,
                    value,
                    ty,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                let mut body_ctx = ctx.clone();
                body_ctx.push_definition(binder.clone(), (**ty).clone(), (**value).clone());
                let body_ty = self.infer_with_remaining_fuel(
                    &body_ctx,
                    universe_context,
                    body,
                    whnf_fuel,
                    conversion_fuel,
                )?;
                instantiate(&body_ty, value)
            }
        }
    }

    fn check_with_remaining_fuel(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        expected: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<()> {
        let actual = self.infer_with_remaining_fuel(
            ctx,
            universe_context,
            term,
            whnf_fuel,
            conversion_fuel,
        )?;
        if self.is_defeq_with_remaining_fuel(
            ctx,
            &universe_context.params,
            &actual,
            expected,
            conversion_fuel,
            &mut DisabledKernelWorkMeter,
        )? {
            Ok(())
        } else {
            Err(Error::TypeMismatch {
                expected: expected.clone(),
                actual,
            })
        }
    }

    fn expect_sort_with_remaining_fuel(
        &self,
        ctx: &Ctx,
        universe_context: &UniverseContext,
        term: &Expr,
        whnf_fuel: &mut usize,
        conversion_fuel: &mut usize,
    ) -> Result<Level> {
        let ty = self.infer_with_remaining_fuel(
            ctx,
            universe_context,
            term,
            whnf_fuel,
            conversion_fuel,
        )?;
        match self.whnf_with_remaining_fuel(
            ctx,
            &universe_context.params,
            &ty,
            whnf_fuel,
            ResourceLimitKind::Whnf,
            &mut DisabledKernelWorkMeter,
        )? {
            Expr::Sort(level) => Ok(level),
            actual => Err(Error::ExpectedSort { actual }),
        }
    }

    fn check_constructor_decl(
        &self,
        data: &InductiveDecl,
        constructor: &ConstructorDecl,
        universe_context: &UniverseContext,
    ) -> Result<()> {
        self.expect_sort_in_universe_context(&Ctx::new(), universe_context, &constructor.ty)?;
        let (domains, result) = peel_pi_domains(&constructor.ty);
        for (domain_index, domain) in domains.iter().enumerate() {
            check_constructor_domain_positive(self, data, &constructor.name, domain_index, domain)?;
        }

        let result = self.whnf(&Ctx::new(), &universe_context.params, &result)?;
        self.check_constructor_result(data, constructor, domains.len(), result)?;
        self.check_constructor_universe_bounds(data, constructor, &domains, universe_context)
    }

    fn check_mutual_constructor_decl(
        &self,
        block: &MutualInductiveBlock,
        data: &InductiveDecl,
        constructor: &ConstructorDecl,
        universe_context: &UniverseContext,
    ) -> Result<()> {
        self.expect_sort_in_universe_context(&Ctx::new(), universe_context, &constructor.ty)?;
        let (domains, result) = peel_pi_domains(&constructor.ty);
        for (domain_index, domain) in domains.iter().enumerate() {
            check_mutual_constructor_domain_positive(
                self,
                block,
                data,
                &constructor.name,
                domain_index,
                domain,
            )?;
        }

        let result = self.whnf(&Ctx::new(), &universe_context.params, &result)?;
        self.check_constructor_result(data, constructor, domains.len(), result)?;
        self.check_constructor_universe_bounds(data, constructor, &domains, universe_context)
    }

    fn check_constructor_universe_bounds(
        &self,
        data: &InductiveDecl,
        constructor: &ConstructorDecl,
        domains: &[Expr],
        universe_context: &UniverseContext,
    ) -> Result<()> {
        let inductive_sort = normalize_level(data.sort.clone());
        if inductive_sort == Level::zero() {
            return Ok(());
        }

        let mut ctx = Ctx::new();
        let mut whnf_fuel = Self::WHNF_FUEL;
        let mut conversion_fuel = Self::DEFEQ_FUEL;
        for (domain_index, domain) in domains.iter().enumerate() {
            let field_level = self.expect_sort_with_remaining_fuel(
                &ctx,
                universe_context,
                domain,
                &mut whnf_fuel,
                &mut conversion_fuel,
            )?;
            if domain_index >= data.params.len()
                && !universe_context.entails_level_le(&field_level, &inductive_sort)?
            {
                return Err(Error::ConstructorUniverseBoundViolation {
                    inductive: data.name.clone(),
                    constructor: constructor.name.clone(),
                    field_index: domain_index - data.params.len(),
                    field_level: normalize_level(field_level),
                    inductive_sort,
                });
            }
            ctx.push_assumption("_", domain.clone());
        }
        Ok(())
    }

    fn check_recursor_decl(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        rules: &RecursorRules,
        universe_context: &UniverseContext,
    ) -> Result<()> {
        if rules.minor_start != data.params.len() + 1 {
            return Err(Error::InvalidInductive(format!(
                "{} recursor minor_start must be params + motive",
                data.name
            )));
        }
        if rules.major_index != rules.minor_start + data.constructors.len() + data.indices.len() {
            return Err(Error::InvalidInductive(format!(
                "{} recursor major_index must follow constructor minor premises and indices",
                data.name
            )));
        }

        let (domains, result) = peel_pi_domains(&recursor.ty);
        if domains.len() <= rules.major_index {
            return Err(Error::InvalidInductive(format!(
                "{} recursor has no major premise",
                recursor.name
            )));
        }
        if domains.len() != rules.major_index + 1 {
            return Err(Error::InvalidInductive(format!(
                "{} recursor major premise must be the final binder in kernel core",
                recursor.name
            )));
        }

        self.check_recursor_params(data, recursor, &domains, universe_context)?;

        let motive_domain = domains.get(data.params.len()).ok_or_else(|| {
            Error::InvalidInductive(format!("{} recursor is missing motive", recursor.name))
        })?;
        self.check_motive_domain(data, recursor, motive_domain)?;

        self.check_recursor_indices(data, recursor, rules, &domains, universe_context)?;

        let major_domain = &domains[rules.major_index];
        self.check_recursor_target(
            data,
            recursor,
            major_domain,
            "major premise",
            rules.major_index,
            rules.minor_start + data.constructors.len(),
        )?;
        self.check_recursor_result(data, recursor, rules, &domains, &result, universe_context)?;

        for (constructor_index, constructor) in data.constructors.iter().enumerate() {
            let minor_index = rules.minor_start + constructor_index;
            let minor_domain = &domains[rules.minor_start + constructor_index];
            let expected_minor = expected_minor_type(data, constructor, constructor_index)?;
            let prefix_ctx = recursor_prefix_ctx(&domains[..minor_index]);
            if !self.is_defeq(
                &prefix_ctx,
                &universe_context.params,
                minor_domain,
                &expected_minor,
            )? {
                return Err(Error::InvalidInductive(format!(
                    "{} minor premise for {} does not match constructor",
                    recursor.name, constructor.name
                )));
            }
        }

        Ok(())
    }

    fn check_mutual_recursor_decl(
        &self,
        block: &MutualInductiveBlock,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        rules: &RecursorRules,
        universe_context: &UniverseContext,
    ) -> Result<()> {
        let param_count = data.params.len();
        let motive_count = block.inductives.len();
        let minor_start = param_count + motive_count;
        let constructor_count = mutual_constructor_count(block);
        if rules.minor_start != minor_start {
            return Err(Error::InvalidInductive(format!(
                "{} mutual recursor minor_start must follow params and motives",
                recursor.name
            )));
        }
        if rules.major_index != minor_start + constructor_count + data.indices.len() {
            return Err(Error::InvalidInductive(format!(
                "{} mutual recursor major_index must follow all minor premises and target indices",
                recursor.name
            )));
        }

        let (domains, result) = peel_pi_domains(&recursor.ty);
        if domains.len() != rules.major_index + 1 {
            return Err(Error::InvalidInductive(format!(
                "{} mutual recursor major premise must be the final binder",
                recursor.name
            )));
        }

        self.check_recursor_params(data, recursor, &domains, universe_context)?;
        for (family_index, family) in block.inductives.iter().enumerate() {
            let motive_domain = domains.get(param_count + family_index).ok_or_else(|| {
                Error::InvalidInductive(format!(
                    "{} mutual recursor is missing motive for {}",
                    recursor.name, family.name
                ))
            })?;
            self.check_motive_domain(family, recursor, motive_domain)?;
        }

        let target_family_index = mutual_family_index(block, &data.name)?;
        let index_start = rules.minor_start + constructor_count;
        self.check_recursor_indices_at(data, recursor, index_start, &domains, universe_context)?;
        self.check_recursor_target(
            data,
            recursor,
            &domains[rules.major_index],
            "major premise",
            rules.major_index,
            index_start,
        )?;
        self.check_mutual_recursor_result(MutualRecursorResultCheck {
            data,
            recursor,
            rules,
            domains: &domains,
            result: &result,
            universe_context,
            family_index: target_family_index,
            index_start,
        })?;

        let mut constructor_index = 0usize;
        for (family_index, family) in block.inductives.iter().enumerate() {
            for constructor in &family.constructors {
                let minor_index = rules.minor_start + constructor_index;
                let expected_minor = expected_mutual_minor_type(
                    block,
                    family_index,
                    constructor,
                    constructor_index,
                )?;
                let prefix_ctx = recursor_prefix_ctx(&domains[..minor_index]);
                if !self.is_defeq(
                    &prefix_ctx,
                    &universe_context.params,
                    &domains[minor_index],
                    &expected_minor,
                )? {
                    return Err(Error::InvalidInductive(format!(
                        "{} minor premise for {} does not match mutual constructor",
                        recursor.name, constructor.name
                    )));
                }
                constructor_index += 1;
            }
        }

        Ok(())
    }

    fn check_constructor_result(
        &self,
        data: &InductiveDecl,
        constructor: &ConstructorDecl,
        domain_count: usize,
        result: Expr,
    ) -> Result<()> {
        let (head, args) = collect_apps(&result);
        let levels = match head {
            Expr::Const { name, levels } if name == data.name => levels,
            _ => {
                return Err(Error::BadConstructorResult {
                    inductive: data.name.clone(),
                    constructor: constructor.name.clone(),
                    result,
                })
            }
        };

        let expected_levels: Vec<_> = data
            .universe_params
            .iter()
            .map(|param| Level::param(param.clone()))
            .collect();
        if !levels_eq(&levels, &expected_levels)
            || args.len() != data.params.len() + data.indices.len()
            || domain_count < data.params.len()
        {
            return Err(Error::BadConstructorResult {
                inductive: data.name.clone(),
                constructor: constructor.name.clone(),
                result,
            });
        }

        for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
            let expected = Expr::bvar((domain_count - 1 - param_index) as u32);
            if arg != &expected {
                return Err(Error::BadConstructorResult {
                    inductive: data.name.clone(),
                    constructor: constructor.name.clone(),
                    result,
                });
            }
        }

        Ok(())
    }

    fn check_recursor_params(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        domains: &[Expr],
        universe_context: &UniverseContext,
    ) -> Result<()> {
        if domains.len() < data.params.len() {
            return Err(Error::InvalidInductive(format!(
                "{} recursor is missing parameter binders",
                recursor.name
            )));
        }

        let mut ctx = Ctx::new();
        for (param_index, param) in data.params.iter().enumerate() {
            self.expect_sort_in_universe_context(&ctx, universe_context, &param.ty)?;
            if !self.is_defeq(
                &ctx,
                &universe_context.params,
                &domains[param_index],
                &param.ty,
            )? {
                return Err(Error::InvalidInductive(format!(
                    "{} recursor parameter {} does not match inductive",
                    recursor.name, param.name
                )));
            }
            ctx.push_assumption(param.name.clone(), param.ty.clone());
        }

        Ok(())
    }

    fn check_motive_domain(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        motive_domain: &Expr,
    ) -> Result<()> {
        let (motive_domains, motive_result) = peel_pi_domains(motive_domain);
        if motive_domains.len() != data.indices.len() + 1 {
            return Err(Error::InvalidInductive(format!(
                "{} motive must take indices and one major premise in kernel core",
                recursor.name
            )));
        }
        let target_index_start = data.params.len();
        for (index, expected) in data.indices.iter().enumerate() {
            let source_ctx_len = data.params.len() + index;
            let target_ctx_len = data.params.len() + index;
            let source_to_target = (0..source_ctx_len).collect::<Vec<_>>();
            let expected_ty = remap_bvars(
                &expected.ty,
                source_ctx_len,
                target_ctx_len,
                &source_to_target,
            )?;
            if motive_domains[index] != expected_ty {
                return Err(Error::InvalidInductive(format!(
                    "{} motive index {} does not match inductive",
                    recursor.name, expected.name
                )));
            }
        }
        self.check_recursor_target(
            data,
            recursor,
            &motive_domains[data.indices.len()],
            "motive domain",
            data.params.len() + data.indices.len(),
            target_index_start,
        )?;
        match motive_result {
            Expr::Sort(level) => {
                if level_eq(&data.sort, &Level::zero()) && !level_eq(&level, &Level::zero()) {
                    return Err(Error::InvalidInductive(format!(
                        "{} Prop recursor motive must return Prop",
                        recursor.name
                    )));
                }
            }
            _ => {
                return Err(Error::InvalidInductive(format!(
                    "{} motive must return a Sort",
                    recursor.name
                )))
            }
        }
        Ok(())
    }

    fn check_recursor_indices(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        rules: &RecursorRules,
        domains: &[Expr],
        universe_context: &UniverseContext,
    ) -> Result<()> {
        let index_start = rules.minor_start + data.constructors.len();
        self.check_recursor_indices_at(data, recursor, index_start, domains, universe_context)
    }

    fn check_recursor_indices_at(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        index_start: usize,
        domains: &[Expr],
        universe_context: &UniverseContext,
    ) -> Result<()> {
        let mut source_to_target = (0..data.params.len()).collect::<Vec<_>>();
        for (index, expected) in data.indices.iter().enumerate() {
            let domain_index = index_start + index;
            let Some(actual) = domains.get(domain_index) else {
                return Err(Error::InvalidInductive(format!(
                    "{} recursor is missing index binder {}",
                    recursor.name, expected.name
                )));
            };
            let source_ctx_len = data.params.len() + index;
            let target_ctx_len = domain_index;
            let expected_ty = remap_bvars(
                &expected.ty,
                source_ctx_len,
                target_ctx_len,
                &source_to_target,
            )?;
            let ctx = recursor_prefix_ctx(&domains[..domain_index]);
            if !self.is_defeq(&ctx, &universe_context.params, actual, &expected_ty)? {
                return Err(Error::InvalidInductive(format!(
                    "{} recursor index {} does not match inductive",
                    recursor.name, expected.name
                )));
            }
            source_to_target.push(domain_index);
        }
        Ok(())
    }

    fn check_recursor_target(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        target: &Expr,
        label: &str,
        ctx_len: usize,
        index_abs_start: usize,
    ) -> Result<()> {
        let (head, args) = collect_apps(target);
        let levels = match head {
            Expr::Const { name, levels } if name == data.name => levels,
            _ => {
                return Err(Error::InvalidInductive(format!(
                    "{} {} must target {}",
                    recursor.name, label, data.name
                )));
            }
        };
        let expected_levels: Vec<_> = data
            .universe_params
            .iter()
            .map(|param| Level::param(param.clone()))
            .collect();
        if !levels_eq(&levels, &expected_levels)
            || args.len() != data.params.len() + data.indices.len()
        {
            return Err(Error::InvalidInductive(format!(
                "{} {} must target {}",
                recursor.name, label, data.name
            )));
        }
        for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
            if arg != &bvar_for_abs(ctx_len, param_index)? {
                return Err(Error::InvalidInductive(format!(
                    "{} {} has non-canonical parameter {}",
                    recursor.name, label, param_index
                )));
            }
        }
        for (index_index, arg) in args.iter().skip(data.params.len()).enumerate() {
            if arg != &bvar_for_abs(ctx_len, index_abs_start + index_index)? {
                return Err(Error::InvalidInductive(format!(
                    "{} {} has non-canonical index {}",
                    recursor.name, label, index_index
                )));
            }
        }
        Ok(())
    }

    fn check_recursor_result(
        &self,
        data: &InductiveDecl,
        recursor: &RecursorDecl,
        rules: &RecursorRules,
        domains: &[Expr],
        result: &Expr,
        universe_context: &UniverseContext,
    ) -> Result<()> {
        let index_start = rules.minor_start + data.constructors.len();
        let index_args = (0..data.indices.len())
            .map(|index| bvar_for_abs(domains.len(), index_start + index))
            .collect::<Result<Vec<_>>>()?;
        let expected = motive_app(
            domains.len(),
            data.params.len(),
            index_args,
            bvar_for_abs(domains.len(), rules.major_index)?,
        )?;
        let result_ctx = recursor_prefix_ctx(domains);
        if self.is_defeq(&result_ctx, &universe_context.params, result, &expected)? {
            Ok(())
        } else {
            Err(Error::InvalidInductive(format!(
                "{} result must apply motive to the major premise",
                recursor.name
            )))
        }
    }

    fn check_mutual_recursor_result(&self, check: MutualRecursorResultCheck<'_>) -> Result<()> {
        let index_args = (0..check.data.indices.len())
            .map(|index| bvar_for_abs(check.domains.len(), check.index_start + index))
            .collect::<Result<Vec<_>>>()?;
        let expected = motive_app(
            check.domains.len(),
            check.data.params.len() + check.family_index,
            index_args,
            bvar_for_abs(check.domains.len(), check.rules.major_index)?,
        )?;
        let result_ctx = recursor_prefix_ctx(check.domains);
        if self.is_defeq(
            &result_ctx,
            &check.universe_context.params,
            check.result,
            &expected,
        )? {
            Ok(())
        } else {
            Err(Error::InvalidInductive(format!(
                "{} result must apply the matching mutual motive to the major premise",
                check.recursor.name
            )))
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn whnf_with_remaining_fuel_memo(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        origin: MemoExprOrigin<'_>,
        fuel: &mut usize,
        kind: ResourceLimitKind,
        state: &mut KernelOperationState,
    ) -> Result<Expr> {
        let lookup = state
            .memo
            .whnf_lookup(origin, ctx, delta, kind, &mut state.counters);
        let token = match lookup {
            WhnfMemoLookup::Hit { result, fuel_cost } => {
                replay_memo_fuel(fuel, fuel_cost, kind, &mut state.counters)?;
                KernelWorkCounters::add(
                    &mut state.counters.memo_bypassed_call_bodies,
                    1,
                    &mut state.counters.overflowed,
                );
                return Ok(result);
            }
            WhnfMemoLookup::Miss(token) => Some(token),
            WhnfMemoLookup::Ineligible => None,
        };

        let starting_fuel = *fuel;
        state.counters.increment(KernelWorkCounter::WhnfCall);
        let result = (|| {
            let mut current = term.clone();
            loop {
                spend_fuel(fuel, kind)?;

                match current {
                    Expr::BVar(index) => {
                        state.counters.increment(KernelWorkCounter::ContextLookup);
                        let value = ctx.lookup_value(index)?;
                        if let Some(value) = value {
                            state.counters.increment(KernelWorkCounter::ContextShift);
                            record_reduction(&mut state.counters, KernelWorkCounter::ZetaStep);
                            current = value;
                        } else {
                            return Ok(Expr::BVar(index));
                        }
                    }
                    Expr::Const {
                        ref name,
                        ref levels,
                    } => {
                        if let Some(
                            Decl::Def {
                                universe_params,
                                value,
                                reducibility: Reducibility::Reducible,
                                ..
                            }
                            | Decl::DefConstrained {
                                universe_params,
                                value,
                                reducibility: Reducibility::Reducible,
                                ..
                            },
                        ) = self.decls.get(name)
                        {
                            record_reduction(&mut state.counters, KernelWorkCounter::DeltaStep);
                            current = subst_levels_expr(value, universe_params, levels);
                        } else {
                            return Ok(current);
                        }
                    }
                    Expr::App(fun, arg) => {
                        let fun_whnf = self.whnf_with_remaining_fuel_memo(
                            ctx,
                            delta,
                            &fun,
                            MemoExprOrigin::Retained(&fun),
                            fuel,
                            kind,
                            state,
                        )?;
                        if let Expr::Lam { body, .. } = fun_whnf {
                            record_reduction(&mut state.counters, KernelWorkCounter::BetaStep);
                            current = instantiate(&body, &arg)?;
                            continue;
                        }

                        let app = Expr::App(Arc::new(fun_whnf), arg);
                        if let Some(reduced) =
                            self.reduce_recursor_memo(ctx, delta, &app, fuel, kind, state)?
                        {
                            record_reduction(&mut state.counters, KernelWorkCounter::IotaStep);
                            current = reduced;
                            continue;
                        }
                        return Ok(app);
                    }
                    Expr::Let { value, body, .. } => {
                        record_reduction(&mut state.counters, KernelWorkCounter::ZetaStep);
                        current = instantiate(&body, &value)?;
                    }
                    _ => return Ok(current),
                }
            }
        })();

        if let (Some(token), Ok(value)) = (token, &result) {
            state.memo.insert_whnf(
                token,
                value,
                starting_fuel.saturating_sub(*fuel),
                &mut state.counters,
            );
        }
        result
    }

    fn whnf_with_remaining_fuel(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        fuel: &mut usize,
        kind: ResourceLimitKind,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<Expr> {
        meter.increment(KernelWorkCounter::WhnfCall);
        let mut current = term.clone();
        loop {
            spend_fuel(fuel, kind)?;

            match current {
                Expr::BVar(index) => {
                    meter.increment(KernelWorkCounter::ContextLookup);
                    let value = ctx.lookup_value(index)?;
                    if let Some(value) = value {
                        meter.increment(KernelWorkCounter::ContextShift);
                        record_reduction(meter, KernelWorkCounter::ZetaStep);
                        current = value;
                    } else {
                        return Ok(Expr::BVar(index));
                    }
                }
                Expr::Const {
                    ref name,
                    ref levels,
                } => {
                    if let Some(
                        Decl::Def {
                            universe_params,
                            value,
                            reducibility: Reducibility::Reducible,
                            ..
                        }
                        | Decl::DefConstrained {
                            universe_params,
                            value,
                            reducibility: Reducibility::Reducible,
                            ..
                        },
                    ) = self.decls.get(name)
                    {
                        record_reduction(meter, KernelWorkCounter::DeltaStep);
                        current = subst_levels_expr(value, universe_params, levels);
                    } else {
                        return Ok(current);
                    }
                }
                Expr::App(fun, arg) => {
                    let fun_whnf =
                        self.whnf_with_remaining_fuel(ctx, delta, &fun, fuel, kind, meter)?;
                    if let Expr::Lam { body, .. } = fun_whnf {
                        record_reduction(meter, KernelWorkCounter::BetaStep);
                        current = instantiate(&body, &arg)?;
                        continue;
                    }

                    let app = Expr::App(Arc::new(fun_whnf), arg);
                    if let Some(reduced) =
                        self.reduce_recursor(ctx, delta, &app, fuel, kind, meter)?
                    {
                        record_reduction(meter, KernelWorkCounter::IotaStep);
                        current = reduced;
                        continue;
                    }
                    return Ok(app);
                }
                Expr::Let { value, body, .. } => {
                    record_reduction(meter, KernelWorkCounter::ZetaStep);
                    current = instantiate(&body, &value)?;
                }
                _ => return Ok(current),
            }
        }
    }

    fn reduce_recursor_memo(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        fuel: &mut usize,
        kind: ResourceLimitKind,
        state: &mut KernelOperationState,
    ) -> Result<Option<Expr>> {
        let (head, retained_args) = collect_apps_with_retained_args(term);
        let Expr::Const {
            name: recursor_name,
            levels,
        } = head
        else {
            return Ok(None);
        };
        let Some(Decl::Recursor {
            inductive, rules, ..
        }) = self.decls.get(&recursor_name)
        else {
            return Ok(None);
        };
        if retained_args.len() <= rules.major_index {
            return Ok(None);
        }

        let major = &retained_args[rules.major_index];
        let major_whnf = self.whnf_with_remaining_fuel_memo(
            ctx,
            delta,
            major,
            MemoExprOrigin::Retained(major),
            fuel,
            kind,
            state,
        )?;
        let args = retained_args
            .iter()
            .map(|argument| (**argument).clone())
            .collect::<Vec<_>>();
        self.finish_recursor_reduction(&recursor_name, &levels, inductive, rules, &args, major_whnf)
    }

    fn reduce_recursor(
        &self,
        ctx: &Ctx,
        delta: &[String],
        term: &Expr,
        fuel: &mut usize,
        kind: ResourceLimitKind,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<Option<Expr>> {
        let (head, args) = collect_apps(term);
        let Expr::Const {
            name: recursor_name,
            levels,
        } = head
        else {
            return Ok(None);
        };
        let Some(Decl::Recursor {
            inductive, rules, ..
        }) = self.decls.get(&recursor_name)
        else {
            return Ok(None);
        };
        if args.len() <= rules.major_index {
            return Ok(None);
        }

        let major = args[rules.major_index].clone();
        let major_whnf = self.whnf_with_remaining_fuel(ctx, delta, &major, fuel, kind, meter)?;
        self.finish_recursor_reduction(&recursor_name, &levels, inductive, rules, &args, major_whnf)
    }

    #[allow(clippy::too_many_arguments)]
    fn finish_recursor_reduction(
        &self,
        recursor_name: &str,
        levels: &[Level],
        inductive: &str,
        rules: &RecursorRules,
        args: &[Expr],
        major_whnf: Expr,
    ) -> Result<Option<Expr>> {
        let rest = args[rules.major_index + 1..].to_vec();
        let (ctor_head, ctor_args) = collect_apps(&major_whnf);
        let Expr::Const {
            name: ctor_name, ..
        } = ctor_head
        else {
            return Ok(None);
        };
        if !self.constructor_belongs_to(&ctor_name, inductive) {
            return Ok(None);
        }

        let data = self.inductive_data(inductive)?;
        let mutual_group = self.mutual_groups.get(inductive).cloned();
        let Some(ctor_index) = data
            .constructors
            .iter()
            .position(|constructor| constructor.name == ctor_name)
        else {
            return Ok(None);
        };
        let block_ctor_offset = match &mutual_group {
            Some(group) => mutual_constructor_offset(self, group, inductive)?,
            None => 0,
        };
        let Some(minor) = args
            .get(rules.minor_start + block_ctor_offset + ctor_index)
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
        let index_start = rules.major_index - data.indices.len();
        let field_args = &ctor_args[param_count..];
        let field_domains = &domains[param_count..];
        if field_args.len() < field_domains.len() {
            return Ok(None);
        }

        let mut reduced = minor;
        for (field_index, (field_arg, field_domain)) in
            field_args.iter().zip(field_domains).enumerate()
        {
            reduced = Expr::app(reduced, field_arg.clone());
            if let Some(group) = &mutual_group {
                if let Ok((field_inductive, index_args)) = direct_mutual_recursive_index_args(
                    self,
                    group,
                    field_domain,
                    param_count + field_index,
                ) {
                    let source_ctx_len = param_count + field_index;
                    let source_args = &ctor_args[..source_ctx_len];
                    let Some(recursive_recursor_name) = group.recursors.get(&field_inductive)
                    else {
                        return Err(Error::InvalidInductive(format!(
                            "{field_inductive} has no mutual recursor"
                        )));
                    };
                    let recursive_data = self.inductive_data(&field_inductive)?;
                    let mut recursive_args = args[..index_start].to_vec();
                    for index_arg in index_args {
                        recursive_args.push(instantiate_constructor_args(&index_arg, source_args)?);
                    }
                    if recursive_args.len() != index_start + recursive_data.indices.len() {
                        return Err(Error::InvalidInductive(format!(
                            "{} recursive call index arity mismatch",
                            recursive_recursor_name
                        )));
                    }
                    recursive_args.push(field_arg.clone());
                    reduced = Expr::app(
                        reduced,
                        Expr::apps(
                            Expr::konst(recursive_recursor_name.clone(), levels.to_vec()),
                            recursive_args,
                        ),
                    );
                }
            } else if is_direct_recursive_domain(data, field_domain, param_count + field_index) {
                let source_ctx_len = param_count + field_index;
                let source_args = &ctor_args[..source_ctx_len];
                let mut recursive_args = args[..index_start].to_vec();
                for index_arg in direct_recursive_index_args(data, field_domain, source_ctx_len)? {
                    recursive_args.push(instantiate_constructor_args(&index_arg, source_args)?);
                }
                recursive_args.push(field_arg.clone());
                reduced = Expr::app(
                    reduced,
                    Expr::apps(
                        Expr::konst(recursor_name.to_owned(), levels.to_vec()),
                        recursive_args,
                    ),
                );
            }
        }

        Ok(Some(Expr::apps(reduced, rest)))
    }

    fn constructor_belongs_to(&self, constructor: &str, inductive: &str) -> bool {
        matches!(
            self.decls.get(constructor),
            Some(Decl::Constructor {
                inductive: owner, ..
            }) if owner == inductive
        )
    }

    fn inductive_data(&self, name: &str) -> Result<&InductiveDecl> {
        match self.decls.get(name) {
            Some(Decl::Inductive { data, .. }) => Ok(data.as_ref()),
            _ => Err(Error::InvalidInductive(name.to_owned())),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn is_defeq_with_remaining_fuel_memo(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        lhs_origin: MemoExprOrigin<'_>,
        rhs: &Expr,
        rhs_origin: MemoExprOrigin<'_>,
        fuel: &mut usize,
        state: &mut KernelOperationState,
    ) -> Result<bool> {
        let lookup =
            state
                .memo
                .defeq_lookup(lhs_origin, rhs_origin, ctx, delta, &mut state.counters);
        let token = match lookup {
            DefeqMemoLookup::Hit { fuel_cost } => {
                replay_memo_fuel(
                    fuel,
                    fuel_cost,
                    ResourceLimitKind::Conversion,
                    &mut state.counters,
                )?;
                KernelWorkCounters::add(
                    &mut state.counters.memo_bypassed_call_bodies,
                    1,
                    &mut state.counters.overflowed,
                );
                return Ok(true);
            }
            DefeqMemoLookup::Miss(token) => Some(token),
            DefeqMemoLookup::Ineligible => None,
        };

        let starting_fuel = *fuel;
        state.counters.increment(KernelWorkCounter::DefeqCall);
        let result = (|| {
            spend_fuel(fuel, ResourceLimitKind::Conversion)?;
            if quick_syntactic_eq(lhs, rhs) {
                state
                    .counters
                    .increment(KernelWorkCounter::QuickEqualityHit);
                return Ok(true);
            }

            let lhs = self.whnf_with_remaining_fuel_memo(
                ctx,
                delta,
                lhs,
                lhs_origin,
                fuel,
                ResourceLimitKind::Conversion,
                state,
            )?;
            let rhs = self.whnf_with_remaining_fuel_memo(
                ctx,
                delta,
                rhs,
                rhs_origin,
                fuel,
                ResourceLimitKind::Conversion,
                state,
            )?;

            match (&lhs, &rhs) {
                (Expr::Sort(lhs), Expr::Sort(rhs)) => Ok(level_eq(lhs, rhs)),
                (Expr::BVar(lhs), Expr::BVar(rhs)) => Ok(lhs == rhs),
                (
                    Expr::Const {
                        name: lhs_name,
                        levels: lhs_levels,
                    },
                    Expr::Const {
                        name: rhs_name,
                        levels: rhs_levels,
                    },
                ) => Ok(lhs_name == rhs_name && levels_eq(lhs_levels, rhs_levels)),
                (Expr::App(lhs_f, lhs_a), Expr::App(rhs_f, rhs_a)) => {
                    Ok(self.is_defeq_with_remaining_fuel_memo(
                        ctx,
                        delta,
                        lhs_f,
                        MemoExprOrigin::Retained(lhs_f),
                        rhs_f,
                        MemoExprOrigin::Retained(rhs_f),
                        fuel,
                        state,
                    )? && self.is_defeq_with_remaining_fuel_memo(
                        ctx,
                        delta,
                        lhs_a,
                        MemoExprOrigin::Retained(lhs_a),
                        rhs_a,
                        MemoExprOrigin::Retained(rhs_a),
                        fuel,
                        state,
                    )?)
                }
                (
                    Expr::Pi {
                        binder,
                        ty: lhs_ty,
                        body: lhs_body,
                    },
                    Expr::Pi {
                        ty: rhs_ty,
                        body: rhs_body,
                        ..
                    },
                ) => {
                    if !self.is_defeq_with_remaining_fuel_memo(
                        ctx,
                        delta,
                        lhs_ty,
                        MemoExprOrigin::Retained(lhs_ty),
                        rhs_ty,
                        MemoExprOrigin::Retained(rhs_ty),
                        fuel,
                        state,
                    )? {
                        return Ok(false);
                    }
                    let mut body_ctx = ctx.clone();
                    body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                    self.is_defeq_with_remaining_fuel_memo(
                        &body_ctx,
                        delta,
                        lhs_body,
                        MemoExprOrigin::Retained(lhs_body),
                        rhs_body,
                        MemoExprOrigin::Retained(rhs_body),
                        fuel,
                        state,
                    )
                }
                (
                    Expr::Lam {
                        binder,
                        ty: lhs_ty,
                        body: lhs_body,
                    },
                    Expr::Lam {
                        ty: rhs_ty,
                        body: rhs_body,
                        ..
                    },
                ) => {
                    if !self.is_defeq_with_remaining_fuel_memo(
                        ctx,
                        delta,
                        lhs_ty,
                        MemoExprOrigin::Retained(lhs_ty),
                        rhs_ty,
                        MemoExprOrigin::Retained(rhs_ty),
                        fuel,
                        state,
                    )? {
                        return Ok(false);
                    }
                    let mut body_ctx = ctx.clone();
                    body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                    self.is_defeq_with_remaining_fuel_memo(
                        &body_ctx,
                        delta,
                        lhs_body,
                        MemoExprOrigin::Retained(lhs_body),
                        rhs_body,
                        MemoExprOrigin::Retained(rhs_body),
                        fuel,
                        state,
                    )
                }
                _ => Ok(false),
            }
        })();

        if let (Some(token), Ok(true)) = (token, &result) {
            state.memo.insert_defeq(
                token,
                starting_fuel.saturating_sub(*fuel),
                &mut state.counters,
            );
        }
        result
    }

    fn is_defeq_with_remaining_fuel(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: &mut usize,
        meter: &mut impl KernelWorkMeter,
    ) -> Result<bool> {
        meter.increment(KernelWorkCounter::DefeqCall);
        spend_fuel(fuel, ResourceLimitKind::Conversion)?;

        // Syntactically identical terms are definitionally equal by
        // reflexivity; this avoids reducing both sides to weak head normal
        // form on the common reflexive comparison.
        if quick_syntactic_eq(lhs, rhs) {
            meter.increment(KernelWorkCounter::QuickEqualityHit);
            return Ok(true);
        }

        let lhs = self.whnf_with_remaining_fuel(
            ctx,
            delta,
            lhs,
            fuel,
            ResourceLimitKind::Conversion,
            meter,
        )?;
        let rhs = self.whnf_with_remaining_fuel(
            ctx,
            delta,
            rhs,
            fuel,
            ResourceLimitKind::Conversion,
            meter,
        )?;

        match (&lhs, &rhs) {
            (Expr::Sort(lhs), Expr::Sort(rhs)) => Ok(level_eq(lhs, rhs)),
            (Expr::BVar(lhs), Expr::BVar(rhs)) => Ok(lhs == rhs),
            (
                Expr::Const {
                    name: lhs_name,
                    levels: lhs_levels,
                },
                Expr::Const {
                    name: rhs_name,
                    levels: rhs_levels,
                },
            ) => Ok(lhs_name == rhs_name && levels_eq(lhs_levels, rhs_levels)),
            (Expr::App(lhs_f, lhs_a), Expr::App(rhs_f, rhs_a)) => Ok(self
                .is_defeq_with_remaining_fuel(ctx, delta, lhs_f, rhs_f, fuel, meter)?
                && self.is_defeq_with_remaining_fuel(ctx, delta, lhs_a, rhs_a, fuel, meter)?),
            (
                Expr::Pi {
                    binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Pi {
                    ty: rhs_ty,
                    body: rhs_body,
                    ..
                },
            ) => {
                if !self.is_defeq_with_remaining_fuel(ctx, delta, lhs_ty, rhs_ty, fuel, meter)? {
                    return Ok(false);
                }
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                self.is_defeq_with_remaining_fuel(&body_ctx, delta, lhs_body, rhs_body, fuel, meter)
            }
            (
                Expr::Lam {
                    binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Lam {
                    ty: rhs_ty,
                    body: rhs_body,
                    ..
                },
            ) => {
                if !self.is_defeq_with_remaining_fuel(ctx, delta, lhs_ty, rhs_ty, fuel, meter)? {
                    return Ok(false);
                }
                let mut body_ctx = ctx.clone();
                body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                self.is_defeq_with_remaining_fuel(&body_ctx, delta, lhs_body, rhs_body, fuel, meter)
            }
            _ => Ok(false),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn is_defeq_with_remaining_fuel_diagnosed(
        &self,
        ctx: &Ctx,
        delta: &[String],
        lhs: &Expr,
        rhs: &Expr,
        fuel: &mut usize,
        recorder: &mut KernelConversionRecorder,
        depth: u32,
    ) -> Result<bool> {
        if *fuel == 0 {
            recorder.record(KernelComparisonOutcome::FuelExhausted, lhs, rhs, depth);
            return Err(Error::ResourceLimit {
                kind: ResourceLimitKind::Conversion,
            });
        }
        *fuel -= 1;
        if quick_syntactic_eq(lhs, rhs) {
            return Ok(true);
        }

        let lhs = match self.whnf_with_remaining_fuel(
            ctx,
            delta,
            lhs,
            fuel,
            ResourceLimitKind::Conversion,
            &mut DisabledKernelWorkMeter,
        ) {
            Ok(lhs) => lhs,
            Err(error) => {
                if matches!(
                    error,
                    Error::ResourceLimit {
                        kind: ResourceLimitKind::Conversion
                    }
                ) {
                    recorder.record(KernelComparisonOutcome::FuelExhausted, lhs, rhs, depth);
                }
                return Err(error);
            }
        };
        let rhs = match self.whnf_with_remaining_fuel(
            ctx,
            delta,
            rhs,
            fuel,
            ResourceLimitKind::Conversion,
            &mut DisabledKernelWorkMeter,
        ) {
            Ok(rhs) => rhs,
            Err(error) => {
                if matches!(
                    error,
                    Error::ResourceLimit {
                        kind: ResourceLimitKind::Conversion
                    }
                ) {
                    recorder.record(KernelComparisonOutcome::FuelExhausted, &lhs, rhs, depth);
                }
                return Err(error);
            }
        };

        let next_depth = depth.saturating_add(1);
        let result = match (&lhs, &rhs) {
            (Expr::Sort(lhs), Expr::Sort(rhs)) => Ok(level_eq(lhs, rhs)),
            (Expr::BVar(lhs), Expr::BVar(rhs)) => Ok(lhs == rhs),
            (
                Expr::Const {
                    name: lhs_name,
                    levels: lhs_levels,
                },
                Expr::Const {
                    name: rhs_name,
                    levels: rhs_levels,
                },
            ) => Ok(lhs_name == rhs_name && levels_eq(lhs_levels, rhs_levels)),
            (Expr::App(lhs_f, lhs_a), Expr::App(rhs_f, rhs_a)) => {
                if !self.is_defeq_with_remaining_fuel_diagnosed(
                    ctx, delta, lhs_f, rhs_f, fuel, recorder, next_depth,
                )? {
                    Ok(false)
                } else {
                    self.is_defeq_with_remaining_fuel_diagnosed(
                        ctx, delta, lhs_a, rhs_a, fuel, recorder, next_depth,
                    )
                }
            }
            (
                Expr::Pi {
                    binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Pi {
                    ty: rhs_ty,
                    body: rhs_body,
                    ..
                },
            ) => {
                if !self.is_defeq_with_remaining_fuel_diagnosed(
                    ctx, delta, lhs_ty, rhs_ty, fuel, recorder, next_depth,
                )? {
                    Ok(false)
                } else {
                    let mut body_ctx = ctx.clone();
                    body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                    self.is_defeq_with_remaining_fuel_diagnosed(
                        &body_ctx, delta, lhs_body, rhs_body, fuel, recorder, next_depth,
                    )
                }
            }
            (
                Expr::Lam {
                    binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Lam {
                    ty: rhs_ty,
                    body: rhs_body,
                    ..
                },
            ) => {
                if !self.is_defeq_with_remaining_fuel_diagnosed(
                    ctx, delta, lhs_ty, rhs_ty, fuel, recorder, next_depth,
                )? {
                    Ok(false)
                } else {
                    let mut body_ctx = ctx.clone();
                    body_ctx.push_assumption(binder.clone(), (**lhs_ty).clone());
                    self.is_defeq_with_remaining_fuel_diagnosed(
                        &body_ctx, delta, lhs_body, rhs_body, fuel, recorder, next_depth,
                    )
                }
            }
            _ => Ok(false),
        };
        if matches!(result, Ok(false)) {
            recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, depth);
        }
        result
    }
}

fn record_reduction(meter: &mut impl KernelWorkMeter, counter: KernelWorkCounter) {
    meter.increment(counter);
    meter.increment(KernelWorkCounter::PhysicalReduction);
}

fn replay_memo_fuel(
    fuel: &mut usize,
    fuel_cost: usize,
    kind: ResourceLimitKind,
    counters: &mut KernelWorkCounters,
) -> Result<()> {
    let charged = (*fuel).min(fuel_cost);
    counters.add_memo_replayed_fuel(charged);
    if *fuel < fuel_cost {
        *fuel = 0;
        return Err(Error::ResourceLimit { kind });
    }
    *fuel -= fuel_cost;
    Ok(())
}

fn spend_fuel(fuel: &mut usize, kind: ResourceLimitKind) -> Result<()> {
    if *fuel == 0 {
        return Err(Error::ResourceLimit { kind });
    }
    *fuel -= 1;
    Ok(())
}

fn collect_apps_with_retained_args(term: &Expr) -> (Expr, Vec<Arc<Expr>>) {
    let mut head = term;
    let mut args = Vec::new();
    while let Expr::App(fun, arg) = head {
        args.push(Arc::clone(arg));
        head = fun;
    }
    args.reverse();
    (head.clone(), args)
}

fn generated_recursor_rules(data: &InductiveDecl) -> RecursorRules {
    let minor_start = data.params.len() + 1;
    RecursorRules::new(
        minor_start,
        minor_start + data.constructors.len() + data.indices.len(),
    )
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

fn mutual_constructor_offset(
    env: &Env,
    group: &MutualGroupInfo,
    target_inductive: &str,
) -> Result<usize> {
    let mut offset = 0usize;
    for inductive in &group.inductives {
        if inductive == target_inductive {
            return Ok(offset);
        }
        offset += env.inductive_data(inductive)?.constructors.len();
    }
    Err(Error::InvalidInductive(format!(
        "{target_inductive} is not in mutual group"
    )))
}

fn mutual_family_index(block: &MutualInductiveBlock, name: &str) -> Result<usize> {
    block
        .inductives
        .iter()
        .position(|data| data.name == name)
        .ok_or_else(|| Error::InvalidInductive(format!("{name} is not in mutual block")))
}

fn recursor_prefix_ctx(domains: &[Expr]) -> Ctx {
    let mut ctx = Ctx::new();
    for (index, domain) in domains.iter().enumerate() {
        ctx.push_assumption(format!("_rec_arg_{index}"), domain.clone());
    }
    ctx
}

fn expected_minor_type(
    data: &InductiveDecl,
    constructor: &ConstructorDecl,
    constructor_index: usize,
) -> Result<Expr> {
    let (domains, constructor_result) = peel_pi_domains(&constructor.ty);
    let param_count = data.params.len();
    if domains.len() < param_count {
        return Err(Error::InvalidInductive(format!(
            "{} constructor is missing parameter binders",
            constructor.name
        )));
    }
    let constructor_result_indices =
        constructor_result_index_args(data, constructor, &constructor_result)?;

    let prefix_len = param_count + 1 + constructor_index;
    let motive_abs = param_count;
    let mut source_to_target: Vec<usize> = (0..param_count).collect();
    let mut target_ctx_len = prefix_len;
    let mut expected_domains = Vec::new();
    let mut field_abs = Vec::new();

    for (field_index, field_domain) in domains[param_count..].iter().enumerate() {
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

        if is_direct_recursive_domain(data, field_domain, source_ctx_len) {
            let index_args = direct_recursive_index_args(data, field_domain, source_ctx_len)?
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

    let levels = data
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
        .map(|arg| remap_bvars(arg, domains.len(), target_ctx_len, &source_to_target))
        .collect::<Result<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs,
        result_index_args,
        constructor_value,
    )?;

    Ok(mk_pi_from_domains(expected_domains, result))
}

fn expected_mutual_minor_type(
    block: &MutualInductiveBlock,
    family_index: usize,
    constructor: &ConstructorDecl,
    constructor_index: usize,
) -> Result<Expr> {
    let owner = block.inductives.get(family_index).ok_or_else(|| {
        Error::InvalidInductive(format!(
            "{} constructor family index {family_index} is out of range",
            block.name
        ))
    })?;
    let (domains, constructor_result) = peel_pi_domains(&constructor.ty);
    let param_count = owner.params.len();
    if domains.len() < param_count {
        return Err(Error::InvalidInductive(format!(
            "{} constructor is missing parameter binders",
            constructor.name
        )));
    }
    let constructor_result_indices =
        constructor_result_index_args(owner, constructor, &constructor_result)?;

    let prefix_len = param_count + block.inductives.len() + constructor_index;
    let motive_abs_start = param_count;
    let mut source_to_target: Vec<usize> = (0..param_count).collect();
    let mut target_ctx_len = prefix_len;
    let mut expected_domains = Vec::new();
    let mut field_abs = Vec::new();

    for (field_index, field_domain) in domains[param_count..].iter().enumerate() {
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
            direct_mutual_recursive_index_args_in_block(block, field_domain, source_ctx_len)
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
        .map(|arg| remap_bvars(arg, domains.len(), target_ctx_len, &source_to_target))
        .collect::<Result<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs_start + family_index,
        result_index_args,
        constructor_value,
    )?;

    Ok(mk_pi_from_domains(expected_domains, result))
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
        return Err(Error::InvalidInductive(format!(
            "binder index {abs} escapes context of length {ctx_len}"
        )));
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
                return Err(Error::InvalidInductive(format!(
                    "binder index {index} escapes context of length {source_ctx_len}"
                )));
            }
            let source_abs = source_ctx_len - 1 - index;
            let Some(target_abs) = source_to_target.get(source_abs).copied() else {
                return Err(Error::InvalidInductive(format!(
                    "binder index {index} has no target in recursor minor"
                )));
            };
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

fn inductive_type(data: &InductiveDecl) -> Expr {
    let binders = data.params.iter().chain(&data.indices);
    mk_pi_telescope(binders, Expr::sort(data.sort.clone()))
}

fn mk_pi_telescope<'a>(
    binders: impl DoubleEndedIterator<Item = &'a crate::Binder>,
    body: Expr,
) -> Expr {
    binders.rev().fold(body, |body, binder| {
        Expr::pi(binder.name.clone(), binder.ty.clone(), body)
    })
}

fn declaration_constraint_levels(
    name: &str,
    params: &[String],
    levels: &[Level],
    constraint_params: &[String],
) -> Result<Vec<Level>> {
    constraint_params
        .iter()
        .map(|constraint_param| {
            let index = params
                .iter()
                .position(|param| param == constraint_param)
                .ok_or_else(|| Error::UnknownUniverseParam(constraint_param.clone()))?;
            levels
                .get(index)
                .cloned()
                .ok_or_else(|| Error::BadUniverseArity {
                    name: name.to_owned(),
                    expected: params.len(),
                    actual: levels.len(),
                })
        })
        .collect()
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

fn check_constructor_domain_positive(
    env: &Env,
    data: &InductiveDecl,
    constructor: &str,
    domain_index: usize,
    domain: &Expr,
) -> Result<()> {
    let allowed = domain_index >= data.params.len()
        && recursive_occurrences_strictly_positive(env, data, domain, domain_index);
    if !allowed && contains_const(domain, &data.name) {
        return Err(Error::NonPositiveOccurrence {
            inductive: data.name.clone(),
            constructor: constructor.to_owned(),
            ty: domain.clone(),
        });
    }
    Ok(())
}

fn check_mutual_constructor_domain_positive(
    env: &Env,
    block: &MutualInductiveBlock,
    data: &InductiveDecl,
    constructor: &str,
    domain_index: usize,
    domain: &Expr,
) -> Result<()> {
    let allowed = domain_index >= data.params.len()
        && mutual_recursive_occurrences_strictly_positive(env, block, domain, domain_index);
    if !allowed
        && contains_any_const(
            domain,
            block.inductives.iter().map(|data| data.name.as_str()),
        )
    {
        return Err(Error::NonPositiveOccurrence {
            inductive: data.name.clone(),
            constructor: constructor.to_owned(),
            ty: domain.clone(),
        });
    }
    Ok(())
}

fn is_direct_recursive_domain(data: &InductiveDecl, domain: &Expr, ctx_len: usize) -> bool {
    direct_recursive_index_args(data, domain, ctx_len).is_ok()
}

fn recursive_occurrences_strictly_positive(
    env: &Env,
    data: &InductiveDecl,
    domain: &Expr,
    ctx_len: usize,
) -> bool {
    if direct_recursive_index_args(data, domain, ctx_len).is_ok() {
        return true;
    }
    match domain {
        Expr::Sort(_) | Expr::BVar(_) => true,
        Expr::Const { name, .. } => name != &data.name,
        Expr::App(_, _) => {
            let (head, args) = collect_apps(domain);
            let Expr::Const { name, .. } = head else {
                return !contains_const(domain, &data.name);
            };
            let Some(functor) = approved_nested_functor(&name, args.len()) else {
                return !contains_const(domain, &data.name);
            };
            if !approved_nested_functor_decl_is_valid(env, functor.name, functor.arity) {
                return !contains_const(domain, &data.name);
            }
            args.iter().enumerate().all(|(index, arg)| {
                if functor.positive_args.contains(&index) {
                    recursive_occurrences_strictly_positive(env, data, arg, ctx_len)
                } else {
                    !contains_const(arg, &data.name)
                }
            })
        }
        Expr::Pi { ty, body, .. } => {
            !contains_const(ty, &data.name)
                && recursive_occurrences_strictly_positive(env, data, body, ctx_len + 1)
        }
        Expr::Lam { .. } | Expr::Let { .. } => !contains_const(domain, &data.name),
    }
}

fn mutual_recursive_occurrences_strictly_positive(
    env: &Env,
    block: &MutualInductiveBlock,
    domain: &Expr,
    ctx_len: usize,
) -> bool {
    if direct_mutual_recursive_index_args_in_block(block, domain, ctx_len).is_ok() {
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
            if !approved_nested_functor_decl_is_valid(env, functor.name, functor.arity) {
                return !contains_any_const(
                    domain,
                    block.inductives.iter().map(|data| data.name.as_str()),
                );
            }
            args.iter().enumerate().all(|(index, arg)| {
                if functor.positive_args.contains(&index) {
                    mutual_recursive_occurrences_strictly_positive(env, block, arg, ctx_len)
                } else {
                    !contains_any_const(arg, block.inductives.iter().map(|data| data.name.as_str()))
                }
            })
        }
        Expr::Pi { ty, body, .. } => {
            !contains_any_const(ty, block.inductives.iter().map(|data| data.name.as_str()))
                && mutual_recursive_occurrences_strictly_positive(env, block, body, ctx_len + 1)
        }
        Expr::Lam { .. } | Expr::Let { .. } => !contains_any_const(
            domain,
            block.inductives.iter().map(|data| data.name.as_str()),
        ),
    }
}

fn approved_nested_functor_decl_is_valid(env: &Env, name: &str, arity: usize) -> bool {
    let Some(Decl::Inductive { data, .. }) = env.decls.get(name) else {
        return false;
    };
    match (name, arity) {
        ("List", 1) => approved_list_decl(data),
        ("Option", 1) => approved_option_decl(data),
        ("Prod", 2) => approved_prod_decl(data),
        _ => false,
    }
}

fn approved_list_decl(data: &InductiveDecl) -> bool {
    if data.name != "List"
        || data.universe_params.len() != 1
        || !data.universe_constraints.is_empty()
        || data.params.len() != 1
        || !data.indices.is_empty()
        || data.constructors.len() != 2
    {
        return false;
    }
    let u = Level::param(data.universe_params[0].clone());
    let list_a = |a| Expr::app(Expr::konst("List", vec![u.clone()]), a);
    let nil_ty = Expr::pi("A", Expr::sort(u.clone()), list_a(Expr::bvar(0)));
    let cons_ty = Expr::pi(
        "A",
        Expr::sort(u.clone()),
        Expr::pi(
            "x",
            Expr::bvar(0),
            Expr::pi("xs", list_a(Expr::bvar(1)), list_a(Expr::bvar(2))),
        ),
    );
    data.params[0].ty == Expr::sort(u.clone())
        && level_eq(&data.sort, &u)
        && data.constructors[0].name == "List.nil"
        && expr_eq_ignoring_binder_names(&data.constructors[0].ty, &nil_ty)
        && data.constructors[1].name == "List.cons"
        && expr_eq_ignoring_binder_names(&data.constructors[1].ty, &cons_ty)
}

fn approved_option_decl(data: &InductiveDecl) -> bool {
    if data.name != "Option"
        || data.universe_params.len() != 1
        || !data.universe_constraints.is_empty()
        || data.params.len() != 1
        || !data.indices.is_empty()
        || data.constructors.len() != 2
    {
        return false;
    }
    let u = Level::param(data.universe_params[0].clone());
    let option_a = |a| Expr::app(Expr::konst("Option", vec![u.clone()]), a);
    let none_ty = Expr::pi("A", Expr::sort(u.clone()), option_a(Expr::bvar(0)));
    let some_ty = Expr::pi(
        "A",
        Expr::sort(u.clone()),
        Expr::pi("value", Expr::bvar(0), option_a(Expr::bvar(1))),
    );
    data.params[0].ty == Expr::sort(u.clone())
        && level_eq(&data.sort, &u)
        && data.constructors[0].name == "Option.none"
        && expr_eq_ignoring_binder_names(&data.constructors[0].ty, &none_ty)
        && data.constructors[1].name == "Option.some"
        && expr_eq_ignoring_binder_names(&data.constructors[1].ty, &some_ty)
}

fn approved_prod_decl(data: &InductiveDecl) -> bool {
    if data.name != "Prod"
        || data.universe_params.len() != 1
        || !data.universe_constraints.is_empty()
        || data.params.len() != 2
        || !data.indices.is_empty()
        || data.constructors.len() != 1
    {
        return false;
    }
    let u = Level::param(data.universe_params[0].clone());
    let prod_ab = |a, b| Expr::apps(Expr::konst("Prod", vec![u.clone()]), vec![a, b]);
    let mk_ty = Expr::pi(
        "A",
        Expr::sort(u.clone()),
        Expr::pi(
            "B",
            Expr::sort(u.clone()),
            Expr::pi(
                "fst",
                Expr::bvar(1),
                Expr::pi("snd", Expr::bvar(1), prod_ab(Expr::bvar(3), Expr::bvar(2))),
            ),
        ),
    );
    data.params[0].ty == Expr::sort(u.clone())
        && data.params[1].ty == Expr::sort(u.clone())
        && level_eq(&data.sort, &u)
        && data.constructors[0].name == "Prod.mk"
        && expr_eq_ignoring_binder_names(&data.constructors[0].ty, &mk_ty)
}

fn expr_eq_ignoring_binder_names(lhs: &Expr, rhs: &Expr) -> bool {
    match (lhs, rhs) {
        (Expr::Sort(lhs), Expr::Sort(rhs)) => level_eq(lhs, rhs),
        (Expr::BVar(lhs), Expr::BVar(rhs)) => lhs == rhs,
        (
            Expr::Const {
                name: lhs_name,
                levels: lhs_levels,
            },
            Expr::Const {
                name: rhs_name,
                levels: rhs_levels,
            },
        ) => lhs_name == rhs_name && levels_eq(lhs_levels, rhs_levels),
        (Expr::App(lhs_fun, lhs_arg), Expr::App(rhs_fun, rhs_arg)) => {
            expr_eq_ignoring_binder_names(lhs_fun, rhs_fun)
                && expr_eq_ignoring_binder_names(lhs_arg, rhs_arg)
        }
        (
            Expr::Lam {
                ty: lhs_ty,
                body: lhs_body,
                ..
            },
            Expr::Lam {
                ty: rhs_ty,
                body: rhs_body,
                ..
            },
        )
        | (
            Expr::Pi {
                ty: lhs_ty,
                body: lhs_body,
                ..
            },
            Expr::Pi {
                ty: rhs_ty,
                body: rhs_body,
                ..
            },
        ) => {
            expr_eq_ignoring_binder_names(lhs_ty, rhs_ty)
                && expr_eq_ignoring_binder_names(lhs_body, rhs_body)
        }
        (
            Expr::Let {
                ty: lhs_ty,
                value: lhs_value,
                body: lhs_body,
                ..
            },
            Expr::Let {
                ty: rhs_ty,
                value: rhs_value,
                body: rhs_body,
                ..
            },
        ) => {
            expr_eq_ignoring_binder_names(lhs_ty, rhs_ty)
                && expr_eq_ignoring_binder_names(lhs_value, rhs_value)
                && expr_eq_ignoring_binder_names(lhs_body, rhs_body)
        }
        _ => false,
    }
}

fn direct_recursive_index_args(
    data: &InductiveDecl,
    domain: &Expr,
    ctx_len: usize,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(domain);
    let levels = match head {
        Expr::Const { name, levels } if name == data.name => levels,
        _ => return Err(Error::InvalidInductive(data.name.clone())),
    };

    let expected_levels: Vec<_> = data
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != data.params.len() + data.indices.len()
    {
        return Err(Error::InvalidInductive(data.name.clone()));
    }

    for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
        if arg != &bvar_for_abs(ctx_len, param_index)? {
            return Err(Error::InvalidInductive(data.name.clone()));
        }
    }

    if args.iter().all(|arg| !contains_const(arg, &data.name)) {
        Ok(args[data.params.len()..].to_vec())
    } else {
        Err(Error::InvalidInductive(data.name.clone()))
    }
}

fn direct_mutual_recursive_index_args(
    env: &Env,
    group: &MutualGroupInfo,
    domain: &Expr,
    ctx_len: usize,
) -> Result<(String, Vec<Expr>)> {
    for name in &group.inductives {
        let data = env.inductive_data(name)?;
        if let Ok(indices) = direct_recursive_index_args(data, domain, ctx_len) {
            return Ok((name.clone(), indices));
        }
    }
    Err(Error::InvalidInductive(
        "not a direct mutual recursive domain".to_owned(),
    ))
}

fn direct_mutual_recursive_index_args_in_block(
    block: &MutualInductiveBlock,
    domain: &Expr,
    ctx_len: usize,
) -> Result<(usize, Vec<Expr>)> {
    for (index, data) in block.inductives.iter().enumerate() {
        if let Ok(indices) = direct_recursive_index_args(data, domain, ctx_len) {
            return Ok((index, indices));
        }
    }
    Err(Error::InvalidInductive(format!(
        "{} domain is not a direct mutual recursive occurrence",
        block.name
    )))
}

fn constructor_result_index_args(
    data: &InductiveDecl,
    constructor: &ConstructorDecl,
    result: &Expr,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(result);
    let levels = match head {
        Expr::Const { name, levels } if name == data.name => levels,
        _ => {
            return Err(Error::BadConstructorResult {
                inductive: data.name.clone(),
                constructor: constructor.name.clone(),
                result: result.clone(),
            });
        }
    };
    let expected_levels: Vec<_> = data
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != data.params.len() + data.indices.len()
    {
        return Err(Error::BadConstructorResult {
            inductive: data.name.clone(),
            constructor: constructor.name.clone(),
            result: result.clone(),
        });
    }
    Ok(args[data.params.len()..].to_vec())
}

fn instantiate_constructor_args(expr: &Expr, args_by_abs: &[Expr]) -> Result<Expr> {
    instantiate_constructor_args_at(expr, args_by_abs, 0)
}

fn instantiate_constructor_args_at(expr: &Expr, args_by_abs: &[Expr], depth: u32) -> Result<Expr> {
    match expr {
        Expr::Sort(level) => Ok(Expr::sort(level.clone())),
        Expr::BVar(index) => {
            if *index < depth {
                return Ok(Expr::bvar(*index));
            }
            let outer_index = (*index - depth) as usize;
            if outer_index >= args_by_abs.len() {
                return Err(Error::InvalidInductive(format!(
                    "binder index {index} escapes constructor argument context"
                )));
            }
            let source_abs = args_by_abs.len() - 1 - outer_index;
            crate::subst::shift(&args_by_abs[source_abs], depth as i32, 0)
        }
        Expr::Const { name, levels } => Ok(Expr::konst(name.clone(), levels.clone())),
        Expr::App(fun, arg) => Ok(Expr::app(
            instantiate_constructor_args_at(fun, args_by_abs, depth)?,
            instantiate_constructor_args_at(arg, args_by_abs, depth)?,
        )),
        Expr::Lam { binder, ty, body } => Ok(Expr::lam(
            binder.clone(),
            instantiate_constructor_args_at(ty, args_by_abs, depth)?,
            instantiate_constructor_args_at(body, args_by_abs, depth + 1)?,
        )),
        Expr::Pi { binder, ty, body } => Ok(Expr::pi(
            binder.clone(),
            instantiate_constructor_args_at(ty, args_by_abs, depth)?,
            instantiate_constructor_args_at(body, args_by_abs, depth + 1)?,
        )),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => Ok(Expr::let_in(
            binder.clone(),
            instantiate_constructor_args_at(ty, args_by_abs, depth)?,
            instantiate_constructor_args_at(value, args_by_abs, depth)?,
            instantiate_constructor_args_at(body, args_by_abs, depth + 1)?,
        )),
    }
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

#[cfg(test)]
mod memo_tests {
    use super::*;
    use crate::{nat, nat_zero};

    fn beta_owner() -> Arc<Expr> {
        Arc::new(Expr::app(
            Expr::lam("x", Expr::sort(Level::zero()), Expr::bvar(0)),
            Expr::konst("a", vec![]),
        ))
    }

    fn repeated_defeq_pair() -> (Expr, Expr) {
        let beta = beta_owner();
        let normal = Arc::new(Expr::konst("a", vec![]));
        let lhs_inner = Arc::new(Expr::App(
            Arc::new(Expr::konst("f", vec![])),
            Arc::clone(&beta),
        ));
        let rhs_inner = Arc::new(Expr::App(
            Arc::new(Expr::konst("f", vec![])),
            Arc::clone(&normal),
        ));
        (Expr::App(lhs_inner, beta), Expr::App(rhs_inner, normal))
    }

    #[test]
    fn ephemeral_defeq_preserves_logical_fuel_and_reduces_physical_calls() {
        let (lhs, rhs) = repeated_defeq_pair();
        let off = Env::new();
        let memo = Env::with_execution_options(KernelExecutionOptions::ephemeral_memo());
        let mut off_counters = KernelWorkCounters::default();
        let mut memo_counters = KernelWorkCounters::default();

        let off_result = off
            .is_defeq_with_work_counters(&Ctx::new(), &[], &lhs, &rhs, Some(&mut off_counters))
            .unwrap();
        let memo_result = memo
            .is_defeq_with_work_counters(&Ctx::new(), &[], &lhs, &rhs, Some(&mut memo_counters))
            .unwrap();

        assert!(off_result && memo_result);
        assert_eq!(memo_counters.logical_fuel, off_counters.logical_fuel);
        assert!(memo_counters.defeq_memo_hits > 0);
        assert!(memo_counters.memo_logical_fuel_replayed > 0);
        assert!(memo_counters.defeq_calls < off_counters.defeq_calls);
        assert_eq!(off_counters.memo_entry_capacity, 0);
        assert_eq!(memo_counters.memo_entry_capacity, 12_288);
    }

    #[test]
    fn memo_and_probe_preserve_explicit_conversion_fuel_and_errors() {
        let (lhs, rhs) = repeated_defeq_pair();
        let off = Env::new();
        let memo = Env::with_execution_options(KernelExecutionOptions::ephemeral_memo());
        for initial in 0..40 {
            let mut off_fuel = initial;
            let mut memo_fuel = initial;
            let off_result =
                off.is_defeq_with_fuel_metered(&Ctx::new(), &[], &lhs, &rhs, &mut off_fuel);
            let memo_result =
                memo.is_defeq_with_fuel_metered(&Ctx::new(), &[], &lhs, &rhs, &mut memo_fuel);
            assert_eq!(memo_result, off_result, "initial fuel {initial}");
            assert_eq!(memo_fuel, off_fuel, "initial fuel {initial}");
        }

        let probe = Env::with_execution_options(KernelExecutionOptions::repetition_probe());
        let mut off_counters = KernelWorkCounters::default();
        let mut probe_counters = KernelWorkCounters::default();
        let off_result =
            off.is_defeq_with_work_counters(&Ctx::new(), &[], &lhs, &rhs, Some(&mut off_counters));
        let probe_result = probe.is_defeq_with_work_counters(
            &Ctx::new(),
            &[],
            &lhs,
            &rhs,
            Some(&mut probe_counters),
        );
        assert_eq!(probe_result, off_result);
        assert_eq!(probe_counters.logical_fuel, off_counters.logical_fuel);
        assert_eq!(probe_counters.defeq_calls, off_counters.defeq_calls);
        assert_eq!(probe_counters.defeq_memo_hits, 0);
        assert!(probe_counters.memo_probe_repetitions > 0);
    }

    #[test]
    fn work_counter_sink_observes_off_memo_and_probe_operations() {
        let (lhs, rhs) = repeated_defeq_pair();

        let off_sink = KernelWorkCounterSink::default();
        let off = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::memo_off(),
            off_sink.clone(),
        );
        assert!(off.is_defeq(&Ctx::new(), &[], &lhs, &rhs).unwrap());
        let off_counters = off_sink.snapshot();
        assert!(off_counters.defeq_calls > 0);
        assert!(off_counters.logical_fuel > 0);
        assert_eq!(off_counters.memo_entry_capacity, 0);

        let memo_sink = KernelWorkCounterSink::default();
        let memo = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::ephemeral_memo(),
            memo_sink.clone(),
        );
        assert!(memo.is_defeq(&Ctx::new(), &[], &lhs, &rhs).unwrap());
        let memo_counters = memo_sink.snapshot();
        assert!(memo_counters.defeq_memo_hits > 0);
        assert_eq!(memo_counters.logical_fuel, off_counters.logical_fuel);

        let probe_sink = KernelWorkCounterSink::default();
        let probe = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::repetition_probe(),
            probe_sink.clone(),
        );
        assert!(probe.is_defeq(&Ctx::new(), &[], &lhs, &rhs).unwrap());
        let probe_counters = probe_sink.snapshot();
        assert_eq!(probe_counters.defeq_memo_hits, 0);
        assert!(probe_counters.memo_probe_repetitions > 0);
        assert_eq!(probe_counters.logical_fuel, off_counters.logical_fuel);
    }

    #[test]
    fn diagnosed_declaration_restores_options_without_environment_clone() {
        let sink = KernelWorkCounterSink::default();
        let mut env = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::ephemeral_memo(),
            sink.clone(),
        );
        let bad = Decl::Def {
            name: "Diagnosed.bad".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
            value: Expr::bvar(0),
            reducibility: Reducibility::Reducible,
        };
        assert!(env.add_decl_diagnosed(bad).is_err());
        assert_eq!(
            env.execution_options(),
            KernelExecutionOptions::ephemeral_memo()
        );
        assert!(env.decl("Diagnosed.bad").is_none());

        env.add_decl_diagnosed(Decl::Axiom {
            name: "Diagnosed.good".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
        })
        .unwrap();
        assert_eq!(
            env.execution_options(),
            KernelExecutionOptions::ephemeral_memo()
        );
        assert!(env.decl("Diagnosed.good").is_some());
        assert_eq!(sink.snapshot().memo_ineligible_diagnosed, 2);
    }

    #[test]
    fn ordinary_and_shared_pool_check_families_match_memo_off() {
        let term = Expr::lam("A", Expr::sort(Level::zero()), Expr::bvar(0));
        let expected = Expr::pi("A", Expr::sort(Level::zero()), Expr::sort(Level::zero()));
        let off = Env::new();
        let memo = Env::with_execution_options(KernelExecutionOptions::ephemeral_memo());
        assert_eq!(
            memo.check(&Ctx::new(), &[], &term, &expected),
            off.check(&Ctx::new(), &[], &term, &expected)
        );
        assert_eq!(
            memo.infer(&Ctx::new(), &[], &term),
            off.infer(&Ctx::new(), &[], &term)
        );

        let mut off_whnf = 1_000;
        let mut off_conversion = 1_000;
        let mut memo_whnf = 1_000;
        let mut memo_conversion = 1_000;
        let off_result = off.check_with_fuel_metered(
            &Ctx::new(),
            &[],
            &term,
            &expected,
            &mut off_whnf,
            &mut off_conversion,
        );
        let memo_result = memo.check_with_fuel_metered(
            &Ctx::new(),
            &[],
            &term,
            &expected,
            &mut memo_whnf,
            &mut memo_conversion,
        );
        assert_eq!(memo_result, off_result);
        assert_eq!(memo_whnf, off_whnf);
        assert_eq!(memo_conversion, off_conversion);
    }

    #[test]
    fn compact_beta_delta_iota_zeta_and_binder_matrix_is_differential() {
        let mut off = Env::with_builtins().unwrap();
        let mut memo =
            Env::with_builtins_and_execution_options(KernelExecutionOptions::ephemeral_memo())
                .unwrap();
        for env in [&mut off, &mut memo] {
            env.add_def(
                "Memo.zero",
                vec![],
                nat(),
                nat_zero(),
                Reducibility::Reducible,
            )
            .unwrap();
        }

        let beta = Expr::app(Expr::lam("x", nat(), Expr::bvar(0)), nat_zero());
        let delta = Expr::konst("Memo.zero", vec![]);
        let zeta = Expr::let_in("x", nat(), nat_zero(), Expr::bvar(0));
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), Expr::bvar(0)));
        let iota = Expr::apps(
            Expr::konst("Nat.rec", vec![Level::zero()]),
            vec![motive, nat_zero(), step, nat_zero()],
        );
        let binder = Expr::pi("x", nat(), Expr::bvar(0));
        let expressions = [beta, delta, zeta, iota, binder];
        for expression in &expressions {
            for initial in 0..16 {
                let mut off_fuel = initial;
                let mut memo_fuel = initial;
                let off_result =
                    off.whnf_with_fuel_metered(&Ctx::new(), &[], expression, &mut off_fuel);
                let memo_result =
                    memo.whnf_with_fuel_metered(&Ctx::new(), &[], expression, &mut memo_fuel);
                assert_eq!(memo_result, off_result, "fuel {initial}: {expression:?}");
                assert_eq!(memo_fuel, off_fuel, "fuel {initial}: {expression:?}");
            }
        }

        for expression in &expressions[..4] {
            for initial in 0..24 {
                let mut off_fuel = initial;
                let mut memo_fuel = initial;
                let off_result = off.is_defeq_with_fuel_metered(
                    &Ctx::new(),
                    &[],
                    expression,
                    &nat_zero(),
                    &mut off_fuel,
                );
                let memo_result = memo.is_defeq_with_fuel_metered(
                    &Ctx::new(),
                    &[],
                    expression,
                    &nat_zero(),
                    &mut memo_fuel,
                );
                assert_eq!(memo_result, off_result, "fuel {initial}: {expression:?}");
                assert_eq!(memo_fuel, off_fuel, "fuel {initial}: {expression:?}");
            }
        }
    }

    #[test]
    fn recursor_major_whnf_uses_memo_and_repetition_probe() {
        let major = Arc::new(Expr::app(Expr::lam("x", nat(), Expr::bvar(0)), nat_zero()));
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), Expr::bvar(0)));
        let recursor_prefix = Expr::apps(
            Expr::konst("Nat.rec", vec![Level::zero()]),
            vec![motive, nat_zero(), step],
        );
        let recursor = Expr::App(Arc::new(recursor_prefix), Arc::clone(&major));

        let memo_env =
            Env::with_builtins_and_execution_options(KernelExecutionOptions::ephemeral_memo())
                .unwrap();
        let mut memo_state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        for _ in 0..2 {
            let mut fuel = 100;
            let reduced = memo_env
                .reduce_recursor_memo(
                    &Ctx::new(),
                    &[],
                    &recursor,
                    &mut fuel,
                    ResourceLimitKind::Whnf,
                    &mut memo_state,
                )
                .unwrap();
            assert_eq!(reduced, Some(nat_zero()));
        }
        assert_eq!(memo_state.counters.whnf_memo_hits, 1);
        assert!(memo_state.counters.memo_logical_fuel_replayed > 0);

        let probe_env =
            Env::with_builtins_and_execution_options(KernelExecutionOptions::repetition_probe())
                .unwrap();
        let mut probe_state = KernelOperationState::new(KernelExecutionOptions::repetition_probe());
        for _ in 0..2 {
            let mut fuel = 100;
            probe_env
                .reduce_recursor_memo(
                    &Ctx::new(),
                    &[],
                    &recursor,
                    &mut fuel,
                    ResourceLimitKind::Whnf,
                    &mut probe_state,
                )
                .unwrap();
        }
        assert_eq!(probe_state.counters.whnf_memo_hits, 0);
        assert!(probe_state.counters.memo_probe_repetitions >= 1);

        let left = Expr::App(
            Arc::new(Expr::apps(
                Expr::konst("Nat.rec", vec![Level::zero()]),
                vec![
                    Expr::lam("_", nat(), nat()),
                    nat_zero(),
                    Expr::lam("_", nat(), Expr::lam("ih", nat(), Expr::bvar(0))),
                ],
            )),
            Arc::clone(&major),
        );
        let right = Expr::App(
            Arc::new(Expr::apps(
                Expr::konst("Nat.rec", vec![Level::zero()]),
                vec![
                    Expr::lam("_", nat(), nat()),
                    nat_zero(),
                    Expr::lam("_", nat(), Expr::lam("_", nat(), nat_zero())),
                ],
            )),
            Arc::clone(&major),
        );

        let memo_sink = KernelWorkCounterSink::default();
        let memo_env = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::ephemeral_memo(),
            memo_sink.clone(),
        );
        let mut memo_env = memo_env;
        memo_env.add_inductive(nat_inductive()).unwrap();
        let memo_hits_before = memo_sink.snapshot().whnf_memo_hits;
        assert!(memo_env.is_defeq(&Ctx::new(), &[], &left, &right).unwrap());
        assert!(memo_sink.snapshot().whnf_memo_hits > memo_hits_before);

        let probe_sink = KernelWorkCounterSink::default();
        let probe_env = Env::with_execution_options_and_work_counter_sink(
            KernelExecutionOptions::repetition_probe(),
            probe_sink.clone(),
        );
        let mut probe_env = probe_env;
        probe_env.add_inductive(nat_inductive()).unwrap();
        let probe_repetitions_before = probe_sink.snapshot().memo_probe_repetitions;
        assert!(probe_env.is_defeq(&Ctx::new(), &[], &left, &right).unwrap());
        assert!(probe_sink.snapshot().memo_probe_repetitions > probe_repetitions_before);
    }

    #[test]
    fn retained_identity_context_parameters_and_fuel_domain_are_exact() {
        let env = Env::new();
        let owner = beta_owner();
        let mut state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        let mut context = Ctx::new();
        context.push_assumption("shared", Expr::sort(Level::zero()));
        let mut fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &context,
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();

        let mut same_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &context.clone(),
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut same_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        assert_eq!(state.counters.whnf_memo_hits, 1);

        let mut extended = context.clone();
        extended.push_assumption("x", Expr::sort(Level::zero()));
        let mut context_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &extended,
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut context_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        let mut independently_allocated = Ctx::new();
        independently_allocated.push_assumption("shared", Expr::sort(Level::zero()));
        let mut independent_context_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &independently_allocated,
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut independent_context_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        let mut parameter_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &context,
            &["u".to_owned()],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut parameter_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        for parameters in [
            vec!["u".to_owned(), "v".to_owned()],
            vec!["v".to_owned(), "u".to_owned()],
        ] {
            let mut ordered_profile_fuel = 100;
            env.whnf_with_remaining_fuel_memo(
                &context,
                &parameters,
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut ordered_profile_fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap();
        }
        let mut conversion_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &context,
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut conversion_fuel,
            ResourceLimitKind::Conversion,
            &mut state,
        )
        .unwrap();
        assert_eq!(state.counters.whnf_memo_hits, 1);
        assert!(state.counters.whnf_memo_misses >= 4);
    }

    #[test]
    fn definition_values_shadowing_and_shifted_locals_do_not_cross_reuse() {
        let env = Env::new();
        let owner = Arc::new(Expr::bvar(0));
        let mut state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());

        let mut first = Ctx::new();
        first.push_definition("x", Expr::sort(Level::zero()), Expr::konst("a", vec![]));
        let mut fuel = 100;
        assert_eq!(
            env.whnf_with_remaining_fuel_memo(
                &first,
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap(),
            Expr::konst("a", vec![]),
        );

        let mut cloned_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &first.clone(),
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut cloned_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        assert_eq!(state.counters.whnf_memo_hits, 1);

        let mut distinct_value = Ctx::new();
        distinct_value.push_definition("x", Expr::sort(Level::zero()), Expr::konst("b", vec![]));
        let mut distinct_fuel = 100;
        assert_eq!(
            env.whnf_with_remaining_fuel_memo(
                &distinct_value,
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut distinct_fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap(),
            Expr::konst("b", vec![]),
        );

        let mut shadowed = first.clone();
        shadowed.push_definition("x", Expr::sort(Level::zero()), Expr::konst("c", vec![]));
        let mut shadowed_fuel = 100;
        assert_eq!(
            env.whnf_with_remaining_fuel_memo(
                &shadowed,
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut shadowed_fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap(),
            Expr::konst("c", vec![]),
        );

        let shifted_owner = Arc::new(Expr::bvar(1));
        let mut shifted_fuel = 100;
        let memo_result = env.whnf_with_remaining_fuel_memo(
            &shadowed,
            &[],
            &shifted_owner,
            MemoExprOrigin::Retained(&shifted_owner),
            &mut shifted_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        );
        let mut oracle_fuel = 100;
        let oracle_result = env.whnf_with_remaining_fuel(
            &shadowed,
            &[],
            &shifted_owner,
            &mut oracle_fuel,
            ResourceLimitKind::Whnf,
            &mut DisabledKernelWorkMeter,
        );
        assert_eq!(memo_result, oracle_result);
        assert_eq!(shifted_fuel, oracle_fuel);
        assert_eq!(state.counters.whnf_memo_hits, 1);
    }

    #[test]
    fn whnf_hit_charges_less_equal_and_greater_fuel_exactly() {
        let env = Env::new();
        let owner = beta_owner();
        let mut state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        let mut first_fuel = 100;
        let expected = env
            .whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut first_fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap();
        let cost = 100 - first_fuel;
        assert!(cost > 0);

        let mut less = cost - 1;
        assert_eq!(
            env.whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut less,
                ResourceLimitKind::Whnf,
                &mut state,
            ),
            Err(Error::ResourceLimit {
                kind: ResourceLimitKind::Whnf
            })
        );
        assert_eq!(less, 0);

        let mut equal = cost;
        assert_eq!(
            env.whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut equal,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap(),
            expected
        );
        assert_eq!(equal, 0);

        let mut greater = cost + 7;
        env.whnf_with_remaining_fuel_memo(
            &Ctx::new(),
            &[],
            &owner,
            MemoExprOrigin::Retained(&owner),
            &mut greater,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        assert_eq!(greater, 7);
    }

    #[test]
    fn defeq_hit_charges_less_equal_and_greater_fuel_exactly() {
        let env = Env::new();
        let owner = Arc::new(Expr::konst("a", vec![]));
        let mut state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        let mut first_fuel = 100;
        assert!(env
            .is_defeq_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut first_fuel,
                &mut state,
            )
            .unwrap());
        let cost = 100 - first_fuel;
        assert_eq!(cost, 1);

        let mut less = cost - 1;
        assert_eq!(
            env.is_defeq_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut less,
                &mut state,
            ),
            Err(Error::ResourceLimit {
                kind: ResourceLimitKind::Conversion
            })
        );
        assert_eq!(less, 0);

        let mut equal = cost;
        assert!(env
            .is_defeq_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut equal,
                &mut state,
            )
            .unwrap());
        assert_eq!(equal, 0);

        let mut greater = cost + 7;
        assert!(env
            .is_defeq_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut greater,
                &mut state,
            )
            .unwrap());
        assert_eq!(greater, 7);
    }

    #[test]
    fn borrowed_and_independently_allocated_roots_do_not_alias() {
        let env = Env::with_execution_options(KernelExecutionOptions::ephemeral_memo());
        let mut borrowed_counters = KernelWorkCounters::default();
        env.whnf_with_work_counters(
            &Ctx::new(),
            &[],
            &Expr::konst("a", vec![]),
            Some(&mut borrowed_counters),
        )
        .unwrap();
        assert_eq!(borrowed_counters.whnf_memo_lookups, 0);
        assert_eq!(borrowed_counters.memo_ineligible_borrowed, 1);

        let mut fresh_state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        let fresh = Expr::konst("fresh", vec![]);
        let mut fresh_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &Ctx::new(),
            &[],
            &fresh,
            MemoExprOrigin::Fresh,
            &mut fresh_fuel,
            ResourceLimitKind::Whnf,
            &mut fresh_state,
        )
        .unwrap();
        assert_eq!(fresh_state.counters.whnf_memo_lookups, 0);
        assert_eq!(fresh_state.counters.memo_ineligible_fresh, 1);

        let mut state = KernelOperationState::new(KernelExecutionOptions::ephemeral_memo());
        let retained = beta_owner();
        let retained_weak = Arc::downgrade(&retained);
        let mut retained_fuel = 100;
        env.whnf_with_remaining_fuel_memo(
            &Ctx::new(),
            &[],
            &retained,
            MemoExprOrigin::Retained(&retained),
            &mut retained_fuel,
            ResourceLimitKind::Whnf,
            &mut state,
        )
        .unwrap();
        drop(retained);
        assert!(retained_weak.upgrade().is_some());

        let misses_before_independent = state.counters.whnf_memo_misses;
        for owner in [beta_owner(), beta_owner()] {
            let mut fuel = 100;
            env.whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            )
            .unwrap();
        }
        assert_eq!(state.counters.whnf_memo_hits, 0);
        assert!(state.counters.whnf_memo_misses >= misses_before_independent.saturating_add(2));
        assert!(state.counters.memo_expr_identities >= 2);
    }

    #[test]
    fn capacity_stop_and_diagnosed_isolation_are_observational() {
        let env = Env::new();
        let mut state = KernelOperationState::with_limits(
            KernelExecutionOptions::ephemeral_memo(),
            KernelMemoLimits::tiny(),
        );
        for owner in [beta_owner(), Arc::new(Expr::konst("b", vec![]))] {
            let mut memo_fuel = 100;
            let memo_result = env.whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut memo_fuel,
                ResourceLimitKind::Whnf,
                &mut state,
            );
            let mut oracle_fuel = 100;
            let oracle_result = env.whnf_with_remaining_fuel(
                &Ctx::new(),
                &[],
                &owner,
                &mut oracle_fuel,
                ResourceLimitKind::Whnf,
                &mut DisabledKernelWorkMeter,
            );
            assert_eq!(memo_result, oracle_result);
            assert_eq!(memo_fuel, oracle_fuel);
        }
        assert!(state.counters.whnf_memo_capacity_stops > 0);

        let mut probe_state = KernelOperationState::with_limits(
            KernelExecutionOptions::repetition_probe(),
            KernelMemoLimits::tiny(),
        );
        for owner in [beta_owner(), beta_owner(), beta_owner()] {
            let mut probe_fuel = 100;
            let probe_result = env.whnf_with_remaining_fuel_memo(
                &Ctx::new(),
                &[],
                &owner,
                MemoExprOrigin::Retained(&owner),
                &mut probe_fuel,
                ResourceLimitKind::Whnf,
                &mut probe_state,
            );
            let mut oracle_fuel = 100;
            let oracle_result = env.whnf_with_remaining_fuel(
                &Ctx::new(),
                &[],
                &owner,
                &mut oracle_fuel,
                ResourceLimitKind::Whnf,
                &mut DisabledKernelWorkMeter,
            );
            assert_eq!(probe_result, oracle_result);
            assert_eq!(probe_fuel, oracle_fuel);
        }
        assert!(probe_state.counters.memo_probe_truncated);
        assert!(probe_state.counters.memo_probe_capacity_stops > 0);
        assert_eq!(probe_state.counters.whnf_memo_hits, 0);

        let diagnosed = Env::with_execution_options(KernelExecutionOptions::ephemeral_memo());
        let (lhs, rhs) = repeated_defeq_pair();
        let mut counters = KernelWorkCounters::default();
        let memo_error = diagnosed
            .is_defeq_diagnosed_with_fuel_and_work_counters(
                &Ctx::new(),
                &[],
                &lhs,
                &rhs,
                0,
                Some(&mut counters),
            )
            .unwrap_err();
        let off_error = env
            .is_defeq_diagnosed_with_fuel(&Ctx::new(), &[], &lhs, &rhs, 0)
            .unwrap_err();
        assert_eq!(memo_error, off_error);
        assert_eq!(counters.memo_ineligible_diagnosed, 1);
        assert_eq!(counters.whnf_memo_lookups, 0);
        assert_eq!(counters.defeq_memo_lookups, 0);

        let term = Expr::lam("A", Expr::sort(Level::zero()), Expr::bvar(0));
        let expected = Expr::sort(Level::zero());
        assert_eq!(
            diagnosed.check_diagnosed(&Ctx::new(), &[], &term, &expected),
            env.check_diagnosed(&Ctx::new(), &[], &term, &expected),
        );
    }
}

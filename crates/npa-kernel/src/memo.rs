//! Operation-local, bounded kernel memoization support.
//!
//! All identities in this module retain the `Arc` owner whose pointer is used
//! for lookup. Nothing in this module is serialized or shared between public
//! kernel operations.

use std::collections::{BTreeMap, BTreeSet};
use std::mem::size_of;
use std::sync::Arc;

use crate::{
    context::{Ctx, LocalDecl},
    error::ResourceLimitKind,
    expr::Expr,
    level::Level,
    work::KernelWorkCounters,
};

const ARC_ALLOCATION_HEADER_BYTES: usize = 2 * size_of::<usize>();
// `BTreeMap`/`BTreeSet` allocate multi-entry nodes. Charge an empty-root
// allowance for each of the six bounded collections, then three times each
// stored key/value footprint. This deliberately exceeds the partially filled
// node and edge storage used by the standard library implementation.
const BTREE_COLLECTION_COUNT: usize = 6;
const BTREE_COLLECTION_BASE_BYTES: usize = 4 * 1024;
const MAP_ENTRY_OVERHEAD_MULTIPLIER: usize = 3;

const fn bounded_vec_capacity(entry_limit: usize) -> usize {
    if entry_limit == 0 {
        return 0;
    }
    let minimum_capacity = if entry_limit < 4 { 4 } else { entry_limit };
    match minimum_capacity.checked_next_power_of_two() {
        Some(capacity) => capacity,
        None => usize::MAX,
    }
}

macro_rules! increment_counter {
    ($counters:ident, $field:ident) => {
        KernelWorkCounters::add(&mut $counters.$field, 1, &mut $counters.overflowed)
    };
}

/// Stable identifier for the production memo capacity contract.
pub const KERNEL_MEMO_LIMITS_V1: &str = "npa.kernel-memo-limits.v1";

/// Kernel memo selection for one public operation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum KernelMemoMode {
    /// Use the uncached implementation.
    #[default]
    Off,
    /// Use one bounded memo that is dropped at the operation boundary.
    Ephemeral,
}

/// Out-of-band kernel execution options. These values never enter proof or
/// certificate identities.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelExecutionOptions {
    memo_mode: KernelMemoMode,
    repetition_probe: bool,
}

impl KernelExecutionOptions {
    /// Existing behavior: no memo and no repetition bookkeeping.
    pub const fn memo_off() -> Self {
        Self {
            memo_mode: KernelMemoMode::Off,
            repetition_probe: false,
        }
    }

    /// Enable the bounded operation-local WHNF and successful-defeq memo.
    pub const fn ephemeral_memo() -> Self {
        Self {
            memo_mode: KernelMemoMode::Ephemeral,
            repetition_probe: false,
        }
    }

    /// Keep memoization off and attach the bounded observational repetition
    /// probe.
    pub const fn repetition_probe() -> Self {
        Self {
            memo_mode: KernelMemoMode::Off,
            repetition_probe: true,
        }
    }

    /// Selected memo mode.
    pub const fn memo_mode(self) -> KernelMemoMode {
        self.memo_mode
    }

    /// Whether the observational memo-off repetition probe is enabled.
    pub const fn probes_repetition(self) -> bool {
        self.repetition_probe
    }

    pub(crate) const fn needs_reuse_state(self) -> bool {
        matches!(self.memo_mode, KernelMemoMode::Ephemeral) || self.repetition_probe
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct KernelMemoLimits {
    whnf_entries: usize,
    defeq_entries: usize,
    expr_identities: usize,
    local_identities: usize,
    context_identities: usize,
    parameter_profiles: usize,
    node_occurrences: usize,
    context_occurrences: usize,
    parameter_occurrences: usize,
    retained_bytes: usize,
}

impl KernelMemoLimits {
    pub(crate) const V1: Self = Self {
        whnf_entries: 4_096,
        defeq_entries: 8_192,
        expr_identities: 16_384,
        local_identities: 8_192,
        context_identities: 4_096,
        parameter_profiles: 64,
        node_occurrences: 262_144,
        context_occurrences: 262_144,
        parameter_occurrences: 4_096,
        retained_bytes: 16 * 1024 * 1024,
    };

    pub(crate) const fn entry_capacity(self) -> usize {
        self.whnf_entries + self.defeq_entries
    }

    const fn retained_sequence_capacity_charge(self) -> usize {
        BTREE_COLLECTION_COUNT
            .saturating_mul(BTREE_COLLECTION_BASE_BYTES)
            .saturating_add(
                bounded_vec_capacity(self.expr_identities).saturating_mul(size_of::<Arc<Expr>>()),
            )
            .saturating_add(
                bounded_vec_capacity(self.local_identities)
                    .saturating_mul(size_of::<Arc<LocalDecl>>()),
            )
            .saturating_add(
                bounded_vec_capacity(self.context_identities)
                    .saturating_mul(size_of::<Box<[MemoLocalId]>>()),
            )
            .saturating_add(
                bounded_vec_capacity(self.parameter_profiles)
                    .saturating_mul(size_of::<Box<[String]>>()),
            )
    }

    #[cfg(test)]
    pub(crate) const fn tiny() -> Self {
        Self {
            whnf_entries: 1,
            defeq_entries: 1,
            expr_identities: 4,
            local_identities: 2,
            context_identities: 2,
            parameter_profiles: 2,
            node_occurrences: 64,
            context_occurrences: 4,
            parameter_occurrences: 4,
            retained_bytes: 64 * 1024,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum MemoExprOrigin<'a> {
    Borrowed,
    Fresh,
    Retained(&'a Arc<Expr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MemoExprId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MemoLocalId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MemoContextId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MemoParameterProfileId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum MemoFuelDomain {
    Whnf,
    Conversion,
}

impl MemoFuelDomain {
    fn from_resource_kind(kind: ResourceLimitKind) -> Option<Self> {
        match kind {
            ResourceLimitKind::Whnf => Some(Self::Whnf),
            ResourceLimitKind::Conversion => Some(Self::Conversion),
            ResourceLimitKind::UniverseConstraints => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct WhnfMemoKey {
    expr: MemoExprId,
    context: MemoContextId,
    parameters: MemoParameterProfileId,
    fuel_domain: MemoFuelDomain,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DefeqMemoKey {
    lhs: MemoExprId,
    rhs: MemoExprId,
    context: MemoContextId,
    parameters: MemoParameterProfileId,
}

#[derive(Clone, Debug)]
struct WhnfMemoValue {
    result: Expr,
    fuel_cost: usize,
}

#[derive(Clone, Copy, Debug)]
struct DefeqMemoValue {
    fuel_cost: usize,
}

#[derive(Default)]
struct RetainedBudget {
    node_occurrences: usize,
    context_occurrences: usize,
    parameter_occurrences: usize,
    retained_bytes: usize,
}

#[derive(Clone, Copy, Default)]
struct RetainedCharge {
    node_occurrences: usize,
    context_occurrences: usize,
    parameter_occurrences: usize,
    retained_bytes: usize,
}

impl RetainedBudget {
    fn try_reserve(
        &mut self,
        charge: RetainedCharge,
        limits: KernelMemoLimits,
        counters: &mut KernelWorkCounters,
    ) -> bool {
        let Some(node_occurrences) = self.node_occurrences.checked_add(charge.node_occurrences)
        else {
            increment_counter!(counters, memo_accounting_overflows);
            counters.overflowed = true;
            return false;
        };
        let Some(context_occurrences) = self
            .context_occurrences
            .checked_add(charge.context_occurrences)
        else {
            increment_counter!(counters, memo_accounting_overflows);
            counters.overflowed = true;
            return false;
        };
        let Some(parameter_occurrences) = self
            .parameter_occurrences
            .checked_add(charge.parameter_occurrences)
        else {
            increment_counter!(counters, memo_accounting_overflows);
            counters.overflowed = true;
            return false;
        };
        let Some(retained_bytes) = self.retained_bytes.checked_add(charge.retained_bytes) else {
            increment_counter!(counters, memo_accounting_overflows);
            counters.overflowed = true;
            return false;
        };
        if node_occurrences > limits.node_occurrences
            || context_occurrences > limits.context_occurrences
            || parameter_occurrences > limits.parameter_occurrences
            || retained_bytes > limits.retained_bytes
        {
            return false;
        }
        self.node_occurrences = node_occurrences;
        self.context_occurrences = context_occurrences;
        self.parameter_occurrences = parameter_occurrences;
        self.retained_bytes = retained_bytes;
        counters.memo_retained_node_occurrences = node_occurrences as u64;
        counters.memo_retained_context_occurrences = context_occurrences as u64;
        counters.memo_retained_parameter_occurrences = parameter_occurrences as u64;
        counters.memo_retained_bytes = retained_bytes as u64;
        true
    }
}

#[derive(Default)]
struct ExprInterner {
    by_pointer: BTreeMap<usize, MemoExprId>,
    retained: Vec<Arc<Expr>>,
}

#[derive(Default)]
struct LocalInterner {
    by_pointer: BTreeMap<usize, MemoLocalId>,
    retained: Vec<Arc<LocalDecl>>,
}

#[derive(Default)]
struct ContextInterner {
    retained: Vec<Box<[MemoLocalId]>>,
}

#[derive(Default)]
struct ParameterProfileInterner {
    retained: Vec<Box<[String]>>,
}

pub(crate) enum WhnfMemoLookup {
    Ineligible,
    Miss(WhnfMemoToken),
    Hit { result: Expr, fuel_cost: usize },
}

pub(crate) enum DefeqMemoLookup {
    Ineligible,
    Miss(DefeqMemoToken),
    Hit { fuel_cost: usize },
}

#[derive(Clone, Copy)]
pub(crate) struct WhnfMemoToken(WhnfMemoKey);

#[derive(Clone, Copy)]
pub(crate) struct DefeqMemoToken(DefeqMemoKey);

pub(crate) struct KernelOperationMemo {
    mode: KernelMemoMode,
    probe: bool,
    limits: KernelMemoLimits,
    budget: RetainedBudget,
    exprs: ExprInterner,
    locals: LocalInterner,
    contexts: ContextInterner,
    parameter_profiles: ParameterProfileInterner,
    whnf: BTreeMap<WhnfMemoKey, WhnfMemoValue>,
    defeq: BTreeMap<DefeqMemoKey, DefeqMemoValue>,
    seen_whnf: BTreeSet<WhnfMemoKey>,
    seen_defeq: BTreeSet<DefeqMemoKey>,
}

impl KernelOperationMemo {
    pub(crate) fn new(options: KernelExecutionOptions) -> Option<Self> {
        options
            .needs_reuse_state()
            .then(|| Self::with_limits(options, KernelMemoLimits::V1))
    }

    pub(crate) fn with_limits(options: KernelExecutionOptions, limits: KernelMemoLimits) -> Self {
        Self {
            mode: options.memo_mode(),
            probe: options.probes_repetition(),
            limits,
            // These four vectors grow only to their fixed identity limits.
            // Charge their complete possible backing capacity up front so a
            // growth step can never retain unaccounted spare capacity.
            budget: RetainedBudget {
                retained_bytes: limits
                    .retained_sequence_capacity_charge()
                    .min(limits.retained_bytes),
                ..RetainedBudget::default()
            },
            exprs: ExprInterner::default(),
            locals: LocalInterner::default(),
            contexts: ContextInterner::default(),
            parameter_profiles: ParameterProfileInterner::default(),
            whnf: BTreeMap::new(),
            defeq: BTreeMap::new(),
            seen_whnf: BTreeSet::new(),
            seen_defeq: BTreeSet::new(),
        }
    }

    pub(crate) const fn entry_capacity(&self) -> usize {
        self.limits.entry_capacity()
    }

    pub(crate) const fn retained_bytes(&self) -> usize {
        self.budget.retained_bytes
    }

    pub(crate) fn whnf_lookup(
        &mut self,
        origin: MemoExprOrigin<'_>,
        ctx: &Ctx,
        parameters: &[String],
        kind: ResourceLimitKind,
        counters: &mut KernelWorkCounters,
    ) -> WhnfMemoLookup {
        let Some(expr) = self.intern_expr_origin(origin, counters) else {
            if matches!(origin, MemoExprOrigin::Retained(_)) {
                self.mark_probe_identity_truncated(counters);
            }
            return WhnfMemoLookup::Ineligible;
        };
        let Some(context) = self.intern_context(ctx, counters) else {
            self.mark_probe_identity_truncated(counters);
            return WhnfMemoLookup::Ineligible;
        };
        let Some(parameters) = self.intern_parameter_profile(parameters, counters) else {
            self.mark_probe_identity_truncated(counters);
            return WhnfMemoLookup::Ineligible;
        };
        let Some(fuel_domain) = MemoFuelDomain::from_resource_kind(kind) else {
            return WhnfMemoLookup::Ineligible;
        };
        let key = WhnfMemoKey {
            expr,
            context,
            parameters,
            fuel_domain,
        };
        increment_counter!(counters, memo_eligible_calls);
        self.observe_whnf_probe(key, counters);
        if self.mode != KernelMemoMode::Ephemeral {
            return WhnfMemoLookup::Ineligible;
        }
        increment_counter!(counters, whnf_memo_lookups);
        if let Some(value) = self.whnf.get(&key) {
            increment_counter!(counters, whnf_memo_hits);
            WhnfMemoLookup::Hit {
                result: value.result.clone(),
                fuel_cost: value.fuel_cost,
            }
        } else {
            increment_counter!(counters, whnf_memo_misses);
            WhnfMemoLookup::Miss(WhnfMemoToken(key))
        }
    }

    pub(crate) fn insert_whnf(
        &mut self,
        token: WhnfMemoToken,
        result: &Expr,
        fuel_cost: usize,
        counters: &mut KernelWorkCounters,
    ) {
        if fuel_cost == 0
            || self.mode != KernelMemoMode::Ephemeral
            || self.whnf.contains_key(&token.0)
        {
            return;
        }
        if self.whnf.len() >= self.limits.whnf_entries {
            increment_counter!(counters, whnf_memo_capacity_stops);
            return;
        }
        let entry_charge =
            MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<(WhnfMemoKey, WhnfMemoValue)>());
        let Some(remaining_bytes) = self.remaining_byte_budget().checked_sub(entry_charge) else {
            increment_counter!(counters, whnf_memo_capacity_stops);
            return;
        };
        let Some(_) = expression_charge(result, self.remaining_node_budget(), remaining_bytes)
        else {
            increment_counter!(counters, whnf_memo_capacity_stops);
            return;
        };
        let retained_result = result.clone();
        let Some(mut charge) = expression_charge(
            &retained_result,
            self.remaining_node_budget(),
            remaining_bytes,
        ) else {
            increment_counter!(counters, whnf_memo_capacity_stops);
            return;
        };
        charge.retained_bytes = charge.retained_bytes.saturating_add(entry_charge);
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, whnf_memo_capacity_stops);
            return;
        }
        self.whnf.insert(
            token.0,
            WhnfMemoValue {
                result: retained_result,
                fuel_cost,
            },
        );
        increment_counter!(counters, whnf_memo_inserts);
        counters.whnf_memo_entries = self.whnf.len() as u64;
    }

    pub(crate) fn defeq_lookup(
        &mut self,
        lhs: MemoExprOrigin<'_>,
        rhs: MemoExprOrigin<'_>,
        ctx: &Ctx,
        parameters: &[String],
        counters: &mut KernelWorkCounters,
    ) -> DefeqMemoLookup {
        let Some(lhs) = self.intern_expr_origin(lhs, counters) else {
            if matches!(lhs, MemoExprOrigin::Retained(_)) {
                self.mark_probe_identity_truncated(counters);
            }
            return DefeqMemoLookup::Ineligible;
        };
        let Some(rhs) = self.intern_expr_origin(rhs, counters) else {
            if matches!(rhs, MemoExprOrigin::Retained(_)) {
                self.mark_probe_identity_truncated(counters);
            }
            return DefeqMemoLookup::Ineligible;
        };
        let Some(context) = self.intern_context(ctx, counters) else {
            self.mark_probe_identity_truncated(counters);
            return DefeqMemoLookup::Ineligible;
        };
        let Some(parameters) = self.intern_parameter_profile(parameters, counters) else {
            self.mark_probe_identity_truncated(counters);
            return DefeqMemoLookup::Ineligible;
        };
        let key = DefeqMemoKey {
            lhs,
            rhs,
            context,
            parameters,
        };
        increment_counter!(counters, memo_eligible_calls);
        self.observe_defeq_probe(key, counters);
        if self.mode != KernelMemoMode::Ephemeral {
            return DefeqMemoLookup::Ineligible;
        }
        increment_counter!(counters, defeq_memo_lookups);
        if let Some(value) = self.defeq.get(&key) {
            increment_counter!(counters, defeq_memo_hits);
            DefeqMemoLookup::Hit {
                fuel_cost: value.fuel_cost,
            }
        } else {
            increment_counter!(counters, defeq_memo_misses);
            DefeqMemoLookup::Miss(DefeqMemoToken(key))
        }
    }

    pub(crate) fn insert_defeq(
        &mut self,
        token: DefeqMemoToken,
        fuel_cost: usize,
        counters: &mut KernelWorkCounters,
    ) {
        if fuel_cost == 0
            || self.mode != KernelMemoMode::Ephemeral
            || self.defeq.contains_key(&token.0)
        {
            return;
        }
        if self.defeq.len() >= self.limits.defeq_entries {
            increment_counter!(counters, defeq_memo_capacity_stops);
            return;
        }
        let charge = RetainedCharge {
            retained_bytes: MAP_ENTRY_OVERHEAD_MULTIPLIER
                .saturating_mul(size_of::<(DefeqMemoKey, DefeqMemoValue)>()),
            ..RetainedCharge::default()
        };
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, defeq_memo_capacity_stops);
            return;
        }
        self.defeq.insert(token.0, DefeqMemoValue { fuel_cost });
        increment_counter!(counters, defeq_memo_inserts);
        counters.defeq_memo_entries = self.defeq.len() as u64;
    }

    fn intern_expr_origin(
        &mut self,
        origin: MemoExprOrigin<'_>,
        counters: &mut KernelWorkCounters,
    ) -> Option<MemoExprId> {
        match origin {
            MemoExprOrigin::Borrowed => {
                increment_counter!(counters, memo_ineligible_borrowed);
                None
            }
            MemoExprOrigin::Fresh => {
                increment_counter!(counters, memo_ineligible_fresh);
                None
            }
            MemoExprOrigin::Retained(owner) => self.intern_expr(owner, counters),
        }
    }

    fn intern_expr(
        &mut self,
        owner: &Arc<Expr>,
        counters: &mut KernelWorkCounters,
    ) -> Option<MemoExprId> {
        let pointer = Arc::as_ptr(owner) as usize;
        if let Some(id) = self.exprs.by_pointer.get(&pointer) {
            return Some(*id);
        }
        if self.exprs.retained.len() >= self.limits.expr_identities {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let Some(mut charge) = expression_charge(
            owner,
            self.remaining_node_budget(),
            self.remaining_byte_budget(),
        ) else {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        };
        charge.retained_bytes = charge
            .retained_bytes
            .saturating_add(ARC_ALLOCATION_HEADER_BYTES)
            .saturating_add(
                MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<(usize, MemoExprId)>()),
            )
            .saturating_add(size_of::<Arc<Expr>>());
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let id = MemoExprId(self.exprs.retained.len() as u32);
        self.exprs.retained.push(Arc::clone(owner));
        self.exprs.by_pointer.insert(pointer, id);
        counters.memo_expr_identities = self.exprs.retained.len() as u64;
        Some(id)
    }

    fn intern_local(
        &mut self,
        owner: &Arc<LocalDecl>,
        counters: &mut KernelWorkCounters,
    ) -> Option<MemoLocalId> {
        let pointer = Arc::as_ptr(owner) as usize;
        if let Some(id) = self.locals.by_pointer.get(&pointer) {
            return Some(*id);
        }
        if self.locals.retained.len() >= self.limits.local_identities {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let mut charge = RetainedCharge {
            retained_bytes: size_of::<LocalDecl>()
                .saturating_add(ARC_ALLOCATION_HEADER_BYTES)
                .saturating_add(
                    MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<(usize, MemoLocalId)>()),
                )
                .saturating_add(size_of::<Arc<LocalDecl>>()),
            ..RetainedCharge::default()
        };
        for expression in owner.memo_expressions() {
            let Some(part) = expression_charge(
                expression,
                self.remaining_node_budget()
                    .saturating_sub(charge.node_occurrences),
                self.remaining_byte_budget()
                    .saturating_sub(charge.retained_bytes),
            ) else {
                increment_counter!(counters, memo_identity_capacity_stops);
                return None;
            };
            charge.node_occurrences = charge.node_occurrences.checked_add(part.node_occurrences)?;
            charge.retained_bytes = charge.retained_bytes.checked_add(part.retained_bytes)?;
        }
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let id = MemoLocalId(self.locals.retained.len() as u32);
        self.locals.retained.push(Arc::clone(owner));
        self.locals.by_pointer.insert(pointer, id);
        counters.memo_local_identities = self.locals.retained.len() as u64;
        Some(id)
    }

    fn intern_context(
        &mut self,
        ctx: &Ctx,
        counters: &mut KernelWorkCounters,
    ) -> Option<MemoContextId> {
        let local_count = ctx.memo_locals().len();
        if local_count > self.limits.context_occurrences
            || local_count > self.limits.local_identities
        {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let mut ids = Vec::with_capacity(local_count);
        for local in ctx.memo_locals() {
            ids.push(self.intern_local(local, counters)?);
        }
        if let Some(index) = self
            .contexts
            .retained
            .iter()
            .position(|existing| existing.as_ref() == ids.as_slice())
        {
            return Some(MemoContextId(index as u32));
        }
        if self.contexts.retained.len() >= self.limits.context_identities {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let charge = RetainedCharge {
            context_occurrences: ids.len(),
            retained_bytes: ids
                .len()
                .saturating_mul(size_of::<MemoLocalId>())
                .saturating_add(
                    MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<Box<[MemoLocalId]>>()),
                ),
            ..RetainedCharge::default()
        };
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let id = MemoContextId(self.contexts.retained.len() as u32);
        self.contexts.retained.push(ids.into_boxed_slice());
        counters.memo_context_identities = self.contexts.retained.len() as u64;
        Some(id)
    }

    fn intern_parameter_profile(
        &mut self,
        parameters: &[String],
        counters: &mut KernelWorkCounters,
    ) -> Option<MemoParameterProfileId> {
        if parameters.len() > self.limits.parameter_occurrences {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        if let Some(index) = self
            .parameter_profiles
            .retained
            .iter()
            .position(|existing| existing.as_ref() == parameters)
        {
            return Some(MemoParameterProfileId(index as u32));
        }
        if self.parameter_profiles.retained.len() >= self.limits.parameter_profiles {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let preflight_bytes = parameters.iter().fold(
            parameters
                .len()
                .saturating_mul(size_of::<String>())
                .saturating_add(
                    MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<Box<[String]>>()),
                ),
            |sum, parameter| sum.saturating_add(parameter.capacity()),
        );
        if parameters.len()
            > self
                .limits
                .parameter_occurrences
                .saturating_sub(self.budget.parameter_occurrences)
            || preflight_bytes > self.remaining_byte_budget()
        {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let exact = parameters
            .iter()
            .map(|parameter| parameter.as_str().to_owned())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let retained_bytes = exact.iter().fold(
            exact
                .len()
                .saturating_mul(size_of::<String>())
                .saturating_add(
                    MAP_ENTRY_OVERHEAD_MULTIPLIER.saturating_mul(size_of::<Box<[String]>>()),
                ),
            |sum, parameter| sum.saturating_add(parameter.capacity()),
        );
        let charge = RetainedCharge {
            parameter_occurrences: parameters.len(),
            retained_bytes,
            ..RetainedCharge::default()
        };
        if !self.budget.try_reserve(charge, self.limits, counters) {
            increment_counter!(counters, memo_identity_capacity_stops);
            return None;
        }
        let id = MemoParameterProfileId(self.parameter_profiles.retained.len() as u32);
        self.parameter_profiles.retained.push(exact);
        counters.memo_parameter_profiles = self.parameter_profiles.retained.len() as u64;
        Some(id)
    }

    fn observe_whnf_probe(&mut self, key: WhnfMemoKey, counters: &mut KernelWorkCounters) {
        if !self.probe {
            return;
        }
        increment_counter!(counters, memo_probe_lookups);
        if self.seen_whnf.contains(&key) {
            increment_counter!(counters, memo_probe_repetitions);
        } else if self.seen_whnf.len() < self.limits.whnf_entries {
            let charge = RetainedCharge {
                retained_bytes: MAP_ENTRY_OVERHEAD_MULTIPLIER
                    .saturating_mul(size_of::<WhnfMemoKey>()),
                ..RetainedCharge::default()
            };
            if !self.budget.try_reserve(charge, self.limits, counters) {
                increment_counter!(counters, memo_probe_capacity_stops);
                counters.memo_probe_truncated = true;
                return;
            }
            self.seen_whnf.insert(key);
            increment_counter!(counters, memo_probe_inserts);
        } else {
            increment_counter!(counters, memo_probe_capacity_stops);
            counters.memo_probe_truncated = true;
        }
    }

    fn observe_defeq_probe(&mut self, key: DefeqMemoKey, counters: &mut KernelWorkCounters) {
        if !self.probe {
            return;
        }
        increment_counter!(counters, memo_probe_lookups);
        if self.seen_defeq.contains(&key) {
            increment_counter!(counters, memo_probe_repetitions);
        } else if self.seen_defeq.len() < self.limits.defeq_entries {
            let charge = RetainedCharge {
                retained_bytes: MAP_ENTRY_OVERHEAD_MULTIPLIER
                    .saturating_mul(size_of::<DefeqMemoKey>()),
                ..RetainedCharge::default()
            };
            if !self.budget.try_reserve(charge, self.limits, counters) {
                increment_counter!(counters, memo_probe_capacity_stops);
                counters.memo_probe_truncated = true;
                return;
            }
            self.seen_defeq.insert(key);
            increment_counter!(counters, memo_probe_inserts);
        } else {
            increment_counter!(counters, memo_probe_capacity_stops);
            counters.memo_probe_truncated = true;
        }
    }

    fn mark_probe_identity_truncated(&self, counters: &mut KernelWorkCounters) {
        if self.probe {
            increment_counter!(counters, memo_probe_capacity_stops);
            counters.memo_probe_truncated = true;
        }
    }

    fn remaining_node_budget(&self) -> usize {
        self.limits
            .node_occurrences
            .saturating_sub(self.budget.node_occurrences)
    }

    fn remaining_byte_budget(&self) -> usize {
        self.limits
            .retained_bytes
            .saturating_sub(self.budget.retained_bytes)
    }
}

fn expression_charge(
    root: &Expr,
    remaining_nodes: usize,
    remaining_bytes: usize,
) -> Option<RetainedCharge> {
    let mut stack = vec![root];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    while let Some(expression) = stack.pop() {
        nodes = nodes.checked_add(1)?;
        bytes = bytes.checked_add(size_of::<Expr>())?;
        if nodes > remaining_nodes || bytes > remaining_bytes {
            return None;
        }
        match expression {
            Expr::Sort(level) => charge_level(
                level,
                &mut nodes,
                &mut bytes,
                remaining_nodes,
                remaining_bytes,
            )?,
            Expr::BVar(_) => {}
            Expr::Const { name, levels } => {
                bytes = bytes
                    .checked_add(name.capacity())?
                    .checked_add(levels.capacity().checked_mul(size_of::<Level>())?)?;
                if bytes > remaining_bytes {
                    return None;
                }
                for level in levels {
                    charge_level(
                        level,
                        &mut nodes,
                        &mut bytes,
                        remaining_nodes,
                        remaining_bytes,
                    )?;
                }
            }
            Expr::App(fun, arg) => {
                bytes = bytes.checked_add(2usize.saturating_mul(ARC_ALLOCATION_HEADER_BYTES))?;
                if bytes > remaining_bytes {
                    return None;
                }
                stack.push(fun);
                stack.push(arg);
            }
            Expr::Lam { binder, ty, body } | Expr::Pi { binder, ty, body } => {
                bytes = bytes
                    .checked_add(binder.capacity())?
                    .checked_add(2usize.saturating_mul(ARC_ALLOCATION_HEADER_BYTES))?;
                if bytes > remaining_bytes {
                    return None;
                }
                stack.push(ty);
                stack.push(body);
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => {
                bytes = bytes
                    .checked_add(binder.capacity())?
                    .checked_add(3usize.saturating_mul(ARC_ALLOCATION_HEADER_BYTES))?;
                if bytes > remaining_bytes {
                    return None;
                }
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
        }
    }
    Some(RetainedCharge {
        node_occurrences: nodes,
        retained_bytes: bytes,
        ..RetainedCharge::default()
    })
}

fn charge_level(
    root: &Level,
    nodes: &mut usize,
    bytes: &mut usize,
    remaining_nodes: usize,
    remaining_bytes: usize,
) -> Option<()> {
    let mut stack = vec![root];
    while let Some(level) = stack.pop() {
        *nodes = nodes.checked_add(1)?;
        *bytes = bytes.checked_add(size_of::<Level>())?;
        if *nodes > remaining_nodes || *bytes > remaining_bytes {
            return None;
        }
        match level {
            Level::Zero => {}
            Level::Succ(inner) => stack.push(inner),
            Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
                stack.push(lhs);
                stack.push(rhs);
            }
            Level::Param(name) => {
                *bytes = bytes.checked_add(name.capacity())?;
                if *bytes > remaining_bytes {
                    return None;
                }
            }
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn retained(name: &str) -> Arc<Expr> {
        Arc::new(Expr::konst(name, vec![]))
    }

    fn memo_with(mut limits: KernelMemoLimits) -> KernelOperationMemo {
        limits.retained_bytes = limits.retained_bytes.max(64 * 1024);
        KernelOperationMemo::with_limits(KernelExecutionOptions::ephemeral_memo(), limits)
    }

    fn whnf_miss(
        memo: &mut KernelOperationMemo,
        owner: &Arc<Expr>,
        ctx: &Ctx,
        parameters: &[String],
        counters: &mut KernelWorkCounters,
    ) -> Option<WhnfMemoToken> {
        match memo.whnf_lookup(
            MemoExprOrigin::Retained(owner),
            ctx,
            parameters,
            ResourceLimitKind::Whnf,
            counters,
        ) {
            WhnfMemoLookup::Miss(token) => Some(token),
            WhnfMemoLookup::Ineligible | WhnfMemoLookup::Hit { .. } => None,
        }
    }

    #[test]
    fn every_identity_and_sequence_limit_stops_deterministically() {
        let root = retained("root");

        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            expr_identities: 1,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &Ctx::new(), &[], &mut counters).is_some());
        assert!(whnf_miss(
            &mut memo,
            &retained("other"),
            &Ctx::new(),
            &[],
            &mut counters,
        )
        .is_none());
        assert_eq!(counters.memo_expr_identities, 1);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut first_ctx = Ctx::new();
        first_ctx.push_assumption("x", Expr::sort(Level::zero()));
        let mut second_ctx = Ctx::new();
        second_ctx.push_assumption("x", Expr::sort(Level::zero()));
        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            local_identities: 1,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &first_ctx, &[], &mut counters).is_some());
        assert!(whnf_miss(&mut memo, &root, &second_ctx, &[], &mut counters).is_none());
        assert_eq!(counters.memo_local_identities, 1);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            context_identities: 1,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &Ctx::new(), &[], &mut counters).is_some());
        assert!(whnf_miss(&mut memo, &root, &first_ctx, &[], &mut counters).is_none());
        assert_eq!(counters.memo_context_identities, 1);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            parameter_profiles: 1,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &Ctx::new(), &[], &mut counters).is_some());
        assert!(whnf_miss(
            &mut memo,
            &root,
            &Ctx::new(),
            &["u".to_owned()],
            &mut counters,
        )
        .is_none());
        assert_eq!(counters.memo_parameter_profiles, 1);
        assert_eq!(counters.memo_identity_capacity_stops, 1);
    }

    #[test]
    fn every_occurrence_and_retained_byte_limit_stops_deterministically() {
        let root = retained("root");

        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            node_occurrences: 0,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &Ctx::new(), &[], &mut counters).is_none());
        assert_eq!(counters.memo_retained_node_occurrences, 0);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut ctx = Ctx::new();
        ctx.push_assumption("x", Expr::sort(Level::zero()));
        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            context_occurrences: 0,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(&mut memo, &root, &ctx, &[], &mut counters).is_none());
        assert_eq!(counters.memo_retained_context_occurrences, 0);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(KernelMemoLimits {
            parameter_occurrences: 0,
            ..KernelMemoLimits::V1
        });
        assert!(whnf_miss(
            &mut memo,
            &root,
            &Ctx::new(),
            &["u".to_owned()],
            &mut counters,
        )
        .is_none());
        assert_eq!(counters.memo_retained_parameter_occurrences, 0);
        assert_eq!(counters.memo_identity_capacity_stops, 1);

        let mut byte_limits = KernelMemoLimits {
            expr_identities: 1,
            local_identities: 0,
            context_identities: 0,
            parameter_profiles: 0,
            ..KernelMemoLimits::V1
        };
        byte_limits.retained_bytes = byte_limits.retained_sequence_capacity_charge();
        let mut counters = KernelWorkCounters::default();
        let mut memo =
            KernelOperationMemo::with_limits(KernelExecutionOptions::ephemeral_memo(), byte_limits);
        assert!(whnf_miss(&mut memo, &root, &Ctx::new(), &[], &mut counters).is_none());
        assert_eq!(memo.retained_bytes(), byte_limits.retained_bytes);
        assert_eq!(counters.memo_identity_capacity_stops, 1);
    }

    #[test]
    fn oversized_context_and_parameter_profiles_stop_before_identity_work() {
        let root = retained("root");
        let limits = KernelMemoLimits {
            local_identities: 8,
            context_occurrences: 4,
            parameter_occurrences: 4,
            ..KernelMemoLimits::tiny()
        };

        let mut oversized_context = Ctx::new();
        for index in 0..5 {
            oversized_context.push_assumption(format!("x{index}"), Expr::sort(Level::zero()));
        }
        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(limits);
        assert!(whnf_miss(&mut memo, &root, &oversized_context, &[], &mut counters,).is_none());
        assert_eq!(counters.memo_local_identities, 0);
        assert_eq!(counters.memo_context_identities, 0);
        assert_eq!(counters.memo_retained_context_occurrences, 0);

        let oversized_parameters = (0..5).map(|index| format!("u{index}")).collect::<Vec<_>>();
        let mut counters = KernelWorkCounters::default();
        let mut memo = memo_with(limits);
        assert!(whnf_miss(
            &mut memo,
            &root,
            &Ctx::new(),
            &oversized_parameters,
            &mut counters,
        )
        .is_none());
        assert_eq!(counters.memo_parameter_profiles, 0);
        assert_eq!(counters.memo_retained_parameter_occurrences, 0);
    }

    #[test]
    fn both_tables_stop_without_eviction_and_keep_existing_hits() {
        let first = retained("first");
        let second = retained("second");
        let third = retained("third");
        let limits = KernelMemoLimits {
            whnf_entries: 1,
            defeq_entries: 1,
            ..KernelMemoLimits::V1
        };
        let mut memo = memo_with(limits);
        let mut counters = KernelWorkCounters::default();
        let whnf_token = whnf_miss(&mut memo, &first, &Ctx::new(), &[], &mut counters).unwrap();
        memo.insert_whnf(whnf_token, &first, 1, &mut counters);
        let stopped_token = whnf_miss(&mut memo, &second, &Ctx::new(), &[], &mut counters).unwrap();
        memo.insert_whnf(stopped_token, &second, 1, &mut counters);
        assert_eq!(counters.whnf_memo_entries, 1);
        assert_eq!(counters.whnf_memo_capacity_stops, 1);
        assert!(matches!(
            memo.whnf_lookup(
                MemoExprOrigin::Retained(&first),
                &Ctx::new(),
                &[],
                ResourceLimitKind::Whnf,
                &mut counters,
            ),
            WhnfMemoLookup::Hit { fuel_cost: 1, .. }
        ));

        let first_defeq = match memo.defeq_lookup(
            MemoExprOrigin::Retained(&first),
            MemoExprOrigin::Retained(&second),
            &Ctx::new(),
            &[],
            &mut counters,
        ) {
            DefeqMemoLookup::Miss(token) => token,
            _ => panic!("expected a defeq miss"),
        };
        memo.insert_defeq(first_defeq, 2, &mut counters);
        let stopped_defeq = match memo.defeq_lookup(
            MemoExprOrigin::Retained(&second),
            MemoExprOrigin::Retained(&third),
            &Ctx::new(),
            &[],
            &mut counters,
        ) {
            DefeqMemoLookup::Miss(token) => token,
            _ => panic!("expected a second defeq miss"),
        };
        memo.insert_defeq(stopped_defeq, 2, &mut counters);
        assert_eq!(counters.defeq_memo_entries, 1);
        assert_eq!(counters.defeq_memo_capacity_stops, 1);
        assert!(matches!(
            memo.defeq_lookup(
                MemoExprOrigin::Retained(&first),
                MemoExprOrigin::Retained(&second),
                &Ctx::new(),
                &[],
                &mut counters,
            ),
            DefeqMemoLookup::Hit { fuel_cost: 2 }
        ));
    }

    #[test]
    fn accounting_rejects_spare_capacity_and_deep_inputs_iteratively() {
        let mut name = String::with_capacity(8 * 1024);
        name.push('x');
        let spare = Expr::Const {
            name,
            levels: Vec::with_capacity(8 * 1024),
        };
        assert!(expression_charge(&spare, 64, 1024).is_none());

        let mut deep = Expr::bvar(0);
        for _ in 0..1024 {
            deep = Expr::app(deep, Expr::bvar(0));
        }
        assert!(expression_charge(&deep, 64, usize::MAX).is_none());
    }

    #[test]
    fn retained_budget_overflow_fails_closed_and_is_reported() {
        let mut budget = RetainedBudget {
            retained_bytes: usize::MAX,
            ..RetainedBudget::default()
        };
        let mut counters = KernelWorkCounters::default();
        assert!(!budget.try_reserve(
            RetainedCharge {
                retained_bytes: 1,
                ..RetainedCharge::default()
            },
            KernelMemoLimits {
                retained_bytes: usize::MAX,
                ..KernelMemoLimits::V1
            },
            &mut counters,
        ));
        assert_eq!(counters.memo_accounting_overflows, 1);
        assert!(counters.overflowed);
    }
}

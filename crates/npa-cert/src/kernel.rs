use std::{
    collections::BTreeSet,
    mem::size_of,
    sync::{atomic::AtomicUsize, Arc},
};

use npa_kernel::{
    eq_inductive, eq_rec_type, nat_inductive, Binder, ConstructorDecl, Decl, Env, Error, Expr,
    InductiveDecl, Level, MutualInductiveBlock, RecursorDecl, RecursorRules, Reducibility,
    UniverseConstraint,
};

use crate::hash_with_domain;
use crate::local_authoring::CertificateImportView;
use crate::types::{
    CertError, CertReducibility, CertificateTermMaterializationObservation, CoreFeature, DeclCert,
    DeclPayload, ExportEntry, ExportKind, GlobalRef, Hash, LevelId, LevelNode, ModuleCert, Name,
    NameId, Result, TermId, TermNode, UniverseConstraintSpec, VerifiedModule,
};
use crate::CertificateFormatVersion;

const BUILTIN_NAT: &str = "Nat";
const BUILTIN_NAT_ZERO: &str = "Nat.zero";
const BUILTIN_NAT_SUCC: &str = "Nat.succ";
const BUILTIN_NAT_REC: &str = "Nat.rec";
const BUILTIN_EQ: &str = "Eq";
const BUILTIN_EQ_REFL: &str = "Eq.refl";
const BUILTIN_EQ_REC: &str = "Eq.rec";

/// Stable identifier for the deterministic certificate term-materialization budget policy.
pub const TERM_MATERIALIZATION_BUDGET_POLICY_V1: &str =
    "npa.certificate-term-materialization-budget.v1";
/// Maximum aggregate logical bytes admitted for term materialization in one verification call.
pub const TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT: u64 = 268_435_456;
pub(crate) const TERM_EXPR_INLINE_CHARGE_BYTES_V1: u64 = 64;
pub(crate) const TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1: u64 = 64;
pub(crate) const TERM_ARC_LAYOUT_ALLOWANCE_BYTES_V1: u64 = 48;
pub(crate) const TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1: u64 = 8;
pub(crate) const TERM_ID_SLOT_CHARGE_BYTES_V1: u64 = 8;
pub(crate) const TERM_SELECTION_SLOT_CHARGE_BYTES_V1: u64 = 1;
pub(crate) const TERM_LEVEL_NODE_CHARGE_BYTES_V1: u64 = 64;
pub(crate) const TERM_PLANNER_RECORD_CHARGE_BYTES_V1: u64 = 256;
pub(crate) const TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1: u64 = 32;

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
const _: () = {
    assert!(size_of::<Expr>() <= TERM_EXPR_INLINE_CHARGE_BYTES_V1 as usize);
    assert!(
        TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1 as usize
            >= 2 * size_of::<AtomicUsize>() + TERM_ARC_LAYOUT_ALLOWANCE_BYTES_V1 as usize
    );
    assert!(size_of::<Option<Arc<Expr>>>() <= TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1 as usize);
    assert!(size_of::<TermId>() <= TERM_ID_SLOT_CHARGE_BYTES_V1 as usize);
    assert!(size_of::<String>() <= TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1 as usize);
    assert!(size_of::<Level>() <= 32);
};

#[derive(Debug)]
pub(crate) struct TermMaterializationBudgetV1 {
    admitted_bytes: u64,
}

impl TermMaterializationBudgetV1 {
    pub(crate) fn new() -> Self {
        Self { admitted_bytes: 0 }
    }

    pub(crate) fn fits(
        &self,
        candidate: u64,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> bool {
        let Some(total) = self.admitted_bytes.checked_add(candidate) else {
            if let Some(observation) = observation {
                observation.observe_overflow();
            }
            return false;
        };
        total <= TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
    }

    pub(crate) fn commit(
        &mut self,
        candidate: u64,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) {
        self.admitted_bytes = self
            .admitted_bytes
            .checked_add(candidate)
            .expect("a previously fitted materialization charge must commit");
        if let Some(observation) = observation {
            observation.observe_charged_bytes(candidate);
        }
    }

    #[cfg(test)]
    pub(crate) fn admitted_bytes(&self) -> u64 {
        self.admitted_bytes
    }

    #[cfg(test)]
    pub(crate) fn exhausted_for_test() -> Self {
        Self {
            admitted_bytes: TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT,
        }
    }

    #[cfg(test)]
    pub(crate) fn with_admitted_bytes_for_test(admitted_bytes: u64) -> Self {
        assert!(admitted_bytes <= TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT);
        Self { admitted_bytes }
    }
}

/// One all-or-legacy admission for a complete imported materialization plan.
///
/// Construction is crate-private so callers cannot build imported tables
/// without first fitting their full aggregate against the operation budget.
pub(crate) struct ImportedMaterializationAdmission {
    charged_bytes: u64,
}

impl ImportedMaterializationAdmission {
    pub(crate) fn fit(
        budget: &TermMaterializationBudgetV1,
        charged_bytes: u64,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> MaterializationAttempt<Self> {
        if budget.fits(charged_bytes, observation) {
            MaterializationAttempt::Ready(Self { charged_bytes })
        } else {
            MaterializationAttempt::Fallback(MaterializationStop::Capacity)
        }
    }

    pub(crate) fn commit(
        self,
        budget: &mut TermMaterializationBudgetV1,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) {
        budget.commit(self.charged_bytes, observation);
    }
}

impl Default for TermMaterializationBudgetV1 {
    fn default() -> Self {
        Self::new()
    }
}

/// Exercise the production v1 admission boundary without allocating a term table.
///
/// This adapter is diagnostic-only and exists for the isolated release harness.
/// It uses the same operation budget and observation transitions as the real
/// current/import lanes, but it neither accepts nor constructs certificate
/// evidence.
#[doc(hidden)]
pub fn benchmark_term_materialization_admission_v1(
    candidate_charged_bytes: u64,
) -> CertificateTermMaterializationObservation {
    let mut observation = CertificateTermMaterializationObservation::default();
    let mut budget = TermMaterializationBudgetV1::new();
    if budget.fits(candidate_charged_bytes, Some(&mut observation)) {
        budget.commit(candidate_charged_bytes, Some(&mut observation));
    } else {
        observation.observe_capacity_stop();
        observation.observe_legacy_fallback();
    }
    observation
}

/// Result of one diagnostic execution of the production selected-term planner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermMaterializationBenchmarkResultV1 {
    /// Observation emitted by the real planner, admission, forward builder, and root handoff.
    pub observation: CertificateTermMaterializationObservation,
    /// Logical charge computed by the production plan and used for admission.
    pub planned_charged_bytes: u64,
    /// Certificate hash of the real canonical certificate whose table was materialized.
    pub certificate_hash: Hash,
}

/// Exercise the production selected-term planner on a real canonical certificate.
///
/// This diagnostic-only adapter is used by the isolated release harness. Roots
/// are collected from the named declaration indices, then planned, admitted,
/// forward-materialized, and handed off through the same implementation as the
/// production imported-module lane. The adapter has no charge or result
/// override: admission always uses the exact charge computed from `cert`.
#[doc(hidden)]
pub fn benchmark_term_materialization_plan_v1(
    cert: &ModuleCert,
    declaration_indices: &[usize],
    root_repetitions: u64,
) -> Result<TermMaterializationBenchmarkResultV1> {
    if declaration_indices.is_empty() || root_repetitions == 0 {
        return Err(CertError::DecodeError);
    }
    let mut roots = Vec::new();
    for _ in 0..root_repetitions {
        for declaration_index in declaration_indices {
            let declaration = cert
                .declarations()
                .get(*declaration_index)
                .ok_or(CertError::DecodeError)?;
            collect_decl_payload_term_roots(&declaration.decl, &mut roots);
        }
    }
    if roots.is_empty() {
        return Err(CertError::DecodeError);
    }

    let plan = match KernelExprMaterialization::plan_selected_roots_unadmitted(cert, &roots) {
        MaterializationAttempt::Ready(plan) => plan,
        MaterializationAttempt::Fallback(_) => return Err(CertError::DecodeError),
    };
    let planned_charged_bytes = plan.charge();
    let mut observation = CertificateTermMaterializationObservation::default();
    let mut budget = TermMaterializationBudgetV1::new();
    let admission = match ImportedMaterializationAdmission::fit(
        &budget,
        planned_charged_bytes,
        Some(&mut observation),
    ) {
        MaterializationAttempt::Ready(admission) => admission,
        MaterializationAttempt::Fallback(stop) => {
            if stop == MaterializationStop::Capacity {
                observation.observe_capacity_stop();
            }
            observation.observe_legacy_fallback();
            return Ok(TermMaterializationBenchmarkResultV1 {
                observation,
                planned_charged_bytes,
                certificate_hash: cert.hashes().certificate_hash,
            });
        }
    };
    let materialization = match KernelExprMaterialization::build_selected_roots_uncommitted(
        cert,
        &plan,
        &admission,
        Some(&mut observation),
    ) {
        MaterializationAttempt::Ready(materialization) => materialization,
        MaterializationAttempt::Fallback(_) => return Err(CertError::DecodeError),
    };
    for root in roots {
        let expression = materialization.root_expr(root, Some(&mut observation))?;
        std::hint::black_box(expression);
    }
    admission.commit(&mut budget, Some(&mut observation));
    Ok(TermMaterializationBenchmarkResultV1 {
        observation,
        planned_charged_bytes,
        certificate_hash: cert.hashes().certificate_hash,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MaterializationStop {
    Capacity,
    SpeculativeInvariant,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CurrentMaterializationReserveStop {
    None,
    Selection,
    Nodes,
}

pub(crate) enum MaterializationAttempt<T> {
    Ready(T),
    Fallback(MaterializationStop),
}

fn materialization_layout_supported() -> bool {
    matches!(size_of::<usize>(), 4 | 8)
        && size_of::<Expr>() <= TERM_EXPR_INLINE_CHARGE_BYTES_V1 as usize
        && TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1 as usize
            >= 2 * size_of::<AtomicUsize>() + TERM_ARC_LAYOUT_ALLOWANCE_BYTES_V1 as usize
        && size_of::<Option<Arc<Expr>>>() <= TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1 as usize
        && size_of::<TermId>() <= TERM_ID_SLOT_CHARGE_BYTES_V1 as usize
        && size_of::<String>() <= TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1 as usize
        && size_of::<Level>() <= 32
}

fn checked_charge_add(total: &mut u64, value: u64) -> Option<()> {
    *total = total.checked_add(value)?;
    Some(())
}

fn checked_slot_charge(count: usize, bytes: u64) -> Option<u64> {
    u64::try_from(count).ok()?.checked_mul(bytes)
}

pub(crate) trait KernelCertView {
    fn name_table(&self) -> &[Name];
    fn level_table(&self) -> &[LevelNode];
    fn term_table(&self) -> &[TermNode];
    fn declarations(&self) -> &[DeclCert];
    fn export_block(&self) -> &[ExportEntry];
}

impl KernelCertView for ModuleCert {
    fn name_table(&self) -> &[Name] {
        self.name_table()
    }

    fn level_table(&self) -> &[LevelNode] {
        self.level_table()
    }

    fn term_table(&self) -> &[TermNode] {
        self.term_table()
    }

    fn declarations(&self) -> &[DeclCert] {
        self.declarations()
    }

    fn export_block(&self) -> &[ExportEntry] {
        self.export_block()
    }
}

impl KernelCertView for VerifiedModule {
    fn name_table(&self) -> &[Name] {
        self.name_table()
    }

    fn level_table(&self) -> &[LevelNode] {
        self.level_table()
    }

    fn term_table(&self) -> &[TermNode] {
        self.term_table()
    }

    fn declarations(&self) -> &[DeclCert] {
        self.declarations()
    }

    fn export_block(&self) -> &[ExportEntry] {
        self.export_block()
    }
}

impl KernelCertView for dyn CertificateImportView + '_ {
    fn name_table(&self) -> &[Name] {
        CertificateImportView::name_table(self)
    }

    fn level_table(&self) -> &[LevelNode] {
        CertificateImportView::level_table(self)
    }

    fn term_table(&self) -> &[TermNode] {
        CertificateImportView::term_table(self)
    }

    fn declarations(&self) -> &[DeclCert] {
        CertificateImportView::declarations(self)
    }

    fn export_block(&self) -> &[ExportEntry] {
        CertificateImportView::export_block(self)
    }
}

fn name_owned_bytes(name: &Name) -> Option<u64> {
    let component_bytes = name.0.iter().try_fold(0_u64, |total, component| {
        total.checked_add(u64::try_from(component.len()).ok()?)
    })?;
    let separators = u64::try_from(name.0.len().saturating_sub(1)).ok()?;
    component_bytes.checked_add(separators)
}

fn name_id_owned_bytes<C: KernelCertView + ?Sized>(cert: &C, name: NameId) -> Option<u64> {
    name_owned_bytes(cert.name_table().get(name)?)
}

fn primary_decl_name_id(decl: &DeclPayload) -> NameId {
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

fn global_ref_owned_name_bytes<C: KernelCertView + ?Sized>(
    cert: &C,
    global_ref: &GlobalRef,
) -> Option<u64> {
    match global_ref {
        GlobalRef::Builtin { name, .. }
        | GlobalRef::Imported { name, .. }
        | GlobalRef::LocalGenerated { name, .. } => name_id_owned_bytes(cert, *name),
        GlobalRef::Local { decl_index } => {
            let decl = cert.declarations().get(*decl_index)?;
            name_id_owned_bytes(cert, primary_decl_name_id(&decl.decl))
        }
    }
}

fn level_owned_charge<C: KernelCertView + ?Sized>(cert: &C, level: LevelId) -> Option<u64> {
    let node = cert.level_table().get(level)?;
    let mut total = TERM_LEVEL_NODE_CHARGE_BYTES_V1;
    match node {
        LevelNode::Zero => {}
        LevelNode::Succ(inner) => {
            checked_charge_add(&mut total, level_owned_charge(cert, *inner)?)?
        }
        LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
            checked_charge_add(&mut total, level_owned_charge(cert, *lhs)?)?;
            checked_charge_add(&mut total, level_owned_charge(cert, *rhs)?)?;
        }
        LevelNode::Param(name) => {
            checked_charge_add(&mut total, name_id_owned_bytes(cert, *name)?)?;
        }
    }
    Some(total)
}

fn term_node_owned_charge<C: KernelCertView + ?Sized>(cert: &C, node: &TermNode) -> Option<u64> {
    let mut total =
        TERM_EXPR_INLINE_CHARGE_BYTES_V1.checked_add(TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1)?;
    match node {
        TermNode::Sort(level) => checked_charge_add(&mut total, level_owned_charge(cert, *level)?)?,
        TermNode::BVar(_) | TermNode::App(_, _) => {}
        TermNode::Const { global_ref, levels } => {
            checked_charge_add(&mut total, global_ref_owned_name_bytes(cert, global_ref)?)?;
            for level in levels {
                checked_charge_add(&mut total, level_owned_charge(cert, *level)?)?;
            }
        }
        TermNode::Lam { .. } | TermNode::Pi { .. } => {
            checked_charge_add(&mut total, 1)?;
        }
    }
    Some(total)
}

fn root_handoff_charge<C: KernelCertView + ?Sized>(cert: &C, root: TermId) -> Option<u64> {
    let node = cert.term_table().get(root)?;
    let mut total = TERM_EXPR_INLINE_CHARGE_BYTES_V1;
    match node {
        TermNode::Sort(level) => checked_charge_add(&mut total, level_owned_charge(cert, *level)?)?,
        TermNode::BVar(_) | TermNode::App(_, _) => {}
        TermNode::Const { global_ref, levels } => {
            checked_charge_add(&mut total, global_ref_owned_name_bytes(cert, global_ref)?)?;
            for level in levels {
                checked_charge_add(&mut total, level_owned_charge(cert, *level)?)?;
            }
        }
        TermNode::Lam { .. } | TermNode::Pi { .. } => {
            checked_charge_add(&mut total, 1)?;
        }
    }
    Some(total)
}

fn compound_edge_count(node: &TermNode) -> u64 {
    match node {
        TermNode::App(_, _) | TermNode::Lam { .. } | TermNode::Pi { .. } => 2,
        TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
    }
}

fn complete_materialization_charge<C: KernelCertView + ?Sized>(
    cert: &C,
    selection: &[u8],
    root_requests: &[TermId],
    root_capacity: usize,
    stack_capacity: usize,
) -> Option<u64> {
    if selection.len() != cert.term_table().len() {
        return None;
    }
    let mut total = checked_slot_charge(
        cert.term_table().len(),
        TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1,
    )?;
    checked_charge_add(
        &mut total,
        checked_slot_charge(selection.len(), TERM_SELECTION_SLOT_CHARGE_BYTES_V1)?,
    )?;
    checked_charge_add(
        &mut total,
        checked_slot_charge(root_capacity, TERM_ID_SLOT_CHARGE_BYTES_V1)?,
    )?;
    checked_charge_add(
        &mut total,
        checked_slot_charge(stack_capacity, TERM_ID_SLOT_CHARGE_BYTES_V1)?,
    )?;
    for (selected, node) in selection.iter().zip(cert.term_table()) {
        if *selected == 1 {
            checked_charge_add(&mut total, term_node_owned_charge(cert, node)?)?;
        } else if *selected != 0 {
            return None;
        }
    }
    for root in root_requests {
        checked_charge_add(&mut total, root_handoff_charge(cert, *root)?)?;
    }
    Some(total)
}

fn complete_dense_materialization_charge<C: KernelCertView + ?Sized>(
    cert: &C,
    root_requests: &[TermId],
) -> Option<u64> {
    let table_len = cert.term_table().len();
    let mut total = checked_slot_charge(table_len, TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1)?;
    checked_charge_add(
        &mut total,
        checked_slot_charge(table_len, TERM_SELECTION_SLOT_CHARGE_BYTES_V1)?,
    )?;
    checked_charge_add(
        &mut total,
        checked_slot_charge(root_requests.len(), TERM_ID_SLOT_CHARGE_BYTES_V1)?,
    )?;
    for node in cert.term_table() {
        checked_charge_add(&mut total, term_node_owned_charge(cert, node)?)?;
    }
    for root in root_requests {
        checked_charge_add(&mut total, root_handoff_charge(cert, *root)?)?;
    }
    Some(total)
}

pub(crate) struct KernelExprMaterialization<'a, C: KernelCertView + ?Sized> {
    cert: &'a C,
    nodes: Vec<Option<Arc<Expr>>>,
}

/// Allocation-complete selected closure plan used by aggregate import
/// admission. It contains no `Expr` and performs no budget commit.
pub(crate) struct SelectedTermMaterializationPlan {
    selection: Vec<u8>,
    // Kept alive through replay so the charged scratch capacity has a concrete
    // owner and cannot be accidentally reused by another module plan.
    stack: Vec<TermId>,
    charge: u64,
}

impl SelectedTermMaterializationPlan {
    pub(crate) fn charge(&self) -> u64 {
        self.charge
    }
}

impl<'a, C: KernelCertView + ?Sized> KernelExprMaterialization<'a, C> {
    /// Conservative no-allocation bound used before imported planner state is
    /// reserved. It assumes every term is both selected and handed off once.
    pub(crate) fn conservative_all_roots_selected_charge(cert: &C) -> Option<u64> {
        if !materialization_layout_supported() {
            return None;
        }
        let table_len = cert.term_table().len();
        let mut total = checked_slot_charge(table_len, TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1)?;
        checked_charge_add(
            &mut total,
            checked_slot_charge(table_len, TERM_SELECTION_SLOT_CHARGE_BYTES_V1)?,
        )?;
        checked_charge_add(
            &mut total,
            checked_slot_charge(table_len, TERM_ID_SLOT_CHARGE_BYTES_V1)?,
        )?;
        checked_charge_add(
            &mut total,
            checked_slot_charge(table_len, TERM_ID_SLOT_CHARGE_BYTES_V1)?,
        )?;
        for (id, node) in cert.term_table().iter().enumerate() {
            checked_charge_add(&mut total, term_node_owned_charge(cert, node)?)?;
            checked_charge_add(&mut total, root_handoff_charge(cert, id)?)?;
        }
        Some(total)
    }

    /// Reserve and mark a selected closure without constructing `Expr` nodes.
    /// The caller must have already fitted a conservative aggregate covering
    /// every module plan in the verification operation.
    pub(crate) fn plan_selected_roots_unadmitted(
        cert: &C,
        root_requests: &[TermId],
    ) -> MaterializationAttempt<SelectedTermMaterializationPlan> {
        if !materialization_layout_supported() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        let table_len = cert.term_table().len();
        let mut roots = Vec::new();
        if roots.try_reserve_exact(root_requests.len()).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        roots.extend_from_slice(root_requests);
        roots.sort_unstable();
        roots.dedup();

        let mut selection = Vec::new();
        if selection.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        selection.resize(table_len, 0_u8);
        let mut stack = Vec::new();
        if stack.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        if mark_selected_term_closure(cert, &roots, &mut selection, &mut stack).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        let Some(charge) = complete_materialization_charge(
            cert,
            &selection,
            root_requests,
            root_requests.len(),
            table_len,
        ) else {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        };
        MaterializationAttempt::Ready(SelectedTermMaterializationPlan {
            selection,
            stack,
            charge,
        })
    }

    /// Build a selected table after aggregate admission without fitting or
    /// committing a per-module charge.
    pub(crate) fn build_selected_roots_uncommitted(
        cert: &'a C,
        plan: &SelectedTermMaterializationPlan,
        _admission: &ImportedMaterializationAdmission,
        mut observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> MaterializationAttempt<Self> {
        if plan.selection.len() != cert.term_table().len()
            || plan.stack.capacity() < cert.term_table().len()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        let table_len = cert.term_table().len();
        let mut nodes = Vec::new();
        if nodes.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        nodes.resize_with(table_len, || None);
        let mut materialization = Self { cert, nodes };
        if materialization
            .build_forward(&plan.selection, observation.as_deref_mut())
            .is_err()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        if let Some(observation) = observation {
            observation.observe_slots(u64::try_from(table_len).unwrap_or(u64::MAX));
        }
        MaterializationAttempt::Ready(materialization)
    }

    pub(crate) fn for_current_module(
        cert: &'a C,
        root_requests: &[TermId],
        budget: &mut TermMaterializationBudgetV1,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> MaterializationAttempt<Self> {
        Self::for_current_module_with_reserve_stop(
            cert,
            root_requests,
            budget,
            observation,
            CurrentMaterializationReserveStop::None,
        )
    }

    #[cfg(test)]
    fn for_current_module_with_injected_reserve_stop(
        cert: &'a C,
        root_requests: &[TermId],
        budget: &mut TermMaterializationBudgetV1,
        observation: Option<&mut CertificateTermMaterializationObservation>,
        reserve_stop: CurrentMaterializationReserveStop,
    ) -> MaterializationAttempt<Self> {
        assert_ne!(reserve_stop, CurrentMaterializationReserveStop::None);
        Self::for_current_module_with_reserve_stop(
            cert,
            root_requests,
            budget,
            observation,
            reserve_stop,
        )
    }

    fn for_current_module_with_reserve_stop(
        cert: &'a C,
        root_requests: &[TermId],
        budget: &mut TermMaterializationBudgetV1,
        mut observation: Option<&mut CertificateTermMaterializationObservation>,
        reserve_stop: CurrentMaterializationReserveStop,
    ) -> MaterializationAttempt<Self> {
        if !materialization_layout_supported() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        let table_len = cert.term_table().len();
        let Some(charge) = complete_dense_materialization_charge(cert, root_requests) else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        };
        if !budget.fits(charge, observation.as_deref_mut()) {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        let mut selection = Vec::new();
        if reserve_stop == CurrentMaterializationReserveStop::Selection
            || selection.try_reserve_exact(table_len).is_err()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        selection.resize(table_len, 1_u8);
        let mut nodes = Vec::new();
        if reserve_stop == CurrentMaterializationReserveStop::Nodes
            || nodes.try_reserve_exact(table_len).is_err()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        nodes.resize_with(table_len, || None);
        let mut materialization = Self { cert, nodes };
        if materialization
            .build_forward(&selection, observation.as_deref_mut())
            .is_err()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        budget.commit(charge, observation.as_deref_mut());
        if let Some(observation) = observation {
            observation.observe_slots(u64::try_from(table_len).unwrap_or(u64::MAX));
        }
        MaterializationAttempt::Ready(materialization)
    }

    pub(crate) fn for_selected_roots(
        cert: &'a C,
        root_requests: &[TermId],
        budget: &mut TermMaterializationBudgetV1,
        mut observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> MaterializationAttempt<Self> {
        if !materialization_layout_supported() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        let table_len = cert.term_table().len();
        let preliminary = checked_slot_charge(table_len, TERM_SELECTION_SLOT_CHARGE_BYTES_V1)
            .and_then(|value| {
                value.checked_add(checked_slot_charge(
                    table_len,
                    TERM_ID_SLOT_CHARGE_BYTES_V1,
                )?)
            })
            .and_then(|value| {
                value.checked_add(checked_slot_charge(
                    root_requests.len(),
                    TERM_ID_SLOT_CHARGE_BYTES_V1,
                )?)
            });
        let Some(preliminary) = preliminary else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        };
        if !budget.fits(preliminary, observation.as_deref_mut()) {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }

        let mut roots = Vec::new();
        if roots.try_reserve_exact(root_requests.len()).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        roots.extend_from_slice(root_requests);
        roots.sort_unstable();
        roots.dedup();

        let mut selection = Vec::new();
        if selection.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        selection.resize(table_len, 0_u8);
        let mut stack = Vec::new();
        if stack.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        if mark_selected_term_closure(cert, &roots, &mut selection, &mut stack).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        let Some(charge) = complete_materialization_charge(
            cert,
            &selection,
            root_requests,
            root_requests.len(),
            table_len,
        ) else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        };
        if !budget.fits(charge, observation.as_deref_mut()) {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        let mut nodes = Vec::new();
        if nodes.try_reserve_exact(table_len).is_err() {
            return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
        }
        nodes.resize_with(table_len, || None);
        let mut materialization = Self { cert, nodes };
        if materialization
            .build_forward(&selection, observation.as_deref_mut())
            .is_err()
        {
            return MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant);
        }
        budget.commit(charge, observation.as_deref_mut());
        if let Some(observation) = observation {
            observation.observe_slots(u64::try_from(table_len).unwrap_or(u64::MAX));
        }
        MaterializationAttempt::Ready(materialization)
    }

    fn build_forward(
        &mut self,
        selection: &[u8],
        mut observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> std::result::Result<(), MaterializationStop> {
        if selection.len() != self.nodes.len() || self.nodes.len() != self.cert.term_table().len() {
            return Err(MaterializationStop::SpeculativeInvariant);
        }
        for (index, selected) in selection.iter().copied().enumerate() {
            if selected == 0 {
                continue;
            }
            if selected != 1 {
                return Err(MaterializationStop::SpeculativeInvariant);
            }
            let node = self
                .cert
                .term_table()
                .get(index)
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            let expr = materialized_expr_from_node(self.cert, &self.nodes, node)?;
            let edges = compound_edge_count(node);
            self.nodes[index] = Some(Arc::new(expr));
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_unique_nodes(1);
                observation.observe_selected_edges(edges);
                observation.observe_reused_child_arcs(edges);
            }
        }
        Ok(())
    }

    pub(crate) fn root_expr(
        &self,
        id: TermId,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> Result<Expr> {
        let root = self
            .nodes
            .get(id)
            .and_then(Option::as_ref)
            .ok_or(CertError::DecodeError)?;
        if let Some(observation) = observation {
            let leaf = matches!(
                root.as_ref(),
                Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. }
            );
            observation.observe_root_request(leaf);
        }
        Ok(root.as_ref().clone())
    }

    #[cfg(test)]
    pub(crate) fn node_arc(&self, id: TermId) -> Option<&Arc<Expr>> {
        self.nodes.get(id).and_then(Option::as_ref)
    }

    #[cfg(test)]
    pub(crate) fn selected_node_count(&self) -> usize {
        self.nodes.iter().filter(|node| node.is_some()).count()
    }
}

fn mark_selected_term_closure<C: KernelCertView + ?Sized>(
    cert: &C,
    roots: &[TermId],
    selection: &mut [u8],
    stack: &mut Vec<TermId>,
) -> std::result::Result<(), MaterializationStop> {
    for root in roots.iter().rev().copied() {
        if root >= selection.len() {
            return Err(MaterializationStop::SpeculativeInvariant);
        }
        if selection[root] == 0 {
            selection[root] = 1;
            stack.push(root);
        }
    }
    while let Some(id) = stack.pop() {
        let node = cert
            .term_table()
            .get(id)
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        let mut push_child = |child: TermId| {
            if child >= selection.len() || child >= id {
                return Err(MaterializationStop::SpeculativeInvariant);
            }
            if selection[child] == 0 {
                selection[child] = 1;
                stack.push(child);
            }
            Ok(())
        };
        match node {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(lhs, rhs) => {
                push_child(*rhs)?;
                push_child(*lhs)?;
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                push_child(*body)?;
                push_child(*ty)?;
            }
        }
    }
    Ok(())
}

fn materialized_child(
    nodes: &[Option<Arc<Expr>>],
    id: TermId,
) -> std::result::Result<Arc<Expr>, MaterializationStop> {
    nodes
        .get(id)
        .and_then(Option::as_ref)
        .cloned()
        .ok_or(MaterializationStop::SpeculativeInvariant)
}

fn materialized_expr_from_node<C: KernelCertView + ?Sized>(
    cert: &C,
    nodes: &[Option<Arc<Expr>>],
    node: &TermNode,
) -> std::result::Result<Expr, MaterializationStop> {
    Ok(match node {
        TermNode::Sort(level) => Expr::Sort(
            level_from_node(cert, *level).map_err(|_| MaterializationStop::SpeculativeInvariant)?,
        ),
        TermNode::BVar(index) => Expr::BVar(*index),
        TermNode::Const { global_ref, levels } => Expr::Const {
            name: global_ref_name(cert, global_ref)
                .map_err(|_| MaterializationStop::SpeculativeInvariant)?,
            levels: levels
                .iter()
                .map(|level| {
                    level_from_node(cert, *level)
                        .map_err(|_| MaterializationStop::SpeculativeInvariant)
                })
                .collect::<std::result::Result<Vec<_>, _>>()?,
        },
        TermNode::App(fun, arg) => Expr::App(
            materialized_child(nodes, *fun)?,
            materialized_child(nodes, *arg)?,
        ),
        TermNode::Lam { ty, body } => Expr::Lam {
            binder: "_".to_owned(),
            ty: materialized_child(nodes, *ty)?,
            body: materialized_child(nodes, *body)?,
        },
        TermNode::Pi { ty, body } => Expr::Pi {
            binder: "_".to_owned(),
            ty: materialized_child(nodes, *ty)?,
            body: materialized_child(nodes, *body)?,
        },
    })
}

pub(crate) enum KernelTermConversion<'a, C: KernelCertView + ?Sized> {
    Legacy(&'a C),
    Materialized(KernelExprMaterialization<'a, C>),
}

impl<'a, C: KernelCertView + ?Sized> KernelTermConversion<'a, C> {
    pub(crate) fn from_attempt(
        cert: &'a C,
        attempt: MaterializationAttempt<KernelExprMaterialization<'a, C>>,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> Self {
        match attempt {
            MaterializationAttempt::Ready(table) => Self::Materialized(table),
            MaterializationAttempt::Fallback(stop) => {
                if let Some(observation) = observation {
                    if stop == MaterializationStop::Capacity {
                        observation.observe_capacity_stop();
                    }
                    observation.observe_legacy_fallback();
                }
                Self::Legacy(cert)
            }
        }
    }

    pub(crate) fn root_expr(
        &self,
        id: TermId,
        observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> Result<Expr> {
        match self {
            Self::Legacy(cert) => expr_from_term(*cert, id),
            Self::Materialized(table) => table.root_expr(id, observation),
        }
    }

    #[cfg(test)]
    pub(crate) fn materialized(&self) -> Option<&KernelExprMaterialization<'a, C>> {
        match self {
            Self::Legacy(_) => None,
            Self::Materialized(table) => Some(table),
        }
    }
}

pub(crate) fn cert_decl_to_kernel_decl_with_terms(
    cert: &ModuleCert,
    terms: &KernelTermConversion<'_, ModuleCert>,
    decl: &DeclCert,
    observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<Decl> {
    decl_payload_to_kernel_decl_with_terms(cert, terms, &decl.decl, observation)
}

/// Reconstruct kernel declarations exported by a verified module for downstream checking.
///
/// Transparent definitions keep their bodies and reducibility metadata; opaque definitions and
/// theorem exports are reconstructed as axioms because their bodies are not part of the public
/// downstream interface.
pub fn verified_module_to_kernel_decls(module: &VerifiedModule) -> Result<Vec<Decl>> {
    certificate_import_to_kernel_decls(module)
}

pub(crate) fn certificate_import_to_kernel_decls(
    module: &dyn CertificateImportView,
) -> Result<Vec<Decl>> {
    let roots = collect_certificate_import_projection_roots(module)?;
    let mut budget = TermMaterializationBudgetV1::new();
    let attempt = KernelExprMaterialization::for_selected_roots(module, &roots, &mut budget, None);
    let terms = KernelTermConversion::from_attempt(module, attempt, None);
    let mut decls = Vec::new();
    for decl in module.declarations() {
        decls.push(match &decl.decl {
            DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } => {
                let entry = export_entry_for_decl(module, *name, ExportKind::Axiom)?;
                let universe_constraints =
                    universe_constraints_from_specs(module, &entry.universe_constraints)?;
                if universe_constraints.is_empty() {
                    Decl::Axiom {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        ty: terms.root_expr(entry.ty, None)?,
                    }
                } else {
                    Decl::AxiomConstrained {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        universe_constraints,
                        ty: terms.root_expr(entry.ty, None)?,
                    }
                }
            }
            DeclPayload::Def { name, .. } | DeclPayload::DefConstrained { name, .. } => {
                let entry = export_entry_for_decl(module, *name, ExportKind::Def)?;
                let ty = terms.root_expr(entry.ty, None)?;
                let universe_constraints =
                    universe_constraints_from_specs(module, &entry.universe_constraints)?;
                match entry.reducibility.ok_or(CertError::DecodeError)? {
                    CertReducibility::Reducible if universe_constraints.is_empty() => Decl::Def {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        ty,
                        value: terms.root_expr(entry.body.ok_or(CertError::DecodeError)?, None)?,
                        reducibility: Reducibility::Reducible,
                    },
                    CertReducibility::Reducible => Decl::DefConstrained {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        universe_constraints,
                        ty,
                        value: terms.root_expr(entry.body.ok_or(CertError::DecodeError)?, None)?,
                        reducibility: Reducibility::Reducible,
                    },
                    CertReducibility::Opaque if universe_constraints.is_empty() => Decl::Axiom {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        ty,
                    },
                    CertReducibility::Opaque => Decl::AxiomConstrained {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        universe_constraints,
                        ty,
                    },
                }
            }
            DeclPayload::Theorem { name, .. } | DeclPayload::TheoremConstrained { name, .. } => {
                let entry = export_entry_for_decl(module, *name, ExportKind::Theorem)?;
                let universe_constraints =
                    universe_constraints_from_specs(module, &entry.universe_constraints)?;
                if universe_constraints.is_empty() {
                    Decl::Axiom {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        ty: terms.root_expr(entry.ty, None)?,
                    }
                } else {
                    Decl::AxiomConstrained {
                        name: name_to_string(module, entry.name)?,
                        universe_params: universe_names(module, &entry.universe_params)?,
                        universe_constraints,
                        ty: terms.root_expr(entry.ty, None)?,
                    }
                }
            }
            DeclPayload::Inductive { .. } | DeclPayload::InductiveConstrained { .. } => {
                normalize_builtin_import_decl(decl_payload_to_kernel_decl_with_terms(
                    module, &terms, &decl.decl, None,
                )?)
            }
            DeclPayload::MutualInductiveBlock { .. } => {
                decl_payload_to_kernel_decl_with_terms(module, &terms, &decl.decl, None)?
            }
        });
    }
    Ok(decls)
}

pub(crate) fn certificate_import_export_entry_to_kernel_decl(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
) -> Result<Decl> {
    let roots = collect_export_entry_roots(module, entry)?;
    let mut budget = TermMaterializationBudgetV1::new();
    let attempt = KernelExprMaterialization::for_selected_roots(module, &roots, &mut budget, None);
    let terms = KernelTermConversion::from_attempt(module, attempt, None);
    certificate_import_export_entry_to_kernel_decl_with_terms(module, entry, &terms, None)
}

pub(crate) fn certificate_import_export_entry_to_kernel_decl_with_terms(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
    terms: &KernelTermConversion<'_, dyn CertificateImportView + '_>,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<Decl> {
    match entry.kind {
        ExportKind::Axiom | ExportKind::Theorem => {
            let ty = terms.root_expr(entry.ty, observation.as_deref_mut())?;
            let universe_constraints =
                universe_constraints_from_specs(module, &entry.universe_constraints)?;
            if universe_constraints.is_empty() {
                Ok(Decl::Axiom {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    ty,
                })
            } else {
                Ok(Decl::AxiomConstrained {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    universe_constraints,
                    ty,
                })
            }
        }
        ExportKind::Def => {
            let ty = terms.root_expr(entry.ty, observation.as_deref_mut())?;
            let universe_constraints =
                universe_constraints_from_specs(module, &entry.universe_constraints)?;
            match entry.reducibility.ok_or(CertError::DecodeError)? {
                CertReducibility::Reducible if universe_constraints.is_empty() => Ok(Decl::Def {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    ty,
                    value: terms.root_expr(
                        entry.body.ok_or(CertError::DecodeError)?,
                        observation.as_deref_mut(),
                    )?,
                    reducibility: Reducibility::Reducible,
                }),
                CertReducibility::Reducible => Ok(Decl::DefConstrained {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    universe_constraints,
                    ty,
                    value: terms.root_expr(
                        entry.body.ok_or(CertError::DecodeError)?,
                        observation.as_deref_mut(),
                    )?,
                    reducibility: Reducibility::Reducible,
                }),
                CertReducibility::Opaque if universe_constraints.is_empty() => Ok(Decl::Axiom {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    ty,
                }),
                CertReducibility::Opaque => Ok(Decl::AxiomConstrained {
                    name: name_to_string(module, entry.name)?,
                    universe_params: universe_names(module, &entry.universe_params)?,
                    universe_constraints,
                    ty,
                }),
            }
        }
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(CertError::DecodeError)?;
            Ok(normalize_builtin_import_decl(
                decl_payload_to_kernel_decl_with_terms(module, terms, &decl.decl, observation)?,
            ))
        }
    }
}

pub(crate) fn source_decl_index_for_export_entry<C: KernelCertView + ?Sized>(
    cert: &C,
    entry: &ExportEntry,
) -> Result<usize> {
    source_decl_index_for_name(cert, entry.name)
}

pub(crate) fn collect_decl_payload_term_roots(decl: &DeclPayload, roots: &mut Vec<TermId>) {
    match decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
            roots.push(*ty);
        }
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            roots.push(*ty);
            roots.push(*value);
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => {
            roots.push(*ty);
            roots.push(*proof);
        }
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
        } => {
            roots.extend(params.iter().map(|binder| binder.ty));
            roots.extend(indices.iter().map(|binder| binder.ty));
            roots.extend(constructors.iter().map(|constructor| constructor.ty));
            roots.extend(recursor.iter().map(|recursor| recursor.ty));
        }
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                roots.extend(inductive.params.iter().map(|binder| binder.ty));
                roots.extend(inductive.indices.iter().map(|binder| binder.ty));
                roots.extend(
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| constructor.ty),
                );
                roots.extend(inductive.recursor.iter().map(|recursor| recursor.ty));
            }
        }
    }
}

pub(crate) fn decl_payload_term_root_count(decl: &DeclPayload) -> Option<usize> {
    match decl {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => Some(1),
        DeclPayload::Def { .. }
        | DeclPayload::DefConstrained { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::TheoremConstrained { .. } => Some(2),
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
            .len()
            .checked_add(indices.len())?
            .checked_add(constructors.len())?
            .checked_add(usize::from(recursor.is_some())),
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            inductives.iter().try_fold(0_usize, |total, inductive| {
                total
                    .checked_add(inductive.params.len())?
                    .checked_add(inductive.indices.len())?
                    .checked_add(inductive.constructors.len())?
                    .checked_add(usize::from(inductive.recursor.is_some()))
            })
        }
    }
}

pub(crate) fn collect_export_entry_roots(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
) -> Result<Vec<TermId>> {
    let mut roots = Vec::new();
    match entry.kind {
        ExportKind::Axiom | ExportKind::Theorem => roots.push(entry.ty),
        ExportKind::Def => {
            roots.push(entry.ty);
            if entry.reducibility == Some(CertReducibility::Reducible) {
                roots.push(entry.body.ok_or(CertError::DecodeError)?);
            }
        }
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(CertError::DecodeError)?;
            collect_decl_payload_term_roots(&decl.decl, &mut roots);
        }
    }
    Ok(roots)
}

fn collect_certificate_import_projection_roots(
    module: &dyn CertificateImportView,
) -> Result<Vec<TermId>> {
    let mut roots = Vec::new();
    for decl in module.declarations() {
        match &decl.decl {
            DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } => {
                roots.extend(collect_export_entry_roots(
                    module,
                    export_entry_for_decl(module, *name, ExportKind::Axiom)?,
                )?);
            }
            DeclPayload::Def { name, .. } | DeclPayload::DefConstrained { name, .. } => {
                roots.extend(collect_export_entry_roots(
                    module,
                    export_entry_for_decl(module, *name, ExportKind::Def)?,
                )?);
            }
            DeclPayload::Theorem { name, .. } | DeclPayload::TheoremConstrained { name, .. } => {
                roots.extend(collect_export_entry_roots(
                    module,
                    export_entry_for_decl(module, *name, ExportKind::Theorem)?,
                )?);
            }
            DeclPayload::Inductive { .. }
            | DeclPayload::InductiveConstrained { .. }
            | DeclPayload::MutualInductiveBlock { .. } => {
                collect_decl_payload_term_roots(&decl.decl, &mut roots);
            }
        }
    }
    Ok(roots)
}

pub(crate) fn source_decl_index_for_name<C: KernelCertView + ?Sized>(
    cert: &C,
    name: NameId,
) -> Result<usize> {
    cert.declarations()
        .iter()
        .enumerate()
        .find_map(|(index, decl)| decl_payload_exports_name(&decl.decl, name).then_some(index))
        .ok_or(CertError::DecodeError)
}

fn decl_payload_exports_name(decl: &DeclPayload, name: NameId) -> bool {
    match decl {
        DeclPayload::Axiom {
            name: decl_name, ..
        }
        | DeclPayload::AxiomConstrained {
            name: decl_name, ..
        }
        | DeclPayload::Def {
            name: decl_name, ..
        }
        | DeclPayload::DefConstrained {
            name: decl_name, ..
        }
        | DeclPayload::Theorem {
            name: decl_name, ..
        }
        | DeclPayload::TheoremConstrained {
            name: decl_name, ..
        } => *decl_name == name,
        DeclPayload::Inductive {
            name: decl_name,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            name: decl_name,
            constructors,
            recursor,
            ..
        } => {
            *decl_name == name
                || constructors
                    .iter()
                    .any(|constructor| constructor.name == name)
                || recursor
                    .as_ref()
                    .is_some_and(|recursor| recursor.name == name)
        }
        DeclPayload::MutualInductiveBlock {
            name: block_name,
            inductives,
            ..
        } => {
            *block_name == name
                || inductives.iter().any(|inductive| {
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
    }
}

fn normalize_builtin_import_decl(decl: Decl) -> Decl {
    match decl {
        Decl::Inductive {
            name,
            universe_params,
            ty,
            mut data,
        } if name == BUILTIN_EQ => {
            data.recursor = None;
            Decl::Inductive {
                name,
                universe_params,
                ty,
                data,
            }
        }
        decl => decl,
    }
}

fn export_entry_for_decl<C: KernelCertView + ?Sized>(
    cert: &C,
    name: NameId,
    kind: ExportKind,
) -> Result<&ExportEntry> {
    cert.export_block()
        .iter()
        .find(|entry| entry.name == name && entry.kind == kind)
        .ok_or(CertError::DecodeError)
}

fn converted_term_root<C: KernelCertView + ?Sized>(
    terms: &KernelTermConversion<'_, C>,
    root: TermId,
    observation: &mut Option<&mut CertificateTermMaterializationObservation>,
) -> Result<Expr> {
    terms.root_expr(root, observation.as_deref_mut())
}

fn decl_payload_to_kernel_decl_with_terms<C: KernelCertView + ?Sized>(
    cert: &C,
    terms: &KernelTermConversion<'_, C>,
    decl: &DeclPayload,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<Decl> {
    Ok(match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => Decl::Axiom {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
        },
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => Decl::AxiomConstrained {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            universe_constraints: universe_constraints_from_specs(cert, universe_constraints)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
        },
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => Decl::Def {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
            value: converted_term_root(terms, *value, &mut observation)?,
            reducibility: (*reducibility).into(),
        },
        DeclPayload::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => Decl::DefConstrained {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            universe_constraints: universe_constraints_from_specs(cert, universe_constraints)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
            value: converted_term_root(terms, *value, &mut observation)?,
            reducibility: (*reducibility).into(),
        },
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => Decl::Theorem {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
            proof: converted_term_root(terms, *proof, &mut observation)?,
        },
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
            ..
        } => Decl::TheoremConstrained {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            universe_constraints: universe_constraints_from_specs(cert, universe_constraints)?,
            ty: converted_term_root(terms, *ty, &mut observation)?,
            proof: converted_term_root(terms, *proof, &mut observation)?,
        },
        DeclPayload::Inductive {
            name,
            universe_params,
            params,
            indices,
            sort,
            constructors,
            recursor,
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
            let name_str = name_to_string(cert, *name)?;
            let universe_names_vec = universe_names(cert, universe_params)?;
            let sort_level = level_from_node(cert, *sort)?;
            let is_eq = name_str == "Eq";
            let data_decl = InductiveDecl::new(
                name_str.clone(),
                universe_names_vec.clone(),
                params
                    .iter()
                    .enumerate()
                    .map(|(index, binder)| {
                        let binder_name = if is_eq {
                            match index {
                                0 => "A".to_owned(),
                                1 => "lhs".to_owned(),
                                _ => format!("p{index}"),
                            }
                        } else {
                            format!("p{index}")
                        };
                        Ok(Binder::new(
                            binder_name,
                            converted_term_root(terms, binder.ty, &mut observation)?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?,
                indices
                    .iter()
                    .enumerate()
                    .map(|(index, binder)| {
                        let binder_name = if is_eq {
                            match index {
                                0 => "rhs".to_owned(),
                                _ => format!("i{index}"),
                            }
                        } else {
                            format!("i{index}")
                        };
                        Ok(Binder::new(
                            binder_name,
                            converted_term_root(terms, binder.ty, &mut observation)?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?,
                sort_level,
                constructors
                    .iter()
                    .map(|constructor| {
                        let constr_name = name_to_string(cert, constructor.name)?;
                        let mut constr_ty =
                            converted_term_root(terms, constructor.ty, &mut observation)?;
                        if is_eq && constr_name == "Eq.refl" {
                            if let Expr::Pi {
                                binder: ref mut b1,
                                body: ref mut body1,
                                ..
                            } = constr_ty
                            {
                                *b1 = "A".to_owned();
                                if let Expr::Pi {
                                    binder: ref mut b2, ..
                                } = std::sync::Arc::make_mut(body1)
                                {
                                    *b2 = "x".to_owned();
                                }
                            }
                        }
                        Ok(ConstructorDecl::new(constr_name, constr_ty))
                    })
                    .collect::<Result<Vec<_>>>()?,
                recursor
                    .as_ref()
                    .map(|recursor| {
                        Ok::<_, CertError>(RecursorDecl::with_rules(
                            name_to_string(cert, recursor.name)?,
                            universe_names(cert, &recursor.universe_params)?,
                            converted_term_root(terms, recursor.ty, &mut observation)?,
                            RecursorRules::new(
                                recursor.rules.minor_start,
                                recursor.rules.major_index,
                            ),
                        ))
                    })
                    .transpose()?,
            )
            .with_universe_constraints(universe_constraints_from_decl_payload(cert, decl)?);

            let ty = crate::inductive::inductive_type(&data_decl);

            Decl::Inductive {
                name: name_str,
                universe_params: universe_names_vec,
                ty,
                data: Box::new(data_decl),
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => Decl::MutualInductiveBlock {
            name: name_to_string(cert, *name)?,
            universe_params: universe_names(cert, universe_params)?,
            data: Box::new(
                MutualInductiveBlock::new(
                    name_to_string(cert, *name)?,
                    universe_names(cert, universe_params)?,
                    inductives
                        .iter()
                        .map(|inductive| {
                            Ok(InductiveDecl::new(
                                name_to_string(cert, inductive.name)?,
                                universe_names(cert, universe_params)?,
                                inductive
                                    .params
                                    .iter()
                                    .enumerate()
                                    .map(|(index, binder)| {
                                        Ok(Binder::new(
                                            format!("p{index}"),
                                            converted_term_root(
                                                terms,
                                                binder.ty,
                                                &mut observation,
                                            )?,
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
                                            converted_term_root(
                                                terms,
                                                binder.ty,
                                                &mut observation,
                                            )?,
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
                                            converted_term_root(
                                                terms,
                                                constructor.ty,
                                                &mut observation,
                                            )?,
                                        ))
                                    })
                                    .collect::<Result<Vec<_>>>()?,
                                inductive
                                    .recursor
                                    .as_ref()
                                    .map(|recursor| {
                                        Ok::<_, CertError>(RecursorDecl::with_rules(
                                            name_to_string(cert, recursor.name)?,
                                            universe_names(cert, &recursor.universe_params)?,
                                            converted_term_root(
                                                terms,
                                                recursor.ty,
                                                &mut observation,
                                            )?,
                                            RecursorRules::new(
                                                recursor.rules.minor_start,
                                                recursor.rules.major_index,
                                            ),
                                        ))
                                    })
                                    .transpose()?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                )
                .with_universe_constraints(universe_constraints_from_specs(
                    cert,
                    universe_constraints,
                )?),
            ),
        },
    })
}

fn universe_constraints_from_decl_payload<C: KernelCertView + ?Sized>(
    cert: &C,
    decl: &DeclPayload,
) -> Result<Vec<UniverseConstraint>> {
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
        } => universe_constraints_from_specs(cert, universe_constraints),
        DeclPayload::Axiom { .. }
        | DeclPayload::Def { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::Inductive { .. } => Ok(Vec::new()),
    }
}

pub(crate) fn universe_constraints_from_specs<C: KernelCertView + ?Sized>(
    cert: &C,
    constraints: &[UniverseConstraintSpec],
) -> Result<Vec<UniverseConstraint>> {
    constraints
        .iter()
        .map(|constraint| {
            Ok(UniverseConstraint {
                lhs: level_from_node(cert, constraint.lhs)?,
                relation: constraint.relation,
                rhs: level_from_node(cert, constraint.rhs)?,
            })
        })
        .collect()
}

pub(crate) fn expr_from_term<C: KernelCertView + ?Sized>(cert: &C, term: TermId) -> Result<Expr> {
    Ok(
        match cert.term_table().get(term).ok_or(CertError::DecodeError)? {
            TermNode::Sort(level) => Expr::sort(level_from_node(cert, *level)?),
            TermNode::BVar(index) => Expr::bvar(*index),
            TermNode::Const { global_ref, levels } => Expr::konst(
                global_ref_name(cert, global_ref)?,
                levels
                    .iter()
                    .map(|level| level_from_node(cert, *level))
                    .collect::<Result<Vec<_>>>()?,
            ),
            TermNode::App(fun, arg) => {
                Expr::app(expr_from_term(cert, *fun)?, expr_from_term(cert, *arg)?)
            }
            TermNode::Lam { ty, body } => Expr::lam(
                "_",
                expr_from_term(cert, *ty)?,
                expr_from_term(cert, *body)?,
            ),
            TermNode::Pi { ty, body } => Expr::pi(
                "_",
                expr_from_term(cert, *ty)?,
                expr_from_term(cert, *body)?,
            ),
        },
    )
}

pub(crate) fn level_from_node<C: KernelCertView + ?Sized>(
    cert: &C,
    level: LevelId,
) -> Result<Level> {
    Ok(
        match cert
            .level_table()
            .get(level)
            .ok_or(CertError::DecodeError)?
        {
            LevelNode::Zero => Level::zero(),
            LevelNode::Succ(inner) => Level::succ(level_from_node(cert, *inner)?),
            LevelNode::Max(lhs, rhs) => {
                Level::max(level_from_node(cert, *lhs)?, level_from_node(cert, *rhs)?)
            }
            LevelNode::IMax(lhs, rhs) => {
                Level::imax(level_from_node(cert, *lhs)?, level_from_node(cert, *rhs)?)
            }
            LevelNode::Param(name) => Level::param(name_to_string(cert, *name)?),
        },
    )
}

fn global_ref_name<C: KernelCertView + ?Sized>(cert: &C, global_ref: &GlobalRef) -> Result<String> {
    match global_ref {
        GlobalRef::Builtin { name, .. } => name_to_string(cert, *name),
        GlobalRef::Imported { name, .. } => name_to_string(cert, *name),
        GlobalRef::Local { decl_index } => decl_name(cert, *decl_index),
        GlobalRef::LocalGenerated { name, .. } => name_to_string(cert, *name),
    }
}

fn decl_name<C: KernelCertView + ?Sized>(cert: &C, decl_index: usize) -> Result<String> {
    let decl = cert
        .declarations()
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
    name_to_string(cert, name)
}

pub(crate) fn name_to_string<C: KernelCertView + ?Sized>(cert: &C, name: NameId) -> Result<String> {
    Ok(cert
        .name_table()
        .get(name)
        .ok_or(CertError::DecodeError)?
        .as_dotted())
}

pub(crate) fn universe_names<C: KernelCertView + ?Sized>(
    cert: &C,
    names: &[NameId],
) -> Result<Vec<String>> {
    names
        .iter()
        .map(|name| name_to_string(cert, *name))
        .collect()
}

pub(crate) fn add_decl_to_env(env: &mut Env, decl: Decl) -> Result<()> {
    match decl {
        Decl::Axiom {
            name,
            universe_params,
            ty,
        } => env.add_axiom(name, universe_params, ty)?,
        Decl::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => env.add_axiom_with_universe_constraints(
            name,
            universe_params,
            universe_constraints,
            ty,
        )?,
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => env.add_def(name, universe_params, ty, value, reducibility)?,
        Decl::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => env.add_def_with_universe_constraints(
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        )?,
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        } => env.add_theorem(name, universe_params, ty, proof)?,
        Decl::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
        } => env.add_theorem_with_universe_constraints(
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
        )?,
        Decl::Inductive { data, .. } => {
            let name = Name::from_dotted(&data.name);
            match env.add_inductive(*data) {
                Ok(()) => {}
                Err(Error::InvalidInductive(message)) if message.contains("recursor") => {
                    return Err(CertError::InductiveGeneratedArtifactMismatch { name });
                }
                Err(err) => return Err(CertError::Kernel(err)),
            }
        }
        Decl::MutualInductiveBlock { data, .. } => {
            let name = Name::from_dotted(&data.name);
            match env.add_mutual_inductive(*data) {
                Ok(()) => {}
                Err(Error::InvalidInductive(message)) if message.contains("recursor") => {
                    return Err(CertError::InductiveGeneratedArtifactMismatch { name });
                }
                Err(err) => return Err(CertError::Kernel(err)),
            }
        }
        Decl::Constructor { .. } | Decl::Recursor { .. } => {
            return Err(CertError::UnknownDependency {
                name: Name::from_dotted(decl.name()),
            });
        }
    }
    Ok(())
}

/// Check a current-module declaration with its declared reducibility, then
/// expose an opaque body only in the environment used by later local
/// declarations.
///
/// The source/certificate `Decl` is never rewritten. Every non-opaque
/// declaration retains the ordinary kernel view.
pub(crate) fn add_current_module_decl_to_env(
    env: &mut Env,
    decl: Decl,
    _version: CertificateFormatVersion,
) -> Result<()> {
    let local_opaque_name = match &decl {
        Decl::Def {
            name,
            reducibility: Reducibility::Opaque,
            ..
        }
        | Decl::DefConstrained {
            name,
            reducibility: Reducibility::Opaque,
            ..
        } => Some(name.clone()),
        _ => None,
    };

    add_decl_to_env(env, decl)?;
    if let Some(name) = local_opaque_name {
        if !env.expose_checked_opaque_definition(&name) {
            return Err(CertError::DecodeError);
        }
    }
    Ok(())
}

/// Return the canonical interface hash for a declaration supplied by the builtin checker profile.
pub fn builtin_decl_interface_hash(name: &Name) -> Option<Hash> {
    let tag = match name.as_dotted().as_str() {
        BUILTIN_NAT => "npa.machine-tactic.builtin.nat.v1",
        BUILTIN_NAT_ZERO => "npa.machine-tactic.builtin.nat.zero.v1",
        BUILTIN_NAT_SUCC => "npa.machine-tactic.builtin.nat.succ.v1",
        BUILTIN_NAT_REC => "npa.machine-tactic.builtin.nat.rec.v1",
        BUILTIN_EQ => "npa.machine-tactic.builtin.eq.v1",
        BUILTIN_EQ_REFL => "npa.machine-tactic.builtin.eq.refl.v1",
        BUILTIN_EQ_REC => "npa.machine-tactic.builtin.eq.rec.v1",
        _ => return None,
    };
    Some(hash_with_domain(
        b"NPA-BUILTIN-INTERFACE-0.1",
        tag.as_bytes(),
    ))
}

pub(crate) fn builtin_is_axiom(name: &Name) -> bool {
    name.as_dotted() == BUILTIN_EQ_REC
}

pub(crate) fn reserved_core_primitive_name(name: &Name) -> bool {
    let _ = name;
    false
}

pub(crate) fn core_features_from_builtins(referenced: &BTreeSet<Name>) -> Vec<CoreFeature> {
    let _ = referenced;
    Vec::new()
}

pub(crate) fn add_referenced_builtins_to_env(
    env: &mut Env,
    referenced: &BTreeSet<Name>,
) -> Result<()> {
    let needs_nat = referenced.iter().any(|name| {
        matches!(
            name.as_dotted().as_str(),
            BUILTIN_NAT | BUILTIN_NAT_ZERO | BUILTIN_NAT_SUCC | BUILTIN_NAT_REC
        )
    });
    let needs_eq = referenced.iter().any(|name| {
        matches!(
            name.as_dotted().as_str(),
            BUILTIN_EQ | BUILTIN_EQ_REFL | BUILTIN_EQ_REC
        )
    });
    let needs_eq_rec = referenced
        .iter()
        .any(|name| name.as_dotted() == BUILTIN_EQ_REC);

    if needs_nat && env.decl(BUILTIN_NAT).is_none() {
        env.add_inductive(nat_inductive())?;
    }
    if needs_eq && env.decl(BUILTIN_EQ).is_none() {
        env.add_inductive(eq_inductive())?;
    }
    if needs_eq_rec && env.decl(BUILTIN_EQ_REC).is_none() {
        env.add_axiom(
            BUILTIN_EQ_REC,
            vec!["u".to_owned(), "v".to_owned()],
            eq_rec_type(Level::param("u"), Level::param("v")),
        )?;
    }
    Ok(())
}

pub(crate) fn certificate_import_referenced_builtin_names(
    module: &dyn CertificateImportView,
) -> Result<BTreeSet<Name>> {
    let mut names = BTreeSet::new();
    for term in module.term_table() {
        if let TermNode::Const {
            global_ref:
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                },
            ..
        } = term
        {
            let name_value = module
                .name_table()
                .get(*name)
                .ok_or(CertError::DecodeError)?;
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

#[cfg(test)]
mod term_materialization_tests {
    use super::*;

    struct TestView {
        terms: Vec<TermNode>,
    }

    impl KernelCertView for TestView {
        fn name_table(&self) -> &[Name] {
            &[]
        }

        fn level_table(&self) -> &[LevelNode] {
            &[]
        }

        fn term_table(&self) -> &[TermNode] {
            &self.terms
        }

        fn declarations(&self) -> &[DeclCert] {
            &[]
        }

        fn export_block(&self) -> &[ExportEntry] {
            &[]
        }
    }

    fn sharing_view() -> TestView {
        TestView {
            terms: vec![
                TermNode::BVar(0),
                TermNode::App(0, 0),
                TermNode::App(1, 1),
                TermNode::BVar(99),
            ],
        }
    }

    #[test]
    fn term_materialization_reuses_child_arcs_and_selected_closure() {
        let view = sharing_view();
        let mut budget = TermMaterializationBudgetV1::new();
        let mut observation = CertificateTermMaterializationObservation::default();
        let MaterializationAttempt::Ready(table) = KernelExprMaterialization::for_selected_roots(
            &view,
            &[2, 2],
            &mut budget,
            Some(&mut observation),
        ) else {
            panic!("the small selected closure must materialize");
        };

        assert_eq!(table.selected_node_count(), 3);
        assert!(table.node_arc(3).is_none());
        let node0 = table.node_arc(0).unwrap();
        let node1 = table.node_arc(1).unwrap();
        let node2 = table.node_arc(2).unwrap();
        let Expr::App(node1_lhs, node1_rhs) = node1.as_ref() else {
            panic!("term 1 must be an application");
        };
        assert!(Arc::ptr_eq(node1_lhs, node0));
        assert!(Arc::ptr_eq(node1_rhs, node0));
        let Expr::App(node2_lhs, node2_rhs) = node2.as_ref() else {
            panic!("term 2 must be an application");
        };
        assert!(Arc::ptr_eq(node2_lhs, node1));
        assert!(Arc::ptr_eq(node2_rhs, node1));

        let first = table.root_expr(2, Some(&mut observation)).unwrap();
        let second = table.root_expr(2, Some(&mut observation)).unwrap();
        assert_eq!(first, second);
        assert_eq!(observation.unique_nodes_materialized, 3);
        assert_eq!(observation.selected_edges, 4);
        assert_eq!(observation.reused_child_arcs, 4);
        assert_eq!(observation.materialization_slots, 4);
        assert_eq!(observation.root_requests, 2);
        assert_eq!(observation.compound_root_clones, 2);
        assert_eq!(observation.leaf_root_clones, 0);
        assert!(observation.materialization_charged_bytes > 0);
        assert_eq!(
            budget.admitted_bytes(),
            observation.materialization_charged_bytes
        );
    }

    #[test]
    fn term_materialization_capacity_stop_selects_one_legacy_fallback() {
        let view = sharing_view();
        let mut budget = TermMaterializationBudgetV1 {
            admitted_bytes: TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT,
        };
        let mut observation = CertificateTermMaterializationObservation::default();
        let attempt = KernelExprMaterialization::for_selected_roots(
            &view,
            &[2],
            &mut budget,
            Some(&mut observation),
        );
        let conversion = KernelTermConversion::from_attempt(&view, attempt, Some(&mut observation));

        assert!(conversion.materialized().is_none());
        assert_eq!(observation.materialization_capacity_stops, 1);
        assert_eq!(observation.materialization_legacy_fallbacks, 1);
        assert_eq!(observation.materialization_charged_bytes, 0);
        assert_eq!(
            budget.admitted_bytes(),
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
        );
        assert_eq!(
            conversion.root_expr(2, Some(&mut observation)).unwrap(),
            expr_from_term(&view, 2).unwrap()
        );
        assert_eq!(observation.root_requests, 0);
    }

    fn term_materialization_observation_merges_and_saturates() {
        fn filled(value: u64, overflowed: bool) -> CertificateTermMaterializationObservation {
            CertificateTermMaterializationObservation {
                root_requests: value,
                unique_nodes_materialized: value,
                selected_edges: value,
                reused_child_arcs: value,
                owned_root_handoffs: value,
                leaf_root_clones: value,
                compound_root_clones: value,
                materialization_slots: value,
                materialization_charged_bytes: value,
                materialization_capacity_stops: value,
                materialization_legacy_fallbacks: value,
                overflowed,
            }
        }

        let zero = CertificateTermMaterializationObservation::default();
        let ordinary = filled(7, false);
        let increment = filled(11, false);
        let expected = filled(18, false);

        let mut forward = ordinary;
        forward.merge(increment);
        let mut reverse = increment;
        reverse.merge(ordinary);
        assert_eq!(forward, expected);
        assert_eq!(reverse, expected, "merge must be exactly commutative");

        let mut left_identity = zero;
        left_identity.merge(ordinary);
        let mut right_identity = ordinary;
        right_identity.merge(zero);
        assert_eq!(left_identity, ordinary);
        assert_eq!(right_identity, ordinary);

        let mut maximum = filled(u64::MAX, false);
        maximum.merge(filled(0, false));
        assert_eq!(maximum, filled(u64::MAX, false));

        maximum.merge(filled(1, false));
        assert_eq!(maximum, filled(u64::MAX, true));

        let mut propagated = zero;
        propagated.merge(filled(0, true));
        assert_eq!(propagated, filled(0, true));
    }

    #[test]
    fn term_materialization_observation_saturates() {
        term_materialization_observation_merges_and_saturates();
    }

    #[test]
    fn term_materialization_observation_merges() {
        term_materialization_observation_merges_and_saturates();
    }

    #[test]
    fn imported_materialization_sorted_selected_indices() {
        // The reviewed sparse decision is AcceptedForwardScan, so the
        // conditional sorted-index implementation is not active. Preserve an
        // executable oracle for the required deterministic order: a sparse
        // closure is marked from unsorted duplicate roots, then the production
        // forward scan materializes exactly the increasing selected ids.
        let view = TestView {
            terms: vec![
                TermNode::BVar(0),
                TermNode::App(0, 0),
                TermNode::BVar(1),
                TermNode::App(1, 1),
                TermNode::BVar(2),
                TermNode::App(3, 3),
            ],
        };
        let mut budget = TermMaterializationBudgetV1::new();
        let mut observation = CertificateTermMaterializationObservation::default();
        let MaterializationAttempt::Ready(table) = KernelExprMaterialization::for_selected_roots(
            &view,
            &[5, 1, 5],
            &mut budget,
            Some(&mut observation),
        ) else {
            panic!("sparse selected closure must materialize");
        };
        let selected = (0..view.terms.len())
            .filter(|index| table.node_arc(*index).is_some())
            .collect::<Vec<_>>();
        assert_eq!(selected, vec![0, 1, 3, 5]);
        assert_eq!(observation.unique_nodes_materialized, 4);
        assert_eq!(observation.materialization_slots, 6);
    }

    #[test]
    fn term_materialization_repeated_edge_ptr_eq() {
        term_materialization_reuses_child_arcs_and_selected_closure();
    }

    #[test]
    fn term_materialization_doubling_dag_counts() {
        let mut terms = vec![TermNode::BVar(0)];
        for child in 0..8 {
            terms.push(TermNode::App(child, child));
        }
        let view = TestView { terms };
        let mut budget = TermMaterializationBudgetV1::new();
        let mut observation = CertificateTermMaterializationObservation::default();
        let MaterializationAttempt::Ready(table) = KernelExprMaterialization::for_selected_roots(
            &view,
            &[8],
            &mut budget,
            Some(&mut observation),
        ) else {
            panic!("bounded doubling DAG must materialize");
        };
        assert_eq!(table.selected_node_count(), 9);
        assert_eq!(observation.unique_nodes_materialized, 9);
        assert_eq!(observation.selected_edges, 16);
        assert_eq!(observation.reused_child_arcs, 16);
        for parent in 1..=8 {
            let Expr::App(lhs, rhs) = table.node_arc(parent).unwrap().as_ref() else {
                panic!("doubling node must be an application");
            };
            assert!(Arc::ptr_eq(lhs, table.node_arc(parent - 1).unwrap()));
            assert!(Arc::ptr_eq(rhs, table.node_arc(parent - 1).unwrap()));
        }
    }

    #[test]
    fn term_materialization_repeated_root_ownership() {
        let view = sharing_view();
        let mut budget = TermMaterializationBudgetV1::new();
        let mut observation = CertificateTermMaterializationObservation::default();
        let MaterializationAttempt::Ready(table) = KernelExprMaterialization::for_selected_roots(
            &view,
            &[2, 2],
            &mut budget,
            Some(&mut observation),
        ) else {
            panic!("repeated root fixture must materialize");
        };
        let first = table.root_expr(2, Some(&mut observation)).unwrap();
        let second = table.root_expr(2, Some(&mut observation)).unwrap();
        let (Expr::App(first_lhs, _), Expr::App(second_lhs, _)) = (&first, &second) else {
            panic!("fixture root must be an application");
        };
        assert!(!std::ptr::eq(&first, &second));
        assert!(Arc::ptr_eq(first_lhs, second_lhs));
        assert_eq!(observation.compound_root_clones, 2);
    }

    #[test]
    fn term_materialization_eq_cow_isolation() {
        let view = TestView {
            terms: vec![
                TermNode::BVar(0),
                TermNode::Pi { ty: 0, body: 0 },
                TermNode::Pi { ty: 0, body: 1 },
            ],
        };
        let mut budget = TermMaterializationBudgetV1::new();
        let MaterializationAttempt::Ready(table) =
            KernelExprMaterialization::for_selected_roots(&view, &[2], &mut budget, None)
        else {
            panic!("Eq-shaped fixture must materialize");
        };
        let mut returned = table.root_expr(2, None).unwrap();
        let Expr::Pi { binder, body, .. } = &mut returned else {
            panic!("outer root must be Pi");
        };
        *binder = "A".to_owned();
        let Expr::Pi {
            binder: inner_binder,
            ..
        } = Arc::make_mut(body)
        else {
            panic!("inner body must be Pi");
        };
        *inner_binder = "x".to_owned();

        let stored = table.root_expr(2, None).unwrap();
        let Expr::Pi { binder, body, .. } = stored else {
            panic!("stored root must be Pi");
        };
        assert_eq!(binder, "_");
        let Expr::Pi { binder, .. } = body.as_ref() else {
            panic!("stored inner body must be Pi");
        };
        assert_eq!(binder, "_");
    }

    #[test]
    fn term_materialization_table_drop_lifetime() {
        let view = sharing_view();
        let owned = {
            let mut budget = TermMaterializationBudgetV1::new();
            let MaterializationAttempt::Ready(table) =
                KernelExprMaterialization::for_selected_roots(&view, &[2], &mut budget, None)
            else {
                panic!("lifetime fixture must materialize");
            };
            table.root_expr(2, None).unwrap()
        };
        assert_eq!(owned, expr_from_term(&view, 2).unwrap());
        let Expr::App(lhs, rhs) = owned else {
            panic!("owned root must remain usable after table drop");
        };
        assert!(Arc::ptr_eq(&lhs, &rhs));
    }

    #[test]
    fn term_materialization_variant_and_stop_matrix() {
        term_materialization_reuses_child_arcs_and_selected_closure();
        term_materialization_capacity_stop_selects_one_legacy_fallback();
        let view = sharing_view();
        let mut budget = TermMaterializationBudgetV1::new();
        assert!(matches!(
            KernelExprMaterialization::for_selected_roots(&view, &[usize::MAX], &mut budget, None),
            MaterializationAttempt::Fallback(MaterializationStop::SpeculativeInvariant)
        ));
        assert_eq!(budget.admitted_bytes(), 0);
    }

    #[test]
    fn term_materialization_structural_ceiling_charge() {
        let view = sharing_view();
        let selection = [1, 1, 1, 0];
        let charge = complete_materialization_charge(&view, &selection, &[2], 1, 4).unwrap();
        let exact_metadata = 4 * TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1
            + 4 * TERM_SELECTION_SLOT_CHARGE_BYTES_V1
            + TERM_ID_SLOT_CHARGE_BYTES_V1
            + 4 * TERM_ID_SLOT_CHARGE_BYTES_V1;
        let exact_nodes =
            3 * (TERM_EXPR_INLINE_CHARGE_BYTES_V1 + TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1);
        let exact_root = TERM_EXPR_INLINE_CHARGE_BYTES_V1;
        assert_eq!(charge, exact_metadata + exact_nodes + exact_root);
        assert!(charge <= TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT);

        const STRUCTURAL_TERM_CEILING: u64 = 4_194_304;
        let ceiling_charge = STRUCTURAL_TERM_CEILING
            .checked_mul(
                TERM_OPTION_ARC_SLOT_CHARGE_BYTES_V1
                    + TERM_SELECTION_SLOT_CHARGE_BYTES_V1
                    + TERM_ID_SLOT_CHARGE_BYTES_V1
                    + TERM_EXPR_INLINE_CHARGE_BYTES_V1
                    + TERM_ARC_NODE_METADATA_CHARGE_BYTES_V1,
            )
            .unwrap()
            .checked_add(
                STRUCTURAL_TERM_CEILING
                    .checked_mul(TERM_LEVEL_NODE_CHARGE_BYTES_V1)
                    .unwrap(),
            )
            .unwrap()
            .checked_add(
                STRUCTURAL_TERM_CEILING
                    .checked_mul(TERM_PLANNER_RECORD_CHARGE_BYTES_V1)
                    .unwrap(),
            )
            .unwrap()
            .checked_add(
                STRUCTURAL_TERM_CEILING
                    .checked_mul(TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1)
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(
            ceiling_charge,
            STRUCTURAL_TERM_CEILING * (8 + 1 + 8 + 64 + 64 + 64 + 256 + 32)
        );
        assert!(ceiling_charge > TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT);

        let exact_prefix = TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - charge;
        let mut exact_budget =
            TermMaterializationBudgetV1::with_admitted_bytes_for_test(exact_prefix);
        let mut exact_observation = CertificateTermMaterializationObservation::default();
        assert!(matches!(
            KernelExprMaterialization::for_selected_roots(
                &view,
                &[2],
                &mut exact_budget,
                Some(&mut exact_observation),
            ),
            MaterializationAttempt::Ready(_)
        ));
        assert_eq!(
            exact_budget.admitted_bytes(),
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
        );
        assert_eq!(exact_observation.materialization_charged_bytes, charge);

        let mut one_over_budget =
            TermMaterializationBudgetV1::with_admitted_bytes_for_test(exact_prefix + 1);
        let mut one_over_observation = CertificateTermMaterializationObservation::default();
        let attempt = KernelExprMaterialization::for_selected_roots(
            &view,
            &[2],
            &mut one_over_budget,
            Some(&mut one_over_observation),
        );
        let conversion =
            KernelTermConversion::from_attempt(&view, attempt, Some(&mut one_over_observation));
        assert!(conversion.materialized().is_none());
        assert_eq!(one_over_budget.admitted_bytes(), exact_prefix + 1);
        assert_eq!(one_over_observation.materialization_capacity_stops, 1);
        assert_eq!(one_over_observation.materialization_legacy_fallbacks, 1);
        assert_eq!(one_over_observation.materialization_charged_bytes, 0);
    }

    #[test]
    fn current_term_materialization_budget_boundaries() {
        let view = sharing_view();
        let roots = [2];
        let charge = complete_dense_materialization_charge(&view, &roots).unwrap();
        let exact_prefix = TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - charge;
        let mut admitted = TermMaterializationBudgetV1::with_admitted_bytes_for_test(exact_prefix);
        assert!(matches!(
            KernelExprMaterialization::for_current_module(&view, &roots, &mut admitted, None),
            MaterializationAttempt::Ready(_)
        ));
        assert_eq!(
            admitted.admitted_bytes(),
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
        );

        let mut exhausted =
            TermMaterializationBudgetV1::with_admitted_bytes_for_test(exact_prefix + 1);
        let mut observation = CertificateTermMaterializationObservation::default();
        let attempt = KernelExprMaterialization::for_current_module(
            &view,
            &roots,
            &mut exhausted,
            Some(&mut observation),
        );
        let conversion = KernelTermConversion::from_attempt(&view, attempt, Some(&mut observation));
        assert!(conversion.materialized().is_none());
        assert_eq!(exhausted.admitted_bytes(), exact_prefix + 1);
        assert_eq!(observation.materialization_capacity_stops, 1);
        assert_eq!(observation.materialization_legacy_fallbacks, 1);
        assert_eq!(observation.materialization_charged_bytes, 0);

        for reserve_stop in [
            CurrentMaterializationReserveStop::Selection,
            CurrentMaterializationReserveStop::Nodes,
        ] {
            let mut budget = TermMaterializationBudgetV1::new();
            let mut observation = CertificateTermMaterializationObservation::default();
            let attempt = KernelExprMaterialization::for_current_module_with_injected_reserve_stop(
                &view,
                &roots,
                &mut budget,
                Some(&mut observation),
                reserve_stop,
            );
            let conversion =
                KernelTermConversion::from_attempt(&view, attempt, Some(&mut observation));
            assert!(
                conversion.materialized().is_none(),
                "reserve stop: {reserve_stop:?}"
            );
            assert_eq!(budget.admitted_bytes(), 0);
            assert_eq!(observation.materialization_capacity_stops, 1);
            assert_eq!(observation.materialization_legacy_fallbacks, 1);
            assert_eq!(observation.materialization_charged_bytes, 0);
        }

        let mut saturated = TermMaterializationBudgetV1 {
            admitted_bytes: u64::MAX,
        };
        let mut saturated_observation = CertificateTermMaterializationObservation::default();
        let attempt = KernelExprMaterialization::for_current_module(
            &view,
            &roots,
            &mut saturated,
            Some(&mut saturated_observation),
        );
        let conversion =
            KernelTermConversion::from_attempt(&view, attempt, Some(&mut saturated_observation));
        assert!(conversion.materialized().is_none());
        assert_eq!(saturated.admitted_bytes(), u64::MAX);
        assert_eq!(saturated_observation.materialization_capacity_stops, 1);
        assert_eq!(saturated_observation.materialization_legacy_fallbacks, 1);
        assert!(saturated_observation.overflowed);
    }

    #[test]
    fn term_materialization_release_harness_admission_boundary() {
        let below = benchmark_term_materialization_admission_v1(
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - 1,
        );
        assert_eq!(
            below.materialization_charged_bytes,
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - 1
        );
        assert_eq!(below.materialization_capacity_stops, 0);
        assert_eq!(below.materialization_legacy_fallbacks, 0);

        let exact =
            benchmark_term_materialization_admission_v1(TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT);
        assert_eq!(
            exact.materialization_charged_bytes,
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
        );
        assert_eq!(exact.materialization_capacity_stops, 0);
        assert_eq!(exact.materialization_legacy_fallbacks, 0);

        let above = benchmark_term_materialization_admission_v1(
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT + 1,
        );
        assert_eq!(above.materialization_charged_bytes, 0);
        assert_eq!(above.materialization_capacity_stops, 1);
        assert_eq!(above.materialization_legacy_fallbacks, 1);
    }
}

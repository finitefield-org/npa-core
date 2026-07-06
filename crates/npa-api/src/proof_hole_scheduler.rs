use crate::proof_skeleton::{
    proof_skeleton_hash, proof_skeleton_hole_hash, ProofSkeleton, ProofSkeletonBudget,
    ProofSkeletonHole, ProofSkeletonPreferredNodeKind, ProofSkeletonPremiseIdentity,
    ProofSkeletonPremiseSource, ProofSkeletonStrategyProfile, ProofSkeletonStrategyProfileId,
};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const PROOF_HOLE_RESULT_SHARING_KEY_HASH_DOMAIN: &str = "npa.proof-hole.result-sharing-key.v1";
pub const PROOF_HOLE_EXPECTED_OUTPUT_HASH_DOMAIN: &str = "npa.proof-hole.expected-output.v1";
pub const PROOF_HOLE_WORK_PLAN_HASH_DOMAIN: &str = "npa.proof-hole.work-plan.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleSchedulerInput {
    pub base_sketch_hash: Hash,
    pub hole_statuses: BTreeMap<String, ProofHoleStatus>,
}

impl ProofHoleSchedulerInput {
    pub fn new(base_sketch_hash: Hash) -> Self {
        Self {
            base_sketch_hash,
            hole_statuses: BTreeMap::new(),
        }
    }

    pub fn with_hole_status(mut self, hole_id: impl Into<String>, status: ProofHoleStatus) -> Self {
        self.hole_statuses.insert(hole_id.into(), status);
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofHoleStatus {
    Unresolved,
    Resolved { output_hash: Hash },
    Rejected { rejection_hash: Hash },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleWorkPlan {
    pub base_sketch_hash: Hash,
    pub skeleton_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub ready_batches: Vec<ProofHoleWorkBatch>,
    pub blocked_holes: Vec<ProofHoleBlocked>,
    pub resolved_hole_ids: Vec<String>,
    pub rejected_hole_ids: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleWorkBatch {
    pub batch_index: u64,
    pub items: Vec<ProofHoleWorkItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleWorkItem {
    pub hole_id: String,
    pub dependency_hole_ids: Vec<String>,
    pub context_hash: Hash,
    pub target_hash: Hash,
    pub allowed_premise_identities: Vec<ProofSkeletonPremiseIdentity>,
    pub strategy_profile: ProofSkeletonStrategyProfile,
    pub budget: ProofSkeletonBudget,
    pub expected_output_identity: ProofHoleExpectedOutputIdentity,
    pub result_sharing_key: ProofHoleResultSharingKey,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleExpectedOutputIdentity {
    pub hole_id: String,
    pub base_sketch_hash: Hash,
    pub skeleton_hash: Hash,
    pub hole_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub context_hash: Hash,
    pub target_hash: Hash,
    pub result_sharing_key_hash: Hash,
    pub expected_output_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleResultSharingKey {
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub context_hash: Hash,
    pub target_hash: Hash,
    pub allowed_premise_identities: Vec<ProofSkeletonPremiseIdentity>,
    pub result_sharing_key_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleBlocked {
    pub hole_id: String,
    pub reason: ProofHoleBlockedReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofHoleBlockedReason {
    DependencyUnresolved { dependency_hole_id: String },
    DependencyRejected { dependency_hole_id: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleSubmittedSolutionIdentity {
    pub hole_id: String,
    pub base_sketch_hash: Hash,
    pub environment_hash: Hash,
    pub context_hash: Hash,
    pub target_hash: Hash,
    pub policy_hash: Hash,
    pub expected_output_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleSolutionRebaseReport {
    pub hole_id: String,
    pub status: ProofHoleSolutionRebaseStatus,
    pub reasons: Vec<ProofHoleSolutionRebaseReason>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofHoleSolutionRebaseStatus {
    Current,
    RebaseRequired,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofHoleSolutionRebaseReason {
    HoleId,
    BaseSketchHash,
    EnvironmentHash,
    ContextHash,
    TargetHash,
    PolicyHash,
    ExpectedOutputHash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofHoleSchedulerError {
    kind: ProofHoleSchedulerErrorKind,
}

impl ProofHoleSchedulerError {
    fn new(kind: ProofHoleSchedulerErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ProofHoleSchedulerErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofHoleSchedulerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofHoleSchedulerError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofHoleSchedulerErrorKind {
    DuplicateHoleId {
        hole_id: String,
    },
    UnknownDependency {
        hole_id: String,
        dependency_hole_id: String,
    },
    DependencyCycle {
        hole_id: String,
    },
    UnknownStatusHole {
        hole_id: String,
    },
    StaleSolution {
        hole_id: String,
        reasons: Vec<ProofHoleSolutionRebaseReason>,
    },
}

impl fmt::Display for ProofHoleSchedulerErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateHoleId { hole_id } => write!(f, "duplicate hole id `{hole_id}`"),
            Self::UnknownDependency {
                hole_id,
                dependency_hole_id,
            } => write!(
                f,
                "hole `{hole_id}` depends on unknown hole `{dependency_hole_id}`"
            ),
            Self::DependencyCycle { hole_id } => {
                write!(f, "hole dependency cycle reaches `{hole_id}`")
            }
            Self::UnknownStatusHole { hole_id } => {
                write!(f, "status was supplied for unknown hole `{hole_id}`")
            }
            Self::StaleSolution { hole_id, reasons } => {
                write!(f, "stale solution for `{hole_id}`: {reasons:?}")
            }
        }
    }
}

pub fn proof_hole_work_plan(
    skeleton: &ProofSkeleton,
    input: &ProofHoleSchedulerInput,
) -> Result<ProofHoleWorkPlan, ProofHoleSchedulerError> {
    let hole_by_id = validated_hole_map(skeleton)?;
    validate_status_holes(input, &hole_by_id)?;
    validate_dependencies(&hole_by_id)?;
    validate_acyclic_dependencies(&hole_by_id)?;

    let skeleton_hash = proof_skeleton_hash(skeleton);
    let mut ready_items = Vec::new();
    let mut blocked_holes = Vec::new();
    let mut resolved_hole_ids = Vec::new();
    let mut rejected_hole_ids = Vec::new();

    for (hole_id, hole) in &hole_by_id {
        match input.hole_statuses.get(*hole_id) {
            Some(ProofHoleStatus::Resolved { .. }) => {
                resolved_hole_ids.push((*hole_id).to_owned());
            }
            Some(ProofHoleStatus::Rejected { .. }) => {
                rejected_hole_ids.push((*hole_id).to_owned());
            }
            Some(ProofHoleStatus::Unresolved) | None => {
                if let Some(reason) = first_blocking_dependency(hole, &input.hole_statuses) {
                    blocked_holes.push(ProofHoleBlocked {
                        hole_id: (*hole_id).to_owned(),
                        reason,
                    });
                } else {
                    ready_items.push(proof_hole_work_item(
                        hole,
                        input.base_sketch_hash,
                        skeleton_hash,
                        skeleton.environment_hash,
                        skeleton.policy_hash,
                    ));
                }
            }
        }
    }

    let ready_batches = if ready_items.is_empty() {
        Vec::new()
    } else {
        vec![ProofHoleWorkBatch {
            batch_index: 0,
            items: ready_items,
        }]
    };

    Ok(ProofHoleWorkPlan {
        base_sketch_hash: input.base_sketch_hash,
        skeleton_hash,
        environment_hash: skeleton.environment_hash,
        policy_hash: skeleton.policy_hash,
        ready_batches,
        blocked_holes,
        resolved_hole_ids,
        rejected_hole_ids,
    })
}

pub fn proof_hole_ready_items(
    skeleton: &ProofSkeleton,
    input: &ProofHoleSchedulerInput,
) -> Result<Vec<ProofHoleWorkItem>, ProofHoleSchedulerError> {
    let plan = proof_hole_work_plan(skeleton, input)?;
    Ok(plan
        .ready_batches
        .into_iter()
        .flat_map(|batch| batch.items)
        .collect())
}

pub fn proof_hole_result_sharing_key_hash(key: &ProofHoleResultSharingKey) -> Hash {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_HOLE_RESULT_SHARING_KEY_HASH_DOMAIN);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &key.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &key.policy_hash);
    encode_string_to(&mut out, "context_hash");
    encode_hash_to(&mut out, &key.context_hash);
    encode_string_to(&mut out, "target_hash");
    encode_hash_to(&mut out, &key.target_hash);
    encode_string_to(&mut out, "allowed_premise_identities");
    encode_premise_identities_to(&mut out, &key.allowed_premise_identities);
    sha256_hash(&out)
}

pub fn proof_hole_expected_output_hash(identity: &ProofHoleExpectedOutputIdentity) -> Hash {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_HOLE_EXPECTED_OUTPUT_HASH_DOMAIN);
    encode_string_to(&mut out, "hole_id");
    encode_string_to(&mut out, &identity.hole_id);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &identity.base_sketch_hash);
    encode_string_to(&mut out, "skeleton_hash");
    encode_hash_to(&mut out, &identity.skeleton_hash);
    encode_string_to(&mut out, "hole_hash");
    encode_hash_to(&mut out, &identity.hole_hash);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &identity.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &identity.policy_hash);
    encode_string_to(&mut out, "context_hash");
    encode_hash_to(&mut out, &identity.context_hash);
    encode_string_to(&mut out, "target_hash");
    encode_hash_to(&mut out, &identity.target_hash);
    encode_string_to(&mut out, "result_sharing_key_hash");
    encode_hash_to(&mut out, &identity.result_sharing_key_hash);
    sha256_hash(&out)
}

pub fn proof_hole_work_plan_hash(plan: &ProofHoleWorkPlan) -> Hash {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_HOLE_WORK_PLAN_HASH_DOMAIN);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &plan.base_sketch_hash);
    encode_string_to(&mut out, "skeleton_hash");
    encode_hash_to(&mut out, &plan.skeleton_hash);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &plan.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &plan.policy_hash);
    encode_string_to(&mut out, "ready_batches");
    encode_len_to(&mut out, plan.ready_batches.len());
    for batch in &plan.ready_batches {
        encode_string_to(&mut out, "batch_index");
        encode_u64_to(&mut out, batch.batch_index);
        encode_string_to(&mut out, "items");
        encode_len_to(&mut out, batch.items.len());
        for item in &batch.items {
            encode_work_item_to(&mut out, item);
        }
    }
    encode_string_to(&mut out, "blocked_holes");
    encode_len_to(&mut out, plan.blocked_holes.len());
    for blocked in &plan.blocked_holes {
        encode_string_to(&mut out, "hole_id");
        encode_string_to(&mut out, &blocked.hole_id);
        encode_blocked_reason_to(&mut out, &blocked.reason);
    }
    encode_string_to(&mut out, "resolved_hole_ids");
    encode_strings_to(&mut out, &plan.resolved_hole_ids);
    encode_string_to(&mut out, "rejected_hole_ids");
    encode_strings_to(&mut out, &plan.rejected_hole_ids);
    sha256_hash(&out)
}

pub fn proof_hole_solution_rebase_report(
    expected: &ProofHoleExpectedOutputIdentity,
    submitted: &ProofHoleSubmittedSolutionIdentity,
) -> ProofHoleSolutionRebaseReport {
    let mut reasons = BTreeSet::new();
    if submitted.hole_id != expected.hole_id {
        reasons.insert(ProofHoleSolutionRebaseReason::HoleId);
    }
    if submitted.base_sketch_hash != expected.base_sketch_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::BaseSketchHash);
    }
    if submitted.environment_hash != expected.environment_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::EnvironmentHash);
    }
    if submitted.context_hash != expected.context_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::ContextHash);
    }
    if submitted.target_hash != expected.target_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::TargetHash);
    }
    if submitted.policy_hash != expected.policy_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::PolicyHash);
    }
    if submitted.expected_output_hash != expected.expected_output_hash {
        reasons.insert(ProofHoleSolutionRebaseReason::ExpectedOutputHash);
    }
    let reasons = reasons.into_iter().collect::<Vec<_>>();
    let status = if reasons.is_empty() {
        ProofHoleSolutionRebaseStatus::Current
    } else {
        ProofHoleSolutionRebaseStatus::RebaseRequired
    };
    ProofHoleSolutionRebaseReport {
        hole_id: expected.hole_id.clone(),
        status,
        reasons,
    }
}

pub fn validate_proof_hole_solution_submission(
    expected: &ProofHoleExpectedOutputIdentity,
    submitted: &ProofHoleSubmittedSolutionIdentity,
) -> Result<(), ProofHoleSchedulerError> {
    let report = proof_hole_solution_rebase_report(expected, submitted);
    if report.status == ProofHoleSolutionRebaseStatus::Current {
        Ok(())
    } else {
        Err(ProofHoleSchedulerError::new(
            ProofHoleSchedulerErrorKind::StaleSolution {
                hole_id: report.hole_id,
                reasons: report.reasons,
            },
        ))
    }
}

fn proof_hole_work_item(
    hole: &ProofSkeletonHole,
    base_sketch_hash: Hash,
    skeleton_hash: Hash,
    environment_hash: Hash,
    policy_hash: Hash,
) -> ProofHoleWorkItem {
    let context_hash = hole.local_context_identity.context_hash;
    let target_hash = hole.expected_type_identity.expected_type_hash;
    let allowed_premise_identities = normalize_premises(&hole.allowed_premise_identities);
    let result_sharing_key = proof_hole_result_sharing_key(
        environment_hash,
        policy_hash,
        context_hash,
        target_hash,
        allowed_premise_identities.clone(),
    );
    let expected_output_identity = proof_hole_expected_output_identity(
        hole,
        base_sketch_hash,
        skeleton_hash,
        environment_hash,
        policy_hash,
        result_sharing_key.result_sharing_key_hash,
    );

    ProofHoleWorkItem {
        hole_id: hole.hole_id.clone(),
        dependency_hole_ids: normalize_strings(&hole.dependent_hole_ids),
        context_hash,
        target_hash,
        allowed_premise_identities,
        strategy_profile: normalize_strategy_profile(&hole.strategy_profile),
        budget: hole.budget.clone(),
        expected_output_identity,
        result_sharing_key,
    }
}

fn proof_hole_result_sharing_key(
    environment_hash: Hash,
    policy_hash: Hash,
    context_hash: Hash,
    target_hash: Hash,
    allowed_premise_identities: Vec<ProofSkeletonPremiseIdentity>,
) -> ProofHoleResultSharingKey {
    let mut key = ProofHoleResultSharingKey {
        environment_hash,
        policy_hash,
        context_hash,
        target_hash,
        allowed_premise_identities: normalize_premises(&allowed_premise_identities),
        result_sharing_key_hash: [0; 32],
    };
    key.result_sharing_key_hash = proof_hole_result_sharing_key_hash(&key);
    key
}

fn proof_hole_expected_output_identity(
    hole: &ProofSkeletonHole,
    base_sketch_hash: Hash,
    skeleton_hash: Hash,
    environment_hash: Hash,
    policy_hash: Hash,
    result_sharing_key_hash: Hash,
) -> ProofHoleExpectedOutputIdentity {
    let mut identity = ProofHoleExpectedOutputIdentity {
        hole_id: hole.hole_id.clone(),
        base_sketch_hash,
        skeleton_hash,
        hole_hash: proof_skeleton_hole_hash(hole),
        environment_hash,
        policy_hash,
        context_hash: hole.local_context_identity.context_hash,
        target_hash: hole.expected_type_identity.expected_type_hash,
        result_sharing_key_hash,
        expected_output_hash: [0; 32],
    };
    identity.expected_output_hash = proof_hole_expected_output_hash(&identity);
    identity
}

fn validated_hole_map(
    skeleton: &ProofSkeleton,
) -> Result<BTreeMap<&str, &ProofSkeletonHole>, ProofHoleSchedulerError> {
    let mut hole_by_id = BTreeMap::new();
    for hole in &skeleton.holes {
        if hole_by_id.insert(hole.hole_id.as_str(), hole).is_some() {
            return Err(ProofHoleSchedulerError::new(
                ProofHoleSchedulerErrorKind::DuplicateHoleId {
                    hole_id: hole.hole_id.clone(),
                },
            ));
        }
    }
    Ok(hole_by_id)
}

fn validate_status_holes(
    input: &ProofHoleSchedulerInput,
    hole_by_id: &BTreeMap<&str, &ProofSkeletonHole>,
) -> Result<(), ProofHoleSchedulerError> {
    for hole_id in input.hole_statuses.keys() {
        if !hole_by_id.contains_key(hole_id.as_str()) {
            return Err(ProofHoleSchedulerError::new(
                ProofHoleSchedulerErrorKind::UnknownStatusHole {
                    hole_id: hole_id.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn validate_dependencies(
    hole_by_id: &BTreeMap<&str, &ProofSkeletonHole>,
) -> Result<(), ProofHoleSchedulerError> {
    for (hole_id, hole) in hole_by_id {
        for dependency_hole_id in normalize_strings(&hole.dependent_hole_ids) {
            if !hole_by_id.contains_key(dependency_hole_id.as_str()) {
                return Err(ProofHoleSchedulerError::new(
                    ProofHoleSchedulerErrorKind::UnknownDependency {
                        hole_id: (*hole_id).to_owned(),
                        dependency_hole_id,
                    },
                ));
            }
        }
    }
    Ok(())
}

fn validate_acyclic_dependencies(
    hole_by_id: &BTreeMap<&str, &ProofSkeletonHole>,
) -> Result<(), ProofHoleSchedulerError> {
    let mut visits = BTreeMap::new();
    for hole_id in hole_by_id.keys() {
        visit_hole(hole_id, hole_by_id, &mut visits)?;
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    Visiting,
    Visited,
}

fn visit_hole(
    hole_id: &str,
    hole_by_id: &BTreeMap<&str, &ProofSkeletonHole>,
    visits: &mut BTreeMap<String, VisitState>,
) -> Result<(), ProofHoleSchedulerError> {
    match visits.get(hole_id) {
        Some(VisitState::Visited) => return Ok(()),
        Some(VisitState::Visiting) => {
            return Err(ProofHoleSchedulerError::new(
                ProofHoleSchedulerErrorKind::DependencyCycle {
                    hole_id: hole_id.to_owned(),
                },
            ));
        }
        None => {}
    }
    visits.insert(hole_id.to_owned(), VisitState::Visiting);
    let hole = hole_by_id
        .get(hole_id)
        .expect("dependency validation guarantees known hole ids");
    for dependency_hole_id in normalize_strings(&hole.dependent_hole_ids) {
        visit_hole(&dependency_hole_id, hole_by_id, visits)?;
    }
    visits.insert(hole_id.to_owned(), VisitState::Visited);
    Ok(())
}

fn first_blocking_dependency(
    hole: &ProofSkeletonHole,
    statuses: &BTreeMap<String, ProofHoleStatus>,
) -> Option<ProofHoleBlockedReason> {
    for dependency_hole_id in normalize_strings(&hole.dependent_hole_ids) {
        match statuses.get(&dependency_hole_id) {
            Some(ProofHoleStatus::Resolved { .. }) => {}
            Some(ProofHoleStatus::Rejected { .. }) => {
                return Some(ProofHoleBlockedReason::DependencyRejected { dependency_hole_id });
            }
            Some(ProofHoleStatus::Unresolved) | None => {
                return Some(ProofHoleBlockedReason::DependencyUnresolved { dependency_hole_id });
            }
        }
    }
    None
}

fn normalize_strings(values: &[String]) -> Vec<String> {
    let mut values = values.to_vec();
    values.sort();
    values.dedup();
    values
}

fn normalize_premises(
    premises: &[ProofSkeletonPremiseIdentity],
) -> Vec<ProofSkeletonPremiseIdentity> {
    let mut premises = premises.to_vec();
    premises.sort();
    premises.dedup();
    premises
}

fn normalize_strategy_profile(
    profile: &ProofSkeletonStrategyProfile,
) -> ProofSkeletonStrategyProfile {
    let mut preferred_node_kinds = profile.preferred_node_kinds.clone();
    preferred_node_kinds.sort();
    preferred_node_kinds.dedup();
    ProofSkeletonStrategyProfile {
        profile_id: profile.profile_id,
        preferred_node_kinds,
    }
}

fn encode_work_item_to(out: &mut Vec<u8>, item: &ProofHoleWorkItem) {
    encode_string_to(out, "hole_id");
    encode_string_to(out, &item.hole_id);
    encode_string_to(out, "dependency_hole_ids");
    encode_strings_to(out, &item.dependency_hole_ids);
    encode_string_to(out, "context_hash");
    encode_hash_to(out, &item.context_hash);
    encode_string_to(out, "target_hash");
    encode_hash_to(out, &item.target_hash);
    encode_string_to(out, "allowed_premise_identities");
    encode_premise_identities_to(out, &item.allowed_premise_identities);
    encode_strategy_profile_to(out, &item.strategy_profile);
    encode_budget_to(out, &item.budget);
    encode_string_to(out, "expected_output_hash");
    encode_hash_to(out, &item.expected_output_identity.expected_output_hash);
    encode_string_to(out, "result_sharing_key_hash");
    encode_hash_to(out, &item.result_sharing_key.result_sharing_key_hash);
}

fn encode_blocked_reason_to(out: &mut Vec<u8>, reason: &ProofHoleBlockedReason) {
    match reason {
        ProofHoleBlockedReason::DependencyUnresolved { dependency_hole_id } => {
            encode_string_to(out, "dependency_unresolved");
            encode_string_to(out, "dependency_hole_id");
            encode_string_to(out, dependency_hole_id);
        }
        ProofHoleBlockedReason::DependencyRejected { dependency_hole_id } => {
            encode_string_to(out, "dependency_rejected");
            encode_string_to(out, "dependency_hole_id");
            encode_string_to(out, dependency_hole_id);
        }
    }
}

fn encode_premise_identities_to(out: &mut Vec<u8>, premises: &[ProofSkeletonPremiseIdentity]) {
    let premises = normalize_premises(premises);
    encode_len_to(out, premises.len());
    for premise in &premises {
        encode_string_to(out, "premise_hash");
        encode_hash_to(out, &premise.premise_hash);
        encode_string_to(out, "source");
        encode_string_to(out, premise_source_wire(premise.source));
        encode_string_to(out, "axiom_profile_hash");
        encode_hash_to(out, &premise.axiom_profile_hash);
    }
}

fn encode_strategy_profile_to(out: &mut Vec<u8>, profile: &ProofSkeletonStrategyProfile) {
    let profile = normalize_strategy_profile(profile);
    encode_string_to(out, "strategy_profile");
    encode_string_to(out, "profile_id");
    encode_string_to(out, strategy_profile_id_wire(profile.profile_id));
    encode_string_to(out, "preferred_node_kinds");
    encode_len_to(out, profile.preferred_node_kinds.len());
    for kind in &profile.preferred_node_kinds {
        encode_string_to(out, preferred_node_kind_wire(*kind));
    }
}

fn encode_budget_to(out: &mut Vec<u8>, budget: &ProofSkeletonBudget) {
    encode_string_to(out, "budget");
    encode_string_to(out, "max_candidates");
    encode_u64_to(out, budget.max_candidates);
    encode_string_to(out, "max_search_nodes");
    encode_u64_to(out, budget.max_search_nodes);
    encode_option_u64_to(out, "max_depth", budget.max_depth);
    encode_option_u64_to(out, "max_repair_steps", budget.max_repair_steps);
}

fn premise_source_wire(source: ProofSkeletonPremiseSource) -> &'static str {
    match source {
        ProofSkeletonPremiseSource::LocalContext => "local_context",
        ProofSkeletonPremiseSource::VerifiedImport => "verified_import",
        ProofSkeletonPremiseSource::VerifiedLocalLemma => "verified_local_lemma",
    }
}

fn strategy_profile_id_wire(profile_id: ProofSkeletonStrategyProfileId) -> &'static str {
    match profile_id {
        ProofSkeletonStrategyProfileId::Exact => "exact",
        ProofSkeletonStrategyProfileId::Rewrite => "rewrite",
        ProofSkeletonStrategyProfileId::Solver => "solver",
        ProofSkeletonStrategyProfileId::Search => "search",
        ProofSkeletonStrategyProfileId::LocalLemma => "local_lemma",
    }
}

fn preferred_node_kind_wire(kind: ProofSkeletonPreferredNodeKind) -> &'static str {
    match kind {
        ProofSkeletonPreferredNodeKind::Introduce => "introduce",
        ProofSkeletonPreferredNodeKind::CaseSplit => "case_split",
        ProofSkeletonPreferredNodeKind::Induction => "induction",
        ProofSkeletonPreferredNodeKind::AssertLemma => "assert_lemma",
        ProofSkeletonPreferredNodeKind::ApplyPremise => "apply_premise",
        ProofSkeletonPreferredNodeKind::RewritePhase => "rewrite_phase",
        ProofSkeletonPreferredNodeKind::SolverPhase => "solver_phase",
        ProofSkeletonPreferredNodeKind::CloseByExact => "close_by_exact",
        ProofSkeletonPreferredNodeKind::SearchSubgoal => "search_subgoal",
    }
}

fn encode_strings_to(out: &mut Vec<u8>, values: &[String]) {
    let values = normalize_strings(values);
    encode_len_to(out, values.len());
    for value in &values {
        encode_string_to(out, value);
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    out.push(b's');
    encode_len_to(out, value.len());
    out.extend(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.push(b'h');
    out.extend(hash);
}

fn encode_option_u64_to(out: &mut Vec<u8>, field: &str, value: Option<u64>) {
    encode_string_to(out, field);
    match value {
        Some(value) => {
            out.push(1);
            encode_u64_to(out, value);
        }
        None => out.push(0),
    }
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.push(b'u');
    out.extend(value.to_be_bytes());
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    encode_u64_to(out, len as u64);
}

fn sha256_hash(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof_skeleton::{
        ProofSkeletonCoreExpr, ProofSkeletonExpectedTypeIdentity,
        ProofSkeletonLocalContextIdentity, ProofSkeletonStaleSolutionRejection,
        ProofSkeletonTargetStatementIdentity, ProofSkeletonTerm, PROOF_SKELETON_API_VERSION,
    };
    use crate::types::format_hash_string;

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn skeleton(holes: Vec<ProofSkeletonHole>, env: Hash, policy: Hash) -> ProofSkeleton {
        ProofSkeleton {
            api_version: PROOF_SKELETON_API_VERSION.to_owned(),
            skeleton_id: hash(0xa0),
            target_statement_identity: ProofSkeletonTargetStatementIdentity {
                statement_hash: hash(0x01),
                expected_type_hash: hash(0x02),
                root_context_hash: hash(0x03),
                module: Some("Proofs.Ai.HoleScheduler".to_owned()),
                declaration: Some("target".to_owned()),
            },
            environment_hash: env,
            policy_hash: policy,
            root: ProofSkeletonTerm::Hole {
                hole_id: "h_root".to_owned(),
            },
            holes,
        }
    }

    fn hole(hole_id: &str, context: u8, target: u8, dependencies: &[&str]) -> ProofSkeletonHole {
        let env = hash(0xe0);
        let policy = hash(0xf0);
        ProofSkeletonHole {
            hole_id: hole_id.to_owned(),
            local_context_identity: ProofSkeletonLocalContextIdentity {
                context_hash: hash(context),
                binder_fingerprint_hash: hash(context.wrapping_add(1)),
            },
            expected_type_identity: ProofSkeletonExpectedTypeIdentity {
                expected_type_hash: hash(target),
                expected_type: ProofSkeletonCoreExpr::Inline {
                    core_expr_hash: hash(target),
                    canonical_bytes: vec![target],
                },
            },
            dependent_hole_ids: dependencies.iter().map(|id| (*id).to_owned()).collect(),
            allowed_premise_identities: vec![premise(0x70, policy)],
            strategy_profile: ProofSkeletonStrategyProfile {
                profile_id: ProofSkeletonStrategyProfileId::Exact,
                preferred_node_kinds: vec![ProofSkeletonPreferredNodeKind::CloseByExact],
            },
            budget: ProofSkeletonBudget {
                max_candidates: 2,
                max_search_nodes: 8,
                max_depth: Some(3),
                max_repair_steps: Some(1),
            },
            stale_solution_rejection: ProofSkeletonStaleSolutionRejection {
                required_context_hash: hash(context),
                required_expected_type_hash: hash(target),
                required_environment_hash: env,
                required_policy_hash: policy,
            },
        }
    }

    fn premise(byte: u8, policy: Hash) -> ProofSkeletonPremiseIdentity {
        ProofSkeletonPremiseIdentity {
            premise_hash: hash(byte),
            source: ProofSkeletonPremiseSource::VerifiedImport,
            axiom_profile_hash: policy,
        }
    }

    fn ready_ids(plan: &ProofHoleWorkPlan) -> Vec<String> {
        plan.ready_batches
            .iter()
            .flat_map(|batch| batch.items.iter().map(|item| item.hole_id.clone()))
            .collect()
    }

    #[test]
    fn hole_scheduler_ready_set_order_is_stable_and_dependency_aware() {
        let env = hash(0xe0);
        let policy = hash(0xf0);
        let skeleton = skeleton(
            vec![
                hole("h3", 0x33, 0x43, &["h1", "h2"]),
                hole("h2", 0x32, 0x42, &[]),
                hole("h1", 0x31, 0x41, &[]),
                hole("h4", 0x34, 0x44, &["h3"]),
            ],
            env,
            policy,
        );
        let base = hash(0xb0);

        let empty_plan = proof_hole_work_plan(&skeleton, &ProofHoleSchedulerInput::new(base))
            .expect("ready-set should build");
        assert_eq!(ready_ids(&empty_plan), vec!["h1", "h2"]);
        assert_eq!(
            empty_plan.blocked_holes,
            vec![
                ProofHoleBlocked {
                    hole_id: "h3".to_owned(),
                    reason: ProofHoleBlockedReason::DependencyUnresolved {
                        dependency_hole_id: "h1".to_owned()
                    }
                },
                ProofHoleBlocked {
                    hole_id: "h4".to_owned(),
                    reason: ProofHoleBlockedReason::DependencyUnresolved {
                        dependency_hole_id: "h3".to_owned()
                    }
                },
            ]
        );

        let first_order = ProofHoleSchedulerInput::new(base)
            .with_hole_status(
                "h2",
                ProofHoleStatus::Resolved {
                    output_hash: hash(0xc2),
                },
            )
            .with_hole_status(
                "h1",
                ProofHoleStatus::Resolved {
                    output_hash: hash(0xc1),
                },
            );
        let second_order = ProofHoleSchedulerInput::new(base)
            .with_hole_status(
                "h1",
                ProofHoleStatus::Resolved {
                    output_hash: hash(0xc1),
                },
            )
            .with_hole_status(
                "h2",
                ProofHoleStatus::Resolved {
                    output_hash: hash(0xc2),
                },
            );
        let first_plan =
            proof_hole_work_plan(&skeleton, &first_order).expect("first plan should build");
        let second_plan =
            proof_hole_work_plan(&skeleton, &second_order).expect("second plan should build");
        assert_eq!(ready_ids(&first_plan), vec!["h3"]);
        assert_eq!(first_plan, second_plan);
        assert_eq!(
            first_plan.ready_batches[0].items[0].context_hash,
            hash(0x33)
        );
        assert_eq!(first_plan.ready_batches[0].items[0].target_hash, hash(0x43));

        let rejected_dependency = ProofHoleSchedulerInput::new(base).with_hole_status(
            "h1",
            ProofHoleStatus::Rejected {
                rejection_hash: hash(0xd1),
            },
        );
        let rejected_plan = proof_hole_work_plan(&skeleton, &rejected_dependency)
            .expect("rejected dependency plan should build");
        assert_eq!(ready_ids(&rejected_plan), vec!["h2"]);
        assert!(rejected_plan.blocked_holes.contains(&ProofHoleBlocked {
            hole_id: "h3".to_owned(),
            reason: ProofHoleBlockedReason::DependencyRejected {
                dependency_hole_id: "h1".to_owned()
            },
        }));
    }

    #[test]
    fn hole_scheduler_result_sharing_key_binds_policy_and_allowed_premises() {
        let env = hash(0xe0);
        let policy = hash(0xf0);
        let mut h1 = hole("h1", 0x31, 0x41, &[]);
        let mut h2 = hole("h2", 0x31, 0x41, &[]);
        h2.allowed_premise_identities = vec![premise(0x70, policy)];
        let skeleton = skeleton(vec![h1.clone(), h2], env, policy);
        let plan = proof_hole_work_plan(&skeleton, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect("ready plan should build");
        let key1 = &plan.ready_batches[0].items[0].result_sharing_key;
        let key2 = &plan.ready_batches[0].items[1].result_sharing_key;
        assert_eq!(key1.context_hash, hash(0x31));
        assert_eq!(key1.target_hash, hash(0x41));
        assert_eq!(key1.result_sharing_key_hash, key2.result_sharing_key_hash);
        assert_eq!(
            key1.result_sharing_key_hash,
            proof_hole_result_sharing_key_hash(key1)
        );

        let mut changed_policy = skeleton.clone();
        changed_policy.policy_hash = hash(0xf1);
        let changed_policy_key =
            &proof_hole_work_plan(&changed_policy, &ProofHoleSchedulerInput::new(hash(0xb0)))
                .expect("policy changed plan should build")
                .ready_batches[0]
                .items[0]
                .result_sharing_key;
        assert_ne!(
            key1.result_sharing_key_hash,
            changed_policy_key.result_sharing_key_hash
        );

        h1.allowed_premise_identities = vec![premise(0x71, policy)];
        let changed_premise = self::skeleton(vec![h1], env, policy);
        let changed_premise_key =
            &proof_hole_work_plan(&changed_premise, &ProofHoleSchedulerInput::new(hash(0xb0)))
                .expect("premise changed plan should build")
                .ready_batches[0]
                .items[0]
                .result_sharing_key;
        assert_ne!(
            key1.result_sharing_key_hash,
            changed_premise_key.result_sharing_key_hash
        );
    }

    #[test]
    fn hole_scheduler_rejects_unknown_status_unknown_dependency_and_cycles() {
        let env = hash(0xe0);
        let policy = hash(0xf0);
        let valid = skeleton(vec![hole("h1", 0x31, 0x41, &[])], env, policy);
        let unknown_status = proof_hole_work_plan(
            &valid,
            &ProofHoleSchedulerInput::new(hash(0xb0))
                .with_hole_status("missing", ProofHoleStatus::Unresolved),
        )
        .expect_err("unknown status must reject");
        assert!(matches!(
            unknown_status.kind(),
            ProofHoleSchedulerErrorKind::UnknownStatusHole { hole_id }
                if hole_id == "missing"
        ));

        let unknown_dependency = skeleton(vec![hole("h1", 0x31, 0x41, &["missing"])], env, policy);
        let dependency_error = proof_hole_work_plan(
            &unknown_dependency,
            &ProofHoleSchedulerInput::new(hash(0xb0)),
        )
        .expect_err("unknown dependency must reject");
        assert!(matches!(
            dependency_error.kind(),
            ProofHoleSchedulerErrorKind::UnknownDependency {
                hole_id,
                dependency_hole_id
            } if hole_id == "h1" && dependency_hole_id == "missing"
        ));

        let cycle = skeleton(
            vec![
                hole("h1", 0x31, 0x41, &["h2"]),
                hole("h2", 0x32, 0x42, &["h1"]),
            ],
            env,
            policy,
        );
        let cycle_error = proof_hole_work_plan(&cycle, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect_err("cycle must reject");
        assert!(matches!(
            cycle_error.kind(),
            ProofHoleSchedulerErrorKind::DependencyCycle { .. }
        ));
    }

    #[test]
    fn hole_solution_stale_rebase_accepts_current_solution_identity() {
        let skeleton = skeleton(vec![hole("h1", 0x31, 0x41, &[])], hash(0xe0), hash(0xf0));
        let item = proof_hole_ready_items(&skeleton, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect("ready items should build")
            .remove(0);
        let expected = &item.expected_output_identity;
        let submitted = ProofHoleSubmittedSolutionIdentity {
            hole_id: item.hole_id.clone(),
            base_sketch_hash: expected.base_sketch_hash,
            environment_hash: expected.environment_hash,
            context_hash: expected.context_hash,
            target_hash: expected.target_hash,
            policy_hash: expected.policy_hash,
            expected_output_hash: expected.expected_output_hash,
        };
        let report = proof_hole_solution_rebase_report(expected, &submitted);
        assert_eq!(report.status, ProofHoleSolutionRebaseStatus::Current);
        assert!(report.reasons.is_empty());
        validate_proof_hole_solution_submission(expected, &submitted)
            .expect("current submitted solution should validate");
    }

    #[test]
    fn hole_solution_stale_rebase_rejects_changed_identities() {
        let skeleton = skeleton(vec![hole("h1", 0x31, 0x41, &[])], hash(0xe0), hash(0xf0));
        let item = proof_hole_ready_items(&skeleton, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect("ready items should build")
            .remove(0);
        let expected = &item.expected_output_identity;
        let submitted = ProofHoleSubmittedSolutionIdentity {
            hole_id: "h1".to_owned(),
            base_sketch_hash: hash(0xb1),
            environment_hash: hash(0xe1),
            context_hash: hash(0x99),
            target_hash: hash(0x98),
            policy_hash: hash(0xf1),
            expected_output_hash: hash(0x97),
        };
        let report = proof_hole_solution_rebase_report(expected, &submitted);
        assert_eq!(report.status, ProofHoleSolutionRebaseStatus::RebaseRequired);
        assert_eq!(
            report.reasons,
            vec![
                ProofHoleSolutionRebaseReason::BaseSketchHash,
                ProofHoleSolutionRebaseReason::EnvironmentHash,
                ProofHoleSolutionRebaseReason::ContextHash,
                ProofHoleSolutionRebaseReason::TargetHash,
                ProofHoleSolutionRebaseReason::PolicyHash,
                ProofHoleSolutionRebaseReason::ExpectedOutputHash,
            ]
        );
        let error = validate_proof_hole_solution_submission(expected, &submitted)
            .expect_err("stale submitted solution must reject");
        assert!(matches!(
            error.kind(),
            ProofHoleSchedulerErrorKind::StaleSolution { reasons, .. }
                if reasons.contains(&ProofHoleSolutionRebaseReason::ContextHash)
                    && reasons.contains(&ProofHoleSolutionRebaseReason::TargetHash)
                    && reasons.contains(&ProofHoleSolutionRebaseReason::BaseSketchHash)
        ));
    }

    #[test]
    fn hole_scheduler_work_plan_hash_is_stable_for_same_ready_set() {
        let skeleton = skeleton(
            vec![hole("h2", 0x32, 0x42, &[]), hole("h1", 0x31, 0x41, &[])],
            hash(0xe0),
            hash(0xf0),
        );
        let plan = proof_hole_work_plan(&skeleton, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect("plan should build");
        let same = proof_hole_work_plan(&skeleton, &ProofHoleSchedulerInput::new(hash(0xb0)))
            .expect("same plan should build");
        assert_eq!(
            proof_hole_work_plan_hash(&plan),
            proof_hole_work_plan_hash(&same)
        );
        assert_eq!(ready_ids(&plan), vec!["h1", "h2"]);
        assert_eq!(
            format_hash_string(
                &plan.ready_batches[0].items[0]
                    .expected_output_identity
                    .target_hash
            ),
            format_hash_string(&hash(0x41))
        );
    }
}

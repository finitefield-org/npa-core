use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const PROOF_SKETCH_API_VERSION: &str = "npa.proof-sketch.v1";
pub const PROOF_SKETCH_HASH_DOMAIN: &str = "npa.proof-sketch.sketch-hash.v1";
pub const PROOF_SKETCH_LOCAL_LEMMA_PROPOSAL_HASH_DOMAIN: &str =
    "npa.proof-sketch.local-lemma-proposal-hash.v1";
pub const PROOF_SKETCH_REVISION_PATCH_HASH_DOMAIN: &str = "npa.proof-sketch.revision-patch-hash.v1";
pub const PROOF_SKETCH_REVISION_DECISION_HASH_DOMAIN: &str =
    "npa.proof-sketch.revision-decision-hash.v1";
pub const PROOF_SKETCH_MINIMIZATION_RECORD_HASH_DOMAIN: &str =
    "npa.proof-sketch.minimization-record-hash.v1";
pub const PROOF_SKETCH_MINIMIZATION_PASS_KINDS: [ProofSketchMinimizationKind; 6] = [
    ProofSketchMinimizationKind::RemoveUnusedLocalLemma,
    ProofSketchMinimizationKind::ReplaceHoleWithExactTerm,
    ProofSketchMinimizationKind::CollapseRewrites,
    ProofSketchMinimizationKind::RemoveDuplicatePremiseApplication,
    ProofSketchMinimizationKind::ExtractSharedBranchSubproof,
    ProofSketchMinimizationKind::ReduceImportClosure,
];
pub const PROOF_SKETCH_NODE_KINDS: &[&str] = &[
    "introduce",
    "case_split",
    "induction",
    "assert_lemma",
    "apply_premise",
    "rewrite_phase",
    "solver_phase",
    "close_by_exact",
    "search_subgoal",
];
pub const PROOF_SKETCH_SUPPORTED_NODE_KINDS: &[ProofSketchNodeKind] = &[
    ProofSketchNodeKind::Introduce,
    ProofSketchNodeKind::CaseSplit,
    ProofSketchNodeKind::Induction,
    ProofSketchNodeKind::AssertLemma,
    ProofSketchNodeKind::ApplyPremise,
    ProofSketchNodeKind::RewritePhase,
    ProofSketchNodeKind::SolverPhase,
    ProofSketchNodeKind::CloseByExact,
    ProofSketchNodeKind::SearchSubgoal,
];

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "sketch_id",
    "target_statement_identity",
    "environment_hash",
    "policy_hash",
    "sublemma_statement_proposals",
    "nodes",
    "edges",
    "advisory",
];
const TARGET_IDENTITY_FIELDS: &[&str] = &[
    "statement_hash",
    "input_context_hash",
    "output_context_hash",
    "module",
    "declaration",
];
const SUBLEMMA_PROPOSAL_FIELDS: &[&str] = &[
    "proposal_id",
    "statement_hash",
    "input_context_hash",
    "output_context_hash",
    "generalization_policy",
    "display",
];
const NODE_FIELDS: &[&str] = &[
    "node_id",
    "kind",
    "input_context_hash",
    "output_context_hash",
    "expected_effect",
    "strategy_hints",
    "budget",
    "fallback_policy",
    "statement_proposal_id",
    "premise_hashes",
    "display",
];
const EXPECTED_EFFECT_FIELDS: &[&str] = &["kind", "goal_delta", "effect_hash"];
const BUDGET_FIELDS: &[&str] = &[
    "max_candidates",
    "max_search_nodes",
    "max_depth",
    "max_repair_steps",
];
const FALLBACK_POLICY_FIELDS: &[&str] = &["action", "fallback_node_id", "repair_profile"];
const EDGE_FIELDS: &[&str] = &["from", "to", "kind"];
const DISPLAY_FIELDS: &[&str] = &["label", "explanation"];
const ADVISORY_FIELDS: &[&str] = &["display_text", "score", "model_score", "scoring_profile"];
const LOCAL_LEMMA_PROPOSAL_FIELDS: &[&str] = &[
    "proposal_id",
    "base_sketch_hash",
    "source_node_id",
    "statement_hash",
    "input_context_hash",
    "output_context_hash",
    "environment_hash",
    "policy_hash",
    "allowed_premise_hashes",
    "state",
];
const REVISION_PATCH_FIELDS: &[&str] = &["base_sketch_hash", "dependency_invalidation", "patch"];
const REVISION_DEPENDENCY_INVALIDATION_FIELDS: &[&str] =
    &["kind", "invalidated_node_ids", "diagnostic_hash"];
const REVISION_PATCH_KIND_FIELDS: &[&str] = &[
    "kind",
    "node",
    "original_node_id",
    "replacement_node_ids",
    "merged_node_id",
    "source_node_ids",
    "node_id",
    "local_lemma_proposal_hash",
    "lemma_id",
    "strategy_hints",
    "repair_profile",
    "premise_hashes",
    "budget",
    "diagnostic_hash",
];
const MINIMIZATION_RECORD_FIELDS: &[&str] = &[
    "base_sketch_hash",
    "kind",
    "target_node_id",
    "candidate_patch_hash",
    "replay_plan_hash",
    "verification_result_hash",
    "outcome",
    "score",
];
const MAX_SUBLEMMA_PROPOSALS: usize = 1000;
const MAX_NODES: usize = 1000;
const MAX_EDGES: usize = 4000;
const MAX_STRATEGY_HINTS: usize = 32;
const MAX_PREMISE_HASHES: usize = 256;
const MAX_REVISION_PATCH_NODE_IDS: usize = 1000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketch {
    pub api_version: String,
    pub sketch_id: Hash,
    pub target_statement_identity: ProofSketchTargetStatementIdentity,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub sublemma_statement_proposals: Vec<ProofSketchSublemmaStatementProposal>,
    pub nodes: Vec<ProofSketchNode>,
    pub edges: Vec<ProofSketchEdge>,
    pub advisory: Option<ProofSketchAdvisory>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchTargetStatementIdentity {
    pub statement_hash: Hash,
    pub input_context_hash: Hash,
    pub output_context_hash: Hash,
    pub module: Option<String>,
    pub declaration: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchSublemmaStatementProposal {
    pub proposal_id: String,
    pub statement_hash: Hash,
    pub input_context_hash: Hash,
    pub output_context_hash: Hash,
    pub generalization_policy: ProofSketchGeneralizationPolicy,
    pub display: Option<ProofSketchDisplay>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchNode {
    pub node_id: String,
    pub kind: ProofSketchNodeKind,
    pub input_context_hash: Hash,
    pub output_context_hash: Hash,
    pub expected_effect: ProofSketchExpectedEffect,
    pub strategy_hints: Vec<ProofSketchStrategyHint>,
    pub budget: ProofSketchBudget,
    pub fallback_policy: ProofSketchFallbackPolicy,
    pub statement_proposal_id: Option<String>,
    pub premise_hashes: Vec<Hash>,
    pub display: Option<ProofSketchDisplay>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchNodeKind {
    Introduce,
    CaseSplit,
    Induction,
    AssertLemma,
    ApplyPremise,
    RewritePhase,
    SolverPhase,
    CloseByExact,
    SearchSubgoal,
}

impl ProofSketchNodeKind {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "introduce" => Some(Self::Introduce),
            "case_split" => Some(Self::CaseSplit),
            "induction" => Some(Self::Induction),
            "assert_lemma" => Some(Self::AssertLemma),
            "apply_premise" => Some(Self::ApplyPremise),
            "rewrite_phase" => Some(Self::RewritePhase),
            "solver_phase" => Some(Self::SolverPhase),
            "close_by_exact" => Some(Self::CloseByExact),
            "search_subgoal" => Some(Self::SearchSubgoal),
            _ => None,
        }
    }

    pub const fn wire(self) -> &'static str {
        match self {
            Self::Introduce => "introduce",
            Self::CaseSplit => "case_split",
            Self::Induction => "induction",
            Self::AssertLemma => "assert_lemma",
            Self::ApplyPremise => "apply_premise",
            Self::RewritePhase => "rewrite_phase",
            Self::SolverPhase => "solver_phase",
            Self::CloseByExact => "close_by_exact",
            Self::SearchSubgoal => "search_subgoal",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchStrategyHint {
    IntroduceLocal,
    SplitCases,
    InductionPrinciple,
    AssertSublemma,
    ApplyPremise,
    RewriteNormalize,
    InvokeSolver,
    ExactTerm,
    BoundedSearch,
}

impl ProofSketchStrategyHint {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "introduce_local" => Some(Self::IntroduceLocal),
            "split_cases" => Some(Self::SplitCases),
            "induction_principle" => Some(Self::InductionPrinciple),
            "assert_sublemma" => Some(Self::AssertSublemma),
            "apply_premise" => Some(Self::ApplyPremise),
            "rewrite_normalize" => Some(Self::RewriteNormalize),
            "invoke_solver" => Some(Self::InvokeSolver),
            "exact_term" => Some(Self::ExactTerm),
            "bounded_search" => Some(Self::BoundedSearch),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::IntroduceLocal => "introduce_local",
            Self::SplitCases => "split_cases",
            Self::InductionPrinciple => "induction_principle",
            Self::AssertSublemma => "assert_sublemma",
            Self::ApplyPremise => "apply_premise",
            Self::RewriteNormalize => "rewrite_normalize",
            Self::InvokeSolver => "invoke_solver",
            Self::ExactTerm => "exact_term",
            Self::BoundedSearch => "bounded_search",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchExpectedEffect {
    pub kind: ProofSketchExpectedEffectKind,
    pub goal_delta: i64,
    pub effect_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchExpectedEffectKind {
    IntroducesLocals,
    SplitsCases,
    StartsInduction,
    AssertsSublemma,
    AppliesPremise,
    RewritesTarget,
    InvokesSolver,
    ClosesGoal,
    SearchesSubgoal,
}

impl ProofSketchExpectedEffectKind {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "introduces_locals" => Some(Self::IntroducesLocals),
            "splits_cases" => Some(Self::SplitsCases),
            "starts_induction" => Some(Self::StartsInduction),
            "asserts_sublemma" => Some(Self::AssertsSublemma),
            "applies_premise" => Some(Self::AppliesPremise),
            "rewrites_target" => Some(Self::RewritesTarget),
            "invokes_solver" => Some(Self::InvokesSolver),
            "closes_goal" => Some(Self::ClosesGoal),
            "searches_subgoal" => Some(Self::SearchesSubgoal),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::IntroducesLocals => "introduces_locals",
            Self::SplitsCases => "splits_cases",
            Self::StartsInduction => "starts_induction",
            Self::AssertsSublemma => "asserts_sublemma",
            Self::AppliesPremise => "applies_premise",
            Self::RewritesTarget => "rewrites_target",
            Self::InvokesSolver => "invokes_solver",
            Self::ClosesGoal => "closes_goal",
            Self::SearchesSubgoal => "searches_subgoal",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchBudget {
    pub max_candidates: u64,
    pub max_search_nodes: u64,
    pub max_depth: Option<u64>,
    pub max_repair_steps: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchFallbackPolicy {
    pub action: ProofSketchFallbackAction,
    pub fallback_node_id: Option<String>,
    pub repair_profile: Option<ProofSketchRepairProfile>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchFallbackAction {
    Fail,
    ExpandSearch,
    SplitNode,
    RequestReview,
}

impl ProofSketchFallbackAction {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "fail" => Some(Self::Fail),
            "expand_search" => Some(Self::ExpandSearch),
            "split_node" => Some(Self::SplitNode),
            "request_review" => Some(Self::RequestReview),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::Fail => "fail",
            Self::ExpandSearch => "expand_search",
            Self::SplitNode => "split_node",
            Self::RequestReview => "request_review",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchRepairProfile {
    None,
    LocalRepair,
    PremiseRetrieval,
    FullReplan,
}

impl ProofSketchRepairProfile {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "none" => Some(Self::None),
            "local_repair" => Some(Self::LocalRepair),
            "premise_retrieval" => Some(Self::PremiseRetrieval),
            "full_replan" => Some(Self::FullReplan),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::LocalRepair => "local_repair",
            Self::PremiseRetrieval => "premise_retrieval",
            Self::FullReplan => "full_replan",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchGeneralizationPolicy {
    None,
    LocalsOnly,
    PremiseClosure,
    InductionHypotheses,
}

impl ProofSketchGeneralizationPolicy {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "none" => Some(Self::None),
            "locals_only" => Some(Self::LocalsOnly),
            "premise_closure" => Some(Self::PremiseClosure),
            "induction_hypotheses" => Some(Self::InductionHypotheses),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::LocalsOnly => "locals_only",
            Self::PremiseClosure => "premise_closure",
            Self::InductionHypotheses => "induction_hypotheses",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchEdge {
    pub from: String,
    pub to: String,
    pub kind: ProofSketchEdgeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchEdgeKind {
    DependsOn,
    Feeds,
    Discharges,
}

impl ProofSketchEdgeKind {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "depends_on" => Some(Self::DependsOn),
            "feeds" => Some(Self::Feeds),
            "discharges" => Some(Self::Discharges),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::DependsOn => "depends_on",
            Self::Feeds => "feeds",
            Self::Discharges => "discharges",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchValidationProfile {
    pub expected_environment_hash: Option<Hash>,
    pub expected_policy_hash: Option<Hash>,
    pub supported_node_kinds: BTreeSet<ProofSketchNodeKind>,
}

impl Default for ProofSketchValidationProfile {
    fn default() -> Self {
        Self {
            expected_environment_hash: None,
            expected_policy_hash: None,
            supported_node_kinds: PROOF_SKETCH_SUPPORTED_NODE_KINDS.iter().copied().collect(),
        }
    }
}

impl ProofSketchValidationProfile {
    pub fn strict(expected_environment_hash: Hash, expected_policy_hash: Hash) -> Self {
        Self {
            expected_environment_hash: Some(expected_environment_hash),
            expected_policy_hash: Some(expected_policy_hash),
            ..Self::default()
        }
    }

    pub fn with_supported_node_kinds(
        mut self,
        supported_node_kinds: impl IntoIterator<Item = ProofSketchNodeKind>,
    ) -> Self {
        self.supported_node_kinds = supported_node_kinds.into_iter().collect();
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchValidationReport {
    pub sketch_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub topological_node_ids: Vec<String>,
    pub root_node_ids: Vec<String>,
    pub terminal_node_ids: Vec<String>,
    pub nodes: Vec<ProofSketchValidatedNode>,
    pub edges: Vec<ProofSketchValidatedEdge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchValidatedNode {
    pub node_id: String,
    pub kind: ProofSketchNodeKind,
    pub predecessor_node_ids: Vec<String>,
    pub successor_node_ids: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProofSketchValidatedEdge {
    pub from: String,
    pub to: String,
    pub kind: ProofSketchEdgeKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchValidationError {
    kind: ProofSketchValidationErrorKind,
}

impl ProofSketchValidationError {
    fn new(kind: ProofSketchValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ProofSketchValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSketchValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofSketchValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchValidationErrorKind {
    DuplicateNodeId {
        node_id: String,
    },
    UnknownNode {
        node_id: String,
    },
    Cycle {
        node_ids: Vec<String>,
    },
    FutureReference {
        from: String,
        to: String,
        kind: ProofSketchEdgeKind,
    },
    DisconnectedRequiredNode {
        node_id: String,
    },
    MalformedEdge {
        from: String,
        to: String,
        kind: ProofSketchEdgeKind,
        reason: ProofSketchMalformedEdgeReason,
    },
    EnvironmentMismatch {
        expected: Hash,
        actual: Hash,
    },
    PolicyMismatch {
        expected: Hash,
        actual: Hash,
    },
    UnsupportedNodeKind {
        node_id: String,
        kind: ProofSketchNodeKind,
    },
}

impl fmt::Display for ProofSketchValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateNodeId { node_id } => write!(f, "duplicate sketch node `{node_id}`"),
            Self::UnknownNode { node_id } => write!(f, "unknown sketch node `{node_id}`"),
            Self::Cycle { node_ids } => write!(f, "sketch validator cycle in `{node_ids:?}`"),
            Self::FutureReference { from, to, kind } => write!(
                f,
                "sketch validator future reference `{from}` -> `{to}` ({})",
                kind.wire()
            ),
            Self::DisconnectedRequiredNode { node_id } => {
                write!(f, "disconnected required sketch node `{node_id}`")
            }
            Self::MalformedEdge {
                from,
                to,
                kind,
                reason,
            } => write!(
                f,
                "malformed sketch edge `{from}` -> `{to}` ({}) because {reason}",
                kind.wire()
            ),
            Self::EnvironmentMismatch { expected, actual } => write!(
                f,
                "sketch environment mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::PolicyMismatch { expected, actual } => write!(
                f,
                "sketch policy mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::UnsupportedNodeKind { node_id, kind } => write!(
                f,
                "unsupported sketch node kind `{}` on `{node_id}`",
                kind.wire()
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchMalformedEdgeReason {
    SelfEdge,
    DuplicateEdge,
    ConflictingEdgeKinds,
    ContextFlowMismatch {
        from_output_context_hash: Hash,
        to_input_context_hash: Hash,
    },
    DischargeTargetDoesNotCloseGoal,
}

impl fmt::Display for ProofSketchMalformedEdgeReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SelfEdge => write!(f, "self edges cannot define proof dependencies"),
            Self::DuplicateEdge => write!(f, "duplicate dependency edge"),
            Self::ConflictingEdgeKinds => {
                write!(f, "the same endpoints use multiple edge kinds")
            }
            Self::ContextFlowMismatch {
                from_output_context_hash,
                to_input_context_hash,
            } => write!(
                f,
                "context flow requires from.output_context_hash {} to match to.input_context_hash {}",
                format_hash_string(from_output_context_hash),
                format_hash_string(to_input_context_hash)
            ),
            Self::DischargeTargetDoesNotCloseGoal => {
                write!(f, "discharge edges must target a closing node")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchDisplay {
    pub label: Option<String>,
    pub explanation: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchAdvisory {
    pub display_text: Option<String>,
    pub score: Option<String>,
    pub model_score: Option<String>,
    pub scoring_profile: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchLocalLemmaProposal {
    pub proposal_id: String,
    pub base_sketch_hash: Hash,
    pub source_node_id: String,
    pub statement_hash: Hash,
    pub input_context_hash: Hash,
    pub output_context_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub allowed_premise_hashes: Vec<Hash>,
    pub state: ProofSketchLocalLemmaState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchLocalLemmaState {
    Proposed,
    TypeChecked,
    ProofTask,
    Verified,
    Available,
    Rejected,
}

impl ProofSketchLocalLemmaState {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "proposed" => Some(Self::Proposed),
            "type_checked" => Some(Self::TypeChecked),
            "proof_task" => Some(Self::ProofTask),
            "verified" => Some(Self::Verified),
            "available" => Some(Self::Available),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }

    pub const fn wire(self) -> &'static str {
        match self {
            Self::Proposed => "proposed",
            Self::TypeChecked => "type_checked",
            Self::ProofTask => "proof_task",
            Self::Verified => "verified",
            Self::Available => "available",
            Self::Rejected => "rejected",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionPatch {
    pub base_sketch_hash: Hash,
    pub dependency_invalidation: ProofSketchRevisionDependencyInvalidation,
    pub patch: ProofSketchRevisionPatchKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionDependencyInvalidation {
    AffectedSubDagOnly,
    Broader {
        invalidated_node_ids: Vec<String>,
        diagnostic_hash: Hash,
    },
}

impl ProofSketchRevisionDependencyInvalidation {
    pub const fn wire(&self) -> &'static str {
        match self {
            Self::AffectedSubDagOnly => "affected_subdag_only",
            Self::Broader { .. } => "broader",
        }
    }

    pub fn invalidated_node_ids(&self) -> Vec<String> {
        match self {
            Self::AffectedSubDagOnly => Vec::new(),
            Self::Broader {
                invalidated_node_ids,
                ..
            } => {
                let mut node_ids = invalidated_node_ids.clone();
                node_ids.sort();
                node_ids.dedup();
                node_ids
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionPatchKind {
    ReplaceNode {
        node: Box<ProofSketchNode>,
    },
    SplitNode {
        original_node_id: String,
        replacement_node_ids: Vec<String>,
    },
    MergeNodes {
        merged_node_id: String,
        source_node_ids: Vec<String>,
    },
    InsertLemma {
        node_id: String,
        local_lemma_proposal_hash: Hash,
    },
    RemoveLemma {
        lemma_id: String,
    },
    ChangeStrategy {
        node_id: String,
        strategy_hints: Vec<ProofSketchStrategyHint>,
        repair_profile: Option<ProofSketchRepairProfile>,
    },
    ChangePremiseSet {
        node_id: String,
        premise_hashes: Vec<Hash>,
    },
    IncreaseBudget {
        node_id: String,
        budget: ProofSketchBudget,
    },
    MarkCounterexample {
        node_id: String,
        diagnostic_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionPatchApplicationPolicy {
    pub max_budget: ProofSketchBudget,
    pub allowed_repair_profiles: BTreeSet<ProofSketchRepairProfile>,
    pub allow_premise_expansion: bool,
}

impl Default for ProofSketchRevisionPatchApplicationPolicy {
    fn default() -> Self {
        Self::strict_local()
    }
}

impl ProofSketchRevisionPatchApplicationPolicy {
    pub fn strict_local() -> Self {
        Self {
            max_budget: ProofSketchBudget {
                max_candidates: 1024,
                max_search_nodes: 100_000,
                max_depth: Some(1024),
                max_repair_steps: Some(1024),
            },
            allowed_repair_profiles: [
                ProofSketchRepairProfile::None,
                ProofSketchRepairProfile::LocalRepair,
            ]
            .into_iter()
            .collect(),
            allow_premise_expansion: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionPatchApplication {
    pub base_sketch_hash: Hash,
    pub patch_hash: Hash,
    pub resulting_sketch_hash: Hash,
    pub affected_node_ids: Vec<String>,
    pub invalidated_node_ids: Vec<String>,
    pub counterexample_diagnostic_hash: Option<Hash>,
    pub resulting_sketch: ProofSketch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionPatchError {
    kind: Box<ProofSketchRevisionPatchErrorKind>,
}

impl ProofSketchRevisionPatchError {
    fn new(kind: ProofSketchRevisionPatchErrorKind) -> Self {
        Self {
            kind: Box::new(kind),
        }
    }

    pub const fn kind(&self) -> &ProofSketchRevisionPatchErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSketchRevisionPatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofSketchRevisionPatchError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionPatchErrorKind {
    StaleBaseSketchHash {
        expected: Hash,
        actual: Hash,
    },
    InvalidPatchTarget {
        node_id: String,
    },
    DuplicateInsertedLemma {
        node_id: String,
    },
    ConflictingNodeReplacement {
        node_id: String,
        reason: ProofSketchRevisionConflictReason,
    },
    BroaderDependencyInvalidationRequired {
        operation: &'static str,
        node_ids: Vec<String>,
    },
    UnsupportedStructuralPatch {
        operation: &'static str,
    },
    PolicyExpandingPatchRejected {
        node_id: String,
        reason: ProofSketchRevisionPolicyRejection,
    },
    ValidationFailed {
        source: Box<ProofSketchValidationErrorKind>,
    },
}

impl fmt::Display for ProofSketchRevisionPatchErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleBaseSketchHash { expected, actual } => write!(
                f,
                "stale sketch revision base: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::InvalidPatchTarget { node_id } => {
                write!(f, "invalid sketch revision target `{node_id}`")
            }
            Self::DuplicateInsertedLemma { node_id } => {
                write!(f, "duplicate inserted lemma node `{node_id}`")
            }
            Self::ConflictingNodeReplacement { node_id, reason } => {
                write!(f, "conflicting replacement for sketch node `{node_id}`: {reason}")
            }
            Self::BroaderDependencyInvalidationRequired {
                operation,
                node_ids,
            } => write!(
                f,
                "sketch revision `{operation}` requires declared broader dependency invalidation for {node_ids:?}"
            ),
            Self::UnsupportedStructuralPatch { operation } => {
                write!(f, "sketch revision `{operation}` requires localized revision engine")
            }
            Self::PolicyExpandingPatchRejected { node_id, reason } => write!(
                f,
                "policy-expanding sketch revision rejected for `{node_id}`: {reason}"
            ),
            Self::ValidationFailed { source } => {
                write!(f, "sketch revision produced invalid sketch: {source}")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionConflictReason {
    ReplacementContextChanged,
    ReplacementNodeIdMismatch,
}

impl fmt::Display for ProofSketchRevisionConflictReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReplacementContextChanged => {
                write!(f, "replacement changes input or output context identity")
            }
            Self::ReplacementNodeIdMismatch => {
                write!(f, "replacement node id does not match the affected target")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionPolicyRejection {
    BudgetExceedsPolicy,
    BudgetDoesNotIncrease,
    RepairProfileNotAllowed,
    PremiseExpansionNotAllowed,
}

impl fmt::Display for ProofSketchRevisionPolicyRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BudgetExceedsPolicy => write!(f, "budget exceeds revision policy bounds"),
            Self::BudgetDoesNotIncrease => write!(f, "increase_budget must be monotone"),
            Self::RepairProfileNotAllowed => write!(f, "repair profile expands revision policy"),
            Self::PremiseExpansionNotAllowed => {
                write!(
                    f,
                    "new premise identities require explicit import/premise policy review"
                )
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionEnginePolicy {
    pub patch_policy: ProofSketchRevisionPatchApplicationPolicy,
    pub max_revision_depth: u32,
    pub max_repeated_diagnostic_hash_count: usize,
    pub max_patch_history_len: usize,
}

impl Default for ProofSketchRevisionEnginePolicy {
    fn default() -> Self {
        Self::strict_local()
    }
}

impl ProofSketchRevisionEnginePolicy {
    pub fn strict_local() -> Self {
        Self {
            patch_policy: ProofSketchRevisionPatchApplicationPolicy::strict_local(),
            max_revision_depth: 8,
            max_repeated_diagnostic_hash_count: 1,
            max_patch_history_len: 64,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProofSketchRevisionEngineContext {
    pub evidence: Vec<ProofSketchRevisionEvidence>,
    pub hole_states: Vec<ProofSketchRevisionHoleState>,
    pub parent_integration_records: Vec<ProofSketchRevisionParentIntegrationRecord>,
    pub history: Vec<ProofSketchRevisionHistoryEntry>,
    pub revision_depth: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionEvidence {
    pub kind: ProofSketchRevisionEvidenceKind,
    pub node_id: Option<String>,
    pub hole_id: Option<String>,
    pub diagnostic_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchRevisionEvidenceKind {
    FailedSubgoal,
    UnusedLemma,
    RepeatedDiagnostic,
    StaleHoleSolution,
    OverDecomposition,
}

impl ProofSketchRevisionEvidenceKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FailedSubgoal => "failed_subgoal",
            Self::UnusedLemma => "unused_lemma",
            Self::RepeatedDiagnostic => "repeated_diagnostic",
            Self::StaleHoleSolution => "stale_hole_solution",
            Self::OverDecomposition => "over_decomposition",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionHoleState {
    pub hole_id: String,
    pub owner_node_id: String,
    pub solution_hash: Option<Hash>,
    pub status: ProofSketchRevisionHoleStatus,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchRevisionHoleStatus {
    Pending,
    Completed,
    Failed,
    Stale,
}

impl ProofSketchRevisionHoleStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Completed => "completed",
            Self::Failed => "failed",
            Self::Stale => "stale",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionParentIntegrationRecord {
    pub record_id: String,
    pub required_node_ids: Vec<String>,
    pub completed_hole_ids: Vec<String>,
    pub required_local_lemma_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionHistoryEntry {
    pub patch_hash: Hash,
    pub diagnostic_hash: Option<Hash>,
    pub resulting_sketch_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionDecisionRecord {
    pub base_sketch_hash: Hash,
    pub patch_hash: Hash,
    pub outcome: ProofSketchRevisionDecisionOutcome,
    pub stop_reason: Option<ProofSketchRevisionEngineStopReason>,
    pub revision_depth: u32,
    pub diagnostic_hashes: Vec<Hash>,
    pub invalidated_node_ids: Vec<String>,
    pub preserved_node_ids: Vec<String>,
    pub rescheduled_node_ids: Vec<String>,
    pub invalidated_hole_ids: Vec<String>,
    pub preserved_completed_hole_ids: Vec<String>,
    pub rescheduled_hole_ids: Vec<String>,
    pub preserved_verified_local_lemma_hashes: Vec<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionDecisionOutcome {
    Applied,
    Stopped,
}

impl ProofSketchRevisionDecisionOutcome {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Applied => "applied",
            Self::Stopped => "stopped",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionEngineStopReason {
    MaxRevisionDepth {
        max: u32,
    },
    RepeatedDiagnosticHash {
        diagnostic_hash: Hash,
        count: usize,
        max: usize,
    },
    RepeatedPatchHash {
        patch_hash: Hash,
    },
}

impl ProofSketchRevisionEngineStopReason {
    pub const fn wire(&self) -> &'static str {
        match self {
            Self::MaxRevisionDepth { .. } => "max_revision_depth",
            Self::RepeatedDiagnosticHash { .. } => "repeated_diagnostic_hash",
            Self::RepeatedPatchHash { .. } => "repeated_patch_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionEngineOutput {
    pub decision: ProofSketchRevisionDecisionRecord,
    pub decision_hash: Hash,
    pub application: Option<ProofSketchRevisionPatchApplication>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchRevisionEngineError {
    kind: Box<ProofSketchRevisionEngineErrorKind>,
}

impl ProofSketchRevisionEngineError {
    fn new(kind: ProofSketchRevisionEngineErrorKind) -> Self {
        Self {
            kind: Box::new(kind),
        }
    }

    pub const fn kind(&self) -> &ProofSketchRevisionEngineErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSketchRevisionEngineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofSketchRevisionEngineError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchRevisionEngineErrorKind {
    StaleBaseSketchHash {
        expected: Hash,
        actual: Hash,
    },
    PatchApplicationFailed {
        source: Box<ProofSketchRevisionPatchErrorKind>,
    },
}

impl fmt::Display for ProofSketchRevisionEngineErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleBaseSketchHash { expected, actual } => write!(
                f,
                "stale sketch revision engine base: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::PatchApplicationFailed { source } => {
                write!(
                    f,
                    "sketch revision engine patch application failed: {source}"
                )
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationRecord {
    pub base_sketch_hash: Hash,
    pub kind: ProofSketchMinimizationKind,
    pub target_node_id: Option<String>,
    pub candidate_patch_hash: Hash,
    pub replay_plan_hash: Hash,
    pub verification_result_hash: Hash,
    pub outcome: ProofSketchMinimizationOutcome,
    pub score: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchMinimizationKind {
    RemoveUnusedLocalLemma,
    ReplaceHoleWithExactTerm,
    CollapseRewrites,
    RemoveDuplicatePremiseApplication,
    ExtractSharedBranchSubproof,
    ReduceImportClosure,
}

impl ProofSketchMinimizationKind {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "remove_unused_local_lemma" => Some(Self::RemoveUnusedLocalLemma),
            "replace_hole_with_exact_term" => Some(Self::ReplaceHoleWithExactTerm),
            "collapse_rewrites" => Some(Self::CollapseRewrites),
            "remove_duplicate_premise_application" => Some(Self::RemoveDuplicatePremiseApplication),
            "extract_shared_branch_subproof" => Some(Self::ExtractSharedBranchSubproof),
            "reduce_import_closure" => Some(Self::ReduceImportClosure),
            _ => None,
        }
    }

    pub const fn wire(self) -> &'static str {
        match self {
            Self::RemoveUnusedLocalLemma => "remove_unused_local_lemma",
            Self::ReplaceHoleWithExactTerm => "replace_hole_with_exact_term",
            Self::CollapseRewrites => "collapse_rewrites",
            Self::RemoveDuplicatePremiseApplication => "remove_duplicate_premise_application",
            Self::ExtractSharedBranchSubproof => "extract_shared_branch_subproof",
            Self::ReduceImportClosure => "reduce_import_closure",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchMinimizationOutcome {
    Accepted,
    Rejected,
    StaleBase,
    VerificationFailed,
}

impl ProofSketchMinimizationOutcome {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "accepted" => Some(Self::Accepted),
            "rejected" => Some(Self::Rejected),
            "stale_base" => Some(Self::StaleBase),
            "verification_failed" => Some(Self::VerificationFailed),
            _ => None,
        }
    }

    pub const fn wire(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::StaleBase => "stale_base",
            Self::VerificationFailed => "verification_failed",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationCandidate {
    pub base_sketch_hash: Hash,
    pub kind: ProofSketchMinimizationKind,
    pub target_node_id: Option<String>,
    pub candidate_patch_hash: Hash,
    pub removed_dependencies: Vec<ProofSketchMinimizationRemovedDependency>,
    pub replay_verification: ProofSketchMinimizationReplayVerification,
    pub score: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationRemovedDependency {
    pub kind: ProofSketchMinimizationRemovedDependencyKind,
    pub identity_hash: Hash,
    pub owner_node_id: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchMinimizationRemovedDependencyKind {
    LocalLemma,
    Hole,
    Premise,
    Import,
}

impl ProofSketchMinimizationRemovedDependencyKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::LocalLemma => "local_lemma",
            Self::Hole => "hole",
            Self::Premise => "premise",
            Self::Import => "import",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationReplayVerification {
    pub replay_base_sketch_hash: Hash,
    pub replay_plan_hash: Hash,
    pub verification_result_hash: Hash,
    pub source_free_verification_hash: Hash,
    pub replay_succeeded: bool,
    pub verifier_succeeded: bool,
    pub source_free_succeeded: bool,
    pub certificate_identity_preserved: bool,
    pub candidate_certificate_identity_hash: Option<Hash>,
    pub certificate_import_identity_hashes: Vec<Hash>,
    pub axiom_summary_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationDependencySnapshot {
    pub last_verified_parent_proof_hash: Hash,
    pub verified_certificate_identity_hash: Hash,
    pub final_parent_dependency_hashes: Vec<Hash>,
    pub replay_plan_dependency_hashes: Vec<Hash>,
    pub certificate_import_identity_hashes: Vec<Hash>,
    pub axiom_dependency_hashes: Vec<Hash>,
    pub verified_dependency_identity_hashes: Vec<Hash>,
    pub axiom_summary_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationDecision {
    pub record: ProofSketchMinimizationRecord,
    pub record_hash: Hash,
    pub last_verified_parent_proof_hash: Hash,
    pub candidate_certificate_identity_hash: Hash,
    pub source_free_verification_hash: Hash,
    pub removed_dependency_identity_hashes: Vec<Hash>,
    pub preserved_dependency_identity_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchMinimizationError {
    kind: Box<ProofSketchMinimizationErrorKind>,
    rejected_record: Box<ProofSketchMinimizationRecord>,
    rejected_record_hash: Hash,
    last_verified_parent_proof_hash: Hash,
}

impl ProofSketchMinimizationError {
    fn new(
        kind: ProofSketchMinimizationErrorKind,
        rejected_record: ProofSketchMinimizationRecord,
        last_verified_parent_proof_hash: Hash,
    ) -> Self {
        let rejected_record_hash = proof_sketch_minimization_record_hash(&rejected_record);
        Self {
            kind: Box::new(kind),
            rejected_record: Box::new(rejected_record),
            rejected_record_hash,
            last_verified_parent_proof_hash,
        }
    }

    pub const fn kind(&self) -> &ProofSketchMinimizationErrorKind {
        &self.kind
    }

    pub const fn rejected_record(&self) -> &ProofSketchMinimizationRecord {
        &self.rejected_record
    }

    pub const fn rejected_record_hash(&self) -> Hash {
        self.rejected_record_hash
    }

    pub const fn last_verified_parent_proof_hash(&self) -> Hash {
        self.last_verified_parent_proof_hash
    }
}

impl fmt::Display for ProofSketchMinimizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofSketchMinimizationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchMinimizationErrorKind {
    StaleBaseSketchHash {
        expected: Hash,
        actual: Hash,
    },
    StaleReplayResult {
        expected_base_sketch_hash: Hash,
        replay_base_sketch_hash: Hash,
    },
    ReplayOrVerifyRequired {
        replay_succeeded: bool,
        verifier_succeeded: bool,
    },
    SourceFreeVerificationRequired,
    MissingCandidateCertificateIdentity,
    CertificateChangedWithoutReverification {
        candidate_certificate_identity_hash: Hash,
    },
    CertificateIdentityMismatch {
        expected: Hash,
        actual: Hash,
    },
    CertificateImportIdentityChanged {
        expected: Vec<Hash>,
        actual: Vec<Hash>,
    },
    AxiomProfileChanged {
        expected: Hash,
        actual: Hash,
    },
    RequiredDependencyRemoval {
        dependency: ProofSketchMinimizationRemovedDependency,
        protected_by: ProofSketchMinimizationDependencyUse,
    },
}

impl fmt::Display for ProofSketchMinimizationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleBaseSketchHash { expected, actual } => write!(
                f,
                "stale sketch minimization base: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::StaleReplayResult {
                expected_base_sketch_hash,
                replay_base_sketch_hash,
            } => write!(
                f,
                "stale sketch minimization replay: expected base {}, replay used {}",
                format_hash_string(expected_base_sketch_hash),
                format_hash_string(replay_base_sketch_hash)
            ),
            Self::ReplayOrVerifyRequired {
                replay_succeeded,
                verifier_succeeded,
            } => write!(
                f,
                "sketch minimization requires replay and verifier success; replay={replay_succeeded}, verify={verifier_succeeded}"
            ),
            Self::SourceFreeVerificationRequired => {
                write!(
                    f,
                    "sketch minimization requires source-free verification after replay"
                )
            }
            Self::MissingCandidateCertificateIdentity => {
                write!(f, "sketch minimization is missing candidate certificate identity")
            }
            Self::CertificateChangedWithoutReverification {
                candidate_certificate_identity_hash,
            } => write!(
                f,
                "sketch minimization changed certificate identity {} without source-free re-verification",
                format_hash_string(candidate_certificate_identity_hash)
            ),
            Self::CertificateIdentityMismatch { expected, actual } => write!(
                f,
                "sketch minimization certificate identity mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::CertificateImportIdentityChanged { .. } => write!(
                f,
                "sketch minimization certificate import identity does not match verified dependencies"
            ),
            Self::AxiomProfileChanged { expected, actual } => write!(
                f,
                "sketch minimization changed axiom profile: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::RequiredDependencyRemoval {
                dependency,
                protected_by,
            } => write!(
                f,
                "sketch minimization attempted to remove {} dependency {} protected by {}",
                dependency.kind.wire(),
                format_hash_string(&dependency.identity_hash),
                protected_by.wire()
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSketchMinimizationDependencyUse {
    FinalParentProof,
    ReplayPlan,
    CertificateImportIdentity,
    AxiomSummary,
    VerifiedDependencyIdentityList,
}

impl ProofSketchMinimizationDependencyUse {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FinalParentProof => "final_parent_proof",
            Self::ReplayPlan => "replay_plan",
            Self::CertificateImportIdentity => "certificate_import_identity",
            Self::AxiomSummary => "axiom_summary",
            Self::VerifiedDependencyIdentityList => "verified_dependency_identity_list",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSketchSchemaError {
    path: String,
    kind: ProofSketchSchemaErrorKind,
}

impl ProofSketchSchemaError {
    fn new(path: impl Into<String>, kind: ProofSketchSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ProofSketchSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSketchSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ProofSketchSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSketchSchemaErrorKind {
    JsonParse {
        offset: usize,
    },
    ExpectedObject {
        actual: JsonValueKind,
    },
    ExpectedArray {
        actual: JsonValueKind,
    },
    ExpectedString {
        actual: JsonValueKind,
    },
    ExpectedInteger {
        actual: JsonValueKind,
    },
    DuplicateKey {
        key: String,
    },
    UnknownField {
        field: String,
    },
    MissingField {
        field: &'static str,
    },
    InvalidApiVersion {
        value: String,
    },
    InvalidHash {
        value: String,
    },
    InvalidIdentifier {
        value: String,
    },
    InvalidNodeKind {
        value: String,
    },
    InvalidExpectedEffectKind {
        value: String,
    },
    InvalidStrategyHint {
        value: String,
    },
    InvalidFallbackAction {
        value: String,
    },
    InvalidRepairProfile {
        value: String,
    },
    InvalidGeneralizationPolicy {
        value: String,
    },
    InvalidEdgeKind {
        value: String,
    },
    InvalidLocalLemmaState {
        value: String,
    },
    InvalidRevisionPatchKind {
        value: String,
    },
    InvalidMinimizationKind {
        value: String,
    },
    InvalidMinimizationOutcome {
        value: String,
    },
    InvalidInteger {
        value: String,
    },
    IntegerOutOfRange {
        value: String,
    },
    ArrayLengthOutOfRange {
        min: usize,
        max: usize,
        actual: usize,
    },
    DuplicateNodeId {
        node_id: String,
    },
    DuplicateProposalId {
        proposal_id: String,
    },
    DuplicateStrategyHint {
        value: String,
    },
    DuplicatePremiseHash {
        value: String,
    },
    DuplicateEdge {
        from: String,
        to: String,
        kind: String,
    },
    DuplicatePatchNodeId {
        node_id: String,
    },
    UnknownNodeReference {
        node_id: String,
    },
    UnknownProposalReference {
        proposal_id: String,
    },
    StringLengthOutOfRange {
        min: usize,
        max: usize,
        actual: usize,
    },
}

impl fmt::Display for ProofSketchSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "json parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedInteger { actual } => write!(f, "expected integer, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidIdentifier { value } => write!(f, "invalid identifier `{value}`"),
            Self::InvalidNodeKind { value } => write!(f, "invalid node kind `{value}`"),
            Self::InvalidExpectedEffectKind { value } => {
                write!(f, "invalid expected effect kind `{value}`")
            }
            Self::InvalidStrategyHint { value } => write!(f, "invalid strategy hint `{value}`"),
            Self::InvalidFallbackAction { value } => {
                write!(f, "invalid fallback action `{value}`")
            }
            Self::InvalidRepairProfile { value } => {
                write!(f, "invalid repair profile `{value}`")
            }
            Self::InvalidGeneralizationPolicy { value } => {
                write!(f, "invalid generalization policy `{value}`")
            }
            Self::InvalidEdgeKind { value } => write!(f, "invalid edge kind `{value}`"),
            Self::InvalidLocalLemmaState { value } => {
                write!(f, "invalid local lemma state `{value}`")
            }
            Self::InvalidRevisionPatchKind { value } => {
                write!(f, "invalid revision patch kind `{value}`")
            }
            Self::InvalidMinimizationKind { value } => {
                write!(f, "invalid minimization kind `{value}`")
            }
            Self::InvalidMinimizationOutcome { value } => {
                write!(f, "invalid minimization outcome `{value}`")
            }
            Self::InvalidInteger { value } => write!(f, "invalid integer `{value}`"),
            Self::IntegerOutOfRange { value } => write!(f, "integer out of range `{value}`"),
            Self::ArrayLengthOutOfRange { min, max, actual } => write!(
                f,
                "array length {actual} is outside allowed range {min}..={max}"
            ),
            Self::DuplicateNodeId { node_id } => write!(f, "duplicate node id `{node_id}`"),
            Self::DuplicateProposalId { proposal_id } => {
                write!(f, "duplicate proposal id `{proposal_id}`")
            }
            Self::DuplicateStrategyHint { value } => {
                write!(f, "duplicate strategy hint `{value}`")
            }
            Self::DuplicatePremiseHash { value } => write!(f, "duplicate premise hash `{value}`"),
            Self::DuplicateEdge { from, to, kind } => {
                write!(f, "duplicate edge `{from}` -> `{to}` ({kind})")
            }
            Self::DuplicatePatchNodeId { node_id } => {
                write!(f, "duplicate revision patch node id `{node_id}`")
            }
            Self::UnknownNodeReference { node_id } => {
                write!(f, "unknown node reference `{node_id}`")
            }
            Self::UnknownProposalReference { proposal_id } => {
                write!(f, "unknown proposal reference `{proposal_id}`")
            }
            Self::StringLengthOutOfRange { min, max, actual } => write!(
                f,
                "string length {actual} is outside allowed range {min}..={max}"
            ),
        }
    }
}

pub fn parse_proof_sketch(source: &str) -> Result<ProofSketch, ProofSketchSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;

    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != PROOF_SKETCH_API_VERSION {
        return Err(ProofSketchSchemaError::new(
            "$.api_version",
            ProofSketchSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    let sketch_id = required_hash(&root, "sketch_id", "$")?;
    let target_statement_identity =
        parse_target_statement_identity(required_value(&root, "target_statement_identity", "$")?)?;
    let environment_hash = required_hash(&root, "environment_hash", "$")?;
    let policy_hash = required_hash(&root, "policy_hash", "$")?;
    let mut sublemma_statement_proposals = parse_sublemma_statement_proposals(required_value(
        &root,
        "sublemma_statement_proposals",
        "$",
    )?)?;
    let mut nodes = parse_nodes(required_value(&root, "nodes", "$")?)?;
    let mut edges = parse_edges(required_value(&root, "edges", "$")?)?;
    let advisory = optional_value(&root, "advisory")
        .map(|value| parse_advisory(value, "$.advisory"))
        .transpose()?;

    sublemma_statement_proposals.sort_by(|left, right| left.proposal_id.cmp(&right.proposal_id));
    nodes.sort_by(|left, right| left.node_id.cmp(&right.node_id));
    edges.sort_by(|left, right| {
        (&left.from, &left.to, left.kind).cmp(&(&right.from, &right.to, right.kind))
    });

    validate_references(&sublemma_statement_proposals, &nodes, &edges)?;

    Ok(ProofSketch {
        api_version,
        sketch_id,
        target_statement_identity,
        environment_hash,
        policy_hash,
        sublemma_statement_proposals,
        nodes,
        edges,
        advisory,
    })
}

pub fn parse_proof_sketch_local_lemma_proposal(
    source: &str,
) -> Result<ProofSketchLocalLemmaProposal, ProofSketchSchemaError> {
    let document = parse_json_document(source)?;
    parse_local_lemma_proposal_value(document.root(), "$")
}

pub fn parse_proof_sketch_revision_patch(
    source: &str,
) -> Result<ProofSketchRevisionPatch, ProofSketchSchemaError> {
    let document = parse_json_document(source)?;
    parse_revision_patch_value(document.root(), "$")
}

pub fn parse_proof_sketch_minimization_record(
    source: &str,
) -> Result<ProofSketchMinimizationRecord, ProofSketchSchemaError> {
    let document = parse_json_document(source)?;
    parse_minimization_record_value(document.root(), "$")
}

pub fn validate_proof_sketch(
    sketch: &ProofSketch,
) -> Result<ProofSketchValidationReport, ProofSketchValidationError> {
    validate_proof_sketch_with_profile(sketch, &ProofSketchValidationProfile::default())
}

pub fn validate_proof_sketch_with_profile(
    sketch: &ProofSketch,
    profile: &ProofSketchValidationProfile,
) -> Result<ProofSketchValidationReport, ProofSketchValidationError> {
    if let Some(expected) = profile.expected_environment_hash {
        if expected != sketch.environment_hash {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::EnvironmentMismatch {
                    expected,
                    actual: sketch.environment_hash,
                },
            ));
        }
    }
    if let Some(expected) = profile.expected_policy_hash {
        if expected != sketch.policy_hash {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::PolicyMismatch {
                    expected,
                    actual: sketch.policy_hash,
                },
            ));
        }
    }

    let node_by_id = validate_sketch_nodes(sketch, profile)?;
    let edge_graph = validate_sketch_edges(sketch, &node_by_id)?;
    let topological_node_ids = validate_sketch_dag(&node_by_id, &edge_graph)?;
    validate_sketch_weak_connectivity(&node_by_id, &edge_graph)?;

    let nodes = topological_node_ids
        .iter()
        .map(|node_id| {
            let node = node_by_id
                .get(node_id.as_str())
                .expect("validated topological node should exist");
            ProofSketchValidatedNode {
                node_id: node_id.clone(),
                kind: node.kind,
                predecessor_node_ids: edge_graph
                    .incoming
                    .get(node_id)
                    .map(sorted_strings)
                    .unwrap_or_default(),
                successor_node_ids: edge_graph
                    .outgoing
                    .get(node_id)
                    .map(sorted_strings)
                    .unwrap_or_default(),
            }
        })
        .collect();
    let edges = sketch
        .edges
        .iter()
        .map(|edge| ProofSketchValidatedEdge {
            from: edge.from.clone(),
            to: edge.to.clone(),
            kind: edge.kind,
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let root_node_ids = edge_graph
        .incoming
        .iter()
        .filter_map(|(node_id, predecessors)| {
            if predecessors.is_empty() {
                Some(node_id.clone())
            } else {
                None
            }
        })
        .collect();
    let terminal_node_ids = edge_graph
        .outgoing
        .iter()
        .filter_map(|(node_id, successors)| {
            if successors.is_empty() {
                Some(node_id.clone())
            } else {
                None
            }
        })
        .collect();

    Ok(ProofSketchValidationReport {
        sketch_hash: proof_sketch_hash(sketch),
        environment_hash: sketch.environment_hash,
        policy_hash: sketch.policy_hash,
        topological_node_ids,
        root_node_ids,
        terminal_node_ids,
        nodes,
        edges,
    })
}

pub fn proof_sketch_canonical_identity_bytes(sketch: &ProofSketch) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKETCH_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &sketch.api_version);
    encode_string_to(&mut out, "target_statement_identity");
    encode_target_statement_identity_to(&mut out, &sketch.target_statement_identity);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &sketch.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &sketch.policy_hash);
    encode_string_to(&mut out, "sublemma_statement_proposals");
    encode_len_to(&mut out, sketch.sublemma_statement_proposals.len());
    for proposal in &sketch.sublemma_statement_proposals {
        encode_sublemma_statement_proposal_to(&mut out, proposal);
    }
    encode_string_to(&mut out, "nodes");
    encode_len_to(&mut out, sketch.nodes.len());
    for node in &sketch.nodes {
        encode_node_to(&mut out, node);
    }
    encode_string_to(&mut out, "edges");
    encode_len_to(&mut out, sketch.edges.len());
    for edge in &sketch.edges {
        encode_edge_to(&mut out, edge);
    }
    out
}

pub fn proof_sketch_hash(sketch: &ProofSketch) -> Hash {
    let digest = Sha256::digest(proof_sketch_canonical_identity_bytes(sketch));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_sketch_hash_string(sketch: &ProofSketch) -> String {
    format_hash_string(&proof_sketch_hash(sketch))
}

struct ProofSketchEdgeGraph {
    incoming: BTreeMap<String, BTreeSet<String>>,
    outgoing: BTreeMap<String, BTreeSet<String>>,
}

fn validate_sketch_nodes<'a>(
    sketch: &'a ProofSketch,
    profile: &ProofSketchValidationProfile,
) -> Result<BTreeMap<&'a str, &'a ProofSketchNode>, ProofSketchValidationError> {
    let mut node_by_id = BTreeMap::new();
    for node in &sketch.nodes {
        if !profile.supported_node_kinds.contains(&node.kind) {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::UnsupportedNodeKind {
                    node_id: node.node_id.clone(),
                    kind: node.kind,
                },
            ));
        }
        if node_by_id.insert(node.node_id.as_str(), node).is_some() {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::DuplicateNodeId {
                    node_id: node.node_id.clone(),
                },
            ));
        }
    }
    for node in &sketch.nodes {
        if let Some(fallback_node_id) = &node.fallback_policy.fallback_node_id {
            if !node_by_id.contains_key(fallback_node_id.as_str()) {
                return Err(ProofSketchValidationError::new(
                    ProofSketchValidationErrorKind::UnknownNode {
                        node_id: fallback_node_id.clone(),
                    },
                ));
            }
        }
    }
    Ok(node_by_id)
}

fn validate_sketch_edges(
    sketch: &ProofSketch,
    node_by_id: &BTreeMap<&str, &ProofSketchNode>,
) -> Result<ProofSketchEdgeGraph, ProofSketchValidationError> {
    let mut incoming = BTreeMap::new();
    let mut outgoing = BTreeMap::new();
    for node in &sketch.nodes {
        incoming.insert(node.node_id.clone(), BTreeSet::new());
        outgoing.insert(node.node_id.clone(), BTreeSet::new());
    }

    let mut seen_edges = BTreeSet::new();
    let mut seen_pairs = BTreeMap::new();
    for edge in &sketch.edges {
        if edge.from == edge.to {
            return Err(malformed_edge(
                edge,
                ProofSketchMalformedEdgeReason::SelfEdge,
            ));
        }
        let Some(from_node) = node_by_id.get(edge.from.as_str()) else {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::UnknownNode {
                    node_id: edge.from.clone(),
                },
            ));
        };
        let Some(to_node) = node_by_id.get(edge.to.as_str()) else {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::UnknownNode {
                    node_id: edge.to.clone(),
                },
            ));
        };
        if !seen_edges.insert((edge.from.clone(), edge.to.clone(), edge.kind)) {
            return Err(malformed_edge(
                edge,
                ProofSketchMalformedEdgeReason::DuplicateEdge,
            ));
        }
        if let Some(previous_kind) =
            seen_pairs.insert((edge.from.clone(), edge.to.clone()), edge.kind)
        {
            if previous_kind != edge.kind {
                return Err(malformed_edge(
                    edge,
                    ProofSketchMalformedEdgeReason::ConflictingEdgeKinds,
                ));
            }
        }

        if to_node.output_context_hash == from_node.input_context_hash {
            return Err(ProofSketchValidationError::new(
                ProofSketchValidationErrorKind::FutureReference {
                    from: edge.from.clone(),
                    to: edge.to.clone(),
                    kind: edge.kind,
                },
            ));
        }

        match edge.kind {
            ProofSketchEdgeKind::DependsOn => {}
            ProofSketchEdgeKind::Feeds => {
                if from_node.output_context_hash != to_node.input_context_hash {
                    return Err(malformed_edge(
                        edge,
                        ProofSketchMalformedEdgeReason::ContextFlowMismatch {
                            from_output_context_hash: from_node.output_context_hash,
                            to_input_context_hash: to_node.input_context_hash,
                        },
                    ));
                }
            }
            ProofSketchEdgeKind::Discharges => {
                if !is_closing_node(to_node) {
                    return Err(malformed_edge(
                        edge,
                        ProofSketchMalformedEdgeReason::DischargeTargetDoesNotCloseGoal,
                    ));
                }
            }
        }

        outgoing
            .get_mut(&edge.from)
            .expect("validated edge source should exist")
            .insert(edge.to.clone());
        incoming
            .get_mut(&edge.to)
            .expect("validated edge target should exist")
            .insert(edge.from.clone());
    }

    Ok(ProofSketchEdgeGraph { incoming, outgoing })
}

fn validate_sketch_dag(
    node_by_id: &BTreeMap<&str, &ProofSketchNode>,
    edge_graph: &ProofSketchEdgeGraph,
) -> Result<Vec<String>, ProofSketchValidationError> {
    let mut incoming_counts = edge_graph
        .incoming
        .iter()
        .map(|(node_id, predecessors)| (node_id.clone(), predecessors.len()))
        .collect::<BTreeMap<_, _>>();
    let mut ready = incoming_counts
        .iter()
        .filter_map(|(node_id, count)| {
            if *count == 0 {
                Some(node_id.clone())
            } else {
                None
            }
        })
        .collect::<BTreeSet<_>>();
    let mut topological_node_ids = Vec::with_capacity(node_by_id.len());

    while let Some(node_id) = ready.iter().next().cloned() {
        ready.remove(&node_id);
        topological_node_ids.push(node_id.clone());
        if let Some(successors) = edge_graph.outgoing.get(&node_id) {
            for successor in successors {
                let count = incoming_counts
                    .get_mut(successor)
                    .expect("validated successor should have indegree");
                *count -= 1;
                if *count == 0 {
                    ready.insert(successor.clone());
                }
            }
        }
    }

    if topological_node_ids.len() != node_by_id.len() {
        let node_ids = incoming_counts
            .into_iter()
            .filter_map(|(node_id, count)| if count > 0 { Some(node_id) } else { None })
            .collect();
        return Err(ProofSketchValidationError::new(
            ProofSketchValidationErrorKind::Cycle { node_ids },
        ));
    }

    Ok(topological_node_ids)
}

fn validate_sketch_weak_connectivity(
    node_by_id: &BTreeMap<&str, &ProofSketchNode>,
    edge_graph: &ProofSketchEdgeGraph,
) -> Result<(), ProofSketchValidationError> {
    if node_by_id.len() <= 1 {
        return Ok(());
    }

    let Some(start) = edge_graph.outgoing.keys().next().cloned() else {
        return Ok(());
    };
    let mut visited = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(node_id) = stack.pop() {
        if !visited.insert(node_id.clone()) {
            continue;
        }
        if let Some(successors) = edge_graph.outgoing.get(&node_id) {
            stack.extend(successors.iter().cloned());
        }
        if let Some(predecessors) = edge_graph.incoming.get(&node_id) {
            stack.extend(predecessors.iter().cloned());
        }
    }

    if visited.len() != node_by_id.len() {
        let node_id = node_by_id
            .keys()
            .find_map(|node_id| {
                if visited.contains(*node_id) {
                    None
                } else {
                    Some((*node_id).to_owned())
                }
            })
            .expect("disconnected graph should expose an unvisited node");
        return Err(ProofSketchValidationError::new(
            ProofSketchValidationErrorKind::DisconnectedRequiredNode { node_id },
        ));
    }

    Ok(())
}

fn malformed_edge(
    edge: &ProofSketchEdge,
    reason: ProofSketchMalformedEdgeReason,
) -> ProofSketchValidationError {
    ProofSketchValidationError::new(ProofSketchValidationErrorKind::MalformedEdge {
        from: edge.from.clone(),
        to: edge.to.clone(),
        kind: edge.kind,
        reason,
    })
}

fn is_closing_node(node: &ProofSketchNode) -> bool {
    node.expected_effect.kind == ProofSketchExpectedEffectKind::ClosesGoal
        && node.expected_effect.goal_delta < 0
}

fn sorted_strings(values: &BTreeSet<String>) -> Vec<String> {
    values.iter().cloned().collect()
}

pub fn proof_sketch_local_lemma_proposal_canonical_identity_bytes(
    proposal: &ProofSketchLocalLemmaProposal,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKETCH_LOCAL_LEMMA_PROPOSAL_HASH_DOMAIN);
    encode_string_to(&mut out, "proposal_id");
    encode_string_to(&mut out, &proposal.proposal_id);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &proposal.base_sketch_hash);
    encode_string_to(&mut out, "source_node_id");
    encode_string_to(&mut out, &proposal.source_node_id);
    encode_string_to(&mut out, "statement_hash");
    encode_hash_to(&mut out, &proposal.statement_hash);
    encode_string_to(&mut out, "input_context_hash");
    encode_hash_to(&mut out, &proposal.input_context_hash);
    encode_string_to(&mut out, "output_context_hash");
    encode_hash_to(&mut out, &proposal.output_context_hash);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &proposal.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &proposal.policy_hash);
    encode_string_to(&mut out, "allowed_premise_hashes");
    let mut premise_hashes = proposal.allowed_premise_hashes.clone();
    premise_hashes.sort();
    premise_hashes.dedup();
    encode_len_to(&mut out, premise_hashes.len());
    for hash in &premise_hashes {
        encode_hash_to(&mut out, hash);
    }
    out
}

pub fn proof_sketch_local_lemma_proposal_hash(proposal: &ProofSketchLocalLemmaProposal) -> Hash {
    let digest = Sha256::digest(proof_sketch_local_lemma_proposal_canonical_identity_bytes(
        proposal,
    ));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_sketch_local_lemma_proposal_hash_string(
    proposal: &ProofSketchLocalLemmaProposal,
) -> String {
    format_hash_string(&proof_sketch_local_lemma_proposal_hash(proposal))
}

pub fn proof_sketch_revision_patch_canonical_identity_bytes(
    patch: &ProofSketchRevisionPatch,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKETCH_REVISION_PATCH_HASH_DOMAIN);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &patch.base_sketch_hash);
    encode_string_to(&mut out, "dependency_invalidation");
    encode_revision_dependency_invalidation_to(&mut out, &patch.dependency_invalidation);
    encode_string_to(&mut out, "patch");
    encode_revision_patch_kind_to(&mut out, &patch.patch);
    out
}

pub fn proof_sketch_revision_patch_hash(patch: &ProofSketchRevisionPatch) -> Hash {
    let digest = Sha256::digest(proof_sketch_revision_patch_canonical_identity_bytes(patch));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_sketch_revision_patch_hash_string(patch: &ProofSketchRevisionPatch) -> String {
    format_hash_string(&proof_sketch_revision_patch_hash(patch))
}

pub fn proof_sketch_revision_decision_canonical_identity_bytes(
    decision: &ProofSketchRevisionDecisionRecord,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKETCH_REVISION_DECISION_HASH_DOMAIN);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &decision.base_sketch_hash);
    encode_string_to(&mut out, "patch_hash");
    encode_hash_to(&mut out, &decision.patch_hash);
    encode_string_to(&mut out, "outcome");
    encode_string_to(&mut out, decision.outcome.wire());
    encode_string_to(&mut out, "stop_reason");
    encode_revision_engine_stop_reason_to(&mut out, decision.stop_reason.as_ref());
    encode_string_to(&mut out, "revision_depth");
    encode_u64_to(&mut out, u64::from(decision.revision_depth));
    encode_string_to(&mut out, "diagnostic_hashes");
    encode_hash_set_to(&mut out, &decision.diagnostic_hashes);
    encode_string_to(&mut out, "invalidated_node_ids");
    encode_string_set_to(&mut out, &decision.invalidated_node_ids);
    encode_string_to(&mut out, "preserved_node_ids");
    encode_string_set_to(&mut out, &decision.preserved_node_ids);
    encode_string_to(&mut out, "rescheduled_node_ids");
    encode_string_set_to(&mut out, &decision.rescheduled_node_ids);
    encode_string_to(&mut out, "invalidated_hole_ids");
    encode_string_set_to(&mut out, &decision.invalidated_hole_ids);
    encode_string_to(&mut out, "preserved_completed_hole_ids");
    encode_string_set_to(&mut out, &decision.preserved_completed_hole_ids);
    encode_string_to(&mut out, "rescheduled_hole_ids");
    encode_string_set_to(&mut out, &decision.rescheduled_hole_ids);
    encode_string_to(&mut out, "preserved_verified_local_lemma_hashes");
    encode_hash_set_to(&mut out, &decision.preserved_verified_local_lemma_hashes);
    out
}

pub fn proof_sketch_revision_decision_hash(decision: &ProofSketchRevisionDecisionRecord) -> Hash {
    let digest = Sha256::digest(proof_sketch_revision_decision_canonical_identity_bytes(
        decision,
    ));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_sketch_revision_decision_hash_string(
    decision: &ProofSketchRevisionDecisionRecord,
) -> String {
    format_hash_string(&proof_sketch_revision_decision_hash(decision))
}

pub fn run_proof_sketch_revision_engine(
    sketch: &ProofSketch,
    patch: &ProofSketchRevisionPatch,
    context: &ProofSketchRevisionEngineContext,
    policy: &ProofSketchRevisionEnginePolicy,
) -> Result<ProofSketchRevisionEngineOutput, ProofSketchRevisionEngineError> {
    let actual_base_sketch_hash = proof_sketch_hash(sketch);
    if patch.base_sketch_hash != actual_base_sketch_hash {
        return Err(ProofSketchRevisionEngineError::new(
            ProofSketchRevisionEngineErrorKind::StaleBaseSketchHash {
                expected: patch.base_sketch_hash,
                actual: actual_base_sketch_hash,
            },
        ));
    }

    let patch_hash = proof_sketch_revision_patch_hash(patch);
    let diagnostic_hashes = revision_engine_diagnostic_hashes(context);
    let stop_reason = revision_engine_stop_reason(patch_hash, &diagnostic_hashes, context, policy);
    let decision = revision_engine_decision(
        sketch,
        patch,
        actual_base_sketch_hash,
        patch_hash,
        context,
        stop_reason.clone(),
    );
    let decision_hash = proof_sketch_revision_decision_hash(&decision);
    if stop_reason.is_some() {
        return Ok(ProofSketchRevisionEngineOutput {
            decision,
            decision_hash,
            application: None,
        });
    }

    let application = apply_proof_sketch_revision_patch(sketch, patch, &policy.patch_policy)
        .map_err(|error| {
            ProofSketchRevisionEngineError::new(
                ProofSketchRevisionEngineErrorKind::PatchApplicationFailed {
                    source: Box::new(error.kind().clone()),
                },
            )
        })?;

    Ok(ProofSketchRevisionEngineOutput {
        decision,
        decision_hash,
        application: Some(application),
    })
}

pub fn apply_proof_sketch_revision_patch(
    sketch: &ProofSketch,
    patch: &ProofSketchRevisionPatch,
    policy: &ProofSketchRevisionPatchApplicationPolicy,
) -> Result<ProofSketchRevisionPatchApplication, ProofSketchRevisionPatchError> {
    let actual_base_sketch_hash = proof_sketch_hash(sketch);
    if patch.base_sketch_hash != actual_base_sketch_hash {
        return Err(ProofSketchRevisionPatchError::new(
            ProofSketchRevisionPatchErrorKind::StaleBaseSketchHash {
                expected: patch.base_sketch_hash,
                actual: actual_base_sketch_hash,
            },
        ));
    }

    let invalidated_node_ids = patch.dependency_invalidation.invalidated_node_ids();
    for node_id in &invalidated_node_ids {
        require_node(sketch, node_id)?;
    }

    let mut resulting_sketch = sketch.clone();
    let mut affected_node_ids = patch_affected_node_ids(&patch.patch);
    let mut counterexample_diagnostic_hash = None;

    match &patch.patch {
        ProofSketchRevisionPatchKind::ReplaceNode { node } => {
            let existing = require_node(sketch, &node.node_id)?;
            validate_node_revision_policy(node, existing, policy)?;
            if node.node_id != existing.node_id {
                return Err(ProofSketchRevisionPatchError::new(
                    ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                        node_id: node.node_id.clone(),
                        reason: ProofSketchRevisionConflictReason::ReplacementNodeIdMismatch,
                    },
                ));
            }
            if matches!(
                patch.dependency_invalidation,
                ProofSketchRevisionDependencyInvalidation::AffectedSubDagOnly
            ) && (node.input_context_hash != existing.input_context_hash
                || node.output_context_hash != existing.output_context_hash)
            {
                return Err(ProofSketchRevisionPatchError::new(
                    ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                        node_id: node.node_id.clone(),
                        reason: ProofSketchRevisionConflictReason::ReplacementContextChanged,
                    },
                ));
            }
            replace_node(&mut resulting_sketch, node.as_ref().clone());
        }
        ProofSketchRevisionPatchKind::ChangeStrategy {
            node_id,
            strategy_hints,
            repair_profile,
        } => {
            let node = require_node_mut(&mut resulting_sketch, node_id)?;
            if let Some(profile) = repair_profile {
                if !policy.allowed_repair_profiles.contains(profile) {
                    return Err(policy_rejection(
                        node_id,
                        ProofSketchRevisionPolicyRejection::RepairProfileNotAllowed,
                    ));
                }
            }
            node.strategy_hints = sorted_dedup_strategy_hints(strategy_hints);
            node.fallback_policy.repair_profile = *repair_profile;
        }
        ProofSketchRevisionPatchKind::ChangePremiseSet {
            node_id,
            premise_hashes,
        } => {
            let node = require_node_mut(&mut resulting_sketch, node_id)?;
            if !policy.allow_premise_expansion {
                let existing = node.premise_hashes.iter().copied().collect::<BTreeSet<_>>();
                if premise_hashes.iter().any(|hash| !existing.contains(hash)) {
                    return Err(policy_rejection(
                        node_id,
                        ProofSketchRevisionPolicyRejection::PremiseExpansionNotAllowed,
                    ));
                }
            }
            node.premise_hashes = sorted_dedup_hashes(premise_hashes);
        }
        ProofSketchRevisionPatchKind::IncreaseBudget { node_id, budget } => {
            let node = require_node_mut(&mut resulting_sketch, node_id)?;
            if !budget_is_monotone_increase(&node.budget, budget) {
                return Err(policy_rejection(
                    node_id,
                    ProofSketchRevisionPolicyRejection::BudgetDoesNotIncrease,
                ));
            }
            if !budget_within_policy(budget, &policy.max_budget) {
                return Err(policy_rejection(
                    node_id,
                    ProofSketchRevisionPolicyRejection::BudgetExceedsPolicy,
                ));
            }
            node.budget = budget.clone();
        }
        ProofSketchRevisionPatchKind::MarkCounterexample {
            node_id,
            diagnostic_hash,
        } => {
            require_node(sketch, node_id)?;
            counterexample_diagnostic_hash = Some(*diagnostic_hash);
        }
        ProofSketchRevisionPatchKind::InsertLemma {
            node_id,
            local_lemma_proposal_hash: _,
        } => {
            if find_node(sketch, node_id).is_some() {
                return Err(ProofSketchRevisionPatchError::new(
                    ProofSketchRevisionPatchErrorKind::DuplicateInsertedLemma {
                        node_id: node_id.clone(),
                    },
                ));
            }
            return Err(ProofSketchRevisionPatchError::new(
                ProofSketchRevisionPatchErrorKind::UnsupportedStructuralPatch {
                    operation: "insert_lemma",
                },
            ));
        }
        ProofSketchRevisionPatchKind::RemoveLemma { lemma_id } => {
            require_node(sketch, lemma_id)?;
            require_broader_invalidation(
                "remove_lemma",
                std::slice::from_ref(lemma_id),
                &patch.dependency_invalidation,
            )?;
            return Err(ProofSketchRevisionPatchError::new(
                ProofSketchRevisionPatchErrorKind::UnsupportedStructuralPatch {
                    operation: "remove_lemma",
                },
            ));
        }
        ProofSketchRevisionPatchKind::SplitNode {
            original_node_id,
            replacement_node_ids,
        } => {
            require_node(sketch, original_node_id)?;
            for replacement_node_id in replacement_node_ids {
                if find_node(sketch, replacement_node_id).is_some() {
                    return Err(ProofSketchRevisionPatchError::new(
                        ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                            node_id: replacement_node_id.clone(),
                            reason: ProofSketchRevisionConflictReason::ReplacementNodeIdMismatch,
                        },
                    ));
                }
            }
            require_broader_invalidation(
                "split_node",
                std::slice::from_ref(original_node_id),
                &patch.dependency_invalidation,
            )?;
            return Err(ProofSketchRevisionPatchError::new(
                ProofSketchRevisionPatchErrorKind::UnsupportedStructuralPatch {
                    operation: "split_node",
                },
            ));
        }
        ProofSketchRevisionPatchKind::MergeNodes {
            merged_node_id,
            source_node_ids,
        } => {
            for source_node_id in source_node_ids {
                require_node(sketch, source_node_id)?;
            }
            if find_node(sketch, merged_node_id).is_some()
                && !source_node_ids
                    .iter()
                    .any(|node_id| node_id == merged_node_id)
            {
                return Err(ProofSketchRevisionPatchError::new(
                    ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                        node_id: merged_node_id.clone(),
                        reason: ProofSketchRevisionConflictReason::ReplacementNodeIdMismatch,
                    },
                ));
            }
            require_broader_invalidation(
                "merge_nodes",
                source_node_ids,
                &patch.dependency_invalidation,
            )?;
            return Err(ProofSketchRevisionPatchError::new(
                ProofSketchRevisionPatchErrorKind::UnsupportedStructuralPatch {
                    operation: "merge_nodes",
                },
            ));
        }
    }

    affected_node_ids.sort();
    affected_node_ids.dedup();
    sort_sketch_for_identity(&mut resulting_sketch);
    validate_proof_sketch_with_profile(
        &resulting_sketch,
        &ProofSketchValidationProfile::strict(sketch.environment_hash, sketch.policy_hash),
    )
    .map_err(|error| {
        ProofSketchRevisionPatchError::new(ProofSketchRevisionPatchErrorKind::ValidationFailed {
            source: Box::new(error.kind().clone()),
        })
    })?;

    Ok(ProofSketchRevisionPatchApplication {
        base_sketch_hash: actual_base_sketch_hash,
        patch_hash: proof_sketch_revision_patch_hash(patch),
        resulting_sketch_hash: proof_sketch_hash(&resulting_sketch),
        affected_node_ids,
        invalidated_node_ids,
        counterexample_diagnostic_hash,
        resulting_sketch,
    })
}

pub fn proof_sketch_minimization_record_canonical_identity_bytes(
    record: &ProofSketchMinimizationRecord,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKETCH_MINIMIZATION_RECORD_HASH_DOMAIN);
    encode_string_to(&mut out, "base_sketch_hash");
    encode_hash_to(&mut out, &record.base_sketch_hash);
    encode_string_to(&mut out, "kind");
    encode_string_to(&mut out, record.kind.wire());
    encode_option_string_to(&mut out, "target_node_id", record.target_node_id.as_deref());
    encode_string_to(&mut out, "candidate_patch_hash");
    encode_hash_to(&mut out, &record.candidate_patch_hash);
    encode_string_to(&mut out, "replay_plan_hash");
    encode_hash_to(&mut out, &record.replay_plan_hash);
    encode_string_to(&mut out, "verification_result_hash");
    encode_hash_to(&mut out, &record.verification_result_hash);
    encode_string_to(&mut out, "outcome");
    encode_string_to(&mut out, record.outcome.wire());
    out
}

pub fn proof_sketch_minimization_record_hash(record: &ProofSketchMinimizationRecord) -> Hash {
    let digest = Sha256::digest(proof_sketch_minimization_record_canonical_identity_bytes(
        record,
    ));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_sketch_minimization_record_hash_string(
    record: &ProofSketchMinimizationRecord,
) -> String {
    format_hash_string(&proof_sketch_minimization_record_hash(record))
}

pub fn validate_proof_sketch_minimization_step(
    sketch: &ProofSketch,
    candidate: &ProofSketchMinimizationCandidate,
    dependencies: &ProofSketchMinimizationDependencySnapshot,
) -> Result<ProofSketchMinimizationDecision, ProofSketchMinimizationError> {
    let actual_base_sketch_hash = proof_sketch_hash(sketch);
    if candidate.base_sketch_hash != actual_base_sketch_hash {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::StaleBase,
            ProofSketchMinimizationErrorKind::StaleBaseSketchHash {
                expected: candidate.base_sketch_hash,
                actual: actual_base_sketch_hash,
            },
        ));
    }

    if candidate.replay_verification.replay_base_sketch_hash != actual_base_sketch_hash {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::StaleBase,
            ProofSketchMinimizationErrorKind::StaleReplayResult {
                expected_base_sketch_hash: actual_base_sketch_hash,
                replay_base_sketch_hash: candidate.replay_verification.replay_base_sketch_hash,
            },
        ));
    }

    if !candidate.replay_verification.replay_succeeded
        || !candidate.replay_verification.verifier_succeeded
    {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::VerificationFailed,
            ProofSketchMinimizationErrorKind::ReplayOrVerifyRequired {
                replay_succeeded: candidate.replay_verification.replay_succeeded,
                verifier_succeeded: candidate.replay_verification.verifier_succeeded,
            },
        ));
    }

    let Some(candidate_certificate_identity_hash) = candidate
        .replay_verification
        .candidate_certificate_identity_hash
    else {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::VerificationFailed,
            ProofSketchMinimizationErrorKind::MissingCandidateCertificateIdentity,
        ));
    };

    if !candidate.replay_verification.certificate_identity_preserved
        && !candidate.replay_verification.source_free_succeeded
    {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::VerificationFailed,
            ProofSketchMinimizationErrorKind::CertificateChangedWithoutReverification {
                candidate_certificate_identity_hash,
            },
        ));
    }

    if !candidate.replay_verification.source_free_succeeded {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::VerificationFailed,
            ProofSketchMinimizationErrorKind::SourceFreeVerificationRequired,
        ));
    }

    if candidate.replay_verification.axiom_summary_hash != dependencies.axiom_summary_hash {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::Rejected,
            ProofSketchMinimizationErrorKind::AxiomProfileChanged {
                expected: dependencies.axiom_summary_hash,
                actual: candidate.replay_verification.axiom_summary_hash,
            },
        ));
    }

    let expected_import_identities =
        sorted_dedup_hashes(&dependencies.certificate_import_identity_hashes);
    let actual_import_identities = sorted_dedup_hashes(
        &candidate
            .replay_verification
            .certificate_import_identity_hashes,
    );
    if expected_import_identities != actual_import_identities {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::Rejected,
            ProofSketchMinimizationErrorKind::CertificateImportIdentityChanged {
                expected: expected_import_identities,
                actual: actual_import_identities,
            },
        ));
    }

    if candidate.replay_verification.certificate_identity_preserved
        && candidate_certificate_identity_hash != dependencies.verified_certificate_identity_hash
    {
        return Err(proof_sketch_minimization_error(
            candidate,
            dependencies,
            ProofSketchMinimizationOutcome::Rejected,
            ProofSketchMinimizationErrorKind::CertificateIdentityMismatch {
                expected: dependencies.verified_certificate_identity_hash,
                actual: candidate_certificate_identity_hash,
            },
        ));
    }

    for dependency in &candidate.removed_dependencies {
        if let Some(protected_by) = proof_sketch_minimization_protected_dependency_use(
            dependencies,
            dependency.identity_hash,
        ) {
            return Err(proof_sketch_minimization_error(
                candidate,
                dependencies,
                ProofSketchMinimizationOutcome::Rejected,
                ProofSketchMinimizationErrorKind::RequiredDependencyRemoval {
                    dependency: dependency.clone(),
                    protected_by,
                },
            ));
        }
    }

    let record =
        proof_sketch_minimization_record(candidate, ProofSketchMinimizationOutcome::Accepted);
    let record_hash = proof_sketch_minimization_record_hash(&record);
    Ok(ProofSketchMinimizationDecision {
        record,
        record_hash,
        last_verified_parent_proof_hash: dependencies.last_verified_parent_proof_hash,
        candidate_certificate_identity_hash,
        source_free_verification_hash: candidate.replay_verification.source_free_verification_hash,
        removed_dependency_identity_hashes: proof_sketch_minimization_removed_dependency_hashes(
            candidate,
        ),
        preserved_dependency_identity_hashes: proof_sketch_minimization_preserved_dependency_hashes(
            dependencies,
        ),
    })
}

pub fn check_proof_sketch_minimization_step(
    sketch: &ProofSketch,
    candidate: &ProofSketchMinimizationCandidate,
    dependencies: &ProofSketchMinimizationDependencySnapshot,
) -> Result<ProofSketchMinimizationDecision, ProofSketchMinimizationError> {
    validate_proof_sketch_minimization_step(sketch, candidate, dependencies)
}

fn proof_sketch_minimization_record(
    candidate: &ProofSketchMinimizationCandidate,
    outcome: ProofSketchMinimizationOutcome,
) -> ProofSketchMinimizationRecord {
    ProofSketchMinimizationRecord {
        base_sketch_hash: candidate.base_sketch_hash,
        kind: candidate.kind,
        target_node_id: candidate.target_node_id.clone(),
        candidate_patch_hash: candidate.candidate_patch_hash,
        replay_plan_hash: candidate.replay_verification.replay_plan_hash,
        verification_result_hash: candidate.replay_verification.verification_result_hash,
        outcome,
        score: candidate.score.clone(),
    }
}

fn proof_sketch_minimization_error(
    candidate: &ProofSketchMinimizationCandidate,
    dependencies: &ProofSketchMinimizationDependencySnapshot,
    outcome: ProofSketchMinimizationOutcome,
    kind: ProofSketchMinimizationErrorKind,
) -> ProofSketchMinimizationError {
    ProofSketchMinimizationError::new(
        kind,
        proof_sketch_minimization_record(candidate, outcome),
        dependencies.last_verified_parent_proof_hash,
    )
}

fn proof_sketch_minimization_protected_dependency_use(
    dependencies: &ProofSketchMinimizationDependencySnapshot,
    identity_hash: Hash,
) -> Option<ProofSketchMinimizationDependencyUse> {
    if dependencies
        .final_parent_dependency_hashes
        .contains(&identity_hash)
    {
        return Some(ProofSketchMinimizationDependencyUse::FinalParentProof);
    }
    if dependencies
        .replay_plan_dependency_hashes
        .contains(&identity_hash)
    {
        return Some(ProofSketchMinimizationDependencyUse::ReplayPlan);
    }
    if dependencies
        .certificate_import_identity_hashes
        .contains(&identity_hash)
    {
        return Some(ProofSketchMinimizationDependencyUse::CertificateImportIdentity);
    }
    if identity_hash == dependencies.axiom_summary_hash
        || dependencies
            .axiom_dependency_hashes
            .contains(&identity_hash)
    {
        return Some(ProofSketchMinimizationDependencyUse::AxiomSummary);
    }
    if dependencies
        .verified_dependency_identity_hashes
        .contains(&identity_hash)
    {
        return Some(ProofSketchMinimizationDependencyUse::VerifiedDependencyIdentityList);
    }
    None
}

fn proof_sketch_minimization_removed_dependency_hashes(
    candidate: &ProofSketchMinimizationCandidate,
) -> Vec<Hash> {
    let mut hashes = candidate
        .removed_dependencies
        .iter()
        .map(|dependency| dependency.identity_hash)
        .collect::<Vec<_>>();
    hashes.sort();
    hashes.dedup();
    hashes
}

fn proof_sketch_minimization_preserved_dependency_hashes(
    dependencies: &ProofSketchMinimizationDependencySnapshot,
) -> Vec<Hash> {
    let mut hashes = Vec::new();
    hashes.extend_from_slice(&dependencies.final_parent_dependency_hashes);
    hashes.extend_from_slice(&dependencies.replay_plan_dependency_hashes);
    hashes.extend_from_slice(&dependencies.certificate_import_identity_hashes);
    hashes.extend_from_slice(&dependencies.axiom_dependency_hashes);
    hashes.extend_from_slice(&dependencies.verified_dependency_identity_hashes);
    hashes.push(dependencies.axiom_summary_hash);
    hashes.sort();
    hashes.dedup();
    hashes
}

fn find_node<'a>(sketch: &'a ProofSketch, node_id: &str) -> Option<&'a ProofSketchNode> {
    sketch.nodes.iter().find(|node| node.node_id == node_id)
}

fn require_node<'a>(
    sketch: &'a ProofSketch,
    node_id: &str,
) -> Result<&'a ProofSketchNode, ProofSketchRevisionPatchError> {
    find_node(sketch, node_id).ok_or_else(|| {
        ProofSketchRevisionPatchError::new(ProofSketchRevisionPatchErrorKind::InvalidPatchTarget {
            node_id: node_id.to_owned(),
        })
    })
}

fn require_node_mut<'a>(
    sketch: &'a mut ProofSketch,
    node_id: &str,
) -> Result<&'a mut ProofSketchNode, ProofSketchRevisionPatchError> {
    sketch
        .nodes
        .iter_mut()
        .find(|node| node.node_id == node_id)
        .ok_or_else(|| {
            ProofSketchRevisionPatchError::new(
                ProofSketchRevisionPatchErrorKind::InvalidPatchTarget {
                    node_id: node_id.to_owned(),
                },
            )
        })
}

fn replace_node(sketch: &mut ProofSketch, replacement: ProofSketchNode) {
    let node = sketch
        .nodes
        .iter_mut()
        .find(|node| node.node_id == replacement.node_id)
        .expect("replacement target is checked before replacement");
    *node = replacement;
}

fn patch_affected_node_ids(patch: &ProofSketchRevisionPatchKind) -> Vec<String> {
    match patch {
        ProofSketchRevisionPatchKind::ReplaceNode { node } => vec![node.node_id.clone()],
        ProofSketchRevisionPatchKind::SplitNode {
            original_node_id,
            replacement_node_ids,
        } => {
            let mut node_ids = Vec::with_capacity(1 + replacement_node_ids.len());
            node_ids.push(original_node_id.clone());
            node_ids.extend(replacement_node_ids.iter().cloned());
            node_ids
        }
        ProofSketchRevisionPatchKind::MergeNodes {
            merged_node_id,
            source_node_ids,
        } => {
            let mut node_ids = Vec::with_capacity(1 + source_node_ids.len());
            node_ids.push(merged_node_id.clone());
            node_ids.extend(source_node_ids.iter().cloned());
            node_ids
        }
        ProofSketchRevisionPatchKind::InsertLemma { node_id, .. }
        | ProofSketchRevisionPatchKind::ChangeStrategy { node_id, .. }
        | ProofSketchRevisionPatchKind::ChangePremiseSet { node_id, .. }
        | ProofSketchRevisionPatchKind::IncreaseBudget { node_id, .. }
        | ProofSketchRevisionPatchKind::MarkCounterexample { node_id, .. } => {
            vec![node_id.clone()]
        }
        ProofSketchRevisionPatchKind::RemoveLemma { lemma_id } => vec![lemma_id.clone()],
    }
}

fn validate_node_revision_policy(
    replacement: &ProofSketchNode,
    existing: &ProofSketchNode,
    policy: &ProofSketchRevisionPatchApplicationPolicy,
) -> Result<(), ProofSketchRevisionPatchError> {
    if replacement.node_id != existing.node_id {
        return Err(ProofSketchRevisionPatchError::new(
            ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                node_id: replacement.node_id.clone(),
                reason: ProofSketchRevisionConflictReason::ReplacementNodeIdMismatch,
            },
        ));
    }
    if let Some(profile) = replacement.fallback_policy.repair_profile {
        if !policy.allowed_repair_profiles.contains(&profile) {
            return Err(policy_rejection(
                &replacement.node_id,
                ProofSketchRevisionPolicyRejection::RepairProfileNotAllowed,
            ));
        }
    }
    if !budget_within_policy(&replacement.budget, &policy.max_budget) {
        return Err(policy_rejection(
            &replacement.node_id,
            ProofSketchRevisionPolicyRejection::BudgetExceedsPolicy,
        ));
    }
    if !policy.allow_premise_expansion {
        let existing_premises = existing
            .premise_hashes
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if replacement
            .premise_hashes
            .iter()
            .any(|hash| !existing_premises.contains(hash))
        {
            return Err(policy_rejection(
                &replacement.node_id,
                ProofSketchRevisionPolicyRejection::PremiseExpansionNotAllowed,
            ));
        }
    }
    Ok(())
}

fn policy_rejection(
    node_id: &str,
    reason: ProofSketchRevisionPolicyRejection,
) -> ProofSketchRevisionPatchError {
    ProofSketchRevisionPatchError::new(
        ProofSketchRevisionPatchErrorKind::PolicyExpandingPatchRejected {
            node_id: node_id.to_owned(),
            reason,
        },
    )
}

fn budget_is_monotone_increase(existing: &ProofSketchBudget, proposed: &ProofSketchBudget) -> bool {
    proposed.max_candidates >= existing.max_candidates
        && proposed.max_search_nodes >= existing.max_search_nodes
        && optional_budget_is_monotone(existing.max_depth, proposed.max_depth)
        && optional_budget_is_monotone(existing.max_repair_steps, proposed.max_repair_steps)
}

fn optional_budget_is_monotone(existing: Option<u64>, proposed: Option<u64>) -> bool {
    match (existing, proposed) {
        (Some(left), Some(right)) => right >= left,
        (None, None) => true,
        (None, Some(_)) => false,
        (Some(_), None) => false,
    }
}

fn budget_within_policy(proposed: &ProofSketchBudget, max: &ProofSketchBudget) -> bool {
    proposed.max_candidates <= max.max_candidates
        && proposed.max_search_nodes <= max.max_search_nodes
        && optional_budget_within_policy(proposed.max_depth, max.max_depth)
        && optional_budget_within_policy(proposed.max_repair_steps, max.max_repair_steps)
}

fn optional_budget_within_policy(proposed: Option<u64>, max: Option<u64>) -> bool {
    match (proposed, max) {
        (Some(value), Some(max)) => value <= max,
        (None, None) => true,
        (Some(_), None) => true,
        (None, Some(_)) => false,
    }
}

fn sorted_dedup_strategy_hints(
    strategy_hints: &[ProofSketchStrategyHint],
) -> Vec<ProofSketchStrategyHint> {
    let mut sorted = strategy_hints.to_vec();
    sorted.sort();
    sorted.dedup();
    sorted
}

fn sorted_dedup_hashes(hashes: &[Hash]) -> Vec<Hash> {
    let mut sorted = hashes.to_vec();
    sorted.sort();
    sorted.dedup();
    sorted
}

fn require_broader_invalidation(
    operation: &'static str,
    node_ids: &[String],
    invalidation: &ProofSketchRevisionDependencyInvalidation,
) -> Result<(), ProofSketchRevisionPatchError> {
    let ProofSketchRevisionDependencyInvalidation::Broader {
        invalidated_node_ids,
        ..
    } = invalidation
    else {
        return Err(ProofSketchRevisionPatchError::new(
            ProofSketchRevisionPatchErrorKind::BroaderDependencyInvalidationRequired {
                operation,
                node_ids: node_ids.to_vec(),
            },
        ));
    };
    let declared = invalidated_node_ids.iter().collect::<BTreeSet<_>>();
    let missing = node_ids
        .iter()
        .filter(|node_id| !declared.contains(node_id))
        .cloned()
        .collect::<Vec<_>>();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(ProofSketchRevisionPatchError::new(
            ProofSketchRevisionPatchErrorKind::BroaderDependencyInvalidationRequired {
                operation,
                node_ids: missing,
            },
        ))
    }
}

fn sort_sketch_for_identity(sketch: &mut ProofSketch) {
    sketch
        .sublemma_statement_proposals
        .sort_by(|left, right| left.proposal_id.cmp(&right.proposal_id));
    sketch
        .nodes
        .sort_by(|left, right| left.node_id.cmp(&right.node_id));
    sketch.edges.sort_by(|left, right| {
        (&left.from, &left.to, left.kind).cmp(&(&right.from, &right.to, right.kind))
    });
}

fn revision_engine_diagnostic_hashes(context: &ProofSketchRevisionEngineContext) -> Vec<Hash> {
    let mut diagnostic_hashes = context
        .evidence
        .iter()
        .map(|evidence| evidence.diagnostic_hash)
        .collect::<Vec<_>>();
    diagnostic_hashes.sort();
    diagnostic_hashes.dedup();
    diagnostic_hashes
}

fn revision_engine_stop_reason(
    patch_hash: Hash,
    current_diagnostic_hashes: &[Hash],
    context: &ProofSketchRevisionEngineContext,
    policy: &ProofSketchRevisionEnginePolicy,
) -> Option<ProofSketchRevisionEngineStopReason> {
    if context.revision_depth >= policy.max_revision_depth {
        return Some(ProofSketchRevisionEngineStopReason::MaxRevisionDepth {
            max: policy.max_revision_depth,
        });
    }
    let history = bounded_revision_history(&context.history, policy.max_patch_history_len);
    if history.iter().any(|entry| entry.patch_hash == patch_hash) {
        return Some(ProofSketchRevisionEngineStopReason::RepeatedPatchHash { patch_hash });
    }

    let mut diagnostic_counts = BTreeMap::<Hash, usize>::new();
    for entry in history {
        if let Some(diagnostic_hash) = entry.diagnostic_hash {
            *diagnostic_counts.entry(diagnostic_hash).or_default() += 1;
        }
    }
    for diagnostic_hash in current_diagnostic_hashes {
        *diagnostic_counts.entry(*diagnostic_hash).or_default() += 1;
    }
    diagnostic_counts
        .into_iter()
        .find_map(|(diagnostic_hash, count)| {
            if count > policy.max_repeated_diagnostic_hash_count {
                Some(
                    ProofSketchRevisionEngineStopReason::RepeatedDiagnosticHash {
                        diagnostic_hash,
                        count,
                        max: policy.max_repeated_diagnostic_hash_count,
                    },
                )
            } else {
                None
            }
        })
}

fn bounded_revision_history(
    history: &[ProofSketchRevisionHistoryEntry],
    max_len: usize,
) -> &[ProofSketchRevisionHistoryEntry] {
    let start = history.len().saturating_sub(max_len);
    &history[start..]
}

fn revision_engine_decision(
    sketch: &ProofSketch,
    patch: &ProofSketchRevisionPatch,
    base_sketch_hash: Hash,
    patch_hash: Hash,
    context: &ProofSketchRevisionEngineContext,
    stop_reason: Option<ProofSketchRevisionEngineStopReason>,
) -> ProofSketchRevisionDecisionRecord {
    let invalidated_node_ids = revision_engine_invalidated_node_ids(sketch, patch, context);
    let all_node_ids = sketch
        .nodes
        .iter()
        .map(|node| node.node_id.clone())
        .collect::<BTreeSet<_>>();
    let invalidated_node_set = invalidated_node_ids
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let preserved_node_ids = all_node_ids
        .difference(&invalidated_node_set)
        .cloned()
        .collect::<Vec<_>>();
    let rescheduled_node_ids = invalidated_node_ids.clone();
    let (invalidated_hole_ids, preserved_completed_hole_ids, rescheduled_hole_ids) =
        revision_engine_hole_disposition(context, &invalidated_node_set);
    let preserved_verified_local_lemma_hashes =
        revision_engine_preserved_verified_local_lemma_hashes(sketch, &preserved_node_ids, context);

    ProofSketchRevisionDecisionRecord {
        base_sketch_hash,
        patch_hash,
        outcome: if stop_reason.is_some() {
            ProofSketchRevisionDecisionOutcome::Stopped
        } else {
            ProofSketchRevisionDecisionOutcome::Applied
        },
        stop_reason,
        revision_depth: context.revision_depth,
        diagnostic_hashes: revision_engine_diagnostic_hashes(context),
        invalidated_node_ids,
        preserved_node_ids,
        rescheduled_node_ids,
        invalidated_hole_ids,
        preserved_completed_hole_ids,
        rescheduled_hole_ids,
        preserved_verified_local_lemma_hashes,
    }
}

fn revision_engine_invalidated_node_ids(
    sketch: &ProofSketch,
    patch: &ProofSketchRevisionPatch,
    context: &ProofSketchRevisionEngineContext,
) -> Vec<String> {
    let known_node_ids = sketch
        .nodes
        .iter()
        .map(|node| node.node_id.clone())
        .collect::<BTreeSet<_>>();
    let mut roots = patch_affected_node_ids(&patch.patch)
        .into_iter()
        .filter(|node_id| known_node_ids.contains(node_id))
        .collect::<BTreeSet<_>>();
    roots.extend(
        patch
            .dependency_invalidation
            .invalidated_node_ids()
            .into_iter()
            .filter(|node_id| known_node_ids.contains(node_id)),
    );
    roots.extend(
        context
            .evidence
            .iter()
            .filter_map(|evidence| evidence.node_id.as_ref())
            .filter(|node_id| known_node_ids.contains(*node_id))
            .cloned(),
    );
    successor_closure(sketch, roots)
}

fn successor_closure(sketch: &ProofSketch, roots: BTreeSet<String>) -> Vec<String> {
    let mut outgoing = BTreeMap::<String, BTreeSet<String>>::new();
    for node in &sketch.nodes {
        outgoing.insert(node.node_id.clone(), BTreeSet::new());
    }
    for edge in &sketch.edges {
        if let Some(successors) = outgoing.get_mut(&edge.from) {
            successors.insert(edge.to.clone());
        }
    }

    let mut visited = BTreeSet::new();
    let mut stack = roots.into_iter().collect::<Vec<_>>();
    while let Some(node_id) = stack.pop() {
        if !visited.insert(node_id.clone()) {
            continue;
        }
        if let Some(successors) = outgoing.get(&node_id) {
            stack.extend(successors.iter().rev().cloned());
        }
    }
    visited.into_iter().collect()
}

fn revision_engine_hole_disposition(
    context: &ProofSketchRevisionEngineContext,
    invalidated_node_ids: &BTreeSet<String>,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let evidence_hole_ids = context
        .evidence
        .iter()
        .filter_map(|evidence| evidence.hole_id.as_ref())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut invalidated_hole_ids = BTreeSet::new();
    let mut preserved_completed_hole_ids = BTreeSet::new();
    for hole in &context.hole_states {
        let invalidated = invalidated_node_ids.contains(&hole.owner_node_id)
            || evidence_hole_ids.contains(&hole.hole_id)
            || matches!(
                hole.status,
                ProofSketchRevisionHoleStatus::Failed | ProofSketchRevisionHoleStatus::Stale
            );
        if invalidated {
            invalidated_hole_ids.insert(hole.hole_id.clone());
        } else if hole.status == ProofSketchRevisionHoleStatus::Completed {
            preserved_completed_hole_ids.insert(hole.hole_id.clone());
        }
    }

    for record in &context.parent_integration_records {
        for hole_id in &record.completed_hole_ids {
            if !invalidated_hole_ids.contains(hole_id) && !evidence_hole_ids.contains(hole_id) {
                preserved_completed_hole_ids.insert(hole_id.clone());
            }
        }
    }

    let rescheduled_hole_ids = invalidated_hole_ids.iter().cloned().collect::<Vec<_>>();
    (
        invalidated_hole_ids.into_iter().collect(),
        preserved_completed_hole_ids.into_iter().collect(),
        rescheduled_hole_ids,
    )
}

fn revision_engine_preserved_verified_local_lemma_hashes(
    sketch: &ProofSketch,
    preserved_node_ids: &[String],
    context: &ProofSketchRevisionEngineContext,
) -> Vec<Hash> {
    let preserved_node_ids = preserved_node_ids.iter().collect::<BTreeSet<_>>();
    let mut required_hashes = BTreeSet::<Hash>::new();
    for node in &sketch.nodes {
        if preserved_node_ids.contains(&node.node_id) {
            required_hashes.extend(node.premise_hashes.iter().copied());
        }
    }
    for record in &context.parent_integration_records {
        required_hashes.extend(record.required_local_lemma_hashes.iter().copied());
    }

    let mut preserved = Vec::new();
    let proposal_statement_hashes = sketch
        .sublemma_statement_proposals
        .iter()
        .map(|proposal| proposal.statement_hash)
        .collect::<BTreeSet<_>>();
    let parent_required_hashes = context
        .parent_integration_records
        .iter()
        .flat_map(|record| record.required_local_lemma_hashes.iter().copied())
        .collect::<BTreeSet<_>>();
    for proposal in &sketch.sublemma_statement_proposals {
        if required_hashes.contains(&proposal.statement_hash) {
            preserved.push(proposal.statement_hash);
        }
    }
    preserved.extend(parent_required_hashes.into_iter().filter(|hash| {
        required_hashes.contains(hash) && !proposal_statement_hashes.contains(hash)
    }));
    preserved.sort();
    preserved.dedup();
    preserved
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ProofSketchSchemaError> {
    JsonDocument::parse(source).map_err(|err| {
        ProofSketchSchemaError::new(
            "$",
            ProofSketchSchemaErrorKind::JsonParse { offset: err.offset },
        )
    })
}

fn parse_target_statement_identity(
    value: &JsonValue<'_>,
) -> Result<ProofSketchTargetStatementIdentity, ProofSketchSchemaError> {
    let path = "$.target_statement_identity";
    let members = object_map(value, path, TARGET_IDENTITY_FIELDS)?;
    Ok(ProofSketchTargetStatementIdentity {
        statement_hash: required_hash(&members, "statement_hash", path)?,
        input_context_hash: required_hash(&members, "input_context_hash", path)?,
        output_context_hash: required_hash(&members, "output_context_hash", path)?,
        module: optional_bounded_string(&members, "module", path, 1, 256)?,
        declaration: optional_bounded_string(&members, "declaration", path, 1, 256)?,
    })
}

fn parse_sublemma_statement_proposals(
    value: &JsonValue<'_>,
) -> Result<Vec<ProofSketchSublemmaStatementProposal>, ProofSketchSchemaError> {
    let elements = array_elements(value, "$.sublemma_statement_proposals")?;
    enforce_array_len(
        "$.sublemma_statement_proposals",
        elements.len(),
        0,
        MAX_SUBLEMMA_PROPOSALS,
    )?;
    let mut proposals = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let path = format!("$.sublemma_statement_proposals[{index}]");
        let members = object_map(element, &path, SUBLEMMA_PROPOSAL_FIELDS)?;
        let proposal_id = required_identifier(&members, "proposal_id", &path)?;
        if !seen.insert(proposal_id.clone()) {
            return Err(ProofSketchSchemaError::new(
                format!("{path}.proposal_id"),
                ProofSketchSchemaErrorKind::DuplicateProposalId { proposal_id },
            ));
        }
        let policy_wire = required_string(&members, "generalization_policy", &path)?;
        let generalization_policy = ProofSketchGeneralizationPolicy::parse(&policy_wire)
            .ok_or_else(|| {
                ProofSketchSchemaError::new(
                    format!("{path}.generalization_policy"),
                    ProofSketchSchemaErrorKind::InvalidGeneralizationPolicy { value: policy_wire },
                )
            })?;
        let display = optional_value(&members, "display")
            .map(|value| parse_display(value, &format!("{path}.display")))
            .transpose()?;
        proposals.push(ProofSketchSublemmaStatementProposal {
            proposal_id,
            statement_hash: required_hash(&members, "statement_hash", &path)?,
            input_context_hash: required_hash(&members, "input_context_hash", &path)?,
            output_context_hash: required_hash(&members, "output_context_hash", &path)?,
            generalization_policy,
            display,
        });
    }
    Ok(proposals)
}

fn parse_nodes(value: &JsonValue<'_>) -> Result<Vec<ProofSketchNode>, ProofSketchSchemaError> {
    let elements = array_elements(value, "$.nodes")?;
    enforce_array_len("$.nodes", elements.len(), 1, MAX_NODES)?;
    let mut nodes = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let path = format!("$.nodes[{index}]");
        let node = parse_node(element, &path)?;
        if !seen.insert(node.node_id.clone()) {
            return Err(ProofSketchSchemaError::new(
                format!("{path}.node_id"),
                ProofSketchSchemaErrorKind::DuplicateNodeId {
                    node_id: node.node_id,
                },
            ));
        }
        nodes.push(node);
    }
    Ok(nodes)
}

fn parse_node(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchNode, ProofSketchSchemaError> {
    let members = object_map(value, path, NODE_FIELDS)?;
    let node_id = required_identifier(&members, "node_id", path)?;
    let kind_wire = required_string(&members, "kind", path)?;
    let kind = ProofSketchNodeKind::parse(&kind_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.kind"),
            ProofSketchSchemaErrorKind::InvalidNodeKind { value: kind_wire },
        )
    })?;
    let display = optional_value(&members, "display")
        .map(|value| parse_display(value, &format!("{path}.display")))
        .transpose()?;
    let statement_proposal_id = optional_identifier(&members, "statement_proposal_id", path)?;
    Ok(ProofSketchNode {
        node_id,
        kind,
        input_context_hash: required_hash(&members, "input_context_hash", path)?,
        output_context_hash: required_hash(&members, "output_context_hash", path)?,
        expected_effect: parse_expected_effect(
            required_value(&members, "expected_effect", path)?,
            &format!("{path}.expected_effect"),
        )?,
        strategy_hints: parse_strategy_hints(
            required_value(&members, "strategy_hints", path)?,
            &format!("{path}.strategy_hints"),
        )?,
        budget: parse_budget(
            required_value(&members, "budget", path)?,
            &format!("{path}.budget"),
        )?,
        fallback_policy: parse_fallback_policy(
            required_value(&members, "fallback_policy", path)?,
            &format!("{path}.fallback_policy"),
        )?,
        statement_proposal_id,
        premise_hashes: optional_value(&members, "premise_hashes")
            .map(|value| parse_hash_array(value, &format!("{path}.premise_hashes")))
            .transpose()?
            .unwrap_or_default(),
        display,
    })
}

fn parse_expected_effect(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchExpectedEffect, ProofSketchSchemaError> {
    let members = object_map(value, path, EXPECTED_EFFECT_FIELDS)?;
    let kind_wire = required_string(&members, "kind", path)?;
    let kind = ProofSketchExpectedEffectKind::parse(&kind_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.kind"),
            ProofSketchSchemaErrorKind::InvalidExpectedEffectKind { value: kind_wire },
        )
    })?;
    Ok(ProofSketchExpectedEffect {
        kind,
        goal_delta: required_i64_in_range(&members, "goal_delta", path, -1000, 1000)?,
        effect_hash: optional_hash(&members, "effect_hash", path)?,
    })
}

fn parse_strategy_hints(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<ProofSketchStrategyHint>, ProofSketchSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), 0, MAX_STRATEGY_HINTS)?;
    let mut hints = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let value = string_value(element, &item_path)?;
        let hint = ProofSketchStrategyHint::parse(&value).ok_or_else(|| {
            ProofSketchSchemaError::new(
                item_path.clone(),
                ProofSketchSchemaErrorKind::InvalidStrategyHint {
                    value: value.clone(),
                },
            )
        })?;
        if !seen.insert(hint) {
            return Err(ProofSketchSchemaError::new(
                item_path,
                ProofSketchSchemaErrorKind::DuplicateStrategyHint { value },
            ));
        }
        hints.push(hint);
    }
    hints.sort();
    Ok(hints)
}

fn parse_budget(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchBudget, ProofSketchSchemaError> {
    let members = object_map(value, path, BUDGET_FIELDS)?;
    Ok(ProofSketchBudget {
        max_candidates: required_u64_in_range(&members, "max_candidates", path, 0, 1_000_000)?,
        max_search_nodes: required_u64_in_range(&members, "max_search_nodes", path, 0, 1_000_000)?,
        max_depth: optional_u64_in_range(&members, "max_depth", path, 0, 1_000_000)?,
        max_repair_steps: optional_u64_in_range(&members, "max_repair_steps", path, 0, 1_000_000)?,
    })
}

fn parse_fallback_policy(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchFallbackPolicy, ProofSketchSchemaError> {
    let members = object_map(value, path, FALLBACK_POLICY_FIELDS)?;
    let action_wire = required_string(&members, "action", path)?;
    let action = ProofSketchFallbackAction::parse(&action_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.action"),
            ProofSketchSchemaErrorKind::InvalidFallbackAction { value: action_wire },
        )
    })?;
    let repair_profile = match optional_string(&members, "repair_profile", path)? {
        Some(profile_wire) => Some(ProofSketchRepairProfile::parse(&profile_wire).ok_or_else(
            || {
                ProofSketchSchemaError::new(
                    format!("{path}.repair_profile"),
                    ProofSketchSchemaErrorKind::InvalidRepairProfile {
                        value: profile_wire,
                    },
                )
            },
        )?),
        None => None,
    };
    Ok(ProofSketchFallbackPolicy {
        action,
        fallback_node_id: optional_identifier(&members, "fallback_node_id", path)?,
        repair_profile,
    })
}

fn parse_edges(value: &JsonValue<'_>) -> Result<Vec<ProofSketchEdge>, ProofSketchSchemaError> {
    let elements = array_elements(value, "$.edges")?;
    enforce_array_len("$.edges", elements.len(), 0, MAX_EDGES)?;
    let mut edges = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let path = format!("$.edges[{index}]");
        let members = object_map(element, &path, EDGE_FIELDS)?;
        let from = required_identifier(&members, "from", &path)?;
        let to = required_identifier(&members, "to", &path)?;
        let kind_wire = required_string(&members, "kind", &path)?;
        let kind = ProofSketchEdgeKind::parse(&kind_wire).ok_or_else(|| {
            ProofSketchSchemaError::new(
                format!("{path}.kind"),
                ProofSketchSchemaErrorKind::InvalidEdgeKind {
                    value: kind_wire.clone(),
                },
            )
        })?;
        if !seen.insert((from.clone(), to.clone(), kind)) {
            return Err(ProofSketchSchemaError::new(
                path,
                ProofSketchSchemaErrorKind::DuplicateEdge {
                    from,
                    to,
                    kind: kind_wire,
                },
            ));
        }
        edges.push(ProofSketchEdge { from, to, kind });
    }
    Ok(edges)
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, ProofSketchSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), 0, MAX_PREMISE_HASHES)?;
    let mut hashes = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let hash = hash_value(element, &item_path)?;
        let wire = format_hash_string(&hash);
        if !seen.insert(wire.clone()) {
            return Err(ProofSketchSchemaError::new(
                item_path,
                ProofSketchSchemaErrorKind::DuplicatePremiseHash { value: wire },
            ));
        }
        hashes.push(hash);
    }
    hashes.sort();
    Ok(hashes)
}

fn parse_identifier_array(
    value: &JsonValue<'_>,
    path: &str,
    min: usize,
    max: usize,
) -> Result<Vec<String>, ProofSketchSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), min, max)?;
    let mut identifiers = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let identifier = identifier_value(element, &item_path)?;
        if !seen.insert(identifier.clone()) {
            return Err(ProofSketchSchemaError::new(
                item_path,
                ProofSketchSchemaErrorKind::DuplicatePatchNodeId {
                    node_id: identifier,
                },
            ));
        }
        identifiers.push(identifier);
    }
    Ok(identifiers)
}

fn parse_display(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchDisplay, ProofSketchSchemaError> {
    let members = object_map(value, path, DISPLAY_FIELDS)?;
    Ok(ProofSketchDisplay {
        label: optional_bounded_string(&members, "label", path, 0, 256)?,
        explanation: optional_bounded_string(&members, "explanation", path, 0, 2000)?,
    })
}

fn parse_advisory(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchAdvisory, ProofSketchSchemaError> {
    let members = object_map(value, path, ADVISORY_FIELDS)?;
    Ok(ProofSketchAdvisory {
        display_text: optional_bounded_string(&members, "display_text", path, 0, 2000)?,
        score: optional_number_raw(&members, "score", path)?,
        model_score: optional_number_raw(&members, "model_score", path)?,
        scoring_profile: optional_bounded_string(&members, "scoring_profile", path, 0, 128)?,
    })
}

fn parse_local_lemma_proposal_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchLocalLemmaProposal, ProofSketchSchemaError> {
    let members = object_map(value, path, LOCAL_LEMMA_PROPOSAL_FIELDS)?;
    let state_wire = required_string(&members, "state", path)?;
    let state = ProofSketchLocalLemmaState::parse(&state_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.state"),
            ProofSketchSchemaErrorKind::InvalidLocalLemmaState { value: state_wire },
        )
    })?;
    Ok(ProofSketchLocalLemmaProposal {
        proposal_id: required_identifier(&members, "proposal_id", path)?,
        base_sketch_hash: required_hash(&members, "base_sketch_hash", path)?,
        source_node_id: required_identifier(&members, "source_node_id", path)?,
        statement_hash: required_hash(&members, "statement_hash", path)?,
        input_context_hash: required_hash(&members, "input_context_hash", path)?,
        output_context_hash: required_hash(&members, "output_context_hash", path)?,
        environment_hash: required_hash(&members, "environment_hash", path)?,
        policy_hash: required_hash(&members, "policy_hash", path)?,
        allowed_premise_hashes: parse_hash_array(
            required_value(&members, "allowed_premise_hashes", path)?,
            &format!("{path}.allowed_premise_hashes"),
        )?,
        state,
    })
}

fn parse_revision_patch_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchRevisionPatch, ProofSketchSchemaError> {
    let members = object_map(value, path, REVISION_PATCH_FIELDS)?;
    Ok(ProofSketchRevisionPatch {
        base_sketch_hash: required_hash(&members, "base_sketch_hash", path)?,
        dependency_invalidation: optional_value(&members, "dependency_invalidation")
            .map(|value| {
                parse_revision_dependency_invalidation(
                    value,
                    &format!("{path}.dependency_invalidation"),
                )
            })
            .transpose()?
            .unwrap_or(ProofSketchRevisionDependencyInvalidation::AffectedSubDagOnly),
        patch: parse_revision_patch_kind(
            required_value(&members, "patch", path)?,
            &format!("{path}.patch"),
        )?,
    })
}

fn parse_revision_dependency_invalidation(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchRevisionDependencyInvalidation, ProofSketchSchemaError> {
    let generic = object_map(value, path, REVISION_DEPENDENCY_INVALIDATION_FIELDS)?;
    let kind_wire = required_string(&generic, "kind", path)?;
    match kind_wire.as_str() {
        "affected_subdag_only" => {
            object_map(value, path, &["kind"])?;
            Ok(ProofSketchRevisionDependencyInvalidation::AffectedSubDagOnly)
        }
        "broader" => {
            let members = object_map(value, path, REVISION_DEPENDENCY_INVALIDATION_FIELDS)?;
            Ok(ProofSketchRevisionDependencyInvalidation::Broader {
                invalidated_node_ids: parse_identifier_array(
                    required_value(&members, "invalidated_node_ids", path)?,
                    &format!("{path}.invalidated_node_ids"),
                    1,
                    MAX_REVISION_PATCH_NODE_IDS,
                )?,
                diagnostic_hash: required_hash(&members, "diagnostic_hash", path)?,
            })
        }
        _ => Err(ProofSketchSchemaError::new(
            format!("{path}.kind"),
            ProofSketchSchemaErrorKind::InvalidRevisionPatchKind { value: kind_wire },
        )),
    }
}

fn parse_revision_patch_kind(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchRevisionPatchKind, ProofSketchSchemaError> {
    let generic = object_map(value, path, REVISION_PATCH_KIND_FIELDS)?;
    let kind_wire = required_string(&generic, "kind", path)?;
    match kind_wire.as_str() {
        "replace_node" => {
            let members = object_map(value, path, &["kind", "node"])?;
            Ok(ProofSketchRevisionPatchKind::ReplaceNode {
                node: Box::new(parse_node(
                    required_value(&members, "node", path)?,
                    &format!("{path}.node"),
                )?),
            })
        }
        "split_node" => {
            let members = object_map(
                value,
                path,
                &["kind", "original_node_id", "replacement_node_ids"],
            )?;
            Ok(ProofSketchRevisionPatchKind::SplitNode {
                original_node_id: required_identifier(&members, "original_node_id", path)?,
                replacement_node_ids: parse_identifier_array(
                    required_value(&members, "replacement_node_ids", path)?,
                    &format!("{path}.replacement_node_ids"),
                    1,
                    MAX_REVISION_PATCH_NODE_IDS,
                )?,
            })
        }
        "merge_nodes" => {
            let members = object_map(value, path, &["kind", "merged_node_id", "source_node_ids"])?;
            Ok(ProofSketchRevisionPatchKind::MergeNodes {
                merged_node_id: required_identifier(&members, "merged_node_id", path)?,
                source_node_ids: parse_identifier_array(
                    required_value(&members, "source_node_ids", path)?,
                    &format!("{path}.source_node_ids"),
                    1,
                    MAX_REVISION_PATCH_NODE_IDS,
                )?,
            })
        }
        "insert_lemma" => {
            let members = object_map(
                value,
                path,
                &["kind", "node_id", "local_lemma_proposal_hash"],
            )?;
            Ok(ProofSketchRevisionPatchKind::InsertLemma {
                node_id: required_identifier(&members, "node_id", path)?,
                local_lemma_proposal_hash: required_hash(
                    &members,
                    "local_lemma_proposal_hash",
                    path,
                )?,
            })
        }
        "remove_lemma" => {
            let members = object_map(value, path, &["kind", "lemma_id"])?;
            Ok(ProofSketchRevisionPatchKind::RemoveLemma {
                lemma_id: required_identifier(&members, "lemma_id", path)?,
            })
        }
        "change_strategy" => {
            let members = object_map(
                value,
                path,
                &["kind", "node_id", "strategy_hints", "repair_profile"],
            )?;
            let repair_profile = match optional_string(&members, "repair_profile", path)? {
                Some(profile_wire) => Some(
                    ProofSketchRepairProfile::parse(&profile_wire).ok_or_else(|| {
                        ProofSketchSchemaError::new(
                            format!("{path}.repair_profile"),
                            ProofSketchSchemaErrorKind::InvalidRepairProfile {
                                value: profile_wire,
                            },
                        )
                    })?,
                ),
                None => None,
            };
            Ok(ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: required_identifier(&members, "node_id", path)?,
                strategy_hints: parse_strategy_hints(
                    required_value(&members, "strategy_hints", path)?,
                    &format!("{path}.strategy_hints"),
                )?,
                repair_profile,
            })
        }
        "change_premise_set" => {
            let members = object_map(value, path, &["kind", "node_id", "premise_hashes"])?;
            Ok(ProofSketchRevisionPatchKind::ChangePremiseSet {
                node_id: required_identifier(&members, "node_id", path)?,
                premise_hashes: parse_hash_array(
                    required_value(&members, "premise_hashes", path)?,
                    &format!("{path}.premise_hashes"),
                )?,
            })
        }
        "increase_budget" => {
            let members = object_map(value, path, &["kind", "node_id", "budget"])?;
            Ok(ProofSketchRevisionPatchKind::IncreaseBudget {
                node_id: required_identifier(&members, "node_id", path)?,
                budget: parse_budget(
                    required_value(&members, "budget", path)?,
                    &format!("{path}.budget"),
                )?,
            })
        }
        "mark_counterexample" => {
            let members = object_map(value, path, &["kind", "node_id", "diagnostic_hash"])?;
            Ok(ProofSketchRevisionPatchKind::MarkCounterexample {
                node_id: required_identifier(&members, "node_id", path)?,
                diagnostic_hash: required_hash(&members, "diagnostic_hash", path)?,
            })
        }
        _ => Err(ProofSketchSchemaError::new(
            format!("{path}.kind"),
            ProofSketchSchemaErrorKind::InvalidRevisionPatchKind { value: kind_wire },
        )),
    }
}

fn parse_minimization_record_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSketchMinimizationRecord, ProofSketchSchemaError> {
    let members = object_map(value, path, MINIMIZATION_RECORD_FIELDS)?;
    let kind_wire = required_string(&members, "kind", path)?;
    let kind = ProofSketchMinimizationKind::parse(&kind_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.kind"),
            ProofSketchSchemaErrorKind::InvalidMinimizationKind { value: kind_wire },
        )
    })?;
    let outcome_wire = required_string(&members, "outcome", path)?;
    let outcome = ProofSketchMinimizationOutcome::parse(&outcome_wire).ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.outcome"),
            ProofSketchSchemaErrorKind::InvalidMinimizationOutcome {
                value: outcome_wire,
            },
        )
    })?;
    Ok(ProofSketchMinimizationRecord {
        base_sketch_hash: required_hash(&members, "base_sketch_hash", path)?,
        kind,
        target_node_id: optional_identifier(&members, "target_node_id", path)?,
        candidate_patch_hash: required_hash(&members, "candidate_patch_hash", path)?,
        replay_plan_hash: required_hash(&members, "replay_plan_hash", path)?,
        verification_result_hash: required_hash(&members, "verification_result_hash", path)?,
        outcome,
        score: optional_number_raw(&members, "score", path)?,
    })
}

fn validate_references(
    proposals: &[ProofSketchSublemmaStatementProposal],
    nodes: &[ProofSketchNode],
    edges: &[ProofSketchEdge],
) -> Result<(), ProofSketchSchemaError> {
    let proposal_ids: BTreeSet<&str> = proposals
        .iter()
        .map(|proposal| proposal.proposal_id.as_str())
        .collect();
    let node_ids: BTreeSet<&str> = nodes.iter().map(|node| node.node_id.as_str()).collect();

    for node in nodes {
        if let Some(proposal_id) = &node.statement_proposal_id {
            if !proposal_ids.contains(proposal_id.as_str()) {
                return Err(ProofSketchSchemaError::new(
                    format!("$.nodes.{}.statement_proposal_id", node.node_id),
                    ProofSketchSchemaErrorKind::UnknownProposalReference {
                        proposal_id: proposal_id.clone(),
                    },
                ));
            }
        }
        if let Some(fallback_node_id) = &node.fallback_policy.fallback_node_id {
            if !node_ids.contains(fallback_node_id.as_str()) {
                return Err(ProofSketchSchemaError::new(
                    format!("$.nodes.{}.fallback_policy.fallback_node_id", node.node_id),
                    ProofSketchSchemaErrorKind::UnknownNodeReference {
                        node_id: fallback_node_id.clone(),
                    },
                ));
            }
        }
    }

    for edge in edges {
        if !node_ids.contains(edge.from.as_str()) {
            return Err(ProofSketchSchemaError::new(
                "$.edges.from",
                ProofSketchSchemaErrorKind::UnknownNodeReference {
                    node_id: edge.from.clone(),
                },
            ));
        }
        if !node_ids.contains(edge.to.as_str()) {
            return Err(ProofSketchSchemaError::new(
                "$.edges.to",
                ProofSketchSchemaErrorKind::UnknownNodeReference {
                    node_id: edge.to.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ProofSketchSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ProofSketchSchemaError::new(
                format!("{path}.{}", member.key()),
                ProofSketchSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ProofSketchSchemaError::new(
                format!("{path}.{}", member.key()),
                ProofSketchSchemaErrorKind::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
        map.insert(member.key(), member.value());
    }
    Ok(map)
}

fn array_elements<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
) -> Result<&'value [JsonValue<'src>], ProofSketchSchemaError> {
    value.array_elements().ok_or_else(|| {
        ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn enforce_array_len(
    path: &str,
    actual: usize,
    min: usize,
    max: usize,
) -> Result<(), ProofSketchSchemaError> {
    if actual < min || actual > max {
        return Err(ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::ArrayLengthOutOfRange { min, max, actual },
        ));
    }
    Ok(())
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ProofSketchSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ProofSketchSchemaError::new(
            format!("{path}.{field}"),
            ProofSketchSchemaErrorKind::MissingField { field },
        )
    })
}

fn optional_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &str,
) -> Option<&'value JsonValue<'src>> {
    members.get(field).copied()
}

fn required_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<String, ProofSketchSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ProofSketchSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn optional_bounded_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: usize,
    max: usize,
) -> Result<Option<String>, ProofSketchSchemaError> {
    let Some(value) = optional_string(members, field, path)? else {
        return Ok(None);
    };
    let actual = value.chars().count();
    if actual < min || actual > max {
        return Err(ProofSketchSchemaError::new(
            format!("{path}.{field}"),
            ProofSketchSchemaErrorKind::StringLengthOutOfRange { min, max, actual },
        ));
    }
    Ok(Some(value))
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ProofSketchSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_identifier(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<String, ProofSketchSchemaError> {
    identifier_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_identifier(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ProofSketchSchemaError> {
    optional_value(members, field)
        .map(|value| identifier_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn identifier_value(value: &JsonValue<'_>, path: &str) -> Result<String, ProofSketchSchemaError> {
    let identifier = string_value(value, path)?;
    if identifier.is_empty()
        || identifier.len() > 128
        || !identifier
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    {
        return Err(ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::InvalidIdentifier { value: identifier },
        ));
    }
    Ok(identifier)
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ProofSketchSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ProofSketchSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ProofSketchSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn required_i64_in_range(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: i64,
    max: i64,
) -> Result<i64, ProofSketchSchemaError> {
    let field_path = format!("{path}.{field}");
    let value = required_value(members, field, path)?;
    let raw = number_raw(value, &field_path)?;
    if raw.contains('.') || raw.contains('e') || raw.contains('E') || raw == "-" {
        return Err(ProofSketchSchemaError::new(
            field_path,
            ProofSketchSchemaErrorKind::InvalidInteger { value: raw },
        ));
    }
    let parsed: i64 = raw.parse().map_err(|_| {
        ProofSketchSchemaError::new(
            field_path.clone(),
            ProofSketchSchemaErrorKind::InvalidInteger { value: raw.clone() },
        )
    })?;
    if parsed < min || parsed > max {
        return Err(ProofSketchSchemaError::new(
            field_path,
            ProofSketchSchemaErrorKind::IntegerOutOfRange { value: raw },
        ));
    }
    Ok(parsed)
}

fn required_u64_in_range(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: u64,
    max: u64,
) -> Result<u64, ProofSketchSchemaError> {
    let field_path = format!("{path}.{field}");
    let value = required_value(members, field, path)?;
    parse_u64_in_range(value, &field_path, min, max)
}

fn optional_u64_in_range(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: u64,
    max: u64,
) -> Result<Option<u64>, ProofSketchSchemaError> {
    optional_value(members, field)
        .map(|value| parse_u64_in_range(value, &format!("{path}.{field}"), min, max))
        .transpose()
}

fn parse_u64_in_range(
    value: &JsonValue<'_>,
    path: &str,
    min: u64,
    max: u64,
) -> Result<u64, ProofSketchSchemaError> {
    let raw = number_raw(value, path)?;
    if raw.is_empty() || raw.bytes().any(|byte| !byte.is_ascii_digit()) {
        return Err(ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::InvalidInteger { value: raw },
        ));
    }
    let parsed: u64 = raw.parse().map_err(|_| {
        ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::InvalidInteger { value: raw.clone() },
        )
    })?;
    if parsed < min || parsed > max {
        return Err(ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::IntegerOutOfRange { value: raw },
        ));
    }
    Ok(parsed)
}

fn optional_number_raw(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ProofSketchSchemaError> {
    optional_value(members, field)
        .map(|value| number_raw(value, &format!("{path}.{field}")))
        .transpose()
}

fn number_raw(value: &JsonValue<'_>, path: &str) -> Result<String, ProofSketchSchemaError> {
    value.number_raw().map(ToOwned::to_owned).ok_or_else(|| {
        ProofSketchSchemaError::new(
            path,
            ProofSketchSchemaErrorKind::ExpectedInteger {
                actual: value.kind(),
            },
        )
    })
}

fn encode_target_statement_identity_to(
    out: &mut Vec<u8>,
    identity: &ProofSketchTargetStatementIdentity,
) {
    encode_string_to(out, "statement_hash");
    encode_hash_to(out, &identity.statement_hash);
    encode_string_to(out, "input_context_hash");
    encode_hash_to(out, &identity.input_context_hash);
    encode_string_to(out, "output_context_hash");
    encode_hash_to(out, &identity.output_context_hash);
    encode_option_string_to(out, "module", identity.module.as_deref());
    encode_option_string_to(out, "declaration", identity.declaration.as_deref());
}

fn encode_sublemma_statement_proposal_to(
    out: &mut Vec<u8>,
    proposal: &ProofSketchSublemmaStatementProposal,
) {
    encode_string_to(out, "proposal_id");
    encode_string_to(out, &proposal.proposal_id);
    encode_string_to(out, "statement_hash");
    encode_hash_to(out, &proposal.statement_hash);
    encode_string_to(out, "input_context_hash");
    encode_hash_to(out, &proposal.input_context_hash);
    encode_string_to(out, "output_context_hash");
    encode_hash_to(out, &proposal.output_context_hash);
    encode_string_to(out, "generalization_policy");
    encode_string_to(out, proposal.generalization_policy.wire());
}

fn encode_node_to(out: &mut Vec<u8>, node: &ProofSketchNode) {
    encode_string_to(out, "node_id");
    encode_string_to(out, &node.node_id);
    encode_string_to(out, "kind");
    encode_string_to(out, node.kind.wire());
    encode_string_to(out, "input_context_hash");
    encode_hash_to(out, &node.input_context_hash);
    encode_string_to(out, "output_context_hash");
    encode_hash_to(out, &node.output_context_hash);
    encode_string_to(out, "expected_effect");
    encode_expected_effect_to(out, &node.expected_effect);
    encode_string_to(out, "strategy_hints");
    encode_len_to(out, node.strategy_hints.len());
    for hint in &node.strategy_hints {
        encode_string_to(out, hint.wire());
    }
    encode_string_to(out, "budget");
    encode_budget_to(out, &node.budget);
    encode_string_to(out, "fallback_policy");
    encode_fallback_policy_to(out, &node.fallback_policy);
    encode_option_string_to(
        out,
        "statement_proposal_id",
        node.statement_proposal_id.as_deref(),
    );
    encode_string_to(out, "premise_hashes");
    encode_len_to(out, node.premise_hashes.len());
    for hash in &node.premise_hashes {
        encode_hash_to(out, hash);
    }
}

fn encode_expected_effect_to(out: &mut Vec<u8>, effect: &ProofSketchExpectedEffect) {
    encode_string_to(out, "kind");
    encode_string_to(out, effect.kind.wire());
    encode_string_to(out, "goal_delta");
    encode_i64_to(out, effect.goal_delta);
    encode_option_hash_to(out, "effect_hash", effect.effect_hash.as_ref());
}

fn encode_budget_to(out: &mut Vec<u8>, budget: &ProofSketchBudget) {
    encode_string_to(out, "max_candidates");
    encode_u64_to(out, budget.max_candidates);
    encode_string_to(out, "max_search_nodes");
    encode_u64_to(out, budget.max_search_nodes);
    encode_option_u64_to(out, "max_depth", budget.max_depth);
    encode_option_u64_to(out, "max_repair_steps", budget.max_repair_steps);
}

fn encode_fallback_policy_to(out: &mut Vec<u8>, fallback: &ProofSketchFallbackPolicy) {
    encode_string_to(out, "action");
    encode_string_to(out, fallback.action.wire());
    encode_option_string_to(
        out,
        "fallback_node_id",
        fallback.fallback_node_id.as_deref(),
    );
    encode_string_to(out, "repair_profile");
    match fallback.repair_profile {
        Some(profile) => {
            out.push(1);
            encode_string_to(out, profile.wire());
        }
        None => out.push(0),
    }
}

fn encode_edge_to(out: &mut Vec<u8>, edge: &ProofSketchEdge) {
    encode_string_to(out, "from");
    encode_string_to(out, &edge.from);
    encode_string_to(out, "to");
    encode_string_to(out, &edge.to);
    encode_string_to(out, "kind");
    encode_string_to(out, edge.kind.wire());
}

fn encode_revision_engine_stop_reason_to(
    out: &mut Vec<u8>,
    stop_reason: Option<&ProofSketchRevisionEngineStopReason>,
) {
    match stop_reason {
        Some(reason) => {
            out.push(1);
            encode_string_to(out, "kind");
            encode_string_to(out, reason.wire());
            match reason {
                ProofSketchRevisionEngineStopReason::MaxRevisionDepth { max } => {
                    encode_string_to(out, "max");
                    encode_u64_to(out, u64::from(*max));
                }
                ProofSketchRevisionEngineStopReason::RepeatedDiagnosticHash {
                    diagnostic_hash,
                    count,
                    max,
                } => {
                    encode_string_to(out, "diagnostic_hash");
                    encode_hash_to(out, diagnostic_hash);
                    encode_string_to(out, "count");
                    encode_u64_to(out, *count as u64);
                    encode_string_to(out, "max");
                    encode_u64_to(out, *max as u64);
                }
                ProofSketchRevisionEngineStopReason::RepeatedPatchHash { patch_hash } => {
                    encode_string_to(out, "patch_hash");
                    encode_hash_to(out, patch_hash);
                }
            }
        }
        None => out.push(0),
    }
}

fn encode_revision_dependency_invalidation_to(
    out: &mut Vec<u8>,
    invalidation: &ProofSketchRevisionDependencyInvalidation,
) {
    encode_string_to(out, "kind");
    encode_string_to(out, invalidation.wire());
    match invalidation {
        ProofSketchRevisionDependencyInvalidation::AffectedSubDagOnly => {}
        ProofSketchRevisionDependencyInvalidation::Broader {
            invalidated_node_ids,
            diagnostic_hash,
        } => {
            encode_string_to(out, "invalidated_node_ids");
            let mut invalidated_node_ids = invalidated_node_ids.clone();
            invalidated_node_ids.sort();
            invalidated_node_ids.dedup();
            encode_len_to(out, invalidated_node_ids.len());
            for node_id in &invalidated_node_ids {
                encode_string_to(out, node_id);
            }
            encode_string_to(out, "diagnostic_hash");
            encode_hash_to(out, diagnostic_hash);
        }
    }
}

fn encode_string_set_to(out: &mut Vec<u8>, values: &[String]) {
    let mut values = values.to_vec();
    values.sort();
    values.dedup();
    encode_len_to(out, values.len());
    for value in &values {
        encode_string_to(out, value);
    }
}

fn encode_hash_set_to(out: &mut Vec<u8>, hashes: &[Hash]) {
    let mut hashes = hashes.to_vec();
    hashes.sort();
    hashes.dedup();
    encode_len_to(out, hashes.len());
    for hash in &hashes {
        encode_hash_to(out, hash);
    }
}

fn encode_revision_patch_kind_to(out: &mut Vec<u8>, patch: &ProofSketchRevisionPatchKind) {
    match patch {
        ProofSketchRevisionPatchKind::ReplaceNode { node } => {
            encode_string_to(out, "replace_node");
            encode_node_to(out, node);
        }
        ProofSketchRevisionPatchKind::SplitNode {
            original_node_id,
            replacement_node_ids,
        } => {
            encode_string_to(out, "split_node");
            encode_string_to(out, "original_node_id");
            encode_string_to(out, original_node_id);
            encode_string_to(out, "replacement_node_ids");
            encode_len_to(out, replacement_node_ids.len());
            for node_id in replacement_node_ids {
                encode_string_to(out, node_id);
            }
        }
        ProofSketchRevisionPatchKind::MergeNodes {
            merged_node_id,
            source_node_ids,
        } => {
            encode_string_to(out, "merge_nodes");
            encode_string_to(out, "merged_node_id");
            encode_string_to(out, merged_node_id);
            encode_string_to(out, "source_node_ids");
            let mut source_node_ids = source_node_ids.clone();
            source_node_ids.sort();
            source_node_ids.dedup();
            encode_len_to(out, source_node_ids.len());
            for node_id in &source_node_ids {
                encode_string_to(out, node_id);
            }
        }
        ProofSketchRevisionPatchKind::InsertLemma {
            node_id,
            local_lemma_proposal_hash,
        } => {
            encode_string_to(out, "insert_lemma");
            encode_string_to(out, "node_id");
            encode_string_to(out, node_id);
            encode_string_to(out, "local_lemma_proposal_hash");
            encode_hash_to(out, local_lemma_proposal_hash);
        }
        ProofSketchRevisionPatchKind::RemoveLemma { lemma_id } => {
            encode_string_to(out, "remove_lemma");
            encode_string_to(out, "lemma_id");
            encode_string_to(out, lemma_id);
        }
        ProofSketchRevisionPatchKind::ChangeStrategy {
            node_id,
            strategy_hints,
            repair_profile,
        } => {
            encode_string_to(out, "change_strategy");
            encode_string_to(out, "node_id");
            encode_string_to(out, node_id);
            encode_string_to(out, "strategy_hints");
            let mut strategy_hints = strategy_hints.clone();
            strategy_hints.sort();
            strategy_hints.dedup();
            encode_len_to(out, strategy_hints.len());
            for hint in &strategy_hints {
                encode_string_to(out, hint.wire());
            }
            encode_string_to(out, "repair_profile");
            match repair_profile {
                Some(profile) => {
                    out.push(1);
                    encode_string_to(out, profile.wire());
                }
                None => out.push(0),
            }
        }
        ProofSketchRevisionPatchKind::ChangePremiseSet {
            node_id,
            premise_hashes,
        } => {
            encode_string_to(out, "change_premise_set");
            encode_string_to(out, "node_id");
            encode_string_to(out, node_id);
            encode_string_to(out, "premise_hashes");
            let mut premise_hashes = premise_hashes.clone();
            premise_hashes.sort();
            premise_hashes.dedup();
            encode_len_to(out, premise_hashes.len());
            for hash in &premise_hashes {
                encode_hash_to(out, hash);
            }
        }
        ProofSketchRevisionPatchKind::IncreaseBudget { node_id, budget } => {
            encode_string_to(out, "increase_budget");
            encode_string_to(out, "node_id");
            encode_string_to(out, node_id);
            encode_string_to(out, "budget");
            encode_budget_to(out, budget);
        }
        ProofSketchRevisionPatchKind::MarkCounterexample {
            node_id,
            diagnostic_hash,
        } => {
            encode_string_to(out, "mark_counterexample");
            encode_string_to(out, "node_id");
            encode_string_to(out, node_id);
            encode_string_to(out, "diagnostic_hash");
            encode_hash_to(out, diagnostic_hash);
        }
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

fn encode_option_hash_to(out: &mut Vec<u8>, field: &str, value: Option<&Hash>) {
    encode_string_to(out, field);
    match value {
        Some(hash) => {
            out.push(1);
            encode_hash_to(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_option_string_to(out: &mut Vec<u8>, field: &str, value: Option<&str>) {
    encode_string_to(out, field);
    match value {
        Some(value) => {
            out.push(1);
            encode_string_to(out, value);
        }
        None => out.push(0),
    }
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

fn encode_i64_to(out: &mut Vec<u8>, value: i64) {
    out.push(b'i');
    out.extend(value.to_be_bytes());
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.push(b'u');
    out.extend(value.to_be_bytes());
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    encode_u64_to(out, len as u64);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    fn fixture_path(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate has workspace parent")
            .parent()
            .expect("workspace has repo root")
            .join("../npa/develop/proof-using-agents/fixtures/pua-m08-proof-sketch")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("proof sketch fixture should exist")
    }

    fn parse_fixture(name: &str) -> ProofSketch {
        parse_proof_sketch(&fixture(name)).expect("fixture should parse")
    }

    fn hash_of(name: &str) -> Hash {
        proof_sketch_hash(&parse_fixture(name))
    }

    fn expect_error(name: &str) -> ProofSketchSchemaErrorKind {
        parse_proof_sketch(&fixture(name))
            .expect_err("fixture should be rejected")
            .kind()
            .clone()
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn hash_wire(byte: u8) -> String {
        format!("sha256:{}", format!("{byte:02x}").repeat(32))
    }

    fn affected_subdag_only() -> ProofSketchRevisionDependencyInvalidation {
        ProofSketchRevisionDependencyInvalidation::AffectedSubDagOnly
    }

    fn minimal_node_json(node_id: &str) -> String {
        format!(
            r#"{{
              "node_id":"{node_id}",
              "kind":"introduce",
              "input_context_hash":"sha256:4444444444444444444444444444444444444444444444444444444444444444",
              "output_context_hash":"sha256:5555555555555555555555555555555555555555555555555555555555555555",
              "expected_effect":{{"kind":"introduces_locals","goal_delta":0}},
              "strategy_hints":["introduce_local"],
              "budget":{{"max_candidates":1,"max_search_nodes":4}},
              "fallback_policy":{{"action":"fail"}}
            }}"#
        )
    }

    fn proof_sketch_json_with_nodes(nodes_json: &str, edges_json: &str) -> String {
        format!(
            r#"{{
              "api_version":"npa.proof-sketch.v1",
              "sketch_id":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
              "target_statement_identity":{{
                "statement_hash":"sha256:1111111111111111111111111111111111111111111111111111111111111111",
                "input_context_hash":"sha256:1212121212121212121212121212121212121212121212121212121212121212",
                "output_context_hash":"sha256:1313131313131313131313131313131313131313131313131313131313131313"
              }},
              "environment_hash":"sha256:2222222222222222222222222222222222222222222222222222222222222222",
              "policy_hash":"sha256:3333333333333333333333333333333333333333333333333333333333333333",
              "sublemma_statement_proposals":[],
              "nodes":[{nodes_json}],
              "edges":[{edges_json}]
            }}"#
        )
    }

    #[test]
    fn proof_sketch_schema_accepts_minimal_fixture_and_hash_is_stable() {
        let sketch = parse_fixture("minimal-valid.json");
        assert_eq!(sketch.api_version, PROOF_SKETCH_API_VERSION);
        assert_eq!(sketch.nodes.len(), 2);
        assert_eq!(sketch.edges.len(), 1);
        assert_eq!(
            proof_sketch_hash(&sketch),
            proof_sketch_hash(&parse_fixture("minimal-valid.json"))
        );
        assert!(proof_sketch_hash_string(&sketch).starts_with("sha256:"));
    }

    #[test]
    fn proof_sketch_schema_rejects_negative_fixtures() {
        assert!(matches!(
            expect_error("duplicate-node-id.json"),
            ProofSketchSchemaErrorKind::DuplicateNodeId { .. }
        ));
        assert!(matches!(
            expect_error("unknown-node-kind.json"),
            ProofSketchSchemaErrorKind::InvalidNodeKind { .. }
        ));
        assert!(matches!(
            expect_error("missing-target-identity.json"),
            ProofSketchSchemaErrorKind::MissingField {
                field: "target_statement_identity"
            }
        ));
        assert!(matches!(
            expect_error("malformed-hash.json"),
            ProofSketchSchemaErrorKind::InvalidHash { .. }
        ));
        assert!(matches!(
            expect_error("duplicate-key.json"),
            ProofSketchSchemaErrorKind::DuplicateKey { .. }
        ));
    }

    #[test]
    fn proof_sketch_schema_score_and_display_only_changes_do_not_change_hash() {
        assert_eq!(
            hash_of("minimal-valid.json"),
            hash_of("score-only-variant.json")
        );
    }

    #[test]
    fn proof_sketch_schema_identity_changes_affect_hash() {
        let base = parse_fixture("minimal-valid.json");

        let mut changed = base.clone();
        changed.sketch_id = [0x9a; 32];
        assert_eq!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.target_statement_identity.statement_hash = [0x99; 32];
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.environment_hash = [0x98; 32];
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.policy_hash = [0x97; 32];
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.target_statement_identity.output_context_hash = [0x96; 32];
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.nodes[0].expected_effect.goal_delta += 1;
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.nodes[0].input_context_hash = [0x95; 32];
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.nodes[0].fallback_policy.action = ProofSketchFallbackAction::ExpandSearch;
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.nodes[0].budget.max_search_nodes += 1;
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed.edges[0].kind = ProofSketchEdgeKind::Feeds;
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        let mut changed = base.clone();
        changed
            .sublemma_statement_proposals
            .push(ProofSketchSublemmaStatementProposal {
                proposal_id: "p1".to_owned(),
                statement_hash: [0x94; 32],
                input_context_hash: [0x93; 32],
                output_context_hash: [0x92; 32],
                generalization_policy: ProofSketchGeneralizationPolicy::LocalsOnly,
                display: None,
            });
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));
    }

    #[test]
    fn proof_sketch_schema_array_order_is_not_identity() {
        let base = parse_fixture("minimal-valid.json");
        let reordered = parse_fixture("reordered-nodes.json");
        assert_eq!(proof_sketch_hash(&base), proof_sketch_hash(&reordered));
    }

    #[test]
    fn sketch_validator_dag_accepts_context_edges_and_orders_deterministically() {
        let base = parse_fixture("minimal-valid.json");
        let profile = ProofSketchValidationProfile::strict(base.environment_hash, base.policy_hash);
        let report = validate_proof_sketch_with_profile(&base, &profile)
            .expect("minimal sketch should validate");
        assert_eq!(report.sketch_hash, proof_sketch_hash(&base));
        assert_eq!(
            report.topological_node_ids,
            vec!["n1".to_owned(), "n2".to_owned()]
        );
        assert_eq!(report.root_node_ids, vec!["n1".to_owned()]);
        assert_eq!(report.terminal_node_ids, vec!["n2".to_owned()]);
        assert_eq!(report.nodes[0].successor_node_ids, vec!["n2".to_owned()]);
        assert_eq!(report.nodes[1].predecessor_node_ids, vec!["n1".to_owned()]);

        let reordered = parse_fixture("reordered-nodes.json");
        let reordered_report = validate_proof_sketch_with_profile(&reordered, &profile)
            .expect("reordered equivalent sketch should validate");
        assert_eq!(report, reordered_report);

        let mut feeds = base.clone();
        feeds.edges[0].kind = ProofSketchEdgeKind::Feeds;
        assert!(validate_proof_sketch(&feeds).is_ok());

        let mut discharges = base;
        discharges.edges[0].kind = ProofSketchEdgeKind::Discharges;
        assert!(validate_proof_sketch(&discharges).is_ok());
    }

    #[test]
    fn sketch_validator_dag_rejects_profile_and_base_identity_mismatches() {
        let base = parse_fixture("minimal-valid.json");

        let err = validate_proof_sketch_with_profile(
            &base,
            &ProofSketchValidationProfile::strict(hash(0xfe), base.policy_hash),
        )
        .expect_err("environment mismatch should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::EnvironmentMismatch { .. }
        ));

        let err = validate_proof_sketch_with_profile(
            &base,
            &ProofSketchValidationProfile::strict(base.environment_hash, hash(0xfd)),
        )
        .expect_err("policy mismatch should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::PolicyMismatch { .. }
        ));

        let unsupported_close = ProofSketchValidationProfile::default()
            .with_supported_node_kinds([ProofSketchNodeKind::Introduce]);
        let err = validate_proof_sketch_with_profile(&base, &unsupported_close)
            .expect_err("unsupported strict profile node kind should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::UnsupportedNodeKind {
                node_id,
                kind: ProofSketchNodeKind::CloseByExact
            } if node_id == "n2"
        ));
    }

    #[test]
    fn sketch_validator_dag_rejects_unknown_malformed_future_cycle_and_disconnected_nodes() {
        let base = parse_fixture("minimal-valid.json");

        let mut unknown = base.clone();
        unknown.edges = vec![ProofSketchEdge {
            from: "n1".to_owned(),
            to: "missing".to_owned(),
            kind: ProofSketchEdgeKind::DependsOn,
        }];
        let err = validate_proof_sketch(&unknown).expect_err("unknown node should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::UnknownNode { node_id } if node_id == "missing"
        ));

        let mut self_edge = base.clone();
        self_edge.edges = vec![ProofSketchEdge {
            from: "n1".to_owned(),
            to: "n1".to_owned(),
            kind: ProofSketchEdgeKind::DependsOn,
        }];
        let err = validate_proof_sketch(&self_edge).expect_err("self edge should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::MalformedEdge {
                reason: ProofSketchMalformedEdgeReason::SelfEdge,
                ..
            }
        ));

        let mut future = base.clone();
        future.edges = vec![ProofSketchEdge {
            from: "n2".to_owned(),
            to: "n1".to_owned(),
            kind: ProofSketchEdgeKind::DependsOn,
        }];
        let err = validate_proof_sketch(&future).expect_err("future reference should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::FutureReference { from, to, .. }
                if from == "n2" && to == "n1"
        ));

        let mut malformed_feed = base.clone();
        malformed_feed.nodes[1].input_context_hash = hash(0x99);
        malformed_feed.edges[0].kind = ProofSketchEdgeKind::Feeds;
        let err =
            validate_proof_sketch(&malformed_feed).expect_err("bad context flow should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::MalformedEdge {
                reason: ProofSketchMalformedEdgeReason::ContextFlowMismatch { .. },
                ..
            }
        ));

        let mut malformed_discharge = base.clone();
        let mut non_closing = malformed_discharge.nodes[0].clone();
        non_closing.node_id = "n3".to_owned();
        non_closing.input_context_hash = malformed_discharge.nodes[0].output_context_hash;
        non_closing.output_context_hash = hash(0x88);
        malformed_discharge.nodes.push(non_closing);
        malformed_discharge.edges = vec![ProofSketchEdge {
            from: "n1".to_owned(),
            to: "n3".to_owned(),
            kind: ProofSketchEdgeKind::Discharges,
        }];
        let err = validate_proof_sketch(&malformed_discharge)
            .expect_err("discharge target must close a goal");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::MalformedEdge {
                reason: ProofSketchMalformedEdgeReason::DischargeTargetDoesNotCloseGoal,
                ..
            }
        ));

        let mut cycle = base.clone();
        cycle.nodes[0].input_context_hash = hash(0x41);
        cycle.nodes[0].output_context_hash = hash(0x42);
        cycle.nodes[1].input_context_hash = hash(0x43);
        cycle.nodes[1].output_context_hash = hash(0x44);
        cycle.edges = vec![
            ProofSketchEdge {
                from: "n1".to_owned(),
                to: "n2".to_owned(),
                kind: ProofSketchEdgeKind::DependsOn,
            },
            ProofSketchEdge {
                from: "n2".to_owned(),
                to: "n1".to_owned(),
                kind: ProofSketchEdgeKind::DependsOn,
            },
        ];
        let err = validate_proof_sketch(&cycle).expect_err("cycle should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::Cycle { node_ids }
                if node_ids == &vec!["n1".to_owned(), "n2".to_owned()]
        ));

        let mut disconnected = base;
        let mut extra = disconnected.nodes[0].clone();
        extra.node_id = "n3".to_owned();
        extra.input_context_hash = hash(0x51);
        extra.output_context_hash = hash(0x52);
        disconnected.nodes.push(extra);
        let err =
            validate_proof_sketch(&disconnected).expect_err("disconnected node should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchValidationErrorKind::DisconnectedRequiredNode { node_id }
                if node_id == "n3"
        ));
    }

    #[test]
    fn proof_sketch_hash_round_trip_excludes_sidecars_and_tracks_semantics() {
        let base = parse_fixture("minimal-valid.json");
        let score_variant = parse_fixture("score-only-variant.json");
        assert_eq!(proof_sketch_hash(&base), proof_sketch_hash(&score_variant));

        let mut changed = base.clone();
        changed.nodes[0].display = Some(ProofSketchDisplay {
            label: Some("changed display".to_owned()),
            explanation: Some("display is advisory".to_owned()),
        });
        changed.advisory = Some(ProofSketchAdvisory {
            display_text: Some("changed score sidecar".to_owned()),
            score: Some("0.1".to_owned()),
            model_score: Some("0.2".to_owned()),
            scoring_profile: Some("changed".to_owned()),
        });
        assert_eq!(proof_sketch_hash(&base), proof_sketch_hash(&changed));

        changed.nodes[0].expected_effect.goal_delta += 1;
        assert_ne!(proof_sketch_hash(&base), proof_sketch_hash(&changed));
    }

    #[test]
    fn proof_sketch_hash_local_lemma_revision_and_minimization_identity() {
        let proposal = ProofSketchLocalLemmaProposal {
            proposal_id: "lemma1".to_owned(),
            base_sketch_hash: hash(1),
            source_node_id: "n1".to_owned(),
            statement_hash: hash(2),
            input_context_hash: hash(3),
            output_context_hash: hash(4),
            environment_hash: hash(5),
            policy_hash: hash(6),
            allowed_premise_hashes: vec![hash(8), hash(7)],
            state: ProofSketchLocalLemmaState::Proposed,
        };
        let mut reordered = proposal.clone();
        reordered.allowed_premise_hashes = vec![hash(7), hash(8)];
        reordered.state = ProofSketchLocalLemmaState::Available;
        assert_eq!(
            proof_sketch_local_lemma_proposal_hash(&proposal),
            proof_sketch_local_lemma_proposal_hash(&reordered)
        );
        assert!(proof_sketch_local_lemma_proposal_hash_string(&proposal).starts_with("sha256:"));

        let proposal_json = format!(
            r#"{{
              "proposal_id":"lemma1",
              "base_sketch_hash":"{}",
              "source_node_id":"n1",
              "statement_hash":"{}",
              "input_context_hash":"{}",
              "output_context_hash":"{}",
              "environment_hash":"{}",
              "policy_hash":"{}",
              "allowed_premise_hashes":["{}","{}"],
              "state":"proposed"
            }}"#,
            hash_wire(1),
            hash_wire(2),
            hash_wire(3),
            hash_wire(4),
            hash_wire(5),
            hash_wire(6),
            hash_wire(7),
            hash_wire(8)
        );
        assert_eq!(
            proof_sketch_local_lemma_proposal_hash(
                &parse_proof_sketch_local_lemma_proposal(&proposal_json)
                    .expect("local lemma proposal should decode")
            ),
            proof_sketch_local_lemma_proposal_hash(&proposal)
        );

        let mut changed = proposal.clone();
        changed.statement_hash = hash(9);
        assert_ne!(
            proof_sketch_local_lemma_proposal_hash(&proposal),
            proof_sketch_local_lemma_proposal_hash(&changed)
        );

        let base_node = parse_fixture("minimal-valid.json").nodes[0].clone();
        let local_lemma_hash = proof_sketch_local_lemma_proposal_hash(&proposal);
        let variants = [
            ProofSketchRevisionPatchKind::ReplaceNode {
                node: Box::new(base_node.clone()),
            },
            ProofSketchRevisionPatchKind::SplitNode {
                original_node_id: "n1".to_owned(),
                replacement_node_ids: vec!["n1a".to_owned(), "n1b".to_owned()],
            },
            ProofSketchRevisionPatchKind::MergeNodes {
                merged_node_id: "n12".to_owned(),
                source_node_ids: vec!["n2".to_owned(), "n1".to_owned()],
            },
            ProofSketchRevisionPatchKind::InsertLemma {
                node_id: "n1".to_owned(),
                local_lemma_proposal_hash: local_lemma_hash,
            },
            ProofSketchRevisionPatchKind::RemoveLemma {
                lemma_id: "lemma1".to_owned(),
            },
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "n1".to_owned(),
                strategy_hints: vec![
                    ProofSketchStrategyHint::ExactTerm,
                    ProofSketchStrategyHint::IntroduceLocal,
                ],
                repair_profile: Some(ProofSketchRepairProfile::LocalRepair),
            },
            ProofSketchRevisionPatchKind::ChangePremiseSet {
                node_id: "n1".to_owned(),
                premise_hashes: vec![hash(11), hash(10)],
            },
            ProofSketchRevisionPatchKind::IncreaseBudget {
                node_id: "n1".to_owned(),
                budget: ProofSketchBudget {
                    max_candidates: 2,
                    max_search_nodes: 8,
                    max_depth: Some(2),
                    max_repair_steps: Some(1),
                },
            },
            ProofSketchRevisionPatchKind::MarkCounterexample {
                node_id: "n1".to_owned(),
                diagnostic_hash: hash(12),
            },
        ];
        for patch in variants {
            let revision = ProofSketchRevisionPatch {
                base_sketch_hash: hash(1),
                dependency_invalidation: affected_subdag_only(),
                patch,
            };
            assert!(proof_sketch_revision_patch_hash_string(&revision).starts_with("sha256:"));
        }

        let first = ProofSketchRevisionPatch {
            base_sketch_hash: hash(1),
            dependency_invalidation: affected_subdag_only(),
            patch: ProofSketchRevisionPatchKind::ChangePremiseSet {
                node_id: "n1".to_owned(),
                premise_hashes: vec![hash(11), hash(10)],
            },
        };
        let second = ProofSketchRevisionPatch {
            base_sketch_hash: hash(1),
            dependency_invalidation: affected_subdag_only(),
            patch: ProofSketchRevisionPatchKind::ChangePremiseSet {
                node_id: "n1".to_owned(),
                premise_hashes: vec![hash(10), hash(11)],
            },
        };
        assert_eq!(
            proof_sketch_revision_patch_hash(&first),
            proof_sketch_revision_patch_hash(&second)
        );
        let revision_json = format!(
            r#"{{
              "base_sketch_hash":"{}",
              "patch":{{
                "kind":"change_premise_set",
                "node_id":"n1",
                "premise_hashes":["{}","{}"]
              }}
            }}"#,
            hash_wire(1),
            hash_wire(10),
            hash_wire(11)
        );
        assert_eq!(
            proof_sketch_revision_patch_hash(
                &parse_proof_sketch_revision_patch(&revision_json)
                    .expect("revision patch should decode")
            ),
            proof_sketch_revision_patch_hash(&first)
        );

        let minimization = ProofSketchMinimizationRecord {
            base_sketch_hash: hash(1),
            kind: ProofSketchMinimizationKind::RemoveUnusedLocalLemma,
            target_node_id: Some("n1".to_owned()),
            candidate_patch_hash: proof_sketch_revision_patch_hash(&first),
            replay_plan_hash: hash(13),
            verification_result_hash: hash(14),
            outcome: ProofSketchMinimizationOutcome::Accepted,
            score: Some("0.9".to_owned()),
        };
        let mut score_only = minimization.clone();
        score_only.score = Some("0.1".to_owned());
        assert_eq!(
            proof_sketch_minimization_record_hash(&minimization),
            proof_sketch_minimization_record_hash(&score_only)
        );
        let minimization_json = format!(
            r#"{{
              "base_sketch_hash":"{}",
              "kind":"remove_unused_local_lemma",
              "target_node_id":"n1",
              "candidate_patch_hash":"{}",
              "replay_plan_hash":"{}",
              "verification_result_hash":"{}",
              "outcome":"accepted",
              "score":0.1
            }}"#,
            hash_wire(1),
            format_hash_string(&proof_sketch_revision_patch_hash(&first)),
            hash_wire(13),
            hash_wire(14)
        );
        assert_eq!(
            proof_sketch_minimization_record_hash(
                &parse_proof_sketch_minimization_record(&minimization_json)
                    .expect("minimization record should decode")
            ),
            proof_sketch_minimization_record_hash(&minimization)
        );
        score_only.outcome = ProofSketchMinimizationOutcome::VerificationFailed;
        assert_ne!(
            proof_sketch_minimization_record_hash(&minimization),
            proof_sketch_minimization_record_hash(&score_only)
        );
    }

    fn revision_patch(
        sketch: &ProofSketch,
        patch: ProofSketchRevisionPatchKind,
    ) -> ProofSketchRevisionPatch {
        ProofSketchRevisionPatch {
            base_sketch_hash: proof_sketch_hash(sketch),
            dependency_invalidation: affected_subdag_only(),
            patch,
        }
    }

    fn strict_policy() -> ProofSketchRevisionPatchApplicationPolicy {
        ProofSketchRevisionPatchApplicationPolicy::strict_local()
    }

    fn removed_dependency(
        kind: ProofSketchMinimizationRemovedDependencyKind,
        byte: u8,
    ) -> ProofSketchMinimizationRemovedDependency {
        ProofSketchMinimizationRemovedDependency {
            kind,
            identity_hash: hash(byte),
            owner_node_id: Some("n2".to_owned()),
        }
    }

    fn sketch_minimization_fixture(
        sketch: &ProofSketch,
        removed_dependencies: Vec<ProofSketchMinimizationRemovedDependency>,
    ) -> (
        ProofSketchMinimizationCandidate,
        ProofSketchMinimizationDependencySnapshot,
    ) {
        let base_sketch_hash = proof_sketch_hash(sketch);
        let dependencies = ProofSketchMinimizationDependencySnapshot {
            last_verified_parent_proof_hash: hash(0x80),
            verified_certificate_identity_hash: hash(0x81),
            final_parent_dependency_hashes: vec![hash(0x82)],
            replay_plan_dependency_hashes: vec![hash(0x83)],
            certificate_import_identity_hashes: vec![hash(0x84)],
            axiom_dependency_hashes: vec![hash(0x85)],
            verified_dependency_identity_hashes: vec![hash(0x86)],
            axiom_summary_hash: hash(0x87),
        };
        let candidate = ProofSketchMinimizationCandidate {
            base_sketch_hash,
            kind: ProofSketchMinimizationKind::RemoveUnusedLocalLemma,
            target_node_id: Some("n2".to_owned()),
            candidate_patch_hash: hash(0x70),
            removed_dependencies,
            replay_verification: ProofSketchMinimizationReplayVerification {
                replay_base_sketch_hash: base_sketch_hash,
                replay_plan_hash: hash(0x90),
                verification_result_hash: hash(0x91),
                source_free_verification_hash: hash(0x92),
                replay_succeeded: true,
                verifier_succeeded: true,
                source_free_succeeded: true,
                certificate_identity_preserved: true,
                candidate_certificate_identity_hash: Some(hash(0x81)),
                certificate_import_identity_hashes: vec![hash(0x84)],
                axiom_summary_hash: hash(0x87),
            },
            score: Some("0.9".to_owned()),
        };
        (candidate, dependencies)
    }

    fn engine_policy() -> ProofSketchRevisionEnginePolicy {
        ProofSketchRevisionEnginePolicy::strict_local()
    }

    fn branched_revision_sketch() -> (ProofSketch, Hash, ProofSketchNode) {
        let mut sketch = parse_fixture("minimal-valid.json");
        let proposal = ProofSketchSublemmaStatementProposal {
            proposal_id: "lemma-n3".to_owned(),
            statement_hash: hash(0xa1),
            input_context_hash: hash(0xa2),
            output_context_hash: hash(0xa3),
            generalization_policy: ProofSketchGeneralizationPolicy::LocalsOnly,
            display: None,
        };
        let proposal_hash = proposal.statement_hash;
        sketch.sublemma_statement_proposals.push(proposal);
        let mut n3 = sketch.nodes[1].clone();
        n3.node_id = "n3".to_owned();
        n3.output_context_hash = hash(0x63);
        n3.premise_hashes = vec![proposal_hash];
        n3.display = None;
        let original_n3 = n3.clone();
        sketch.nodes.push(n3);
        sketch.edges.push(ProofSketchEdge {
            from: "n1".to_owned(),
            to: "n3".to_owned(),
            kind: ProofSketchEdgeKind::DependsOn,
        });
        sort_sketch_for_identity(&mut sketch);
        validate_proof_sketch(&sketch).expect("branched sketch should remain valid");
        (sketch, proposal_hash, original_n3)
    }

    fn local_strategy_patch(sketch: &ProofSketch) -> ProofSketchRevisionPatch {
        revision_patch(
            sketch,
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "n2".to_owned(),
                strategy_hints: vec![ProofSketchStrategyHint::BoundedSearch],
                repair_profile: Some(ProofSketchRepairProfile::LocalRepair),
            },
        )
    }

    fn failed_n2_context(
        diagnostic_hash: Hash,
        preserved_lemma_hash: Hash,
    ) -> ProofSketchRevisionEngineContext {
        ProofSketchRevisionEngineContext {
            evidence: vec![ProofSketchRevisionEvidence {
                kind: ProofSketchRevisionEvidenceKind::FailedSubgoal,
                node_id: Some("n2".to_owned()),
                hole_id: Some("h2".to_owned()),
                diagnostic_hash,
            }],
            hole_states: vec![
                ProofSketchRevisionHoleState {
                    hole_id: "h2".to_owned(),
                    owner_node_id: "n2".to_owned(),
                    solution_hash: None,
                    status: ProofSketchRevisionHoleStatus::Failed,
                },
                ProofSketchRevisionHoleState {
                    hole_id: "h3".to_owned(),
                    owner_node_id: "n3".to_owned(),
                    solution_hash: Some(hash(0x33)),
                    status: ProofSketchRevisionHoleStatus::Completed,
                },
            ],
            parent_integration_records: vec![ProofSketchRevisionParentIntegrationRecord {
                record_id: "parent".to_owned(),
                required_node_ids: vec!["n3".to_owned()],
                completed_hole_ids: vec!["h3".to_owned()],
                required_local_lemma_hashes: vec![preserved_lemma_hash],
            }],
            history: Vec::new(),
            revision_depth: 0,
        }
    }

    #[test]
    fn sketch_revision_patch_applies_local_strategy_without_touching_unaffected_subdag() {
        let sketch = parse_fixture("minimal-valid.json");
        let original_n2 = sketch
            .nodes
            .iter()
            .find(|node| node.node_id == "n2")
            .unwrap()
            .clone();
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "n1".to_owned(),
                strategy_hints: vec![ProofSketchStrategyHint::IntroduceLocal],
                repair_profile: Some(ProofSketchRepairProfile::LocalRepair),
            },
        );

        let application =
            apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy()).unwrap();
        assert_eq!(application.affected_node_ids, vec!["n1"]);
        assert!(application.invalidated_node_ids.is_empty());
        assert_eq!(
            application.patch_hash,
            proof_sketch_revision_patch_hash(&patch)
        );
        assert_ne!(
            application.resulting_sketch_hash,
            proof_sketch_hash(&sketch)
        );
        assert_eq!(
            application
                .resulting_sketch
                .nodes
                .iter()
                .find(|node| node.node_id == "n2")
                .unwrap(),
            &original_n2
        );
        assert_eq!(application.resulting_sketch.edges, sketch.edges);
    }

    #[test]
    fn sketch_revision_patch_rejects_stale_base_hash() {
        let sketch = parse_fixture("minimal-valid.json");
        let mut patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "n1".to_owned(),
                strategy_hints: vec![ProofSketchStrategyHint::IntroduceLocal],
                repair_profile: Some(ProofSketchRepairProfile::LocalRepair),
            },
        );
        patch.base_sketch_hash = hash(0xfe);

        let error = apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy())
            .expect_err("stale patch should reject");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::StaleBaseSketchHash { .. }
        ));
    }

    #[test]
    fn sketch_revision_patch_rejects_conflicting_node_replacement() {
        let sketch = parse_fixture("minimal-valid.json");
        let mut replacement = sketch
            .nodes
            .iter()
            .find(|node| node.node_id == "n1")
            .unwrap()
            .clone();
        replacement.output_context_hash = hash(0xa1);
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::ReplaceNode {
                node: Box::new(replacement),
            },
        );

        let error = apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy())
            .expect_err("context-changing replacement should reject without broad invalidation");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::ConflictingNodeReplacement {
                reason: ProofSketchRevisionConflictReason::ReplacementContextChanged,
                ..
            }
        ));
    }

    #[test]
    fn sketch_revision_patch_rejects_invalid_patch_target() {
        let sketch = parse_fixture("minimal-valid.json");
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "missing".to_owned(),
                strategy_hints: vec![ProofSketchStrategyHint::ExactTerm],
                repair_profile: Some(ProofSketchRepairProfile::LocalRepair),
            },
        );

        let error = apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy())
            .expect_err("unknown target should reject");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::InvalidPatchTarget { node_id }
                if node_id == "missing"
        ));
    }

    #[test]
    fn sketch_revision_patch_rejects_duplicate_inserted_lemma() {
        let sketch = parse_fixture("minimal-valid.json");
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::InsertLemma {
                node_id: "n1".to_owned(),
                local_lemma_proposal_hash: hash(0x44),
            },
        );

        let error = apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy())
            .expect_err("duplicate lemma node should reject");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::DuplicateInsertedLemma { node_id }
                if node_id == "n1"
        ));
    }

    #[test]
    fn sketch_revision_patch_requires_broader_invalidation_for_structural_changes() {
        let sketch = parse_fixture("minimal-valid.json");
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::SplitNode {
                original_node_id: "n1".to_owned(),
                replacement_node_ids: vec!["n1a".to_owned(), "n1b".to_owned()],
            },
        );

        let error = apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy())
            .expect_err("structural patch should require declared broad invalidation");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::BroaderDependencyInvalidationRequired {
                operation: "split_node",
                node_ids
            } if node_ids == &vec!["n1".to_owned()]
        ));
    }

    #[test]
    fn sketch_revision_patch_rejects_policy_expanding_changes() {
        let sketch = parse_fixture("minimal-valid.json");
        let strategy_patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::ChangeStrategy {
                node_id: "n1".to_owned(),
                strategy_hints: vec![ProofSketchStrategyHint::IntroduceLocal],
                repair_profile: Some(ProofSketchRepairProfile::FullReplan),
            },
        );
        let error = apply_proof_sketch_revision_patch(&sketch, &strategy_patch, &strict_policy())
            .expect_err("full replan profile should reject in local policy");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::PolicyExpandingPatchRejected {
                reason: ProofSketchRevisionPolicyRejection::RepairProfileNotAllowed,
                ..
            }
        ));

        let budget_patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::IncreaseBudget {
                node_id: "n1".to_owned(),
                budget: ProofSketchBudget {
                    max_candidates: 2048,
                    max_search_nodes: 100_001,
                    max_depth: Some(1025),
                    max_repair_steps: Some(1025),
                },
            },
        );
        let error = apply_proof_sketch_revision_patch(&sketch, &budget_patch, &strict_policy())
            .expect_err("over-policy budget increase should reject");
        assert!(matches!(
            error.kind(),
            ProofSketchRevisionPatchErrorKind::PolicyExpandingPatchRejected {
                reason: ProofSketchRevisionPolicyRejection::BudgetExceedsPolicy,
                ..
            }
        ));
    }

    #[test]
    fn sketch_revision_engine_patches_failed_hole_without_whole_restart() {
        let (sketch, proposal_hash, original_n3) = branched_revision_sketch();
        let patch = local_strategy_patch(&sketch);
        let context = failed_n2_context(hash(0xd1), proposal_hash);

        let output =
            run_proof_sketch_revision_engine(&sketch, &patch, &context, &engine_policy()).unwrap();

        assert_eq!(
            output.decision.outcome,
            ProofSketchRevisionDecisionOutcome::Applied
        );
        assert_eq!(output.decision.invalidated_node_ids, vec!["n2"]);
        assert_eq!(
            output.decision.preserved_node_ids,
            vec!["n1".to_owned(), "n3".to_owned()]
        );
        assert_eq!(output.decision.rescheduled_node_ids, vec!["n2"]);
        assert_eq!(output.decision.invalidated_hole_ids, vec!["h2"]);
        assert_eq!(output.decision.preserved_completed_hole_ids, vec!["h3"]);
        assert_eq!(
            output.decision.preserved_verified_local_lemma_hashes,
            vec![proposal_hash]
        );

        let application = output.application.expect("local patch should apply");
        assert_eq!(application.affected_node_ids, vec!["n2"]);
        assert_eq!(
            application
                .resulting_sketch
                .nodes
                .iter()
                .find(|node| node.node_id == "n3")
                .unwrap(),
            &original_n3
        );
        assert!(application
            .resulting_sketch
            .sublemma_statement_proposals
            .iter()
            .any(|proposal| proposal.statement_hash == proposal_hash));
    }

    #[test]
    fn sketch_revision_engine_repeated_diagnostic_stops_with_structured_reason() {
        let (sketch, proposal_hash, _) = branched_revision_sketch();
        let patch = local_strategy_patch(&sketch);
        let mut context = failed_n2_context(hash(0xd2), proposal_hash);
        context.history.push(ProofSketchRevisionHistoryEntry {
            patch_hash: hash(0xee),
            diagnostic_hash: Some(hash(0xd2)),
            resulting_sketch_hash: Some(hash(0xef)),
        });

        let output =
            run_proof_sketch_revision_engine(&sketch, &patch, &context, &engine_policy()).unwrap();

        assert_eq!(
            output.decision.outcome,
            ProofSketchRevisionDecisionOutcome::Stopped
        );
        assert!(matches!(
            output.decision.stop_reason,
            Some(ProofSketchRevisionEngineStopReason::RepeatedDiagnosticHash {
                diagnostic_hash,
                count: 2,
                max: 1
            }) if diagnostic_hash == hash(0xd2)
        ));
        assert!(output.application.is_none());
    }

    #[test]
    fn sketch_revision_engine_outputs_are_deterministic() {
        let (sketch, proposal_hash, _) = branched_revision_sketch();
        let patch = local_strategy_patch(&sketch);
        let context = failed_n2_context(hash(0xd3), proposal_hash);

        let first =
            run_proof_sketch_revision_engine(&sketch, &patch, &context, &engine_policy()).unwrap();
        let second =
            run_proof_sketch_revision_engine(&sketch, &patch, &context, &engine_policy()).unwrap();

        assert_eq!(first, second);
        assert_eq!(
            first.decision_hash,
            proof_sketch_revision_decision_hash(&first.decision)
        );
        assert!(proof_sketch_revision_decision_hash_string(&first.decision).starts_with("sha256:"));
    }

    #[test]
    fn repair_depth_zero_stops_sketch_revision_before_patch_application() {
        let (sketch, proposal_hash, _) = branched_revision_sketch();
        let patch = local_strategy_patch(&sketch);
        let context = failed_n2_context(hash(0xd4), proposal_hash);
        let policy = ProofSketchRevisionEnginePolicy {
            max_revision_depth: 0,
            ..engine_policy()
        };

        let output = run_proof_sketch_revision_engine(&sketch, &patch, &context, &policy).unwrap();

        assert_eq!(
            output.decision.outcome,
            ProofSketchRevisionDecisionOutcome::Stopped
        );
        assert!(matches!(
            output.decision.stop_reason,
            Some(ProofSketchRevisionEngineStopReason::MaxRevisionDepth { max: 0 })
        ));
        assert!(output.application.is_none());
    }

    #[test]
    fn sketch_revision_patch_mark_counterexample_is_sidecar_only() {
        let sketch = parse_fixture("minimal-valid.json");
        let patch = revision_patch(
            &sketch,
            ProofSketchRevisionPatchKind::MarkCounterexample {
                node_id: "n2".to_owned(),
                diagnostic_hash: hash(0xc0),
            },
        );

        let application =
            apply_proof_sketch_revision_patch(&sketch, &patch, &strict_policy()).unwrap();
        assert_eq!(application.counterexample_diagnostic_hash, Some(hash(0xc0)));
        assert_eq!(
            application.resulting_sketch_hash,
            proof_sketch_hash(&sketch)
        );
        assert_eq!(application.resulting_sketch.nodes, sketch.nodes);
        assert_eq!(
            application
                .resulting_sketch
                .sublemma_statement_proposals
                .len(),
            sketch.sublemma_statement_proposals.len()
        );
    }

    #[test]
    fn sketch_minimization_pass_framework_lists_ws05_passes() {
        assert_eq!(
            PROOF_SKETCH_MINIMIZATION_PASS_KINDS,
            [
                ProofSketchMinimizationKind::RemoveUnusedLocalLemma,
                ProofSketchMinimizationKind::ReplaceHoleWithExactTerm,
                ProofSketchMinimizationKind::CollapseRewrites,
                ProofSketchMinimizationKind::RemoveDuplicatePremiseApplication,
                ProofSketchMinimizationKind::ExtractSharedBranchSubproof,
                ProofSketchMinimizationKind::ReduceImportClosure,
            ]
        );
        let wires = PROOF_SKETCH_MINIMIZATION_PASS_KINDS
            .iter()
            .map(|kind| kind.wire())
            .collect::<Vec<_>>();
        assert_eq!(
            wires,
            vec![
                "remove_unused_local_lemma",
                "replace_hole_with_exact_term",
                "collapse_rewrites",
                "remove_duplicate_premise_application",
                "extract_shared_branch_subproof",
                "reduce_import_closure",
            ]
        );
    }

    #[test]
    fn sketch_minimization_accepts_unused_dependencies_after_replay_and_source_free_verify() {
        let sketch = parse_fixture("minimal-valid.json");
        let (candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![
                removed_dependency(
                    ProofSketchMinimizationRemovedDependencyKind::LocalLemma,
                    0x40,
                ),
                removed_dependency(ProofSketchMinimizationRemovedDependencyKind::Hole, 0x41),
                removed_dependency(ProofSketchMinimizationRemovedDependencyKind::Premise, 0x42),
                removed_dependency(ProofSketchMinimizationRemovedDependencyKind::Import, 0x43),
            ],
        );

        let decision =
            validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies).unwrap();

        assert_eq!(
            decision.record.outcome,
            ProofSketchMinimizationOutcome::Accepted
        );
        assert_eq!(
            decision.record.replay_plan_hash,
            candidate.replay_verification.replay_plan_hash
        );
        assert_eq!(
            decision.source_free_verification_hash,
            candidate.replay_verification.source_free_verification_hash
        );
        assert_eq!(
            decision.last_verified_parent_proof_hash,
            dependencies.last_verified_parent_proof_hash
        );
        assert_eq!(
            decision.removed_dependency_identity_hashes,
            vec![hash(0x40), hash(0x41), hash(0x42), hash(0x43)]
        );
        assert!(decision
            .preserved_dependency_identity_hashes
            .contains(&dependencies.verified_dependency_identity_hashes[0]));

        let mut score_only = candidate.clone();
        score_only.score = Some("0.1".to_owned());
        let score_only_decision =
            check_proof_sketch_minimization_step(&sketch, &score_only, &dependencies).unwrap();
        assert_eq!(decision.record_hash, score_only_decision.record_hash);
    }

    #[test]
    fn sketch_minimization_rejects_required_verified_dependency_removal() {
        let sketch = parse_fixture("minimal-valid.json");
        let (candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![removed_dependency(
                ProofSketchMinimizationRemovedDependencyKind::Premise,
                0x86,
            )],
        );

        let error = validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
            .expect_err("verified dependency removal should reject");

        assert_eq!(
            error.last_verified_parent_proof_hash(),
            dependencies.last_verified_parent_proof_hash
        );
        assert_eq!(
            error.rejected_record().outcome,
            ProofSketchMinimizationOutcome::Rejected
        );
        assert!(matches!(
            error.kind(),
            ProofSketchMinimizationErrorKind::RequiredDependencyRemoval {
                dependency,
                protected_by: ProofSketchMinimizationDependencyUse::VerifiedDependencyIdentityList
            } if dependency.identity_hash == hash(0x86)
        ));
    }

    #[test]
    fn sketch_minimization_rejects_final_parent_replay_import_and_axiom_dependency_removal() {
        let sketch = parse_fixture("minimal-valid.json");
        for (identity_byte, expected_use) in [
            (0x82, ProofSketchMinimizationDependencyUse::FinalParentProof),
            (0x83, ProofSketchMinimizationDependencyUse::ReplayPlan),
            (
                0x84,
                ProofSketchMinimizationDependencyUse::CertificateImportIdentity,
            ),
            (0x85, ProofSketchMinimizationDependencyUse::AxiomSummary),
            (0x87, ProofSketchMinimizationDependencyUse::AxiomSummary),
        ] {
            let (candidate, dependencies) = sketch_minimization_fixture(
                &sketch,
                vec![removed_dependency(
                    ProofSketchMinimizationRemovedDependencyKind::Import,
                    identity_byte,
                )],
            );

            let error = validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
                .expect_err("protected dependency removal should reject");

            assert!(matches!(
                error.kind(),
                ProofSketchMinimizationErrorKind::RequiredDependencyRemoval {
                    protected_by,
                    ..
                } if *protected_by == expected_use
            ));
        }
    }

    #[test]
    fn sketch_minimization_rejects_axiom_profile_change() {
        let sketch = parse_fixture("minimal-valid.json");
        let (mut candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![removed_dependency(
                ProofSketchMinimizationRemovedDependencyKind::LocalLemma,
                0x40,
            )],
        );
        candidate.replay_verification.axiom_summary_hash = hash(0xaa);

        let error = validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
            .expect_err("axiom profile changes should reject");

        assert!(matches!(
            error.kind(),
            ProofSketchMinimizationErrorKind::AxiomProfileChanged { expected, actual }
                if *expected == hash(0x87) && *actual == hash(0xaa)
        ));
    }

    #[test]
    fn sketch_minimization_rejects_certificate_change_without_reverification() {
        let sketch = parse_fixture("minimal-valid.json");
        let (mut candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![removed_dependency(
                ProofSketchMinimizationRemovedDependencyKind::Premise,
                0x40,
            )],
        );
        candidate.replay_verification.certificate_identity_preserved = false;
        candidate.replay_verification.source_free_succeeded = false;
        candidate
            .replay_verification
            .candidate_certificate_identity_hash = Some(hash(0xab));

        let error = validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
            .expect_err("certificate changes without source-free verification should reject");

        assert!(matches!(
            error.kind(),
            ProofSketchMinimizationErrorKind::CertificateChangedWithoutReverification {
                candidate_certificate_identity_hash
            } if *candidate_certificate_identity_hash == hash(0xab)
        ));
    }

    #[test]
    fn sketch_minimization_rejects_stale_replay_result_and_preserves_last_verified_parent() {
        let sketch = parse_fixture("minimal-valid.json");
        let (mut candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![removed_dependency(
                ProofSketchMinimizationRemovedDependencyKind::Import,
                0x40,
            )],
        );
        candidate.replay_verification.replay_base_sketch_hash = hash(0xee);

        let error = validate_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
            .expect_err("stale replay should reject");

        assert_eq!(
            error.last_verified_parent_proof_hash(),
            dependencies.last_verified_parent_proof_hash
        );
        assert_eq!(
            error.rejected_record().outcome,
            ProofSketchMinimizationOutcome::StaleBase
        );
        assert!(matches!(
            error.kind(),
            ProofSketchMinimizationErrorKind::StaleReplayResult {
                expected_base_sketch_hash,
                replay_base_sketch_hash
            } if *expected_base_sketch_hash == proof_sketch_hash(&sketch)
                && *replay_base_sketch_hash == hash(0xee)
        ));
    }

    #[test]
    fn ai_search_minimize_sketch_gate_requires_source_free_verify_before_accepting() {
        let sketch = parse_fixture("minimal-valid.json");
        let (mut candidate, dependencies) = sketch_minimization_fixture(
            &sketch,
            vec![removed_dependency(
                ProofSketchMinimizationRemovedDependencyKind::Hole,
                0x40,
            )],
        );
        candidate.replay_verification.source_free_succeeded = false;

        let error = check_proof_sketch_minimization_step(&sketch, &candidate, &dependencies)
            .expect_err("ai search minimization sidecar should require source-free verify");

        assert_eq!(
            error.last_verified_parent_proof_hash(),
            dependencies.last_verified_parent_proof_hash
        );
        assert!(matches!(
            error.kind(),
            ProofSketchMinimizationErrorKind::SourceFreeVerificationRequired
        ));
    }

    #[test]
    fn proof_sketch_strict_decode_rejects_structured_schema_failures() {
        assert!(matches!(
            expect_error("malformed-hash.json"),
            ProofSketchSchemaErrorKind::InvalidHash { .. }
        ));
        assert!(matches!(
            expect_error("duplicate-key.json"),
            ProofSketchSchemaErrorKind::DuplicateKey { .. }
        ));
        assert!(matches!(
            expect_error("unknown-node-kind.json"),
            ProofSketchSchemaErrorKind::InvalidNodeKind { .. }
        ));

        let oversized_nodes = (0..=MAX_NODES)
            .map(|index| minimal_node_json(&format!("n{index}")))
            .collect::<Vec<_>>()
            .join(",");
        let err = parse_proof_sketch(&proof_sketch_json_with_nodes(&oversized_nodes, ""))
            .expect_err("oversized nodes should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::ArrayLengthOutOfRange { .. }
        ));

        let bad_edge = r#"{"from":"n0","to":"missing","kind":"depends_on"}"#;
        let err = parse_proof_sketch(&proof_sketch_json_with_nodes(
            &minimal_node_json("n0"),
            bad_edge,
        ))
        .expect_err("unknown edge endpoint should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::UnknownNodeReference { .. }
        ));

        let oversized_display = fixture("minimal-valid.json").replace(
            r#""label": "intro""#,
            &format!(r#""label": "{}""#, "x".repeat(257)),
        );
        let err = parse_proof_sketch(&oversized_display)
            .expect_err("oversized display label should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::StringLengthOutOfRange { .. }
        ));

        let bad_local_lemma_state = format!(
            r#"{{
              "proposal_id":"lemma1",
              "base_sketch_hash":"{}",
              "source_node_id":"n1",
              "statement_hash":"{}",
              "input_context_hash":"{}",
              "output_context_hash":"{}",
              "environment_hash":"{}",
              "policy_hash":"{}",
              "allowed_premise_hashes":[],
              "state":"done"
            }}"#,
            hash_wire(1),
            hash_wire(2),
            hash_wire(3),
            hash_wire(4),
            hash_wire(5),
            hash_wire(6)
        );
        let err = parse_proof_sketch_local_lemma_proposal(&bad_local_lemma_state)
            .expect_err("unknown local lemma state should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::InvalidLocalLemmaState { .. }
        ));

        let revision_with_unknown_field = format!(
            r#"{{
              "base_sketch_hash":"{}",
              "patch":{{
                "kind":"change_premise_set",
                "node_id":"n1",
                "premise_hashes":[],
                "score":0.9
              }}
            }}"#,
            hash_wire(1)
        );
        let err = parse_proof_sketch_revision_patch(&revision_with_unknown_field)
            .expect_err("unknown revision patch field should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::UnknownField { .. }
        ));

        let affected_invalidation_with_payload = format!(
            r#"{{
              "base_sketch_hash":"{}",
              "dependency_invalidation":{{
                "kind":"affected_subdag_only",
                "invalidated_node_ids":["n1"],
                "diagnostic_hash":"{}"
              }},
              "patch":{{
                "kind":"mark_counterexample",
                "node_id":"n1",
                "diagnostic_hash":"{}"
              }}
            }}"#,
            hash_wire(1),
            hash_wire(2),
            hash_wire(3)
        );
        let err = parse_proof_sketch_revision_patch(&affected_invalidation_with_payload)
            .expect_err("affected-subdag invalidation payload should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::UnknownField { .. }
        ));

        let bad_minimization_outcome = format!(
            r#"{{
              "base_sketch_hash":"{}",
              "kind":"remove_unused_local_lemma",
              "candidate_patch_hash":"{}",
              "replay_plan_hash":"{}",
              "verification_result_hash":"{}",
              "outcome":"maybe"
            }}"#,
            hash_wire(1),
            hash_wire(2),
            hash_wire(3),
            hash_wire(4)
        );
        let err = parse_proof_sketch_minimization_record(&bad_minimization_outcome)
            .expect_err("unknown minimization outcome should reject");
        assert!(matches!(
            err.kind(),
            ProofSketchSchemaErrorKind::InvalidMinimizationOutcome { .. }
        ));
    }

    #[test]
    fn proof_sketch_schema_contract_file_mentions_identity_exclusions() {
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate has workspace parent")
            .parent()
            .expect("workspace has repo root");
        let schema = std::fs::read_to_string(
            repo_root.join("../npa/develop/proof-using-agents/schemas/proof_sketch.schema.json"),
        )
        .expect("schema should exist");
        for node_kind in PROOF_SKETCH_NODE_KINDS {
            assert!(schema.contains(node_kind));
        }
        assert!(schema.contains("expected_effect"));
        assert!(schema.contains("fallback_policy"));
        assert!(schema.contains("sketch_hash"));
        assert!(schema.contains("display text"));
        assert!(schema.contains("model scores"));
        assert!(schema.contains("wall-clock timing"));
        assert!(schema.contains("scheduling order"));

        let revision_schema = std::fs::read_to_string(repo_root.join(
            "../npa/develop/proof-using-agents/schemas/proof_sketch_revision_patch.schema.json",
        ))
        .expect("revision patch schema should exist");
        for patch_kind in [
            "replace_node",
            "split_node",
            "merge_nodes",
            "insert_lemma",
            "remove_lemma",
            "change_strategy",
            "change_premise_set",
            "increase_budget",
            "mark_counterexample",
        ] {
            assert!(revision_schema.contains(patch_kind));
        }
        assert!(revision_schema.contains("base_sketch_hash"));
        assert!(revision_schema.contains("dependency_invalidation"));
        assert!(revision_schema.contains("affected_subdag_only"));
        assert!(revision_schema.contains("broader"));
    }
}

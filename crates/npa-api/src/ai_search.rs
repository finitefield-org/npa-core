use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use npa_cert::{Hash, Name};
use npa_frontend::{
    lex_machine_surface_tokens, parse_machine_term, FileId, MachineSurfaceTokenKind, MachineTerm,
};
use npa_kernel::Level;
use npa_tactic::{
    goal_id_canonical_bytes, tactic_budget_hash, CandidateApplyArg, CandidateRewriteRuleRef,
    CasesPayload, ChangePayload, CongrPayload, ConstructorSelection, ContradictionMode,
    ContradictionPayload, GeneralInductionPayload, GeneralizePayload, GoalId, HavePayload,
    LocalLemmaInsertionPolicy, LocalLemmaProof, MachineTacticBatchPolicy, MachineTacticCandidate,
    OccurrencePath, RawMachineTerm, RefinePayload, RevertDependencyPolicy, RevertPayload,
    RewriteDirection, RewriteSite, SimpRuleRef, SmtLemmaRef, SpecializePayload,
    SpecializeResultPolicy, SubstPayload, SufficesContinuationPolicy, SufficesPayload,
    TacticBudget, TacticHead, TacticTarget, UnfoldPayload,
};
use sha2::{Digest, Sha256};

use crate::current::MachineAxiomRefWire;
use crate::json::{JsonMember, JsonValue, JsonValueKind};
use crate::prompt::FailedCandidateErrorKind;
use crate::renderer::MachineGlobalRefView;
use crate::search::{
    verified_premise_identity_json, MachinePremiseCandidateProvenance,
    MachinePremiseRankingMetadata, MachinePremiseSearchOkFields, MachinePremiseSetAxiomImpact,
    MachineRetrievalCacheKey, MachineVerifiedPremiseIdentity,
};
use crate::snapshot::{MachineSnapshotGetError, MachineSnapshotGetOk};
use crate::solver::{SolverFamily, SOLVER_CONTRACT_VERSION};
use crate::tactic::parse_deterministic_budget_with_error_kind;
use crate::theorem_graph::{
    certificate_theorem_graph_node_is_certificate_bound_public_export,
    certificate_theorem_graph_snapshot_hash, validate_certificate_theorem_graph_snapshot_sidecar,
    CertificateTheoremGraphEdgeKind, CertificateTheoremGraphError, CertificateTheoremGraphNode,
    CertificateTheoremGraphNodeId, CertificateTheoremGraphNodeScope,
    CertificateTheoremGraphSnapshot, CertificateTheoremGraphSnapshotSidecar,
    CertificateTheoremGraphSnapshotValidationOptions,
};
use crate::types::{
    format_goal_id_wire, format_hash_string, is_machine_local_name, MachineApiCompactErrorWire,
    MachineApiErrorWire, MachineApiOkResponse, MachineApiResponseEnvelope,
    MachineApiResponseStatus, MachineApiVersion, MachineGoalView, MachineLocalView,
    MachineProofSession, MachineProofSnapshot, SessionId, SnapshotId,
};
use crate::validation::{
    parse_request_body, parse_strict_u64_token, validate_json_object, FieldSpec, JsonFieldType,
    JsonPath, MachineApiErrorKind, MachineApiRequestError, MachineApiRequestErrorReason,
    ObjectSchema, StrictUnsignedIntegerError, ValidatedObject,
};
use crate::{
    get_machine_snapshot, parse_machine_replay_request, parse_machine_tactic_batch_request,
    parse_machine_theorem_search_request, parse_machine_verify_request, run_machine_replay_request,
    run_machine_tactic_batch_request, run_machine_verify_request, search_machine_theorems_for_goal,
    MachineApiTacticKind, MachineBatchSchedulerLimits, MachineReplayError, MachineReplayOkFields,
    MachineReplayResponse, MachineTacticBatchError, MachineTacticBatchItemResponse,
    MachineTacticBatchOkFields, MachineTacticBatchResponse, MachineTacticBatchSchedulerFields,
    MachineTheoremMode, MachineTheoremSearchError, MachineTheoremSearchOkFields,
    MachineTheoremSearchResponse, MachineTheoremSearchResult, MachineVerifyError,
    MachineVerifyOkFields, MachineVerifyResponse,
};

const AI_SEARCH_MVP_MAX_TACTICS_PER_NODE: u32 = 16;
const AI_SEARCH_MVP_PREMISE_QUERY_LIMIT: u32 = 32;
const AI_SEARCH_CANDIDATE_PAYLOAD_HASH_TAG: &str = "npa.ai-search.candidate-payload.v1";
pub const AI_SEARCH_TRAINING_TRACE_SCHEMA: &str = "npa.ai-search.training-trace.v1";
const AI_SEARCH_POSITIVE_TRAINING_IDENTITY_HASH_TAG: &str =
    "npa.ai-search.training-positive-identity.v1";
const AI_SEARCH_NEGATIVE_TRAINING_IDENTITY_HASH_TAG: &str =
    "npa.ai-search.training-negative-identity.v1";
pub const AI_SEARCH_FOCUSED_REPLAY_PAYLOAD_SCHEMA: &str = "npa.ai-search.focused-replay-payload.v1";

const AI_SEARCH_CONFIG_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("search_budget", JsonFieldType::Object),
    FieldSpec::required("per_tactic_deterministic_budget", JsonFieldType::Object),
    FieldSpec::required("batch_policy", JsonFieldType::Object),
];

const AI_SEARCH_SEARCH_BUDGET_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "wall_clock_ms",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_nodes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_tactics_per_node",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_depth",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

const AI_SEARCH_BATCH_POLICY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "max_evaluated_candidates",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "stop_after_successes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "stop_after_failures",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

const AI_SEARCH_BATCH_SCHEDULER_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional(
        "per_candidate_timeout_ms",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::optional(
        "batch_timeout_ms",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::optional(
        "max_memory_mb",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchBudget {
    pub wall_clock_ms: u64,
    pub max_nodes: u64,
    pub max_tactics_per_node: u32,
    pub max_depth: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchMvpControllerConfig {
    pub search_budget: AiSearchBudget,
    pub per_tactic_deterministic_budget: TacticBudget,
    pub scheduler_limits: Option<MachineBatchSchedulerLimits>,
    pub batch_policy: MachineTacticBatchPolicy,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchSnapshotGetRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchInitialSnapshot {
    pub snapshot: MachineProofSnapshot,
    pub goals: Vec<AiSearchGoalSummary>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchGoalSummary {
    pub goal_id: GoalId,
    pub open_goal_index: u32,
    pub goal_fingerprint: Hash,
    pub target_hash: Hash,
    pub target_head: Option<MachineGlobalRefView>,
    pub target_free_local_count: u32,
    pub context_size: u32,
    pub expr_size: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseQueryRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchRetrievalCacheKey {
    pub session_root_hash: Hash,
    pub query_fingerprint: Hash,
    pub theorem_index_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseUsage {
    pub premise_ref: AiSearchPremiseRef,
    pub universe_params: Vec<String>,
    pub statement_core_hash: Hash,
    pub axioms_used: Vec<MachineAxiomRefWire>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseCacheEntry {
    pub premise_ref: AiSearchPremiseRef,
    pub universe_params: Vec<String>,
    pub statement_core_hash: Hash,
    pub statement_head: Option<MachineGlobalRefView>,
    pub axioms_used: Vec<MachineAxiomRefWire>,
    pub modes: Vec<MachineTheoremMode>,
    pub response_index: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseRetrieval {
    pub cache_key: AiSearchRetrievalCacheKey,
    pub cache_entries: Vec<AiSearchPremiseCacheEntry>,
    pub results: Vec<MachineTheoremSearchResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchRepairPremiseRetrieval {
    pub query_fingerprint: Hash,
    pub query_profile_hash: Hash,
    pub theorem_index_fingerprint: Hash,
    pub retrieval_cache_key: MachineRetrievalCacheKey,
    pub premises: Vec<AiSearchRepairPremise>,
    pub premise_sets: Vec<AiSearchRepairPremiseSet>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchRepairPremise {
    pub premise_id: String,
    pub verified_identity: MachineVerifiedPremiseIdentity,
    pub selected_modes: Vec<MachineTheoremMode>,
    pub ranking_metadata: MachinePremiseRankingMetadata,
    pub candidate_provenance: MachinePremiseCandidateProvenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchRepairPremiseSet {
    pub source_premise_id: String,
    pub selected_premise_identities: Vec<MachineVerifiedPremiseIdentity>,
    pub axiom_impact: MachinePremiseSetAxiomImpact,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseGraphRanking {
    pub graph_snapshot_hash: Option<Hash>,
    pub fallback: AiSearchPremiseGraphRankingFallback,
    pub entries: Vec<AiSearchPremiseGraphRankingEntry>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchPremiseGraphRankingFallback {
    PrecomputedSnapshot,
    SnapshotMissing,
    SnapshotStaleIgnored,
    SnapshotInvalidIgnored,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseGraphRankingOptions {
    pub expected_graph_snapshot_hash: Option<Hash>,
    pub stale_policy: AiSearchPremiseGraphSnapshotStalePolicy,
}

impl Default for AiSearchPremiseGraphRankingOptions {
    fn default() -> Self {
        Self {
            expected_graph_snapshot_hash: None,
            stale_policy: AiSearchPremiseGraphSnapshotStalePolicy::EmptyContribution,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchPremiseGraphSnapshotStalePolicy {
    Reject,
    EmptyContribution,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchPremiseGraphRankingError {
    GraphSnapshotStale { expected: Hash, actual: Hash },
    GraphSnapshotInvalid,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchPremiseGraphRankingSource {
    VerifiedIndexMatch,
    GraphEdgeExpansion,
    VerifiedIndexAndGraphEdgeExpansion,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AiSearchPremiseGraphScoreComponents {
    pub direct_dependency_count: u32,
    pub transitive_dependency_count: u32,
    pub used_by_count: u32,
    pub similar_statement_count: u32,
    pub direct_axiom_path_count: u32,
    pub transitive_axiom_path_count: u32,
}

impl AiSearchPremiseGraphScoreComponents {
    fn score(&self) -> AiSearchScore {
        i64::from(self.direct_dependency_count) * 1_000
            + i64::from(self.similar_statement_count) * 750
            + i64::from(self.used_by_count) * 500
            + i64::from(self.transitive_dependency_count) * 250
            + i64::from(self.direct_axiom_path_count) * 125
            + i64::from(self.transitive_axiom_path_count) * 75
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AiSearchPremiseGraphEdgeMetadata {
    pub direct_dependencies: Vec<CertificateTheoremGraphNodeId>,
    pub transitive_dependencies: Vec<CertificateTheoremGraphNodeId>,
    pub used_by: Vec<CertificateTheoremGraphNodeId>,
    pub similar_statements: Vec<CertificateTheoremGraphNodeId>,
    pub direct_axiom_paths: Vec<CertificateTheoremGraphNodeId>,
    pub transitive_axiom_paths: Vec<CertificateTheoremGraphNodeId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPremiseGraphRankingEntry {
    pub premise_ref: AiSearchPremiseRef,
    pub response_index: u32,
    pub graph_rank: u32,
    pub graph_node: Option<CertificateTheoremGraphNodeId>,
    pub direct_dependency_count: u32,
    pub graph_source: AiSearchPremiseGraphRankingSource,
    pub graph_score_components: AiSearchPremiseGraphScoreComponents,
    pub graph_edges: AiSearchPremiseGraphEdgeMetadata,
    pub graph_score: AiSearchScore,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPositiveTrainingIdentity {
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate_hash: Hash,
    pub proof_delta_hash: Hash,
    pub next_state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchNegativeTrainingIdentity {
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate_hash: Hash,
    pub error_kind: FailedCandidateErrorKind,
    pub diagnostic_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchTrainingTraceRecord {
    pub trace_schema: String,
    pub session_root_hash: Hash,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub node_id: AiSearchNodeId,
    pub batch_index: u32,
    pub goal: AiSearchGoalSummary,
    pub retrieved_premises: Vec<AiSearchPremiseCacheEntry>,
    pub tactic_candidates: Vec<AiSearchTrainingTraceCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchTrainingTraceCandidate {
    Success {
        rank_index: u32,
        ai_search_candidate_payload_hash: Hash,
        candidate: MachineTacticCandidate,
        candidate_hash: Hash,
        deterministic_budget_hash: Hash,
        proof_delta_hash: Hash,
        next_snapshot_id: SnapshotId,
        next_state_fingerprint: Hash,
    },
    Error {
        rank_index: u32,
        ai_search_candidate_payload_hash: Hash,
        candidate: MachineTacticCandidate,
        candidate_hash: Hash,
        error_kind: FailedCandidateErrorKind,
        phase: crate::MachineApiDiagnosticPhase,
        deterministic_budget_hash: Hash,
        diagnostic_hash: Hash,
        retryable: bool,
        goal_id: Option<GoalId>,
        tactic_kind: Option<MachineApiTacticKind>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateEnvelope {
    pub candidate: MachineTacticCandidate,
    pub ai_search_candidate_payload_hash: Hash,
    pub candidate_hash: Option<Hash>,
    pub metadata: AiSearchCandidateMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateMetadata {
    pub source: AiSearchCandidateSource,
    pub rank: AiSearchCandidateRankMetadata,
    pub score: AiSearchScore,
    pub display_text: Option<String>,
    pub premises_used: Vec<AiSearchPremiseUsage>,
    pub expected_effect: AiSearchExpectedEffect,
    pub cost_estimate: AiSearchCandidateCostEstimate,
    pub trust_flags: AiSearchTrustFlags,
    pub repair: Option<AiSearchCandidateRepairMetadata>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchCandidateSource {
    MachineApiSuggested,
    Builtin,
    Model,
    Exploration,
    Repair,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateRankMetadata {
    pub cheap_first_stage: AiSearchCheapFirstStage,
    pub stage_rank: u8,
    pub skip_reason: Option<AiSearchCheapFirstSkipReason>,
    pub source_rank: u8,
    pub source_index: u32,
    pub builtin_kind_rank: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchBuiltinKind {
    Intro,
    LocalExact,
    InductionNat,
    SimpLiteEmpty,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AiSearchCheapFirstStage {
    LocalExact,
    KnownExact,
    ReflexivityComputation,
    FiniteDecide,
    Rewrite,
    SimpLite,
    RingOmega,
    Bitblast,
    Smt,
    Apply,
    Constructor,
    Cases,
    Induction,
    Solver,
    ExplicitTerm,
    LocalLemma,
    NewLibraryTheorem,
}

impl AiSearchCheapFirstStage {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LocalExact => "local_exact",
            Self::KnownExact => "known_exact",
            Self::ReflexivityComputation => "reflexivity_computation",
            Self::FiniteDecide => "finite_decide",
            Self::Rewrite => "rewrite",
            Self::SimpLite => "simp_lite",
            Self::RingOmega => "ring_omega",
            Self::Bitblast => "bitblast",
            Self::Smt => "smt",
            Self::Apply => "apply",
            Self::Constructor => "constructor",
            Self::Cases => "cases",
            Self::Induction => "induction",
            Self::Solver => "solver",
            Self::ExplicitTerm => "explicit_term",
            Self::LocalLemma => "local_lemma",
            Self::NewLibraryTheorem => "new_library_theorem",
        }
    }
}

pub const AI_SEARCH_CHEAP_FIRST_STAGE_ORDER: &[AiSearchCheapFirstStage] = &[
    AiSearchCheapFirstStage::LocalExact,
    AiSearchCheapFirstStage::KnownExact,
    AiSearchCheapFirstStage::ReflexivityComputation,
    AiSearchCheapFirstStage::FiniteDecide,
    AiSearchCheapFirstStage::Rewrite,
    AiSearchCheapFirstStage::SimpLite,
    AiSearchCheapFirstStage::RingOmega,
    AiSearchCheapFirstStage::Bitblast,
    AiSearchCheapFirstStage::Smt,
    AiSearchCheapFirstStage::Apply,
    AiSearchCheapFirstStage::Constructor,
    AiSearchCheapFirstStage::Cases,
    AiSearchCheapFirstStage::Induction,
    AiSearchCheapFirstStage::Solver,
    AiSearchCheapFirstStage::ExplicitTerm,
    AiSearchCheapFirstStage::LocalLemma,
    AiSearchCheapFirstStage::NewLibraryTheorem,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchCheapFirstSkipReason {
    ReservedUntypedSolverBucket,
    DeferredToLibraryGrowth,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchCheapFirstStageBudget {
    pub stage: AiSearchCheapFirstStage,
    pub max_candidate_count: u32,
    pub max_new_goals: u32,
    pub deterministic_budget: TacticBudget,
    pub batch_policy: Option<MachineTacticBatchPolicy>,
    pub skip_reason: Option<AiSearchCheapFirstSkipReason>,
}

pub fn ai_search_cheap_first_skip_reason(
    stage: AiSearchCheapFirstStage,
) -> Option<AiSearchCheapFirstSkipReason> {
    match stage {
        AiSearchCheapFirstStage::Solver => {
            Some(AiSearchCheapFirstSkipReason::ReservedUntypedSolverBucket)
        }
        AiSearchCheapFirstStage::NewLibraryTheorem => {
            Some(AiSearchCheapFirstSkipReason::DeferredToLibraryGrowth)
        }
        AiSearchCheapFirstStage::LocalExact
        | AiSearchCheapFirstStage::KnownExact
        | AiSearchCheapFirstStage::ReflexivityComputation
        | AiSearchCheapFirstStage::FiniteDecide
        | AiSearchCheapFirstStage::Rewrite
        | AiSearchCheapFirstStage::SimpLite
        | AiSearchCheapFirstStage::RingOmega
        | AiSearchCheapFirstStage::Bitblast
        | AiSearchCheapFirstStage::Smt
        | AiSearchCheapFirstStage::Apply
        | AiSearchCheapFirstStage::Constructor
        | AiSearchCheapFirstStage::Cases
        | AiSearchCheapFirstStage::Induction
        | AiSearchCheapFirstStage::ExplicitTerm
        | AiSearchCheapFirstStage::LocalLemma => None,
    }
}

pub fn ai_search_cheap_first_stage_budget(
    stage: AiSearchCheapFirstStage,
) -> AiSearchCheapFirstStageBudget {
    let (max_candidate_count, max_new_goals, deterministic_budget) = match stage {
        AiSearchCheapFirstStage::LocalExact => (
            8,
            0,
            TacticBudget {
                max_tactic_steps: 4,
                max_whnf_steps: 2_000,
                max_conversion_steps: 2_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 4_000,
            },
        ),
        AiSearchCheapFirstStage::KnownExact => (
            8,
            0,
            TacticBudget {
                max_tactic_steps: 6,
                max_whnf_steps: 4_000,
                max_conversion_steps: 4_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 8_000,
            },
        ),
        AiSearchCheapFirstStage::ReflexivityComputation => (
            4,
            2,
            TacticBudget {
                max_tactic_steps: 8,
                max_whnf_steps: 8_000,
                max_conversion_steps: 8_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 4,
                max_expr_nodes: 12_000,
            },
        ),
        AiSearchCheapFirstStage::FiniteDecide => (
            4,
            0,
            TacticBudget {
                max_tactic_steps: 12,
                max_whnf_steps: 8_000,
                max_conversion_steps: 8_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 16_000,
            },
        ),
        AiSearchCheapFirstStage::Rewrite => (
            8,
            1,
            TacticBudget {
                max_tactic_steps: 10,
                max_whnf_steps: 8_000,
                max_conversion_steps: 8_000,
                max_rewrite_steps: 64,
                max_meta_allocations: 4,
                max_expr_nodes: 16_000,
            },
        ),
        AiSearchCheapFirstStage::SimpLite => (
            4,
            1,
            TacticBudget {
                max_tactic_steps: 12,
                max_whnf_steps: 10_000,
                max_conversion_steps: 10_000,
                max_rewrite_steps: 128,
                max_meta_allocations: 4,
                max_expr_nodes: 18_000,
            },
        ),
        AiSearchCheapFirstStage::RingOmega => (
            4,
            0,
            TacticBudget {
                max_tactic_steps: 16,
                max_whnf_steps: 12_000,
                max_conversion_steps: 12_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 24_000,
            },
        ),
        AiSearchCheapFirstStage::Bitblast => (
            2,
            0,
            TacticBudget {
                max_tactic_steps: 16,
                max_whnf_steps: 16_000,
                max_conversion_steps: 16_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 32_000,
            },
        ),
        AiSearchCheapFirstStage::Smt => (
            2,
            0,
            TacticBudget {
                max_tactic_steps: 16,
                max_whnf_steps: 16_000,
                max_conversion_steps: 16_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 32_000,
            },
        ),
        AiSearchCheapFirstStage::Apply => (
            8,
            4,
            TacticBudget {
                max_tactic_steps: 16,
                max_whnf_steps: 10_000,
                max_conversion_steps: 10_000,
                max_rewrite_steps: 32,
                max_meta_allocations: 8,
                max_expr_nodes: 20_000,
            },
        ),
        AiSearchCheapFirstStage::Constructor => (
            4,
            4,
            TacticBudget {
                max_tactic_steps: 16,
                max_whnf_steps: 10_000,
                max_conversion_steps: 10_000,
                max_rewrite_steps: 16,
                max_meta_allocations: 8,
                max_expr_nodes: 20_000,
            },
        ),
        AiSearchCheapFirstStage::Cases => (
            4,
            8,
            TacticBudget {
                max_tactic_steps: 24,
                max_whnf_steps: 12_000,
                max_conversion_steps: 12_000,
                max_rewrite_steps: 64,
                max_meta_allocations: 16,
                max_expr_nodes: 24_000,
            },
        ),
        AiSearchCheapFirstStage::Induction => (
            4,
            8,
            TacticBudget {
                max_tactic_steps: 32,
                max_whnf_steps: 16_000,
                max_conversion_steps: 16_000,
                max_rewrite_steps: 128,
                max_meta_allocations: 24,
                max_expr_nodes: 32_000,
            },
        ),
        AiSearchCheapFirstStage::Solver => (
            0,
            0,
            TacticBudget {
                max_tactic_steps: 0,
                max_whnf_steps: 0,
                max_conversion_steps: 0,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 0,
            },
        ),
        AiSearchCheapFirstStage::ExplicitTerm => (
            4,
            0,
            TacticBudget {
                max_tactic_steps: 24,
                max_whnf_steps: 20_000,
                max_conversion_steps: 20_000,
                max_rewrite_steps: 0,
                max_meta_allocations: 16,
                max_expr_nodes: 50_000,
            },
        ),
        AiSearchCheapFirstStage::LocalLemma => (
            2,
            2,
            TacticBudget {
                max_tactic_steps: 32,
                max_whnf_steps: 20_000,
                max_conversion_steps: 20_000,
                max_rewrite_steps: 64,
                max_meta_allocations: 24,
                max_expr_nodes: 50_000,
            },
        ),
        AiSearchCheapFirstStage::NewLibraryTheorem => (
            0,
            0,
            TacticBudget {
                max_tactic_steps: 0,
                max_whnf_steps: 0,
                max_conversion_steps: 0,
                max_rewrite_steps: 0,
                max_meta_allocations: 0,
                max_expr_nodes: 0,
            },
        ),
    };
    let skip_reason = ai_search_cheap_first_skip_reason(stage);
    let batch_policy =
        (skip_reason.is_none() && max_candidate_count > 0).then_some(MachineTacticBatchPolicy {
            max_evaluated_candidates: max_candidate_count,
            stop_after_successes: 1,
            stop_after_failures: max_candidate_count,
        });
    AiSearchCheapFirstStageBudget {
        stage,
        max_candidate_count,
        max_new_goals,
        deterministic_budget,
        batch_policy,
        skip_reason,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchExpectedEffect {
    IntroBinder,
    CloseGoal,
    Rewrite,
    Simplify,
    InductionSplit,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateCostEstimate {
    pub estimated_timeout_ms: u32,
    pub risk: AiSearchCandidateCostRisk,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchCandidateCostRisk {
    Low,
    Medium,
    High,
}

pub type AiSearchScore = i64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchTrustFlags {
    pub uses_axioms: Vec<MachineAxiomRefWire>,
    pub contains_forbidden_tokens: bool,
    pub forbidden_token_class: Option<AiSearchForbiddenTokenClass>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateRepairMetadata {
    pub parent_candidate_hash: Hash,
    pub error_kind: FailedCandidateErrorKind,
    pub repair_depth: u32,
    pub chain_tried_payload_hashes: Vec<Hash>,
    pub premise_retrieval: Option<AiSearchRepairPremiseRetrieval>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchForbiddenToken {
    pub class: AiSearchForbiddenTokenClass,
    pub spelling: String,
    pub raw_term_index: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchForbiddenTokenClass {
    Sorry,
    Admit,
    Axiom,
    Unsafe,
    Import,
    SetOptionUnsafe,
    Declare,
    Eval,
    Shell,
    ExternalCommand,
    DisallowedTacticKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchCandidateFilterError {
    RawMachineTermLex {
        raw_term_index: u32,
        source: String,
        message: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchCandidateFilterResult {
    pub accepted: Vec<AiSearchCandidateEnvelope>,
    pub rejected: Vec<AiSearchRejectedCandidateEnvelope>,
    pub errors: Vec<AiSearchCandidateFilterError>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchRejectedCandidateEnvelope {
    pub envelope: AiSearchCandidateEnvelope,
    pub forbidden_token: AiSearchForbiddenToken,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchAssignedCandidate {
    pub candidate_id: String,
    pub rank_index: u32,
    pub envelope: AiSearchCandidateEnvelope,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchTacticBatchRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidates: Vec<AiSearchAssignedCandidate>,
    pub deterministic_budget: TacticBudget,
    pub batch_policy: MachineTacticBatchPolicy,
    pub scheduler_limits: Option<MachineBatchSchedulerLimits>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchReplayStep {
    pub previous_state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate: MachineTacticCandidate,
    pub deterministic_budget: TacticBudget,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
    pub proof_delta_hash: Hash,
    pub next_state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchReplayPlan {
    pub protocol_version: MachineApiVersion,
    pub session_root_hash: Hash,
    pub initial_state_fingerprint: Hash,
    pub steps: Vec<AiSearchReplayStep>,
    pub final_state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchFocusedReplayPayload {
    pub schema: &'static str,
    pub replay_plan: AiSearchReplayPlan,
    pub retrieval_provenance: Vec<AiSearchFocusedReplayPremiseProvenance>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchFocusedReplayPremiseProvenance {
    pub step_index: u32,
    pub query_fingerprint: Hash,
    pub theorem_index_fingerprint: Hash,
    pub premise_identities: Vec<MachineVerifiedPremiseIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchAcceptedCandidateFailure {
    pub error_kind: FailedCandidateErrorKind,
    pub phase: crate::MachineApiDiagnosticPhase,
    pub goal_id: Option<GoalId>,
    pub tactic_kind: Option<MachineApiTacticKind>,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
    pub diagnostic_hash: Hash,
    pub retryable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchNonAcceptedCandidateError {
    pub candidate_id: String,
    pub ai_search_candidate_payload_hash: Hash,
    pub error_kind: MachineApiErrorKind,
    pub phase: crate::MachineApiDiagnosticPhase,
    pub diagnostic_hash: Hash,
    pub has_candidate_hash: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchDeferredCandidate {
    pub candidate_id: String,
    pub envelope: AiSearchCandidateEnvelope,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchDeferredCandidateDropReason {
    SchedulerStoppedCandidate,
    MaxTacticsPerNode,
    WallClockBudgetExceeded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AiSearchSchedulerStop {
    pub status: MachineApiResponseStatus,
    pub completed_prefix_len: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchBatchEvaluation {
    pub successful_transitions: Vec<AiSearchSuccessfulCandidateTransition>,
    pub accepted_failure_records: Vec<AiSearchAcceptedCandidateFailureRecord>,
    pub replay_steps: Vec<AiSearchReplayStep>,
    pub accepted_failures: Vec<AiSearchAcceptedCandidateFailure>,
    pub non_accepted_errors: Vec<AiSearchNonAcceptedCandidateError>,
    pub training_trace_candidates: Vec<AiSearchTrainingTraceCandidate>,
    pub evaluated_count: u32,
    pub deferred_candidates: Vec<AiSearchDeferredCandidate>,
    pub scheduler_stop: Option<AiSearchSchedulerStop>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchBatchProgressAccounting {
    pub evaluated_candidates: u32,
    pub successful_candidates: u32,
    pub failed_candidates: u32,
    pub closed_goals: u32,
    pub new_goals: u32,
    pub replay_step_count: u32,
    pub proof_delta_hashes: Vec<Hash>,
    pub next_state_fingerprints: Vec<Hash>,
    pub unchanged_state_fingerprints: Vec<Hash>,
    pub failure_diagnostic_hashes: Vec<Hash>,
    pub scheduler_stop: Option<AiSearchSchedulerStop>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchProgressAccountingError {
    SuccessGoalCountMismatch {
        success_count: u32,
        supplied_count: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchSuccessfulCandidateTransition {
    pub candidate_id: String,
    pub envelope: AiSearchCandidateEnvelope,
    pub next_snapshot_id: SnapshotId,
    pub replay_step: AiSearchReplayStep,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchAcceptedCandidateFailureRecord {
    pub candidate_id: String,
    pub envelope: AiSearchCandidateEnvelope,
    pub failure: AiSearchAcceptedCandidateFailure,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchPendingCandidate {
    pub goal_id: GoalId,
    pub candidate: AiSearchCandidateEnvelope,
    pub repair_depth: u32,
    pub parent_candidate_hash: Hash,
    pub error_kind: FailedCandidateErrorKind,
    pub chain_tried_payload_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AiSearchRepairCandidateOutput {
    pub pending: Vec<AiSearchPendingCandidate>,
    pub repeated_candidate_payload_hashes: Vec<Hash>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AiSearchRuleBasedRepair;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchRuleBasedRepairAction {
    Noop,
    TrySimpLite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchRepairChainStopReason {
    RepeatedError,
    RepeatedCandidate,
    MaxRepairDepth,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchMachineControllerErrorKind {
    TopLevelBatchError,
    BatchResponseContractViolation,
    SuggestedCandidateHashMismatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchMachineControllerError {
    pub kind: AiSearchMachineControllerErrorKind,
    pub endpoint: AiSearchMachineApiEndpointKind,
    pub message: String,
    pub candidate_id: Option<String>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
    pub diagnostic_hash: Option<Hash>,
    pub phase: Option<crate::MachineApiDiagnosticPhase>,
    pub status: Option<MachineApiResponseStatus>,
}

pub type AiSearchMachineControllerResult<T> = Result<T, Box<AiSearchMachineControllerError>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchTacticBatchRunError {
    MachineApi(AiSearchMachineApiError),
    Controller(Box<AiSearchMachineControllerError>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchLocalAuthoringControllerError {
    pub endpoint: String,
    pub error_kind: String,
    pub error_phase: Option<String>,
    pub diagnostic_hash: Option<Hash>,
    pub status: Option<MachineApiResponseStatus>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AiSearchLocalAuthoringLoopOutput {
    pub snapshot: Option<MachineProofSnapshot>,
    pub selected_goal: Option<AiSearchGoalSummary>,
    pub retrieval: Option<AiSearchPremiseRetrieval>,
    pub generated_candidate_count: u32,
    pub executed_stages: Vec<AiSearchCheapFirstStage>,
    pub successful_stage: Option<AiSearchCheapFirstStage>,
    pub batch_evaluations: Vec<AiSearchBatchEvaluation>,
    pub successful_transition: Option<AiSearchSuccessfulCandidateTransition>,
    pub best_partial_replay_prefix: Option<Vec<AiSearchReplayStep>>,
    pub advisory_replay_plan: Option<AiSearchReplayPlan>,
    pub remaining_goals: Option<Vec<AiSearchGoalSummary>>,
    pub accepted_failures: Vec<AiSearchAcceptedCandidateFailureRecord>,
    pub non_accepted_errors: Vec<AiSearchNonAcceptedCandidateError>,
    pub controller_error: Option<AiSearchLocalAuthoringControllerError>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AiSearchNodeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchNodeStatus {
    Queued,
    Expanded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchNode {
    pub node_id: AiSearchNodeId,
    pub session_id: SessionId,
    pub session_root_hash: Hash,
    pub initial_state_fingerprint: Hash,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goals: Vec<AiSearchGoalSummary>,
    pub replay_steps: Vec<AiSearchReplayStep>,
    pub depth: u32,
    pub cumulative_score: AiSearchScore,
    pub last_candidate: Option<MachineTacticCandidate>,
    pub last_candidate_hash: Option<Hash>,
    pub used_premises: Vec<AiSearchPremiseUsage>,
    pub parent: Option<AiSearchNodeId>,
    pub status: AiSearchNodeStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchInput {
    pub session_id: SessionId,
    pub session_root_hash: Hash,
    pub initial_snapshot: MachineProofSnapshot,
    pub search_budget: AiSearchBudget,
    pub per_tactic_deterministic_budget: TacticBudget,
    pub scheduler_limits: Option<MachineBatchSchedulerLimits>,
    pub batch_policy: MachineTacticBatchPolicy,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AiSearchStats {
    pub nodes_expanded: u64,
    pub candidates_evaluated: u64,
    pub scheduler_stops: u64,
    pub zero_progress_scheduler_stops: u64,
    pub closed_node_replay_rejections: u64,
    pub closed_node_verify_rejections: u64,
    pub controller_errors: u64,
    pub no_candidate_stops: u64,
    pub max_depth_stops: u64,
    pub best_partial_updates: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchBudgetLimit {
    WallClock,
    MaxNodes,
    MaxDepth,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchFailureReason {
    QueueExhausted,
    SearchBudgetExceeded {
        limit: AiSearchBudgetLimit,
    },
    MachineControllerError {
        endpoint: String,
        error_kind: String,
        error_phase: Option<String>,
        diagnostic_hash: Option<Hash>,
    },
    NoCandidateForSelectedGoal {
        goal_id: GoalId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchFailure {
    pub reason: AiSearchFailureReason,
    pub best_partial_replay_prefix: Option<Vec<AiSearchReplayStep>>,
    pub best_snapshot_id: Option<SnapshotId>,
    pub best_state_fingerprint: Option<Hash>,
    pub remaining_goals: Option<Vec<AiSearchGoalSummary>>,
    pub search_stats: AiSearchStats,
    pub trace_events: Vec<AiSearchTraceEvent>,
    pub training_trace_records: Vec<AiSearchTrainingTraceRecord>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AiSearchMinimizationStats {
    pub pass_kinds_attempted: u64,
    pub rebuilt_plans: u64,
    pub replay_attempts: u64,
    pub verify_attempts: u64,
    pub accepted_proposals: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchMinimizationResult {
    pub replay_plan: AiSearchReplayPlan,
    pub replay_response: MachineReplayOkFields,
    pub verify_response: MachineApiOkResponse<MachineVerifyOkFields>,
    pub minimization_stats: AiSearchMinimizationStats,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchReplayStepEdit {
    pub original_goal_id: GoalId,
    pub original_open_goal_index: u32,
    pub candidate: MachineTacticCandidate,
    pub deterministic_budget: TacticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchVerifiedProof {
    pub replay_plan: AiSearchReplayPlan,
    pub final_snapshot_id: SnapshotId,
    pub final_state_fingerprint: Hash,
    pub verify_response: MachineApiOkResponse<MachineVerifyOkFields>,
    pub search_stats: AiSearchStats,
    pub minimization_stats: AiSearchMinimizationStats,
    pub trace_events: Vec<AiSearchTraceEvent>,
    pub training_trace_records: Vec<AiSearchTrainingTraceRecord>,
}

pub type AiSearchResult = Result<AiSearchVerifiedProof, Box<AiSearchFailure>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AiSearchTraceEvent {
    pub event_index: u64,
    pub node_id: AiSearchNodeId,
    pub kind: AiSearchTraceEventKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchTraceEventKind {
    NodeExpanded,
    DuplicateStateSkipped {
        duplicate_state_fingerprint: Hash,
    },
    ChildQueued {
        child_node_id: AiSearchNodeId,
        state_fingerprint: Hash,
    },
    NoCandidateForSelectedGoal {
        goal_id: GoalId,
    },
    MaxDepthStopped {
        max_depth: u32,
    },
    SchedulerStopped {
        status: MachineApiResponseStatus,
        completed_prefix_len: u32,
    },
    ZeroProgressSchedulerStopped {
        status: MachineApiResponseStatus,
    },
    NonAcceptedCandidateError {
        candidate_id: String,
        ai_search_candidate_payload_hash: Hash,
        error_kind: MachineApiErrorKind,
        phase: crate::MachineApiDiagnosticPhase,
        has_candidate_hash: bool,
        has_diagnostic_hash: bool,
    },
    DeferredCandidateDropped {
        candidate_id: String,
        ai_search_candidate_payload_hash: Hash,
        reason: AiSearchDeferredCandidateDropReason,
    },
    ForbiddenCandidateDiscarded {
        ai_search_candidate_payload_hash: Hash,
        forbidden_token_class: AiSearchForbiddenTokenClass,
    },
    MaxTacticsPerNodeStopped {
        max_tactics_per_node: u32,
    },
    MachineControllerError {
        endpoint: String,
        error_kind: String,
    },
    RepairChainStopped {
        parent_candidate_hash: Hash,
        error_kind: FailedCandidateErrorKind,
        repair_depth: u32,
        reason: AiSearchRepairChainStopReason,
        repeated_candidate_payload_hash: Option<Hash>,
    },
    ClosedNodeReplayRejected {
        endpoint: String,
        status: MachineApiResponseStatus,
    },
    ClosedNodeVerifyRejected {
        endpoint: String,
        status: MachineApiResponseStatus,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AiSearchPriorityKey {
    pub open_goal_count: u32,
    pub depth: u32,
    pub replay_step_count: u32,
    pub total_open_goal_target_size: u64,
    pub state_fingerprint: Hash,
    pub node_id: AiSearchNodeId,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AiSearchBestPartialKey {
    pub open_goal_count: u32,
    pub total_open_goal_target_size: u64,
    pub replay_step_count: u32,
    pub depth: u32,
    pub state_fingerprint: Hash,
    pub node_id: AiSearchNodeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AiSearchMachineApiEndpointKind {
    SnapshotGet,
    SearchForGoal,
    TacticBatch,
    Replay,
    Verify,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchMachineApiCall {
    SnapshotGet {
        session_id: SessionId,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
        include_pretty: bool,
    },
    SearchForGoal {
        source: String,
    },
    TacticBatch {
        source: String,
    },
    Replay {
        source: String,
    },
    Verify {
        source: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AiSearchMachineApiError {
    SnapshotGet(Box<MachineSnapshotGetError>),
    SearchForGoal(Box<MachineTheoremSearchError>),
    TacticBatch(Box<MachineTacticBatchError>),
    Replay(Box<MachineReplayError>),
    Verify(Box<MachineVerifyError>),
    SearchForGoalResponse(Box<MachineApiErrorWire>),
    UnexpectedSchedulerStop {
        endpoint: AiSearchMachineApiEndpointKind,
    },
    FakeRequestValidation {
        endpoint: AiSearchMachineApiEndpointKind,
        error: MachineApiRequestError,
    },
    FakeResponseExhausted {
        endpoint: AiSearchMachineApiEndpointKind,
    },
}

pub type AiSearchMachineApiResult<T> = Result<T, AiSearchMachineApiError>;

pub trait AiSearchMachineApiClient {
    fn get_snapshot(
        &mut self,
        request: AiSearchSnapshotGetRequest,
    ) -> AiSearchMachineApiResult<MachineSnapshotGetOk>;

    fn search_for_goal(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTheoremSearchResponse>;

    fn run_tactic_batch(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTacticBatchResponse>;

    fn replay(&mut self, source: &str) -> AiSearchMachineApiResult<MachineReplayResponse>;

    fn verify(&mut self, source: &str) -> AiSearchMachineApiResult<MachineVerifyResponse>;
}

pub struct AiSearchLocalMachineApiClient<'session> {
    session: &'session mut MachineProofSession,
}

impl<'session> AiSearchLocalMachineApiClient<'session> {
    pub fn new(session: &'session mut MachineProofSession) -> Self {
        Self { session }
    }
}

impl AiSearchMachineApiClient for AiSearchLocalMachineApiClient<'_> {
    fn get_snapshot(
        &mut self,
        request: AiSearchSnapshotGetRequest,
    ) -> AiSearchMachineApiResult<MachineSnapshotGetOk> {
        let source = ai_search_snapshot_get_request_json(&request);
        get_machine_snapshot(&source, std::iter::once(&*self.session))
            .map_err(AiSearchMachineApiError::SnapshotGet)
    }

    fn search_for_goal(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTheoremSearchResponse> {
        search_machine_theorems_for_goal(source, &*self.session)
            .map_err(AiSearchMachineApiError::SearchForGoal)
    }

    fn run_tactic_batch(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTacticBatchResponse> {
        run_machine_tactic_batch_request(source, self.session)
            .map_err(AiSearchMachineApiError::TacticBatch)
    }

    fn replay(&mut self, source: &str) -> AiSearchMachineApiResult<MachineReplayResponse> {
        run_machine_replay_request(source, self.session).map_err(AiSearchMachineApiError::Replay)
    }

    fn verify(&mut self, source: &str) -> AiSearchMachineApiResult<MachineVerifyResponse> {
        run_machine_verify_request(source, &*self.session).map_err(AiSearchMachineApiError::Verify)
    }
}

#[derive(Clone, Debug, Default)]
pub struct AiSearchFakeMachineApiClient {
    calls: Vec<AiSearchMachineApiCall>,
    snapshot_get_responses: VecDeque<AiSearchMachineApiResult<MachineSnapshotGetOk>>,
    search_for_goal_responses: VecDeque<AiSearchMachineApiResult<MachineTheoremSearchResponse>>,
    tactic_batch_responses: VecDeque<AiSearchMachineApiResult<MachineTacticBatchResponse>>,
    replay_responses: VecDeque<AiSearchMachineApiResult<MachineReplayResponse>>,
    verify_responses: VecDeque<AiSearchMachineApiResult<MachineVerifyResponse>>,
}

impl AiSearchFakeMachineApiClient {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn calls(&self) -> &[AiSearchMachineApiCall] {
        &self.calls
    }

    pub fn push_snapshot_get_response(
        &mut self,
        response: AiSearchMachineApiResult<MachineSnapshotGetOk>,
    ) {
        self.snapshot_get_responses.push_back(response);
    }

    pub fn push_search_for_goal_response(
        &mut self,
        response: AiSearchMachineApiResult<MachineTheoremSearchResponse>,
    ) {
        self.search_for_goal_responses.push_back(response);
    }

    pub fn push_tactic_batch_response(
        &mut self,
        response: AiSearchMachineApiResult<MachineTacticBatchResponse>,
    ) {
        self.tactic_batch_responses.push_back(response);
    }

    pub fn push_replay_response(
        &mut self,
        response: AiSearchMachineApiResult<MachineReplayResponse>,
    ) {
        self.replay_responses.push_back(response);
    }

    pub fn push_verify_response(
        &mut self,
        response: AiSearchMachineApiResult<MachineVerifyResponse>,
    ) {
        self.verify_responses.push_back(response);
    }
}

impl AiSearchMachineApiClient for AiSearchFakeMachineApiClient {
    fn get_snapshot(
        &mut self,
        request: AiSearchSnapshotGetRequest,
    ) -> AiSearchMachineApiResult<MachineSnapshotGetOk> {
        self.calls.push(AiSearchMachineApiCall::SnapshotGet {
            session_id: request.session_id,
            snapshot_id: request.snapshot_id,
            state_fingerprint: request.state_fingerprint,
            include_pretty: false,
        });
        self.snapshot_get_responses.pop_front().unwrap_or(Err(
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::SnapshotGet,
            },
        ))
    }

    fn search_for_goal(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTheoremSearchResponse> {
        parse_machine_theorem_search_request(source).map_err(|error| {
            AiSearchMachineApiError::FakeRequestValidation {
                endpoint: AiSearchMachineApiEndpointKind::SearchForGoal,
                error,
            }
        })?;
        self.calls.push(AiSearchMachineApiCall::SearchForGoal {
            source: source.to_owned(),
        });
        self.search_for_goal_responses.pop_front().unwrap_or(Err(
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::SearchForGoal,
            },
        ))
    }

    fn run_tactic_batch(
        &mut self,
        source: &str,
    ) -> AiSearchMachineApiResult<MachineTacticBatchResponse> {
        parse_machine_tactic_batch_request(source).map_err(|error| {
            AiSearchMachineApiError::FakeRequestValidation {
                endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
                error,
            }
        })?;
        self.calls.push(AiSearchMachineApiCall::TacticBatch {
            source: source.to_owned(),
        });
        self.tactic_batch_responses.pop_front().unwrap_or(Err(
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
            },
        ))
    }

    fn replay(&mut self, source: &str) -> AiSearchMachineApiResult<MachineReplayResponse> {
        parse_machine_replay_request(source).map_err(|error| {
            AiSearchMachineApiError::FakeRequestValidation {
                endpoint: AiSearchMachineApiEndpointKind::Replay,
                error,
            }
        })?;
        self.calls.push(AiSearchMachineApiCall::Replay {
            source: source.to_owned(),
        });
        self.replay_responses.pop_front().unwrap_or(Err(
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::Replay,
            },
        ))
    }

    fn verify(&mut self, source: &str) -> AiSearchMachineApiResult<MachineVerifyResponse> {
        parse_machine_verify_request(source).map_err(|error| {
            AiSearchMachineApiError::FakeRequestValidation {
                endpoint: AiSearchMachineApiEndpointKind::Verify,
                error,
            }
        })?;
        self.calls.push(AiSearchMachineApiCall::Verify {
            source: source.to_owned(),
        });
        self.verify_responses.pop_front().unwrap_or(Err(
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::Verify,
            },
        ))
    }
}

pub fn ai_search_assign_candidate_ids(
    candidates: Vec<AiSearchCandidateEnvelope>,
) -> Vec<AiSearchAssignedCandidate> {
    candidates
        .into_iter()
        .enumerate()
        .map(|(index, envelope)| AiSearchAssignedCandidate {
            candidate_id: format!("c{index}"),
            rank_index: usize_to_u32(index),
            envelope,
        })
        .collect()
}

pub fn ai_search_cap_batch_policy(
    policy: MachineTacticBatchPolicy,
    candidate_count: usize,
) -> MachineTacticBatchPolicy {
    let candidate_cap = usize_to_u32(candidate_count).max(1);
    MachineTacticBatchPolicy {
        max_evaluated_candidates: policy.max_evaluated_candidates.min(candidate_cap),
        stop_after_successes: policy.stop_after_successes.min(candidate_cap),
        stop_after_failures: policy.stop_after_failures.min(candidate_cap),
    }
}

pub fn ai_search_cheap_first_tactic_batch_request(
    session_id: SessionId,
    snapshot_id: SnapshotId,
    state_fingerprint: Hash,
    goal_id: GoalId,
    stage: AiSearchCheapFirstStage,
    candidates: Vec<AiSearchCandidateEnvelope>,
    scheduler_limits: Option<MachineBatchSchedulerLimits>,
) -> Option<AiSearchTacticBatchRequest> {
    let stage_budget = ai_search_cheap_first_stage_budget(stage);
    let batch_policy = stage_budget.batch_policy?;
    let staged_candidates = ai_search_rank_and_dedupe_candidate_envelopes(candidates)
        .into_iter()
        .filter(|candidate| candidate.metadata.rank.cheap_first_stage == stage)
        .filter(|candidate| {
            ai_search_candidate_within_stage_new_goal_budget(candidate, stage_budget)
        })
        .take(stage_budget.max_candidate_count as usize)
        .collect::<Vec<_>>();
    if staged_candidates.is_empty() {
        return None;
    }

    Some(AiSearchTacticBatchRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        candidates: ai_search_assign_candidate_ids(staged_candidates),
        deterministic_budget: stage_budget.deterministic_budget,
        batch_policy,
        scheduler_limits,
    })
}

pub fn ai_search_tactic_batch_request_json(request: &AiSearchTacticBatchRequest) -> String {
    let candidates = request
        .candidates
        .iter()
        .map(|candidate| {
            format!(
                r#"{{"candidate_id":{},"candidate":{}}}"#,
                json_string(&candidate.candidate_id),
                ai_search_candidate_payload_json(&candidate.envelope.candidate)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let capped_policy = ai_search_cap_batch_policy(request.batch_policy, request.candidates.len());
    let mut source = format!(
        r#"{{"session_id":"{}","snapshot_id":"{}","state_fingerprint":"{}","goal_id":"{}","candidates":[{}],"deterministic_budget":{},"batch_policy":{}"#,
        request.session_id.wire(),
        request.snapshot_id.wire(),
        format_hash_string(&request.state_fingerprint),
        format_goal_id_wire(request.goal_id),
        candidates,
        ai_search_tactic_budget_json(request.deterministic_budget),
        ai_search_batch_policy_json(capped_policy)
    );
    if let Some(scheduler_limits) = request.scheduler_limits {
        source.push_str(r#","scheduler_limits":"#);
        source.push_str(&ai_search_scheduler_limits_json(scheduler_limits));
    }
    source.push('}');
    source
}

pub fn ai_search_run_tactic_batch(
    client: &mut impl AiSearchMachineApiClient,
    request: &AiSearchTacticBatchRequest,
) -> Result<AiSearchBatchEvaluation, AiSearchTacticBatchRunError> {
    let source = ai_search_tactic_batch_request_json(request);
    let response = client
        .run_tactic_batch(&source)
        .map_err(AiSearchTacticBatchRunError::MachineApi)?;
    ai_search_evaluate_tactic_batch_response(request, response)
        .map_err(AiSearchTacticBatchRunError::Controller)
}

pub fn ai_search_positive_training_identity(
    state_fingerprint: Hash,
    goal_id: GoalId,
    candidate_hash: Hash,
    proof_delta_hash: Hash,
    next_state_fingerprint: Hash,
) -> AiSearchPositiveTrainingIdentity {
    AiSearchPositiveTrainingIdentity {
        state_fingerprint,
        goal_id,
        candidate_hash,
        proof_delta_hash,
        next_state_fingerprint,
    }
}

pub fn ai_search_negative_training_identity(
    state_fingerprint: Hash,
    goal_id: GoalId,
    failure: &AiSearchAcceptedCandidateFailure,
) -> AiSearchNegativeTrainingIdentity {
    AiSearchNegativeTrainingIdentity {
        state_fingerprint,
        goal_id,
        candidate_hash: failure.candidate_hash,
        error_kind: failure.error_kind,
        diagnostic_hash: failure.diagnostic_hash,
    }
}

pub fn ai_search_positive_training_identity_hash(
    identity: &AiSearchPositiveTrainingIdentity,
) -> Hash {
    let payload = ai_search_positive_training_identity_json(identity);
    let mut bytes = Vec::new();
    bytes.extend_from_slice(AI_SEARCH_POSITIVE_TRAINING_IDENTITY_HASH_TAG.as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(payload.as_bytes());
    sha256(&bytes)
}

pub fn ai_search_negative_training_identity_hash(
    identity: &AiSearchNegativeTrainingIdentity,
) -> Hash {
    let payload = ai_search_negative_training_identity_json(identity);
    let mut bytes = Vec::new();
    bytes.extend_from_slice(AI_SEARCH_NEGATIVE_TRAINING_IDENTITY_HASH_TAG.as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(payload.as_bytes());
    sha256(&bytes)
}

pub fn ai_search_candidate_hash_mismatch(
    envelope: &AiSearchCandidateEnvelope,
    response_candidate_hash: Option<Hash>,
) -> bool {
    envelope
        .candidate_hash
        .is_some_and(|expected| response_candidate_hash != Some(expected))
}

pub fn ai_search_evaluate_tactic_batch_response(
    request: &AiSearchTacticBatchRequest,
    response: MachineTacticBatchResponse,
) -> AiSearchMachineControllerResult<AiSearchBatchEvaluation> {
    match response {
        MachineApiResponseEnvelope::Ok(ok) => {
            if ok.status != MachineApiResponseStatus::Ok {
                return Err(ai_search_batch_contract_violation(
                    format!("batch ok envelope used status {}", ok.status.as_str()),
                    Some(ok.status),
                ));
            }
            let fields = ok.endpoint_fields;
            ai_search_validate_ok_batch_fields(request, &fields)?;
            Ok(ai_search_build_batch_evaluation(
                request,
                &fields.results,
                fields.deterministic_budget_hash,
                None,
                fields.results.len(),
            ))
        }
        MachineApiResponseEnvelope::SchedulerStopped(stop) => {
            if !matches!(
                stop.status,
                MachineApiResponseStatus::PartialTimeout
                    | MachineApiResponseStatus::PartialResourceLimit
            ) {
                return Err(ai_search_batch_contract_violation(
                    format!(
                        "batch scheduler envelope used status {}",
                        stop.status.as_str()
                    ),
                    Some(stop.status),
                ));
            }
            let fields = stop.endpoint_fields;
            ai_search_validate_scheduler_batch_fields(request, &fields, stop.status)?;
            let completed_prefix_len = fields.completed_prefix_len;
            let deferred_start = if fields.results.is_empty() {
                request.candidates.len()
            } else {
                (fields.results.len() + 1).min(request.candidates.len())
            };
            Ok(ai_search_build_batch_evaluation(
                request,
                &fields.results,
                fields.deterministic_budget_hash,
                Some(AiSearchSchedulerStop {
                    status: stop.status,
                    completed_prefix_len,
                }),
                deferred_start,
            ))
        }
        MachineApiResponseEnvelope::Error(error) => Err(Box::new(AiSearchMachineControllerError {
            kind: AiSearchMachineControllerErrorKind::TopLevelBatchError,
            endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
            message: error.error.kind.as_str().to_owned(),
            candidate_id: None,
            expected_hash: None,
            actual_hash: None,
            diagnostic_hash: Some(error.error.diagnostic_hash),
            phase: Some(error.error.phase),
            status: Some(error.status),
        })),
    }
}

pub fn ai_search_replay_step_json(step: &AiSearchReplayStep) -> String {
    format!(
        r#"{{"previous_state_fingerprint":{},"goal_id":{},"candidate":{},"deterministic_budget":{},"candidate_hash":{},"deterministic_budget_hash":{},"proof_delta_hash":{},"next_state_fingerprint":{}}}"#,
        json_string(&format_hash_string(&step.previous_state_fingerprint)),
        json_string(&format_goal_id_wire(step.goal_id)),
        ai_search_candidate_payload_json(&step.candidate),
        ai_search_tactic_budget_json(step.deterministic_budget),
        json_string(&format_hash_string(&step.candidate_hash)),
        json_string(&format_hash_string(&step.deterministic_budget_hash)),
        json_string(&format_hash_string(&step.proof_delta_hash)),
        json_string(&format_hash_string(&step.next_state_fingerprint)),
    )
}

pub fn ai_search_build_replay_plan(node: &AiSearchNode) -> AiSearchReplayPlan {
    AiSearchReplayPlan {
        protocol_version: MachineApiVersion::V1,
        session_root_hash: node.session_root_hash,
        initial_state_fingerprint: node.initial_state_fingerprint,
        steps: node.replay_steps.clone(),
        final_state_fingerprint: node.state_fingerprint,
    }
}

pub fn ai_search_replay_plan_json(plan: &AiSearchReplayPlan) -> String {
    let steps = plan
        .steps
        .iter()
        .map(ai_search_replay_step_json)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"protocol_version":{},"session_root_hash":{},"initial_state_fingerprint":{},"steps":[{}],"final_state_fingerprint":{}}}"#,
        json_string(plan.protocol_version.as_str()),
        json_string(&format_hash_string(&plan.session_root_hash)),
        json_string(&format_hash_string(&plan.initial_state_fingerprint)),
        steps,
        json_string(&format_hash_string(&plan.final_state_fingerprint)),
    )
}

pub fn ai_search_replay_request_json(session_id: SessionId, plan: &AiSearchReplayPlan) -> String {
    format!(
        r#"{{"session_id":"{}","plan":{}}}"#,
        session_id.wire(),
        ai_search_replay_plan_json(plan)
    )
}

pub fn ai_search_verify_request_json(
    session_id: SessionId,
    snapshot_id: SnapshotId,
    state_fingerprint: Hash,
) -> String {
    format!(
        r#"{{"session_id":"{}","snapshot_id":"{}","state_fingerprint":"{}","mode":"certificate"}}"#,
        session_id.wire(),
        snapshot_id.wire(),
        format_hash_string(&state_fingerprint),
    )
}

pub fn ai_search_training_trace_records_json(records: &[AiSearchTrainingTraceRecord]) -> String {
    let members = records
        .iter()
        .map(ai_search_training_trace_record_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

pub fn ai_search_training_trace_record_json(record: &AiSearchTrainingTraceRecord) -> String {
    format!(
        r#"{{"trace_schema":{},"session_root_hash":{},"snapshot_id":{},"state_fingerprint":{},"node_id":{},"batch_index":{},"goal":{},"retrieved_premises":{},"tactic_candidates":{}}}"#,
        json_string(&record.trace_schema),
        json_string(&format_hash_string(&record.session_root_hash)),
        json_string(&record.snapshot_id.wire()),
        json_string(&format_hash_string(&record.state_fingerprint)),
        record.node_id.0,
        record.batch_index,
        ai_search_goal_summary_json(&record.goal),
        ai_search_premise_cache_entries_json(&record.retrieved_premises),
        ai_search_training_trace_candidates_json(&record.tactic_candidates),
    )
}

pub fn ai_search_positive_training_identity_json(
    identity: &AiSearchPositiveTrainingIdentity,
) -> String {
    format!(
        r#"{{"state_fingerprint":{},"goal_id":{},"candidate_hash":{},"proof_delta_hash":{},"next_state_fingerprint":{}}}"#,
        json_string(&format_hash_string(&identity.state_fingerprint)),
        json_string(&format_goal_id_wire(identity.goal_id)),
        json_string(&format_hash_string(&identity.candidate_hash)),
        json_string(&format_hash_string(&identity.proof_delta_hash)),
        json_string(&format_hash_string(&identity.next_state_fingerprint)),
    )
}

pub fn ai_search_negative_training_identity_json(
    identity: &AiSearchNegativeTrainingIdentity,
) -> String {
    format!(
        r#"{{"state_fingerprint":{},"goal_id":{},"candidate_hash":{},"error_kind":{},"diagnostic_hash":{}}}"#,
        json_string(&format_hash_string(&identity.state_fingerprint)),
        json_string(&format_goal_id_wire(identity.goal_id)),
        json_string(&format_hash_string(&identity.candidate_hash)),
        json_string(identity.error_kind.as_str()),
        json_string(&format_hash_string(&identity.diagnostic_hash)),
    )
}

pub fn ai_search_minimize_replay_plan(
    client: &mut impl AiSearchMachineApiClient,
    session_id: SessionId,
    initial_snapshot: &MachineProofSnapshot,
    verified_replay_plan: AiSearchReplayPlan,
    verified_replay: MachineReplayOkFields,
    verified_response: MachineApiOkResponse<MachineVerifyOkFields>,
) -> AiSearchMinimizationResult {
    let mut current_plan = verified_replay_plan;
    let mut current_replay = verified_replay;
    let mut current_verify = verified_response;
    let mut minimization_stats = AiSearchMinimizationStats::default();

    for pass in AiSearchMinimizationPassKind::ALL {
        minimization_stats.pass_kinds_attempted += 1;
        let mut changed = true;

        while changed {
            changed = false;
            let Some(step_edits) = ai_search_make_step_edits_with_goal_indices(
                client,
                session_id.clone(),
                initial_snapshot,
                &current_plan,
            ) else {
                break;
            };

            for proposed_steps in ai_search_minimization_proposals(pass, &step_edits) {
                let Some(rebuilt) = ai_search_rebuild_replay_plan_from_step_edits(
                    client,
                    session_id.clone(),
                    initial_snapshot,
                    &current_plan,
                    &proposed_steps,
                ) else {
                    continue;
                };
                minimization_stats.rebuilt_plans += 1;

                minimization_stats.replay_attempts += 1;
                let replay_source = ai_search_replay_request_json(session_id.clone(), &rebuilt);
                let Ok(MachineApiResponseEnvelope::Ok(replayed)) = client.replay(&replay_source)
                else {
                    continue;
                };
                if replayed.status != MachineApiResponseStatus::Ok {
                    continue;
                }

                minimization_stats.verify_attempts += 1;
                let verify_source = ai_search_verify_request_json(
                    session_id.clone(),
                    replayed.endpoint_fields.final_snapshot_id,
                    replayed.endpoint_fields.final_state_fingerprint,
                );
                let Ok(MachineApiResponseEnvelope::Ok(verified)) = client.verify(&verify_source)
                else {
                    continue;
                };
                if verified.status != MachineApiResponseStatus::Verified {
                    continue;
                }

                current_plan = rebuilt;
                current_replay = replayed.endpoint_fields;
                current_verify = verified;
                minimization_stats.accepted_proposals += 1;
                changed = true;
                break;
            }
        }
    }

    AiSearchMinimizationResult {
        replay_plan: current_plan,
        replay_response: current_replay,
        verify_response: current_verify,
        minimization_stats,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AiSearchMinimizationPassKind {
    DeleteRedundantSteps,
    ReplaceBlocksWithSimpLiteEmpty,
    MinimizeExistingSimpLiteRules,
}

impl AiSearchMinimizationPassKind {
    const ALL: [Self; 3] = [
        Self::DeleteRedundantSteps,
        Self::ReplaceBlocksWithSimpLiteEmpty,
        Self::MinimizeExistingSimpLiteRules,
    ];
}

fn ai_search_minimization_proposals(
    pass: AiSearchMinimizationPassKind,
    step_edits: &[AiSearchReplayStepEdit],
) -> Vec<Vec<AiSearchReplayStepEdit>> {
    match pass {
        AiSearchMinimizationPassKind::DeleteRedundantSteps => {
            ai_search_delete_redundant_steps_proposals(step_edits)
        }
        AiSearchMinimizationPassKind::ReplaceBlocksWithSimpLiteEmpty => {
            ai_search_replace_blocks_with_simp_lite_empty_proposals(step_edits)
        }
        AiSearchMinimizationPassKind::MinimizeExistingSimpLiteRules => {
            ai_search_minimize_existing_simp_lite_rules_proposals(step_edits)
        }
    }
}

fn ai_search_delete_redundant_steps_proposals(
    step_edits: &[AiSearchReplayStepEdit],
) -> Vec<Vec<AiSearchReplayStepEdit>> {
    let mut proposals = Vec::new();
    for index in 0..step_edits.len() {
        let mut proposal = step_edits.to_vec();
        proposal.remove(index);
        if proposal != step_edits {
            proposals.push(proposal);
        }
    }
    proposals
}

fn ai_search_replace_blocks_with_simp_lite_empty_proposals(
    step_edits: &[AiSearchReplayStepEdit],
) -> Vec<Vec<AiSearchReplayStepEdit>> {
    let mut proposals = Vec::new();
    for block_len in (1..=step_edits.len()).rev() {
        for start_index in 0..=step_edits.len() - block_len {
            let replacement_source = &step_edits[start_index];
            let mut proposal = Vec::new();
            proposal.extend_from_slice(&step_edits[..start_index]);
            proposal.push(AiSearchReplayStepEdit {
                original_goal_id: replacement_source.original_goal_id,
                original_open_goal_index: replacement_source.original_open_goal_index,
                candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
                deterministic_budget: replacement_source.deterministic_budget,
            });
            proposal.extend_from_slice(&step_edits[start_index + block_len..]);
            if proposal != step_edits {
                proposals.push(proposal);
            }
        }
    }
    proposals
}

fn ai_search_minimize_existing_simp_lite_rules_proposals(
    step_edits: &[AiSearchReplayStepEdit],
) -> Vec<Vec<AiSearchReplayStepEdit>> {
    let mut proposals = Vec::new();
    for step_index in 0..step_edits.len() {
        let MachineTacticCandidate::SimpLite { rules } = &step_edits[step_index].candidate else {
            continue;
        };
        for rule_index in 0..rules.len() {
            let mut reduced_rules = rules.clone();
            reduced_rules.remove(rule_index);
            let mut proposal = step_edits.to_vec();
            proposal[step_index].candidate = MachineTacticCandidate::SimpLite {
                rules: reduced_rules,
            };
            if proposal != step_edits {
                proposals.push(proposal);
            }
        }
    }
    proposals
}

fn ai_search_make_step_edits_with_goal_indices(
    client: &mut impl AiSearchMachineApiClient,
    session_id: SessionId,
    initial_snapshot: &MachineProofSnapshot,
    current_plan: &AiSearchReplayPlan,
) -> Option<Vec<AiSearchReplayStepEdit>> {
    let mut snapshot = ai_search_minimization_initial_snapshot(
        client,
        session_id.clone(),
        initial_snapshot,
        current_plan,
    )?;
    let mut edits = Vec::new();

    for step in &current_plan.steps {
        let open_goal_index = snapshot
            .open_goals
            .iter()
            .position(|goal_id| *goal_id == step.goal_id)?;
        edits.push(AiSearchReplayStepEdit {
            original_goal_id: step.goal_id,
            original_open_goal_index: usize_to_u32(open_goal_index),
            candidate: step.candidate.clone(),
            deterministic_budget: step.deterministic_budget,
        });

        let (replayed_step, next_snapshot) = ai_search_minimization_reexecute_step(
            client,
            session_id.clone(),
            &snapshot,
            step.goal_id,
            step.candidate.clone(),
            step.deterministic_budget,
        )?;
        if replayed_step.candidate_hash != step.candidate_hash
            || replayed_step.deterministic_budget_hash != step.deterministic_budget_hash
            || replayed_step.proof_delta_hash != step.proof_delta_hash
            || replayed_step.next_state_fingerprint != step.next_state_fingerprint
        {
            return None;
        }
        snapshot = next_snapshot;
    }

    Some(edits)
}

fn ai_search_rebuild_replay_plan_from_step_edits(
    client: &mut impl AiSearchMachineApiClient,
    session_id: SessionId,
    initial_snapshot: &MachineProofSnapshot,
    current_plan: &AiSearchReplayPlan,
    proposed_steps: &[AiSearchReplayStepEdit],
) -> Option<AiSearchReplayPlan> {
    let mut snapshot = ai_search_minimization_initial_snapshot(
        client,
        session_id.clone(),
        initial_snapshot,
        current_plan,
    )?;
    let mut replay_steps = Vec::new();

    for edit in proposed_steps {
        let execution_goal_id = ai_search_minimization_execution_goal_id(&snapshot, edit)?;
        let (step, next_snapshot) = ai_search_minimization_reexecute_step(
            client,
            session_id.clone(),
            &snapshot,
            execution_goal_id,
            edit.candidate.clone(),
            edit.deterministic_budget,
        )?;
        replay_steps.push(step);
        snapshot = next_snapshot;
    }

    Some(AiSearchReplayPlan {
        protocol_version: current_plan.protocol_version,
        session_root_hash: current_plan.session_root_hash,
        initial_state_fingerprint: current_plan.initial_state_fingerprint,
        steps: replay_steps,
        final_state_fingerprint: snapshot.state_fingerprint,
    })
}

fn ai_search_minimization_initial_snapshot(
    client: &mut impl AiSearchMachineApiClient,
    session_id: SessionId,
    initial_snapshot: &MachineProofSnapshot,
    current_plan: &AiSearchReplayPlan,
) -> Option<MachineProofSnapshot> {
    if initial_snapshot.state_fingerprint != current_plan.initial_state_fingerprint {
        return None;
    }
    client
        .get_snapshot(AiSearchSnapshotGetRequest {
            session_id,
            snapshot_id: initial_snapshot.snapshot_id,
            state_fingerprint: current_plan.initial_state_fingerprint,
        })
        .ok()
        .map(|ok| ok.snapshot)
}

fn ai_search_minimization_execution_goal_id(
    snapshot: &MachineProofSnapshot,
    edit: &AiSearchReplayStepEdit,
) -> Option<GoalId> {
    if snapshot.open_goals.contains(&edit.original_goal_id) {
        return Some(edit.original_goal_id);
    }
    snapshot
        .open_goals
        .get(edit.original_open_goal_index as usize)
        .copied()
}

fn ai_search_minimization_reexecute_step(
    client: &mut impl AiSearchMachineApiClient,
    session_id: SessionId,
    snapshot: &MachineProofSnapshot,
    goal_id: GoalId,
    candidate: MachineTacticCandidate,
    deterministic_budget: TacticBudget,
) -> Option<(AiSearchReplayStep, MachineProofSnapshot)> {
    let request = AiSearchTacticBatchRequest {
        session_id: session_id.clone(),
        snapshot_id: snapshot.snapshot_id,
        state_fingerprint: snapshot.state_fingerprint,
        goal_id,
        candidates: vec![AiSearchAssignedCandidate {
            candidate_id: "c0".to_owned(),
            rank_index: 0,
            envelope: ai_search_minimization_candidate_envelope(candidate),
        }],
        deterministic_budget,
        batch_policy: MachineTacticBatchPolicy {
            max_evaluated_candidates: 1,
            stop_after_successes: 1,
            stop_after_failures: 1,
        },
        scheduler_limits: None,
    };
    let evaluation = ai_search_run_tactic_batch(client, &request).ok()?;
    if evaluation.scheduler_stop.is_some()
        || evaluation.evaluated_count != 1
        || !evaluation.accepted_failure_records.is_empty()
        || !evaluation.non_accepted_errors.is_empty()
    {
        return None;
    }
    let transition = evaluation.successful_transitions.into_iter().next()?;
    let next_snapshot = client
        .get_snapshot(AiSearchSnapshotGetRequest {
            session_id,
            snapshot_id: transition.next_snapshot_id,
            state_fingerprint: transition.replay_step.next_state_fingerprint,
        })
        .ok()?
        .snapshot;
    Some((transition.replay_step, next_snapshot))
}

fn ai_search_minimization_candidate_envelope(
    candidate: MachineTacticCandidate,
) -> AiSearchCandidateEnvelope {
    let metadata = ai_search_candidate_metadata(
        AiSearchCandidateSource::Builtin,
        None,
        0,
        Vec::new(),
        Vec::new(),
        &candidate,
    );
    ai_search_candidate_envelope(candidate, None, metadata)
}

fn ai_search_validate_ok_batch_fields(
    request: &AiSearchTacticBatchRequest,
    fields: &MachineTacticBatchOkFields,
) -> AiSearchMachineControllerResult<()> {
    ai_search_validate_batch_common_fields(
        request,
        fields.previous_state_fingerprint,
        fields.deterministic_budget_hash,
        &fields.results,
        fields.success_count,
        fields.failure_count,
    )
}

fn ai_search_validate_scheduler_batch_fields(
    request: &AiSearchTacticBatchRequest,
    fields: &MachineTacticBatchSchedulerFields,
    status: MachineApiResponseStatus,
) -> AiSearchMachineControllerResult<()> {
    ai_search_validate_batch_common_fields(
        request,
        fields.previous_state_fingerprint,
        fields.deterministic_budget_hash,
        &fields.results,
        fields.success_count,
        fields.failure_count,
    )?;
    if fields.completed_prefix_len as usize != fields.results.len() {
        return Err(ai_search_batch_contract_violation(
            format!(
                "completed_prefix_len {} did not match result prefix length {}",
                fields.completed_prefix_len,
                fields.results.len()
            ),
            Some(status),
        ));
    }
    if fields.results.len() == request.candidates.len() {
        return Err(ai_search_batch_contract_violation(
            "scheduler partial response completed every candidate".to_owned(),
            Some(status),
        ));
    }
    Ok(())
}

fn ai_search_validate_batch_common_fields(
    request: &AiSearchTacticBatchRequest,
    previous_state_fingerprint: Hash,
    deterministic_budget_hash: Hash,
    results: &[MachineTacticBatchItemResponse],
    success_count: u32,
    failure_count: u32,
) -> AiSearchMachineControllerResult<()> {
    if previous_state_fingerprint != request.state_fingerprint {
        return Err(Box::new(AiSearchMachineControllerError {
            kind: AiSearchMachineControllerErrorKind::BatchResponseContractViolation,
            endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
            message: "batch previous_state_fingerprint did not match request".to_owned(),
            candidate_id: None,
            expected_hash: Some(request.state_fingerprint),
            actual_hash: Some(previous_state_fingerprint),
            diagnostic_hash: None,
            phase: None,
            status: None,
        }));
    }

    let expected_budget_hash = tactic_budget_hash(request.deterministic_budget);
    if deterministic_budget_hash != expected_budget_hash {
        return Err(Box::new(AiSearchMachineControllerError {
            kind: AiSearchMachineControllerErrorKind::BatchResponseContractViolation,
            endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
            message: "batch deterministic_budget_hash did not match request budget".to_owned(),
            candidate_id: None,
            expected_hash: Some(expected_budget_hash),
            actual_hash: Some(deterministic_budget_hash),
            diagnostic_hash: None,
            phase: None,
            status: None,
        }));
    }

    if results.len() > request.candidates.len() {
        return Err(ai_search_batch_contract_violation(
            format!(
                "batch returned {} results for {} candidates",
                results.len(),
                request.candidates.len()
            ),
            None,
        ));
    }

    let mut seen_ids = BTreeSet::new();
    let mut actual_success_count = 0u32;
    let mut actual_failure_count = 0u32;
    for (index, item) in results.iter().enumerate() {
        let expected_id = &request.candidates[index].candidate_id;
        let actual_id = ai_search_batch_item_candidate_id(item);
        if actual_id != expected_id {
            return Err(Box::new(AiSearchMachineControllerError {
                kind: AiSearchMachineControllerErrorKind::BatchResponseContractViolation,
                endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
                message: format!(
                    "batch result at index {index} used candidate_id {actual_id}, expected {expected_id}"
                ),
                candidate_id: Some(actual_id.to_owned()),
                expected_hash: None,
                actual_hash: None,
                diagnostic_hash: None,
                phase: None,
                status: None,
            }));
        }
        if !seen_ids.insert(actual_id) {
            return Err(ai_search_batch_contract_violation(
                format!("batch repeated candidate_id {actual_id}"),
                None,
            ));
        }
        if item.is_success() {
            actual_success_count += 1;
        } else {
            actual_failure_count += 1;
        }
    }

    if success_count != actual_success_count || failure_count != actual_failure_count {
        return Err(ai_search_batch_contract_violation(
            format!(
                "batch count fields reported {success_count} successes and {failure_count} failures, observed {actual_success_count} successes and {actual_failure_count} failures"
            ),
            None,
        ));
    }

    ai_search_validate_candidate_hashes(request, results)
}

fn ai_search_validate_candidate_hashes(
    request: &AiSearchTacticBatchRequest,
    results: &[MachineTacticBatchItemResponse],
) -> AiSearchMachineControllerResult<()> {
    for (index, item) in results.iter().enumerate() {
        let assigned = &request.candidates[index];
        let actual_hash = ai_search_batch_item_candidate_hash(item);
        if ai_search_candidate_hash_mismatch(&assigned.envelope, actual_hash) {
            return Err(Box::new(AiSearchMachineControllerError {
                kind: AiSearchMachineControllerErrorKind::SuggestedCandidateHashMismatch,
                endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
                message: "batch candidate_hash did not match suggested candidate envelope"
                    .to_owned(),
                candidate_id: Some(assigned.candidate_id.clone()),
                expected_hash: assigned.envelope.candidate_hash,
                actual_hash,
                diagnostic_hash: None,
                phase: None,
                status: None,
            }));
        }
    }
    Ok(())
}

fn ai_search_build_batch_evaluation(
    request: &AiSearchTacticBatchRequest,
    results: &[MachineTacticBatchItemResponse],
    deterministic_budget_hash: Hash,
    scheduler_stop: Option<AiSearchSchedulerStop>,
    deferred_start: usize,
) -> AiSearchBatchEvaluation {
    let mut successful_transitions = Vec::new();
    let mut accepted_failure_records = Vec::new();
    let mut replay_steps = Vec::new();
    let mut accepted_failures = Vec::new();
    let mut non_accepted_errors = Vec::new();
    let mut training_trace_candidates = Vec::new();

    for (index, item) in results.iter().enumerate() {
        let assigned = &request.candidates[index];
        match item {
            MachineTacticBatchItemResponse::Success {
                candidate_id,
                candidate_hash,
                next_snapshot_id,
                next_state_fingerprint,
                proof_delta_hash,
            } => {
                let replay_step = AiSearchReplayStep {
                    previous_state_fingerprint: request.state_fingerprint,
                    goal_id: request.goal_id,
                    candidate: assigned.envelope.candidate.clone(),
                    deterministic_budget: request.deterministic_budget,
                    candidate_hash: *candidate_hash,
                    deterministic_budget_hash,
                    proof_delta_hash: *proof_delta_hash,
                    next_state_fingerprint: *next_state_fingerprint,
                };
                replay_steps.push(replay_step.clone());
                successful_transitions.push(AiSearchSuccessfulCandidateTransition {
                    candidate_id: candidate_id.clone(),
                    envelope: assigned.envelope.clone(),
                    next_snapshot_id: *next_snapshot_id,
                    replay_step,
                });
                training_trace_candidates.push(AiSearchTrainingTraceCandidate::Success {
                    rank_index: assigned.rank_index,
                    ai_search_candidate_payload_hash: assigned
                        .envelope
                        .ai_search_candidate_payload_hash,
                    candidate: assigned.envelope.candidate.clone(),
                    candidate_hash: *candidate_hash,
                    deterministic_budget_hash,
                    proof_delta_hash: *proof_delta_hash,
                    next_snapshot_id: *next_snapshot_id,
                    next_state_fingerprint: *next_state_fingerprint,
                });
            }
            MachineTacticBatchItemResponse::Error {
                candidate_hash,
                diagnostic,
                ..
            } => {
                if let Some(failure) = ai_search_normalize_accepted_candidate_failure(
                    diagnostic,
                    *candidate_hash,
                    deterministic_budget_hash,
                ) {
                    accepted_failure_records.push(AiSearchAcceptedCandidateFailureRecord {
                        candidate_id: assigned.candidate_id.clone(),
                        envelope: assigned.envelope.clone(),
                        failure: failure.clone(),
                    });
                    training_trace_candidates.push(AiSearchTrainingTraceCandidate::Error {
                        rank_index: assigned.rank_index,
                        ai_search_candidate_payload_hash: assigned
                            .envelope
                            .ai_search_candidate_payload_hash,
                        candidate: assigned.envelope.candidate.clone(),
                        candidate_hash: failure.candidate_hash,
                        error_kind: failure.error_kind,
                        phase: failure.phase,
                        deterministic_budget_hash,
                        diagnostic_hash: failure.diagnostic_hash,
                        retryable: failure.retryable,
                        goal_id: failure.goal_id,
                        tactic_kind: failure.tactic_kind,
                    });
                    accepted_failures.push(failure);
                } else {
                    non_accepted_errors.push(AiSearchNonAcceptedCandidateError {
                        candidate_id: assigned.candidate_id.clone(),
                        ai_search_candidate_payload_hash: assigned
                            .envelope
                            .ai_search_candidate_payload_hash,
                        error_kind: diagnostic.error_kind,
                        phase: diagnostic.phase,
                        diagnostic_hash: diagnostic.diagnostic_hash,
                        has_candidate_hash: candidate_hash.is_some(),
                    });
                }
            }
        }
    }

    AiSearchBatchEvaluation {
        successful_transitions,
        accepted_failure_records,
        replay_steps,
        accepted_failures,
        non_accepted_errors,
        training_trace_candidates,
        evaluated_count: usize_to_u32(results.len()),
        deferred_candidates: ai_search_deferred_candidates(request, deferred_start),
        scheduler_stop,
    }
}

pub fn ai_search_batch_progress_accounting(
    evaluation: &AiSearchBatchEvaluation,
    open_goal_count_before: u32,
    open_goal_counts_after_successes: &[u32],
) -> Result<AiSearchBatchProgressAccounting, AiSearchProgressAccountingError> {
    let successful_candidates = usize_to_u32(evaluation.successful_transitions.len());
    let supplied_count = usize_to_u32(open_goal_counts_after_successes.len());
    if supplied_count != successful_candidates {
        return Err(AiSearchProgressAccountingError::SuccessGoalCountMismatch {
            success_count: successful_candidates,
            supplied_count,
        });
    }

    let base_open_goals_after_closing_selected = open_goal_count_before.saturating_sub(1);
    let new_goals = open_goal_counts_after_successes
        .iter()
        .map(|after| after.saturating_sub(base_open_goals_after_closing_selected))
        .sum();
    let proof_delta_hashes = evaluation
        .successful_transitions
        .iter()
        .map(|transition| transition.replay_step.proof_delta_hash)
        .collect::<Vec<_>>();
    let next_state_fingerprints = evaluation
        .successful_transitions
        .iter()
        .map(|transition| transition.replay_step.next_state_fingerprint)
        .collect::<Vec<_>>();
    let unchanged_state_fingerprints = evaluation
        .successful_transitions
        .iter()
        .filter_map(|transition| {
            (transition.replay_step.previous_state_fingerprint
                == transition.replay_step.next_state_fingerprint)
                .then_some(transition.replay_step.next_state_fingerprint)
        })
        .collect::<Vec<_>>();
    let mut failure_diagnostic_hashes = evaluation
        .accepted_failures
        .iter()
        .map(|failure| failure.diagnostic_hash)
        .collect::<Vec<_>>();
    failure_diagnostic_hashes.extend(
        evaluation
            .non_accepted_errors
            .iter()
            .map(|error| error.diagnostic_hash),
    );

    Ok(AiSearchBatchProgressAccounting {
        evaluated_candidates: evaluation.evaluated_count,
        successful_candidates,
        failed_candidates: evaluation
            .evaluated_count
            .saturating_sub(successful_candidates),
        closed_goals: successful_candidates,
        new_goals,
        replay_step_count: usize_to_u32(evaluation.replay_steps.len()),
        proof_delta_hashes,
        next_state_fingerprints,
        unchanged_state_fingerprints,
        failure_diagnostic_hashes,
        scheduler_stop: evaluation.scheduler_stop,
    })
}

fn ai_search_normalize_accepted_candidate_failure(
    diagnostic: &MachineApiCompactErrorWire,
    candidate_hash: Option<Hash>,
    deterministic_budget_hash: Hash,
) -> Option<AiSearchAcceptedCandidateFailure> {
    Some(AiSearchAcceptedCandidateFailure {
        error_kind: ai_search_failed_candidate_error_kind(diagnostic.error_kind)?,
        phase: diagnostic.phase,
        goal_id: diagnostic.goal_id,
        tactic_kind: diagnostic.tactic_kind,
        candidate_hash: candidate_hash?,
        deterministic_budget_hash,
        diagnostic_hash: diagnostic.diagnostic_hash,
        retryable: diagnostic.retryable,
    })
}

fn ai_search_failed_candidate_error_kind(
    kind: MachineApiErrorKind,
) -> Option<FailedCandidateErrorKind> {
    match kind {
        MachineApiErrorKind::UnsupportedTactic => Some(FailedCandidateErrorKind::UnsupportedTactic),
        MachineApiErrorKind::MachineTermElaborationError => {
            Some(FailedCandidateErrorKind::MachineTermElaborationError)
        }
        MachineApiErrorKind::UnknownName => Some(FailedCandidateErrorKind::UnknownName),
        MachineApiErrorKind::ImplicitArgumentRequired => {
            Some(FailedCandidateErrorKind::ImplicitArgumentRequired)
        }
        MachineApiErrorKind::TypeMismatch => Some(FailedCandidateErrorKind::TypeMismatch),
        MachineApiErrorKind::ExpectedPiType => Some(FailedCandidateErrorKind::ExpectedPiType),
        MachineApiErrorKind::RewriteRuleInvalid => {
            Some(FailedCandidateErrorKind::RewriteRuleInvalid)
        }
        MachineApiErrorKind::SimpNoProgress => Some(FailedCandidateErrorKind::SimpNoProgress),
        MachineApiErrorKind::InductionTargetNotNat => {
            Some(FailedCandidateErrorKind::InductionTargetNotNat)
        }
        MachineApiErrorKind::BudgetExceeded => Some(FailedCandidateErrorKind::BudgetExceeded),
        MachineApiErrorKind::TooManyGoals => Some(FailedCandidateErrorKind::TooManyGoals),
        MachineApiErrorKind::TooLargeTerm => Some(FailedCandidateErrorKind::TooLargeTerm),
        _ => None,
    }
}

fn ai_search_batch_item_candidate_id(item: &MachineTacticBatchItemResponse) -> &str {
    match item {
        MachineTacticBatchItemResponse::Success { candidate_id, .. }
        | MachineTacticBatchItemResponse::Error { candidate_id, .. } => candidate_id,
    }
}

fn ai_search_batch_item_candidate_hash(item: &MachineTacticBatchItemResponse) -> Option<Hash> {
    match item {
        MachineTacticBatchItemResponse::Success { candidate_hash, .. } => Some(*candidate_hash),
        MachineTacticBatchItemResponse::Error { candidate_hash, .. } => *candidate_hash,
    }
}

fn ai_search_deferred_candidates(
    request: &AiSearchTacticBatchRequest,
    start: usize,
) -> Vec<AiSearchDeferredCandidate> {
    request
        .candidates
        .iter()
        .skip(start)
        .map(|assigned| AiSearchDeferredCandidate {
            candidate_id: assigned.candidate_id.clone(),
            envelope: assigned.envelope.clone(),
        })
        .collect()
}

fn ai_search_batch_contract_violation(
    message: String,
    status: Option<MachineApiResponseStatus>,
) -> Box<AiSearchMachineControllerError> {
    Box::new(AiSearchMachineControllerError {
        kind: AiSearchMachineControllerErrorKind::BatchResponseContractViolation,
        endpoint: AiSearchMachineApiEndpointKind::TacticBatch,
        message,
        candidate_id: None,
        expected_hash: None,
        actual_hash: None,
        diagnostic_hash: None,
        phase: None,
        status,
    })
}

fn ai_search_tactic_budget_json(budget: TacticBudget) -> String {
    format!(
        r#"{{"max_tactic_steps":{},"max_whnf_steps":{},"max_conversion_steps":{},"max_rewrite_steps":{},"max_meta_allocations":{},"max_expr_nodes":{}}}"#,
        budget.max_tactic_steps,
        budget.max_whnf_steps,
        budget.max_conversion_steps,
        budget.max_rewrite_steps,
        budget.max_meta_allocations,
        budget.max_expr_nodes,
    )
}

fn ai_search_batch_policy_json(policy: MachineTacticBatchPolicy) -> String {
    format!(
        r#"{{"max_evaluated_candidates":{},"stop_after_successes":{},"stop_after_failures":{}}}"#,
        policy.max_evaluated_candidates, policy.stop_after_successes, policy.stop_after_failures,
    )
}

fn ai_search_scheduler_limits_json(limits: MachineBatchSchedulerLimits) -> String {
    let mut fields = Vec::new();
    if let Some(value) = limits.per_candidate_timeout_ms {
        fields.push(format!(r#""per_candidate_timeout_ms":{value}"#));
    }
    if let Some(value) = limits.batch_timeout_ms {
        fields.push(format!(r#""batch_timeout_ms":{value}"#));
    }
    if let Some(value) = limits.max_memory_mb {
        fields.push(format!(r#""max_memory_mb":{value}"#));
    }
    format!("{{{}}}", fields.join(","))
}

impl AiSearchRuleBasedRepair {
    pub fn new() -> Self {
        Self
    }

    pub fn repair_candidate(
        self,
        goal: &MachineGoalView,
        failed_envelope: &AiSearchCandidateEnvelope,
        failure: &AiSearchAcceptedCandidateFailure,
        repair_depth: u32,
    ) -> AiSearchRepairCandidateOutput {
        if repair_depth > 2 {
            return AiSearchRepairCandidateOutput::default();
        }

        match ai_search_rule_based_repair_action(failure.error_kind) {
            AiSearchRuleBasedRepairAction::Noop => AiSearchRepairCandidateOutput::default(),
            AiSearchRuleBasedRepairAction::TrySimpLite => {
                ai_search_simp_lite_repair_candidate(goal, failed_envelope, failure, repair_depth)
            }
        }
    }

    pub fn repair_candidate_with_premise_retrieval(
        self,
        goal: &MachineGoalView,
        failed_envelope: &AiSearchCandidateEnvelope,
        failure: &AiSearchAcceptedCandidateFailure,
        repair_depth: u32,
        retrieval: Option<&AiSearchRepairPremiseRetrieval>,
    ) -> AiSearchRepairCandidateOutput {
        let mut output = self.repair_candidate(goal, failed_envelope, failure, repair_depth);
        if let Some(retrieval) = retrieval {
            for pending in &mut output.pending {
                if let Some(repair) = &mut pending.candidate.metadata.repair {
                    repair.premise_retrieval = Some(retrieval.clone());
                }
            }
        }
        output
    }
}

pub fn ai_search_rule_based_repair_action(
    kind: FailedCandidateErrorKind,
) -> AiSearchRuleBasedRepairAction {
    match kind {
        FailedCandidateErrorKind::UnsupportedTactic
        | FailedCandidateErrorKind::MachineTermElaborationError
        | FailedCandidateErrorKind::UnknownName
        | FailedCandidateErrorKind::ImplicitArgumentRequired
        | FailedCandidateErrorKind::InductionTargetNotNat
        | FailedCandidateErrorKind::BudgetExceeded
        | FailedCandidateErrorKind::TooLargeTerm => AiSearchRuleBasedRepairAction::Noop,
        FailedCandidateErrorKind::TypeMismatch
        | FailedCandidateErrorKind::ExpectedPiType
        | FailedCandidateErrorKind::RewriteRuleInvalid
        | FailedCandidateErrorKind::SimpNoProgress
        | FailedCandidateErrorKind::TooManyGoals => AiSearchRuleBasedRepairAction::TrySimpLite,
    }
}

pub fn ai_search_repair_should_request_premise_retrieval(kind: FailedCandidateErrorKind) -> bool {
    matches!(
        kind,
        FailedCandidateErrorKind::TypeMismatch
            | FailedCandidateErrorKind::ExpectedPiType
            | FailedCandidateErrorKind::RewriteRuleInvalid
            | FailedCandidateErrorKind::SimpNoProgress
            | FailedCandidateErrorKind::InductionTargetNotNat
            | FailedCandidateErrorKind::TooManyGoals
    )
}

pub fn ai_search_repair_depth_of(envelope: &AiSearchCandidateEnvelope) -> u32 {
    envelope
        .metadata
        .repair
        .as_ref()
        .map_or(0, |repair| repair.repair_depth)
}

fn ai_search_simp_lite_repair_candidate(
    goal: &MachineGoalView,
    failed_envelope: &AiSearchCandidateEnvelope,
    failure: &AiSearchAcceptedCandidateFailure,
    repair_depth: u32,
) -> AiSearchRepairCandidateOutput {
    if !ai_search_goal_allows_tactic(goal, MachineApiTacticKind::SimpLite) {
        return AiSearchRepairCandidateOutput::default();
    }

    let chain_tried_payload_hashes = ai_search_repair_chain_tried_payload_hashes(failed_envelope);
    let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
    let mut metadata = ai_search_candidate_metadata(
        AiSearchCandidateSource::Repair,
        None,
        0,
        Vec::new(),
        Vec::new(),
        &candidate,
    );
    metadata.display_text = Some("simp-lite".to_owned());
    metadata.repair = Some(AiSearchCandidateRepairMetadata {
        parent_candidate_hash: failure.candidate_hash,
        error_kind: failure.error_kind,
        repair_depth,
        chain_tried_payload_hashes: chain_tried_payload_hashes.clone(),
        premise_retrieval: None,
    });
    let envelope = ai_search_candidate_envelope(candidate, None, metadata);

    if chain_tried_payload_hashes.contains(&envelope.ai_search_candidate_payload_hash) {
        return AiSearchRepairCandidateOutput {
            pending: Vec::new(),
            repeated_candidate_payload_hashes: vec![envelope.ai_search_candidate_payload_hash],
        };
    }

    AiSearchRepairCandidateOutput {
        pending: vec![AiSearchPendingCandidate {
            goal_id: goal.goal_id,
            repair_depth,
            parent_candidate_hash: failure.candidate_hash,
            error_kind: failure.error_kind,
            chain_tried_payload_hashes,
            candidate: envelope,
        }],
        repeated_candidate_payload_hashes: Vec::new(),
    }
}

fn ai_search_repair_chain_tried_payload_hashes(envelope: &AiSearchCandidateEnvelope) -> Vec<Hash> {
    let mut chain = envelope
        .metadata
        .repair
        .as_ref()
        .map_or_else(Vec::new, |repair| repair.chain_tried_payload_hashes.clone());
    chain.push(envelope.ai_search_candidate_payload_hash);
    chain
}

fn ai_search_repeated_repair_error(
    envelope: &AiSearchCandidateEnvelope,
    failure: &AiSearchAcceptedCandidateFailure,
) -> bool {
    envelope
        .metadata
        .repair
        .as_ref()
        .is_some_and(|repair| repair.error_kind == failure.error_kind)
}

fn ai_search_limit_repairs(
    pending_repairs: Vec<AiSearchPendingCandidate>,
) -> Vec<AiSearchPendingCandidate> {
    let mut seen_payloads = BTreeSet::new();
    let mut per_parent_counts: BTreeMap<(GoalId, Hash, FailedCandidateErrorKind), u32> =
        BTreeMap::new();
    let mut out = Vec::new();

    for pending in pending_repairs {
        if !seen_payloads.insert(pending.candidate.ai_search_candidate_payload_hash) {
            continue;
        }

        let key = (
            pending.goal_id,
            pending.parent_candidate_hash,
            pending.error_kind,
        );
        let count = per_parent_counts.entry(key).or_insert(0);
        if *count >= 3 {
            continue;
        }
        *count += 1;
        out.push(pending);
    }

    out
}

fn ai_search_merge_node_candidates(
    deferred_candidates: &mut Vec<AiSearchDeferredCandidate>,
    pending_repairs: &mut Vec<AiSearchPendingCandidate>,
    fresh_candidates: &mut Vec<AiSearchCandidateEnvelope>,
) -> Vec<AiSearchCandidateEnvelope> {
    let mut candidates = Vec::new();
    candidates.extend(
        deferred_candidates
            .drain(..)
            .map(|deferred| deferred.envelope),
    );

    let mut repairs = ai_search_limit_repairs(std::mem::take(pending_repairs));
    repairs.sort_by(ai_search_pending_candidate_order);
    candidates.extend(repairs.into_iter().map(|pending| pending.candidate));

    candidates.extend(std::mem::take(fresh_candidates));
    ai_search_dedupe_candidate_envelopes(candidates)
}

fn ai_search_pending_candidate_order(
    left: &AiSearchPendingCandidate,
    right: &AiSearchPendingCandidate,
) -> Ordering {
    left.repair_depth
        .cmp(&right.repair_depth)
        .then_with(|| left.parent_candidate_hash.cmp(&right.parent_candidate_hash))
        .then_with(|| left.error_kind.as_str().cmp(right.error_kind.as_str()))
        .then_with(|| {
            left.candidate
                .ai_search_candidate_payload_hash
                .cmp(&right.candidate.ai_search_candidate_payload_hash)
        })
}

pub fn ai_search_node_priority_key(node: &AiSearchNode) -> AiSearchPriorityKey {
    AiSearchPriorityKey {
        open_goal_count: usize_to_u32(node.goals.len()),
        depth: node.depth,
        replay_step_count: usize_to_u32(node.replay_steps.len()),
        total_open_goal_target_size: ai_search_total_open_goal_target_size(&node.goals),
        state_fingerprint: node.state_fingerprint,
        node_id: node.node_id,
    }
}

pub fn ai_search_node_best_partial_key(node: &AiSearchNode) -> AiSearchBestPartialKey {
    AiSearchBestPartialKey {
        open_goal_count: usize_to_u32(node.goals.len()),
        total_open_goal_target_size: ai_search_total_open_goal_target_size(&node.goals),
        replay_step_count: usize_to_u32(node.replay_steps.len()),
        depth: node.depth,
        state_fingerprint: node.state_fingerprint,
        node_id: node.node_id,
    }
}

pub fn ai_search_run_mvp_search(
    client: &mut impl AiSearchMachineApiClient,
    input: AiSearchInput,
) -> AiSearchResult {
    let mut node_ids = AiSearchNodeIdAllocator::new();
    let mut queue = AiSearchPriorityQueue::new();
    let mut discovered_states = BTreeSet::new();
    let mut stats = AiSearchStats::default();
    let mut trace = AiSearchTraceBuilder::new();
    let mut training_trace_records = Vec::new();
    let mut best_partial: Option<AiSearchNode> = None;
    let mut failure_reason = AiSearchFailureReason::QueueExhausted;
    let mut depth_budget_hit = false;
    let mut initial_no_candidate_goal = None;

    let root = ai_search_root_search_node(&input, node_ids.allocate());
    discovered_states.insert(root.state_fingerprint);
    queue.push(root);

    while let Some(mut node) = queue.pop_best() {
        node.status = AiSearchNodeStatus::Expanded;
        trace.push(&node, AiSearchTraceEventKind::NodeExpanded);

        let snapshot = match client.get_snapshot(AiSearchSnapshotGetRequest {
            session_id: node.session_id.clone(),
            snapshot_id: node.snapshot_id,
            state_fingerprint: node.state_fingerprint,
        }) {
            Ok(ok) => ok.snapshot,
            Err(error) => {
                stats.controller_errors += 1;
                let reason = ai_search_failure_reason_from_machine_api_error(
                    AiSearchMachineApiEndpointKind::SnapshotGet,
                    &error,
                );
                trace.push(
                    &node,
                    ai_search_machine_controller_trace_kind_from_reason(&reason),
                );
                return Err(ai_search_failure(
                    reason,
                    best_partial,
                    stats,
                    trace.finish(),
                    training_trace_records,
                ));
            }
        };
        node.goals = ai_search_goal_summaries(&snapshot);

        if node.goals.is_empty() {
            match ai_search_attempt_closed_node(client, &node, &mut stats, &mut trace) {
                AiSearchClosedNodeOutcome::Verified(verified) => {
                    let minimization = ai_search_minimize_replay_plan(
                        client,
                        node.session_id.clone(),
                        &input.initial_snapshot,
                        verified.replay_plan,
                        verified.replay_response,
                        verified.verify_response,
                    );
                    return Ok(AiSearchVerifiedProof {
                        replay_plan: minimization.replay_plan,
                        final_snapshot_id: minimization.replay_response.final_snapshot_id,
                        final_state_fingerprint: minimization
                            .replay_response
                            .final_state_fingerprint,
                        verify_response: minimization.verify_response,
                        search_stats: stats,
                        minimization_stats: minimization.minimization_stats,
                        trace_events: trace.finish(),
                        training_trace_records,
                    });
                }
                AiSearchClosedNodeOutcome::Rejected => continue,
                AiSearchClosedNodeOutcome::ControllerError { reason } => {
                    return Err(ai_search_failure(
                        reason,
                        best_partial,
                        stats,
                        trace.finish(),
                        training_trace_records,
                    ));
                }
            }
        }

        if best_partial.as_ref().is_none_or(|best| {
            ai_search_node_best_partial_key(&node) < ai_search_node_best_partial_key(best)
        }) {
            best_partial = Some(node.clone());
            stats.best_partial_updates += 1;
        }

        if node.depth >= input.search_budget.max_depth {
            depth_budget_hit = true;
            stats.max_depth_stops += 1;
            trace.push(
                &node,
                AiSearchTraceEventKind::MaxDepthStopped {
                    max_depth: input.search_budget.max_depth,
                },
            );
            continue;
        }

        if stats.nodes_expanded >= input.search_budget.max_nodes {
            failure_reason = AiSearchFailureReason::SearchBudgetExceeded {
                limit: AiSearchBudgetLimit::MaxNodes,
            };
            break;
        }
        stats.nodes_expanded += 1;

        let Some(goal_summary) = select_ai_search_goal(&snapshot) else {
            stats.no_candidate_stops += 1;
            continue;
        };
        let goal_id = goal_summary.goal_id;
        let Some(goal) = snapshot.goals.iter().find(|goal| goal.goal_id == goal_id) else {
            stats.controller_errors += 1;
            let reason = AiSearchFailureReason::MachineControllerError {
                endpoint: ai_search_machine_api_endpoint_wire(
                    AiSearchMachineApiEndpointKind::SnapshotGet,
                )
                .to_owned(),
                error_kind: "invalid_machine_proof_state".to_owned(),
                error_phase: None,
                diagnostic_hash: None,
            };
            trace.push(
                &node,
                ai_search_machine_controller_trace_kind_from_reason(&reason),
            );
            return Err(ai_search_failure(
                reason,
                best_partial,
                stats,
                trace.finish(),
                training_trace_records,
            ));
        };

        let retrieval = match retrieve_ai_search_premises(
            client,
            &AiSearchPremiseQueryRequest {
                session_id: node.session_id.clone(),
                snapshot_id: node.snapshot_id,
                state_fingerprint: node.state_fingerprint,
                goal_id,
            },
            node.session_root_hash,
        ) {
            Ok(retrieval) => retrieval,
            Err(error) => {
                stats.controller_errors += 1;
                let reason = ai_search_failure_reason_from_machine_api_error(
                    AiSearchMachineApiEndpointKind::SearchForGoal,
                    &error,
                );
                trace.push(
                    &node,
                    ai_search_machine_controller_trace_kind_from_reason(&reason),
                );
                return Err(ai_search_failure(
                    reason,
                    best_partial,
                    stats,
                    trace.finish(),
                    training_trace_records,
                ));
            }
        };

        let candidate_generation = ai_search_mvp_candidate_generation(goal, &retrieval);
        ai_search_record_forbidden_candidate_discards(
            &mut trace,
            &node,
            &candidate_generation.rejected,
        );
        let mut fresh_candidates = candidate_generation.accepted;
        let mut deferred_candidates = Vec::new();
        let mut pending_repairs = Vec::new();
        let mut evaluated_for_node = 0u32;
        let mut training_batch_index = 0u32;
        let repair = AiSearchRuleBasedRepair::new();

        loop {
            let mut candidates = ai_search_merge_node_candidates(
                &mut deferred_candidates,
                &mut pending_repairs,
                &mut fresh_candidates,
            );
            let remaining_tactic_budget = input
                .search_budget
                .max_tactics_per_node
                .saturating_sub(evaluated_for_node);
            let max_tactics_budget_reached_before_batch =
                remaining_tactic_budget == 0 && !candidates.is_empty();
            let candidates_exceeded_remaining_tactic_budget =
                candidates.len() > remaining_tactic_budget as usize;
            candidates =
                ai_search_take_remaining_node_tactic_budget(candidates, remaining_tactic_budget);

            if candidates.is_empty() {
                if max_tactics_budget_reached_before_batch {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::MaxTacticsPerNodeStopped {
                            max_tactics_per_node: input.search_budget.max_tactics_per_node,
                        },
                    );
                } else if evaluated_for_node == 0 {
                    stats.no_candidate_stops += 1;
                    if node.parent.is_none() {
                        initial_no_candidate_goal = Some(goal_id);
                    }
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::NoCandidateForSelectedGoal { goal_id },
                    );
                }
                break;
            }

            let batch_request = AiSearchTacticBatchRequest {
                session_id: node.session_id.clone(),
                snapshot_id: node.snapshot_id,
                state_fingerprint: node.state_fingerprint,
                goal_id,
                candidates: ai_search_assign_candidate_ids(candidates),
                deterministic_budget: input.per_tactic_deterministic_budget,
                batch_policy: input.batch_policy,
                scheduler_limits: input.scheduler_limits,
            };
            let evaluation = match ai_search_run_tactic_batch(client, &batch_request) {
                Ok(evaluation) => evaluation,
                Err(error) => {
                    stats.controller_errors += 1;
                    let reason = ai_search_failure_reason_from_tactic_batch_run_error(&error);
                    trace.push(
                        &node,
                        ai_search_machine_controller_trace_kind_from_reason(&reason),
                    );
                    return Err(ai_search_failure(
                        reason,
                        best_partial,
                        stats,
                        trace.finish(),
                        training_trace_records,
                    ));
                }
            };

            if let Some(scheduler_stop) = evaluation.scheduler_stop {
                stats.scheduler_stops += 1;
                if evaluation.evaluated_count == 0 {
                    stats.zero_progress_scheduler_stops += 1;
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::ZeroProgressSchedulerStopped {
                            status: scheduler_stop.status,
                        },
                    );
                } else {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::SchedulerStopped {
                            status: scheduler_stop.status,
                            completed_prefix_len: scheduler_stop.completed_prefix_len,
                        },
                    );
                }
                ai_search_record_scheduler_dropped_candidates(
                    &mut trace,
                    &node,
                    &batch_request,
                    &evaluation,
                );
            }

            if evaluation.evaluated_count == 0
                && evaluation.scheduler_stop.is_none()
                && !evaluation.deferred_candidates.is_empty()
            {
                stats.controller_errors += 1;
                let error = ai_search_batch_contract_violation(
                    "batch ok response did not evaluate any candidate".to_owned(),
                    None,
                );
                let reason = ai_search_failure_reason_from_controller_error(&error);
                trace.push(
                    &node,
                    ai_search_machine_controller_trace_kind_from_reason(&reason),
                );
                return Err(ai_search_failure(
                    reason,
                    best_partial,
                    stats,
                    trace.finish(),
                    training_trace_records,
                ));
            }

            ai_search_record_training_trace_batch(
                &mut training_trace_records,
                &node,
                &mut training_batch_index,
                &goal_summary,
                &retrieval.cache_entries,
                &evaluation,
            );
            ai_search_record_non_accepted_candidate_errors(
                &mut trace,
                &node,
                &evaluation.non_accepted_errors,
            );

            evaluated_for_node = evaluated_for_node
                .checked_add(evaluation.evaluated_count)
                .expect("ai_search evaluated candidates for node fits in u32");
            stats.candidates_evaluated += u64::from(evaluation.evaluated_count);

            for transition in evaluation.successful_transitions {
                if discovered_states.contains(&transition.replay_step.next_state_fingerprint) {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::DuplicateStateSkipped {
                            duplicate_state_fingerprint: transition
                                .replay_step
                                .next_state_fingerprint,
                        },
                    );
                    continue;
                }

                let child_snapshot = match client.get_snapshot(AiSearchSnapshotGetRequest {
                    session_id: node.session_id.clone(),
                    snapshot_id: transition.next_snapshot_id,
                    state_fingerprint: transition.replay_step.next_state_fingerprint,
                }) {
                    Ok(ok) => ok.snapshot,
                    Err(error) => {
                        stats.controller_errors += 1;
                        let reason = ai_search_failure_reason_from_machine_api_error(
                            AiSearchMachineApiEndpointKind::SnapshotGet,
                            &error,
                        );
                        trace.push(
                            &node,
                            ai_search_machine_controller_trace_kind_from_reason(&reason),
                        );
                        return Err(ai_search_failure(
                            reason,
                            best_partial,
                            stats,
                            trace.finish(),
                            training_trace_records,
                        ));
                    }
                };

                let child_node_id = node_ids.allocate();
                let child = ai_search_make_child_search_node(
                    &node,
                    child_node_id,
                    transition,
                    &child_snapshot,
                );
                discovered_states.insert(child.state_fingerprint);
                trace.push(
                    &node,
                    AiSearchTraceEventKind::ChildQueued {
                        child_node_id,
                        state_fingerprint: child.state_fingerprint,
                    },
                );
                queue.push(child);
            }

            let mut next_repairs = Vec::new();
            for record in evaluation.accepted_failure_records {
                if ai_search_repeated_repair_error(&record.envelope, &record.failure) {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::RepairChainStopped {
                            parent_candidate_hash: record.failure.candidate_hash,
                            error_kind: record.failure.error_kind,
                            repair_depth: ai_search_repair_depth_of(&record.envelope),
                            reason: AiSearchRepairChainStopReason::RepeatedError,
                            repeated_candidate_payload_hash: None,
                        },
                    );
                    continue;
                }

                let parent_repair_depth = ai_search_repair_depth_of(&record.envelope);
                if parent_repair_depth >= 2 {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::RepairChainStopped {
                            parent_candidate_hash: record.failure.candidate_hash,
                            error_kind: record.failure.error_kind,
                            repair_depth: parent_repair_depth,
                            reason: AiSearchRepairChainStopReason::MaxRepairDepth,
                            repeated_candidate_payload_hash: None,
                        },
                    );
                    continue;
                }

                let repair_output = repair.repair_candidate(
                    goal,
                    &record.envelope,
                    &record.failure,
                    parent_repair_depth + 1,
                );
                for repeated_hash in repair_output.repeated_candidate_payload_hashes {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::RepairChainStopped {
                            parent_candidate_hash: record.failure.candidate_hash,
                            error_kind: record.failure.error_kind,
                            repair_depth: parent_repair_depth,
                            reason: AiSearchRepairChainStopReason::RepeatedCandidate,
                            repeated_candidate_payload_hash: Some(repeated_hash),
                        },
                    );
                }
                next_repairs.extend(repair_output.pending);
            }
            pending_repairs = ai_search_limit_repairs(next_repairs);

            deferred_candidates = evaluation.deferred_candidates;
            if deferred_candidates.is_empty() && pending_repairs.is_empty() {
                if candidates_exceeded_remaining_tactic_budget
                    && evaluated_for_node >= input.search_budget.max_tactics_per_node
                {
                    trace.push(
                        &node,
                        AiSearchTraceEventKind::MaxTacticsPerNodeStopped {
                            max_tactics_per_node: input.search_budget.max_tactics_per_node,
                        },
                    );
                }
                break;
            }
            if evaluated_for_node >= input.search_budget.max_tactics_per_node {
                ai_search_record_deferred_candidate_drops(
                    &mut trace,
                    &node,
                    &deferred_candidates,
                    AiSearchDeferredCandidateDropReason::MaxTacticsPerNode,
                );
                trace.push(
                    &node,
                    AiSearchTraceEventKind::MaxTacticsPerNodeStopped {
                        max_tactics_per_node: input.search_budget.max_tactics_per_node,
                    },
                );
                break;
            }
        }
    }

    if let Some(goal_id) = initial_no_candidate_goal.filter(|_| {
        best_partial
            .as_ref()
            .is_some_and(|partial| partial.parent.is_none())
    }) {
        failure_reason = AiSearchFailureReason::NoCandidateForSelectedGoal { goal_id };
    } else if matches!(failure_reason, AiSearchFailureReason::QueueExhausted) && depth_budget_hit {
        failure_reason = AiSearchFailureReason::SearchBudgetExceeded {
            limit: AiSearchBudgetLimit::MaxDepth,
        };
    }

    Err(ai_search_failure(
        failure_reason,
        best_partial,
        stats,
        trace.finish(),
        training_trace_records,
    ))
}

struct AiSearchClosedNodeVerified {
    replay_plan: AiSearchReplayPlan,
    replay_response: MachineReplayOkFields,
    verify_response: MachineApiOkResponse<MachineVerifyOkFields>,
}

enum AiSearchClosedNodeOutcome {
    Verified(Box<AiSearchClosedNodeVerified>),
    Rejected,
    ControllerError { reason: AiSearchFailureReason },
}

fn ai_search_attempt_closed_node(
    client: &mut impl AiSearchMachineApiClient,
    node: &AiSearchNode,
    stats: &mut AiSearchStats,
    trace: &mut AiSearchTraceBuilder,
) -> AiSearchClosedNodeOutcome {
    let replay_plan = ai_search_build_replay_plan(node);
    let replay_source = ai_search_replay_request_json(node.session_id.clone(), &replay_plan);
    let replay_response = match client.replay(&replay_source) {
        Ok(response) => match response {
            MachineApiResponseEnvelope::Ok(ok) => {
                if ok.status == MachineApiResponseStatus::Ok {
                    ok.endpoint_fields
                } else {
                    ai_search_record_closed_node_replay_rejection(node, stats, trace, ok.status);
                    return AiSearchClosedNodeOutcome::Rejected;
                }
            }
            MachineApiResponseEnvelope::SchedulerStopped(stop) => {
                ai_search_record_closed_node_replay_rejection(node, stats, trace, stop.status);
                return AiSearchClosedNodeOutcome::Rejected;
            }
            MachineApiResponseEnvelope::Error(error) => {
                if ai_search_is_replay_controller_error_wire(&error.error) {
                    return ai_search_closed_node_controller_error(
                        node,
                        stats,
                        trace,
                        ai_search_machine_controller_error_reason_from_wire(
                            AiSearchMachineApiEndpointKind::Replay,
                            error.error.kind.as_str(),
                            Some(error.error.phase.as_str()),
                            Some(error.error.diagnostic_hash),
                        ),
                    );
                }
                ai_search_record_closed_node_replay_rejection(node, stats, trace, error.status);
                return AiSearchClosedNodeOutcome::Rejected;
            }
        },
        Err(error) => {
            if ai_search_is_replay_controller_error(&error) {
                return ai_search_closed_node_controller_error(
                    node,
                    stats,
                    trace,
                    ai_search_failure_reason_from_machine_api_error(
                        AiSearchMachineApiEndpointKind::Replay,
                        &error,
                    ),
                );
            }
            ai_search_record_closed_node_replay_rejection(
                node,
                stats,
                trace,
                ai_search_replay_error_status(&error),
            );
            return AiSearchClosedNodeOutcome::Rejected;
        }
    };

    let verify_source = ai_search_verify_request_json(
        node.session_id.clone(),
        replay_response.final_snapshot_id,
        replay_response.final_state_fingerprint,
    );
    let verify_response = match client.verify(&verify_source) {
        Ok(response) => match response {
            MachineApiResponseEnvelope::Ok(ok) => {
                if ok.status == MachineApiResponseStatus::Verified {
                    ok
                } else {
                    ai_search_record_closed_node_verify_rejection(node, stats, trace, ok.status);
                    return AiSearchClosedNodeOutcome::Rejected;
                }
            }
            MachineApiResponseEnvelope::SchedulerStopped(stop) => {
                ai_search_record_closed_node_verify_rejection(node, stats, trace, stop.status);
                return AiSearchClosedNodeOutcome::Rejected;
            }
            MachineApiResponseEnvelope::Error(error) => {
                if ai_search_is_verify_controller_error_wire(&error.error) {
                    return ai_search_closed_node_controller_error(
                        node,
                        stats,
                        trace,
                        ai_search_machine_controller_error_reason_from_wire(
                            AiSearchMachineApiEndpointKind::Verify,
                            error.error.kind.as_str(),
                            Some(error.error.phase.as_str()),
                            Some(error.error.diagnostic_hash),
                        ),
                    );
                }
                ai_search_record_closed_node_verify_rejection(node, stats, trace, error.status);
                return AiSearchClosedNodeOutcome::Rejected;
            }
        },
        Err(error) => {
            if ai_search_is_verify_controller_error(&error) {
                return ai_search_closed_node_controller_error(
                    node,
                    stats,
                    trace,
                    ai_search_failure_reason_from_machine_api_error(
                        AiSearchMachineApiEndpointKind::Verify,
                        &error,
                    ),
                );
            }
            ai_search_record_closed_node_verify_rejection(
                node,
                stats,
                trace,
                ai_search_verify_error_status(&error),
            );
            return AiSearchClosedNodeOutcome::Rejected;
        }
    };

    AiSearchClosedNodeOutcome::Verified(Box::new(AiSearchClosedNodeVerified {
        replay_plan,
        replay_response,
        verify_response,
    }))
}

fn ai_search_closed_node_controller_error(
    node: &AiSearchNode,
    stats: &mut AiSearchStats,
    trace: &mut AiSearchTraceBuilder,
    reason: AiSearchFailureReason,
) -> AiSearchClosedNodeOutcome {
    stats.controller_errors += 1;
    trace.push(
        node,
        ai_search_machine_controller_trace_kind_from_reason(&reason),
    );
    AiSearchClosedNodeOutcome::ControllerError { reason }
}

fn ai_search_record_closed_node_replay_rejection(
    node: &AiSearchNode,
    stats: &mut AiSearchStats,
    trace: &mut AiSearchTraceBuilder,
    status: MachineApiResponseStatus,
) {
    stats.closed_node_replay_rejections += 1;
    trace.push(
        node,
        AiSearchTraceEventKind::ClosedNodeReplayRejected {
            endpoint: ai_search_machine_api_endpoint_wire(AiSearchMachineApiEndpointKind::Replay)
                .to_owned(),
            status,
        },
    );
}

fn ai_search_record_closed_node_verify_rejection(
    node: &AiSearchNode,
    stats: &mut AiSearchStats,
    trace: &mut AiSearchTraceBuilder,
    status: MachineApiResponseStatus,
) {
    stats.closed_node_verify_rejections += 1;
    trace.push(
        node,
        AiSearchTraceEventKind::ClosedNodeVerifyRejected {
            endpoint: ai_search_machine_api_endpoint_wire(AiSearchMachineApiEndpointKind::Verify)
                .to_owned(),
            status,
        },
    );
}

fn ai_search_is_replay_controller_error(error: &AiSearchMachineApiError) -> bool {
    match error {
        AiSearchMachineApiError::Replay(error) => {
            ai_search_is_replay_controller_error_kind(error.diagnostic.kind)
        }
        _ => true,
    }
}

fn ai_search_is_replay_controller_error_wire(error: &MachineApiErrorWire) -> bool {
    ai_search_is_replay_controller_error_kind(error.kind)
}

fn ai_search_is_replay_controller_error_kind(kind: MachineApiErrorKind) -> bool {
    matches!(
        kind,
        MachineApiErrorKind::InvalidReplayPlan
            | MachineApiErrorKind::UnknownSession
            | MachineApiErrorKind::SessionRootHashMismatch
            | MachineApiErrorKind::StateFingerprintMismatch
            | MachineApiErrorKind::ReplayHashMismatch
            | MachineApiErrorKind::InvalidMachineProofState
    )
}

fn ai_search_is_verify_controller_error(error: &AiSearchMachineApiError) -> bool {
    match error {
        AiSearchMachineApiError::Verify(error) => {
            ai_search_is_verify_controller_error_kind(error.diagnostic.kind, error.diagnostic.phase)
        }
        _ => true,
    }
}

fn ai_search_is_verify_controller_error_wire(error: &MachineApiErrorWire) -> bool {
    ai_search_is_verify_controller_error_kind(error.kind, error.phase)
}

fn ai_search_is_verify_controller_error_kind(
    kind: MachineApiErrorKind,
    phase: crate::MachineApiDiagnosticPhase,
) -> bool {
    matches!(
        (kind, phase),
        (
            MachineApiErrorKind::InvalidVerifyRequest,
            crate::MachineApiDiagnosticPhase::RequestValidation
        )
    ) || matches!(
        kind,
        MachineApiErrorKind::UnknownSession
            | MachineApiErrorKind::UnknownSnapshot
            | MachineApiErrorKind::StateFingerprintMismatch
            | MachineApiErrorKind::InvalidMachineProofState
    )
}

fn ai_search_replay_error_status(error: &AiSearchMachineApiError) -> MachineApiResponseStatus {
    match error {
        AiSearchMachineApiError::Replay(error) => ai_search_replay_response_status(&error.response),
        _ => MachineApiResponseStatus::Error,
    }
}

fn ai_search_verify_error_status(error: &AiSearchMachineApiError) -> MachineApiResponseStatus {
    match error {
        AiSearchMachineApiError::Verify(error) => ai_search_verify_response_status(&error.response),
        _ => MachineApiResponseStatus::Error,
    }
}

fn ai_search_replay_response_status(response: &MachineReplayResponse) -> MachineApiResponseStatus {
    match response {
        MachineApiResponseEnvelope::Ok(ok) => ok.status,
        MachineApiResponseEnvelope::Error(error) => error.status,
        MachineApiResponseEnvelope::SchedulerStopped(stop) => stop.status,
    }
}

fn ai_search_verify_response_status(response: &MachineVerifyResponse) -> MachineApiResponseStatus {
    match response {
        MachineApiResponseEnvelope::Ok(ok) => ok.status,
        MachineApiResponseEnvelope::Error(error) => error.status,
        MachineApiResponseEnvelope::SchedulerStopped(stop) => stop.status,
    }
}

fn ai_search_root_search_node(input: &AiSearchInput, node_id: AiSearchNodeId) -> AiSearchNode {
    AiSearchNode {
        node_id,
        session_id: input.session_id.clone(),
        session_root_hash: input.session_root_hash,
        initial_state_fingerprint: input.initial_snapshot.state_fingerprint,
        snapshot_id: input.initial_snapshot.snapshot_id,
        state_fingerprint: input.initial_snapshot.state_fingerprint,
        goals: ai_search_goal_summaries(&input.initial_snapshot),
        replay_steps: Vec::new(),
        depth: 0,
        cumulative_score: 0,
        last_candidate: None,
        last_candidate_hash: None,
        used_premises: Vec::new(),
        parent: None,
        status: AiSearchNodeStatus::Queued,
    }
}

fn ai_search_make_child_search_node(
    parent: &AiSearchNode,
    node_id: AiSearchNodeId,
    transition: AiSearchSuccessfulCandidateTransition,
    child_snapshot: &MachineProofSnapshot,
) -> AiSearchNode {
    let mut replay_steps = parent.replay_steps.clone();
    replay_steps.push(transition.replay_step.clone());
    AiSearchNode {
        node_id,
        session_id: parent.session_id.clone(),
        session_root_hash: parent.session_root_hash,
        initial_state_fingerprint: parent.initial_state_fingerprint,
        snapshot_id: transition.next_snapshot_id,
        state_fingerprint: transition.replay_step.next_state_fingerprint,
        goals: ai_search_goal_summaries(child_snapshot),
        replay_steps,
        depth: parent
            .depth
            .checked_add(1)
            .expect("ai_search search depth fits in u32"),
        cumulative_score: parent.cumulative_score,
        last_candidate: Some(transition.envelope.candidate.clone()),
        last_candidate_hash: Some(transition.replay_step.candidate_hash),
        used_premises: ai_search_append_unique_premises(
            &parent.used_premises,
            &transition.envelope.metadata.premises_used,
        ),
        parent: Some(parent.node_id),
        status: AiSearchNodeStatus::Queued,
    }
}

fn ai_search_append_unique_premises(
    current: &[AiSearchPremiseUsage],
    next: &[AiSearchPremiseUsage],
) -> Vec<AiSearchPremiseUsage> {
    let mut out = current.to_vec();
    for premise in next {
        if !out.contains(premise) {
            out.push(premise.clone());
        }
    }
    out
}

fn ai_search_record_training_trace_batch(
    records: &mut Vec<AiSearchTrainingTraceRecord>,
    node: &AiSearchNode,
    batch_index: &mut u32,
    goal: &AiSearchGoalSummary,
    retrieved_premises: &[AiSearchPremiseCacheEntry],
    evaluation: &AiSearchBatchEvaluation,
) {
    if evaluation.evaluated_count == 0 {
        return;
    }

    records.push(AiSearchTrainingTraceRecord {
        trace_schema: AI_SEARCH_TRAINING_TRACE_SCHEMA.to_owned(),
        session_root_hash: node.session_root_hash,
        snapshot_id: node.snapshot_id,
        state_fingerprint: node.state_fingerprint,
        node_id: node.node_id,
        batch_index: *batch_index,
        goal: goal.clone(),
        retrieved_premises: retrieved_premises.to_vec(),
        tactic_candidates: evaluation.training_trace_candidates.clone(),
    });
    *batch_index = batch_index
        .checked_add(1)
        .expect("ai_search training batch index fits in u32");
}

fn ai_search_record_forbidden_candidate_discards(
    trace: &mut AiSearchTraceBuilder,
    node: &AiSearchNode,
    rejected: &[AiSearchRejectedCandidateEnvelope],
) {
    for rejected in rejected {
        trace.push(
            node,
            AiSearchTraceEventKind::ForbiddenCandidateDiscarded {
                ai_search_candidate_payload_hash: rejected
                    .envelope
                    .ai_search_candidate_payload_hash,
                forbidden_token_class: rejected.forbidden_token.class,
            },
        );
    }
}

fn ai_search_record_non_accepted_candidate_errors(
    trace: &mut AiSearchTraceBuilder,
    node: &AiSearchNode,
    errors: &[AiSearchNonAcceptedCandidateError],
) {
    for error in errors {
        trace.push(
            node,
            AiSearchTraceEventKind::NonAcceptedCandidateError {
                candidate_id: error.candidate_id.clone(),
                ai_search_candidate_payload_hash: error.ai_search_candidate_payload_hash,
                error_kind: error.error_kind,
                phase: error.phase,
                has_candidate_hash: error.has_candidate_hash,
                has_diagnostic_hash: true,
            },
        );
    }
}

fn ai_search_record_scheduler_dropped_candidates(
    trace: &mut AiSearchTraceBuilder,
    node: &AiSearchNode,
    request: &AiSearchTacticBatchRequest,
    evaluation: &AiSearchBatchEvaluation,
) {
    if evaluation.scheduler_stop.is_none() {
        return;
    }
    let deferred_ids = evaluation
        .deferred_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.as_str())
        .collect::<BTreeSet<_>>();
    for assigned in request
        .candidates
        .iter()
        .skip(evaluation.evaluated_count as usize)
    {
        if deferred_ids.contains(assigned.candidate_id.as_str()) {
            continue;
        }
        trace.push(
            node,
            AiSearchTraceEventKind::DeferredCandidateDropped {
                candidate_id: assigned.candidate_id.clone(),
                ai_search_candidate_payload_hash: assigned
                    .envelope
                    .ai_search_candidate_payload_hash,
                reason: AiSearchDeferredCandidateDropReason::SchedulerStoppedCandidate,
            },
        );
    }
}

fn ai_search_record_deferred_candidate_drops(
    trace: &mut AiSearchTraceBuilder,
    node: &AiSearchNode,
    deferred_candidates: &[AiSearchDeferredCandidate],
    reason: AiSearchDeferredCandidateDropReason,
) {
    for candidate in deferred_candidates {
        trace.push(
            node,
            AiSearchTraceEventKind::DeferredCandidateDropped {
                candidate_id: candidate.candidate_id.clone(),
                ai_search_candidate_payload_hash: candidate
                    .envelope
                    .ai_search_candidate_payload_hash,
                reason,
            },
        );
    }
}

fn ai_search_take_remaining_node_tactic_budget(
    candidates: Vec<AiSearchCandidateEnvelope>,
    remaining: u32,
) -> Vec<AiSearchCandidateEnvelope> {
    candidates.into_iter().take(remaining as usize).collect()
}

fn ai_search_total_open_goal_target_size(goals: &[AiSearchGoalSummary]) -> u64 {
    goals.iter().map(|goal| u64::from(goal.expr_size)).sum()
}

fn ai_search_failure(
    reason: AiSearchFailureReason,
    best_partial: Option<AiSearchNode>,
    search_stats: AiSearchStats,
    trace_events: Vec<AiSearchTraceEvent>,
    training_trace_records: Vec<AiSearchTrainingTraceRecord>,
) -> Box<AiSearchFailure> {
    let (best_partial_replay_prefix, best_snapshot_id, best_state_fingerprint, remaining_goals) =
        if let Some(node) = best_partial {
            (
                Some(node.replay_steps),
                Some(node.snapshot_id),
                Some(node.state_fingerprint),
                Some(node.goals),
            )
        } else {
            (None, None, None, None)
        };
    Box::new(AiSearchFailure {
        reason,
        best_partial_replay_prefix,
        best_snapshot_id,
        best_state_fingerprint,
        remaining_goals,
        search_stats,
        trace_events,
        training_trace_records,
    })
}

fn ai_search_failure_reason_from_tactic_batch_run_error(
    error: &AiSearchTacticBatchRunError,
) -> AiSearchFailureReason {
    match error {
        AiSearchTacticBatchRunError::MachineApi(error) => {
            ai_search_failure_reason_from_machine_api_error(
                AiSearchMachineApiEndpointKind::TacticBatch,
                error,
            )
        }
        AiSearchTacticBatchRunError::Controller(error) => {
            ai_search_failure_reason_from_controller_error(error)
        }
    }
}

fn ai_search_failure_reason_from_controller_error(
    error: &AiSearchMachineControllerError,
) -> AiSearchFailureReason {
    AiSearchFailureReason::MachineControllerError {
        endpoint: ai_search_machine_api_endpoint_wire(error.endpoint).to_owned(),
        error_kind: ai_search_machine_controller_error_kind_wire(error),
        error_phase: error.phase.map(|phase| phase.as_str().to_owned()),
        diagnostic_hash: error.diagnostic_hash,
    }
}

fn ai_search_machine_controller_error_kind_wire(error: &AiSearchMachineControllerError) -> String {
    match error.kind {
        AiSearchMachineControllerErrorKind::TopLevelBatchError => error.message.clone(),
        AiSearchMachineControllerErrorKind::BatchResponseContractViolation => {
            "batch_response_contract_violation".to_owned()
        }
        AiSearchMachineControllerErrorKind::SuggestedCandidateHashMismatch => {
            "suggested_candidate_hash_mismatch".to_owned()
        }
    }
}

fn ai_search_failure_reason_from_machine_api_error(
    fallback_endpoint: AiSearchMachineApiEndpointKind,
    error: &AiSearchMachineApiError,
) -> AiSearchFailureReason {
    match error {
        AiSearchMachineApiError::SnapshotGet(error) => {
            ai_search_machine_controller_error_reason_from_wire(
                fallback_endpoint,
                error.error.kind.as_str(),
                Some(error.error.phase.as_str()),
                Some(error.error.diagnostic_hash),
            )
        }
        AiSearchMachineApiError::SearchForGoal(error) => {
            ai_search_machine_controller_error_reason_from_diagnostic(
                fallback_endpoint,
                &error.diagnostic,
            )
        }
        AiSearchMachineApiError::TacticBatch(error) => {
            ai_search_machine_controller_error_reason_from_diagnostic(
                fallback_endpoint,
                &error.diagnostic,
            )
        }
        AiSearchMachineApiError::Replay(error) => {
            ai_search_machine_controller_error_reason_from_diagnostic(
                fallback_endpoint,
                &error.diagnostic,
            )
        }
        AiSearchMachineApiError::Verify(error) => {
            ai_search_machine_controller_error_reason_from_diagnostic(
                fallback_endpoint,
                &error.diagnostic,
            )
        }
        AiSearchMachineApiError::SearchForGoalResponse(error) => {
            ai_search_machine_controller_error_reason_from_wire(
                fallback_endpoint,
                error.kind.as_str(),
                Some(error.phase.as_str()),
                Some(error.diagnostic_hash),
            )
        }
        AiSearchMachineApiError::UnexpectedSchedulerStop { endpoint } => {
            ai_search_machine_controller_error_reason_from_wire(
                *endpoint,
                "scheduler_stopped",
                None,
                None,
            )
        }
        AiSearchMachineApiError::FakeRequestValidation { endpoint, error } => {
            ai_search_machine_controller_error_reason_from_wire(
                *endpoint,
                error.kind.as_str(),
                Some(crate::MachineApiDiagnosticPhase::RequestValidation.as_str()),
                None,
            )
        }
        AiSearchMachineApiError::FakeResponseExhausted { endpoint } => {
            ai_search_machine_controller_error_reason_from_wire(
                *endpoint,
                "transport_error",
                None,
                None,
            )
        }
    }
}

fn ai_search_machine_controller_error_reason_from_diagnostic(
    endpoint: AiSearchMachineApiEndpointKind,
    diagnostic: &crate::MachineApiDiagnosticProjection,
) -> AiSearchFailureReason {
    ai_search_machine_controller_error_reason_from_wire(
        endpoint,
        diagnostic.kind.as_str(),
        Some(diagnostic.phase.as_str()),
        diagnostic.diagnostic_hash().ok(),
    )
}

fn ai_search_machine_controller_error_reason_from_wire(
    endpoint: AiSearchMachineApiEndpointKind,
    error_kind: &str,
    error_phase: Option<&str>,
    diagnostic_hash: Option<Hash>,
) -> AiSearchFailureReason {
    AiSearchFailureReason::MachineControllerError {
        endpoint: ai_search_machine_api_endpoint_wire(endpoint).to_owned(),
        error_kind: error_kind.to_owned(),
        error_phase: error_phase.map(str::to_owned),
        diagnostic_hash,
    }
}

fn ai_search_machine_controller_trace_kind_from_reason(
    reason: &AiSearchFailureReason,
) -> AiSearchTraceEventKind {
    match reason {
        AiSearchFailureReason::MachineControllerError {
            endpoint,
            error_kind,
            ..
        } => AiSearchTraceEventKind::MachineControllerError {
            endpoint: endpoint.clone(),
            error_kind: error_kind.clone(),
        },
        _ => AiSearchTraceEventKind::MachineControllerError {
            endpoint: "ai_search".to_owned(),
            error_kind: "controller_error".to_owned(),
        },
    }
}

fn ai_search_machine_api_endpoint_wire(endpoint: AiSearchMachineApiEndpointKind) -> &'static str {
    match endpoint {
        AiSearchMachineApiEndpointKind::SnapshotGet => "/machine/snapshots/get",
        AiSearchMachineApiEndpointKind::SearchForGoal => "/machine/search/for_goal",
        AiSearchMachineApiEndpointKind::TacticBatch => "/machine/tactics/batch",
        AiSearchMachineApiEndpointKind::Replay => "/machine/replay",
        AiSearchMachineApiEndpointKind::Verify => "/machine/verify",
    }
}

#[derive(Clone, Debug, Default)]
struct AiSearchNodeIdAllocator {
    next: u64,
}

impl AiSearchNodeIdAllocator {
    fn new() -> Self {
        Self::default()
    }

    fn allocate(&mut self) -> AiSearchNodeId {
        let node_id = AiSearchNodeId(self.next);
        self.next = self
            .next
            .checked_add(1)
            .expect("ai_search node id fits in u64");
        node_id
    }
}

#[derive(Clone, Debug, Default)]
struct AiSearchPriorityQueue {
    nodes: Vec<AiSearchNode>,
}

impl AiSearchPriorityQueue {
    fn new() -> Self {
        Self::default()
    }

    fn push(&mut self, node: AiSearchNode) {
        self.nodes.push(node);
    }

    fn pop_best(&mut self) -> Option<AiSearchNode> {
        let best_index = self
            .nodes
            .iter()
            .enumerate()
            .min_by_key(|(_, node)| ai_search_node_priority_key(node))
            .map(|(index, _)| index)?;
        Some(self.nodes.remove(best_index))
    }
}

#[derive(Clone, Debug, Default)]
struct AiSearchTraceBuilder {
    events: Vec<AiSearchTraceEvent>,
}

impl AiSearchTraceBuilder {
    fn new() -> Self {
        Self::default()
    }

    fn push(&mut self, node: &AiSearchNode, kind: AiSearchTraceEventKind) {
        self.events.push(AiSearchTraceEvent {
            event_index: u64::try_from(self.events.len())
                .expect("ai_search trace event count fits in u64"),
            node_id: node.node_id,
            kind,
        });
    }

    fn finish(self) -> Vec<AiSearchTraceEvent> {
        self.events
    }
}

pub fn ai_search_snapshot_get_request_json(request: &AiSearchSnapshotGetRequest) -> String {
    format!(
        r#"{{"session_id":"{}","snapshot_id":"{}","state_fingerprint":"{}","include_pretty":false}}"#,
        request.session_id.wire(),
        request.snapshot_id.wire(),
        format_hash_string(&request.state_fingerprint)
    )
}

pub fn load_ai_search_initial_snapshot(
    client: &mut impl AiSearchMachineApiClient,
    request: AiSearchSnapshotGetRequest,
) -> AiSearchMachineApiResult<AiSearchInitialSnapshot> {
    let snapshot = client.get_snapshot(request)?.snapshot;
    let goals = ai_search_goal_summaries(&snapshot);
    Ok(AiSearchInitialSnapshot { snapshot, goals })
}

pub fn ai_search_goal_summaries(snapshot: &MachineProofSnapshot) -> Vec<AiSearchGoalSummary> {
    snapshot
        .goals
        .iter()
        .enumerate()
        .map(|(index, goal)| ai_search_goal_summary(goal, index))
        .collect()
}

pub fn select_ai_search_goal(snapshot: &MachineProofSnapshot) -> Option<AiSearchGoalSummary> {
    ai_search_goal_summaries(snapshot)
        .into_iter()
        .min_by(ai_search_goal_selection_order)
}

pub fn ai_search_mvp_premise_query_json(request: &AiSearchPremiseQueryRequest) -> String {
    format!(
        r#"{{"session_id":"{}","snapshot_id":"{}","state_fingerprint":"{}","goal_id":"{}","modes":["exact","apply","rw","simp"],"limit":{},"filters":{{"exclude_axioms":true}}}}"#,
        request.session_id.wire(),
        request.snapshot_id.wire(),
        format_hash_string(&request.state_fingerprint),
        format_goal_id_wire(request.goal_id),
        AI_SEARCH_MVP_PREMISE_QUERY_LIMIT
    )
}

pub fn retrieve_ai_search_premises(
    client: &mut impl AiSearchMachineApiClient,
    request: &AiSearchPremiseQueryRequest,
    session_root_hash: Hash,
) -> AiSearchMachineApiResult<AiSearchPremiseRetrieval> {
    let source = ai_search_mvp_premise_query_json(request);
    let response = client.search_for_goal(&source)?;
    match response {
        MachineApiResponseEnvelope::Ok(ok) => Ok(ai_search_premise_retrieval_from_search_ok(
            session_root_hash,
            ok.endpoint_fields,
        )),
        MachineApiResponseEnvelope::Error(error) => Err(
            AiSearchMachineApiError::SearchForGoalResponse(Box::new(error.error)),
        ),
        MachineApiResponseEnvelope::SchedulerStopped(_) => {
            Err(AiSearchMachineApiError::UnexpectedSchedulerStop {
                endpoint: AiSearchMachineApiEndpointKind::SearchForGoal,
            })
        }
    }
}

pub fn ai_search_run_local_authoring_loop(
    client: &mut impl AiSearchMachineApiClient,
    input: AiSearchInput,
) -> AiSearchLocalAuthoringLoopOutput {
    let mut output = AiSearchLocalAuthoringLoopOutput::default();
    let snapshot = match client.get_snapshot(AiSearchSnapshotGetRequest {
        session_id: input.session_id.clone(),
        snapshot_id: input.initial_snapshot.snapshot_id,
        state_fingerprint: input.initial_snapshot.state_fingerprint,
    }) {
        Ok(ok) => ok.snapshot,
        Err(error) => {
            output.controller_error = Some(
                ai_search_local_authoring_controller_error_from_machine_api_error(
                    AiSearchMachineApiEndpointKind::SnapshotGet,
                    &error,
                ),
            );
            return output;
        }
    };

    output.remaining_goals = Some(ai_search_goal_summaries(&snapshot));
    output.snapshot = Some(snapshot.clone());

    let Some(goal_summary) = select_ai_search_goal(&snapshot) else {
        return output;
    };
    let goal_id = goal_summary.goal_id;
    output.selected_goal = Some(goal_summary);

    let Some(goal) = snapshot.goals.iter().find(|goal| goal.goal_id == goal_id) else {
        output.controller_error = Some(ai_search_local_authoring_controller_error_from_wire(
            AiSearchMachineApiEndpointKind::SnapshotGet,
            "invalid_machine_proof_state",
            None,
            None,
            None,
        ));
        return output;
    };

    let retrieval = match retrieve_ai_search_premises(
        client,
        &AiSearchPremiseQueryRequest {
            session_id: input.session_id.clone(),
            snapshot_id: snapshot.snapshot_id,
            state_fingerprint: snapshot.state_fingerprint,
            goal_id,
        },
        input.session_root_hash,
    ) {
        Ok(retrieval) => retrieval,
        Err(error) => {
            output.controller_error = Some(
                ai_search_local_authoring_controller_error_from_machine_api_error(
                    AiSearchMachineApiEndpointKind::SearchForGoal,
                    &error,
                ),
            );
            return output;
        }
    };
    output.retrieval = Some(retrieval.clone());

    let candidate_generation = ai_search_mvp_candidate_generation(goal, &retrieval);
    let candidates = candidate_generation.accepted;
    output.generated_candidate_count = usize_to_u32(candidates.len());

    for stage in AI_SEARCH_CHEAP_FIRST_STAGE_ORDER.iter().copied() {
        let Some(batch_request) = ai_search_cheap_first_tactic_batch_request(
            input.session_id.clone(),
            snapshot.snapshot_id,
            snapshot.state_fingerprint,
            goal_id,
            stage,
            candidates.clone(),
            input.scheduler_limits,
        ) else {
            continue;
        };
        output.executed_stages.push(stage);

        let evaluation = match ai_search_run_tactic_batch(client, &batch_request) {
            Ok(evaluation) => evaluation,
            Err(error) => {
                output.controller_error = Some(
                    ai_search_local_authoring_controller_error_from_tactic_batch_run_error(&error),
                );
                return output;
            }
        };

        output
            .accepted_failures
            .extend(evaluation.accepted_failure_records.clone());
        output
            .non_accepted_errors
            .extend(evaluation.non_accepted_errors.clone());

        let successful_transition = evaluation.successful_transitions.first().cloned();
        output.batch_evaluations.push(evaluation);

        if let Some(transition) = successful_transition {
            output.successful_stage = Some(stage);
            output.successful_transition = Some(transition.clone());

            let prefix = vec![transition.replay_step.clone()];
            output.best_partial_replay_prefix = Some(prefix.clone());
            output.advisory_replay_plan = Some(AiSearchReplayPlan {
                protocol_version: MachineApiVersion::V1,
                session_root_hash: input.session_root_hash,
                initial_state_fingerprint: snapshot.state_fingerprint,
                steps: prefix,
                final_state_fingerprint: transition.replay_step.next_state_fingerprint,
            });

            match client.get_snapshot(AiSearchSnapshotGetRequest {
                session_id: input.session_id,
                snapshot_id: transition.next_snapshot_id,
                state_fingerprint: transition.replay_step.next_state_fingerprint,
            }) {
                Ok(ok) => {
                    output.remaining_goals = Some(ai_search_goal_summaries(&ok.snapshot));
                }
                Err(error) => {
                    output.controller_error = Some(
                        ai_search_local_authoring_controller_error_from_machine_api_error(
                            AiSearchMachineApiEndpointKind::SnapshotGet,
                            &error,
                        ),
                    );
                }
            }
            return output;
        }

        if output
            .batch_evaluations
            .last()
            .is_some_and(|evaluation| evaluation.scheduler_stop.is_some())
        {
            return output;
        }
    }

    output
}

fn ai_search_local_authoring_controller_error_from_tactic_batch_run_error(
    error: &AiSearchTacticBatchRunError,
) -> AiSearchLocalAuthoringControllerError {
    match error {
        AiSearchTacticBatchRunError::MachineApi(error) => {
            ai_search_local_authoring_controller_error_from_machine_api_error(
                AiSearchMachineApiEndpointKind::TacticBatch,
                error,
            )
        }
        AiSearchTacticBatchRunError::Controller(error) => {
            let status = error.status;
            let reason = ai_search_failure_reason_from_controller_error(error);
            ai_search_local_authoring_controller_error_from_failure_reason(&reason, status)
        }
    }
}

fn ai_search_local_authoring_controller_error_from_machine_api_error(
    fallback_endpoint: AiSearchMachineApiEndpointKind,
    error: &AiSearchMachineApiError,
) -> AiSearchLocalAuthoringControllerError {
    let reason = ai_search_failure_reason_from_machine_api_error(fallback_endpoint, error);
    ai_search_local_authoring_controller_error_from_failure_reason(&reason, None)
}

fn ai_search_local_authoring_controller_error_from_failure_reason(
    reason: &AiSearchFailureReason,
    status: Option<MachineApiResponseStatus>,
) -> AiSearchLocalAuthoringControllerError {
    match reason {
        AiSearchFailureReason::MachineControllerError {
            endpoint,
            error_kind,
            error_phase,
            diagnostic_hash,
        } => AiSearchLocalAuthoringControllerError {
            endpoint: endpoint.clone(),
            error_kind: error_kind.clone(),
            error_phase: error_phase.clone(),
            diagnostic_hash: *diagnostic_hash,
            status,
        },
        _ => ai_search_local_authoring_controller_error_from_wire(
            AiSearchMachineApiEndpointKind::TacticBatch,
            "controller_error",
            None,
            None,
            status,
        ),
    }
}

fn ai_search_local_authoring_controller_error_from_wire(
    endpoint: AiSearchMachineApiEndpointKind,
    error_kind: &str,
    error_phase: Option<&str>,
    diagnostic_hash: Option<Hash>,
    status: Option<MachineApiResponseStatus>,
) -> AiSearchLocalAuthoringControllerError {
    AiSearchLocalAuthoringControllerError {
        endpoint: ai_search_machine_api_endpoint_wire(endpoint).to_owned(),
        error_kind: error_kind.to_owned(),
        error_phase: error_phase.map(str::to_owned),
        diagnostic_hash,
        status,
    }
}

pub fn ai_search_premise_retrieval_from_search_ok(
    session_root_hash: Hash,
    search: MachineTheoremSearchOkFields,
) -> AiSearchPremiseRetrieval {
    let cache_key = ai_search_retrieval_cache_key(session_root_hash, &search);
    let cache_entries = ai_search_premise_cache_entries(&search);
    AiSearchPremiseRetrieval {
        cache_key,
        cache_entries,
        results: search.results,
    }
}

pub fn ai_search_retrieval_cache_key(
    session_root_hash: Hash,
    search: &MachineTheoremSearchOkFields,
) -> AiSearchRetrievalCacheKey {
    AiSearchRetrievalCacheKey {
        session_root_hash,
        query_fingerprint: search.query_fingerprint,
        theorem_index_fingerprint: search.theorem_index_fingerprint,
    }
}

pub fn ai_search_premise_cache_entries(
    search: &MachineTheoremSearchOkFields,
) -> Vec<AiSearchPremiseCacheEntry> {
    search
        .results
        .iter()
        .enumerate()
        .map(|(index, result)| ai_search_premise_cache_entry(result, index))
        .collect()
}

pub fn ai_search_repair_premise_retrieval_from_premise_search_ok(
    search: &MachinePremiseSearchOkFields,
) -> AiSearchRepairPremiseRetrieval {
    let premises = search
        .results
        .iter()
        .map(|result| AiSearchRepairPremise {
            premise_id: result.premise_id.clone(),
            verified_identity: result.verified_identity.clone(),
            selected_modes: result.selected_modes.clone(),
            ranking_metadata: result.ranking_metadata.clone(),
            candidate_provenance: result.candidate_provenance.clone(),
        })
        .collect::<Vec<_>>();
    let premise_sets = search
        .results
        .iter()
        .filter_map(|result| {
            let premise_set = result.ranking_metadata.premise_set.as_ref()?;
            let selected_premise_identities = premise_set
                .selected_premises
                .iter()
                .filter_map(|selected| {
                    search
                        .results
                        .iter()
                        .find(|candidate| {
                            ai_search_repair_premise_matches_structural_ref(
                                &candidate.verified_identity,
                                &selected.premise,
                            )
                        })
                        .map(|candidate| candidate.verified_identity.clone())
                })
                .collect::<Vec<_>>();
            Some(AiSearchRepairPremiseSet {
                source_premise_id: result.premise_id.clone(),
                selected_premise_identities,
                axiom_impact: premise_set.axiom_impact.clone(),
            })
        })
        .collect::<Vec<_>>();
    AiSearchRepairPremiseRetrieval {
        query_fingerprint: search.query_fingerprint,
        query_profile_hash: search.query_profile_hash,
        theorem_index_fingerprint: search.theorem_index_fingerprint,
        retrieval_cache_key: search.retrieval_cache_key.clone(),
        premises,
        premise_sets,
    }
}

fn ai_search_repair_premise_matches_structural_ref(
    identity: &MachineVerifiedPremiseIdentity,
    structural: &crate::MachinePremiseStructuralRef,
) -> bool {
    identity.module == structural.module
        && identity.global_ref.name == structural.name
        && Some(identity.export_hash) == structural.export_hash
        && identity.global_ref.decl_interface_hash == structural.decl_interface_hash
}

pub fn ai_search_focused_replay_payload(
    replay_plan: AiSearchReplayPlan,
    retrieval_provenance: Vec<AiSearchFocusedReplayPremiseProvenance>,
) -> AiSearchFocusedReplayPayload {
    AiSearchFocusedReplayPayload {
        schema: AI_SEARCH_FOCUSED_REPLAY_PAYLOAD_SCHEMA,
        replay_plan,
        retrieval_provenance,
    }
}

pub fn ai_search_focused_replay_provenance_from_retrieval(
    step_index: u32,
    retrieval: &AiSearchRepairPremiseRetrieval,
) -> AiSearchFocusedReplayPremiseProvenance {
    AiSearchFocusedReplayPremiseProvenance {
        step_index,
        query_fingerprint: retrieval.query_fingerprint,
        theorem_index_fingerprint: retrieval.theorem_index_fingerprint,
        premise_identities: retrieval
            .premises
            .iter()
            .map(|premise| premise.verified_identity.clone())
            .collect(),
    }
}

pub fn ai_search_focused_replay_payload_json(payload: &AiSearchFocusedReplayPayload) -> String {
    let provenance = payload
        .retrieval_provenance
        .iter()
        .map(ai_search_focused_replay_premise_provenance_json)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"schema":{},"replay_plan":{},"retrieval_provenance":[{}]}}"#,
        json_string(payload.schema),
        ai_search_replay_plan_json(&payload.replay_plan),
        provenance,
    )
}

fn ai_search_focused_replay_premise_provenance_json(
    provenance: &AiSearchFocusedReplayPremiseProvenance,
) -> String {
    let identities = provenance
        .premise_identities
        .iter()
        .map(verified_premise_identity_json)
        .collect::<Vec<_>>()
        .join(",");
    let identity_hashes = provenance
        .premise_identities
        .iter()
        .map(|identity| json_string(&format_hash_string(&identity.identity_hash())))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"step_index":{},"query_fingerprint":{},"theorem_index_fingerprint":{},"premise_identities":[{}],"premise_identity_hashes":[{}]}}"#,
        provenance.step_index,
        json_string(&format_hash_string(&provenance.query_fingerprint)),
        json_string(&format_hash_string(&provenance.theorem_index_fingerprint)),
        identities,
        identity_hashes,
    )
}

pub fn ai_search_premise_graph_ranking_features(
    retrieval: &AiSearchPremiseRetrieval,
    graph_snapshot: Option<&CertificateTheoremGraphSnapshot>,
) -> AiSearchPremiseGraphRanking {
    ai_search_premise_graph_aware_retrieval(
        retrieval,
        graph_snapshot,
        AiSearchPremiseGraphRankingOptions::default(),
    )
    .unwrap_or_else(|error| {
        let fallback = match error {
            AiSearchPremiseGraphRankingError::GraphSnapshotStale { .. } => {
                AiSearchPremiseGraphRankingFallback::SnapshotStaleIgnored
            }
            AiSearchPremiseGraphRankingError::GraphSnapshotInvalid => {
                AiSearchPremiseGraphRankingFallback::SnapshotInvalidIgnored
            }
        };
        ai_search_premise_graph_empty_ranking(retrieval, fallback)
    })
}

pub fn ai_search_premise_graph_aware_retrieval(
    retrieval: &AiSearchPremiseRetrieval,
    graph_snapshot: Option<&CertificateTheoremGraphSnapshot>,
    options: AiSearchPremiseGraphRankingOptions,
) -> Result<AiSearchPremiseGraphRanking, AiSearchPremiseGraphRankingError> {
    let Some(snapshot) = graph_snapshot else {
        return Ok(ai_search_premise_graph_empty_ranking(
            retrieval,
            AiSearchPremiseGraphRankingFallback::SnapshotMissing,
        ));
    };
    let graph_snapshot_hash = match ai_search_validate_graph_snapshot(snapshot, options) {
        Ok(hash) => hash,
        Err(error) => {
            if options.stale_policy == AiSearchPremiseGraphSnapshotStalePolicy::Reject {
                return Err(error);
            }
            let fallback = match error {
                AiSearchPremiseGraphRankingError::GraphSnapshotStale { .. } => {
                    AiSearchPremiseGraphRankingFallback::SnapshotStaleIgnored
                }
                AiSearchPremiseGraphRankingError::GraphSnapshotInvalid => {
                    AiSearchPremiseGraphRankingFallback::SnapshotInvalidIgnored
                }
            };
            return Ok(ai_search_premise_graph_empty_ranking(retrieval, fallback));
        }
    };

    let mut entries = retrieval
        .cache_entries
        .iter()
        .map(|entry| ai_search_premise_graph_ranking_entry(entry, Some(snapshot)))
        .collect::<Vec<_>>();
    entries.sort_by(ai_search_premise_graph_ranking_entry_order);
    for (index, entry) in entries.iter_mut().enumerate() {
        entry.graph_rank = usize_to_u32(index);
    }
    Ok(AiSearchPremiseGraphRanking {
        graph_snapshot_hash: Some(graph_snapshot_hash),
        fallback: AiSearchPremiseGraphRankingFallback::PrecomputedSnapshot,
        entries,
    })
}

fn ai_search_premise_graph_empty_ranking(
    retrieval: &AiSearchPremiseRetrieval,
    fallback: AiSearchPremiseGraphRankingFallback,
) -> AiSearchPremiseGraphRanking {
    let mut entries = retrieval
        .cache_entries
        .iter()
        .map(|entry| ai_search_premise_graph_ranking_entry(entry, None))
        .collect::<Vec<_>>();
    entries.sort_by(ai_search_premise_graph_ranking_entry_order);
    for (index, entry) in entries.iter_mut().enumerate() {
        entry.graph_rank = usize_to_u32(index);
    }
    AiSearchPremiseGraphRanking {
        graph_snapshot_hash: None,
        fallback,
        entries,
    }
}

fn ai_search_validate_graph_snapshot(
    snapshot: &CertificateTheoremGraphSnapshot,
    options: AiSearchPremiseGraphRankingOptions,
) -> Result<Hash, AiSearchPremiseGraphRankingError> {
    let graph_snapshot_hash = options
        .expected_graph_snapshot_hash
        .unwrap_or(snapshot.graph_hash);
    validate_certificate_theorem_graph_snapshot_sidecar(
        CertificateTheoremGraphSnapshotSidecar::Inline {
            snapshot,
            graph_snapshot_hash,
        },
        CertificateTheoremGraphSnapshotValidationOptions::default(),
    )
    .map(|validated| {
        validated
            .expect("inline graph snapshot validation returns a validated snapshot")
            .graph_snapshot_hash
    })
    .map_err(|error| match error {
        CertificateTheoremGraphError::GraphSnapshotHashMismatch { expected, actual } => {
            AiSearchPremiseGraphRankingError::GraphSnapshotStale { expected, actual }
        }
        _ => {
            let actual = certificate_theorem_graph_snapshot_hash(snapshot);
            if graph_snapshot_hash != actual {
                AiSearchPremiseGraphRankingError::GraphSnapshotStale {
                    expected: graph_snapshot_hash,
                    actual,
                }
            } else {
                AiSearchPremiseGraphRankingError::GraphSnapshotInvalid
            }
        }
    })
}

pub fn ai_search_premise_usages(
    search: &MachineTheoremSearchOkFields,
) -> Vec<AiSearchPremiseUsage> {
    search.results.iter().map(ai_search_premise_usage).collect()
}

pub fn ai_search_mvp_candidate_envelopes(
    goal: &MachineGoalView,
    retrieval: &AiSearchPremiseRetrieval,
) -> Vec<AiSearchCandidateEnvelope> {
    ai_search_mvp_candidate_generation(goal, retrieval).accepted
}

pub fn ai_search_mvp_candidate_generation(
    goal: &MachineGoalView,
    retrieval: &AiSearchPremiseRetrieval,
) -> AiSearchCandidateFilterResult {
    let mut candidates = ai_search_suggested_candidate_envelopes(&retrieval.results);
    candidates.extend(ai_search_builtin_candidate_envelopes(goal));
    ai_search_rank_filter_and_dedupe_candidate_envelopes(candidates)
}

pub fn ai_search_suggested_candidate_envelopes(
    results: &[MachineTheoremSearchResult],
) -> Vec<AiSearchCandidateEnvelope> {
    let mut out = Vec::new();
    let mut source_index = 0u32;
    for result in results {
        let premise_usage = ai_search_premise_usage(result);
        for suggested in &result.suggested_candidates {
            let candidate = suggested.candidate.clone();
            let metadata = ai_search_candidate_metadata(
                AiSearchCandidateSource::MachineApiSuggested,
                None,
                source_index,
                vec![premise_usage.clone()],
                result.axioms_used.clone(),
                &candidate,
            );
            let envelope = ai_search_candidate_envelope(candidate, None, metadata);
            out.push(envelope);
            source_index = source_index
                .checked_add(1)
                .expect("ai_search suggested candidate source_index fits in u32");
        }
    }
    out
}

pub fn ai_search_builtin_candidate_envelopes(
    goal: &MachineGoalView,
) -> Vec<AiSearchCandidateEnvelope> {
    let mut out = Vec::new();

    if let Some(candidate) = ai_search_builtin_intro_candidate(goal) {
        push_ai_search_builtin_candidate(&mut out, AiSearchBuiltinKind::Intro, 0, candidate);
    }

    let mut local_exact_index = 0u32;
    for local in &goal.context {
        if ai_search_local_exact_prefilter(goal, local) {
            push_ai_search_builtin_candidate(
                &mut out,
                AiSearchBuiltinKind::LocalExact,
                local_exact_index,
                MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new(local.machine_name.clone()),
                },
            );
            local_exact_index = local_exact_index
                .checked_add(1)
                .expect("ai_search local exact source_index fits in u32");
        }
    }

    let mut induction_index = 0u32;
    for (index, local) in goal.context.iter().enumerate() {
        if ai_search_induction_nat_prefilter(goal, index, local) {
            push_ai_search_builtin_candidate(
                &mut out,
                AiSearchBuiltinKind::InductionNat,
                induction_index,
                MachineTacticCandidate::InductionNat {
                    local_name: local.machine_name.clone(),
                },
            );
            induction_index = induction_index
                .checked_add(1)
                .expect("ai_search induction source_index fits in u32");
        }
    }

    if ai_search_goal_allows_tactic(goal, MachineApiTacticKind::SimpLite) {
        push_ai_search_builtin_candidate(
            &mut out,
            AiSearchBuiltinKind::SimpLiteEmpty,
            0,
            MachineTacticCandidate::SimpLite { rules: Vec::new() },
        );
    }

    out
}

pub fn ai_search_rank_filter_and_dedupe_candidate_envelopes(
    mut candidates: Vec<AiSearchCandidateEnvelope>,
) -> AiSearchCandidateFilterResult {
    candidates.sort_by(ai_search_candidate_envelope_order);
    let mut filtered = filter_ai_search_candidate_envelopes(candidates);
    filtered.accepted = ai_search_dedupe_candidate_envelopes(filtered.accepted);
    filtered
}

pub fn ai_search_rank_and_dedupe_candidate_envelopes(
    mut candidates: Vec<AiSearchCandidateEnvelope>,
) -> Vec<AiSearchCandidateEnvelope> {
    candidates.sort_by(ai_search_candidate_envelope_order);
    ai_search_dedupe_candidate_envelopes(candidates)
}

fn ai_search_dedupe_candidate_envelopes(
    candidates: Vec<AiSearchCandidateEnvelope>,
) -> Vec<AiSearchCandidateEnvelope> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for candidate in candidates {
        if seen.insert(candidate.ai_search_candidate_payload_hash) {
            out.push(candidate);
        }
    }
    out
}

pub fn filter_ai_search_candidate_envelopes(
    candidates: Vec<AiSearchCandidateEnvelope>,
) -> AiSearchCandidateFilterResult {
    let mut accepted = Vec::new();
    let mut rejected = Vec::new();
    let mut errors = Vec::new();
    for mut envelope in candidates {
        match ai_search_candidate_forbidden_token(&envelope.candidate) {
            Ok(Some(forbidden_token)) => {
                envelope.metadata.trust_flags.contains_forbidden_tokens = true;
                envelope.metadata.trust_flags.forbidden_token_class = Some(forbidden_token.class);
                rejected.push(AiSearchRejectedCandidateEnvelope {
                    envelope,
                    forbidden_token,
                });
            }
            Ok(None) => accepted.push(envelope),
            Err(error) => errors.push(error),
        }
    }
    AiSearchCandidateFilterResult {
        accepted,
        rejected,
        errors,
    }
}

pub fn ai_search_candidate_envelope(
    candidate: MachineTacticCandidate,
    candidate_hash: Option<Hash>,
    metadata: AiSearchCandidateMetadata,
) -> AiSearchCandidateEnvelope {
    AiSearchCandidateEnvelope {
        ai_search_candidate_payload_hash: ai_search_candidate_payload_hash(&candidate),
        candidate,
        candidate_hash,
        metadata,
    }
}

pub fn ai_search_candidate_payload_hash(candidate: &MachineTacticCandidate) -> Hash {
    let payload = ai_search_candidate_payload_json(candidate);
    let mut bytes = Vec::new();
    bytes.extend_from_slice(AI_SEARCH_CANDIDATE_PAYLOAD_HASH_TAG.as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(payload.as_bytes());
    sha256(&bytes)
}

pub fn ai_search_candidate_payload_json(candidate: &MachineTacticCandidate) -> String {
    match candidate {
        MachineTacticCandidate::Exact { term } => {
            format!(
                r#"{{"kind":"exact","term":{}}}"#,
                ai_search_raw_machine_term_json(term)
            )
        }
        MachineTacticCandidate::Intro { name } => {
            format!(r#"{{"kind":"intro","name":{}}}"#, json_string(name))
        }
        MachineTacticCandidate::Apply {
            head,
            universe_args,
            args,
        } => format!(
            r#"{{"args":{},"head":{},"kind":"apply","universe_args":{}}}"#,
            ai_search_apply_arg_array_json(args),
            ai_search_tactic_head_json(head),
            ai_search_level_array_json(universe_args),
        ),
        MachineTacticCandidate::Rewrite {
            rule,
            direction,
            site,
        } => format!(
            r#"{{"direction":{},"kind":"rw","rule":{},"site":{}}}"#,
            json_string(ai_search_rewrite_direction_wire(*direction)),
            ai_search_rewrite_rule_json(rule),
            json_string(ai_search_rewrite_site_wire(*site)),
        ),
        MachineTacticCandidate::SimpLite { rules } => {
            format!(
                r#"{{"kind":"simp-lite","rules":{}}}"#,
                ai_search_simp_rule_array_json(rules)
            )
        }
        MachineTacticCandidate::Smt { lemmas } => {
            format!(
                r#"{{"kind":"smt","lemmas":{}}}"#,
                ai_search_smt_lemma_array_json(lemmas)
            )
        }
        MachineTacticCandidate::InductionNat { local_name } => format!(
            r#"{{"kind":"induction-nat","local_name":{}}}"#,
            json_string(local_name)
        ),
        MachineTacticCandidate::Constructor(payload) => format!(
            r#"{{"kind":"constructor","max_new_goals":{},"selection":{}}}"#,
            ai_search_optional_u64_json(payload.max_new_goals),
            ai_search_constructor_selection_json(&payload.selection),
        ),
        MachineTacticCandidate::Cases(payload) => ai_search_cases_payload_json(payload),
        MachineTacticCandidate::GeneralInduction(payload) => {
            ai_search_general_induction_payload_json(payload)
        }
        MachineTacticCandidate::Refine(payload) => ai_search_refine_payload_json(payload),
        MachineTacticCandidate::Have(payload) => ai_search_have_payload_json(payload),
        MachineTacticCandidate::Suffices(payload) => ai_search_suffices_payload_json(payload),
        MachineTacticCandidate::Specialize(payload) => ai_search_specialize_payload_json(payload),
        MachineTacticCandidate::Revert(payload) => ai_search_revert_payload_json(payload),
        MachineTacticCandidate::Generalize(payload) => ai_search_generalize_payload_json(payload),
        MachineTacticCandidate::Change(payload) => ai_search_change_payload_json(payload),
        MachineTacticCandidate::Unfold(payload) => ai_search_unfold_payload_json(payload),
        MachineTacticCandidate::Congr(payload) => ai_search_congr_payload_json(payload),
        MachineTacticCandidate::Subst(payload) => ai_search_subst_payload_json(payload),
        MachineTacticCandidate::Contradiction(payload) => {
            ai_search_contradiction_payload_json(payload)
        }
        MachineTacticCandidate::FiniteDecide => r#"{"kind":"finite-decide"}"#.to_owned(),
        MachineTacticCandidate::Omega => r#"{"kind":"omega"}"#.to_owned(),
        MachineTacticCandidate::Ring => r#"{"kind":"ring"}"#.to_owned(),
        MachineTacticCandidate::Bitblast => r#"{"kind":"bitblast"}"#.to_owned(),
    }
}

fn ai_search_constructor_selection_json(selection: &ConstructorSelection) -> String {
    match selection {
        ConstructorSelection::Auto => r#"{"mode":"auto"}"#.to_owned(),
        ConstructorSelection::Explicit { constructor } => format!(
            r#"{{"constructor":{},"mode":"explicit"}}"#,
            ai_search_tactic_head_json(constructor)
        ),
    }
}

fn ai_search_cases_payload_json(payload: &CasesPayload<RawMachineTerm>) -> String {
    format!(
        r#"{{"branch_names":{},"kind":"cases","major_local":{},"max_new_goals":{},"motive":{}}}"#,
        ai_search_string_array_json(&payload.branch_names),
        json_string(&payload.major_local),
        ai_search_optional_u64_json(payload.max_new_goals),
        ai_search_optional_raw_machine_term_json(payload.motive.as_ref()),
    )
}

fn ai_search_general_induction_payload_json(
    payload: &GeneralInductionPayload<RawMachineTerm>,
) -> String {
    format!(
        r#"{{"branch_names":{},"generalized_locals":{},"kind":"general-induction","major_local":{},"max_new_goals":{},"motive":{},"recursor":{}}}"#,
        ai_search_string_array_json(&payload.branch_names),
        ai_search_string_array_json(&payload.generalized_locals),
        json_string(&payload.major_local),
        payload.max_new_goals,
        ai_search_optional_raw_machine_term_json(payload.motive.as_ref()),
        ai_search_tactic_head_json(&payload.recursor),
    )
}

fn ai_search_refine_payload_json(payload: &RefinePayload<RawMachineTerm>) -> String {
    format!(
        r#"{{"kind":"refine","max_holes":{},"term":{}}}"#,
        ai_search_optional_u64_json(payload.max_holes),
        ai_search_raw_machine_term_json(&payload.term),
    )
}

fn ai_search_have_payload_json(payload: &HavePayload<RawMachineTerm>) -> String {
    format!(
        r#"{{"insertion":{},"kind":"have","name":{},"proof":{},"type":{}}}"#,
        json_string(ai_search_local_lemma_insertion_policy_wire(
            payload.insertion
        )),
        json_string(&payload.name),
        ai_search_local_lemma_proof_json(&payload.proof),
        ai_search_raw_machine_term_json(&payload.ty),
    )
}

fn ai_search_suffices_payload_json(payload: &SufficesPayload<RawMachineTerm>) -> String {
    format!(
        r#"{{"continuation":{},"kind":"suffices","proof":{},"target":{}}}"#,
        json_string(ai_search_suffices_continuation_policy_wire(
            payload.continuation
        )),
        ai_search_local_lemma_proof_json(&payload.proof),
        ai_search_raw_machine_term_json(&payload.target),
    )
}

fn ai_search_local_lemma_proof_json(proof: &LocalLemmaProof<RawMachineTerm>) -> String {
    match proof {
        LocalLemmaProof::ChildGoal => r#"{"mode":"child-goal"}"#.to_owned(),
        LocalLemmaProof::Term(term) => format!(
            r#"{{"mode":"term","term":{}}}"#,
            ai_search_raw_machine_term_json(term)
        ),
    }
}

fn ai_search_specialize_payload_json(payload: &SpecializePayload<CandidateApplyArg>) -> String {
    let result_name = payload
        .result_name
        .as_ref()
        .map(|name| json_string(name))
        .unwrap_or_else(|| "null".to_owned());
    format!(
        r#"{{"args":{},"kind":"specialize","local_name":{},"result_name":{},"result_policy":{},"universe_args":{}}}"#,
        ai_search_apply_arg_array_json(&payload.args),
        json_string(&payload.local_name),
        result_name,
        json_string(ai_search_specialize_result_policy_wire(
            payload.result_policy
        )),
        ai_search_level_array_json(&payload.universe_args),
    )
}

fn ai_search_revert_payload_json(payload: &RevertPayload) -> String {
    format!(
        r#"{{"dependency_policy":{},"kind":"revert","locals":{}}}"#,
        json_string(ai_search_revert_dependency_policy_wire(
            payload.dependency_policy
        )),
        ai_search_string_array_json(&payload.locals),
    )
}

fn ai_search_generalize_payload_json(payload: &GeneralizePayload<RawMachineTerm>) -> String {
    let name_hint = payload
        .name_hint
        .as_ref()
        .map(|name| json_string(name))
        .unwrap_or_else(|| "null".to_owned());
    format!(
        r#"{{"kind":"generalize","name_hint":{},"occurrences":{},"target":{},"term":{}}}"#,
        name_hint,
        ai_search_occurrence_paths_json(&payload.occurrences),
        ai_search_tactic_target_json(&payload.target),
        ai_search_raw_machine_term_json(&payload.term),
    )
}

fn ai_search_change_payload_json(payload: &ChangePayload<RawMachineTerm>) -> String {
    format!(
        r#"{{"kind":"change","occurrences":{},"replacement":{},"target":{}}}"#,
        ai_search_occurrence_paths_json(&payload.occurrences),
        ai_search_raw_machine_term_json(&payload.replacement),
        ai_search_tactic_target_json(&payload.target),
    )
}

fn ai_search_unfold_payload_json(payload: &UnfoldPayload) -> String {
    format!(
        r#"{{"constant":{},"kind":"unfold","max_delta_steps":{},"occurrences":{},"target":{}}}"#,
        ai_search_tactic_head_json(&payload.constant),
        ai_search_optional_u64_json(payload.max_delta_steps),
        ai_search_occurrence_paths_json(&payload.occurrences),
        ai_search_tactic_target_json(&payload.target),
    )
}

fn ai_search_congr_payload_json(payload: &CongrPayload) -> String {
    format!(
        r#"{{"kind":"congr","max_depth":{},"max_new_goals":{},"target":{}}}"#,
        ai_search_optional_u64_json(payload.max_depth),
        ai_search_optional_u64_json(payload.max_new_goals),
        ai_search_tactic_target_json(&payload.target),
    )
}

fn ai_search_subst_payload_json(payload: &SubstPayload) -> String {
    format!(
        r#"{{"direction":{},"equality_local":{},"kind":"subst","occurrences":{},"target":{}}}"#,
        json_string(ai_search_rewrite_direction_wire(payload.direction)),
        json_string(&payload.equality_local),
        ai_search_occurrence_paths_json(&payload.occurrences),
        ai_search_tactic_target_json(&payload.target),
    )
}

fn ai_search_contradiction_payload_json(payload: &ContradictionPayload) -> String {
    match &payload.mode {
        ContradictionMode::Auto => {
            r#"{"kind":"contradiction","major_local":null,"mode":"auto"}"#.to_owned()
        }
        ContradictionMode::Local { major_local } => format!(
            r#"{{"kind":"contradiction","major_local":{},"mode":"local"}}"#,
            json_string(major_local)
        ),
    }
}

fn ai_search_tactic_target_json(target: &TacticTarget) -> String {
    match target {
        TacticTarget::Goal => r#"{"mode":"goal"}"#.to_owned(),
        TacticTarget::Local { name } => {
            format!(r#"{{"mode":"local","name":{}}}"#, json_string(name))
        }
    }
}

fn ai_search_occurrence_paths_json(paths: &[OccurrencePath]) -> String {
    let members = paths
        .iter()
        .map(|path| {
            let indices = path.indices.iter().map(u64::to_string).collect::<Vec<_>>();
            format!(r#"{{"indices":[{}]}}"#, indices.join(","))
        })
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_optional_raw_machine_term_json(term: Option<&RawMachineTerm>) -> String {
    term.map(ai_search_raw_machine_term_json)
        .unwrap_or_else(|| "null".to_owned())
}

fn ai_search_optional_u64_json(value: Option<u64>) -> String {
    value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "null".to_owned())
}

fn ai_search_local_lemma_insertion_policy_wire(policy: LocalLemmaInsertionPolicy) -> &'static str {
    match policy {
        LocalLemmaInsertionPolicy::AfterCurrent => "after-current",
        LocalLemmaInsertionPolicy::End => "end",
    }
}

fn ai_search_suffices_continuation_policy_wire(policy: SufficesContinuationPolicy) -> &'static str {
    match policy {
        SufficesContinuationPolicy::ProveIntermediateFirst => "prove-intermediate-first",
        SufficesContinuationPolicy::ProveContinuationFirst => "prove-continuation-first",
    }
}

fn ai_search_specialize_result_policy_wire(policy: SpecializeResultPolicy) -> &'static str {
    match policy {
        SpecializeResultPolicy::AddLocal => "add-local",
        SpecializeResultPolicy::ReplaceOriginal => "replace-original",
    }
}

fn ai_search_revert_dependency_policy_wire(policy: RevertDependencyPolicy) -> &'static str {
    match policy {
        RevertDependencyPolicy::Exact => "exact",
        RevertDependencyPolicy::Closure => "closure",
    }
}

fn ai_search_training_trace_candidates_json(
    candidates: &[AiSearchTrainingTraceCandidate],
) -> String {
    let members = candidates
        .iter()
        .map(ai_search_training_trace_candidate_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_training_trace_candidate_json(candidate: &AiSearchTrainingTraceCandidate) -> String {
    match candidate {
        AiSearchTrainingTraceCandidate::Success {
            rank_index,
            ai_search_candidate_payload_hash,
            candidate,
            candidate_hash,
            deterministic_budget_hash,
            proof_delta_hash,
            next_snapshot_id,
            next_state_fingerprint,
        } => format!(
            r#"{{"rank_index":{},"ai_search_candidate_payload_hash":{},"candidate":{},"candidate_hash":{},"result":"success","deterministic_budget_hash":{},"proof_delta_hash":{},"next_snapshot_id":{},"next_state_fingerprint":{}{}}}"#,
            rank_index,
            json_string(&format_hash_string(ai_search_candidate_payload_hash)),
            ai_search_candidate_payload_json(candidate),
            json_string(&format_hash_string(candidate_hash)),
            json_string(&format_hash_string(deterministic_budget_hash)),
            json_string(&format_hash_string(proof_delta_hash)),
            json_string(&next_snapshot_id.wire()),
            json_string(&format_hash_string(next_state_fingerprint)),
            ai_search_solver_trace_fields(candidate),
        ),
        AiSearchTrainingTraceCandidate::Error {
            rank_index,
            ai_search_candidate_payload_hash,
            candidate,
            candidate_hash,
            error_kind,
            phase,
            deterministic_budget_hash,
            diagnostic_hash,
            retryable,
            goal_id,
            tactic_kind,
        } => {
            let mut source = format!(
                r#"{{"rank_index":{},"ai_search_candidate_payload_hash":{},"candidate":{},"candidate_hash":{},"result":"error","error_kind":{},"phase":{},"deterministic_budget_hash":{},"diagnostic_hash":{},"retryable":{}"#,
                rank_index,
                json_string(&format_hash_string(ai_search_candidate_payload_hash)),
                ai_search_candidate_payload_json(candidate),
                json_string(&format_hash_string(candidate_hash)),
                json_string(error_kind.as_str()),
                json_string(phase.as_str()),
                json_string(&format_hash_string(deterministic_budget_hash)),
                json_string(&format_hash_string(diagnostic_hash)),
                bool_json(*retryable),
            );
            source.push_str(&ai_search_solver_trace_fields(candidate));
            if let Some(goal_id) = goal_id {
                source.push_str(r#","goal_id":"#);
                source.push_str(&json_string(&format_goal_id_wire(*goal_id)));
            }
            if let Some(tactic_kind) = tactic_kind {
                source.push_str(r#","tactic_kind":"#);
                source.push_str(&json_string(tactic_kind.as_str()));
            }
            source.push('}');
            source
        }
    }
}

fn ai_search_solver_trace_fields(candidate: &MachineTacticCandidate) -> String {
    match ai_search_solver_family(candidate) {
        Some(family) => format!(
            r#","solver_family":{},"solver_contract_version":{}"#,
            json_string(family.as_str()),
            json_string(SOLVER_CONTRACT_VERSION),
        ),
        None => String::new(),
    }
}

fn ai_search_solver_family(candidate: &MachineTacticCandidate) -> Option<SolverFamily> {
    match candidate {
        MachineTacticCandidate::Smt { .. } => Some(SolverFamily::Smt),
        MachineTacticCandidate::FiniteDecide => Some(SolverFamily::FiniteDecide),
        MachineTacticCandidate::Omega => Some(SolverFamily::Omega),
        MachineTacticCandidate::Ring => Some(SolverFamily::Ring),
        MachineTacticCandidate::Bitblast => Some(SolverFamily::Bitblast),
        _ => None,
    }
}

pub fn ai_search_candidate_forbidden_token(
    candidate: &MachineTacticCandidate,
) -> Result<Option<AiSearchForbiddenToken>, AiSearchCandidateFilterError> {
    let mut best_token = None;
    for (raw_term_index, term) in ai_search_candidate_raw_terms(candidate)
        .into_iter()
        .enumerate()
    {
        if let Some(token) = ai_search_raw_term_forbidden_token(usize_to_u32(raw_term_index), term)?
        {
            if ai_search_forbidden_token_is_better(best_token.as_ref(), &token) {
                best_token = Some(token);
            }
        }
    }
    Ok(best_token)
}

pub fn ai_search_expected_effect(candidate: &MachineTacticCandidate) -> AiSearchExpectedEffect {
    match candidate {
        MachineTacticCandidate::Intro { .. } => AiSearchExpectedEffect::IntroBinder,
        MachineTacticCandidate::Exact { .. } => AiSearchExpectedEffect::CloseGoal,
        MachineTacticCandidate::Rewrite { .. } => AiSearchExpectedEffect::Rewrite,
        MachineTacticCandidate::SimpLite { .. } => AiSearchExpectedEffect::Simplify,
        MachineTacticCandidate::Smt { .. }
        | MachineTacticCandidate::FiniteDecide
        | MachineTacticCandidate::Omega
        | MachineTacticCandidate::Ring
        | MachineTacticCandidate::Bitblast => AiSearchExpectedEffect::CloseGoal,
        MachineTacticCandidate::InductionNat { .. } => AiSearchExpectedEffect::InductionSplit,
        MachineTacticCandidate::Apply { .. }
        | MachineTacticCandidate::Constructor(_)
        | MachineTacticCandidate::Cases(_)
        | MachineTacticCandidate::GeneralInduction(_)
        | MachineTacticCandidate::Refine(_)
        | MachineTacticCandidate::Have(_)
        | MachineTacticCandidate::Suffices(_)
        | MachineTacticCandidate::Specialize(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Generalize(_)
        | MachineTacticCandidate::Change(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Contradiction(_) => AiSearchExpectedEffect::Unknown,
    }
}

pub fn ai_search_candidate_cost_estimate(
    candidate: &MachineTacticCandidate,
) -> AiSearchCandidateCostEstimate {
    match candidate {
        MachineTacticCandidate::Intro { .. } | MachineTacticCandidate::Exact { .. } => {
            AiSearchCandidateCostEstimate {
                estimated_timeout_ms: 100,
                risk: AiSearchCandidateCostRisk::Low,
            }
        }
        MachineTacticCandidate::Rewrite { .. } => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 200,
            risk: AiSearchCandidateCostRisk::Medium,
        },
        MachineTacticCandidate::SimpLite { rules } if rules.is_empty() => {
            AiSearchCandidateCostEstimate {
                estimated_timeout_ms: 100,
                risk: AiSearchCandidateCostRisk::Low,
            }
        }
        MachineTacticCandidate::SimpLite { .. } => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 200,
            risk: AiSearchCandidateCostRisk::Medium,
        },
        MachineTacticCandidate::Smt { .. } => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 500,
            risk: AiSearchCandidateCostRisk::High,
        },
        MachineTacticCandidate::FiniteDecide => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 100,
            risk: AiSearchCandidateCostRisk::Low,
        },
        MachineTacticCandidate::Omega | MachineTacticCandidate::Ring => {
            AiSearchCandidateCostEstimate {
                estimated_timeout_ms: 250,
                risk: AiSearchCandidateCostRisk::Medium,
            }
        }
        MachineTacticCandidate::Bitblast => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 400,
            risk: AiSearchCandidateCostRisk::High,
        },
        MachineTacticCandidate::InductionNat { .. } => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 500,
            risk: AiSearchCandidateCostRisk::Medium,
        },
        MachineTacticCandidate::Apply { .. } => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 500,
            risk: AiSearchCandidateCostRisk::High,
        },
        MachineTacticCandidate::Constructor(_)
        | MachineTacticCandidate::Cases(_)
        | MachineTacticCandidate::GeneralInduction(_)
        | MachineTacticCandidate::Refine(_)
        | MachineTacticCandidate::Have(_)
        | MachineTacticCandidate::Suffices(_)
        | MachineTacticCandidate::Specialize(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Generalize(_)
        | MachineTacticCandidate::Change(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Contradiction(_) => AiSearchCandidateCostEstimate {
            estimated_timeout_ms: 500,
            risk: AiSearchCandidateCostRisk::High,
        },
    }
}

pub fn ai_search_fresh_intro_name(
    goal: &MachineGoalView,
    outer_binder_name: Option<&str>,
) -> Option<String> {
    let forbidden = goal
        .context
        .iter()
        .map(|local| local.machine_name.as_str())
        .collect::<BTreeSet<_>>();
    let mut bases = Vec::new();
    if let Some(name) = outer_binder_name {
        if is_machine_local_name(name) {
            bases.push(name.to_owned());
        }
    }
    bases.extend(["x".to_owned(), "h".to_owned(), "n".to_owned()]);

    for base in bases {
        let suffix_limit = forbidden.len().saturating_add(1);
        for suffix in 0..=suffix_limit {
            let candidate = if suffix == 0 {
                base.clone()
            } else {
                format!("{base}{suffix}")
            };
            if !is_machine_local_name(&candidate) {
                if suffix > 0 {
                    break;
                }
                continue;
            }
            if !forbidden.contains(candidate.as_str()) {
                return Some(candidate);
            }
        }
    }
    None
}

fn ai_search_goal_summary(goal: &MachineGoalView, open_goal_index: usize) -> AiSearchGoalSummary {
    AiSearchGoalSummary {
        goal_id: goal.goal_id,
        open_goal_index: usize_to_u32(open_goal_index),
        goal_fingerprint: goal.goal_fingerprint,
        target_hash: goal.target_hash,
        target_head: goal.target.head.clone(),
        target_free_local_count: usize_to_u32(goal.target.free_locals.len()),
        context_size: usize_to_u32(goal.context.len()),
        expr_size: goal.target.size,
    }
}

fn ai_search_goal_summary_json(goal: &AiSearchGoalSummary) -> String {
    format!(
        r#"{{"goal_id":{},"open_goal_index":{},"goal_fingerprint":{},"target_hash":{},"target_head":{},"target_free_local_count":{},"context_size":{},"expr_size":{}}}"#,
        json_string(&format_goal_id_wire(goal.goal_id)),
        goal.open_goal_index,
        json_string(&format_hash_string(&goal.goal_fingerprint)),
        json_string(&format_hash_string(&goal.target_hash)),
        ai_search_optional_global_ref_view_json(goal.target_head.as_ref()),
        goal.target_free_local_count,
        goal.context_size,
        goal.expr_size,
    )
}

fn ai_search_premise_cache_entries_json(entries: &[AiSearchPremiseCacheEntry]) -> String {
    let members = entries
        .iter()
        .map(ai_search_premise_cache_entry_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_premise_cache_entry_json(entry: &AiSearchPremiseCacheEntry) -> String {
    format!(
        r#"{{"premise_ref":{},"universe_params":{},"statement_core_hash":{},"statement_head":{},"axioms_used":{},"modes":{},"response_index":{}}}"#,
        ai_search_premise_ref_json(&entry.premise_ref),
        ai_search_string_array_json(&entry.universe_params),
        json_string(&format_hash_string(&entry.statement_core_hash)),
        ai_search_optional_global_ref_view_json(entry.statement_head.as_ref()),
        ai_search_axiom_refs_json(&entry.axioms_used),
        ai_search_theorem_modes_json(&entry.modes),
        entry.response_index,
    )
}

fn ai_search_premise_ref_json(premise_ref: &AiSearchPremiseRef) -> String {
    format!(
        r#"{{"module":{},"name":{},"export_hash":{},"decl_interface_hash":{}}}"#,
        json_string(&premise_ref.module.as_dotted()),
        json_string(&premise_ref.name.as_dotted()),
        json_string(&format_hash_string(&premise_ref.export_hash)),
        json_string(&format_hash_string(&premise_ref.decl_interface_hash)),
    )
}

fn ai_search_goal_selection_order(
    left: &AiSearchGoalSummary,
    right: &AiSearchGoalSummary,
) -> Ordering {
    left.expr_size
        .cmp(&right.expr_size)
        .then_with(|| left.context_size.cmp(&right.context_size))
        .then_with(|| {
            left.target_free_local_count
                .cmp(&right.target_free_local_count)
        })
        .then_with(|| left.open_goal_index.cmp(&right.open_goal_index))
        .then_with(|| {
            goal_id_canonical_bytes(left.goal_id).cmp(&goal_id_canonical_bytes(right.goal_id))
        })
}

fn ai_search_premise_cache_entry(
    result: &MachineTheoremSearchResult,
    response_index: usize,
) -> AiSearchPremiseCacheEntry {
    AiSearchPremiseCacheEntry {
        premise_ref: ai_search_premise_ref(result),
        universe_params: result.universe_params.clone(),
        statement_core_hash: result.statement.core_hash,
        statement_head: result.statement.head.clone(),
        axioms_used: result.axioms_used.clone(),
        modes: result.modes.clone(),
        response_index: usize_to_u32(response_index),
    }
}

fn ai_search_premise_usage(result: &MachineTheoremSearchResult) -> AiSearchPremiseUsage {
    AiSearchPremiseUsage {
        premise_ref: ai_search_premise_ref(result),
        universe_params: result.universe_params.clone(),
        statement_core_hash: result.statement.core_hash,
        axioms_used: result.axioms_used.clone(),
    }
}

fn ai_search_premise_ref(result: &MachineTheoremSearchResult) -> AiSearchPremiseRef {
    AiSearchPremiseRef {
        module: result.global_ref.module.clone(),
        name: result.global_ref.name.clone(),
        export_hash: result.global_ref.export_hash,
        decl_interface_hash: result.global_ref.decl_interface_hash,
    }
}

fn ai_search_premise_graph_ranking_entry(
    entry: &AiSearchPremiseCacheEntry,
    graph_snapshot: Option<&CertificateTheoremGraphSnapshot>,
) -> AiSearchPremiseGraphRankingEntry {
    let graph_node = graph_snapshot
        .and_then(|snapshot| ai_search_premise_graph_node(snapshot, &entry.premise_ref));
    let graph_edges = graph_snapshot
        .zip(graph_node)
        .map(|(snapshot, node)| ai_search_premise_graph_edge_metadata(snapshot, node))
        .unwrap_or_default();
    let graph_score_components = ai_search_premise_graph_score_components(&graph_edges);
    let graph_score = graph_score_components.score();
    let graph_source = if graph_score > 0 {
        AiSearchPremiseGraphRankingSource::VerifiedIndexAndGraphEdgeExpansion
    } else {
        AiSearchPremiseGraphRankingSource::VerifiedIndexMatch
    };
    AiSearchPremiseGraphRankingEntry {
        premise_ref: entry.premise_ref.clone(),
        response_index: entry.response_index,
        graph_rank: entry.response_index,
        graph_node: graph_node.map(|node| node.id.clone()),
        direct_dependency_count: graph_score_components.direct_dependency_count,
        graph_source,
        graph_score_components,
        graph_edges,
        graph_score,
    }
}

fn ai_search_premise_graph_node<'a>(
    snapshot: &'a CertificateTheoremGraphSnapshot,
    premise_ref: &AiSearchPremiseRef,
) -> Option<&'a CertificateTheoremGraphNode> {
    snapshot
        .nodes
        .iter()
        .filter(|node| certificate_theorem_graph_node_is_certificate_bound_public_export(node))
        .find(|node| ai_search_premise_matches_graph_node(snapshot, premise_ref, node))
}

fn ai_search_premise_matches_graph_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    premise_ref: &AiSearchPremiseRef,
    node: &CertificateTheoremGraphNode,
) -> bool {
    if node.id.module != premise_ref.module
        || node.id.name != premise_ref.name
        || node.id.decl_interface_hash != premise_ref.decl_interface_hash
    {
        return false;
    }
    match &node.id.scope {
        CertificateTheoremGraphNodeScope::Imported {
            import_export_hash, ..
        } => *import_export_hash == premise_ref.export_hash,
        CertificateTheoremGraphNodeScope::Local
        | CertificateTheoremGraphNodeScope::LocalGenerated { .. } => {
            snapshot.source_export_hash == premise_ref.export_hash
        }
        CertificateTheoremGraphNodeScope::Builtin => false,
    }
}

fn ai_search_premise_graph_score_components(
    edges: &AiSearchPremiseGraphEdgeMetadata,
) -> AiSearchPremiseGraphScoreComponents {
    AiSearchPremiseGraphScoreComponents {
        direct_dependency_count: usize_to_u32(edges.direct_dependencies.len()),
        transitive_dependency_count: usize_to_u32(edges.transitive_dependencies.len()),
        used_by_count: usize_to_u32(edges.used_by.len()),
        similar_statement_count: usize_to_u32(edges.similar_statements.len()),
        direct_axiom_path_count: usize_to_u32(edges.direct_axiom_paths.len()),
        transitive_axiom_path_count: usize_to_u32(edges.transitive_axiom_paths.len()),
    }
}

fn ai_search_premise_graph_edge_metadata(
    snapshot: &CertificateTheoremGraphSnapshot,
    node: &CertificateTheoremGraphNode,
) -> AiSearchPremiseGraphEdgeMetadata {
    AiSearchPremiseGraphEdgeMetadata {
        direct_dependencies: ai_search_premise_graph_direct_dependency_targets(snapshot, node),
        transitive_dependencies: ai_search_premise_graph_transitive_dependency_targets(
            snapshot, node,
        ),
        used_by: ai_search_premise_graph_edge_targets(snapshot, &node.id, |kind| {
            kind == CertificateTheoremGraphEdgeKind::UsedBy
        }),
        similar_statements: ai_search_premise_graph_edge_targets(snapshot, &node.id, |kind| {
            kind == CertificateTheoremGraphEdgeKind::SimilarStatement
        }),
        direct_axiom_paths: ai_search_premise_graph_edge_targets(snapshot, &node.id, |kind| {
            kind == CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom
        }),
        transitive_axiom_paths: ai_search_premise_graph_edge_targets(snapshot, &node.id, |kind| {
            matches!(
                kind,
                CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom
                    | CertificateTheoremGraphEdgeKind::AxiomPath
            )
        }),
    }
}

fn ai_search_premise_graph_direct_dependency_targets(
    snapshot: &CertificateTheoremGraphSnapshot,
    node: &CertificateTheoremGraphNode,
) -> Vec<CertificateTheoremGraphNodeId> {
    ai_search_premise_graph_edge_targets(snapshot, &node.id, |kind| {
        matches!(
            kind,
            CertificateTheoremGraphEdgeKind::ImportsDeclaration
                | CertificateTheoremGraphEdgeKind::MentionsType
                | CertificateTheoremGraphEdgeKind::UsesConstant
                | CertificateTheoremGraphEdgeKind::GeneratedDeclaration
        )
    })
}

fn ai_search_premise_graph_transitive_dependency_targets(
    snapshot: &CertificateTheoremGraphSnapshot,
    node: &CertificateTheoremGraphNode,
) -> Vec<CertificateTheoremGraphNodeId> {
    let mut dependencies = BTreeSet::new();
    let mut visited = BTreeSet::from([node.id.clone()]);
    let mut queue = VecDeque::from([node.id.clone()]);
    while let Some(current) = queue.pop_front() {
        for target in ai_search_premise_graph_edge_targets(snapshot, &current, |kind| {
            matches!(
                kind,
                CertificateTheoremGraphEdgeKind::ImportsDeclaration
                    | CertificateTheoremGraphEdgeKind::MentionsType
                    | CertificateTheoremGraphEdgeKind::UsesConstant
                    | CertificateTheoremGraphEdgeKind::GeneratedDeclaration
            )
        }) {
            if target == node.id {
                continue;
            }
            if dependencies.insert(target.clone()) && visited.insert(target.clone()) {
                queue.push_back(target);
            }
        }
    }
    dependencies.into_iter().collect()
}

fn ai_search_premise_graph_edge_targets(
    snapshot: &CertificateTheoremGraphSnapshot,
    source: &CertificateTheoremGraphNodeId,
    include: impl Fn(CertificateTheoremGraphEdgeKind) -> bool,
) -> Vec<CertificateTheoremGraphNodeId> {
    let mut targets = BTreeSet::new();
    for edge in &snapshot.edges {
        if edge.from == *source
            && include(edge.kind)
            && snapshot
                .node(&edge.to)
                .is_some_and(certificate_theorem_graph_node_is_certificate_bound_public_export)
        {
            targets.insert(edge.to.clone());
        }
    }
    targets.into_iter().collect()
}

fn ai_search_premise_graph_ranking_entry_order(
    left: &AiSearchPremiseGraphRankingEntry,
    right: &AiSearchPremiseGraphRankingEntry,
) -> Ordering {
    right
        .graph_score
        .cmp(&left.graph_score)
        .then_with(|| left.response_index.cmp(&right.response_index))
        .then_with(|| left.premise_ref.module.cmp(&right.premise_ref.module))
        .then_with(|| left.premise_ref.name.cmp(&right.premise_ref.name))
        .then_with(|| {
            left.premise_ref
                .decl_interface_hash
                .cmp(&right.premise_ref.decl_interface_hash)
        })
}

fn push_ai_search_builtin_candidate(
    out: &mut Vec<AiSearchCandidateEnvelope>,
    builtin_kind: AiSearchBuiltinKind,
    source_index: u32,
    candidate: MachineTacticCandidate,
) {
    let metadata = ai_search_candidate_metadata(
        AiSearchCandidateSource::Builtin,
        Some(builtin_kind),
        source_index,
        Vec::new(),
        Vec::new(),
        &candidate,
    );
    let envelope = ai_search_candidate_envelope(candidate, None, metadata);
    out.push(envelope);
}

fn ai_search_candidate_metadata(
    source: AiSearchCandidateSource,
    builtin_kind: Option<AiSearchBuiltinKind>,
    source_index: u32,
    premises_used: Vec<AiSearchPremiseUsage>,
    uses_axioms: Vec<MachineAxiomRefWire>,
    candidate: &MachineTacticCandidate,
) -> AiSearchCandidateMetadata {
    let cheap_first_stage =
        ai_search_candidate_cheap_first_stage(source, builtin_kind, &premises_used, candidate);
    AiSearchCandidateMetadata {
        source,
        rank: AiSearchCandidateRankMetadata {
            cheap_first_stage,
            stage_rank: ai_search_cheap_first_stage_rank(cheap_first_stage),
            skip_reason: ai_search_cheap_first_skip_reason(cheap_first_stage),
            source_rank: ai_search_candidate_source_rank(source),
            source_index,
            builtin_kind_rank: ai_search_builtin_kind_rank(builtin_kind),
        },
        score: 0,
        display_text: None,
        premises_used,
        expected_effect: ai_search_expected_effect(candidate),
        cost_estimate: ai_search_candidate_cost_estimate(candidate),
        trust_flags: AiSearchTrustFlags {
            uses_axioms,
            contains_forbidden_tokens: false,
            forbidden_token_class: None,
        },
        repair: None,
    }
}

pub fn ai_search_candidate_cheap_first_stage(
    source: AiSearchCandidateSource,
    builtin_kind: Option<AiSearchBuiltinKind>,
    premises_used: &[AiSearchPremiseUsage],
    candidate: &MachineTacticCandidate,
) -> AiSearchCheapFirstStage {
    match candidate {
        MachineTacticCandidate::Exact { .. } => {
            if matches!(builtin_kind, Some(AiSearchBuiltinKind::LocalExact)) {
                AiSearchCheapFirstStage::LocalExact
            } else if source == AiSearchCandidateSource::MachineApiSuggested
                || !premises_used.is_empty()
            {
                AiSearchCheapFirstStage::KnownExact
            } else {
                AiSearchCheapFirstStage::ExplicitTerm
            }
        }
        MachineTacticCandidate::Intro { .. }
        | MachineTacticCandidate::Change(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Contradiction(_) => {
            AiSearchCheapFirstStage::ReflexivityComputation
        }
        MachineTacticCandidate::Rewrite { .. } | MachineTacticCandidate::Subst(_) => {
            AiSearchCheapFirstStage::Rewrite
        }
        MachineTacticCandidate::SimpLite { .. } => AiSearchCheapFirstStage::SimpLite,
        MachineTacticCandidate::Apply { .. } | MachineTacticCandidate::Specialize(_) => {
            AiSearchCheapFirstStage::Apply
        }
        MachineTacticCandidate::Constructor(_) => AiSearchCheapFirstStage::Constructor,
        MachineTacticCandidate::Cases(_) => AiSearchCheapFirstStage::Cases,
        MachineTacticCandidate::InductionNat { .. }
        | MachineTacticCandidate::GeneralInduction(_) => AiSearchCheapFirstStage::Induction,
        MachineTacticCandidate::FiniteDecide => AiSearchCheapFirstStage::FiniteDecide,
        MachineTacticCandidate::Omega | MachineTacticCandidate::Ring => {
            AiSearchCheapFirstStage::RingOmega
        }
        MachineTacticCandidate::Bitblast => AiSearchCheapFirstStage::Bitblast,
        MachineTacticCandidate::Smt { .. } => AiSearchCheapFirstStage::Smt,
        MachineTacticCandidate::Refine(_) => AiSearchCheapFirstStage::ExplicitTerm,
        MachineTacticCandidate::Have(_) | MachineTacticCandidate::Suffices(_) => {
            AiSearchCheapFirstStage::LocalLemma
        }
        MachineTacticCandidate::Revert(_) | MachineTacticCandidate::Generalize(_) => {
            AiSearchCheapFirstStage::ReflexivityComputation
        }
    }
}

pub fn ai_search_cheap_first_stage_rank(stage: AiSearchCheapFirstStage) -> u8 {
    let rank = match stage {
        AiSearchCheapFirstStage::LocalExact => 0,
        AiSearchCheapFirstStage::KnownExact => 1,
        AiSearchCheapFirstStage::ReflexivityComputation => 2,
        AiSearchCheapFirstStage::FiniteDecide => 3,
        AiSearchCheapFirstStage::Rewrite => 4,
        AiSearchCheapFirstStage::SimpLite => 5,
        AiSearchCheapFirstStage::RingOmega => 6,
        AiSearchCheapFirstStage::Bitblast => 7,
        AiSearchCheapFirstStage::Smt => 8,
        AiSearchCheapFirstStage::Apply => 9,
        AiSearchCheapFirstStage::Constructor => 10,
        AiSearchCheapFirstStage::Cases => 11,
        AiSearchCheapFirstStage::Induction => 12,
        AiSearchCheapFirstStage::Solver => 13,
        AiSearchCheapFirstStage::ExplicitTerm => 14,
        AiSearchCheapFirstStage::LocalLemma => 15,
        AiSearchCheapFirstStage::NewLibraryTheorem => 16,
    };
    debug_assert_eq!(AI_SEARCH_CHEAP_FIRST_STAGE_ORDER[rank as usize], stage);
    rank
}

fn ai_search_candidate_within_stage_new_goal_budget(
    candidate: &AiSearchCandidateEnvelope,
    stage_budget: AiSearchCheapFirstStageBudget,
) -> bool {
    let Some(candidate_max_new_goals) =
        ai_search_candidate_payload_max_new_goals(&candidate.candidate)
    else {
        return true;
    };
    candidate_max_new_goals <= u64::from(stage_budget.max_new_goals)
}

fn ai_search_candidate_payload_max_new_goals(candidate: &MachineTacticCandidate) -> Option<u64> {
    match candidate {
        MachineTacticCandidate::Constructor(payload) => payload.max_new_goals,
        MachineTacticCandidate::Cases(payload) => payload.max_new_goals,
        MachineTacticCandidate::GeneralInduction(payload) => Some(payload.max_new_goals),
        MachineTacticCandidate::Congr(payload) => payload.max_new_goals,
        MachineTacticCandidate::Exact { .. }
        | MachineTacticCandidate::Intro { .. }
        | MachineTacticCandidate::Apply { .. }
        | MachineTacticCandidate::Rewrite { .. }
        | MachineTacticCandidate::SimpLite { .. }
        | MachineTacticCandidate::Smt { .. }
        | MachineTacticCandidate::InductionNat { .. }
        | MachineTacticCandidate::Change(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Contradiction(_)
        | MachineTacticCandidate::FiniteDecide
        | MachineTacticCandidate::Omega
        | MachineTacticCandidate::Ring
        | MachineTacticCandidate::Bitblast
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Specialize(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Generalize(_)
        | MachineTacticCandidate::Refine(_)
        | MachineTacticCandidate::Have(_)
        | MachineTacticCandidate::Suffices(_) => None,
    }
}

fn ai_search_candidate_source_rank(source: AiSearchCandidateSource) -> u8 {
    match source {
        AiSearchCandidateSource::MachineApiSuggested => 0,
        AiSearchCandidateSource::Builtin => 1,
        AiSearchCandidateSource::Model => 2,
        AiSearchCandidateSource::Exploration => 3,
        AiSearchCandidateSource::Repair => 4,
    }
}

fn ai_search_builtin_kind_rank(kind: Option<AiSearchBuiltinKind>) -> u8 {
    match kind {
        Some(AiSearchBuiltinKind::Intro) => 0,
        Some(AiSearchBuiltinKind::LocalExact) => 1,
        Some(AiSearchBuiltinKind::InductionNat) => 2,
        Some(AiSearchBuiltinKind::SimpLiteEmpty) => 3,
        None => 255,
    }
}

fn ai_search_candidate_envelope_order(
    left: &AiSearchCandidateEnvelope,
    right: &AiSearchCandidateEnvelope,
) -> Ordering {
    left.metadata
        .rank
        .stage_rank
        .cmp(&right.metadata.rank.stage_rank)
        .then_with(|| {
            left.metadata
                .rank
                .source_rank
                .cmp(&right.metadata.rank.source_rank)
        })
        .then_with(|| {
            left.metadata
                .rank
                .builtin_kind_rank
                .cmp(&right.metadata.rank.builtin_kind_rank)
        })
        .then_with(|| {
            left.metadata
                .rank
                .source_index
                .cmp(&right.metadata.rank.source_index)
        })
        .then_with(|| {
            left.ai_search_candidate_payload_hash
                .cmp(&right.ai_search_candidate_payload_hash)
        })
}

fn ai_search_builtin_intro_candidate(goal: &MachineGoalView) -> Option<MachineTacticCandidate> {
    let term = parse_machine_term(FileId(0), &goal.target.machine).ok()?;
    let MachineTerm::Pi { binders, .. } = term else {
        return None;
    };
    let outer_binder_name = binders.first().map(|binder| binder.name.as_str());
    Some(MachineTacticCandidate::Intro {
        name: ai_search_fresh_intro_name(goal, outer_binder_name)?,
    })
}

fn ai_search_local_exact_prefilter(goal: &MachineGoalView, local: &MachineLocalView) -> bool {
    local.value.is_none()
        && local.ty.core_hash == goal.target.core_hash
        && ai_search_machine_name_is_unique(goal, &local.machine_name)
}

fn ai_search_induction_nat_prefilter(
    goal: &MachineGoalView,
    context_index: usize,
    local: &MachineLocalView,
) -> bool {
    ai_search_goal_allows_tactic(goal, MachineApiTacticKind::InductionNat)
        && ai_search_machine_name_is_unique(goal, &local.machine_name)
        && local.value.is_none()
        && context_index + 1 == goal.context.len()
        && goal.target.free_locals.contains(&local.local_id)
}

fn ai_search_goal_allows_tactic(goal: &MachineGoalView, tactic: MachineApiTacticKind) -> bool {
    goal.allowed_tactics.contains(&tactic)
}

fn ai_search_machine_name_is_unique(goal: &MachineGoalView, machine_name: &str) -> bool {
    goal.context
        .iter()
        .filter(|local| local.machine_name == machine_name)
        .count()
        == 1
}

fn ai_search_raw_term_forbidden_token(
    raw_term_index: u32,
    term: &RawMachineTerm,
) -> Result<Option<AiSearchForbiddenToken>, AiSearchCandidateFilterError> {
    let tokens = lex_machine_surface_tokens(&term.source).map_err(|error| {
        AiSearchCandidateFilterError::RawMachineTermLex {
            raw_term_index,
            source: term.source.clone(),
            message: error.message,
        }
    })?;
    let semantic_tokens = tokens
        .iter()
        .filter(|token| {
            !matches!(
                token.kind,
                MachineSurfaceTokenKind::Whitespace | MachineSurfaceTokenKind::Comment
            )
        })
        .collect::<Vec<_>>();

    let mut best_token = None;
    for (index, token) in semantic_tokens.iter().enumerate() {
        if matches!(token.kind, MachineSurfaceTokenKind::ExternalCommand) {
            let candidate = AiSearchForbiddenToken {
                class: AiSearchForbiddenTokenClass::ExternalCommand,
                spelling: token.spelling.clone(),
                raw_term_index,
            };
            if ai_search_forbidden_token_is_better(best_token.as_ref(), &candidate) {
                best_token = Some(candidate);
            }
        }
        if token.spelling == "set_option"
            && semantic_tokens
                .get(index + 1)
                .is_some_and(|next| next.spelling == "unsafe")
        {
            let candidate = AiSearchForbiddenToken {
                class: AiSearchForbiddenTokenClass::SetOptionUnsafe,
                spelling: "set_option unsafe".to_owned(),
                raw_term_index,
            };
            if ai_search_forbidden_token_is_better(best_token.as_ref(), &candidate) {
                best_token = Some(candidate);
            }
            continue;
        }
        if token.spelling == "unsafe"
            && index > 0
            && semantic_tokens[index - 1].spelling == "set_option"
        {
            continue;
        }
        if let Some(class) = ai_search_forbidden_token_class_for_spelling(&token.spelling) {
            let candidate = AiSearchForbiddenToken {
                class,
                spelling: token.spelling.clone(),
                raw_term_index,
            };
            if ai_search_forbidden_token_is_better(best_token.as_ref(), &candidate) {
                best_token = Some(candidate);
            }
        }
    }
    Ok(best_token)
}

fn ai_search_forbidden_token_is_better(
    current: Option<&AiSearchForbiddenToken>,
    candidate: &AiSearchForbiddenToken,
) -> bool {
    current.is_none_or(|current| {
        ai_search_forbidden_token_class_rank(candidate.class)
            < ai_search_forbidden_token_class_rank(current.class)
    })
}

fn ai_search_forbidden_token_class_rank(class: AiSearchForbiddenTokenClass) -> u8 {
    match class {
        AiSearchForbiddenTokenClass::Sorry => 0,
        AiSearchForbiddenTokenClass::Admit => 1,
        AiSearchForbiddenTokenClass::Axiom => 2,
        AiSearchForbiddenTokenClass::Unsafe => 3,
        AiSearchForbiddenTokenClass::Import => 4,
        AiSearchForbiddenTokenClass::SetOptionUnsafe => 5,
        AiSearchForbiddenTokenClass::Declare => 6,
        AiSearchForbiddenTokenClass::Eval => 7,
        AiSearchForbiddenTokenClass::Shell => 8,
        AiSearchForbiddenTokenClass::ExternalCommand => 9,
        AiSearchForbiddenTokenClass::DisallowedTacticKind => 10,
    }
}

fn ai_search_forbidden_token_class_for_spelling(
    spelling: &str,
) -> Option<AiSearchForbiddenTokenClass> {
    match spelling {
        "sorry" => Some(AiSearchForbiddenTokenClass::Sorry),
        "admit" => Some(AiSearchForbiddenTokenClass::Admit),
        "axiom" => Some(AiSearchForbiddenTokenClass::Axiom),
        "unsafe" => Some(AiSearchForbiddenTokenClass::Unsafe),
        "import" => Some(AiSearchForbiddenTokenClass::Import),
        "declare" => Some(AiSearchForbiddenTokenClass::Declare),
        "eval" => Some(AiSearchForbiddenTokenClass::Eval),
        "shell" => Some(AiSearchForbiddenTokenClass::Shell),
        _ => None,
    }
}

fn ai_search_candidate_raw_terms(candidate: &MachineTacticCandidate) -> Vec<&RawMachineTerm> {
    let mut terms = Vec::new();
    match candidate {
        MachineTacticCandidate::Exact { term } => terms.push(term),
        MachineTacticCandidate::Apply { args, .. } => {
            for arg in args {
                if let CandidateApplyArg::Term(term) = arg {
                    terms.push(term);
                }
            }
        }
        MachineTacticCandidate::Rewrite { rule, .. } => {
            for arg in &rule.args {
                if let CandidateApplyArg::Term(term) = arg {
                    terms.push(term);
                }
            }
        }
        MachineTacticCandidate::Intro { .. }
        | MachineTacticCandidate::SimpLite { .. }
        | MachineTacticCandidate::Smt { .. }
        | MachineTacticCandidate::InductionNat { .. }
        | MachineTacticCandidate::Constructor(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Contradiction(_)
        | MachineTacticCandidate::FiniteDecide
        | MachineTacticCandidate::Omega
        | MachineTacticCandidate::Ring
        | MachineTacticCandidate::Bitblast => {}
        MachineTacticCandidate::Cases(payload) => {
            if let Some(motive) = &payload.motive {
                terms.push(motive);
            }
        }
        MachineTacticCandidate::GeneralInduction(payload) => {
            if let Some(motive) = &payload.motive {
                terms.push(motive);
            }
        }
        MachineTacticCandidate::Refine(payload) => terms.push(&payload.term),
        MachineTacticCandidate::Have(payload) => {
            terms.push(&payload.ty);
            ai_search_push_local_lemma_proof_terms(&payload.proof, &mut terms);
        }
        MachineTacticCandidate::Suffices(payload) => {
            terms.push(&payload.target);
            ai_search_push_local_lemma_proof_terms(&payload.proof, &mut terms);
        }
        MachineTacticCandidate::Specialize(payload) => {
            for arg in &payload.args {
                if let CandidateApplyArg::Term(term) = arg {
                    terms.push(term);
                }
            }
        }
        MachineTacticCandidate::Generalize(payload) => terms.push(&payload.term),
        MachineTacticCandidate::Change(payload) => terms.push(&payload.replacement),
    }
    terms
}

fn ai_search_push_local_lemma_proof_terms<'a>(
    proof: &'a LocalLemmaProof<RawMachineTerm>,
    terms: &mut Vec<&'a RawMachineTerm>,
) {
    if let LocalLemmaProof::Term(term) = proof {
        terms.push(term);
    }
}

fn ai_search_raw_machine_term_json(term: &RawMachineTerm) -> String {
    format!(r#"{{"source":{}}}"#, json_string(&term.source))
}

fn ai_search_tactic_head_json(head: &TacticHead) -> String {
    match head {
        TacticHead::Imported {
            name,
            decl_interface_hash,
        } => format!(
            r#"{{"imported":{{"decl_interface_hash":{},"name":{}}}}}"#,
            json_string(&format_hash_string(decl_interface_hash)),
            json_string(&name.as_dotted()),
        ),
        TacticHead::CurrentModule {
            name,
            decl_interface_hash,
        } => format!(
            r#"{{"current_module":{{"decl_interface_hash":{},"name":{}}}}}"#,
            json_string(&format_hash_string(decl_interface_hash)),
            json_string(&name.as_dotted()),
        ),
        TacticHead::Local { name } => {
            format!(r#"{{"local":{{"name":{}}}}}"#, json_string(name))
        }
    }
}

fn ai_search_rewrite_rule_json(rule: &CandidateRewriteRuleRef) -> String {
    format!(
        r#"{{"args":{},"head":{},"universe_args":{}}}"#,
        ai_search_apply_arg_array_json(&rule.args),
        ai_search_tactic_head_json(&rule.head),
        ai_search_level_array_json(&rule.universe_args),
    )
}

fn ai_search_apply_arg_array_json(args: &[CandidateApplyArg]) -> String {
    let members = args
        .iter()
        .map(ai_search_apply_arg_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_apply_arg_json(arg: &CandidateApplyArg) -> String {
    match arg {
        CandidateApplyArg::Term(term) => format!(
            r#"{{"mode":"term","term":{}}}"#,
            ai_search_raw_machine_term_json(term)
        ),
        CandidateApplyArg::Subgoal { name_hint } => {
            let name_hint = name_hint
                .as_ref()
                .map(|name| json_string(name))
                .unwrap_or_else(|| "null".to_owned());
            format!(r#"{{"mode":"subgoal","name_hint":{name_hint}}}"#)
        }
        CandidateApplyArg::InferFromTarget => r#"{"mode":"infer_from_target"}"#.to_owned(),
    }
}

fn ai_search_simp_rule_array_json(rules: &[SimpRuleRef]) -> String {
    let members = rules
        .iter()
        .map(ai_search_simp_rule_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_simp_rule_json(rule: &SimpRuleRef) -> String {
    format!(
        r#"{{"decl_interface_hash":{},"direction":{},"name":{}}}"#,
        json_string(&format_hash_string(&rule.decl_interface_hash)),
        json_string(ai_search_rewrite_direction_wire(rule.direction)),
        json_string(&rule.name.as_dotted()),
    )
}

fn ai_search_smt_lemma_array_json(lemmas: &[SmtLemmaRef]) -> String {
    let members = lemmas
        .iter()
        .map(ai_search_smt_lemma_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_smt_lemma_json(lemma: &SmtLemmaRef) -> String {
    format!(
        r#"{{"head":{},"universe_args":{}}}"#,
        ai_search_tactic_head_json(&lemma.head),
        ai_search_level_array_json(&lemma.universe_args),
    )
}

fn ai_search_level_array_json(levels: &[Level]) -> String {
    let members = levels
        .iter()
        .map(|level| json_string(&ai_search_render_level_wire(level)))
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_render_level_wire(level: &Level) -> String {
    if let Some(value) = ai_search_level_as_nat(level) {
        return value.to_string();
    }
    match level {
        Level::Zero => "0".to_owned(),
        Level::Succ(inner) => format!("succ {}", ai_search_render_level_wire(inner)),
        Level::Max(lhs, rhs) => {
            format!(
                "max {} {}",
                ai_search_render_level_wire(lhs),
                ai_search_render_level_wire(rhs)
            )
        }
        Level::IMax(lhs, rhs) => {
            format!(
                "imax {} {}",
                ai_search_render_level_wire(lhs),
                ai_search_render_level_wire(rhs)
            )
        }
        Level::Param(name) => name.clone(),
    }
}

fn ai_search_level_as_nat(level: &Level) -> Option<u64> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(inner) => Some(ai_search_level_as_nat(inner)? + 1),
        _ => None,
    }
}

fn ai_search_rewrite_direction_wire(direction: RewriteDirection) -> &'static str {
    match direction {
        RewriteDirection::Forward => "forward",
        RewriteDirection::Backward => "backward",
    }
}

fn ai_search_rewrite_site_wire(site: RewriteSite) -> &'static str {
    match site {
        RewriteSite::EqTargetLeft => "eq_target_left",
        RewriteSite::EqTargetRight => "eq_target_right",
    }
}

fn ai_search_optional_global_ref_view_json(view: Option<&MachineGlobalRefView>) -> String {
    view.map(ai_search_global_ref_view_json)
        .unwrap_or_else(|| "null".to_owned())
}

fn ai_search_global_ref_view_json(view: &MachineGlobalRefView) -> String {
    match view {
        MachineGlobalRefView::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
            public_export,
            tactic_head_visible,
        } => format!(
            r#"{{"kind":"imported","module":{},"name":{},"export_hash":{},"decl_interface_hash":{},"public_export":{},"tactic_head_visible":{}}}"#,
            json_string(&module.as_dotted()),
            json_string(&name.as_dotted()),
            json_string(&format_hash_string(export_hash)),
            json_string(&format_hash_string(decl_interface_hash)),
            bool_json(*public_export),
            bool_json(*tactic_head_visible),
        ),
        MachineGlobalRefView::CurrentModule {
            module,
            name,
            decl_interface_hash,
            source_index,
        } => format!(
            r#"{{"kind":"current_module","module":{},"name":{},"decl_interface_hash":{},"source_index":{}}}"#,
            json_string(&module.as_dotted()),
            json_string(&name.as_dotted()),
            json_string(&format_hash_string(decl_interface_hash)),
            source_index,
        ),
        MachineGlobalRefView::LocalGenerated {
            module,
            export_hash,
            parent_name,
            name,
            parent_decl_interface_hash,
            decl_interface_hash,
            public_export,
            tactic_head_visible,
        } => {
            let export_hash = export_hash
                .map(|hash| json_string(&format_hash_string(&hash)))
                .unwrap_or_else(|| "null".to_owned());
            format!(
                r#"{{"kind":"local_generated","module":{},"export_hash":{},"parent_name":{},"name":{},"parent_decl_interface_hash":{},"decl_interface_hash":{},"public_export":{},"tactic_head_visible":{}}}"#,
                json_string(&module.as_dotted()),
                export_hash,
                json_string(&parent_name.as_dotted()),
                json_string(&name.as_dotted()),
                json_string(&format_hash_string(parent_decl_interface_hash)),
                json_string(&format_hash_string(decl_interface_hash)),
                bool_json(*public_export),
                bool_json(*tactic_head_visible),
            )
        }
    }
}

fn ai_search_axiom_refs_json(axioms: &[MachineAxiomRefWire]) -> String {
    let members = axioms
        .iter()
        .map(ai_search_axiom_ref_json)
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_axiom_ref_json(axiom: &MachineAxiomRefWire) -> String {
    match axiom {
        MachineAxiomRefWire::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
        } => format!(
            r#"{{"kind":"imported","module":{},"name":{},"export_hash":{},"decl_interface_hash":{}}}"#,
            json_string(&module.as_dotted()),
            json_string(&name.as_dotted()),
            json_string(&format_hash_string(export_hash)),
            json_string(&format_hash_string(decl_interface_hash)),
        ),
        MachineAxiomRefWire::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
        } => format!(
            r#"{{"kind":"current_module","module":{},"name":{},"source_index":{},"decl_interface_hash":{}}}"#,
            json_string(&module.as_dotted()),
            json_string(&name.as_dotted()),
            source_index,
            json_string(&format_hash_string(decl_interface_hash)),
        ),
        MachineAxiomRefWire::Builtin {
            name,
            decl_interface_hash,
        } => format!(
            r#"{{"kind":"builtin","name":{},"decl_interface_hash":{}}}"#,
            json_string(&name.as_dotted()),
            json_string(&format_hash_string(decl_interface_hash)),
        ),
    }
}

fn ai_search_theorem_modes_json(modes: &[MachineTheoremMode]) -> String {
    let members = modes
        .iter()
        .map(|mode| json_string(mode.as_str()))
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn ai_search_string_array_json(values: &[String]) -> String {
    let members = values
        .iter()
        .map(|value| json_string(value))
        .collect::<Vec<_>>();
    format!("[{}]", members.join(","))
}

fn bool_json(value: bool) -> &'static str {
    if value {
        "true"
    } else {
        "false"
    }
}

fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            ch if ch <= '\u{1f}' => {
                out.push_str("\\u");
                out.push_str(&format!("{:04x}", ch as u32));
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).expect("machine API vector length fits in u32")
}

pub fn parse_ai_search_mvp_controller_config(
    source: &str,
) -> Result<AiSearchMvpControllerConfig, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidBatchPolicy)?;
    let members = validate_ai_search_config_top_level(doc.root())?;

    let search_budget = parse_ai_search_budget(
        required_config_field(members, "search_budget"),
        &JsonPath::root().field("search_budget"),
    )?;
    let per_tactic_deterministic_budget = parse_deterministic_budget_with_error_kind(
        required_config_field(members, "per_tactic_deterministic_budget"),
        &JsonPath::root().field("per_tactic_deterministic_budget"),
        MachineApiErrorKind::InvalidBudget,
    )?;
    let scheduler_limits = member_value(members, "scheduler_limits")
        .map(|value| {
            parse_ai_search_batch_scheduler_limits(
                value,
                &JsonPath::root().field("scheduler_limits"),
            )
        })
        .transpose()?;
    let batch_policy = parse_ai_search_batch_policy(
        required_config_field(members, "batch_policy"),
        &JsonPath::root().field("batch_policy"),
    )?;

    validate_ai_search_mvp_controller_config(AiSearchMvpControllerConfig {
        search_budget,
        per_tactic_deterministic_budget,
        scheduler_limits,
        batch_policy,
    })
}

pub fn validate_ai_search_mvp_controller_config(
    config: AiSearchMvpControllerConfig,
) -> Result<AiSearchMvpControllerConfig, MachineApiRequestError> {
    validate_positive_u64(
        config.search_budget.wall_clock_ms,
        "wall_clock_ms",
        &JsonPath::root()
            .field("search_budget")
            .field("wall_clock_ms"),
        MachineApiErrorKind::InvalidBatchPolicy,
    )?;
    validate_positive_u64(
        config.search_budget.max_nodes,
        "max_nodes",
        &JsonPath::root().field("search_budget").field("max_nodes"),
        MachineApiErrorKind::InvalidBatchPolicy,
    )?;
    if config.search_budget.max_tactics_per_node != AI_SEARCH_MVP_MAX_TACTICS_PER_NODE {
        return Err(invalid_u64(
            "max_tactics_per_node",
            u64::from(config.search_budget.max_tactics_per_node),
            &JsonPath::root()
                .field("search_budget")
                .field("max_tactics_per_node"),
            MachineApiErrorKind::InvalidBatchPolicy,
        ));
    }

    validate_batch_policy_value(
        config.batch_policy.max_evaluated_candidates,
        "max_evaluated_candidates",
    )?;
    validate_batch_policy_value(
        config.batch_policy.stop_after_successes,
        "stop_after_successes",
    )?;
    validate_batch_policy_value(
        config.batch_policy.stop_after_failures,
        "stop_after_failures",
    )?;

    if let Some(scheduler_limits) = config.scheduler_limits {
        validate_optional_scheduler_limit(
            scheduler_limits.per_candidate_timeout_ms,
            "per_candidate_timeout_ms",
        )?;
        validate_optional_scheduler_limit(scheduler_limits.batch_timeout_ms, "batch_timeout_ms")?;
        validate_optional_scheduler_limit(scheduler_limits.max_memory_mb, "max_memory_mb")?;
    }

    Ok(config)
}

fn parse_ai_search_budget(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<AiSearchBudget, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            AI_SEARCH_SEARCH_BUDGET_FIELDS,
        ),
        path,
    )?;
    Ok(AiSearchBudget {
        wall_clock_ms: required_u64(&object, "wall_clock_ms"),
        max_nodes: required_u64(&object, "max_nodes"),
        max_tactics_per_node: required_u32(
            &object,
            "max_tactics_per_node",
            &path.field("max_tactics_per_node"),
        )?,
        max_depth: required_u32(&object, "max_depth", &path.field("max_depth"))?,
    })
}

fn parse_ai_search_batch_policy(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineTacticBatchPolicy, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            AI_SEARCH_BATCH_POLICY_FIELDS,
        ),
        path,
    )?;
    Ok(MachineTacticBatchPolicy {
        max_evaluated_candidates: required_batch_policy_u32(
            &object,
            "max_evaluated_candidates",
            &path.field("max_evaluated_candidates"),
        )?,
        stop_after_successes: required_batch_policy_u32(
            &object,
            "stop_after_successes",
            &path.field("stop_after_successes"),
        )?,
        stop_after_failures: required_batch_policy_u32(
            &object,
            "stop_after_failures",
            &path.field("stop_after_failures"),
        )?,
    })
}

fn parse_ai_search_batch_scheduler_limits(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineBatchSchedulerLimits, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidSchedulerLimits,
            AI_SEARCH_BATCH_SCHEDULER_FIELDS,
        ),
        path,
    )?;
    Ok(MachineBatchSchedulerLimits {
        per_candidate_timeout_ms: optional_positive_u64(
            &object,
            "per_candidate_timeout_ms",
            &path.field("per_candidate_timeout_ms"),
        )?,
        batch_timeout_ms: optional_positive_u64(
            &object,
            "batch_timeout_ms",
            &path.field("batch_timeout_ms"),
        )?,
        max_memory_mb: optional_positive_u64(
            &object,
            "max_memory_mb",
            &path.field("max_memory_mb"),
        )?,
    })
}

fn validate_ai_search_config_top_level<'value, 'src>(
    root: &'value JsonValue<'src>,
) -> Result<&'value [JsonMember<'src>], MachineApiRequestError> {
    let members = root.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            JsonPath::root(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: root.kind(),
            },
        )
    })?;

    let mut seen = std::collections::BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                JsonPath::root().field(member.key()),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }

    for member in members {
        if member.key() == "scheduler_limits" {
            validate_top_level_field(
                member.value(),
                "scheduler_limits",
                JsonFieldType::Object,
                MachineApiErrorKind::InvalidSchedulerLimits,
            )?;
        } else if let Some(field) = AI_SEARCH_CONFIG_FIELDS
            .iter()
            .find(|field| field.name == member.key())
        {
            validate_top_level_field(
                member.value(),
                field.name,
                field.field_type,
                field_error_kind(field.name),
            )?;
        } else {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                JsonPath::root().field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }

    for field in AI_SEARCH_CONFIG_FIELDS {
        if !members.iter().any(|member| member.key() == field.name) {
            return Err(MachineApiRequestError::new(
                field_error_kind(field.name),
                JsonPath::root().field(field.name),
                MachineApiRequestErrorReason::MissingField { field: field.name },
            ));
        }
    }

    Ok(members)
}

fn validate_top_level_field(
    value: &JsonValue<'_>,
    field: &'static str,
    expected: JsonFieldType,
    error_kind: MachineApiErrorKind,
) -> Result<(), MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Err(MachineApiRequestError::new(
            error_kind,
            JsonPath::root().field(field),
            MachineApiRequestErrorReason::NullField { field },
        ));
    }

    let valid = matches!(
        (expected, value.kind()),
        (JsonFieldType::Object, JsonValueKind::Object)
            | (JsonFieldType::Array, JsonValueKind::Array)
            | (JsonFieldType::String, JsonValueKind::String)
            | (JsonFieldType::Boolean, JsonValueKind::Bool)
    );
    if valid {
        return Ok(());
    }

    Err(MachineApiRequestError::new(
        error_kind,
        JsonPath::root().field(field),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected,
            actual: value.kind(),
        },
    ))
}

fn field_error_kind(field: &str) -> MachineApiErrorKind {
    match field {
        "per_tactic_deterministic_budget" => MachineApiErrorKind::InvalidBudget,
        _ => MachineApiErrorKind::InvalidBatchPolicy,
    }
}

fn required_config_field<'value, 'src>(
    members: &'value [JsonMember<'src>],
    field: &str,
) -> &'value JsonValue<'src> {
    member_value(members, field).expect("schema checked required field")
}

fn member_value<'value, 'src>(
    members: &'value [JsonMember<'src>],
    field: &str,
) -> Option<&'value JsonValue<'src>> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
}

fn required_u64(object: &ValidatedObject<'_, '_>, field: &str) -> u64 {
    object
        .field(field)
        .and_then(JsonValue::number_raw)
        .and_then(|raw| parse_strict_u64_token(raw, u64::MAX).ok())
        .expect("schema checked required u64 field")
}

fn required_u32(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<u32, MachineApiRequestError> {
    let raw = object
        .field(field)
        .and_then(JsonValue::number_raw)
        .expect("schema checked required u32 field");
    let parsed = parse_strict_u64_token(raw, u64::from(u32::MAX)).map_err(|error| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error,
            },
        )
    })?;
    Ok(parsed as u32)
}

fn required_batch_policy_u32(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<u32, MachineApiRequestError> {
    let raw = object
        .field(field)
        .and_then(JsonValue::number_raw)
        .expect("schema checked required batch policy u64 field");
    let parsed = parse_strict_u64_token(raw, 256).map_err(|error| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error,
            },
        )
    })?;
    if parsed == 0 {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            },
        ));
    }
    Ok(parsed as u32)
}

fn optional_positive_u64(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Option<u64>, MachineApiRequestError> {
    let Some(value) = object.field(field) else {
        return Ok(None);
    };
    let raw = value
        .number_raw()
        .expect("schema checked optional scheduler u64 field");
    let parsed =
        parse_strict_u64_token(raw, u64::MAX).expect("schema checked optional scheduler u64 field");
    if parsed == 0 {
        return Err(invalid_u64(
            field,
            parsed,
            path,
            MachineApiErrorKind::InvalidSchedulerLimits,
        ));
    }
    Ok(Some(parsed))
}

fn validate_positive_u64(
    value: u64,
    field: &'static str,
    path: &JsonPath,
    kind: MachineApiErrorKind,
) -> Result<(), MachineApiRequestError> {
    if value == 0 {
        return Err(invalid_u64(field, value, path, kind));
    }
    Ok(())
}

fn validate_batch_policy_value(
    value: u32,
    field: &'static str,
) -> Result<(), MachineApiRequestError> {
    if value == 0 || value > 256 {
        return Err(invalid_u64(
            field,
            u64::from(value),
            &JsonPath::root().field("batch_policy").field(field),
            MachineApiErrorKind::InvalidBatchPolicy,
        ));
    }
    Ok(())
}

fn validate_optional_scheduler_limit(
    value: Option<u64>,
    field: &'static str,
) -> Result<(), MachineApiRequestError> {
    if value == Some(0) {
        return Err(invalid_u64(
            field,
            0,
            &JsonPath::root().field("scheduler_limits").field(field),
            MachineApiErrorKind::InvalidSchedulerLimits,
        ));
    }
    Ok(())
}

fn invalid_u64(
    field: &'static str,
    value: u64,
    path: &JsonPath,
    kind: MachineApiErrorKind,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        path.clone(),
        MachineApiRequestErrorReason::InvalidUnsignedInteger {
            field,
            raw: value.to_string(),
            error: StrictUnsignedIntegerError::InvalidGrammar,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_tactic::{
        CandidateApplyArg, CandidateRewriteRuleRef, MachineTacticCandidate, MetaVarId,
        RawMachineTerm, RewriteDirection, RewriteSite, TacticHead,
    };

    use crate::search::{
        MachinePremiseAxiomPath, MachinePremiseAxiomPathSource, MachinePremiseAxiomRankingMetadata,
        MachinePremiseAxiomRankingPenalties, MachinePremiseCandidateProvenance,
        MachinePremiseIndexSource, MachinePremiseRankingMetadata, MachinePremiseSearchOkFields,
        MachinePremiseSearchResult, MachinePremiseSetAxiomImpact, MachinePremiseSetFeature,
        MachinePremiseSetFeatureKind, MachinePremiseSetMetadata, MachinePremiseSetObjective,
        MachinePremiseSetSelectedPremise, MachinePremiseStructuralFeatures,
        MachinePremiseStructuralRef, MachinePremiseTheoremLevel, MachinePremiseUntrustedSidecar,
        MachineRetrievalCacheKey, MachineTheoremFilters, MachineTypeAwarePremiseMetadata,
        MachineVerifiedPremiseAxiomSummary, MachineVerifiedPremiseGlobalRef,
        MachineVerifiedPremiseIdentity,
    };
    use crate::{
        parse_machine_snapshot_get_request, parse_machine_tactic_batch_request,
        parse_machine_theorem_search_request, CertificateTheoremGraphEdge,
        CertificateTheoremGraphExtractorVersion, CertificateTheoremGraphNodeKind,
        CertificateTheoremGraphNodeMetadata, JsonFieldType, LocalId, MachineAllowedModulesFilter,
        MachineApiErrorResponse, MachineApiOkResponse, MachineApiRequestErrorReason,
        MachineApiResponseEnvelope, MachineApiResponseStatus, MachineApiSchedulerResponse,
        MachineCertificateWirePayload, MachineExprView, MachineLocalView, MachineSchedulerArtifact,
        MachineSchedulerArtifactKind, MachineSchedulerArtifactScope, MachineSuggestedCandidate,
        MachineSuggestedCandidateStatus, MachineTheoremGlobalRef, MachineTheoremStatement,
        MachineVerifiedModuleCertificatePayload,
    };

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    #[test]
    fn ai_search_candidate_api_stays_separate_from_certificate_core_candidates() {
        let _: fn(
            MachineTacticCandidate,
            Option<Hash>,
            AiSearchCandidateMetadata,
        ) -> AiSearchCandidateEnvelope = ai_search_candidate_envelope;
        let _: fn(&MachineTacticCandidate) -> Hash = ai_search_candidate_payload_hash;
        let _: fn(&MachineTacticCandidate) -> String = ai_search_candidate_payload_json;
        let _: fn(&MachineTacticCandidate) -> AiSearchExpectedEffect = ai_search_expected_effect;
        let _: fn(&MachineTacticCandidate) -> AiSearchCandidateCostEstimate =
            ai_search_candidate_cost_estimate;
        let _: fn(
            &MachineTacticCandidate,
        ) -> std::result::Result<
            Option<AiSearchForbiddenToken>,
            AiSearchCandidateFilterError,
        > = ai_search_candidate_forbidden_token;
        let _: fn(
            GoalId,
            MachineTacticCandidate,
        ) -> crate::MachineTacticAdapterResult<crate::ValidatedMachineTactic> =
            crate::machine_tactic_validate_machine_tactic_candidate;

        assert_ne!(
            std::any::TypeId::of::<MachineTacticCandidate>(),
            std::any::TypeId::of::<npa_cert::CoreDeclCandidate>()
        );
    }

    #[test]
    fn ai_search_smt_training_trace_serializes_solver_family_without_logs() {
        let smt_candidate = MachineTacticCandidate::Smt { lemmas: Vec::new() };
        let trace_candidate = AiSearchTrainingTraceCandidate::Error {
            rank_index: 0,
            ai_search_candidate_payload_hash: ai_search_candidate_payload_hash(&smt_candidate),
            candidate: smt_candidate.clone(),
            candidate_hash: hash(20),
            error_kind: FailedCandidateErrorKind::UnsupportedTactic,
            phase: crate::MachineApiDiagnosticPhase::CandidateValidation,
            deterministic_budget_hash: hash(21),
            diagnostic_hash: hash(22),
            retryable: false,
            goal_id: Some(GoalId(0)),
            tactic_kind: Some(MachineApiTacticKind::Smt),
        };

        let trace_json = ai_search_training_trace_candidate_json(&trace_candidate);
        assert!(trace_json.contains(r#""solver_family":"smt""#));
        assert!(trace_json.contains(r#""solver_contract_version":"npa.solver-contract.v1""#));
        assert!(trace_json.contains(r#""candidate":{"kind":"smt","lemmas":[]}"#));
        assert!(
            trace_json.contains(&format_hash_string(&ai_search_candidate_payload_hash(
                &smt_candidate
            )))
        );
        for forbidden in [
            "raw_solver_stdout",
            "raw_solver_stderr",
            "wall_clock",
            "display_text",
            "ranking_score",
        ] {
            assert!(!trace_json.contains(forbidden));
        }

        let finite_candidate = MachineTacticCandidate::FiniteDecide;
        let success = AiSearchTrainingTraceCandidate::Success {
            rank_index: 1,
            ai_search_candidate_payload_hash: ai_search_candidate_payload_hash(&finite_candidate),
            candidate: finite_candidate,
            candidate_hash: hash(30),
            deterministic_budget_hash: hash(31),
            proof_delta_hash: hash(32),
            next_snapshot_id: SnapshotId::from_state_fingerprint(hash(33)),
            next_state_fingerprint: hash(33),
        };
        let success_json = ai_search_training_trace_candidate_json(&success);
        assert!(success_json.contains(r#""solver_family":"finite_decide""#));
        assert!(success_json.contains(r#""result":"success""#));
    }

    #[test]
    fn ai_search_solver_candidates_are_structured_ranked_and_sidecar_free() {
        let solvers = [
            (
                MachineTacticCandidate::FiniteDecide,
                r#"{"kind":"finite-decide"}"#,
                AiSearchCheapFirstStage::FiniteDecide,
                AiSearchCandidateCostEstimate {
                    estimated_timeout_ms: 100,
                    risk: AiSearchCandidateCostRisk::Low,
                },
            ),
            (
                MachineTacticCandidate::Omega,
                r#"{"kind":"omega"}"#,
                AiSearchCheapFirstStage::RingOmega,
                AiSearchCandidateCostEstimate {
                    estimated_timeout_ms: 250,
                    risk: AiSearchCandidateCostRisk::Medium,
                },
            ),
            (
                MachineTacticCandidate::Ring,
                r#"{"kind":"ring"}"#,
                AiSearchCheapFirstStage::RingOmega,
                AiSearchCandidateCostEstimate {
                    estimated_timeout_ms: 250,
                    risk: AiSearchCandidateCostRisk::Medium,
                },
            ),
            (
                MachineTacticCandidate::Bitblast,
                r#"{"kind":"bitblast"}"#,
                AiSearchCheapFirstStage::Bitblast,
                AiSearchCandidateCostEstimate {
                    estimated_timeout_ms: 400,
                    risk: AiSearchCandidateCostRisk::High,
                },
            ),
            (
                MachineTacticCandidate::Smt { lemmas: Vec::new() },
                r#"{"kind":"smt","lemmas":[]}"#,
                AiSearchCheapFirstStage::Smt,
                AiSearchCandidateCostEstimate {
                    estimated_timeout_ms: 500,
                    risk: AiSearchCandidateCostRisk::High,
                },
            ),
        ];
        let mut payload_hashes = std::collections::BTreeSet::new();

        for (index, (candidate, expected_json, expected_stage, expected_cost)) in
            solvers.iter().enumerate()
        {
            assert_eq!(ai_search_candidate_payload_json(candidate), *expected_json);
            assert!(payload_hashes.insert(ai_search_candidate_payload_hash(candidate)));
            assert_eq!(
                ai_search_expected_effect(candidate),
                AiSearchExpectedEffect::CloseGoal
            );
            assert_eq!(ai_search_candidate_cost_estimate(candidate), *expected_cost);
            assert_eq!(
                ai_search_candidate_forbidden_token(candidate).unwrap(),
                None
            );

            let metadata = ai_search_candidate_metadata(
                AiSearchCandidateSource::Exploration,
                None,
                index as u32,
                Vec::new(),
                Vec::new(),
                candidate,
            );
            assert_eq!(metadata.rank.cheap_first_stage, *expected_stage);
            assert_eq!(metadata.rank.skip_reason, None);
            assert_eq!(metadata.expected_effect, AiSearchExpectedEffect::CloseGoal);
            assert_eq!(metadata.cost_estimate, *expected_cost);

            let envelope = ai_search_candidate_envelope(candidate.clone(), Some(hash(1)), metadata);
            let mut scored_metadata = envelope.metadata.clone();
            scored_metadata.score = 99_000;
            scored_metadata.display_text =
                Some("raw_solver_stdout wall_clock ranking_score".to_owned());
            let scored =
                ai_search_candidate_envelope(candidate.clone(), Some(hash(2)), scored_metadata);
            assert_eq!(
                envelope.ai_search_candidate_payload_hash,
                scored.ai_search_candidate_payload_hash
            );

            let family = ai_search_solver_family(candidate).expect("solver family");
            let trace = AiSearchTrainingTraceCandidate::Error {
                rank_index: index as u32,
                ai_search_candidate_payload_hash: ai_search_candidate_payload_hash(candidate),
                candidate: candidate.clone(),
                candidate_hash: hash((30 + index) as u8),
                error_kind: FailedCandidateErrorKind::UnsupportedTactic,
                phase: crate::MachineApiDiagnosticPhase::CandidateValidation,
                deterministic_budget_hash: hash((40 + index) as u8),
                diagnostic_hash: hash((50 + index) as u8),
                retryable: false,
                goal_id: Some(GoalId(index as u64)),
                tactic_kind: None,
            };
            let trace_json = ai_search_training_trace_candidate_json(&trace);
            assert!(trace_json.contains(&format!(r#""solver_family":"{}""#, family.as_str())));
            assert!(trace_json.contains(&format!(
                r#""solver_contract_version":"{}""#,
                SOLVER_CONTRACT_VERSION
            )));
            for forbidden in [
                "raw_solver_stdout",
                "raw_solver_stderr",
                "wall_clock",
                "display_text",
                "ranking_score",
            ] {
                assert!(!trace_json.contains(forbidden));
            }
        }

        assert_eq!(payload_hashes.len(), solvers.len());

        let rewrite = MachineTacticCandidate::Rewrite {
            rule: CandidateRewriteRuleRef {
                head: TacticHead::Imported {
                    name: name("Test.rewrite"),
                    decl_interface_hash: hash(60),
                },
                universe_args: Vec::new(),
                args: Vec::new(),
            },
            direction: RewriteDirection::Forward,
            site: RewriteSite::EqTargetLeft,
        };
        let stage_rank = |candidate: &MachineTacticCandidate| {
            ai_search_candidate_metadata(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                Vec::new(),
                Vec::new(),
                candidate,
            )
            .rank
            .stage_rank
        };

        assert!(
            stage_rank(&MachineTacticCandidate::FiniteDecide) < stage_rank(&rewrite),
            "finite_decide should be tried before simplification/rewrite candidates"
        );
        assert!(
            stage_rank(&rewrite) < stage_rank(&MachineTacticCandidate::Ring),
            "ring/omega should follow rewrite/simplification"
        );
        assert_eq!(
            stage_rank(&MachineTacticCandidate::Ring),
            stage_rank(&MachineTacticCandidate::Omega)
        );
        assert!(
            stage_rank(&MachineTacticCandidate::Omega)
                < stage_rank(&MachineTacticCandidate::Bitblast)
        );
        assert!(
            stage_rank(&MachineTacticCandidate::Bitblast)
                < stage_rank(&MachineTacticCandidate::Smt { lemmas: Vec::new() })
        );
    }

    fn unwrap_search_failure(result: AiSearchResult) -> AiSearchFailure {
        match result {
            Ok(proof) => panic!("expected search failure, got verified proof {proof:?}"),
            Err(failure) => *failure,
        }
    }

    fn unwrap_verified_proof(result: AiSearchResult) -> AiSearchVerifiedProof {
        match result {
            Ok(proof) => proof,
            Err(failure) => panic!("expected verified proof, got search failure {failure:?}"),
        }
    }

    fn name(value: &str) -> Name {
        Name::from_dotted(value)
    }

    fn simp_rule(name_suffix: &str, byte: u8) -> SimpRuleRef {
        SimpRuleRef {
            name: name(&format!("Nat.{name_suffix}")),
            decl_interface_hash: hash(byte),
            direction: RewriteDirection::Forward,
        }
    }

    fn snapshot_request() -> AiSearchSnapshotGetRequest {
        AiSearchSnapshotGetRequest {
            session_id: SessionId::parse("msess_001").unwrap(),
            snapshot_id: SnapshotId::from_state_fingerprint(hash(1)),
            state_fingerprint: hash(1),
        }
    }

    fn imported_ref(name_suffix: &str, byte: u8) -> MachineGlobalRefView {
        MachineGlobalRefView::Imported {
            module: name("Std.Nat.Basic"),
            name: name(&format!("Nat.{name_suffix}")),
            export_hash: hash(byte),
            decl_interface_hash: hash(byte + 1),
            public_export: true,
            tactic_head_visible: true,
        }
    }

    fn expr_view(
        byte: u8,
        size: u32,
        free_local_count: u32,
        head: Option<MachineGlobalRefView>,
    ) -> MachineExprView {
        MachineExprView {
            core_hash: hash(byte),
            head: head.clone(),
            constants: head.into_iter().collect(),
            free_locals: (0..free_local_count).map(LocalId).collect(),
            size,
            machine: format!("expr_{byte}"),
            pretty: Some(format!("pretty_{byte}")),
        }
    }

    fn local_view(index: u32) -> MachineLocalView {
        MachineLocalView {
            local_id: LocalId(index),
            machine_name: format!("x{index}"),
            display_name: format!("x{index}"),
            ty: expr_view(70 + index as u8, 1, 0, None),
            value: None,
            depends_on: Vec::new(),
            binder_index: index,
        }
    }

    fn goal_view(
        goal_id: GoalId,
        byte: u8,
        expr_size: u32,
        free_local_count: u32,
        context_size: u32,
        head: Option<MachineGlobalRefView>,
    ) -> MachineGoalView {
        MachineGoalView {
            goal_id,
            meta_id: MetaVarId(goal_id.0),
            context_hash: hash(byte + 10),
            local_name_map_hash: hash(byte + 11),
            context: (0..context_size).map(local_view).collect(),
            target: expr_view(byte, expr_size, free_local_count, head),
            target_hash: hash(byte + 12),
            goal_fingerprint: hash(byte + 13),
            allowed_tactics: Vec::new(),
        }
    }

    fn snapshot_with_goals(goals: Vec<MachineGoalView>) -> MachineProofSnapshot {
        snapshot_with_state(1, goals)
    }

    fn snapshot_with_state(byte: u8, goals: Vec<MachineGoalView>) -> MachineProofSnapshot {
        MachineProofSnapshot {
            snapshot_id: SnapshotId::from_state_fingerprint(hash(byte)),
            session_id: SessionId::parse("msess_001").unwrap(),
            state_fingerprint: hash(byte),
            tactic_options_fingerprint: hash(byte + 1),
            open_goals: goals.iter().map(|goal| goal.goal_id).collect(),
            goals,
            proof_skeleton_hash: hash(byte + 2),
        }
    }

    fn theorem_result(
        machine: &str,
        suggested: Vec<MachineSuggestedCandidate>,
    ) -> MachineTheoremSearchResult {
        MachineTheoremSearchResult {
            premise_id: "prem_0".to_owned(),
            global_ref: MachineTheoremGlobalRef {
                module: name("Std.Nat.Basic"),
                name: name("Nat.add_zero"),
                export_hash: hash(10),
                decl_interface_hash: hash(11),
            },
            universe_params: vec!["u".to_owned()],
            statement: MachineTheoremStatement {
                core_hash: hash(12),
                head: Some(imported_ref("Eq", 13)),
                machine: machine.to_owned(),
            },
            modes: vec![MachineTheoremMode::Exact, MachineTheoremMode::Simp],
            suggested_candidates: suggested,
            score: 0,
            axioms_used: vec![MachineAxiomRefWire::Imported {
                module: name("Std.Nat.Basic"),
                name: name("Nat.zero_ax"),
                export_hash: hash(14),
                decl_interface_hash: hash(15),
            }],
        }
    }

    fn repair_retrieval_axiom() -> MachineAxiomRefWire {
        MachineAxiomRefWire::Imported {
            module: name("Std.Nat.Basic"),
            name: name("Nat.zero_ax"),
            export_hash: hash(70),
            decl_interface_hash: hash(71),
        }
    }

    fn repair_retrieval_structural_ref() -> MachinePremiseStructuralRef {
        MachinePremiseStructuralRef {
            module: name("Std.Nat.Basic"),
            name: name("Nat.add_zero"),
            export_hash: Some(hash(10)),
            decl_interface_hash: hash(11),
        }
    }

    fn repair_retrieval_identity() -> MachineVerifiedPremiseIdentity {
        MachineVerifiedPremiseIdentity::new(
            name("Std.Nat.Basic"),
            hash(10),
            hash(16),
            MachineVerifiedPremiseGlobalRef {
                module: name("Std.Nat.Basic"),
                name: name("Nat.add_zero"),
                export_hash: hash(10),
                certificate_hash: hash(16),
                decl_interface_hash: hash(11),
            },
            hash(11),
            hash(12),
            MachineVerifiedPremiseAxiomSummary::new(vec![repair_retrieval_axiom()], Vec::new()),
        )
        .unwrap()
    }

    fn repair_retrieval_structural_features() -> MachinePremiseStructuralFeatures {
        MachinePremiseStructuralFeatures::new(
            Some(repair_retrieval_structural_ref()),
            0,
            Vec::new(),
            hash(80),
            Vec::new(),
            None,
            None,
            Vec::new(),
            Vec::new(),
            vec![hash(81)],
        )
    }

    fn repair_retrieval_feature() -> MachinePremiseSetFeature {
        MachinePremiseSetFeature {
            kind: MachinePremiseSetFeatureKind::NormalizedExpression,
            feature_hash: hash(81),
        }
    }

    fn repair_retrieval_objective() -> MachinePremiseSetObjective {
        MachinePremiseSetObjective {
            coverage_score: 1_000,
            historical_co_use_score: 0,
            graph_connectivity_score: 0,
            set_size_penalty: 10,
            import_cost_penalty: 0,
            axiom_cost_penalty: 50,
            final_score: 940,
        }
    }

    fn repair_premise_search_ok_fields() -> MachinePremiseSearchOkFields {
        let identity = repair_retrieval_identity();
        let structural_features = repair_retrieval_structural_features();
        let axiom_path = MachinePremiseAxiomPath {
            source: MachinePremiseAxiomPathSource::DirectAxiomUse,
            axiom: repair_retrieval_axiom(),
            path_length: 1,
            graph_snapshot_hash: None,
        };
        let axiom_impact = MachinePremiseSetAxiomImpact {
            direct_axiom_count: 1,
            transitive_axiom_count: 0,
            summary_hash: identity.axiom_summary.summary_hash,
            axiom_paths: vec![axiom_path.clone()],
        };
        let premise_set = MachinePremiseSetMetadata {
            max_set_size: 4,
            graph_snapshot_hash: None,
            selected_premises: vec![MachinePremiseSetSelectedPremise {
                premise: repair_retrieval_structural_ref(),
                added_features: vec![repair_retrieval_feature()],
                objective: repair_retrieval_objective(),
            }],
            covered_goal_features: vec![repair_retrieval_feature()],
            missing_goal_features: Vec::new(),
            rejected_alternatives: Vec::new(),
            import_requirements: vec![name("Std.Nat.Basic")],
            axiom_impact,
            objective: repair_retrieval_objective(),
        };
        let penalties = MachinePremiseAxiomRankingPenalties {
            direct_axiom_use: 10,
            total: 10,
            ..Default::default()
        };
        MachinePremiseSearchOkFields {
            query_fingerprint: hash(90),
            query_profile_hash: hash(91),
            query_profile_version: crate::PREMISE_SEARCH_QUERY_PROFILE_VERSION,
            theorem_index_fingerprint: hash(92),
            graph_snapshot_hash: None,
            visible_imports_fingerprint: hash(93),
            retrieval_cache_key: MachineRetrievalCacheKey {
                key_hash: hash(94),
                environment_hash: hash(95),
                goal_fingerprint: hash(96),
                local_context_hash: hash(97),
                query_fingerprint: hash(90),
                query_profile_hash: hash(91),
                theorem_index_fingerprint: hash(92),
                graph_snapshot_hash: None,
                visible_imports_fingerprint: hash(93),
            },
            selected_modes: vec![MachineTheoremMode::PremiseSet, MachineTheoremMode::Exact],
            filters: MachineTheoremFilters {
                exclude_axioms: false,
                allowed_modules: MachineAllowedModulesFilter::Explicit(vec![name("Std.Nat.Basic")]),
            },
            limit: 4,
            results: vec![MachinePremiseSearchResult {
                premise_id: "prem_0".to_owned(),
                verified_identity: identity,
                statement_core_hash: hash(12),
                structural_features,
                selected_modes: vec![MachineTheoremMode::PremiseSet],
                ranking_metadata: MachinePremiseRankingMetadata {
                    score: 9_990,
                    axiom_ranking: MachinePremiseAxiomRankingMetadata {
                        theorem_level: MachinePremiseTheoremLevel::VerifiedCertificate,
                        candidate_verified: true,
                        usable_under_axiom_policy: true,
                        direct_axiom_count: 1,
                        transitive_axiom_count: 0,
                        disallowed_axiom_count: 0,
                        axiom_paths: vec![axiom_path],
                        penalties,
                    },
                    type_aware: MachineTypeAwarePremiseMetadata::not_evaluated(),
                    mode_metadata: Vec::new(),
                    premise_set: Some(premise_set),
                },
                candidate_provenance: MachinePremiseCandidateProvenance {
                    premise_source: MachinePremiseIndexSource::DirectImport,
                    suggestion_profile_version: "test-suggestion-profile",
                    suggested_candidate_count: 0,
                },
                untrusted_sidecar: MachinePremiseUntrustedSidecar {
                    suggested_candidates: Vec::new(),
                },
            }],
        }
    }

    fn theorem_result_in_module(
        module: &str,
        theorem: &str,
        byte: u8,
        machine: &str,
    ) -> MachineTheoremSearchResult {
        MachineTheoremSearchResult {
            premise_id: format!("prem_{byte}"),
            global_ref: MachineTheoremGlobalRef {
                module: name(module),
                name: name(theorem),
                export_hash: hash(byte),
                decl_interface_hash: hash(byte + 1),
            },
            universe_params: vec!["u".to_owned()],
            statement: MachineTheoremStatement {
                core_hash: hash(byte + 2),
                head: Some(imported_ref("Eq", byte + 3)),
                machine: machine.to_owned(),
            },
            modes: vec![MachineTheoremMode::Exact, MachineTheoremMode::Simp],
            suggested_candidates: Vec::new(),
            score: 0,
            axioms_used: Vec::new(),
        }
    }

    fn search_ok_fields(result: MachineTheoremSearchResult) -> MachineTheoremSearchOkFields {
        MachineTheoremSearchOkFields {
            query_fingerprint: hash(20),
            theorem_index_fingerprint: hash(21),
            search_profile_version: "mvp-zero-score-v1",
            suggestion_profile_version: "mvp-suggested-candidates-v1",
            results: vec![result],
        }
    }

    fn search_ok_response(
        results: Vec<MachineTheoremSearchResult>,
    ) -> MachineTheoremSearchResponse {
        MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
            status: MachineApiResponseStatus::Ok,
            endpoint_fields: MachineTheoremSearchOkFields {
                query_fingerprint: hash(20),
                theorem_index_fingerprint: hash(21),
                search_profile_version: "mvp-zero-score-v1",
                suggestion_profile_version: "mvp-suggested-candidates-v1",
                results,
            },
        })
    }

    fn empty_retrieval() -> AiSearchPremiseRetrieval {
        AiSearchPremiseRetrieval {
            cache_key: AiSearchRetrievalCacheKey {
                session_root_hash: hash(90),
                query_fingerprint: hash(91),
                theorem_index_fingerprint: hash(92),
            },
            cache_entries: Vec::new(),
            results: Vec::new(),
        }
    }

    fn theorem_graph_search_node(
        name_value: &str,
        decl_interface_hash: Hash,
    ) -> CertificateTheoremGraphNode {
        CertificateTheoremGraphNode {
            id: CertificateTheoremGraphNodeId {
                scope: CertificateTheoremGraphNodeScope::Local,
                module: name("Std.Nat.Basic"),
                name: name(name_value),
                decl_interface_hash,
            },
            kind: CertificateTheoremGraphNodeKind::Theorem,
            type_hash: Some(hash(150)),
            proof_hash: Some(hash(151)),
            body_hash: None,
            metadata: CertificateTheoremGraphNodeMetadata::default(),
        }
    }

    fn theorem_graph_snapshot_for_ai_search() -> CertificateTheoremGraphSnapshot {
        let add_zero = theorem_graph_search_node("Nat.add_zero", hash(11));
        let add_assoc = theorem_graph_search_node("Nat.add_assoc", hash(31));
        let mut snapshot = CertificateTheoremGraphSnapshot {
            source_module: name("Std.Nat.Basic"),
            source_export_hash: hash(10),
            source_certificate_hash: hash(160),
            extractor_version: CertificateTheoremGraphExtractorVersion::CertificateGraphV1,
            imports: Vec::new(),
            nodes: vec![add_zero.clone(), add_assoc.clone()],
            edges: vec![CertificateTheoremGraphEdge {
                from: add_assoc.id,
                to: add_zero.id,
                kind: CertificateTheoremGraphEdgeKind::MentionsType,
            }],
            graph_hash: [0; 32],
        };
        snapshot.graph_hash = crate::certificate_theorem_graph_snapshot_hash(&snapshot);
        snapshot
    }

    fn theorem_graph_snapshot_for_graph_aware_retrieval() -> CertificateTheoremGraphSnapshot {
        let mut snapshot = theorem_graph_snapshot_for_ai_search();
        let add_assoc = snapshot
            .nodes
            .iter()
            .find(|node| node.id.name == name("Nat.add_assoc"))
            .map(|node| node.id.clone())
            .unwrap();
        let add_zero = snapshot
            .nodes
            .iter()
            .find(|node| node.id.name == name("Nat.add_zero"))
            .map(|node| node.id.clone())
            .unwrap();
        for kind in [
            CertificateTheoremGraphEdgeKind::UsedBy,
            CertificateTheoremGraphEdgeKind::SimilarStatement,
            CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom,
            CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom,
            CertificateTheoremGraphEdgeKind::AxiomPath,
        ] {
            snapshot.edges.push(CertificateTheoremGraphEdge {
                from: add_assoc.clone(),
                to: add_zero.clone(),
                kind,
            });
        }
        snapshot.graph_hash = crate::certificate_theorem_graph_snapshot_hash(&snapshot);
        snapshot
    }

    fn graph_aware_retrieval_fixture() -> AiSearchPremiseRetrieval {
        let add_zero = theorem_result("zero", Vec::new());
        let mut add_assoc = theorem_result("assoc", Vec::new());
        add_assoc.global_ref.name = name("Nat.add_assoc");
        add_assoc.global_ref.export_hash = hash(10);
        add_assoc.global_ref.decl_interface_hash = hash(31);
        ai_search_premise_retrieval_from_search_ok(
            hash(99),
            MachineTheoremSearchOkFields {
                query_fingerprint: hash(20),
                theorem_index_fingerprint: hash(21),
                search_profile_version: "mvp-zero-score-v1",
                suggestion_profile_version: "mvp-suggested-candidates-v1",
                results: vec![add_zero, add_assoc],
            },
        )
    }

    fn valid_config_json() -> &'static str {
        r#"{
          "search_budget": {
            "wall_clock_ms": 30000,
            "max_nodes": 10000,
            "max_tactics_per_node": 16,
            "max_depth": 64
          },
          "per_tactic_deterministic_budget": {
            "max_tactic_steps": 64,
            "max_whnf_steps": 10000,
            "max_conversion_steps": 10000,
            "max_rewrite_steps": 100,
            "max_meta_allocations": 8,
            "max_expr_nodes": 20000
          },
          "batch_policy": {
            "max_evaluated_candidates": 16,
            "stop_after_successes": 8,
            "stop_after_failures": 16
          }
        }"#
    }

    fn batch_request_with_candidate(candidate_json: &str) -> String {
        let request = snapshot_request();
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":[{{"candidate_id":"c0","candidate":{candidate_json}}}],
              "deterministic_budget":{{
                "max_tactic_steps":64,
                "max_whnf_steps":10000,
                "max_conversion_steps":10000,
                "max_rewrite_steps":100,
                "max_meta_allocations":8,
                "max_expr_nodes":20000
              }},
              "batch_policy":{{
                "max_evaluated_candidates":16,
                "stop_after_successes":8,
                "stop_after_failures":16
              }}
            }}"#,
            request.session_id.wire(),
            request.snapshot_id.wire(),
            format_hash_string(&request.state_fingerprint),
        )
    }

    fn mvp_config() -> AiSearchMvpControllerConfig {
        parse_ai_search_mvp_controller_config(valid_config_json()).unwrap()
    }

    fn ai_search_test_envelope(
        source_index: u32,
        candidate_hash: Option<Hash>,
    ) -> AiSearchCandidateEnvelope {
        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::SimpLiteEmpty),
            source_index,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        ai_search_candidate_envelope(candidate, candidate_hash, metadata)
    }

    fn ai_search_exact_test_envelope(
        source_index: u32,
        candidate_hash: Option<Hash>,
        term: &str,
    ) -> AiSearchCandidateEnvelope {
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new(term),
        };
        let metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::LocalExact),
            source_index,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        ai_search_candidate_envelope(candidate, candidate_hash, metadata)
    }

    fn ai_search_cheap_first_test_envelope(
        source: AiSearchCandidateSource,
        builtin_kind: Option<AiSearchBuiltinKind>,
        source_index: u32,
        candidate_hash: Option<Hash>,
        candidate: MachineTacticCandidate,
    ) -> AiSearchCandidateEnvelope {
        let mut metadata = ai_search_candidate_metadata(
            source,
            builtin_kind,
            source_index,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        metadata.score = 99_999;
        metadata.display_text = Some("misleading display text is not rank evidence".to_owned());
        ai_search_candidate_envelope(candidate, candidate_hash, metadata)
    }

    fn ai_search_test_batch_request(
        candidates: Vec<AiSearchCandidateEnvelope>,
    ) -> AiSearchTacticBatchRequest {
        let snapshot = snapshot_request();
        let config = mvp_config();
        AiSearchTacticBatchRequest {
            session_id: snapshot.session_id,
            snapshot_id: snapshot.snapshot_id,
            state_fingerprint: snapshot.state_fingerprint,
            goal_id: GoalId(0),
            candidates: ai_search_assign_candidate_ids(candidates),
            deterministic_budget: config.per_tactic_deterministic_budget,
            batch_policy: config.batch_policy,
            scheduler_limits: None,
        }
    }

    fn ai_search_test_search_input(initial_snapshot: MachineProofSnapshot) -> AiSearchInput {
        let config = mvp_config();
        AiSearchInput {
            session_id: initial_snapshot.session_id.clone(),
            session_root_hash: hash(90),
            initial_snapshot,
            search_budget: config.search_budget,
            per_tactic_deterministic_budget: config.per_tactic_deterministic_budget,
            scheduler_limits: config.scheduler_limits,
            batch_policy: config.batch_policy,
        }
    }

    fn suggested_candidate(
        candidate_hash: Hash,
        candidate: MachineTacticCandidate,
    ) -> MachineSuggestedCandidate {
        MachineSuggestedCandidate {
            status: MachineSuggestedCandidateStatus::Validated,
            candidate_hash,
            candidate,
        }
    }

    fn accepted_failure(
        error_kind: FailedCandidateErrorKind,
        candidate_hash: Hash,
    ) -> AiSearchAcceptedCandidateFailure {
        AiSearchAcceptedCandidateFailure {
            error_kind,
            phase: crate::MachineApiDiagnosticPhase::TacticExecution,
            goal_id: Some(GoalId(0)),
            tactic_kind: Some(MachineApiTacticKind::Exact),
            candidate_hash,
            deterministic_budget_hash: tactic_budget_hash(
                mvp_config().per_tactic_deterministic_budget,
            ),
            diagnostic_hash: hash(55),
            retryable: false,
        }
    }

    fn compact_error(kind: MachineApiErrorKind) -> MachineApiCompactErrorWire {
        MachineApiCompactErrorWire {
            error_kind: kind,
            phase: crate::MachineApiDiagnosticPhase::TacticExecution,
            diagnostic_hash: hash(55),
            retryable: false,
            goal_id: Some(GoalId(0)),
            tactic_kind: Some(MachineApiTacticKind::SimpLite),
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
        }
    }

    fn ok_batch_response(
        request: &AiSearchTacticBatchRequest,
        results: Vec<MachineTacticBatchItemResponse>,
    ) -> MachineTacticBatchResponse {
        ok_batch_response_for(
            request.state_fingerprint,
            request.deterministic_budget,
            results,
        )
    }

    fn ok_batch_response_for(
        previous_state_fingerprint: Hash,
        deterministic_budget: TacticBudget,
        results: Vec<MachineTacticBatchItemResponse>,
    ) -> MachineTacticBatchResponse {
        let success_count = usize_to_u32(results.iter().filter(|item| item.is_success()).count());
        let failure_count = usize_to_u32(results.len()) - success_count;
        MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
            status: MachineApiResponseStatus::Ok,
            endpoint_fields: MachineTacticBatchOkFields {
                previous_state_fingerprint,
                deterministic_budget_hash: tactic_budget_hash(deterministic_budget),
                results,
                success_count,
                failure_count,
            },
        })
    }

    fn replay_ok_response(
        final_snapshot_id: SnapshotId,
        final_state_fingerprint: Hash,
    ) -> MachineReplayResponse {
        MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
            status: MachineApiResponseStatus::Ok,
            endpoint_fields: MachineReplayOkFields {
                final_snapshot_id,
                final_state_fingerprint,
            },
        })
    }

    fn replay_scheduler_stopped_response() -> MachineReplayResponse {
        MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
            status: MachineApiResponseStatus::SchedulerStopped,
            scheduler_artifact: MachineSchedulerArtifact {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Replay,
                retryable: true,
            },
            endpoint_fields: (),
        })
    }

    fn verify_ok_response() -> MachineVerifyResponse {
        MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
            status: MachineApiResponseStatus::Verified,
            endpoint_fields: verify_ok_fields(),
        })
    }

    fn verify_ok_fields() -> MachineVerifyOkFields {
        MachineVerifyOkFields {
            root_decl_interface_hash: hash(80),
            root_decl_certificate_hash: hash(81),
            root_axioms_used: Vec::new(),
            module_export_hash: hash(82),
            module_certificate_hash: hash(83),
            module_axioms_used: Vec::new(),
            certificate: certificate_payload(84),
            dependency_import_closure: Vec::new(),
            import_payload: verified_module_certificate_payload(85),
        }
    }

    fn verify_ok_envelope() -> MachineApiOkResponse<MachineVerifyOkFields> {
        MachineApiOkResponse {
            status: MachineApiResponseStatus::Verified,
            endpoint_fields: verify_ok_fields(),
        }
    }

    fn replay_and_verify_advisory_plan(
        client: &mut AiSearchFakeMachineApiClient,
        session_id: SessionId,
        plan: &AiSearchReplayPlan,
        final_snapshot_id: SnapshotId,
        final_state_fingerprint: Hash,
    ) -> MachineApiOkResponse<MachineVerifyOkFields> {
        client.push_replay_response(Ok(replay_ok_response(
            final_snapshot_id,
            final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_ok_response()));

        let replay_response = client
            .replay(&ai_search_replay_request_json(session_id.clone(), plan))
            .unwrap();
        let MachineApiResponseEnvelope::Ok(replay_ok) = replay_response else {
            panic!("expected replay ok response")
        };
        assert_eq!(replay_ok.status, MachineApiResponseStatus::Ok);

        let verify_response = client
            .verify(&ai_search_verify_request_json(
                session_id,
                replay_ok.endpoint_fields.final_snapshot_id,
                replay_ok.endpoint_fields.final_state_fingerprint,
            ))
            .unwrap();
        let MachineApiResponseEnvelope::Ok(verify_ok) = verify_response else {
            panic!("expected verify ok response")
        };
        verify_ok
    }

    fn replay_error_response(
        kind: MachineApiErrorKind,
        phase: crate::MachineApiDiagnosticPhase,
    ) -> MachineReplayResponse {
        MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
            status: MachineApiResponseStatus::Error,
            error: error_wire(kind, phase),
            endpoint_fields: (),
        }))
    }

    fn verify_error_response(
        kind: MachineApiErrorKind,
        phase: crate::MachineApiDiagnosticPhase,
    ) -> MachineVerifyResponse {
        MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
            status: MachineApiResponseStatus::Error,
            error: error_wire(kind, phase),
            endpoint_fields: (),
        }))
    }

    fn error_wire(
        kind: MachineApiErrorKind,
        phase: crate::MachineApiDiagnosticPhase,
    ) -> MachineApiErrorWire {
        MachineApiErrorWire {
            kind,
            phase,
            diagnostic_hash: hash(79),
            retryable: false,
            goal_id: None,
            tactic_kind: None,
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
        }
    }

    fn certificate_payload(byte: u8) -> MachineCertificateWirePayload {
        MachineCertificateWirePayload {
            encoding: "npa.certificate.canonical.v0.1.hex",
            bytes: format!("{byte:02x}"),
        }
    }

    fn verified_module_certificate_payload(byte: u8) -> MachineVerifiedModuleCertificatePayload {
        MachineVerifiedModuleCertificatePayload {
            module: name("Test.Module"),
            expected_export_hash: hash(byte),
            expected_certificate_hash: hash(byte + 1),
            certificate: certificate_payload(byte + 2),
        }
    }

    #[test]
    fn ai_search_snapshot_get_request_forces_include_pretty_false() {
        let source = ai_search_snapshot_get_request_json(&snapshot_request());

        let parsed = parse_machine_snapshot_get_request(&source).unwrap();

        assert!(!parsed.include_pretty);
        assert_eq!(parsed.session_id, SessionId::parse("msess_001").unwrap());
        assert_eq!(parsed.state_fingerprint, hash(1));
    }

    #[test]
    fn fake_client_records_snapshot_get_without_pretty() {
        let request = snapshot_request();
        let mut client = AiSearchFakeMachineApiClient::new();

        let err = client.get_snapshot(request.clone()).unwrap_err();

        assert_eq!(
            err,
            AiSearchMachineApiError::FakeResponseExhausted {
                endpoint: AiSearchMachineApiEndpointKind::SnapshotGet
            }
        );
        assert_eq!(
            client.calls(),
            &[AiSearchMachineApiCall::SnapshotGet {
                session_id: request.session_id,
                snapshot_id: request.snapshot_id,
                state_fingerprint: request.state_fingerprint,
                include_pretty: false,
            }]
        );
    }

    #[test]
    fn initial_snapshot_loader_uses_snapshot_boundary_and_derives_goal_summaries() {
        let request = snapshot_request();
        let snapshot = snapshot_with_goals(vec![
            goal_view(GoalId(1), 30, 8, 0, 0, Some(imported_ref("Eq", 40))),
            goal_view(GoalId(0), 31, 3, 1, 2, None),
        ]);
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: snapshot.clone(),
        }));

        let loaded = load_ai_search_initial_snapshot(&mut client, request.clone()).unwrap();

        assert_eq!(loaded.snapshot, snapshot);
        assert_eq!(loaded.goals.len(), 2);
        assert_eq!(loaded.goals[0].goal_id, GoalId(1));
        assert_eq!(loaded.goals[0].open_goal_index, 0);
        assert_eq!(loaded.goals[0].expr_size, 8);
        assert_eq!(loaded.goals[0].target_free_local_count, 0);
        assert_eq!(
            client.calls(),
            &[AiSearchMachineApiCall::SnapshotGet {
                session_id: request.session_id,
                snapshot_id: request.snapshot_id,
                state_fingerprint: request.state_fingerprint,
                include_pretty: false,
            }]
        );
    }

    #[test]
    fn goal_selection_uses_derived_snapshot_fields_only() {
        let snapshot = snapshot_with_goals(vec![
            goal_view(GoalId(2), 30, 10, 0, 1, Some(imported_ref("Eq", 40))),
            goal_view(GoalId(1), 31, 5, 2, 0, Some(imported_ref("And", 42))),
            goal_view(GoalId(0), 32, 5, 1, 0, None),
        ]);

        let summaries = ai_search_goal_summaries(&snapshot);
        let selected = select_ai_search_goal(&snapshot).unwrap();

        assert_eq!(summaries[0].goal_id, GoalId(2));
        assert_eq!(summaries[1].open_goal_index, 1);
        assert_eq!(summaries[2].target_hash, hash(44));
        assert_eq!(selected.goal_id, GoalId(0));
        assert_eq!(selected.expr_size, 5);
        assert_eq!(selected.target_free_local_count, 1);
    }

    #[test]
    fn ai_search_mvp_premise_query_is_fixed_machine_api_search_shape() {
        let source = ai_search_mvp_premise_query_json(&AiSearchPremiseQueryRequest {
            session_id: SessionId::parse("msess_001").unwrap(),
            snapshot_id: SnapshotId::from_state_fingerprint(hash(1)),
            state_fingerprint: hash(1),
            goal_id: GoalId(7),
        });

        let parsed = parse_machine_theorem_search_request(&source).unwrap();

        assert_eq!(
            parsed.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
            ]
        );
        assert_eq!(parsed.limit, 32);
        assert!(parsed.filters.exclude_axioms);
        assert_eq!(
            parsed.filters.allowed_modules,
            MachineAllowedModulesFilter::AllDirect
        );
        assert!(!source.contains("allowed_modules"));
    }

    #[test]
    fn retrieve_ai_search_premises_uses_fixed_query_and_preserves_machine_api_results() {
        let request = AiSearchPremiseQueryRequest {
            session_id: SessionId::parse("msess_001").unwrap(),
            snapshot_id: SnapshotId::from_state_fingerprint(hash(1)),
            state_fingerprint: hash(1),
            goal_id: GoalId(7),
        };
        let search = search_ok_fields(theorem_result("display", Vec::new()));
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_search_for_goal_response(Ok(MachineApiResponseEnvelope::Ok(
            MachineApiOkResponse {
                status: MachineApiResponseStatus::Ok,
                endpoint_fields: search.clone(),
            },
        )));

        let retrieval = retrieve_ai_search_premises(&mut client, &request, hash(99)).unwrap();

        assert_eq!(
            retrieval.cache_key,
            AiSearchRetrievalCacheKey {
                session_root_hash: hash(99),
                query_fingerprint: hash(20),
                theorem_index_fingerprint: hash(21),
            }
        );
        assert_eq!(retrieval.cache_entries.len(), 1);
        assert_eq!(retrieval.results, search.results);
        assert_eq!(client.calls().len(), 1);
        let AiSearchMachineApiCall::SearchForGoal { source } = &client.calls()[0] else {
            panic!("expected search_for_goal call");
        };
        let parsed = parse_machine_theorem_search_request(source).unwrap();
        assert_eq!(parsed.goal_id, GoalId(7));
        assert_eq!(
            parsed.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
            ]
        );
        assert_eq!(
            parsed.filters.allowed_modules,
            MachineAllowedModulesFilter::AllDirect
        );
    }

    #[test]
    fn premise_cache_entries_use_verified_metadata_not_display_or_suggestions() {
        let suggested = MachineSuggestedCandidate {
            status: MachineSuggestedCandidateStatus::Validated,
            candidate_hash: hash(16),
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
        };
        let mut search = search_ok_fields(theorem_result("pretty theorem text", vec![suggested]));

        let entries = ai_search_premise_cache_entries(&search);
        let usages = ai_search_premise_usages(&search);

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].premise_ref.module, name("Std.Nat.Basic"));
        assert_eq!(entries[0].premise_ref.name, name("Nat.add_zero"));
        assert_eq!(entries[0].universe_params, vec!["u".to_owned()]);
        assert_eq!(entries[0].statement_core_hash, hash(12));
        assert_eq!(entries[0].statement_head, Some(imported_ref("Eq", 13)));
        assert_eq!(
            entries[0].modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Simp]
        );
        assert_eq!(entries[0].response_index, 0);
        assert_eq!(
            usages[0],
            AiSearchPremiseUsage {
                premise_ref: entries[0].premise_ref.clone(),
                universe_params: entries[0].universe_params.clone(),
                statement_core_hash: entries[0].statement_core_hash,
                axioms_used: entries[0].axioms_used.clone(),
            }
        );

        let original_entries = entries;
        search.results[0].statement.machine = "different display".to_owned();
        search.results[0].score = 99;
        search.results[0].suggested_candidates.clear();

        assert_eq!(ai_search_premise_cache_entries(&search), original_entries);
    }

    #[test]
    fn retrieval_cache_key_uses_machine_api_fingerprints() {
        let search = search_ok_fields(theorem_result("display", Vec::new()));

        let key = ai_search_retrieval_cache_key(hash(99), &search);

        assert_eq!(
            key,
            AiSearchRetrievalCacheKey {
                session_root_hash: hash(99),
                query_fingerprint: hash(20),
                theorem_index_fingerprint: hash(21),
            }
        );
    }

    #[test]
    fn ai_search_graph_ranking_uses_precomputed_snapshot_with_missing_snapshot_fallback() {
        let retrieval = graph_aware_retrieval_fixture();

        let missing = ai_search_premise_graph_ranking_features(&retrieval, None);
        assert_eq!(
            missing.fallback,
            AiSearchPremiseGraphRankingFallback::SnapshotMissing
        );
        assert_eq!(missing.graph_snapshot_hash, None);
        assert_eq!(missing.entries.len(), 2);
        assert_eq!(missing.entries[0].response_index, 0);
        assert_eq!(missing.entries[0].graph_rank, 0);
        assert_eq!(missing.entries[0].graph_node, None);
        assert_eq!(missing.entries[0].graph_score, 0);

        let snapshot = theorem_graph_snapshot_for_ai_search();
        let ranked = ai_search_premise_graph_ranking_features(&retrieval, Some(&snapshot));

        assert_eq!(
            ranked.fallback,
            AiSearchPremiseGraphRankingFallback::PrecomputedSnapshot
        );
        assert_eq!(ranked.graph_snapshot_hash, Some(snapshot.graph_hash));
        assert_eq!(ranked.entries.len(), 2);
        assert_eq!(ranked.entries[0].premise_ref.name, name("Nat.add_assoc"));
        assert_eq!(ranked.entries[0].response_index, 1);
        assert_eq!(ranked.entries[0].graph_rank, 0);
        assert_eq!(ranked.entries[0].direct_dependency_count, 1);
        assert_eq!(
            ranked.entries[0].graph_score_components,
            AiSearchPremiseGraphScoreComponents {
                direct_dependency_count: 1,
                transitive_dependency_count: 1,
                ..AiSearchPremiseGraphScoreComponents::default()
            }
        );
        assert_eq!(
            ranked.entries[0].graph_source,
            AiSearchPremiseGraphRankingSource::VerifiedIndexAndGraphEdgeExpansion
        );
        assert_eq!(ranked.entries[0].graph_score, 1_250);
        assert!(ranked.entries[0].graph_node.is_some());
        assert_eq!(ranked.entries[1].premise_ref.name, name("Nat.add_zero"));
    }

    #[test]
    fn graph_aware_retrieval_records_edge_components_and_sidecar_source() {
        let retrieval = graph_aware_retrieval_fixture();
        let snapshot = theorem_graph_snapshot_for_graph_aware_retrieval();

        let ranked = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            Some(&snapshot),
            AiSearchPremiseGraphRankingOptions {
                expected_graph_snapshot_hash: Some(snapshot.graph_hash),
                stale_policy: AiSearchPremiseGraphSnapshotStalePolicy::Reject,
            },
        )
        .unwrap();

        assert_eq!(ranked.graph_snapshot_hash, Some(snapshot.graph_hash));
        assert_eq!(
            ranked.fallback,
            AiSearchPremiseGraphRankingFallback::PrecomputedSnapshot
        );
        assert_eq!(ranked.entries[0].premise_ref.name, name("Nat.add_assoc"));
        assert_eq!(
            ranked.entries[0].graph_source,
            AiSearchPremiseGraphRankingSource::VerifiedIndexAndGraphEdgeExpansion
        );
        assert_eq!(
            ranked.entries[0].graph_score_components,
            AiSearchPremiseGraphScoreComponents {
                direct_dependency_count: 1,
                transitive_dependency_count: 1,
                used_by_count: 1,
                similar_statement_count: 1,
                direct_axiom_path_count: 1,
                transitive_axiom_path_count: 1,
            }
        );
        assert_eq!(ranked.entries[0].graph_edges.direct_dependencies.len(), 1);
        assert_eq!(
            ranked.entries[0].graph_edges.transitive_dependencies.len(),
            1
        );
        assert_eq!(ranked.entries[0].graph_edges.used_by.len(), 1);
        assert_eq!(ranked.entries[0].graph_edges.similar_statements.len(), 1);
        assert_eq!(ranked.entries[0].graph_edges.direct_axiom_paths.len(), 1);
        assert_eq!(
            ranked.entries[0].graph_edges.transitive_axiom_paths.len(),
            1
        );
        assert_eq!(ranked.entries[0].graph_score, 2_700);
        assert_eq!(
            ranked.entries[1].graph_source,
            AiSearchPremiseGraphRankingSource::VerifiedIndexMatch
        );
        assert_eq!(ranked.entries[1].graph_score, 0);
    }

    #[test]
    fn graph_aware_retrieval_rejects_or_ignores_stale_graph_snapshot_by_policy() {
        let retrieval = graph_aware_retrieval_fixture();
        let snapshot = theorem_graph_snapshot_for_ai_search();
        let expected = hash(222);

        let err = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            Some(&snapshot),
            AiSearchPremiseGraphRankingOptions {
                expected_graph_snapshot_hash: Some(expected),
                stale_policy: AiSearchPremiseGraphSnapshotStalePolicy::Reject,
            },
        )
        .unwrap_err();
        assert_eq!(
            err,
            AiSearchPremiseGraphRankingError::GraphSnapshotStale {
                expected,
                actual: snapshot.graph_hash,
            }
        );

        let ignored = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            Some(&snapshot),
            AiSearchPremiseGraphRankingOptions {
                expected_graph_snapshot_hash: Some(expected),
                stale_policy: AiSearchPremiseGraphSnapshotStalePolicy::EmptyContribution,
            },
        )
        .unwrap();
        assert_eq!(
            ignored.fallback,
            AiSearchPremiseGraphRankingFallback::SnapshotStaleIgnored
        );
        assert_eq!(ignored.graph_snapshot_hash, None);
        assert!(ignored.entries.iter().all(|entry| {
            entry.graph_score == 0
                && entry.graph_source == AiSearchPremiseGraphRankingSource::VerifiedIndexMatch
                && entry.graph_edges == AiSearchPremiseGraphEdgeMetadata::default()
        }));
    }

    #[test]
    fn graph_aware_retrieval_orders_deterministically_when_graph_scores_tie() {
        let retrieval = graph_aware_retrieval_fixture();
        let mut snapshot = theorem_graph_snapshot_for_ai_search();
        snapshot.edges.clear();
        snapshot.graph_hash = crate::certificate_theorem_graph_snapshot_hash(&snapshot);

        let first = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            Some(&snapshot),
            AiSearchPremiseGraphRankingOptions::default(),
        )
        .unwrap();
        let second = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            Some(&snapshot),
            AiSearchPremiseGraphRankingOptions::default(),
        )
        .unwrap();

        assert_eq!(first, second);
        assert_eq!(first.entries.len(), 2);
        assert_eq!(first.entries[0].response_index, 0);
        assert_eq!(first.entries[0].premise_ref.name, name("Nat.add_zero"));
        assert_eq!(first.entries[1].response_index, 1);
        assert_eq!(first.entries[1].premise_ref.name, name("Nat.add_assoc"));
        assert!(first.entries.iter().all(|entry| entry.graph_score == 0));
    }

    #[test]
    fn graph_aware_retrieval_graph_unavailable_fallback_is_empty_contribution() {
        let retrieval = graph_aware_retrieval_fixture();

        let ranked = ai_search_premise_graph_aware_retrieval(
            &retrieval,
            None,
            AiSearchPremiseGraphRankingOptions::default(),
        )
        .unwrap();

        assert_eq!(
            ranked.fallback,
            AiSearchPremiseGraphRankingFallback::SnapshotMissing
        );
        assert_eq!(ranked.graph_snapshot_hash, None);
        assert!(ranked.entries.iter().all(|entry| {
            entry.graph_score == 0
                && entry.graph_node.is_none()
                && entry.graph_edges == AiSearchPremiseGraphEdgeMetadata::default()
        }));
    }

    #[test]
    fn ai_search_graph_score_sidecar_does_not_change_candidate_hashes_or_order() {
        let suggested = MachineSuggestedCandidate {
            status: MachineSuggestedCandidateStatus::Validated,
            candidate_hash: hash(40),
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
        };
        let retrieval = ai_search_premise_retrieval_from_search_ok(
            hash(99),
            search_ok_fields(theorem_result("display", vec![suggested])),
        );
        let goal = goal_view(GoalId(0), 30, 5, 0, 0, None);

        let before = ai_search_mvp_candidate_generation(&goal, &retrieval);
        let graph_features = ai_search_premise_graph_ranking_features(
            &retrieval,
            Some(&theorem_graph_snapshot_for_ai_search()),
        );
        let after = ai_search_mvp_candidate_generation(&goal, &retrieval);

        assert_eq!(
            graph_features.fallback,
            AiSearchPremiseGraphRankingFallback::PrecomputedSnapshot
        );
        assert_eq!(before, after);
        assert_eq!(
            before.accepted[0].ai_search_candidate_payload_hash,
            ai_search_candidate_payload_hash(&MachineTacticCandidate::SimpLite {
                rules: Vec::new()
            })
        );
    }

    #[test]
    fn candidate_payload_json_is_machine_api_candidate_shape_and_hash_is_payload_only() {
        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let payload = ai_search_candidate_payload_json(&candidate);

        assert_eq!(payload, r#"{"kind":"simp-lite","rules":[]}"#);
        parse_machine_tactic_batch_request(&batch_request_with_candidate(&payload)).unwrap();

        let mut metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::SimpLiteEmpty),
            0,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        metadata.score = 999;
        metadata.display_text = Some("unsafe display is not payload".to_owned());
        let first = ai_search_candidate_envelope(candidate.clone(), None, metadata);
        let second = ai_search_candidate_envelope(
            candidate,
            Some(hash(77)),
            ai_search_candidate_metadata(
                AiSearchCandidateSource::MachineApiSuggested,
                None,
                7,
                Vec::new(),
                Vec::new(),
                &MachineTacticCandidate::SimpLite { rules: Vec::new() },
            ),
        );

        assert_eq!(
            first.ai_search_candidate_payload_hash,
            second.ai_search_candidate_payload_hash
        );
        assert!(!payload.contains("candidate_hash"));
        assert!(!payload.contains("display"));
        assert!(!payload.contains("premises"));
    }

    fn assert_p8h00_phase8_audit_fields_absent(label: &str, source: &str) {
        for forbidden in [
            "independent_checker",
            "checker_profile",
            "reference",
            "external",
            "audit",
            "sidecar",
            "challenge",
            "normalized_result",
            "release_policy",
        ] {
            assert!(
                !source.contains(forbidden),
                "{label} must not synchronously carry audit field {forbidden}"
            );
        }
    }

    fn assert_p9h00_phase9_human_heavy_fields_absent(label: &str, source: &str) {
        for forbidden in [
            "human_boundary",
            "advanced_ai",
            "theorem_graph",
            "graph_snapshot",
            "smt_solver",
            "smt_reconstruction",
            "smt_proof",
            "formalization",
            "confidence",
            "sidecar",
            "independent_checker",
            "external_checker",
            "release_audit",
        ] {
            assert!(
                !source.contains(forbidden),
                "{label} must not synchronously carry advanced human-boundary heavy field {forbidden}"
            );
        }
    }

    #[test]
    fn p8h00_ai_fast_path_request_shapes_exclude_phase8_audit_metadata() {
        let request = ai_search_test_batch_request(vec![ai_search_test_envelope(0, None)]);
        let batch_source = ai_search_tactic_batch_request_json(&request);
        parse_machine_tactic_batch_request(&batch_source).unwrap();
        assert_p8h00_phase8_audit_fields_absent("tactic_batch", &batch_source);

        let batch_response = ok_batch_response(
            &request,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                next_state_fingerprint: hash(42),
                proof_delta_hash: hash(43),
            }],
        );
        let MachineApiResponseEnvelope::Ok(ok_batch) = &batch_response else {
            panic!("test fixture must be a successful machine batch response");
        };
        assert_eq!(
            ok_batch.endpoint_fields.previous_state_fingerprint,
            request.state_fingerprint
        );
        assert!(matches!(
            &ok_batch.endpoint_fields.results[0],
            MachineTacticBatchItemResponse::Success {
                candidate_hash,
                next_state_fingerprint,
                ..
            } if *candidate_hash == hash(40) && *next_state_fingerprint == hash(42)
        ));
        let evaluation =
            ai_search_evaluate_tactic_batch_response(&request, batch_response).unwrap();
        assert_eq!(
            evaluation.replay_steps[0].previous_state_fingerprint,
            request.state_fingerprint
        );
        assert_eq!(evaluation.replay_steps[0].candidate_hash, hash(40));
        assert_eq!(evaluation.replay_steps[0].next_state_fingerprint, hash(42));

        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let candidate_payload = ai_search_candidate_payload_json(&candidate);
        assert_p8h00_phase8_audit_fields_absent("candidate_payload", &candidate_payload);
        assert_eq!(
            ai_search_candidate_payload_hash(&candidate),
            ai_search_candidate_payload_hash(&MachineTacticCandidate::SimpLite {
                rules: Vec::new()
            })
        );

        let step = AiSearchReplayStep {
            previous_state_fingerprint: request.state_fingerprint,
            goal_id: request.goal_id,
            candidate,
            deterministic_budget: request.deterministic_budget,
            candidate_hash: hash(40),
            deterministic_budget_hash: tactic_budget_hash(request.deterministic_budget),
            proof_delta_hash: hash(41),
            next_state_fingerprint: hash(42),
        };
        let replay_plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(90),
            initial_state_fingerprint: request.state_fingerprint,
            steps: vec![step],
            final_state_fingerprint: hash(42),
        };
        let replay_source = ai_search_replay_request_json(request.session_id.clone(), &replay_plan);
        parse_machine_replay_request(&replay_source).unwrap();
        assert_p8h00_phase8_audit_fields_absent("replay", &replay_source);

        let verify_source = ai_search_verify_request_json(
            request.session_id.clone(),
            request.snapshot_id,
            request.state_fingerprint,
        );
        parse_machine_verify_request(&verify_source).unwrap();
        assert_p8h00_phase8_audit_fields_absent("verify", &verify_source);

        let snapshot_source = ai_search_snapshot_get_request_json(&snapshot_request());
        parse_machine_snapshot_get_request(&snapshot_source).unwrap();
        assert_p8h00_phase8_audit_fields_absent("snapshot_get", &snapshot_source);

        let premise_source = ai_search_mvp_premise_query_json(&AiSearchPremiseQueryRequest {
            session_id: request.session_id.clone(),
            snapshot_id: request.snapshot_id,
            state_fingerprint: request.state_fingerprint,
            goal_id: request.goal_id,
        });
        parse_machine_theorem_search_request(&premise_source).unwrap();
        assert_p8h00_phase8_audit_fields_absent("premise_query", &premise_source);

        let tampered_batch = batch_source.replace(
            r#""candidates""#,
            r#""checker_profile":"reference","candidates""#,
        );
        assert!(parse_machine_tactic_batch_request(&tampered_batch).is_err());

        let tampered_verify =
            verify_source.replace(r#""mode""#, r#""audit_summary":"checked","mode""#);
        assert!(parse_machine_verify_request(&tampered_verify).is_err());
    }

    #[test]
    fn p9h00_ai_fast_path_request_shapes_exclude_phase9_human_heavy_checks() {
        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let mut metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::MachineApiSuggested,
            None,
            0,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        metadata.score = 99_999;
        metadata.display_text = Some(
            "human_boundary independent_checker external_checker release_audit smt_solver \
             theorem_graph formalization confidence sidecar"
                .to_owned(),
        );
        let request = ai_search_test_batch_request(vec![ai_search_candidate_envelope(
            candidate.clone(),
            Some(hash(77)),
            metadata,
        )]);
        let batch_source = ai_search_tactic_batch_request_json(&request);
        let parsed_batch = parse_machine_tactic_batch_request(&batch_source).unwrap();
        assert_eq!(parsed_batch.state_fingerprint, request.state_fingerprint);
        assert_p9h00_phase9_human_heavy_fields_absent("tactic_batch", &batch_source);

        let payload_hash = ai_search_candidate_payload_hash(&candidate);
        assert_eq!(
            payload_hash,
            ai_search_candidate_payload_hash(&MachineTacticCandidate::SimpLite {
                rules: Vec::new()
            })
        );
        let candidate_payload = ai_search_candidate_payload_json(&candidate);
        assert_p9h00_phase9_human_heavy_fields_absent("candidate_payload", &candidate_payload);

        let batch_response = ok_batch_response(
            &request,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(77),
                next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                next_state_fingerprint: hash(42),
                proof_delta_hash: hash(43),
            }],
        );
        let evaluation =
            ai_search_evaluate_tactic_batch_response(&request, batch_response).unwrap();
        assert_eq!(
            evaluation.replay_steps[0].previous_state_fingerprint,
            request.state_fingerprint
        );
        assert_eq!(evaluation.replay_steps[0].candidate_hash, hash(77));
        assert_eq!(evaluation.replay_steps[0].next_state_fingerprint, hash(42));

        let replay_plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(90),
            initial_state_fingerprint: request.state_fingerprint,
            steps: evaluation.replay_steps,
            final_state_fingerprint: hash(42),
        };
        let replay_source = ai_search_replay_request_json(request.session_id.clone(), &replay_plan);
        parse_machine_replay_request(&replay_source).unwrap();
        assert_p9h00_phase9_human_heavy_fields_absent("replay", &replay_source);

        let verify_source = ai_search_verify_request_json(
            request.session_id.clone(),
            request.snapshot_id,
            request.state_fingerprint,
        );
        let parsed_verify = parse_machine_verify_request(&verify_source).unwrap();
        assert_eq!(parsed_verify.state_fingerprint, request.state_fingerprint);
        assert_p9h00_phase9_human_heavy_fields_absent("verify", &verify_source);

        let snapshot_source = ai_search_snapshot_get_request_json(&snapshot_request());
        let parsed_snapshot = parse_machine_snapshot_get_request(&snapshot_source).unwrap();
        assert_eq!(
            parsed_snapshot.state_fingerprint,
            snapshot_request().state_fingerprint
        );
        assert_p9h00_phase9_human_heavy_fields_absent("snapshot_get", &snapshot_source);

        let premise_source = ai_search_mvp_premise_query_json(&AiSearchPremiseQueryRequest {
            session_id: request.session_id.clone(),
            snapshot_id: request.snapshot_id,
            state_fingerprint: request.state_fingerprint,
            goal_id: request.goal_id,
        });
        parse_machine_theorem_search_request(&premise_source).unwrap();
        assert_p9h00_phase9_human_heavy_fields_absent("premise_query", &premise_source);

        let tampered_batch = batch_source.replace(
            r#""candidates""#,
            r#""human_boundary":"release_audit","candidates""#,
        );
        assert!(parse_machine_tactic_batch_request(&tampered_batch).is_err());

        let tampered_replay =
            replay_source.replace(r#""plan""#, r#""theorem_graph":"snapshot","plan""#);
        assert!(parse_machine_replay_request(&tampered_replay).is_err());

        let tampered_verify =
            verify_source.replace(r#""mode""#, r#""smt_reconstruction":"done","mode""#);
        assert!(parse_machine_verify_request(&tampered_verify).is_err());

        let tampered_snapshot = snapshot_source.replace(
            r#""include_pretty""#,
            r#""formalization_confidence":99,"include_pretty""#,
        );
        assert!(parse_machine_snapshot_get_request(&tampered_snapshot).is_err());
    }

    #[test]
    fn candidate_payload_json_uses_canonical_object_key_order() {
        let apply = MachineTacticCandidate::Apply {
            head: TacticHead::Local {
                name: "f".to_owned(),
            },
            universe_args: Vec::new(),
            args: vec![
                CandidateApplyArg::Term(RawMachineTerm::new("h\n")),
                CandidateApplyArg::Subgoal { name_hint: None },
                CandidateApplyArg::InferFromTarget,
            ],
        };
        let apply_payload = ai_search_candidate_payload_json(&apply);

        assert_eq!(
            apply_payload,
            r#"{"args":[{"mode":"term","term":{"source":"h\u000a"}},{"mode":"subgoal","name_hint":null},{"mode":"infer_from_target"}],"head":{"local":{"name":"f"}},"kind":"apply","universe_args":[]}"#
        );
        parse_machine_tactic_batch_request(&batch_request_with_candidate(&apply_payload)).unwrap();

        let rw = MachineTacticCandidate::Rewrite {
            rule: CandidateRewriteRuleRef {
                head: TacticHead::Imported {
                    name: name("Nat.add_zero"),
                    decl_interface_hash: hash(50),
                },
                universe_args: Vec::new(),
                args: vec![CandidateApplyArg::InferFromTarget],
            },
            direction: RewriteDirection::Forward,
            site: RewriteSite::EqTargetLeft,
        };
        let rw_payload = ai_search_candidate_payload_json(&rw);

        assert_eq!(
            rw_payload,
            format!(
                r#"{{"direction":"forward","kind":"rw","rule":{{"args":[{{"mode":"infer_from_target"}}],"head":{{"imported":{{"decl_interface_hash":{},"name":"Nat.add_zero"}}}},"universe_args":[]}},"site":"eq_target_left"}}"#,
                json_string(&format_hash_string(&hash(50)))
            )
        );
        parse_machine_tactic_batch_request(&batch_request_with_candidate(&rw_payload)).unwrap();
    }

    #[test]
    fn candidate_metadata_matches_ai_search_score_and_repair_shape() {
        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let mut metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Repair,
            None,
            0,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        metadata.score = -1;
        metadata.repair = Some(AiSearchCandidateRepairMetadata {
            parent_candidate_hash: hash(60),
            error_kind: FailedCandidateErrorKind::TypeMismatch,
            repair_depth: 1,
            chain_tried_payload_hashes: vec![hash(61)],
            premise_retrieval: None,
        });

        assert_eq!(metadata.score, -1);
        assert_eq!(
            metadata.repair,
            Some(AiSearchCandidateRepairMetadata {
                parent_candidate_hash: hash(60),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                repair_depth: 1,
                chain_tried_payload_hashes: vec![hash(61)],
                premise_retrieval: None,
            })
        );
    }

    #[test]
    fn suggested_candidate_envelopes_flatten_machine_api_results_and_preserve_hashes() {
        let suggested = MachineSuggestedCandidate {
            status: MachineSuggestedCandidateStatus::Validated,
            candidate_hash: hash(40),
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
        };
        let mut result = theorem_result("display", vec![suggested]);
        result.score = 999;

        let envelopes = ai_search_suggested_candidate_envelopes(&[result.clone()]);

        assert_eq!(envelopes.len(), 1);
        assert_eq!(envelopes[0].candidate_hash, None);
        assert_eq!(result.suggested_candidates[0].candidate_hash, hash(40));
        assert_eq!(
            envelopes[0].metadata.source,
            AiSearchCandidateSource::MachineApiSuggested
        );
        assert_eq!(
            envelopes[0].metadata.rank,
            AiSearchCandidateRankMetadata {
                cheap_first_stage: AiSearchCheapFirstStage::SimpLite,
                stage_rank: 5,
                skip_reason: None,
                source_rank: 0,
                source_index: 0,
                builtin_kind_rank: 255
            }
        );
        assert_eq!(envelopes[0].metadata.score, 0);
        assert_eq!(envelopes[0].metadata.premises_used.len(), 1);
        assert_eq!(
            envelopes[0].metadata.premises_used[0].premise_ref,
            ai_search_premise_ref(&result)
        );
        assert_eq!(
            envelopes[0].metadata.trust_flags.uses_axioms,
            result.axioms_used
        );
    }

    #[test]
    fn cheap_first_stage_order_matches_ws11_t01_with_design_insertions() {
        assert_eq!(
            AI_SEARCH_CHEAP_FIRST_STAGE_ORDER,
            &[
                AiSearchCheapFirstStage::LocalExact,
                AiSearchCheapFirstStage::KnownExact,
                AiSearchCheapFirstStage::ReflexivityComputation,
                AiSearchCheapFirstStage::FiniteDecide,
                AiSearchCheapFirstStage::Rewrite,
                AiSearchCheapFirstStage::SimpLite,
                AiSearchCheapFirstStage::RingOmega,
                AiSearchCheapFirstStage::Bitblast,
                AiSearchCheapFirstStage::Smt,
                AiSearchCheapFirstStage::Apply,
                AiSearchCheapFirstStage::Constructor,
                AiSearchCheapFirstStage::Cases,
                AiSearchCheapFirstStage::Induction,
                AiSearchCheapFirstStage::Solver,
                AiSearchCheapFirstStage::ExplicitTerm,
                AiSearchCheapFirstStage::LocalLemma,
                AiSearchCheapFirstStage::NewLibraryTheorem,
            ]
        );
        for (rank, stage) in AI_SEARCH_CHEAP_FIRST_STAGE_ORDER.iter().enumerate() {
            assert_eq!(ai_search_cheap_first_stage_rank(*stage), rank as u8);
        }
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::Solver),
            Some(AiSearchCheapFirstSkipReason::ReservedUntypedSolverBucket)
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::FiniteDecide),
            None
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::RingOmega),
            None
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::Bitblast),
            None
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::Smt),
            None
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::NewLibraryTheorem),
            Some(AiSearchCheapFirstSkipReason::DeferredToLibraryGrowth)
        );
        assert_eq!(
            ai_search_cheap_first_skip_reason(AiSearchCheapFirstStage::Apply),
            None
        );
        assert_eq!(
            AiSearchCheapFirstStage::ReflexivityComputation.as_str(),
            "reflexivity_computation"
        );
    }

    #[test]
    fn cheap_first_stage_classification_uses_typed_machine_candidates() {
        let candidates = [
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Builtin,
                Some(AiSearchBuiltinKind::LocalExact),
                0,
                None,
                MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("h"),
                },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::MachineApiSuggested,
                None,
                0,
                None,
                MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("Nat.zero"),
                },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Builtin,
                Some(AiSearchBuiltinKind::Intro),
                0,
                None,
                MachineTacticCandidate::Intro {
                    name: "x".to_owned(),
                },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::MachineApiSuggested,
                None,
                0,
                None,
                MachineTacticCandidate::Rewrite {
                    rule: CandidateRewriteRuleRef {
                        head: TacticHead::Imported {
                            name: name("Nat.add_zero"),
                            decl_interface_hash: hash(20),
                        },
                        universe_args: Vec::new(),
                        args: Vec::new(),
                    },
                    direction: RewriteDirection::Forward,
                    site: RewriteSite::EqTargetLeft,
                },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Builtin,
                Some(AiSearchBuiltinKind::SimpLiteEmpty),
                0,
                None,
                MachineTacticCandidate::SimpLite { rules: Vec::new() },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::MachineApiSuggested,
                None,
                0,
                None,
                MachineTacticCandidate::Apply {
                    head: TacticHead::Local {
                        name: "f".to_owned(),
                    },
                    universe_args: Vec::new(),
                    args: vec![CandidateApplyArg::InferFromTarget],
                },
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::Constructor(npa_tactic::ConstructorPayload {
                    selection: ConstructorSelection::Auto,
                    max_new_goals: Some(2),
                }),
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::Cases(CasesPayload {
                    major_local: "h".to_owned(),
                    motive: None,
                    branch_names: vec!["left".to_owned(), "right".to_owned()],
                    max_new_goals: Some(2),
                }),
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::GeneralInduction(GeneralInductionPayload {
                    major_local: "n".to_owned(),
                    recursor: TacticHead::Imported {
                        name: name("Nat.rec"),
                        decl_interface_hash: hash(21),
                    },
                    motive: None,
                    generalized_locals: Vec::new(),
                    branch_names: vec!["zero".to_owned(), "succ".to_owned()],
                    max_new_goals: 2,
                }),
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::Omega,
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Model,
                None,
                0,
                None,
                MachineTacticCandidate::Refine(RefinePayload {
                    term: RawMachineTerm::new("proof"),
                    max_holes: Some(0),
                }),
            ),
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::Have(HavePayload {
                    name: "h2".to_owned(),
                    ty: RawMachineTerm::new("Prop"),
                    proof: LocalLemmaProof::ChildGoal,
                    insertion: LocalLemmaInsertionPolicy::AfterCurrent,
                }),
            ),
        ];
        let stages = candidates
            .iter()
            .map(|candidate| candidate.metadata.rank.cheap_first_stage)
            .collect::<Vec<_>>();

        assert_eq!(
            stages,
            vec![
                AiSearchCheapFirstStage::LocalExact,
                AiSearchCheapFirstStage::KnownExact,
                AiSearchCheapFirstStage::ReflexivityComputation,
                AiSearchCheapFirstStage::Rewrite,
                AiSearchCheapFirstStage::SimpLite,
                AiSearchCheapFirstStage::Apply,
                AiSearchCheapFirstStage::Constructor,
                AiSearchCheapFirstStage::Cases,
                AiSearchCheapFirstStage::Induction,
                AiSearchCheapFirstStage::RingOmega,
                AiSearchCheapFirstStage::ExplicitTerm,
                AiSearchCheapFirstStage::LocalLemma,
            ]
        );
        assert_eq!(candidates[9].metadata.rank.skip_reason, None);
    }

    #[test]
    fn cheap_first_budget_defaults_cover_stage_order_and_stop_policy() {
        for stage in AI_SEARCH_CHEAP_FIRST_STAGE_ORDER {
            let budget = ai_search_cheap_first_stage_budget(*stage);
            assert_eq!(budget.stage, *stage);
            assert_eq!(
                budget.skip_reason,
                ai_search_cheap_first_skip_reason(*stage)
            );

            if budget.skip_reason.is_some() {
                assert_eq!(budget.max_candidate_count, 0);
                assert_eq!(budget.max_new_goals, 0);
                assert_eq!(budget.batch_policy, None);
                assert_eq!(budget.deterministic_budget.max_tactic_steps, 0);
                continue;
            }

            assert!(budget.max_candidate_count > 0);
            let policy = budget.batch_policy.unwrap();
            assert_eq!(policy.max_evaluated_candidates, budget.max_candidate_count);
            assert_eq!(policy.stop_after_successes, 1);
            assert_eq!(policy.stop_after_failures, budget.max_candidate_count);
            assert!(budget.deterministic_budget.max_tactic_steps > 0);
            assert_eq!(
                tactic_budget_hash(budget.deterministic_budget),
                tactic_budget_hash(ai_search_cheap_first_stage_budget(*stage).deterministic_budget)
            );
        }

        assert_eq!(
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::LocalExact).max_new_goals,
            0
        );
        assert!(
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::Apply).max_new_goals
                > ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::KnownExact)
                    .max_new_goals
        );
        assert!(
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::Induction)
                .deterministic_budget
                .max_tactic_steps
                > ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::Apply)
                    .deterministic_budget
                    .max_tactic_steps
        );
    }

    #[test]
    fn cheap_first_budget_request_caps_candidates_and_filters_new_goal_overflow() {
        let snapshot = snapshot_request();
        let local_lemma_budget =
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::LocalLemma);
        let local_lemma_candidate = |name: &str, source_index| {
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                source_index,
                Some(hash((80 + source_index) as u8)),
                MachineTacticCandidate::Have(HavePayload {
                    name: name.to_owned(),
                    ty: RawMachineTerm::new("Prop"),
                    proof: LocalLemmaProof::ChildGoal,
                    insertion: LocalLemmaInsertionPolicy::AfterCurrent,
                }),
            )
        };

        let request = ai_search_cheap_first_tactic_batch_request(
            snapshot.session_id.clone(),
            snapshot.snapshot_id,
            snapshot.state_fingerprint,
            GoalId(0),
            AiSearchCheapFirstStage::LocalLemma,
            vec![
                local_lemma_candidate("late", 2),
                ai_search_exact_test_envelope(0, None, "h"),
                local_lemma_candidate("early", 0),
                local_lemma_candidate("middle", 1),
            ],
            Some(MachineBatchSchedulerLimits {
                per_candidate_timeout_ms: Some(100),
                batch_timeout_ms: Some(500),
                max_memory_mb: None,
            }),
        )
        .unwrap();

        assert_eq!(
            request.candidates.len(),
            local_lemma_budget.max_candidate_count as usize
        );
        assert_eq!(request.candidates[0].candidate_id, "c0");
        assert_eq!(request.candidates[1].candidate_id, "c1");
        assert!(matches!(
            request.candidates[0].envelope.candidate,
            MachineTacticCandidate::Have(HavePayload { ref name, .. }) if name == "early"
        ));
        assert!(matches!(
            request.candidates[1].envelope.candidate,
            MachineTacticCandidate::Have(HavePayload { ref name, .. }) if name == "middle"
        ));
        assert_eq!(
            request.deterministic_budget,
            local_lemma_budget.deterministic_budget
        );
        assert_eq!(
            request.batch_policy,
            local_lemma_budget.batch_policy.unwrap()
        );

        let request_json = ai_search_tactic_batch_request_json(&request);
        let parsed = parse_machine_tactic_batch_request(&request_json).unwrap();
        assert_eq!(
            parsed.batch_policy.max_evaluated_candidates,
            local_lemma_budget.max_candidate_count
        );
        assert_eq!(parsed.batch_policy.stop_after_successes, 1);
        assert_eq!(
            parsed.deterministic_budget,
            local_lemma_budget.deterministic_budget
        );

        let constructor_budget =
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::Constructor);
        let constructor = |max_new_goals: u64, source_index| {
            ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                source_index,
                None,
                MachineTacticCandidate::Constructor(npa_tactic::ConstructorPayload {
                    selection: ConstructorSelection::Auto,
                    max_new_goals: Some(max_new_goals),
                }),
            )
        };
        let constructor_request = ai_search_cheap_first_tactic_batch_request(
            snapshot.session_id,
            snapshot.snapshot_id,
            snapshot.state_fingerprint,
            GoalId(0),
            AiSearchCheapFirstStage::Constructor,
            vec![
                constructor(u64::from(constructor_budget.max_new_goals) + 1, 0),
                constructor(u64::from(constructor_budget.max_new_goals), 1),
            ],
            None,
        )
        .unwrap();
        assert_eq!(constructor_request.candidates.len(), 1);
        assert!(matches!(
            constructor_request.candidates[0].envelope.candidate,
            MachineTacticCandidate::Constructor(npa_tactic::ConstructorPayload {
                max_new_goals: Some(value),
                ..
            }) if value == u64::from(constructor_budget.max_new_goals)
        ));

        assert!(ai_search_cheap_first_tactic_batch_request(
            SessionId::new_unchecked("s-budget"),
            SnapshotId::from_state_fingerprint(hash(1)),
            hash(1),
            GoalId(0),
            AiSearchCheapFirstStage::Solver,
            vec![ai_search_cheap_first_test_envelope(
                AiSearchCandidateSource::Exploration,
                None,
                0,
                None,
                MachineTacticCandidate::Omega,
            )],
            None,
        )
        .is_none());
    }

    #[test]
    fn cheap_first_budget_progress_records_hashes_repeated_failures_and_no_progress() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
            ai_search_test_envelope(2, None),
            ai_search_test_envelope(3, None),
            ai_search_test_envelope(4, None),
        ]);
        let mut no_progress = compact_error(MachineApiErrorKind::SimpNoProgress);
        no_progress.diagnostic_hash = hash(56);
        let mut repeated_no_progress = compact_error(MachineApiErrorKind::SimpNoProgress);
        repeated_no_progress.diagnostic_hash = hash(56);
        let mut budget_exhausted = compact_error(MachineApiErrorKind::BudgetExceeded);
        budget_exhausted.diagnostic_hash = hash(57);
        let mut non_accepted = compact_error(MachineApiErrorKind::TypeMismatch);
        non_accepted.diagnostic_hash = hash(58);
        let response = ok_batch_response(
            &request,
            vec![
                MachineTacticBatchItemResponse::Success {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: hash(40),
                    next_snapshot_id: SnapshotId::from_state_fingerprint(request.state_fingerprint),
                    next_state_fingerprint: request.state_fingerprint,
                    proof_delta_hash: hash(43),
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c1".to_owned(),
                    candidate_hash: Some(hash(50)),
                    diagnostic: no_progress,
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c2".to_owned(),
                    candidate_hash: Some(hash(51)),
                    diagnostic: repeated_no_progress,
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c3".to_owned(),
                    candidate_hash: Some(hash(52)),
                    diagnostic: budget_exhausted,
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c4".to_owned(),
                    candidate_hash: None,
                    diagnostic: non_accepted,
                },
            ],
        );

        let evaluation =
            ai_search_evaluate_tactic_batch_response(&request, response.clone()).unwrap();
        let repeated_evaluation =
            ai_search_evaluate_tactic_batch_response(&request, response).unwrap();

        assert_eq!(evaluation, repeated_evaluation);
        assert_eq!(evaluation.accepted_failures.len(), 3);
        assert_eq!(evaluation.non_accepted_errors.len(), 1);
        assert_eq!(evaluation.non_accepted_errors[0].diagnostic_hash, hash(58));

        let progress = ai_search_batch_progress_accounting(&evaluation, 1, &[2]).unwrap();
        assert_eq!(progress.evaluated_candidates, 5);
        assert_eq!(progress.successful_candidates, 1);
        assert_eq!(progress.failed_candidates, 4);
        assert_eq!(progress.closed_goals, 1);
        assert_eq!(progress.new_goals, 2);
        assert_eq!(progress.replay_step_count, 1);
        assert_eq!(progress.proof_delta_hashes, vec![hash(43)]);
        assert_eq!(
            progress.next_state_fingerprints,
            vec![request.state_fingerprint]
        );
        assert_eq!(
            progress.unchanged_state_fingerprints,
            vec![request.state_fingerprint]
        );
        assert_eq!(
            progress.failure_diagnostic_hashes,
            vec![hash(56), hash(56), hash(57), hash(58)]
        );
        assert_eq!(
            ai_search_batch_progress_accounting(&evaluation, 1, &[]).unwrap_err(),
            AiSearchProgressAccountingError::SuccessGoalCountMismatch {
                success_count: 1,
                supplied_count: 0,
            }
        );
    }

    #[test]
    fn cheap_first_budget_scheduler_timeout_is_progress_artifact_not_failure() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
        ]);
        let response = MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
            status: MachineApiResponseStatus::PartialTimeout,
            scheduler_artifact: MachineSchedulerArtifact {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Batch,
                retryable: true,
            },
            endpoint_fields: MachineTacticBatchSchedulerFields {
                previous_state_fingerprint: request.state_fingerprint,
                deterministic_budget_hash: tactic_budget_hash(request.deterministic_budget),
                completed_prefix_len: 0,
                results: Vec::new(),
                success_count: 0,
                failure_count: 0,
            },
        });

        let evaluation = ai_search_evaluate_tactic_batch_response(&request, response).unwrap();
        let progress = ai_search_batch_progress_accounting(&evaluation, 1, &[]).unwrap();

        assert_eq!(progress.evaluated_candidates, 0);
        assert_eq!(progress.successful_candidates, 0);
        assert_eq!(progress.failed_candidates, 0);
        assert_eq!(progress.replay_step_count, 0);
        assert!(progress.failure_diagnostic_hashes.is_empty());
        assert_eq!(
            progress.scheduler_stop,
            Some(AiSearchSchedulerStop {
                status: MachineApiResponseStatus::PartialTimeout,
                completed_prefix_len: 0,
            })
        );
        assert!(evaluation.accepted_failures.is_empty());
        assert!(evaluation.non_accepted_errors.is_empty());
    }

    #[test]
    fn builtin_generator_emits_mvp_candidates_without_machine_api_hashes() {
        let mut goal = goal_view(GoalId(0), 30, 5, 1, 1, None);
        goal.target.machine = "forall (p : Prop), Prop".to_owned();
        goal.context[0].machine_name = "n".to_owned();
        goal.context[0].display_name = "n".to_owned();
        goal.allowed_tactics = vec![
            MachineApiTacticKind::InductionNat,
            MachineApiTacticKind::SimpLite,
        ];

        let envelopes = ai_search_builtin_candidate_envelopes(&goal);

        assert_eq!(envelopes.len(), 3);
        assert!(envelopes
            .iter()
            .all(|envelope| envelope.candidate_hash.is_none()));
        assert!(matches!(
            envelopes[0].candidate,
            MachineTacticCandidate::Intro { ref name } if name == "p"
        ));
        assert!(matches!(
            envelopes[1].candidate,
            MachineTacticCandidate::InductionNat { ref local_name } if local_name == "n"
        ));
        assert!(matches!(
            envelopes[2].candidate,
            MachineTacticCandidate::SimpLite { ref rules } if rules.is_empty()
        ));
        assert_eq!(envelopes[0].metadata.rank.builtin_kind_rank, 0);
        assert_eq!(envelopes[1].metadata.rank.builtin_kind_rank, 2);
        assert_eq!(envelopes[2].metadata.rank.builtin_kind_rank, 3);
        assert_eq!(
            envelopes[0].metadata.rank.cheap_first_stage,
            AiSearchCheapFirstStage::ReflexivityComputation
        );
        assert_eq!(
            envelopes[1].metadata.rank.cheap_first_stage,
            AiSearchCheapFirstStage::Induction
        );
        assert_eq!(
            envelopes[2].metadata.rank.cheap_first_stage,
            AiSearchCheapFirstStage::SimpLite
        );
    }

    #[test]
    fn fresh_intro_name_skips_unbounded_suffix_scan_for_max_length_base() {
        let max_length_name = "a".repeat(64);
        assert!(is_machine_local_name(&max_length_name));
        assert!(!is_machine_local_name(&format!("{max_length_name}1")));

        let mut goal = goal_view(GoalId(0), 30, 5, 0, 1, None);
        goal.context[0].machine_name = max_length_name.clone();

        assert_eq!(
            ai_search_fresh_intro_name(&goal, Some(&max_length_name)),
            Some("x".to_owned())
        );
    }

    #[test]
    fn builtin_local_exact_requires_unique_assumption_with_matching_target_hash() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let mut local = local_view(0);
        local.machine_name = "h".to_owned();
        local.display_name = "h".to_owned();
        local.ty = goal.target.clone();
        goal.context = vec![local.clone()];

        let envelopes = ai_search_builtin_candidate_envelopes(&goal);

        assert_eq!(envelopes.len(), 1);
        assert!(matches!(
            envelopes[0].candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h"
        ));

        let mut duplicate_goal = goal;
        duplicate_goal.context.push(local);
        assert!(ai_search_builtin_candidate_envelopes(&duplicate_goal).is_empty());
    }

    #[test]
    fn induction_nat_prefilter_requires_last_context_assumption_used_by_target() {
        let mut goal = goal_view(GoalId(0), 30, 5, 1, 2, None);
        goal.context[0].machine_name = "n".to_owned();
        goal.context[1].machine_name = "m".to_owned();
        goal.allowed_tactics = vec![MachineApiTacticKind::InductionNat];

        let envelopes = ai_search_builtin_candidate_envelopes(&goal);

        assert!(envelopes.is_empty());

        goal.context.swap(0, 1);
        goal.context[1].local_id = LocalId(0);
        goal.context[1].machine_name = "n".to_owned();
        let envelopes = ai_search_builtin_candidate_envelopes(&goal);

        assert_eq!(envelopes.len(), 1);
        assert!(matches!(
            envelopes[0].candidate,
            MachineTacticCandidate::InductionNat { ref local_name } if local_name == "n"
        ));
    }

    #[test]
    fn forbidden_token_filter_scans_only_raw_machine_term_tokens() {
        let unsafe_candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Std.unsafe.Type"),
        };
        let token = ai_search_candidate_forbidden_token(&unsafe_candidate)
            .unwrap()
            .unwrap();
        assert_eq!(token.class, AiSearchForbiddenTokenClass::Unsafe);
        assert_eq!(token.spelling, "unsafe");

        let set_option_candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("set_option -- comment\n unsafe"),
        };
        let token = ai_search_candidate_forbidden_token(&set_option_candidate)
            .unwrap()
            .unwrap();
        assert_eq!(token.class, AiSearchForbiddenTokenClass::SetOptionUnsafe);

        let priority_candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("import unsafe"),
        };
        let token = ai_search_candidate_forbidden_token(&priority_candidate)
            .unwrap()
            .unwrap();
        assert_eq!(token.class, AiSearchForbiddenTokenClass::Unsafe);
        assert_eq!(token.spelling, "unsafe");

        let safe_candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("hunsafe"),
        };
        assert_eq!(
            ai_search_candidate_forbidden_token(&safe_candidate).unwrap(),
            None
        );

        let candidate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let mut metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::SimpLiteEmpty),
            0,
            Vec::new(),
            Vec::new(),
            &candidate,
        );
        metadata.display_text = Some("unsafe".to_owned());
        let result = filter_ai_search_candidate_envelopes(vec![ai_search_candidate_envelope(
            candidate, None, metadata,
        )]);
        assert_eq!(result.accepted.len(), 1);
        assert!(result.rejected.is_empty());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn mvp_candidate_generation_preserves_forbidden_rejections_before_dedupe() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let mut local = local_view(0);
        local.machine_name = "unsafe".to_owned();
        local.display_name = "unsafe".to_owned();
        local.ty = goal.target.clone();
        goal.context = vec![local];

        let builtin = ai_search_builtin_candidate_envelopes(&goal);
        assert_eq!(builtin.len(), 1);
        assert!(matches!(
            builtin[0].candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "unsafe"
        ));

        let result = ai_search_mvp_candidate_generation(&goal, &empty_retrieval());

        assert!(result.accepted.is_empty());
        assert!(result.errors.is_empty());
        assert_eq!(result.rejected.len(), 1);
        assert_eq!(
            result.rejected[0].forbidden_token.class,
            AiSearchForbiddenTokenClass::Unsafe
        );
        assert!(
            result.rejected[0]
                .envelope
                .metadata
                .trust_flags
                .contains_forbidden_tokens
        );
    }

    #[test]
    fn candidate_ordering_and_dedupe_use_rank_not_score_or_display_text() {
        let candidate0 = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("h0"),
        };
        let candidate1 = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("h1"),
        };
        let duplicate = MachineTacticCandidate::SimpLite { rules: Vec::new() };
        let apply = MachineTacticCandidate::Apply {
            head: TacticHead::Local {
                name: "f".to_owned(),
            },
            universe_args: Vec::new(),
            args: vec![CandidateApplyArg::InferFromTarget],
        };

        let mut later_metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::LocalExact),
            1,
            Vec::new(),
            Vec::new(),
            &candidate1,
        );
        later_metadata.score = 1000;
        later_metadata.display_text = Some("aaa".to_owned());
        let earlier_metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::LocalExact),
            0,
            Vec::new(),
            Vec::new(),
            &candidate0,
        );
        let builtin_duplicate_metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::Builtin,
            Some(AiSearchBuiltinKind::SimpLiteEmpty),
            0,
            Vec::new(),
            Vec::new(),
            &duplicate,
        );
        let suggested_duplicate_metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::MachineApiSuggested,
            None,
            9,
            Vec::new(),
            Vec::new(),
            &duplicate,
        );
        let mut apply_metadata = ai_search_candidate_metadata(
            AiSearchCandidateSource::MachineApiSuggested,
            None,
            0,
            Vec::new(),
            Vec::new(),
            &apply,
        );
        apply_metadata.score = -1000;
        apply_metadata.display_text = Some("should not outrank local exact".to_owned());

        let ordered = ai_search_rank_and_dedupe_candidate_envelopes(vec![
            ai_search_candidate_envelope(duplicate.clone(), None, builtin_duplicate_metadata),
            ai_search_candidate_envelope(candidate1, None, later_metadata),
            ai_search_candidate_envelope(candidate0, None, earlier_metadata),
            ai_search_candidate_envelope(duplicate, Some(hash(88)), suggested_duplicate_metadata),
            ai_search_candidate_envelope(apply, Some(hash(89)), apply_metadata),
        ]);

        assert_eq!(ordered.len(), 4);
        assert!(matches!(
            ordered[0].candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h0"
        ));
        assert!(matches!(
            ordered[1].candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h1"
        ));
        assert!(matches!(
            ordered[2].candidate,
            MachineTacticCandidate::SimpLite { .. }
        ));
        assert_eq!(ordered[2].candidate_hash, Some(hash(88)));
        assert!(matches!(
            ordered[3].candidate,
            MachineTacticCandidate::Apply { .. }
        ));
        assert_eq!(
            ordered
                .iter()
                .map(|candidate| candidate.metadata.rank.cheap_first_stage)
                .collect::<Vec<_>>(),
            vec![
                AiSearchCheapFirstStage::LocalExact,
                AiSearchCheapFirstStage::LocalExact,
                AiSearchCheapFirstStage::SimpLite,
                AiSearchCheapFirstStage::Apply,
            ]
        );
    }

    #[test]
    fn batch_request_builder_assigns_ids_caps_policy_and_uses_batch_endpoint() {
        let mut request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
        ]);
        request.scheduler_limits = Some(MachineBatchSchedulerLimits {
            per_candidate_timeout_ms: Some(100),
            batch_timeout_ms: Some(1000),
            max_memory_mb: None,
        });

        let source = ai_search_tactic_batch_request_json(&request);
        let parsed = parse_machine_tactic_batch_request(&source).unwrap();

        assert_eq!(parsed.candidates[0].candidate_id, "c0");
        assert_eq!(parsed.candidates[1].candidate_id, "c1");
        assert_eq!(parsed.batch_policy.max_evaluated_candidates, 2);
        assert_eq!(parsed.batch_policy.stop_after_successes, 2);
        assert_eq!(parsed.batch_policy.stop_after_failures, 2);
        assert_eq!(parsed.scheduler_limits.per_candidate_timeout_ms, Some(100));
        assert_eq!(parsed.scheduler_limits.batch_timeout_ms, Some(1000));

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_tactic_batch_response(Ok(ok_batch_response(&request, Vec::new())));
        let evaluation = ai_search_run_tactic_batch(&mut client, &request).unwrap();

        assert_eq!(evaluation.replay_steps.len(), 0);
        assert_eq!(evaluation.deferred_candidates.len(), 2);
        assert_eq!(client.calls().len(), 1);
        assert!(matches!(
            &client.calls()[0],
            AiSearchMachineApiCall::TacticBatch { source: actual } if actual == &source
        ));
    }

    #[test]
    fn batch_success_items_build_replay_steps_and_errors_normalize_failures() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, Some(hash(50))),
        ]);
        let response = ok_batch_response(
            &request,
            vec![
                MachineTacticBatchItemResponse::Success {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: hash(40),
                    next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                    next_state_fingerprint: hash(42),
                    proof_delta_hash: hash(43),
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c1".to_owned(),
                    candidate_hash: Some(hash(50)),
                    diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
                },
            ],
        );

        let evaluation = ai_search_evaluate_tactic_batch_response(&request, response).unwrap();

        assert_eq!(evaluation.successful_transitions.len(), 1);
        assert_eq!(evaluation.replay_steps.len(), 1);
        assert_eq!(evaluation.accepted_failure_records.len(), 1);
        assert_eq!(evaluation.accepted_failures.len(), 1);
        assert_eq!(evaluation.training_trace_candidates.len(), 2);
        assert!(evaluation.non_accepted_errors.is_empty());
        assert_eq!(evaluation.deferred_candidates.len(), 0);

        let transition = &evaluation.successful_transitions[0];
        assert_eq!(transition.candidate_id, "c0");
        assert_eq!(
            transition.next_snapshot_id,
            SnapshotId::from_state_fingerprint(hash(41))
        );

        let step = &evaluation.replay_steps[0];
        assert_eq!(&transition.replay_step, step);
        assert_eq!(step.previous_state_fingerprint, request.state_fingerprint);
        assert_eq!(step.goal_id, GoalId(0));
        assert_eq!(step.candidate_hash, hash(40));
        assert_eq!(step.proof_delta_hash, hash(43));
        assert_eq!(step.next_state_fingerprint, hash(42));

        let failure = &evaluation.accepted_failures[0];
        assert_eq!(evaluation.accepted_failure_records[0].candidate_id, "c1");
        assert_eq!(&evaluation.accepted_failure_records[0].failure, failure);
        assert_eq!(failure.error_kind, FailedCandidateErrorKind::TypeMismatch);
        assert_eq!(failure.candidate_hash, hash(50));
        assert_eq!(
            failure.deterministic_budget_hash,
            tactic_budget_hash(request.deterministic_budget)
        );
        assert_eq!(failure.diagnostic_hash, hash(55));

        assert!(matches!(
            &evaluation.training_trace_candidates[0],
            AiSearchTrainingTraceCandidate::Success {
                rank_index: 0,
                candidate_hash,
                proof_delta_hash,
                next_state_fingerprint,
                ..
            } if *candidate_hash == hash(40)
                && *proof_delta_hash == hash(43)
                && *next_state_fingerprint == hash(42)
        ));
        assert!(matches!(
            &evaluation.training_trace_candidates[1],
            AiSearchTrainingTraceCandidate::Error {
                rank_index: 1,
                candidate_hash,
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                diagnostic_hash,
                ..
            } if *candidate_hash == hash(50) && *diagnostic_hash == hash(55)
        ));

        let step_json = ai_search_replay_step_json(step);
        assert!(!step_json.contains("candidate_id"));
        assert!(!step_json.contains("display"));
        let replay_source = format!(
            r#"{{"session_id":"{}","plan":{{"protocol_version":{},"session_root_hash":{},"initial_state_fingerprint":{},"steps":[{}],"final_state_fingerprint":{}}}}}"#,
            request.session_id.wire(),
            json_string(crate::MachineApiVersion::V1.as_str()),
            json_string(&format_hash_string(&hash(90))),
            json_string(&format_hash_string(&request.state_fingerprint)),
            step_json,
            json_string(&format_hash_string(&hash(42))),
        );
        parse_machine_replay_request(&replay_source).unwrap();
    }

    #[test]
    fn m8_training_identity_hashes_exclude_ai_search_payload_hash() {
        let positive =
            ai_search_positive_training_identity(hash(1), GoalId(0), hash(40), hash(41), hash(42));
        let same_positive =
            ai_search_positive_training_identity(hash(1), GoalId(0), hash(40), hash(41), hash(42));
        let changed_positive =
            ai_search_positive_training_identity(hash(1), GoalId(0), hash(40), hash(99), hash(42));
        assert_eq!(
            ai_search_positive_training_identity_hash(&positive),
            ai_search_positive_training_identity_hash(&same_positive)
        );
        assert_ne!(
            ai_search_positive_training_identity_hash(&positive),
            ai_search_positive_training_identity_hash(&changed_positive)
        );
        assert!(!ai_search_positive_training_identity_json(&positive)
            .contains("ai_search_candidate_payload_hash"));

        let failure = AiSearchAcceptedCandidateFailure {
            error_kind: FailedCandidateErrorKind::TypeMismatch,
            phase: crate::MachineApiDiagnosticPhase::TacticExecution,
            goal_id: Some(GoalId(0)),
            tactic_kind: Some(MachineApiTacticKind::Exact),
            candidate_hash: hash(50),
            deterministic_budget_hash: hash(51),
            diagnostic_hash: hash(52),
            retryable: false,
        };
        let negative = ai_search_negative_training_identity(hash(1), GoalId(0), &failure);
        let changed_payload_sidecar =
            ai_search_candidate_payload_hash(&MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("different_payload"),
            });
        assert_ne!(changed_payload_sidecar, hash(50));
        assert_eq!(
            ai_search_negative_training_identity_hash(&negative),
            ai_search_negative_training_identity_hash(&ai_search_negative_training_identity(
                hash(1),
                GoalId(0),
                &failure,
            ))
        );
        assert!(!ai_search_negative_training_identity_json(&negative)
            .contains("ai_search_candidate_payload_hash"));
    }

    #[test]
    fn batch_candidate_hash_mismatch_is_controller_error_before_replay() {
        let request =
            ai_search_test_batch_request(vec![ai_search_test_envelope(0, Some(hash(77)))]);
        let response = ok_batch_response(
            &request,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(78),
                next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                next_state_fingerprint: hash(42),
                proof_delta_hash: hash(43),
            }],
        );

        let error = ai_search_evaluate_tactic_batch_response(&request, response).unwrap_err();

        assert_eq!(
            error.kind,
            AiSearchMachineControllerErrorKind::SuggestedCandidateHashMismatch
        );
        assert_eq!(error.candidate_id.as_deref(), Some("c0"));
        assert_eq!(error.expected_hash, Some(hash(77)));
        assert_eq!(error.actual_hash, Some(hash(78)));
    }

    #[test]
    fn zero_progress_scheduler_stop_is_not_a_candidate_failure_or_deferred_suffix() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
        ]);
        let response = MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
            status: MachineApiResponseStatus::PartialTimeout,
            scheduler_artifact: MachineSchedulerArtifact {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Batch,
                retryable: true,
            },
            endpoint_fields: MachineTacticBatchSchedulerFields {
                previous_state_fingerprint: request.state_fingerprint,
                deterministic_budget_hash: tactic_budget_hash(request.deterministic_budget),
                completed_prefix_len: 0,
                results: Vec::new(),
                success_count: 0,
                failure_count: 0,
            },
        });

        let evaluation = ai_search_evaluate_tactic_batch_response(&request, response).unwrap();

        assert_eq!(evaluation.evaluated_count, 0);
        assert!(evaluation.replay_steps.is_empty());
        assert!(evaluation.accepted_failures.is_empty());
        assert!(evaluation.training_trace_candidates.is_empty());
        assert!(evaluation.non_accepted_errors.is_empty());
        assert_eq!(
            evaluation.scheduler_stop,
            Some(AiSearchSchedulerStop {
                status: MachineApiResponseStatus::PartialTimeout,
                completed_prefix_len: 0,
            })
        );
        assert!(evaluation.deferred_candidates.is_empty());
    }

    #[test]
    fn m8_search_traces_non_accepted_errors_without_negative_training() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let root = snapshot_with_state(1, vec![goal]);
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Error {
                candidate_id: "c0".to_owned(),
                candidate_hash: None,
                diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
            }],
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(failure.training_trace_records.len(), 1);
        assert!(failure.training_trace_records[0]
            .tactic_candidates
            .is_empty());
        assert!(failure.trace_events.iter().any(|event| matches!(
            &event.kind,
            AiSearchTraceEventKind::NonAcceptedCandidateError {
                candidate_id,
                error_kind: MachineApiErrorKind::TypeMismatch,
                has_candidate_hash: false,
                has_diagnostic_hash: true,
                ..
            } if candidate_id == "c0"
        )));
    }

    #[test]
    fn m8_search_traces_zero_progress_scheduler_drop_without_training_record() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let root = snapshot_with_state(1, vec![goal]);
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(MachineApiResponseEnvelope::SchedulerStopped(
            MachineApiSchedulerResponse {
                status: MachineApiResponseStatus::PartialTimeout,
                scheduler_artifact: MachineSchedulerArtifact {
                    kind: MachineSchedulerArtifactKind::Timeout,
                    scope: MachineSchedulerArtifactScope::Batch,
                    retryable: true,
                },
                endpoint_fields: MachineTacticBatchSchedulerFields {
                    previous_state_fingerprint: root.state_fingerprint,
                    deterministic_budget_hash: tactic_budget_hash(
                        config.per_tactic_deterministic_budget,
                    ),
                    completed_prefix_len: 0,
                    results: Vec::new(),
                    success_count: 0,
                    failure_count: 0,
                },
            },
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert!(failure.training_trace_records.is_empty());
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::ZeroProgressSchedulerStopped {
                status: MachineApiResponseStatus::PartialTimeout
            }
        )));
        assert!(failure.trace_events.iter().any(|event| matches!(
            &event.kind,
            AiSearchTraceEventKind::DeferredCandidateDropped {
                candidate_id,
                reason: AiSearchDeferredCandidateDropReason::SchedulerStoppedCandidate,
                ..
            } if candidate_id == "c0"
        )));
    }

    #[test]
    fn scheduler_stop_after_prefix_defers_only_suffix_after_stopped_candidate() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
            ai_search_test_envelope(2, None),
            ai_search_test_envelope(3, None),
        ]);
        let response = MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
            status: MachineApiResponseStatus::PartialResourceLimit,
            scheduler_artifact: MachineSchedulerArtifact {
                kind: MachineSchedulerArtifactKind::ResourceLimitExceeded,
                scope: MachineSchedulerArtifactScope::Batch,
                retryable: true,
            },
            endpoint_fields: MachineTacticBatchSchedulerFields {
                previous_state_fingerprint: request.state_fingerprint,
                deterministic_budget_hash: tactic_budget_hash(request.deterministic_budget),
                completed_prefix_len: 1,
                results: vec![MachineTacticBatchItemResponse::Success {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: hash(40),
                    next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                    next_state_fingerprint: hash(42),
                    proof_delta_hash: hash(43),
                }],
                success_count: 1,
                failure_count: 0,
            },
        });

        let evaluation = ai_search_evaluate_tactic_batch_response(&request, response).unwrap();

        assert_eq!(evaluation.replay_steps.len(), 1);
        assert!(evaluation.accepted_failures.is_empty());
        assert!(evaluation.non_accepted_errors.is_empty());
        assert_eq!(
            evaluation.scheduler_stop,
            Some(AiSearchSchedulerStop {
                status: MachineApiResponseStatus::PartialResourceLimit,
                completed_prefix_len: 1,
            })
        );
        assert_eq!(evaluation.deferred_candidates.len(), 2);
        assert_eq!(evaluation.deferred_candidates[0].candidate_id, "c2");
        assert_eq!(evaluation.deferred_candidates[1].candidate_id, "c3");
    }

    #[test]
    fn batch_contract_violations_end_as_controller_errors() {
        let request = ai_search_test_batch_request(vec![
            ai_search_test_envelope(0, None),
            ai_search_test_envelope(1, None),
        ]);
        let bad_prefix = ok_batch_response(
            &request,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c1".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: SnapshotId::from_state_fingerprint(hash(41)),
                next_state_fingerprint: hash(42),
                proof_delta_hash: hash(43),
            }],
        );

        let error = ai_search_evaluate_tactic_batch_response(&request, bad_prefix).unwrap_err();
        assert_eq!(
            error.kind,
            AiSearchMachineControllerErrorKind::BatchResponseContractViolation
        );

        let bad_budget = MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
            status: MachineApiResponseStatus::Ok,
            endpoint_fields: MachineTacticBatchOkFields {
                previous_state_fingerprint: request.state_fingerprint,
                deterministic_budget_hash: hash(99),
                results: Vec::new(),
                success_count: 0,
                failure_count: 0,
            },
        });
        let error = ai_search_evaluate_tactic_batch_response(&request, bad_budget).unwrap_err();
        assert_eq!(
            error.kind,
            AiSearchMachineControllerErrorKind::BatchResponseContractViolation
        );
        assert_eq!(
            error.expected_hash,
            Some(tactic_budget_hash(request.deterministic_budget))
        );
        assert_eq!(error.actual_hash, Some(hash(99)));
    }

    #[test]
    fn m5_batch_error_without_candidate_hash_is_not_repair_accepted_failure() {
        let request = ai_search_test_batch_request(vec![ai_search_test_envelope(0, None)]);
        let response = ok_batch_response(
            &request,
            vec![MachineTacticBatchItemResponse::Error {
                candidate_id: "c0".to_owned(),
                candidate_hash: None,
                diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
            }],
        );

        let evaluation = ai_search_evaluate_tactic_batch_response(&request, response).unwrap();

        assert!(evaluation.accepted_failures.is_empty());
        assert!(evaluation.accepted_failure_records.is_empty());
        assert_eq!(evaluation.non_accepted_errors.len(), 1);
        assert_eq!(evaluation.non_accepted_errors[0].candidate_id, "c0");
        assert_eq!(
            evaluation.non_accepted_errors[0].error_kind,
            MachineApiErrorKind::TypeMismatch
        );
        assert!(!evaluation.non_accepted_errors[0].has_candidate_hash);
    }

    #[test]
    fn m5_rule_based_repair_classifies_all_failed_candidate_kinds() {
        let cases = [
            (
                FailedCandidateErrorKind::UnsupportedTactic,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::MachineTermElaborationError,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::UnknownName,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::ImplicitArgumentRequired,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::TypeMismatch,
                AiSearchRuleBasedRepairAction::TrySimpLite,
            ),
            (
                FailedCandidateErrorKind::ExpectedPiType,
                AiSearchRuleBasedRepairAction::TrySimpLite,
            ),
            (
                FailedCandidateErrorKind::RewriteRuleInvalid,
                AiSearchRuleBasedRepairAction::TrySimpLite,
            ),
            (
                FailedCandidateErrorKind::SimpNoProgress,
                AiSearchRuleBasedRepairAction::TrySimpLite,
            ),
            (
                FailedCandidateErrorKind::InductionTargetNotNat,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::BudgetExceeded,
                AiSearchRuleBasedRepairAction::Noop,
            ),
            (
                FailedCandidateErrorKind::TooManyGoals,
                AiSearchRuleBasedRepairAction::TrySimpLite,
            ),
            (
                FailedCandidateErrorKind::TooLargeTerm,
                AiSearchRuleBasedRepairAction::Noop,
            ),
        ];

        assert_eq!(cases.len(), 12);
        for (kind, expected) in cases {
            assert_eq!(ai_search_rule_based_repair_action(kind), expected);
        }
    }

    #[test]
    fn m5_rule_based_repair_generates_limited_simp_lite_metadata() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let failed = ai_search_exact_test_envelope(0, Some(hash(40)), "h");
        let failure = accepted_failure(FailedCandidateErrorKind::TypeMismatch, hash(40));

        let output = AiSearchRuleBasedRepair::new().repair_candidate(&goal, &failed, &failure, 1);

        assert!(output.repeated_candidate_payload_hashes.is_empty());
        assert_eq!(output.pending.len(), 1);
        let pending = &output.pending[0];
        assert_eq!(pending.goal_id, GoalId(0));
        assert_eq!(pending.repair_depth, 1);
        assert_eq!(pending.parent_candidate_hash, hash(40));
        assert_eq!(pending.error_kind, FailedCandidateErrorKind::TypeMismatch);
        assert_eq!(
            pending.chain_tried_payload_hashes,
            vec![failed.ai_search_candidate_payload_hash]
        );
        assert_eq!(ai_search_repair_depth_of(&pending.candidate), 1);
        assert_eq!(pending.candidate.candidate_hash, None);
        assert!(matches!(
            pending.candidate.candidate,
            MachineTacticCandidate::SimpLite { ref rules } if rules.is_empty()
        ));
        assert_eq!(
            pending.candidate.metadata.source,
            AiSearchCandidateSource::Repair
        );
        assert_eq!(pending.candidate.metadata.rank.source_rank, 4);
        assert_eq!(pending.candidate.metadata.rank.source_index, 0);
        assert_eq!(pending.candidate.metadata.rank.builtin_kind_rank, 255);
        assert_eq!(
            pending.candidate.metadata.expected_effect,
            AiSearchExpectedEffect::Simplify
        );
        assert!(pending.candidate.metadata.premises_used.is_empty());
        assert_eq!(
            pending.candidate.metadata.repair,
            Some(AiSearchCandidateRepairMetadata {
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                repair_depth: 1,
                chain_tried_payload_hashes: vec![failed.ai_search_candidate_payload_hash],
                premise_retrieval: None,
            })
        );
    }

    #[test]
    fn repair_premise_retrieval_adapter_attaches_verified_premises_and_premise_sets() {
        let search = repair_premise_search_ok_fields();
        let retrieval = ai_search_repair_premise_retrieval_from_premise_search_ok(&search);

        assert_eq!(retrieval.query_fingerprint, search.query_fingerprint);
        assert_eq!(retrieval.premises.len(), 1);
        assert_eq!(
            retrieval.premises[0].verified_identity.identity_hash(),
            search.results[0].verified_identity.identity_hash()
        );
        assert_eq!(retrieval.premise_sets.len(), 1);
        assert_eq!(
            retrieval.premise_sets[0].selected_premise_identities,
            vec![search.results[0].verified_identity.clone()]
        );
        assert_eq!(retrieval.premise_sets[0].axiom_impact.direct_axiom_count, 1);
        for kind in [
            FailedCandidateErrorKind::TypeMismatch,
            FailedCandidateErrorKind::ExpectedPiType,
            FailedCandidateErrorKind::RewriteRuleInvalid,
            FailedCandidateErrorKind::SimpNoProgress,
            FailedCandidateErrorKind::InductionTargetNotNat,
        ] {
            assert!(ai_search_repair_should_request_premise_retrieval(kind));
        }

        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let failed = ai_search_exact_test_envelope(0, Some(hash(40)), "h");
        let failure = accepted_failure(FailedCandidateErrorKind::TypeMismatch, hash(40));
        let output = AiSearchRuleBasedRepair::new().repair_candidate_with_premise_retrieval(
            &goal,
            &failed,
            &failure,
            1,
            Some(&retrieval),
        );

        let [pending] = output.pending.as_slice() else {
            panic!("expected one retrieval-backed repair candidate");
        };
        let attached = pending
            .candidate
            .metadata
            .repair
            .as_ref()
            .and_then(|repair| repair.premise_retrieval.as_ref())
            .expect("repair metadata should carry advisory retrieval");
        assert_eq!(attached.query_fingerprint, retrieval.query_fingerprint);
        assert_eq!(attached.premises[0].premise_id, "prem_0");
        assert_eq!(
            attached.premise_sets[0].axiom_impact.summary_hash,
            search.results[0]
                .verified_identity
                .axiom_summary
                .summary_hash
        );
    }

    #[test]
    fn focused_replay_premise_provenance_is_advisory_sidecar_not_replay_input() {
        let search = repair_premise_search_ok_fields();
        let retrieval = ai_search_repair_premise_retrieval_from_premise_search_ok(&search);
        let budget = mvp_config().per_tactic_deterministic_budget;
        let plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(99),
            initial_state_fingerprint: hash(1),
            steps: vec![AiSearchReplayStep {
                previous_state_fingerprint: hash(1),
                goal_id: GoalId(0),
                candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
                deterministic_budget: budget,
                candidate_hash: hash(40),
                deterministic_budget_hash: tactic_budget_hash(budget),
                proof_delta_hash: hash(41),
                next_state_fingerprint: hash(2),
            }],
            final_state_fingerprint: hash(2),
        };
        let provenance = ai_search_focused_replay_provenance_from_retrieval(0, &retrieval);
        let payload = ai_search_focused_replay_payload(plan, vec![provenance]);
        let sidecar = ai_search_focused_replay_payload_json(&payload);

        assert!(sidecar.contains(r#""retrieval_provenance""#));
        assert!(sidecar.contains(r#""premise_identities""#));
        assert!(sidecar.contains(&format_hash_string(
            &search.results[0].verified_identity.identity_hash()
        )));
        let replay_source = ai_search_replay_request_json(
            SessionId::parse("msess_001").unwrap(),
            &payload.replay_plan,
        );
        parse_machine_replay_request(&replay_source).unwrap();
        assert!(!replay_source.contains("retrieval_provenance"));
        assert!(!replay_source.contains("premise_identities"));
        assert!(!replay_source.contains("premise_identity_hashes"));
        assert!(!replay_source.contains("retrieval_cache"));
    }

    #[test]
    fn m5_rule_based_repair_does_not_generate_without_allowed_simp_lite() {
        let goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let failed = ai_search_exact_test_envelope(0, Some(hash(40)), "h");
        let failure = accepted_failure(FailedCandidateErrorKind::TypeMismatch, hash(40));

        let output = AiSearchRuleBasedRepair::new().repair_candidate(&goal, &failed, &failure, 1);

        assert!(output.pending.is_empty());
        assert!(output.repeated_candidate_payload_hashes.is_empty());
    }

    #[test]
    fn m5_rule_based_repair_refuses_depth_above_two() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let failed = ai_search_exact_test_envelope(0, Some(hash(40)), "h");
        let failure = accepted_failure(FailedCandidateErrorKind::TypeMismatch, hash(40));

        let output = AiSearchRuleBasedRepair::new().repair_candidate(&goal, &failed, &failure, 3);

        assert!(output.pending.is_empty());
        assert!(output.repeated_candidate_payload_hashes.is_empty());
    }

    #[test]
    fn m5_rule_based_repair_reports_chain_duplicate_payload() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let failed = ai_search_test_envelope(0, Some(hash(40)));
        let failure = accepted_failure(FailedCandidateErrorKind::SimpNoProgress, hash(40));

        let output = AiSearchRuleBasedRepair::new().repair_candidate(&goal, &failed, &failure, 1);

        assert!(output.pending.is_empty());
        assert_eq!(
            output.repeated_candidate_payload_hashes,
            vec![failed.ai_search_candidate_payload_hash]
        );
    }

    #[test]
    fn m5_repair_limiter_preserves_first_three_per_parent_and_dedupes_payload() {
        let pending = vec![
            AiSearchPendingCandidate {
                goal_id: GoalId(0),
                candidate: ai_search_exact_test_envelope(0, None, "h0"),
                repair_depth: 1,
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                chain_tried_payload_hashes: vec![hash(90)],
            },
            AiSearchPendingCandidate {
                goal_id: GoalId(0),
                candidate: ai_search_exact_test_envelope(0, None, "h0"),
                repair_depth: 1,
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                chain_tried_payload_hashes: vec![hash(90)],
            },
            AiSearchPendingCandidate {
                goal_id: GoalId(0),
                candidate: ai_search_exact_test_envelope(1, None, "h1"),
                repair_depth: 1,
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                chain_tried_payload_hashes: vec![hash(90)],
            },
            AiSearchPendingCandidate {
                goal_id: GoalId(0),
                candidate: ai_search_exact_test_envelope(2, None, "h2"),
                repair_depth: 1,
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                chain_tried_payload_hashes: vec![hash(90)],
            },
            AiSearchPendingCandidate {
                goal_id: GoalId(0),
                candidate: ai_search_exact_test_envelope(3, None, "h3"),
                repair_depth: 1,
                parent_candidate_hash: hash(40),
                error_kind: FailedCandidateErrorKind::TypeMismatch,
                chain_tried_payload_hashes: vec![hash(90)],
            },
        ];

        let limited = ai_search_limit_repairs(pending);

        assert_eq!(limited.len(), 3);
        assert!(matches!(
            limited[0].candidate.candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h0"
        ));
        assert!(matches!(
            limited[1].candidate.candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h1"
        ));
        assert!(matches!(
            limited[2].candidate.candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h2"
        ));
    }

    #[test]
    fn m5_search_runs_pending_repair_in_same_node_after_accepted_failure() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let root = snapshot_with_state(1, vec![goal]);
        let closed_child = snapshot_with_state(2, Vec::new());
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display",
            vec![suggested_candidate(
                hash(40),
                MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("h"),
                },
            )],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: Some(hash(40)),
                    diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c1".to_owned(),
                    candidate_hash: Some(hash(41)),
                    diagnostic: compact_error(MachineApiErrorKind::SimpNoProgress),
                },
            ],
        )));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(42),
                next_snapshot_id: closed_child.snapshot_id,
                next_state_fingerprint: closed_child.state_fingerprint,
                proof_delta_hash: hash(43),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed_child.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed_child,
        }));
        client.push_replay_response(Ok(replay_scheduler_stopped_response()));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(failure.search_stats.candidates_evaluated, 3);
        let batch_sources = client
            .calls()
            .iter()
            .filter_map(|call| match call {
                AiSearchMachineApiCall::TacticBatch { source } => Some(source),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(batch_sources.len(), 2);
        let repair_batch = parse_machine_tactic_batch_request(batch_sources[1]).unwrap();
        assert_eq!(repair_batch.candidates.len(), 1);
        assert_eq!(repair_batch.candidates[0].candidate_id, "c0");
        assert!(batch_sources[1].contains(r#""kind":"simp-lite""#));
        assert!(batch_sources[1].contains(r#""rules":[]"#));
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::RepairChainStopped {
                reason: AiSearchRepairChainStopReason::RepeatedCandidate,
                repeated_candidate_payload_hash: Some(_),
                ..
            }
        )));
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::ChildQueued {
                child_node_id: AiSearchNodeId(1),
                ..
            }
        )));
    }

    #[test]
    fn m6_closed_node_replays_and_verifies_before_success() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let closed_child = snapshot_with_state(2, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(90));
        let replay_final_state_fingerprint = hash(90);
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display",
            vec![suggested_candidate(
                hash(40),
                MachineTacticCandidate::SimpLite { rules: Vec::new() },
            )],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: closed_child.snapshot_id,
                next_state_fingerprint: closed_child.state_fingerprint,
                proof_delta_hash: hash(43),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed_child.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed_child.clone(),
        }));
        client.push_replay_response(Ok(replay_ok_response(
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_ok_response()));

        let proof = unwrap_verified_proof(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(proof.replay_plan.steps.len(), 1);
        assert_eq!(
            proof.replay_plan.final_state_fingerprint,
            closed_child.state_fingerprint
        );
        assert_eq!(proof.final_snapshot_id, replay_final_snapshot_id);
        assert_eq!(
            proof.final_state_fingerprint,
            replay_final_state_fingerprint
        );
        assert_eq!(
            proof.verify_response.status,
            MachineApiResponseStatus::Verified
        );
        assert_eq!(proof.training_trace_records.len(), 1);
        assert_eq!(
            proof.training_trace_records[0].trace_schema,
            AI_SEARCH_TRAINING_TRACE_SCHEMA
        );
        assert_eq!(proof.training_trace_records[0].batch_index, 0);
        assert_eq!(proof.training_trace_records[0].tactic_candidates.len(), 1);
        assert!(matches!(
            &proof.training_trace_records[0].tactic_candidates[0],
            AiSearchTrainingTraceCandidate::Success {
                rank_index: 0,
                ai_search_candidate_payload_hash: _,
                candidate_hash,
                proof_delta_hash,
                next_state_fingerprint,
                ..
            } if *candidate_hash == hash(40)
                && *proof_delta_hash == hash(43)
                && *next_state_fingerprint == closed_child.state_fingerprint
        ));
        let training_json = ai_search_training_trace_records_json(&proof.training_trace_records);
        assert!(training_json.starts_with(r#"[{"trace_schema":"npa.ai-search.training-trace.v1""#));
        assert!(training_json.contains(r#""result":"success""#));
        assert!(training_json.contains(r#""ai_search_candidate_payload_hash":"#));
        assert!(!training_json.contains("chosen_candidate_hash"));
        assert_eq!(proof.search_stats.candidates_evaluated, 1);
        assert_eq!(proof.search_stats.closed_node_replay_rejections, 0);
        assert_eq!(proof.search_stats.closed_node_verify_rejections, 0);

        let replay_source = client.calls().iter().find_map(|call| match call {
            AiSearchMachineApiCall::Replay { source } => Some(source),
            _ => None,
        });
        let replay_source = replay_source.expect("expected replay call");
        assert!(replay_source.contains(r#""steps":[{"#));
        assert!(replay_source.contains(&format!(
            r#""final_state_fingerprint":"{}""#,
            format_hash_string(&closed_child.state_fingerprint)
        )));

        let verify_source = client.calls().iter().find_map(|call| match call {
            AiSearchMachineApiCall::Verify { source } => Some(source),
            _ => None,
        });
        let verify_source = verify_source.expect("expected verify call");
        assert!(verify_source.contains(&format!(
            r#""snapshot_id":"{}""#,
            replay_final_snapshot_id.wire()
        )));
        assert!(verify_source.contains(&format!(
            r#""state_fingerprint":"{}""#,
            format_hash_string(&replay_final_state_fingerprint)
        )));
        assert!(verify_source.contains(r#""mode":"certificate""#));
    }

    #[test]
    fn m6_replay_success_without_verify_is_not_verified_proof() {
        let root = snapshot_with_state(1, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(90));
        let replay_final_state_fingerprint = hash(90);
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_replay_response(Ok(replay_ok_response(
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_error_response(
            MachineApiErrorKind::VerifyFailed,
            crate::MachineApiDiagnosticPhase::CertificateVerify,
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(failure.reason, AiSearchFailureReason::QueueExhausted);
        assert_eq!(failure.best_partial_replay_prefix, None);
        assert_eq!(failure.best_snapshot_id, None);
        assert_eq!(failure.search_stats.closed_node_verify_rejections, 1);
        assert_eq!(failure.search_stats.closed_node_replay_rejections, 0);
        assert!(failure.trace_events.iter().any(|event| matches!(
            &event.kind,
            AiSearchTraceEventKind::ClosedNodeVerifyRejected { endpoint, status }
                if endpoint == "/machine/verify" && matches!(status, MachineApiResponseStatus::Error)
        )));
    }

    #[test]
    fn m6_replay_controller_error_preserves_phase_in_failure_reason() {
        let root = snapshot_with_state(1, Vec::new());
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_replay_response(Ok(replay_error_response(
            MachineApiErrorKind::ReplayHashMismatch,
            crate::MachineApiDiagnosticPhase::ReplayExecution,
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::MachineControllerError {
                endpoint: "/machine/replay".to_owned(),
                error_kind: "replay_hash_mismatch".to_owned(),
                error_phase: Some("replay_execution".to_owned()),
                diagnostic_hash: Some(hash(79)),
            }
        );
        assert_eq!(failure.search_stats.controller_errors, 1);
        assert!(failure.trace_events.iter().any(|event| matches!(
            &event.kind,
            AiSearchTraceEventKind::MachineControllerError { endpoint, error_kind }
                if endpoint == "/machine/replay" && error_kind == "replay_hash_mismatch"
        )));
    }

    #[test]
    fn m6_verify_controller_error_preserves_phase_in_failure_reason() {
        let root = snapshot_with_state(1, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(90));
        let replay_final_state_fingerprint = hash(90);
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_replay_response(Ok(replay_ok_response(
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_error_response(
            MachineApiErrorKind::InvalidVerifyRequest,
            crate::MachineApiDiagnosticPhase::RequestValidation,
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::MachineControllerError {
                endpoint: "/machine/verify".to_owned(),
                error_kind: "invalid_verify_request".to_owned(),
                error_phase: Some("request_validation".to_owned()),
                diagnostic_hash: Some(hash(79)),
            }
        );
        assert_eq!(failure.search_stats.controller_errors, 1);
        assert_eq!(failure.search_stats.closed_node_verify_rejections, 0);
    }

    #[test]
    fn m7_minimization_proposal_order_is_fixed() {
        let budget = mvp_config().per_tactic_deterministic_budget;
        let edits = vec![
            AiSearchReplayStepEdit {
                original_goal_id: GoalId(0),
                original_open_goal_index: 0,
                candidate: MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("h0"),
                },
                deterministic_budget: budget,
            },
            AiSearchReplayStepEdit {
                original_goal_id: GoalId(1),
                original_open_goal_index: 0,
                candidate: MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("h1"),
                },
                deterministic_budget: budget,
            },
            AiSearchReplayStepEdit {
                original_goal_id: GoalId(2),
                original_open_goal_index: 0,
                candidate: MachineTacticCandidate::SimpLite {
                    rules: vec![simp_rule("add_zero", 40), simp_rule("zero_add", 41)],
                },
                deterministic_budget: budget,
            },
        ];

        assert_eq!(
            AiSearchMinimizationPassKind::ALL,
            [
                AiSearchMinimizationPassKind::DeleteRedundantSteps,
                AiSearchMinimizationPassKind::ReplaceBlocksWithSimpLiteEmpty,
                AiSearchMinimizationPassKind::MinimizeExistingSimpLiteRules,
            ]
        );

        let delete = ai_search_delete_redundant_steps_proposals(&edits);
        assert_eq!(delete.len(), 3);
        assert_eq!(delete[0][0].original_goal_id, GoalId(1));
        assert_eq!(delete[1][0].original_goal_id, GoalId(0));
        assert_eq!(delete[1][1].original_goal_id, GoalId(2));

        let replace = ai_search_replace_blocks_with_simp_lite_empty_proposals(&edits);
        assert_eq!(replace.len(), 6);
        assert_eq!(replace[0].len(), 1);
        assert!(matches!(
            replace[0][0].candidate,
            MachineTacticCandidate::SimpLite { ref rules } if rules.is_empty()
        ));
        assert_eq!(replace[0][0].original_goal_id, GoalId(0));
        assert_eq!(replace[1].len(), 2);
        assert_eq!(replace[1][0].original_goal_id, GoalId(0));
        assert_eq!(replace[2].len(), 2);
        assert_eq!(replace[2][0].original_goal_id, GoalId(0));
        assert_eq!(replace[2][1].original_goal_id, GoalId(1));

        let simp_rules = ai_search_minimize_existing_simp_lite_rules_proposals(&edits);
        assert_eq!(simp_rules.len(), 2);
        assert!(matches!(
            simp_rules[0][2].candidate,
            MachineTacticCandidate::SimpLite { ref rules }
                if rules == &vec![simp_rule("zero_add", 41)]
        ));
        assert!(matches!(
            simp_rules[1][2].candidate,
            MachineTacticCandidate::SimpLite { ref rules }
                if rules == &vec![simp_rule("add_zero", 40)]
        ));
    }

    #[test]
    fn m7_rebuild_uses_open_goal_index_fallback_and_fresh_step_fields() {
        let initial = snapshot_with_state(1, vec![goal_view(GoalId(2), 30, 5, 0, 0, None)]);
        let closed = snapshot_with_state(2, Vec::new());
        let budget = mvp_config().per_tactic_deterministic_budget;
        let current_plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(90),
            initial_state_fingerprint: initial.state_fingerprint,
            steps: Vec::new(),
            final_state_fingerprint: initial.state_fingerprint,
        };
        let edit = AiSearchReplayStepEdit {
            original_goal_id: GoalId(99),
            original_open_goal_index: 0,
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
            deterministic_budget: budget,
        };
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: initial.clone(),
        }));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            initial.state_fingerprint,
            budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(70),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(71),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));

        let rebuilt = ai_search_rebuild_replay_plan_from_step_edits(
            &mut client,
            initial.session_id.clone(),
            &initial,
            &current_plan,
            &[edit],
        )
        .unwrap();

        assert_eq!(rebuilt.steps.len(), 1);
        assert_eq!(rebuilt.steps[0].goal_id, GoalId(2));
        assert_eq!(rebuilt.steps[0].candidate_hash, hash(70));
        assert_eq!(rebuilt.steps[0].proof_delta_hash, hash(71));
        assert_eq!(
            rebuilt.steps[0].deterministic_budget_hash,
            tactic_budget_hash(budget)
        );
        assert_eq!(rebuilt.final_state_fingerprint, closed.state_fingerprint);
    }

    #[test]
    fn m7_minimizer_accepts_delete_only_after_replay_and_verify() {
        let initial = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let closed = snapshot_with_state(2, Vec::new());
        let budget = mvp_config().per_tactic_deterministic_budget;
        let step = AiSearchReplayStep {
            previous_state_fingerprint: initial.state_fingerprint,
            goal_id: GoalId(0),
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
            deterministic_budget: budget,
            candidate_hash: hash(40),
            deterministic_budget_hash: tactic_budget_hash(budget),
            proof_delta_hash: hash(41),
            next_state_fingerprint: closed.state_fingerprint,
        };
        let plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(90),
            initial_state_fingerprint: initial.state_fingerprint,
            steps: vec![step],
            final_state_fingerprint: closed.state_fingerprint,
        };
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: initial.clone(),
        }));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            initial.state_fingerprint,
            budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(41),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: closed }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: initial.clone(),
        }));
        client.push_replay_response(Ok(replay_ok_response(
            initial.snapshot_id,
            initial.state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_ok_response()));

        let result = ai_search_minimize_replay_plan(
            &mut client,
            initial.session_id.clone(),
            &initial,
            plan,
            MachineReplayOkFields {
                final_snapshot_id: SnapshotId::from_state_fingerprint(hash(90)),
                final_state_fingerprint: hash(90),
            },
            verify_ok_envelope(),
        );

        assert!(result.replay_plan.steps.is_empty());
        assert_eq!(
            result.replay_plan.final_state_fingerprint,
            initial.state_fingerprint
        );
        assert_eq!(
            result.replay_response.final_snapshot_id,
            initial.snapshot_id
        );
        assert_eq!(
            result.replay_response.final_state_fingerprint,
            initial.state_fingerprint
        );
        assert_eq!(result.minimization_stats.pass_kinds_attempted, 3);
        assert_eq!(result.minimization_stats.rebuilt_plans, 1);
        assert_eq!(result.minimization_stats.replay_attempts, 1);
        assert_eq!(result.minimization_stats.verify_attempts, 1);
        assert_eq!(result.minimization_stats.accepted_proposals, 1);
    }

    #[test]
    fn m7_minimizer_keeps_verified_plan_when_verify_rejects_proposal() {
        let initial = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let closed = snapshot_with_state(2, Vec::new());
        let budget = mvp_config().per_tactic_deterministic_budget;
        let step = AiSearchReplayStep {
            previous_state_fingerprint: initial.state_fingerprint,
            goal_id: GoalId(0),
            candidate: MachineTacticCandidate::SimpLite { rules: Vec::new() },
            deterministic_budget: budget,
            candidate_hash: hash(40),
            deterministic_budget_hash: tactic_budget_hash(budget),
            proof_delta_hash: hash(41),
            next_state_fingerprint: closed.state_fingerprint,
        };
        let plan = AiSearchReplayPlan {
            protocol_version: MachineApiVersion::V1,
            session_root_hash: hash(90),
            initial_state_fingerprint: initial.state_fingerprint,
            steps: vec![step],
            final_state_fingerprint: closed.state_fingerprint,
        };
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: initial.clone(),
        }));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            initial.state_fingerprint,
            budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(41),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: initial }));
        client.push_replay_response(Ok(replay_ok_response(
            SnapshotId::from_state_fingerprint(hash(91)),
            hash(91),
        )));
        client.push_verify_response(Ok(verify_error_response(
            MachineApiErrorKind::VerifyFailed,
            crate::MachineApiDiagnosticPhase::CertificateVerify,
        )));

        let result = ai_search_minimize_replay_plan(
            &mut client,
            closed.session_id.clone(),
            &snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]),
            plan,
            MachineReplayOkFields {
                final_snapshot_id: closed.snapshot_id,
                final_state_fingerprint: closed.state_fingerprint,
            },
            verify_ok_envelope(),
        );

        assert_eq!(result.replay_plan.steps.len(), 1);
        assert_eq!(
            result.replay_plan.final_state_fingerprint,
            closed.state_fingerprint
        );
        assert_eq!(result.replay_response.final_snapshot_id, closed.snapshot_id);
        assert_eq!(result.minimization_stats.replay_attempts, 1);
        assert_eq!(result.minimization_stats.verify_attempts, 1);
        assert_eq!(result.minimization_stats.accepted_proposals, 0);
    }

    #[test]
    fn m4_search_priority_and_best_partial_keys_are_deterministic() {
        let one_goal = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 9, 0, 0, None)]);
        let two_goals = snapshot_with_state(
            2,
            vec![
                goal_view(GoalId(0), 31, 4, 0, 0, None),
                goal_view(GoalId(1), 32, 5, 0, 0, None),
            ],
        );
        let mut one_goal_node =
            ai_search_root_search_node(&ai_search_test_search_input(one_goal), AiSearchNodeId(1));
        let mut two_goal_node =
            ai_search_root_search_node(&ai_search_test_search_input(two_goals), AiSearchNodeId(2));
        one_goal_node.depth = 1;
        two_goal_node.depth = 0;

        let one_goal_priority = ai_search_node_priority_key(&one_goal_node);
        assert_eq!(one_goal_priority.open_goal_count, 1);
        assert_eq!(one_goal_priority.depth, 1);
        assert_eq!(one_goal_priority.total_open_goal_target_size, 9);
        assert!(one_goal_priority < ai_search_node_priority_key(&two_goal_node));

        let two_goal_partial = ai_search_node_best_partial_key(&two_goal_node);
        assert_eq!(two_goal_partial.open_goal_count, 2);
        assert_eq!(two_goal_partial.total_open_goal_target_size, 9);
        assert!(ai_search_node_best_partial_key(&one_goal_node) < two_goal_partial);
    }

    #[test]
    fn m4_search_respects_max_depth_without_expanding_node() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let mut input = ai_search_test_search_input(root.clone());
        input.search_budget.max_depth = 0;
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(&mut client, input));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::SearchBudgetExceeded {
                limit: AiSearchBudgetLimit::MaxDepth
            }
        );
        assert_eq!(failure.search_stats.nodes_expanded, 0);
        assert_eq!(failure.search_stats.max_depth_stops, 1);
        assert_eq!(failure.best_snapshot_id, Some(root.snapshot_id));
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::MaxDepthStopped { max_depth: 0 }
        )));
        assert_eq!(client.calls().len(), 1);
    }

    #[test]
    fn m4_search_no_candidate_initial_goal_returns_no_candidate_failure() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::NoCandidateForSelectedGoal { goal_id: GoalId(0) }
        );
        assert_eq!(failure.search_stats.nodes_expanded, 1);
        assert_eq!(failure.search_stats.no_candidate_stops, 1);
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::NoCandidateForSelectedGoal { goal_id: GoalId(0) }
        )));
    }

    #[test]
    fn m4_search_caps_batch_to_max_tactics_per_node() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let config = mvp_config();
        let mut input = ai_search_test_search_input(root.clone());
        input.search_budget.max_tactics_per_node = 1;
        let suggested = vec![
            suggested_candidate(
                hash(40),
                MachineTacticCandidate::SimpLite { rules: Vec::new() },
            ),
            suggested_candidate(
                hash(41),
                MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("h"),
                },
            ),
        ];
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display", suggested,
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Error {
                candidate_id: "c0".to_owned(),
                candidate_hash: Some(hash(40)),
                diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
            }],
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(&mut client, input));

        assert_eq!(failure.search_stats.candidates_evaluated, 1);
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::MaxTacticsPerNodeStopped {
                max_tactics_per_node: 1
            }
        )));
        let batch_source = client.calls().iter().find_map(|call| match call {
            AiSearchMachineApiCall::TacticBatch { source } => Some(source),
            _ => None,
        });
        let parsed = parse_machine_tactic_batch_request(batch_source.unwrap()).unwrap();
        assert_eq!(parsed.candidates.len(), 1);
        assert_eq!(parsed.candidates[0].candidate_id, "c0");
    }

    #[test]
    fn m4_search_rejects_no_progress_ok_batch_as_controller_error() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display",
            vec![suggested_candidate(
                hash(40),
                MachineTacticCandidate::SimpLite { rules: Vec::new() },
            )],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            Vec::new(),
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::MachineControllerError {
                endpoint: "/machine/tactics/batch".to_owned(),
                error_kind: "batch_response_contract_violation".to_owned(),
                error_phase: None,
                diagnostic_hash: None,
            }
        );
        assert_eq!(failure.search_stats.controller_errors, 1);
        assert_eq!(failure.search_stats.candidates_evaluated, 0);
        assert!(failure.trace_events.iter().any(|event| matches!(
            &event.kind,
            AiSearchTraceEventKind::MachineControllerError { endpoint, error_kind }
                if endpoint == "/machine/tactics/batch"
                    && error_kind == "batch_response_contract_violation"
        )));
    }

    #[test]
    fn m4_search_records_duplicate_state_without_queueing_it() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let config = mvp_config();
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display",
            vec![suggested_candidate(
                hash(40),
                MachineTacticCandidate::SimpLite { rules: Vec::new() },
            )],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: root.snapshot_id,
                next_state_fingerprint: root.state_fingerprint,
                proof_delta_hash: hash(43),
            }],
        )));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root.clone()),
        ));

        assert_eq!(failure.search_stats.candidates_evaluated, 1);
        assert!(failure.trace_events.iter().any(|event| matches!(
            event.kind,
            AiSearchTraceEventKind::DuplicateStateSkipped {
                duplicate_state_fingerprint
            } if duplicate_state_fingerprint == root.state_fingerprint
        )));
        assert!(!failure
            .trace_events
            .iter()
            .any(|event| { matches!(event.kind, AiSearchTraceEventKind::ChildQueued { .. }) }));
        assert_eq!(client.calls().len(), 3);
    }

    #[test]
    fn m4_search_allocates_child_node_ids_in_batch_success_order() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let child0 = snapshot_with_state(2, vec![goal_view(GoalId(1), 31, 5, 0, 0, None)]);
        let child1 = snapshot_with_state(3, vec![goal_view(GoalId(2), 32, 5, 0, 0, None)]);
        let config = mvp_config();
        let mut input = ai_search_test_search_input(root.clone());
        input.search_budget.max_nodes = 1;
        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "display",
            vec![
                suggested_candidate(
                    hash(40),
                    MachineTacticCandidate::SimpLite { rules: Vec::new() },
                ),
                suggested_candidate(
                    hash(41),
                    MachineTacticCandidate::Exact {
                        term: RawMachineTerm::new("h"),
                    },
                ),
            ],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![
                MachineTacticBatchItemResponse::Success {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: hash(40),
                    next_snapshot_id: child0.snapshot_id,
                    next_state_fingerprint: child0.state_fingerprint,
                    proof_delta_hash: hash(43),
                },
                MachineTacticBatchItemResponse::Success {
                    candidate_id: "c1".to_owned(),
                    candidate_hash: hash(41),
                    next_snapshot_id: child1.snapshot_id,
                    next_state_fingerprint: child1.state_fingerprint,
                    proof_delta_hash: hash(44),
                },
            ],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: child0.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: child1 }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: child0 }));

        let failure = unwrap_search_failure(ai_search_run_mvp_search(&mut client, input));

        assert_eq!(
            failure.reason,
            AiSearchFailureReason::SearchBudgetExceeded {
                limit: AiSearchBudgetLimit::MaxNodes
            }
        );
        let child_ids = failure
            .trace_events
            .iter()
            .filter_map(|event| match event.kind {
                AiSearchTraceEventKind::ChildQueued { child_node_id, .. } => Some(child_node_id),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(child_ids, vec![AiSearchNodeId(1), AiSearchNodeId(2)]);
    }

    #[test]
    fn m9_exact_retrieval_fixture_returns_simp_lite_through_replay_and_verify() {
        let mut root_goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        root_goal.target.machine = "forall (n : Nat), Eq n n".to_owned();
        let root = snapshot_with_state(1, vec![root_goal]);

        let mut child_goal = goal_view(GoalId(0), 31, 5, 1, 1, Some(imported_ref("Eq", 40)));
        child_goal.context[0].machine_name = "n".to_owned();
        child_goal.context[0].display_name = "n".to_owned();
        child_goal.target.machine = "Eq n n".to_owned();
        child_goal.allowed_tactics = vec![MachineApiTacticKind::SimpLite];
        let child = snapshot_with_state(2, vec![child_goal]);
        let closed = snapshot_with_state(3, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(90));
        let replay_final_state_fingerprint = hash(90);
        let config = mvp_config();

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(40),
                next_snapshot_id: child.snapshot_id,
                next_state_fingerprint: child.state_fingerprint,
                proof_delta_hash: hash(41),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: child.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: child.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![
            theorem_result_in_module(
                "Std.Nat.Basic",
                "Nat.add_zero",
                50,
                "forall (n : Nat), Eq (Nat.add n Nat.zero) n",
            ),
            theorem_result_in_module(
                "Std.List.Basic",
                "List.append_nil",
                60,
                "forall (A : Type) (xs : List A), Eq (List.append xs (List.nil A)) xs",
            ),
        ])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            child.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(42),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(43),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: closed }));
        client.push_replay_response(Ok(replay_ok_response(
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_ok_response()));

        let proof = unwrap_verified_proof(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));

        assert_eq!(proof.replay_plan.steps.len(), 2);
        assert!(matches!(
            proof.replay_plan.steps[0].candidate,
            MachineTacticCandidate::Intro { ref name } if name == "n"
        ));
        assert!(matches!(
            proof.replay_plan.steps[1].candidate,
            MachineTacticCandidate::SimpLite { ref rules } if rules.is_empty()
        ));
        assert_eq!(proof.final_snapshot_id, replay_final_snapshot_id);
        assert_eq!(
            proof.final_state_fingerprint,
            replay_final_state_fingerprint
        );
        assert_eq!(proof.training_trace_records.len(), 2);
        assert!(proof.training_trace_records[0]
            .retrieved_premises
            .is_empty());
        let retrieved_names = proof.training_trace_records[1]
            .retrieved_premises
            .iter()
            .map(|premise| premise.premise_ref.name.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            retrieved_names,
            vec![name("Nat.add_zero"), name("List.append_nil")]
        );

        let batch_sources = client
            .calls()
            .iter()
            .filter_map(|call| match call {
                AiSearchMachineApiCall::TacticBatch { source } => Some(source),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(batch_sources.len(), 2);
        assert!(batch_sources[0].contains(r#""kind":"intro""#));
        assert!(batch_sources[1].contains(r#""kind":"simp-lite""#));
        assert!(batch_sources[1].contains(r#""rules":[]"#));
        assert!(!batch_sources[1].contains(r#""kind":"exact""#));
        assert!(!batch_sources[1].contains("Nat.add_zero"));
        assert!(client
            .calls()
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Replay { .. })));
        assert!(client
            .calls()
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Verify { .. })));
    }

    fn run_m9_local_exact_fixture() -> (AiSearchVerifiedProof, Vec<AiSearchMachineApiCall>) {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let mut local = local_view(0);
        local.machine_name = "h".to_owned();
        local.display_name = "h".to_owned();
        local.ty = goal.target.clone();
        goal.context = vec![local];
        let root = snapshot_with_state(1, vec![goal]);
        let closed = snapshot_with_state(2, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(91));
        let replay_final_state_fingerprint = hash(91);
        let config = mvp_config();

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            config.per_tactic_deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(44),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(45),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk { snapshot: closed }));
        client.push_replay_response(Ok(replay_ok_response(
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        )));
        client.push_verify_response(Ok(verify_ok_response()));

        let proof = unwrap_verified_proof(ai_search_run_mvp_search(
            &mut client,
            ai_search_test_search_input(root),
        ));
        let calls = client.calls().to_vec();
        (proof, calls)
    }

    #[test]
    fn ai_search_mvp_local_authoring_adapter_exact_replays_and_verifies_after_advisory_transition()
    {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let mut local = local_view(0);
        local.machine_name = "h".to_owned();
        local.display_name = "h".to_owned();
        local.ty = goal.target.clone();
        goal.context = vec![local];
        let root = snapshot_with_state(1, vec![goal]);
        let closed = snapshot_with_state(2, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(91));
        let replay_final_state_fingerprint = hash(91);
        let session_id = root.session_id.clone();
        let input = ai_search_test_search_input(root.clone());

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::LocalExact)
                .deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(44),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(45),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));

        let output = ai_search_run_local_authoring_loop(&mut client, input);

        assert_eq!(
            output.executed_stages,
            vec![AiSearchCheapFirstStage::LocalExact]
        );
        assert_eq!(
            output.successful_stage,
            Some(AiSearchCheapFirstStage::LocalExact)
        );
        assert_eq!(output.generated_candidate_count, 1);
        assert_eq!(output.remaining_goals, Some(Vec::new()));
        assert!(output.controller_error.is_none());
        assert!(matches!(
            output.best_partial_replay_prefix.as_deref(),
            Some([AiSearchReplayStep {
                candidate: MachineTacticCandidate::Exact {
                    term: RawMachineTerm { source }
                },
                ..
            }]) if source == "h"
        ));
        assert_eq!(output.advisory_replay_plan.as_ref().unwrap().steps.len(), 1);

        let calls_after_adapter = client.calls().to_vec();
        assert!(calls_after_adapter
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::TacticBatch { .. })));
        assert!(!calls_after_adapter
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Replay { .. })));
        assert!(!calls_after_adapter
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Verify { .. })));

        let verify_ok = replay_and_verify_advisory_plan(
            &mut client,
            session_id,
            output.advisory_replay_plan.as_ref().unwrap(),
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        );

        assert_eq!(verify_ok.status, MachineApiResponseStatus::Verified);
        assert!(client
            .calls()
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Replay { .. })));
        assert!(client
            .calls()
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Verify { .. })));
    }

    #[test]
    fn ai_search_mvp_local_authoring_adapter_apply_replays_and_verifies_after_batch_success() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let closed = snapshot_with_state(2, Vec::new());
        let replay_final_snapshot_id = SnapshotId::from_state_fingerprint(hash(92));
        let replay_final_state_fingerprint = hash(92);
        let session_id = root.session_id.clone();
        let input = ai_search_test_search_input(root.clone());
        let apply_candidate = MachineTacticCandidate::Apply {
            head: TacticHead::Imported {
                name: name("Nat.eq_refl"),
                decl_interface_hash: hash(54),
            },
            universe_args: Vec::new(),
            args: vec![CandidateApplyArg::InferFromTarget],
        };

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(vec![theorem_result(
            "Eq target",
            vec![suggested_candidate(hash(55), apply_candidate.clone())],
        )])));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::Apply).deterministic_budget,
            vec![MachineTacticBatchItemResponse::Success {
                candidate_id: "c0".to_owned(),
                candidate_hash: hash(56),
                next_snapshot_id: closed.snapshot_id,
                next_state_fingerprint: closed.state_fingerprint,
                proof_delta_hash: hash(57),
            }],
        )));
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: closed.clone(),
        }));

        let output = ai_search_run_local_authoring_loop(&mut client, input);

        assert_eq!(output.executed_stages, vec![AiSearchCheapFirstStage::Apply]);
        assert_eq!(
            output.successful_stage,
            Some(AiSearchCheapFirstStage::Apply)
        );
        assert_eq!(output.generated_candidate_count, 1);
        assert_eq!(
            output
                .retrieval
                .as_ref()
                .map(|retrieval| retrieval.results.len()),
            Some(1)
        );
        assert!(matches!(
            output.best_partial_replay_prefix.as_deref(),
            Some([AiSearchReplayStep {
                candidate: MachineTacticCandidate::Apply { .. },
                ..
            }])
        ));
        assert!(output.controller_error.is_none());

        let verify_ok = replay_and_verify_advisory_plan(
            &mut client,
            session_id,
            output.advisory_replay_plan.as_ref().unwrap(),
            replay_final_snapshot_id,
            replay_final_state_fingerprint,
        );

        assert_eq!(verify_ok.status, MachineApiResponseStatus::Verified);
    }

    #[test]
    fn ai_search_mvp_local_authoring_adapter_empty_retrieval_returns_compact_failure_output() {
        let mut goal = goal_view(GoalId(0), 30, 5, 0, 0, None);
        let mut h0 = local_view(0);
        h0.machine_name = "h0".to_owned();
        h0.display_name = "h0".to_owned();
        h0.ty = goal.target.clone();
        let mut h1 = local_view(1);
        h1.machine_name = "h1".to_owned();
        h1.display_name = "h1".to_owned();
        h1.ty = goal.target.clone();
        goal.context = vec![h0, h1];
        let root = snapshot_with_state(1, vec![goal]);
        let input = ai_search_test_search_input(root.clone());

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(search_ok_response(Vec::new())));
        client.push_tactic_batch_response(Ok(ok_batch_response_for(
            root.state_fingerprint,
            ai_search_cheap_first_stage_budget(AiSearchCheapFirstStage::LocalExact)
                .deterministic_budget,
            vec![
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c0".to_owned(),
                    candidate_hash: Some(hash(60)),
                    diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
                },
                MachineTacticBatchItemResponse::Error {
                    candidate_id: "c1".to_owned(),
                    candidate_hash: None,
                    diagnostic: compact_error(MachineApiErrorKind::TypeMismatch),
                },
            ],
        )));

        let output = ai_search_run_local_authoring_loop(&mut client, input);

        assert_eq!(
            output.executed_stages,
            vec![AiSearchCheapFirstStage::LocalExact]
        );
        assert_eq!(output.generated_candidate_count, 2);
        assert!(output.successful_transition.is_none());
        assert!(output.best_partial_replay_prefix.is_none());
        assert!(output.advisory_replay_plan.is_none());
        assert_eq!(
            output.remaining_goals.as_ref().map(Vec::len),
            Some(root.goals.len())
        );
        assert!(output.controller_error.is_none());
        assert_eq!(output.accepted_failures.len(), 1);
        assert_eq!(output.accepted_failures[0].candidate_id, "c0");
        assert_eq!(
            output.accepted_failures[0].failure.error_kind,
            FailedCandidateErrorKind::TypeMismatch
        );
        assert_eq!(
            output.accepted_failures[0].failure.diagnostic_hash,
            hash(55)
        );
        assert_eq!(output.non_accepted_errors.len(), 1);
        assert_eq!(output.non_accepted_errors[0].candidate_id, "c1");
        assert!(!output.non_accepted_errors[0].has_candidate_hash);
        assert_eq!(output.non_accepted_errors[0].diagnostic_hash, hash(55));
        assert!(client.calls().iter().all(|call| !matches!(
            call,
            AiSearchMachineApiCall::Replay { .. } | AiSearchMachineApiCall::Verify { .. }
        )));
    }

    #[test]
    fn ai_search_mvp_local_authoring_adapter_returns_structured_controller_error() {
        let root = snapshot_with_state(1, vec![goal_view(GoalId(0), 30, 5, 0, 0, None)]);
        let input = ai_search_test_search_input(root.clone());

        let mut client = AiSearchFakeMachineApiClient::new();
        client.push_snapshot_get_response(Ok(MachineSnapshotGetOk {
            snapshot: root.clone(),
        }));
        client.push_search_for_goal_response(Ok(MachineApiResponseEnvelope::Error(Box::new(
            MachineApiErrorResponse {
                status: MachineApiResponseStatus::Error,
                error: error_wire(
                    MachineApiErrorKind::UnknownName,
                    crate::MachineApiDiagnosticPhase::TheoremSearch,
                ),
                endpoint_fields: (),
            },
        ))));

        let output = ai_search_run_local_authoring_loop(&mut client, input);

        let controller_error = output
            .controller_error
            .as_ref()
            .expect("expected controller error");
        assert_eq!(controller_error.endpoint, "/machine/search/for_goal");
        assert_eq!(controller_error.error_kind, "unknown_name");
        assert_eq!(
            controller_error.error_phase,
            Some("theorem_search".to_owned())
        );
        assert_eq!(controller_error.diagnostic_hash, Some(hash(79)));
        assert_eq!(controller_error.status, None);
        assert!(output.batch_evaluations.is_empty());
        assert!(output.advisory_replay_plan.is_none());
    }

    #[test]
    fn m9_local_exact_fixture_uses_only_mvp_success_condition() {
        let (proof, calls) = run_m9_local_exact_fixture();

        assert_eq!(proof.replay_plan.steps.len(), 1);
        assert!(matches!(
            proof.replay_plan.steps[0].candidate,
            MachineTacticCandidate::Exact {
                term: RawMachineTerm { ref source }
            } if source == "h"
        ));
        assert_eq!(proof.search_stats.candidates_evaluated, 1);

        let batch_source = calls.iter().find_map(|call| match call {
            AiSearchMachineApiCall::TacticBatch { source } => Some(source),
            _ => None,
        });
        let batch_source = batch_source.expect("expected local Exact batch call");
        assert!(batch_source.contains(r#""kind":"exact""#));
        assert!(batch_source.contains(r#""source":"h""#));

        let replay_source = calls.iter().find_map(|call| match call {
            AiSearchMachineApiCall::Replay { source } => Some(source),
            _ => None,
        });
        let replay_source = replay_source.expect("expected replay call");
        for source in [batch_source.as_str(), replay_source.as_str()] {
            assert!(!source.contains(r#""kind":"apply""#));
            assert!(!source.contains(r#""kind":"rw""#));
            assert!(!source.contains("constructor"));
            assert!(!source.contains("cases"));
            assert!(!source.contains("refine"));
        }
        assert!(calls
            .iter()
            .any(|call| matches!(call, AiSearchMachineApiCall::Verify { .. })));
    }

    #[test]
    fn m9_local_exact_fixture_keeps_machine_surface_fast_path() {
        let (proof, calls) = run_m9_local_exact_fixture();
        let MachineTacticCandidate::Exact {
            term: RawMachineTerm { source },
        } = &proof.replay_plan.steps[0].candidate
        else {
            panic!("expected local Exact fixture");
        };

        assert_eq!(source, "h");
        assert!(npa_frontend::lex_machine_surface_tokens(source).is_ok());
        for human_only in [
            "open",
            "namespace",
            "notation",
            "infix",
            "axiom",
            "inductive",
            "_",
        ] {
            assert!(
                !source.contains(human_only),
                "AI search M9 local exact fixture must not use Human syntax: {human_only}"
            );
        }

        for call in calls {
            let Some(source) = (match call {
                AiSearchMachineApiCall::TacticBatch { source }
                | AiSearchMachineApiCall::Replay { source }
                | AiSearchMachineApiCall::Verify { source }
                | AiSearchMachineApiCall::SearchForGoal { source } => Some(source),
                AiSearchMachineApiCall::SnapshotGet { .. } => None,
            }) else {
                continue;
            };
            for human_only in ["notation", "infix", "namespace", "inductive"] {
                assert!(
                    !source.contains(human_only),
                    "AI search M9 API fixture must stay on Machine Surface payloads: {human_only}"
                );
            }
        }
    }

    #[test]
    fn m9_same_input_budget_and_machine_api_responses_are_deterministic() {
        let (first_proof, first_calls) = run_m9_local_exact_fixture();
        let (second_proof, second_calls) = run_m9_local_exact_fixture();

        assert_eq!(first_proof.replay_plan, second_proof.replay_plan);
        assert_eq!(first_proof.trace_events, second_proof.trace_events);
        assert_eq!(
            first_proof.training_trace_records,
            second_proof.training_trace_records
        );
        assert_eq!(first_calls, second_calls);
    }

    #[test]
    fn m9_no_model_mvp_profile_rejects_model_sidecar_fields() {
        let disallowed_fields = ["model", "embedding", "value_model", "parallel_search"];

        for field in disallowed_fields {
            let source = valid_config_json().replace(
                r#""batch_policy""#,
                &format!(r#""{field}":true,"batch_policy""#),
            );

            let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

            assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
            assert_eq!(
                err.reason,
                MachineApiRequestErrorReason::UnknownField {
                    field: field.to_owned()
                }
            );
        }

        let (proof, _) = run_m9_local_exact_fixture();
        assert_eq!(
            proof.verify_response.status,
            MachineApiResponseStatus::Verified
        );
    }

    #[test]
    fn fake_client_validates_raw_machine_api_requests_before_queue_lookup() {
        let mut client = AiSearchFakeMachineApiClient::new();

        let cases = [
            (
                client.search_for_goal("{}").unwrap_err(),
                AiSearchMachineApiEndpointKind::SearchForGoal,
                MachineApiErrorKind::InvalidTheoremQuery,
            ),
            (
                client.run_tactic_batch("{}").unwrap_err(),
                AiSearchMachineApiEndpointKind::TacticBatch,
                MachineApiErrorKind::InvalidBatchPolicy,
            ),
            (
                client.replay("{}").unwrap_err(),
                AiSearchMachineApiEndpointKind::Replay,
                MachineApiErrorKind::InvalidReplayPlan,
            ),
            (
                client.verify("{}").unwrap_err(),
                AiSearchMachineApiEndpointKind::Verify,
                MachineApiErrorKind::InvalidVerifyRequest,
            ),
        ];

        for (error, endpoint, kind) in cases {
            match error {
                AiSearchMachineApiError::FakeRequestValidation {
                    endpoint: actual,
                    error,
                } => {
                    assert_eq!(actual, endpoint);
                    assert_eq!(error.kind, kind);
                }
                other => panic!("expected fake request validation error, got {other:?}"),
            }
        }
        assert!(client.calls().is_empty());
    }

    #[test]
    fn ai_search_mvp_config_accepts_omitted_scheduler_limits() {
        let config = parse_ai_search_mvp_controller_config(valid_config_json()).unwrap();

        assert_eq!(config.search_budget.max_tactics_per_node, 16);
        assert_eq!(config.scheduler_limits, None);
        assert_eq!(config.batch_policy.max_evaluated_candidates, 16);
    }

    #[test]
    fn ai_search_mvp_config_accepts_present_scheduler_limits() {
        let source = valid_config_json().replace(
            r#""batch_policy""#,
            r#""scheduler_limits":{"per_candidate_timeout_ms":100,"batch_timeout_ms":1000,"max_memory_mb":1024},"batch_policy""#,
        );

        let config = parse_ai_search_mvp_controller_config(&source).unwrap();

        assert_eq!(
            config.scheduler_limits,
            Some(MachineBatchSchedulerLimits {
                per_candidate_timeout_ms: Some(100),
                batch_timeout_ms: Some(1000),
                max_memory_mb: Some(1024),
            })
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_non_mvp_tactics_per_node() {
        let source = valid_config_json().replace(
            r#""max_tactics_per_node": 16"#,
            r#""max_tactics_per_node": 8"#,
        );

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.path,
            JsonPath::root()
                .field("search_budget")
                .field("max_tactics_per_node")
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_tactics_per_node_outside_u32_range() {
        let source = valid_config_json().replace(
            r#""max_tactics_per_node": 16"#,
            r#""max_tactics_per_node": 4294967296"#,
        );

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field: "max_tactics_per_node",
                raw: "4294967296".to_owned(),
                error: StrictUnsignedIntegerError::ExceedsMaximum {
                    max: u64::from(u32::MAX)
                },
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_null_scheduler_limits() {
        let source = valid_config_json().replace(
            r#""batch_policy""#,
            r#""scheduler_limits":null,"batch_policy""#,
        );

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidSchedulerLimits);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::NullField {
                field: "scheduler_limits"
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_unknown_field() {
        let source =
            valid_config_json().replace(r#""batch_policy""#, r#""unknown":true,"batch_policy""#);

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::UnknownField {
                field: "unknown".to_owned()
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_float_search_budget() {
        let source = valid_config_json().replace(r#""max_nodes": 10000"#, r#""max_nodes": 1.5"#);

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field: "max_nodes",
                raw: "1.5".to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_negative_search_budget() {
        let source = valid_config_json().replace(r#""max_nodes": 10000"#, r#""max_nodes": -1"#);

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field: "max_nodes",
                raw: "-1".to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_max_depth_outside_u32_range() {
        let source =
            valid_config_json().replace(r#""max_depth": 64"#, r#""max_depth": 4294967296"#);

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field: "max_depth",
                raw: "4294967296".to_owned(),
                error: StrictUnsignedIntegerError::ExceedsMaximum {
                    max: u64::from(u32::MAX)
                },
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_scheduler_zero() {
        let source = valid_config_json().replace(
            r#""batch_policy""#,
            r#""scheduler_limits":{"batch_timeout_ms":0},"batch_policy""#,
        );

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidSchedulerLimits);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field: "batch_timeout_ms",
                raw: "0".to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            }
        );
    }

    #[test]
    fn ai_search_mvp_config_rejects_scheduler_string() {
        let source = valid_config_json().replace(
            r#""batch_policy""#,
            r#""scheduler_limits":{"batch_timeout_ms":"1000"},"batch_policy""#,
        );

        let err = parse_ai_search_mvp_controller_config(&source).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidSchedulerLimits);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "batch_timeout_ms",
                expected: JsonFieldType::UnsignedInteger { max: u64::MAX },
                actual: crate::JsonValueKind::String,
            }
        );
    }
}

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use npa_cert::{ExportKind, Hash, Name};
use npa_kernel::{level::normalize_level, Level};
use npa_tactic::{
    core_expr_hash, plan_lazy_diagnostic_profile, tactic_budget_canonical_bytes,
    tactic_budget_hash, CandidateApplyArg, CandidateRewriteRuleRef, CasesPayload, ChangePayload,
    CongrPayload, ConstructorPayload, ConstructorSelection, ContradictionMode,
    ContradictionPayload, DiagnosticBudget, DiagnosticBudgetReport, DiagnosticProfile,
    DiagnosticRequestPath, GeneralInductionPayload, GeneralizePayload, GoalId, HavePayload,
    LocalLemmaInsertionPolicy, LocalLemmaProof, MachineProofState, MachineTacticBatchPolicy,
    MachineTacticCandidate, MachineTacticDiagnostic, MachineTacticDiagnosticKind,
    MachineTacticFeature, MachineTacticProfileVersion, OccurrencePath, RawMachineTerm,
    RefinePayload, RevertDependencyPolicy, RevertPayload, RewriteDirection, RewriteSite,
    SimpRuleRef, SpecializePayload, SpecializeResultPolicy, SubstPayload,
    SufficesContinuationPolicy, SufficesPayload, TacticBudget, TacticHead, TacticTarget,
    UnfoldPayload,
};
use sha2::{Digest, Sha256};

use crate::adapter::{
    machine_tactic_run_machine_tactic_with_budget,
    machine_tactic_validate_machine_tactic_candidate_for_state, MachineApiDiagnosticPhase,
    MachineApiDiagnosticProjection, MachineApiTacticKind, MachineTacticAdapterError,
    ValidatedMachineTactic,
};
use crate::current::{encode_machine_axiom_ref_wire, MachineAxiomRefWire};
use crate::diagnostic::{
    machine_api_projection_diagnostic_tree, MachineDiagnosticTree,
    MachineDiagnosticTreeAdapterContext, MachineDiagnosticTreeAdapterError,
};
use crate::json::{JsonDocument, JsonMember, JsonValue, JsonValueKind};
use crate::snapshot::{
    MachineSnapshotLookupError, MachineSnapshotMaterializationContext,
    MachineSnapshotMaterializationError, MachineSnapshotStoreError,
};
use crate::trust::{
    proof_candidate_axiom_policy_hash, proof_candidate_environment_hash,
    proof_candidate_feature_profile_hash, proof_candidate_goal_fingerprint,
    proof_candidate_identity_hash, proof_candidate_import_closure_hash, ProofCandidateIdentity,
    ProofCandidateKind, ProofCandidateSourceKind,
};
use crate::types::{
    is_machine_local_name, is_machine_universe_param_name, parse_goal_id_wire,
    parse_machine_surface_renderable_name_wire, ExprPath, HashString, MachineApiCompactErrorWire,
    MachineApiErrorResponse, MachineApiErrorWire, MachineApiResponseStatus,
    MachineApiSchedulerResponse, MachineProofSession, MachineSchedulerArtifact,
    MachineSchedulerArtifactKind, MachineSchedulerArtifactScope, SessionId, SnapshotId,
};
use crate::validation::{
    delayed_json_payload, parse_request_body, parse_strict_u64_token, validate_json_object,
    DelayedJsonPayload, FieldSpec, JsonFieldType, JsonPath, JsonPathElement, MachineApiErrorKind,
    MachineApiRequestError, MachineApiRequestErrorReason, ObjectSchema, StrictUnsignedIntegerError,
};
use crate::{
    MachineApiDiagnosticCanonicalizationError, MachineApiResponseEnvelope,
    MachineApiUpstreamDiagnostic,
};

const BUDGET_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "max_tactic_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_whnf_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_conversion_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_rewrite_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_meta_allocations",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_expr_nodes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

pub(crate) const STRUCTURAL_V2_REQUIRED_FEATURES: &[MachineTacticFeature] =
    &[MachineTacticFeature::StructuralTactics];

const RUN_SCHEDULER_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional(
        "timeout_ms",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::optional(
        "max_memory_mb",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

const BATCH_POLICY_FIELDS: &[FieldSpec] = &[
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

const BATCH_SCHEDULER_FIELDS: &[FieldSpec] = &[
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

const LAZY_DIAGNOSTIC_REQUEST_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("session_id", JsonFieldType::String),
    FieldSpec::required("snapshot_id", JsonFieldType::String),
    FieldSpec::required("state_fingerprint", JsonFieldType::String),
    FieldSpec::required("goal_id", JsonFieldType::String),
    FieldSpec::required("candidate", JsonFieldType::Object),
    FieldSpec::required("deterministic_budget", JsonFieldType::Object),
    FieldSpec::required("diagnostic_hash", JsonFieldType::String),
    FieldSpec::required("profile", JsonFieldType::String),
    FieldSpec::required("diagnostic_budget", JsonFieldType::Object),
];

const DIAGNOSTIC_BUDGET_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "max_graph_nodes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_expression_paths",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_rewrite_site_scans",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_pretty_term_bytes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_repair_proposals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_diagnostic_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

const RAW_MACHINE_TERM_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("source", JsonFieldType::String)];
const EXACT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("term", JsonFieldType::Object),
];
const INTRO_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("name", JsonFieldType::String),
];
const APPLY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("head", JsonFieldType::Object),
    FieldSpec::required("universe_args", JsonFieldType::Array),
    FieldSpec::required("args", JsonFieldType::Array),
];
const REWRITE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("rule", JsonFieldType::Object),
    FieldSpec::required("direction", JsonFieldType::String),
    FieldSpec::required("site", JsonFieldType::String),
];
const REWRITE_RULE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("head", JsonFieldType::Object),
    FieldSpec::required("universe_args", JsonFieldType::Array),
    FieldSpec::required("args", JsonFieldType::Array),
];
const SIMP_LITE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("rules", JsonFieldType::Array),
];
const INDUCTION_NAT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("local_name", JsonFieldType::String),
];
const CONSTRUCTOR_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("selection", JsonFieldType::Object),
    FieldSpec::optional(
        "max_new_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
];
const CONSTRUCTOR_AUTO_SELECTION_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("mode", JsonFieldType::String)];
const CONSTRUCTOR_EXPLICIT_SELECTION_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("constructor", JsonFieldType::Object),
];
const CASES_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("major_local", JsonFieldType::String),
    FieldSpec::required("motive", JsonFieldType::Object).allow_null(),
    FieldSpec::required("branch_names", JsonFieldType::Array),
    FieldSpec::optional(
        "max_new_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
];
const GENERAL_INDUCTION_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("major_local", JsonFieldType::String),
    FieldSpec::required("recursor", JsonFieldType::Object),
    FieldSpec::required("motive", JsonFieldType::Object).allow_null(),
    FieldSpec::required("generalized_locals", JsonFieldType::Array),
    FieldSpec::required("branch_names", JsonFieldType::Array),
    FieldSpec::required(
        "max_new_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const REFINE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("term", JsonFieldType::Object),
    FieldSpec::optional(
        "max_holes",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
];
const HAVE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("type", JsonFieldType::Object),
    FieldSpec::required("proof", JsonFieldType::Object),
    FieldSpec::required("insertion", JsonFieldType::String),
];
const SUFFICES_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::required("proof", JsonFieldType::Object),
    FieldSpec::required("continuation", JsonFieldType::String),
];
const LOCAL_LEMMA_PROOF_CHILD_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("mode", JsonFieldType::String)];
const LOCAL_LEMMA_PROOF_TERM_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("term", JsonFieldType::Object),
];
const SPECIALIZE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("local_name", JsonFieldType::String),
    FieldSpec::required("universe_args", JsonFieldType::Array),
    FieldSpec::required("args", JsonFieldType::Array),
    FieldSpec::required("result_name", JsonFieldType::String).allow_null(),
    FieldSpec::required("result_policy", JsonFieldType::String),
];
const REVERT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("locals", JsonFieldType::Array),
    FieldSpec::required("dependency_policy", JsonFieldType::String),
];
const GENERALIZE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::required("term", JsonFieldType::Object),
    FieldSpec::required("occurrences", JsonFieldType::Array),
    FieldSpec::required("name_hint", JsonFieldType::String).allow_null(),
];
const CHANGE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::required("replacement", JsonFieldType::Object),
    FieldSpec::required("occurrences", JsonFieldType::Array),
];
const UNFOLD_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::required("constant", JsonFieldType::Object),
    FieldSpec::required("occurrences", JsonFieldType::Array),
    FieldSpec::optional(
        "max_delta_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
];
const CONGR_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::optional(
        "max_depth",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
    FieldSpec::optional(
        "max_new_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
];
const SUBST_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("equality_local", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
    FieldSpec::required("direction", JsonFieldType::String),
    FieldSpec::required("occurrences", JsonFieldType::Array),
];
const CONTRADICTION_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("major_local", JsonFieldType::String).allow_null(),
];
const RESERVED_SOLVER_FIELDS: &[FieldSpec] = &[FieldSpec::required("kind", JsonFieldType::String)];
const TARGET_GOAL_FIELDS: &[FieldSpec] = &[FieldSpec::required("mode", JsonFieldType::String)];
const TARGET_LOCAL_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("name", JsonFieldType::String),
];
const OCCURRENCE_PATH_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("indices", JsonFieldType::Array)];
const IMPORTED_HEAD_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
];
const CURRENT_HEAD_FIELDS: &[FieldSpec] = IMPORTED_HEAD_FIELDS;
const LOCAL_HEAD_FIELDS: &[FieldSpec] = &[FieldSpec::required("name", JsonFieldType::String)];
const ARG_TERM_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("term", JsonFieldType::Object),
];
const ARG_SUBGOAL_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("name_hint", JsonFieldType::String).allow_null(),
];
const ARG_INFER_FIELDS: &[FieldSpec] = &[FieldSpec::required("mode", JsonFieldType::String)];
const SIMP_RULE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    FieldSpec::required("direction", JsonFieldType::String),
];

pub const REPAIR_OPERATOR_SCHEMA: &str = "npa.repair_operator.v1";
pub const REPAIR_OPERATOR_HASH_DOMAIN: &str = "npa.machine-api.repair-operator.hash.v1";
pub const REPAIR_CHAIN_CANDIDATE_IDENTITY_HASH_DOMAIN: &str =
    "npa.machine-api.repair-chain.candidate-identity.v1";
pub const DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN: usize = 16;

const REPAIR_OPERATOR_TOP_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("operator", JsonFieldType::String),
    FieldSpec::required("payload", JsonFieldType::Object),
];
const REPAIR_OPERATOR_GOAL_FIELDS: &[FieldSpec] =
    &[FieldSpec::optional("goal_id", JsonFieldType::String)];
const REPAIR_OPERATOR_PATH_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("path", JsonFieldType::Array),
];
const REPAIR_OPERATOR_ARGUMENT_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required(
        "binder",
        JsonFieldType::UnsignedInteger {
            max: u32::MAX as u64,
        },
    ),
    FieldSpec::required("term", JsonFieldType::Object),
];
const REPAIR_OPERATOR_UNIVERSE_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("param", JsonFieldType::String),
    FieldSpec::required("level", JsonFieldType::String),
];
const REPAIR_OPERATOR_SPECIALIZE_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("local", JsonFieldType::Object),
    FieldSpec::required("args", JsonFieldType::Array),
];
const REPAIR_OPERATOR_GLOBAL_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("constant", JsonFieldType::Object),
];
const REPAIR_OPERATOR_TERM_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("term", JsonFieldType::Object),
];
const REPAIR_OPERATOR_LOCAL_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("local", JsonFieldType::Object),
];
const REPAIR_OPERATOR_CHANGE_GOAL_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("target", JsonFieldType::Object),
];
const REPAIR_OPERATOR_REDUCE_SIMP_SET_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("remove", JsonFieldType::Array),
];
const REPAIR_OPERATOR_SWITCH_STRATEGY_FIELDS: &[FieldSpec] = &[
    FieldSpec::optional("goal_id", JsonFieldType::String),
    FieldSpec::required("profile", JsonFieldType::String),
];
const REPAIR_LOCAL_REF_FIELDS: &[FieldSpec] = &[FieldSpec::required("name", JsonFieldType::String)];
const REPAIR_GLOBAL_REF_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("name", JsonFieldType::String)];
const REPAIR_CHECKED_TERM_PAYLOAD_FIELDS: &[FieldSpec] =
    &[FieldSpec::required("term_hash", JsonFieldType::String)];

const MAX_NUMERIC_UNIVERSE_LEVEL: u64 = 1024;

pub type MachineTacticRunResponse = MachineApiResponseEnvelope<
    MachineTacticRunSuccessFields,
    MachineTacticRunErrorObject,
    MachineTacticRunErrorFields,
    MachineTacticRunSchedulerFields,
>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunSuccessFields {
    pub result: MachineTacticRunSuccessResult,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunSuccessResult {
    pub kind: MachineTacticRunResultKind,
    pub previous_state_fingerprint: Hash,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
    pub next_snapshot_id: SnapshotId,
    pub next_state_fingerprint: Hash,
    pub closed_goals: Vec<npa_tactic::GoalId>,
    pub new_goals: Vec<npa_tactic::GoalId>,
    pub delta: MachineTacticRunDeltaSummary,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineTacticRunResultKind {
    Closed,
    Expanded,
}

impl MachineTacticRunResultKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Closed => "closed",
            Self::Expanded => "expanded",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunDeltaSummary {
    pub proof_delta_hash: Hash,
    pub assigned_goal: npa_tactic::GoalId,
    pub assigned_proof_expr_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunErrorObject {
    pub diagnostic: MachineApiErrorWire,
    pub candidate_hash: Option<Hash>,
    pub deterministic_budget_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunErrorFields {
    pub unchanged_state_fingerprint: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunSchedulerFields {
    pub previous_state_fingerprint: Hash,
    pub deterministic_budget_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachineTacticRunResponse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticRunRequest<'src> {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: npa_tactic::GoalId,
    pub candidate: DelayedJsonPayload<'src>,
    pub deterministic_budget: TacticBudget,
    pub scheduler_limits: MachineRunSchedulerLimits,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MachineRunSchedulerLimits {
    pub timeout_ms: Option<u64>,
    pub max_memory_mb: Option<u64>,
}

pub type MachineTacticBatchResponse = MachineApiResponseEnvelope<
    MachineTacticBatchOkFields,
    MachineApiErrorWire,
    (),
    MachineTacticBatchSchedulerFields,
>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticBatchOkFields {
    pub previous_state_fingerprint: Hash,
    pub deterministic_budget_hash: Hash,
    pub results: Vec<MachineTacticBatchItemResponse>,
    pub success_count: u32,
    pub failure_count: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineTacticBatchItemResponse {
    Success {
        candidate_id: String,
        candidate_hash: Hash,
        next_snapshot_id: SnapshotId,
        next_state_fingerprint: Hash,
        proof_delta_hash: Hash,
    },
    Error {
        candidate_id: String,
        candidate_hash: Option<Hash>,
        diagnostic: MachineApiCompactErrorWire,
    },
}

impl MachineTacticBatchItemResponse {
    pub const fn is_success(&self) -> bool {
        matches!(self, Self::Success { .. })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticBatchSchedulerFields {
    pub previous_state_fingerprint: Hash,
    pub deterministic_budget_hash: Hash,
    pub completed_prefix_len: u32,
    pub results: Vec<MachineTacticBatchItemResponse>,
    pub success_count: u32,
    pub failure_count: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticBatchError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachineTacticBatchResponse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticBatchRequest<'src> {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: npa_tactic::GoalId,
    pub candidates: Vec<MachineTacticBatchCandidateRequest<'src>>,
    pub deterministic_budget: TacticBudget,
    pub batch_policy: MachineTacticBatchPolicy,
    pub scheduler_limits: MachineBatchSchedulerLimits,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticBatchCandidateRequest<'src> {
    pub candidate_id: String,
    pub candidate: DelayedJsonPayload<'src>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MachineBatchSchedulerLimits {
    pub per_candidate_timeout_ms: Option<u64>,
    pub batch_timeout_ms: Option<u64>,
    pub max_memory_mb: Option<u64>,
}

pub const LAZY_DIAGNOSTIC_CACHE_PRODUCER_VERSION: &str = "npa.machine-api.lazy-diagnostic-cache.v1";
pub const LAZY_DIAGNOSTIC_BUDGET_HASH_DOMAIN: &str =
    "npa.machine-api.lazy-diagnostic-budget.hash.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLazyDiagnosticRequest<'src> {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate: DelayedJsonPayload<'src>,
    pub deterministic_budget: TacticBudget,
    pub diagnostic_hash: Hash,
    pub profile: DiagnosticProfile,
    pub diagnostic_budget: DiagnosticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachineLazyDiagnosticCacheKey {
    pub diagnostic_hash: Hash,
    pub profile: DiagnosticProfile,
    pub environment_hash: Hash,
    pub state_fingerprint: Hash,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLazyDiagnosticCacheMetadata {
    pub producer_version: String,
    pub key: MachineLazyDiagnosticCacheKey,
    pub diagnostic_budget: DiagnosticBudget,
    pub diagnostic_budget_hash: Hash,
    pub truncation_report: Option<DiagnosticBudgetReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLazyDiagnosticCacheEntry {
    pub metadata: MachineLazyDiagnosticCacheMetadata,
    pub diagnostic_tree: MachineDiagnosticTree,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MachineLazyDiagnosticCacheCounters {
    pub full_diagnostics_generated: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub success_path_full_diagnostic_attempts: u64,
    pub full_diagnostics_generated_on_success: u64,
    pub theorem_graph_calls: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineLazyDiagnosticCache {
    entries: BTreeMap<MachineLazyDiagnosticCacheKey, MachineLazyDiagnosticCacheEntry>,
    counters: MachineLazyDiagnosticCacheCounters,
}

impl MachineLazyDiagnosticCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    pub const fn counters(&self) -> MachineLazyDiagnosticCacheCounters {
        self.counters
    }

    fn lookup(
        &mut self,
        expected: &MachineLazyDiagnosticCacheMetadata,
    ) -> Result<MachineLazyDiagnosticCacheEntry, MachineLazyDiagnosticCacheMissReason> {
        if let Some(entry) = self.entries.get(&expected.key) {
            if entry.metadata.producer_version != LAZY_DIAGNOSTIC_CACHE_PRODUCER_VERSION {
                self.counters.cache_misses += 1;
                return Err(MachineLazyDiagnosticCacheMissReason::ProducerVersionMismatch);
            }
            if entry.metadata.diagnostic_budget_hash != expected.diagnostic_budget_hash {
                self.counters.cache_misses += 1;
                return Err(MachineLazyDiagnosticCacheMissReason::DiagnosticBudgetHashMismatch);
            }
            self.counters.cache_hits += 1;
            return Ok(entry.clone());
        }

        self.counters.cache_misses += 1;
        Err(self.miss_reason(&expected.key))
    }

    fn insert(&mut self, entry: MachineLazyDiagnosticCacheEntry) {
        self.entries.insert(entry.metadata.key.clone(), entry);
    }

    fn record_full_diagnostic_generation(&mut self) {
        self.counters.full_diagnostics_generated += 1;
    }

    fn record_success_path_full_diagnostic_attempt(&mut self) {
        self.counters.success_path_full_diagnostic_attempts += 1;
    }

    fn miss_reason(
        &self,
        expected: &MachineLazyDiagnosticCacheKey,
    ) -> MachineLazyDiagnosticCacheMissReason {
        for key in self.entries.keys() {
            if key.diagnostic_hash != expected.diagnostic_hash || key.profile != expected.profile {
                continue;
            }
            if key.environment_hash != expected.environment_hash {
                return MachineLazyDiagnosticCacheMissReason::StaleEnvironmentHash;
            }
            if key.state_fingerprint != expected.state_fingerprint {
                return MachineLazyDiagnosticCacheMissReason::StaleStateFingerprint;
            }
            if key.deterministic_budget_hash != expected.deterministic_budget_hash {
                return MachineLazyDiagnosticCacheMissReason::DeterministicBudgetHashMismatch;
            }
            if key.candidate_hash != expected.candidate_hash {
                return MachineLazyDiagnosticCacheMissReason::CandidateHashMismatch;
            }
        }
        MachineLazyDiagnosticCacheMissReason::Absent
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineLazyDiagnosticCacheMissReason {
    Absent,
    StaleEnvironmentHash,
    StaleStateFingerprint,
    CandidateHashMismatch,
    DeterministicBudgetHashMismatch,
    DiagnosticBudgetHashMismatch,
    ProducerVersionMismatch,
}

impl MachineLazyDiagnosticCacheMissReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Absent => "absent",
            Self::StaleEnvironmentHash => "stale_environment_hash",
            Self::StaleStateFingerprint => "stale_state_fingerprint",
            Self::CandidateHashMismatch => "candidate_hash_mismatch",
            Self::DeterministicBudgetHashMismatch => "deterministic_budget_hash_mismatch",
            Self::DiagnosticBudgetHashMismatch => "diagnostic_budget_hash_mismatch",
            Self::ProducerVersionMismatch => "producer_version_mismatch",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineLazyDiagnosticCacheStatus {
    Disabled,
    Hit,
    Miss {
        reason: MachineLazyDiagnosticCacheMissReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLazyDiagnosticOk {
    pub diagnostic_tree: MachineDiagnosticTree,
    pub metadata: MachineLazyDiagnosticCacheMetadata,
    pub cache_status: MachineLazyDiagnosticCacheStatus,
    pub counters: MachineLazyDiagnosticCacheCounters,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineLazyDiagnosticError {
    Request(MachineApiRequestError),
    UnknownSession { session_id: SessionId },
    SnapshotLookup(MachineSnapshotLookupError),
    GoalNotOpen { goal_id: GoalId },
    DiagnosticCanonicalization(MachineApiDiagnosticCanonicalizationError),
    DiagnosticTree(MachineDiagnosticTreeAdapterError),
    DiagnosticHashMismatch { requested: Hash, actual: Hash },
    CandidateSucceeded,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepairLocalRef {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepairGlobalRef {
    pub name: Name,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepairCheckedTermPayload {
    pub term_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RepairStrategyProfile {
    Default,
    ApplyExact,
    SmallerSimp,
    LowerGoalGrowth,
}

impl RepairStrategyProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::ApplyExact => "apply_exact",
            Self::SmallerSimp => "smaller_simp",
            Self::LowerGoalGrowth => "lower_goal_growth",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "default" => Some(Self::Default),
            "apply_exact" => Some(Self::ApplyExact),
            "smaller_simp" => Some(Self::SmallerSimp),
            "lower_goal_growth" => Some(Self::LowerGoalGrowth),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RepairOperatorKind {
    ReverseRewrite,
    SelectRewriteOccurrence,
    InstantiateArgument,
    InstantiateUniverse,
    IntroduceBinder,
    SpecializeHypothesis,
    Unfold,
    Fold,
    InsertEqTransport,
    Generalize,
    Revert,
    ChangeGoal,
    ReduceSimpSet,
    SwitchStrategy,
}

impl RepairOperatorKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReverseRewrite => "ReverseRewrite",
            Self::SelectRewriteOccurrence => "SelectRewriteOccurrence",
            Self::InstantiateArgument => "InstantiateArgument",
            Self::InstantiateUniverse => "InstantiateUniverse",
            Self::IntroduceBinder => "IntroduceBinder",
            Self::SpecializeHypothesis => "SpecializeHypothesis",
            Self::Unfold => "Unfold",
            Self::Fold => "Fold",
            Self::InsertEqTransport => "InsertEqTransport",
            Self::Generalize => "Generalize",
            Self::Revert => "Revert",
            Self::ChangeGoal => "ChangeGoal",
            Self::ReduceSimpSet => "ReduceSimpSet",
            Self::SwitchStrategy => "SwitchStrategy",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "ReverseRewrite" => Some(Self::ReverseRewrite),
            "SelectRewriteOccurrence" => Some(Self::SelectRewriteOccurrence),
            "InstantiateArgument" => Some(Self::InstantiateArgument),
            "InstantiateUniverse" => Some(Self::InstantiateUniverse),
            "IntroduceBinder" => Some(Self::IntroduceBinder),
            "SpecializeHypothesis" => Some(Self::SpecializeHypothesis),
            "Unfold" => Some(Self::Unfold),
            "Fold" => Some(Self::Fold),
            "InsertEqTransport" => Some(Self::InsertEqTransport),
            "Generalize" => Some(Self::Generalize),
            "Revert" => Some(Self::Revert),
            "ChangeGoal" => Some(Self::ChangeGoal),
            "ReduceSimpSet" => Some(Self::ReduceSimpSet),
            "SwitchStrategy" => Some(Self::SwitchStrategy),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairOperator {
    ReverseRewrite {
        goal_id: Option<GoalId>,
    },
    SelectRewriteOccurrence {
        goal_id: Option<GoalId>,
        path: ExprPath,
    },
    InstantiateArgument {
        goal_id: Option<GoalId>,
        binder: u32,
        term: RepairCheckedTermPayload,
    },
    InstantiateUniverse {
        goal_id: Option<GoalId>,
        param: String,
        level: Level,
    },
    IntroduceBinder {
        goal_id: Option<GoalId>,
    },
    SpecializeHypothesis {
        goal_id: Option<GoalId>,
        local: RepairLocalRef,
        args: Vec<RepairCheckedTermPayload>,
    },
    Unfold {
        goal_id: Option<GoalId>,
        constant: RepairGlobalRef,
    },
    Fold {
        goal_id: Option<GoalId>,
        constant: RepairGlobalRef,
    },
    InsertEqTransport {
        goal_id: Option<GoalId>,
    },
    Generalize {
        goal_id: Option<GoalId>,
        term: RepairCheckedTermPayload,
    },
    Revert {
        goal_id: Option<GoalId>,
        local: RepairLocalRef,
    },
    ChangeGoal {
        goal_id: Option<GoalId>,
        target: RepairCheckedTermPayload,
    },
    ReduceSimpSet {
        goal_id: Option<GoalId>,
        remove: Vec<RepairGlobalRef>,
    },
    SwitchStrategy {
        goal_id: Option<GoalId>,
        profile: RepairStrategyProfile,
    },
}

impl RepairOperator {
    pub const fn kind(&self) -> RepairOperatorKind {
        match self {
            Self::ReverseRewrite { .. } => RepairOperatorKind::ReverseRewrite,
            Self::SelectRewriteOccurrence { .. } => RepairOperatorKind::SelectRewriteOccurrence,
            Self::InstantiateArgument { .. } => RepairOperatorKind::InstantiateArgument,
            Self::InstantiateUniverse { .. } => RepairOperatorKind::InstantiateUniverse,
            Self::IntroduceBinder { .. } => RepairOperatorKind::IntroduceBinder,
            Self::SpecializeHypothesis { .. } => RepairOperatorKind::SpecializeHypothesis,
            Self::Unfold { .. } => RepairOperatorKind::Unfold,
            Self::Fold { .. } => RepairOperatorKind::Fold,
            Self::InsertEqTransport { .. } => RepairOperatorKind::InsertEqTransport,
            Self::Generalize { .. } => RepairOperatorKind::Generalize,
            Self::Revert { .. } => RepairOperatorKind::Revert,
            Self::ChangeGoal { .. } => RepairOperatorKind::ChangeGoal,
            Self::ReduceSimpSet { .. } => RepairOperatorKind::ReduceSimpSet,
            Self::SwitchStrategy { .. } => RepairOperatorKind::SwitchStrategy,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RepairDiagnosticCategory {
    UnsupportedMachineTactic,
    InvalidReplayPlan,
    KernelRejectedAfterVerify,
    UnknownName,
    TypeMismatch,
    ExpectedPiType,
    RewriteRuleInvalid,
    SimpNoProgress,
    ImplicitArgumentRequired,
    UniverseMismatch,
    TooManyGoals,
    BudgetExceeded,
}

impl RepairDiagnosticCategory {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedMachineTactic => "unsupported_machine_tactic",
            Self::InvalidReplayPlan => "invalid_replay_plan",
            Self::KernelRejectedAfterVerify => "kernel_rejected_after_verify",
            Self::UnknownName => "unknown_name",
            Self::TypeMismatch => "type_mismatch",
            Self::ExpectedPiType => "expected_pi_type",
            Self::RewriteRuleInvalid => "rewrite_rule_invalid",
            Self::SimpNoProgress => "simp_no_progress",
            Self::ImplicitArgumentRequired => "implicit_argument_required",
            Self::UniverseMismatch => "universe_mismatch",
            Self::TooManyGoals => "too_many_goals",
            Self::BudgetExceeded => "budget_exceeded",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepairProposalCategory {
    ProofStateRepair,
    ImportChangeProposal,
    AxiomChangeProposal,
}

impl RepairProposalCategory {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProofStateRepair => "proof_state_repair",
            Self::ImportChangeProposal => "import_change_proposal",
            Self::AxiomChangeProposal => "axiom_change_proposal",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairOperatorValidationError {
    BudgetExceeded {
        actual: usize,
        max: usize,
    },
    DuplicateOperator {
        operator_hash: Hash,
    },
    DisallowedOperator {
        category: RepairDiagnosticCategory,
        operator: RepairOperatorKind,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepairProposalSource {
    LocalOperator,
    RetrievalCandidate,
}

impl RepairProposalSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LocalOperator => "local_operator",
            Self::RetrievalCandidate => "retrieval_candidate",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairProposalProvenance {
    pub source: RepairProposalSource,
    pub category: RepairDiagnosticCategory,
    pub diagnostic_path: Vec<String>,
    pub state_fingerprint: Hash,
    pub deterministic_budget_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairProposalValidationError {
    NoOpenGoal,
    DisallowedOperator {
        category: RepairDiagnosticCategory,
        operator: RepairOperatorKind,
    },
    OperatorNotConvertible {
        operator: RepairOperatorKind,
    },
    CandidateRejected {
        operator: Option<RepairOperatorKind>,
        diagnostic_kind: MachineApiErrorKind,
        phase: MachineApiDiagnosticPhase,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairProposalValidation {
    Candidate {
        candidate: MachineTacticCandidate,
        validated: Box<ValidatedMachineTactic>,
    },
    Rejected {
        error: RepairProposalValidationError,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairGeneratedProposal {
    pub provenance: RepairProposalProvenance,
    pub operator: Option<RepairOperator>,
    pub operator_hash: Option<Hash>,
    pub validation: RepairProposalValidation,
}

#[derive(Clone, Copy)]
pub struct RepairGenerationContext<'a> {
    pub state: &'a MachineProofState,
    pub state_fingerprint: Hash,
    pub diagnostic: &'a MachineApiDiagnosticProjection,
    pub deterministic_budget: TacticBudget,
    pub profile_version: MachineTacticProfileVersion,
    pub required_features: &'a [MachineTacticFeature],
    pub max_proposals: usize,
}

pub struct RepairRetrievalRequest<'a> {
    pub category: RepairDiagnosticCategory,
    pub diagnostic: &'a MachineApiDiagnosticProjection,
    pub state_fingerprint: Hash,
    pub deterministic_budget_hash: Hash,
    pub goal_id: GoalId,
}

pub trait RepairRetrievalAdapter {
    fn repair_candidates(
        &self,
        _request: &RepairRetrievalRequest<'_>,
    ) -> Vec<MachineTacticCandidate> {
        Vec::new()
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct EmptyRepairRetrievalAdapter;

impl RepairRetrievalAdapter for EmptyRepairRetrievalAdapter {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RepairChainLimits {
    pub max_repair_depth: usize,
    pub max_total_candidates: usize,
    pub max_generated_goals: usize,
    pub max_repeated_diagnostic_hash_count: usize,
    pub max_repeated_candidate_payload_hash_count: usize,
    pub max_proposals_per_error_category: usize,
}

impl Default for RepairChainLimits {
    fn default() -> Self {
        Self {
            max_repair_depth: 8,
            max_total_candidates: 32,
            max_generated_goals: 8,
            max_repeated_diagnostic_hash_count: 1,
            max_repeated_candidate_payload_hash_count: 1,
            max_proposals_per_error_category: DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN,
        }
    }
}

#[derive(Clone, Copy)]
pub struct RepairChainRunContext<'a> {
    pub state: &'a MachineProofState,
    pub state_fingerprint: Hash,
    pub diagnostic: &'a MachineApiDiagnosticProjection,
    pub deterministic_budget: TacticBudget,
    pub profile_version: MachineTacticProfileVersion,
    pub required_features: &'a [MachineTacticFeature],
    pub limits: RepairChainLimits,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RepairChainBudgetReport {
    pub consumed_diagnostic_budget: usize,
    pub consumed_tactic_budget: usize,
    pub generated_proposal_count: usize,
    pub suppressed_proposal_count: usize,
    pub considered_candidate_count: usize,
    pub generated_goal_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairChainTerminationReason {
    RepairSucceeded,
    NoRepairCategory,
    NoRepairProposals,
    NoExecutableProposal,
    MaxRepairDepth {
        max: usize,
    },
    MaxTotalCandidates {
        max: usize,
    },
    MaxGeneratedGoals {
        max: usize,
        attempted: usize,
    },
    RepeatedDiagnosticHash {
        diagnostic_hash: Hash,
        count: usize,
        max: usize,
    },
    RepeatedCandidatePayloadHash {
        candidate_payload_hash: Hash,
        count: usize,
        max: usize,
    },
    RepeatedCandidateIdentity {
        candidate_identity_hash: Hash,
    },
    PerErrorCategoryProposalLimit {
        category: RepairDiagnosticCategory,
        max: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepairChainStepOutcome {
    CandidateFailed {
        next_diagnostic_hash: Hash,
    },
    CandidateSucceeded {
        next_state_fingerprint: Hash,
        generated_goals: usize,
    },
    Terminated {
        reason: RepairChainTerminationReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairChainStepReport {
    pub depth: usize,
    pub category: Option<RepairDiagnosticCategory>,
    pub diagnostic_hash: Hash,
    pub generated_proposal_count: usize,
    pub suppressed_proposal_count: usize,
    pub executed_candidate_identity_hash: Option<Hash>,
    pub executed_candidate_payload_hash: Option<Hash>,
    pub outcome: RepairChainStepOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairChainReport {
    pub termination_reason: RepairChainTerminationReason,
    pub budget: RepairChainBudgetReport,
    pub steps: Vec<RepairChainStepReport>,
    pub initial_state_fingerprint: Hash,
    pub final_state_fingerprint: Hash,
    pub final_diagnostic_hash: Option<Hash>,
}

pub const FAILURE_MEMORY_SCHEMA: &str = "npa.failure_memory.v1";
pub const FAILURE_MEMORY_KEY_HASH_DOMAIN: &str = "npa.failure-memory.key-hash.v1";
pub const FAILURE_MEMORY_CANDIDATE_SHAPE_HASH_DOMAIN: &str =
    "npa.failure-memory.candidate-shape-hash.v1";
pub const MINIMAL_FAILING_ARTIFACT_SCHEMA: &str = "npa.minimal_failing_artifact.v1";
pub const MINIMAL_FAILING_ARTIFACT_HASH_DOMAIN: &str =
    "npa.machine-api.minimal-failing-artifact.hash.v1";
pub const FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA: &str = "npa.focused_replay_failure_artifact.v1";
pub const FOCUSED_REPLAY_FAILURE_ARTIFACT_HASH_DOMAIN: &str =
    "npa.machine-api.focused-replay-failure-artifact.hash.v1";
pub const FOCUSED_REPLAY_FAILURE_EXCLUDED_FIELDS: &[&str] = &[
    "raw_prompts",
    "model_completions",
    "secrets",
    "broad_source_context",
    "theorem_graph_scores",
    "unrelated_filesystem_paths",
];
pub const HARD_NEGATIVE_EXPORT_SCHEMA: &str = "npa.hard_negative_export.v1";
pub const HARD_NEGATIVE_EXPORT_HASH_DOMAIN: &str = "npa.machine-api.hard-negative-export.hash.v1";
pub const REPAIR_EFFECTIVENESS_BENCHMARK_SCHEMA: &str = "npa.repair_effectiveness_benchmark.v1";
pub const DIAGNOSTIC_PROFILE_BENCHMARK_SCHEMA: &str = "npa.diagnostic_profile_benchmark.v1";
pub const PERFORMANCE_ISOLATION_GUARDRAIL_SCHEMA: &str = "npa.performance_isolation_guardrail.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RepairBenchmarkErrorCategory {
    TypeMismatch,
    ExpectedPiTarget,
    UnresolvedMetavariable,
    RewriteNoProgress,
    InvalidRewriteRule,
    UniverseMismatch,
    BudgetExceeded,
    StaleState,
    UnsupportedTactic,
}

impl RepairBenchmarkErrorCategory {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TypeMismatch => "type_mismatch",
            Self::ExpectedPiTarget => "expected_pi_target",
            Self::UnresolvedMetavariable => "unresolved_metavariable",
            Self::RewriteNoProgress => "rewrite_no_progress",
            Self::InvalidRewriteRule => "invalid_rewrite_rule",
            Self::UniverseMismatch => "universe_mismatch",
            Self::BudgetExceeded => "budget_exceeded",
            Self::StaleState => "stale_state",
            Self::UnsupportedTactic => "unsupported_tactic",
        }
    }

    pub const fn required_fixture_categories() -> [Self; 9] {
        [
            Self::TypeMismatch,
            Self::ExpectedPiTarget,
            Self::UnresolvedMetavariable,
            Self::RewriteNoProgress,
            Self::InvalidRewriteRule,
            Self::UniverseMismatch,
            Self::BudgetExceeded,
            Self::StaleState,
            Self::UnsupportedTactic,
        ]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairEffectivenessBenchmarkCase {
    pub category: RepairBenchmarkErrorCategory,
    pub repair_succeeded: bool,
    pub repair_depth: u64,
    pub repeated_failure_count: u64,
    pub baseline_candidate_count: u64,
    pub considered_candidate_count: u64,
    pub generated_proposal_count: u64,
    pub invalid_repair_proposal_count: u64,
    pub final_verified_before_repair: bool,
    pub final_verified_after_repair: bool,
    pub new_goal_growth: u64,
}

impl RepairEffectivenessBenchmarkCase {
    pub fn from_repair_chain(
        category: RepairBenchmarkErrorCategory,
        baseline_candidate_count: u64,
        invalid_repair_proposal_count: u64,
        final_verified_before_repair: bool,
        report: &RepairChainReport,
    ) -> Self {
        let repair_succeeded = matches!(
            report.termination_reason,
            RepairChainTerminationReason::RepairSucceeded
        );
        let repeated_failure_count = u64::from(matches!(
            report.termination_reason,
            RepairChainTerminationReason::RepeatedDiagnosticHash { .. }
                | RepairChainTerminationReason::RepeatedCandidatePayloadHash { .. }
                | RepairChainTerminationReason::RepeatedCandidateIdentity { .. }
        ));
        Self {
            category,
            repair_succeeded,
            repair_depth: report.budget.consumed_tactic_budget as u64,
            repeated_failure_count,
            baseline_candidate_count,
            considered_candidate_count: report.budget.considered_candidate_count as u64,
            generated_proposal_count: report.budget.generated_proposal_count as u64,
            invalid_repair_proposal_count,
            final_verified_before_repair,
            final_verified_after_repair: repair_succeeded,
            new_goal_growth: report.budget.generated_goal_count as u64,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RepairEffectivenessCategoryKpis {
    pub fixture_count: u64,
    pub repair_success_count: u64,
    pub average_repair_depth_milli: u64,
    pub repeated_failure_rate_basis_points: u64,
    pub baseline_candidate_count: u64,
    pub considered_candidate_count: u64,
    pub candidate_count_reduction: i64,
    pub final_verified_rate_uplift_basis_points: i64,
    pub invalid_repair_proposal_rate_basis_points: u64,
    pub invalid_repair_proposal_count: u64,
    pub generated_proposal_count: u64,
    pub new_goal_growth: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepairEffectivenessBenchmarkSummary {
    pub schema: &'static str,
    pub fixture_count: u64,
    pub repair_success_by_error_category:
        BTreeMap<RepairBenchmarkErrorCategory, RepairEffectivenessCategoryKpis>,
    pub average_repair_depth_milli: u64,
    pub repeated_failure_rate_basis_points: u64,
    pub candidate_count_reduction: i64,
    pub final_verified_rate_uplift_basis_points: i64,
    pub invalid_repair_proposal_rate_basis_points: u64,
    pub new_goal_growth: u64,
    pub sidecar_only: bool,
}

impl RepairEffectivenessBenchmarkSummary {
    pub const fn reported_kpi_names() -> [&'static str; 7] {
        [
            "repair_success_by_error_category",
            "average_repair_depth",
            "repeated_failure_rate",
            "candidate_count_reduction",
            "final_verified_rate_uplift",
            "invalid_repair_proposal_rate",
            "new_goal_growth",
        ]
    }

    pub fn sidecar_lines(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("fixture_count={}\n", self.fixture_count));
        out.push_str(&format!(
            "average_repair_depth_milli={}\n",
            self.average_repair_depth_milli
        ));
        out.push_str(&format!(
            "repeated_failure_rate_basis_points={}\n",
            self.repeated_failure_rate_basis_points
        ));
        out.push_str(&format!(
            "candidate_count_reduction={}\n",
            self.candidate_count_reduction
        ));
        out.push_str(&format!(
            "final_verified_rate_uplift_basis_points={}\n",
            self.final_verified_rate_uplift_basis_points
        ));
        out.push_str(&format!(
            "invalid_repair_proposal_rate_basis_points={}\n",
            self.invalid_repair_proposal_rate_basis_points
        ));
        out.push_str(&format!("new_goal_growth={}\n", self.new_goal_growth));
        out.push_str("repair_success_by_error_category=true\n");
        for (category, kpis) in &self.repair_success_by_error_category {
            out.push_str(&format!(
                "category.{}.fixture_count={}\n",
                category.as_str(),
                kpis.fixture_count
            ));
            out.push_str(&format!(
                "category.{}.repair_success_count={}\n",
                category.as_str(),
                kpis.repair_success_count
            ));
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosticProfileBenchmarkRow {
    pub profile: DiagnosticProfile,
    pub failure_fixture_count: u64,
    pub success_fixture_count: u64,
    pub diagnostic_tree_bytes: u64,
    pub full_diagnostics_generated: u64,
    pub full_diagnostics_generated_on_success: u64,
    pub theorem_graph_calls: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosticProfileBenchmarkSummary {
    pub schema: &'static str,
    pub rows: Vec<DiagnosticProfileBenchmarkRow>,
    pub full_diagnostics_generated_on_success: u64,
    pub theorem_graph_calls: u64,
    pub sidecar_only: bool,
}

impl DiagnosticProfileBenchmarkSummary {
    pub fn sidecar_lines(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!(
            "full_diagnostics_generated_on_success={}\n",
            self.full_diagnostics_generated_on_success
        ));
        out.push_str(&format!(
            "theorem_graph_calls={}\n",
            self.theorem_graph_calls
        ));
        for row in &self.rows {
            out.push_str(&format!(
                "profile.{}.failure_fixture_count={}\n",
                row.profile.as_str(),
                row.failure_fixture_count
            ));
            out.push_str(&format!(
                "profile.{}.success_fixture_count={}\n",
                row.profile.as_str(),
                row.success_fixture_count
            ));
            out.push_str(&format!(
                "profile.{}.full_diagnostics_generated={}\n",
                row.profile.as_str(),
                row.full_diagnostics_generated
            ));
        }
        out
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MachinePerformanceIsolationCounters {
    pub theorem_graph_calls: u64,
    pub embedding_calls: u64,
    pub llm_calls: u64,
    pub agent_calls: u64,
    pub database_calls: u64,
    pub rich_diagnostic_graph_calls: u64,
    pub full_diagnostics_generated_on_success: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachinePerformanceIsolationGuardrailReport {
    pub schema: &'static str,
    pub counters: MachinePerformanceIsolationCounters,
    pub release_blocked: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachinePerformanceIsolationGuardrailError {
    TheoremGraphCalls { count: u64 },
    EmbeddingCalls { count: u64 },
    LlmCalls { count: u64 },
    AgentCalls { count: u64 },
    DatabaseCalls { count: u64 },
    RichDiagnosticGraphCalls { count: u64 },
    FullDiagnosticsGeneratedOnSuccess { count: u64 },
}

pub fn repair_effectiveness_benchmark_summary(
    cases: impl IntoIterator<Item = RepairEffectivenessBenchmarkCase>,
) -> RepairEffectivenessBenchmarkSummary {
    #[derive(Default)]
    struct Accumulator {
        fixture_count: u64,
        repair_success_count: u64,
        repair_depth: u64,
        repeated_failure_count: u64,
        baseline_candidate_count: u64,
        considered_candidate_count: u64,
        generated_proposal_count: u64,
        invalid_repair_proposal_count: u64,
        final_verified_before_repair_count: u64,
        final_verified_after_repair_count: u64,
        new_goal_growth: u64,
    }

    fn update(acc: &mut Accumulator, case: &RepairEffectivenessBenchmarkCase) {
        acc.fixture_count += 1;
        acc.repair_success_count += u64::from(case.repair_succeeded);
        acc.repair_depth += case.repair_depth;
        acc.repeated_failure_count += case.repeated_failure_count;
        acc.baseline_candidate_count += case.baseline_candidate_count;
        acc.considered_candidate_count += case.considered_candidate_count;
        acc.generated_proposal_count += case.generated_proposal_count;
        acc.invalid_repair_proposal_count += case.invalid_repair_proposal_count;
        acc.final_verified_before_repair_count += u64::from(case.final_verified_before_repair);
        acc.final_verified_after_repair_count += u64::from(case.final_verified_after_repair);
        acc.new_goal_growth += case.new_goal_growth;
    }

    fn kpis(acc: &Accumulator) -> RepairEffectivenessCategoryKpis {
        RepairEffectivenessCategoryKpis {
            fixture_count: acc.fixture_count,
            repair_success_count: acc.repair_success_count,
            average_repair_depth_milli: ratio_milli(acc.repair_depth, acc.fixture_count),
            repeated_failure_rate_basis_points: ratio_basis_points(
                acc.repeated_failure_count,
                acc.fixture_count,
            ),
            baseline_candidate_count: acc.baseline_candidate_count,
            considered_candidate_count: acc.considered_candidate_count,
            candidate_count_reduction: acc.baseline_candidate_count as i64
                - acc.considered_candidate_count as i64,
            final_verified_rate_uplift_basis_points: ratio_basis_points_i64(
                acc.final_verified_after_repair_count as i64
                    - acc.final_verified_before_repair_count as i64,
                acc.fixture_count,
            ),
            invalid_repair_proposal_rate_basis_points: ratio_basis_points(
                acc.invalid_repair_proposal_count,
                acc.generated_proposal_count,
            ),
            invalid_repair_proposal_count: acc.invalid_repair_proposal_count,
            generated_proposal_count: acc.generated_proposal_count,
            new_goal_growth: acc.new_goal_growth,
        }
    }

    let mut total = Accumulator::default();
    let mut by_category = BTreeMap::<RepairBenchmarkErrorCategory, Accumulator>::new();
    for case in cases {
        update(&mut total, &case);
        update(by_category.entry(case.category).or_default(), &case);
    }

    let repair_success_by_error_category = by_category
        .into_iter()
        .map(|(category, acc)| (category, kpis(&acc)))
        .collect();
    let total_kpis = kpis(&total);

    RepairEffectivenessBenchmarkSummary {
        schema: REPAIR_EFFECTIVENESS_BENCHMARK_SCHEMA,
        fixture_count: total_kpis.fixture_count,
        repair_success_by_error_category,
        average_repair_depth_milli: total_kpis.average_repair_depth_milli,
        repeated_failure_rate_basis_points: total_kpis.repeated_failure_rate_basis_points,
        candidate_count_reduction: total_kpis.candidate_count_reduction,
        final_verified_rate_uplift_basis_points: total_kpis.final_verified_rate_uplift_basis_points,
        invalid_repair_proposal_rate_basis_points: total_kpis
            .invalid_repair_proposal_rate_basis_points,
        new_goal_growth: total_kpis.new_goal_growth,
        sidecar_only: true,
    }
}

pub fn diagnostic_profile_benchmark_summary(
    rows: impl IntoIterator<Item = DiagnosticProfileBenchmarkRow>,
) -> DiagnosticProfileBenchmarkSummary {
    let mut rows = rows.into_iter().collect::<Vec<_>>();
    rows.sort_by_key(|row| row.profile);
    let full_diagnostics_generated_on_success = rows
        .iter()
        .map(|row| row.full_diagnostics_generated_on_success)
        .sum();
    let theorem_graph_calls = rows.iter().map(|row| row.theorem_graph_calls).sum();
    DiagnosticProfileBenchmarkSummary {
        schema: DIAGNOSTIC_PROFILE_BENCHMARK_SCHEMA,
        rows,
        full_diagnostics_generated_on_success,
        theorem_graph_calls,
        sidecar_only: true,
    }
}

pub fn performance_isolation_counters_from_lazy_cache(
    counters: MachineLazyDiagnosticCacheCounters,
) -> MachinePerformanceIsolationCounters {
    MachinePerformanceIsolationCounters {
        theorem_graph_calls: counters.theorem_graph_calls,
        full_diagnostics_generated_on_success: counters.full_diagnostics_generated_on_success,
        ..MachinePerformanceIsolationCounters::default()
    }
}

pub fn performance_isolation_guardrail(
    counters: MachinePerformanceIsolationCounters,
) -> Result<MachinePerformanceIsolationGuardrailReport, MachinePerformanceIsolationGuardrailError> {
    if counters.theorem_graph_calls != 0 {
        return Err(
            MachinePerformanceIsolationGuardrailError::TheoremGraphCalls {
                count: counters.theorem_graph_calls,
            },
        );
    }
    if counters.embedding_calls != 0 {
        return Err(MachinePerformanceIsolationGuardrailError::EmbeddingCalls {
            count: counters.embedding_calls,
        });
    }
    if counters.llm_calls != 0 {
        return Err(MachinePerformanceIsolationGuardrailError::LlmCalls {
            count: counters.llm_calls,
        });
    }
    if counters.agent_calls != 0 {
        return Err(MachinePerformanceIsolationGuardrailError::AgentCalls {
            count: counters.agent_calls,
        });
    }
    if counters.database_calls != 0 {
        return Err(MachinePerformanceIsolationGuardrailError::DatabaseCalls {
            count: counters.database_calls,
        });
    }
    if counters.rich_diagnostic_graph_calls != 0 {
        return Err(
            MachinePerformanceIsolationGuardrailError::RichDiagnosticGraphCalls {
                count: counters.rich_diagnostic_graph_calls,
            },
        );
    }
    if counters.full_diagnostics_generated_on_success != 0 {
        return Err(
            MachinePerformanceIsolationGuardrailError::FullDiagnosticsGeneratedOnSuccess {
                count: counters.full_diagnostics_generated_on_success,
            },
        );
    }
    Ok(MachinePerformanceIsolationGuardrailReport {
        schema: PERFORMANCE_ISOLATION_GUARDRAIL_SCHEMA,
        counters,
        release_blocked: false,
    })
}

fn ratio_milli(numerator: u64, denominator: u64) -> u64 {
    numerator
        .saturating_mul(1000)
        .checked_div(denominator)
        .unwrap_or(0)
}

fn ratio_basis_points(numerator: u64, denominator: u64) -> u64 {
    numerator
        .saturating_mul(10_000)
        .checked_div(denominator)
        .unwrap_or(0)
}

fn ratio_basis_points_i64(numerator: i64, denominator: u64) -> i64 {
    numerator
        .saturating_mul(10_000)
        .checked_div(denominator as i64)
        .unwrap_or(0)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MinimalFailingArtifactProofAcceptanceState {
    DiagnosticOnly,
}

impl MinimalFailingArtifactProofAcceptanceState {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DiagnosticOnly => "diagnostic_only",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactImportExport {
    pub name: Name,
    pub kind: String,
    pub decl_interface_hash: Hash,
    pub type_hash: Hash,
    pub body_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactImport {
    pub module: String,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub visible: bool,
    pub exports: Vec<MinimalFailingArtifactImportExport>,
    pub certified_env_decl_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactCheckedCurrentDecl {
    pub source_index: u64,
    pub name: Name,
    pub universe_params: Vec<String>,
    pub type_hash: Hash,
    pub decl_interface_hash: Hash,
    pub core_decl_hash: Hash,
    pub prior_chain_fingerprint: Hash,
    pub checked_env_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactLocal {
    pub name: String,
    pub type_hash: Hash,
    pub value_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactExpectedPolicy {
    pub profile_version: MachineTacticProfileVersion,
    pub required_features: Vec<MachineTacticFeature>,
    pub expected_error_kind: MachineApiErrorKind,
    pub expected_phase: MachineApiDiagnosticPhase,
    pub expected_retryable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifactDiagnostic {
    pub kind: MachineApiErrorKind,
    pub phase: MachineApiDiagnosticPhase,
    pub retryable: bool,
    pub goal_id: Option<GoalId>,
    pub tactic_kind: Option<MachineApiTacticKind>,
    pub primary_name: Option<Name>,
    pub primary_axiom_ref: Option<MachineAxiomRefWire>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
    pub diagnostic_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalFailingArtifact {
    pub artifact_hash: Hash,
    pub sidecar_only: bool,
    pub proof_acceptance_state: MinimalFailingArtifactProofAcceptanceState,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub goal_fingerprint: Hash,
    pub imports: Vec<MinimalFailingArtifactImport>,
    pub checked_current_decls: Vec<MinimalFailingArtifactCheckedCurrentDecl>,
    pub local_context: Vec<MinimalFailingArtifactLocal>,
    pub context_hash: Hash,
    pub target_hash: Hash,
    pub candidate: MachineTacticCandidate,
    pub candidate_payload_hash: Hash,
    pub deterministic_budget: TacticBudget,
    pub deterministic_budget_hash: Hash,
    pub expected_policy: MinimalFailingArtifactExpectedPolicy,
    pub structured_diagnostic: MinimalFailingArtifactDiagnostic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FocusedReplayDeclarationInterface {
    pub module: String,
    pub declaration: Name,
    pub universe_params: Vec<String>,
    pub declaration_interface_hash: Hash,
    pub local_context_hash: Hash,
    pub target_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FocusedReplaySourceFreeVerifierBaseline {
    pub verifier_profile: String,
    pub baseline_reference: String,
    pub state_fingerprint: Hash,
    pub goal_fingerprint: Hash,
    pub import_identity_hash: Hash,
    pub checked_current_decl_interface_hash: Hash,
    pub certificate_verification_claim: bool,
    pub independent_checker_claim: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FocusedReplayFailureArtifact {
    pub artifact_hash: Hash,
    pub schema: &'static str,
    pub trusted: bool,
    pub sidecar_only: bool,
    pub proof_acceptance_state: MinimalFailingArtifactProofAcceptanceState,
    pub declaration_interface: FocusedReplayDeclarationInterface,
    pub source_free_verifier_baseline: FocusedReplaySourceFreeVerifierBaseline,
    pub minimal_failing_artifact: MinimalFailingArtifact,
    pub excluded_fields: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct FocusedReplayTacticBatchFailureInput<'a> {
    pub module: &'a str,
    pub declaration: Name,
    pub state: &'a MachineProofState,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate: MachineTacticCandidate,
    pub candidate_payload_hash: Option<Hash>,
    pub deterministic_budget: TacticBudget,
    pub deterministic_budget_hash: Option<Hash>,
    pub profile_version: MachineTacticProfileVersion,
    pub required_features: &'a [MachineTacticFeature],
    pub diagnostic: &'a MachineApiCompactErrorWire,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MinimalFailingArtifactError {
    UnknownGoal { goal_id: GoalId },
    ArtifactHashMismatch { expected: Hash, actual: Hash },
    CandidatePayloadHashMismatch { expected: Hash, actual: Hash },
    DeterministicBudgetHashMismatch { expected: Hash, actual: Hash },
    DiagnosticHashMismatch { expected: Hash, actual: Hash },
    DeclarationInterfaceHashMismatch { expected: Hash, actual: Hash },
    ImportIdentityHashMismatch { expected: Hash, actual: Hash },
    CheckedCurrentDeclInterfaceHashMismatch { expected: Hash, actual: Hash },
    DiagnosticPolicyMismatch,
    StateFingerprintMismatch { expected: Hash, actual: Hash },
    GoalFingerprintMismatch { expected: Hash, actual: Hash },
    ExcludedFieldsMismatch,
    CandidateUnexpectedlySucceeded,
    DiagnosticCanonicalization,
    ProofAcceptanceStateClaim,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FailureMemoryKey {
    pub environment_hash: Hash,
    pub goal_fingerprint: Hash,
    pub candidate_shape_hash: Hash,
    pub error_kind: MachineApiErrorKind,
    pub diagnostic_hash: Hash,
}

impl FailureMemoryKey {
    pub const fn new(
        environment_hash: Hash,
        goal_fingerprint: Hash,
        candidate_shape_hash: Hash,
        error_kind: MachineApiErrorKind,
        diagnostic_hash: Hash,
    ) -> Self {
        Self {
            environment_hash,
            goal_fingerprint,
            candidate_shape_hash,
            error_kind,
            diagnostic_hash,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct FailureMemoryObservation {
    pub logical_clock: u64,
    pub wall_clock_unix_ms: Option<u64>,
}

impl FailureMemoryObservation {
    pub const fn new(logical_clock: u64) -> Self {
        Self {
            logical_clock,
            wall_clock_unix_ms: None,
        }
    }

    pub const fn with_wall_clock(logical_clock: u64, wall_clock_unix_ms: u64) -> Self {
        Self {
            logical_clock,
            wall_clock_unix_ms: Some(wall_clock_unix_ms),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FailureMemoryRepairOutcome {
    RejectedBeforeExecution,
    CandidateRejected,
    TacticFailed,
    RepairSucceeded,
}

impl FailureMemoryRepairOutcome {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RejectedBeforeExecution => "rejected_before_execution",
            Self::CandidateRejected => "candidate_rejected",
            Self::TacticFailed => "tactic_failed",
            Self::RepairSucceeded => "repair_succeeded",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum FailureMemoryBudgetClass {
    #[default]
    Unknown,
    Tiny,
    Small,
    Normal,
    Large,
    Exhausted,
}

impl FailureMemoryBudgetClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unknown => "unknown",
            Self::Tiny => "tiny",
            Self::Small => "small",
            Self::Normal => "normal",
            Self::Large => "large",
            Self::Exhausted => "exhausted",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FailureMemoryRepairAttempt {
    pub repair_operator_hash: Hash,
    pub outcome: FailureMemoryRepairOutcome,
    pub observed_at: FailureMemoryObservation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailureMemoryRecord {
    pub key: FailureMemoryKey,
    pub import_identity_hash: Hash,
    pub occurrence_count: u64,
    pub first_observation: FailureMemoryObservation,
    pub last_observation: FailureMemoryObservation,
    pub repair_attempts: Vec<FailureMemoryRepairAttempt>,
    pub successful_repair: Option<Hash>,
    pub alternative_used_in_final_proof: Option<Hash>,
    pub model_or_profile: Option<String>,
    pub budget_class: FailureMemoryBudgetClass,
}

impl FailureMemoryRecord {
    pub fn new(
        key: FailureMemoryKey,
        import_identity_hash: Hash,
        observed_at: FailureMemoryObservation,
        model_or_profile: Option<String>,
        budget_class: FailureMemoryBudgetClass,
    ) -> Self {
        Self {
            key,
            import_identity_hash,
            occurrence_count: 1,
            first_observation: observed_at,
            last_observation: observed_at,
            repair_attempts: Vec::new(),
            successful_repair: None,
            alternative_used_in_final_proof: None,
            model_or_profile,
            budget_class,
        }
    }

    pub fn with_repair_attempt(mut self, attempt: FailureMemoryRepairAttempt) -> Self {
        self.repair_attempts.push(attempt);
        self.deduplicate_repair_attempts();
        self
    }

    pub fn with_successful_repair(mut self, repair_operator_hash: Hash) -> Self {
        self.successful_repair = Some(repair_operator_hash);
        self
    }

    pub fn with_alternative_used_in_final_proof(mut self, candidate_shape_hash: Hash) -> Self {
        self.alternative_used_in_final_proof = Some(candidate_shape_hash);
        self
    }

    fn merge_from(&mut self, incoming: FailureMemoryRecord) {
        let previous_last_observation = self.last_observation;
        self.occurrence_count = self
            .occurrence_count
            .saturating_add(incoming.occurrence_count);
        self.first_observation = self.first_observation.min(incoming.first_observation);
        self.last_observation = previous_last_observation.max(incoming.last_observation);
        self.successful_repair = choose_failure_memory_field(
            self.successful_repair,
            incoming.successful_repair,
            previous_last_observation,
            incoming.last_observation,
        );
        self.alternative_used_in_final_proof = choose_failure_memory_field(
            self.alternative_used_in_final_proof,
            incoming.alternative_used_in_final_proof,
            previous_last_observation,
            incoming.last_observation,
        );
        self.model_or_profile = choose_failure_memory_field(
            self.model_or_profile.take(),
            incoming.model_or_profile,
            previous_last_observation,
            incoming.last_observation,
        );
        self.budget_class = choose_failure_memory_field(
            Some(self.budget_class),
            Some(incoming.budget_class),
            previous_last_observation,
            incoming.last_observation,
        )
        .unwrap_or(FailureMemoryBudgetClass::Unknown);
        self.repair_attempts.extend(incoming.repair_attempts);
        self.deduplicate_repair_attempts();
    }

    fn deduplicate_repair_attempts(&mut self) {
        self.repair_attempts.sort_by(|left, right| {
            left.repair_operator_hash
                .cmp(&right.repair_operator_hash)
                .then_with(|| left.outcome.cmp(&right.outcome))
                .then_with(|| left.observed_at.cmp(&right.observed_at))
        });
        let mut seen = BTreeSet::new();
        self.repair_attempts
            .retain(|attempt| seen.insert((attempt.repair_operator_hash, attempt.outcome)));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FailureMemoryLookupContext {
    pub environment_hash: Hash,
    pub import_identity_hash: Hash,
    pub goal_fingerprint: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FailureMemoryStaleReason {
    EnvironmentHash,
    ImportIdentity,
    GoalFingerprint,
}

impl FailureMemoryStaleReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EnvironmentHash => "environment_hash",
            Self::ImportIdentity => "import_identity",
            Self::GoalFingerprint => "goal_fingerprint",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailureMemoryStaleSuggestion {
    pub key: FailureMemoryKey,
    pub reasons: Vec<FailureMemoryStaleReason>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FailureMemorySuppressionPolicy {
    pub suppress_exact_repeated_failures: bool,
}

impl Default for FailureMemorySuppressionPolicy {
    fn default() -> Self {
        Self {
            suppress_exact_repeated_failures: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FailureMemorySuppressionDecision {
    Allow,
    AllowWithStaleSuggestions {
        stale: Vec<FailureMemoryStaleSuggestion>,
    },
    SuppressExactRepeatedFailure {
        key: FailureMemoryKey,
        occurrence_count: u64,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FailureMemoryMergeReport {
    pub inserted: usize,
    pub merged: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailureMemoryHardNegative {
    pub key: FailureMemoryKey,
    pub occurrence_count: u64,
    pub repair_operator_hashes: Vec<Hash>,
    pub successful_repair: Option<Hash>,
    pub alternative_used_in_final_proof: Option<Hash>,
    pub model_or_profile: Option<String>,
    pub budget_class: FailureMemoryBudgetClass,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FailureMemoryStore {
    records: BTreeMap<FailureMemoryKey, FailureMemoryRecord>,
}

impl FailureMemoryStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    pub fn record(&self, key: &FailureMemoryKey) -> Option<&FailureMemoryRecord> {
        self.records.get(key)
    }

    pub fn records(&self) -> impl ExactSizeIterator<Item = &FailureMemoryRecord> {
        self.records.values()
    }

    pub fn observe(&mut self, record: FailureMemoryRecord) -> FailureMemoryMergeReport {
        let key = record.key.clone();
        match self.records.get_mut(&key) {
            Some(existing) => {
                existing.merge_from(record);
                FailureMemoryMergeReport {
                    inserted: 0,
                    merged: 1,
                }
            }
            None => {
                self.records.insert(key, record);
                FailureMemoryMergeReport {
                    inserted: 1,
                    merged: 0,
                }
            }
        }
    }

    pub fn merge(&mut self, other: &Self) -> FailureMemoryMergeReport {
        let mut report = FailureMemoryMergeReport::default();
        for record in other.records.values().cloned() {
            let step = self.observe(record);
            report.inserted += step.inserted;
            report.merged += step.merged;
        }
        report
    }

    pub fn suppression_decision(
        &self,
        key: &FailureMemoryKey,
        context: &FailureMemoryLookupContext,
        policy: FailureMemorySuppressionPolicy,
    ) -> FailureMemorySuppressionDecision {
        if policy.suppress_exact_repeated_failures {
            if let Some(record) = self.records.get(key) {
                if failure_memory_stale_reasons(record, context).is_empty() {
                    return FailureMemorySuppressionDecision::SuppressExactRepeatedFailure {
                        key: key.clone(),
                        occurrence_count: record.occurrence_count,
                    };
                }
            }
        }

        let stale = self.stale_suggestions(context);
        if stale.is_empty() {
            FailureMemorySuppressionDecision::Allow
        } else {
            FailureMemorySuppressionDecision::AllowWithStaleSuggestions { stale }
        }
    }

    pub fn stale_suggestions(
        &self,
        context: &FailureMemoryLookupContext,
    ) -> Vec<FailureMemoryStaleSuggestion> {
        self.records
            .values()
            .filter_map(|record| {
                let reasons = failure_memory_stale_reasons(record, context);
                (!reasons.is_empty()).then(|| FailureMemoryStaleSuggestion {
                    key: record.key.clone(),
                    reasons,
                })
            })
            .collect()
    }

    pub fn hard_negatives(&self, min_occurrence_count: u64) -> Vec<FailureMemoryHardNegative> {
        self.records
            .values()
            .filter(|record| record.occurrence_count >= min_occurrence_count)
            .map(|record| FailureMemoryHardNegative {
                key: record.key.clone(),
                occurrence_count: record.occurrence_count,
                repair_operator_hashes: record
                    .repair_attempts
                    .iter()
                    .map(|attempt| attempt.repair_operator_hash)
                    .collect(),
                successful_repair: record.successful_repair,
                alternative_used_in_final_proof: record.alternative_used_in_final_proof,
                model_or_profile: record.model_or_profile.clone(),
                budget_class: record.budget_class,
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HardNegativeKind {
    ExactRepeatedFailure,
    StaleMemorySuggestion,
    InvalidRepairProposal,
    NoProgressRepairLoop,
}

impl HardNegativeKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExactRepeatedFailure => "exact_repeated_failure",
            Self::StaleMemorySuggestion => "stale_memory_suggestion",
            Self::InvalidRepairProposal => "invalid_repair_proposal",
            Self::NoProgressRepairLoop => "no_progress_repair_loop",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HardNegativeRecord {
    pub kind: HardNegativeKind,
    pub key: Option<FailureMemoryKey>,
    pub artifact_hash: Option<Hash>,
    pub candidate_shape_hash: Option<Hash>,
    pub diagnostic_hash: Option<Hash>,
    pub error_kind: Option<MachineApiErrorKind>,
    pub repair_operator_hash: Option<Hash>,
    pub repair_chain_termination: Option<RepairChainTerminationReason>,
    pub reasons: Vec<String>,
    pub occurrence_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HardNegativeExport {
    pub export_hash: Hash,
    pub records: Vec<HardNegativeRecord>,
}

pub struct HardNegativeExportInput<'a> {
    pub failure_memory: &'a FailureMemoryStore,
    pub lookup_context: Option<&'a FailureMemoryLookupContext>,
    pub artifacts: &'a [MinimalFailingArtifact],
    pub invalid_repair_proposals: &'a [RepairGeneratedProposal],
    pub repair_chains: &'a [RepairChainReport],
    pub min_occurrence_count: u64,
}

pub fn failure_memory_candidate_shape_hash(candidate: &MachineTacticCandidate) -> Hash {
    let payload_hash = crate::ai_search::ai_search_candidate_payload_hash(candidate);
    failure_memory_hash_with_domain(FAILURE_MEMORY_CANDIDATE_SHAPE_HASH_DOMAIN, &payload_hash)
}

pub fn failure_memory_key_from_projection(
    environment_hash: Hash,
    goal_fingerprint: Hash,
    candidate_shape_hash: Hash,
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<FailureMemoryKey, MachineApiDiagnosticCanonicalizationError> {
    Ok(FailureMemoryKey::new(
        environment_hash,
        goal_fingerprint,
        candidate_shape_hash,
        diagnostic.kind,
        diagnostic.diagnostic_hash()?,
    ))
}

pub fn failure_memory_key_canonical_bytes(key: &FailureMemoryKey) -> Vec<u8> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, FAILURE_MEMORY_SCHEMA);
    out.extend_from_slice(&key.environment_hash);
    out.extend_from_slice(&key.goal_fingerprint);
    out.extend_from_slice(&key.candidate_shape_hash);
    repair_encode_string(&mut out, key.error_kind.as_str());
    out.extend_from_slice(&key.diagnostic_hash);
    out
}

pub fn failure_memory_key_hash(key: &FailureMemoryKey) -> Hash {
    failure_memory_hash_with_domain(
        FAILURE_MEMORY_KEY_HASH_DOMAIN,
        &failure_memory_key_canonical_bytes(key),
    )
}

pub fn minimal_failing_artifact_diagnostic_from_projection(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<MinimalFailingArtifactDiagnostic, MinimalFailingArtifactError> {
    Ok(MinimalFailingArtifactDiagnostic {
        kind: diagnostic.kind,
        phase: diagnostic.phase,
        retryable: diagnostic.retryable,
        goal_id: diagnostic.goal_id,
        tactic_kind: diagnostic.tactic_kind,
        primary_name: diagnostic.primary_name.clone(),
        primary_axiom_ref: diagnostic.primary_axiom_ref.clone(),
        expected_hash: diagnostic.expected_hash,
        actual_hash: diagnostic.actual_hash,
        diagnostic_hash: diagnostic
            .diagnostic_hash()
            .map_err(|_| MinimalFailingArtifactError::DiagnosticCanonicalization)?,
    })
}

pub fn minimal_failing_artifact_diagnostic_from_compact(
    diagnostic: &MachineApiCompactErrorWire,
) -> MinimalFailingArtifactDiagnostic {
    MinimalFailingArtifactDiagnostic {
        kind: diagnostic.error_kind,
        phase: diagnostic.phase,
        retryable: diagnostic.retryable,
        goal_id: diagnostic.goal_id,
        tactic_kind: diagnostic.tactic_kind,
        primary_name: diagnostic.primary_name.clone(),
        primary_axiom_ref: diagnostic.primary_axiom_ref.clone(),
        expected_hash: diagnostic.expected_hash,
        actual_hash: diagnostic.actual_hash,
        diagnostic_hash: diagnostic.diagnostic_hash,
    }
}

pub fn build_minimal_failing_artifact(
    state: &MachineProofState,
    goal_id: GoalId,
    candidate: MachineTacticCandidate,
    deterministic_budget: TacticBudget,
    profile_version: MachineTacticProfileVersion,
    required_features: &[MachineTacticFeature],
) -> Result<MinimalFailingArtifact, MinimalFailingArtifactError> {
    let goal = state
        .goal(goal_id)
        .map_err(|_| MinimalFailingArtifactError::UnknownGoal { goal_id })?;
    let diagnostic = match machine_tactic_validate_machine_tactic_candidate_for_state(
        state,
        goal_id,
        candidate.clone(),
        deterministic_budget,
        profile_version,
        required_features,
    ) {
        Err(error) => error.diagnostic,
        Ok(validated) => match machine_tactic_run_machine_tactic_with_budget(
            state,
            validated.tactic,
            deterministic_budget,
        ) {
            Err(error) => error.diagnostic,
            Ok(_) => return Err(MinimalFailingArtifactError::CandidateUnexpectedlySucceeded),
        },
    };
    let structured_diagnostic = minimal_failing_artifact_diagnostic_from_projection(&diagnostic)?;
    let candidate_payload_hash = crate::ai_search::ai_search_candidate_payload_hash(&candidate);
    let deterministic_budget_hash = tactic_budget_hash(deterministic_budget);
    let mut artifact = MinimalFailingArtifact {
        artifact_hash: [0; 32],
        sidecar_only: true,
        proof_acceptance_state: MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly,
        state_fingerprint: state.fingerprint,
        goal_id,
        goal_fingerprint: proof_candidate_goal_fingerprint(state.fingerprint, goal_id),
        imports: minimal_failing_artifact_imports(state),
        checked_current_decls: minimal_failing_artifact_checked_current_decls(state),
        local_context: minimal_failing_artifact_local_context(&goal),
        context_hash: goal.context_hash,
        target_hash: goal.target_hash,
        candidate,
        candidate_payload_hash,
        deterministic_budget,
        deterministic_budget_hash,
        expected_policy: MinimalFailingArtifactExpectedPolicy {
            profile_version,
            required_features: required_features.to_vec(),
            expected_error_kind: structured_diagnostic.kind,
            expected_phase: structured_diagnostic.phase,
            expected_retryable: structured_diagnostic.retryable,
        },
        structured_diagnostic,
    };
    artifact.artifact_hash = minimal_failing_artifact_hash(&artifact)?;
    validate_minimal_failing_artifact_identity(&artifact)?;
    Ok(artifact)
}

pub fn build_focused_replay_failure_artifact_from_tactic_batch(
    input: FocusedReplayTacticBatchFailureInput<'_>,
) -> Result<FocusedReplayFailureArtifact, MinimalFailingArtifactError> {
    if input.state.fingerprint != input.state_fingerprint {
        return Err(MinimalFailingArtifactError::StateFingerprintMismatch {
            expected: input.state_fingerprint,
            actual: input.state.fingerprint,
        });
    }
    let goal =
        input
            .state
            .goal(input.goal_id)
            .map_err(|_| MinimalFailingArtifactError::UnknownGoal {
                goal_id: input.goal_id,
            })?;

    let actual_candidate_payload_hash =
        crate::ai_search::ai_search_candidate_payload_hash(&input.candidate);
    if let Some(expected) = input.candidate_payload_hash {
        if expected != actual_candidate_payload_hash {
            return Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch {
                expected,
                actual: actual_candidate_payload_hash,
            });
        }
    }
    let actual_budget_hash = tactic_budget_hash(input.deterministic_budget);
    if let Some(expected) = input.deterministic_budget_hash {
        if expected != actual_budget_hash {
            return Err(
                MinimalFailingArtifactError::DeterministicBudgetHashMismatch {
                    expected,
                    actual: actual_budget_hash,
                },
            );
        }
    }

    let candidate_tactic_kind = MachineApiTacticKind::from_candidate(&input.candidate);
    if input.diagnostic.goal_id != Some(input.goal_id)
        || input.diagnostic.tactic_kind != Some(candidate_tactic_kind)
    {
        return Err(MinimalFailingArtifactError::DiagnosticPolicyMismatch);
    }

    let structured_diagnostic = minimal_failing_artifact_diagnostic_from_compact(input.diagnostic);
    let mut minimal = MinimalFailingArtifact {
        artifact_hash: [0; 32],
        sidecar_only: true,
        proof_acceptance_state: MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly,
        state_fingerprint: input.state.fingerprint,
        goal_id: input.goal_id,
        goal_fingerprint: proof_candidate_goal_fingerprint(input.state.fingerprint, input.goal_id),
        imports: minimal_failing_artifact_imports(input.state),
        checked_current_decls: minimal_failing_artifact_checked_current_decls(input.state),
        local_context: minimal_failing_artifact_local_context(&goal),
        context_hash: goal.context_hash,
        target_hash: goal.target_hash,
        candidate: input.candidate,
        candidate_payload_hash: actual_candidate_payload_hash,
        deterministic_budget: input.deterministic_budget,
        deterministic_budget_hash: actual_budget_hash,
        expected_policy: MinimalFailingArtifactExpectedPolicy {
            profile_version: input.profile_version,
            required_features: input.required_features.to_vec(),
            expected_error_kind: structured_diagnostic.kind,
            expected_phase: structured_diagnostic.phase,
            expected_retryable: structured_diagnostic.retryable,
        },
        structured_diagnostic,
    };
    minimal.artifact_hash = minimal_failing_artifact_hash(&minimal)?;
    validate_minimal_failing_artifact_identity(&minimal)?;
    build_focused_replay_failure_artifact(input.module, input.declaration, minimal)
}

pub fn validate_minimal_failing_artifact_identity(
    artifact: &MinimalFailingArtifact,
) -> Result<(), MinimalFailingArtifactError> {
    if !artifact.sidecar_only
        || artifact.proof_acceptance_state
            != MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly
    {
        return Err(MinimalFailingArtifactError::ProofAcceptanceStateClaim);
    }
    let actual_candidate_payload_hash =
        crate::ai_search::ai_search_candidate_payload_hash(&artifact.candidate);
    if actual_candidate_payload_hash != artifact.candidate_payload_hash {
        return Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch {
            expected: artifact.candidate_payload_hash,
            actual: actual_candidate_payload_hash,
        });
    }
    let actual_budget_hash = tactic_budget_hash(artifact.deterministic_budget);
    if actual_budget_hash != artifact.deterministic_budget_hash {
        return Err(
            MinimalFailingArtifactError::DeterministicBudgetHashMismatch {
                expected: artifact.deterministic_budget_hash,
                actual: actual_budget_hash,
            },
        );
    }
    if artifact.expected_policy.expected_error_kind != artifact.structured_diagnostic.kind
        || artifact.expected_policy.expected_phase != artifact.structured_diagnostic.phase
        || artifact.expected_policy.expected_retryable != artifact.structured_diagnostic.retryable
    {
        return Err(MinimalFailingArtifactError::DiagnosticPolicyMismatch);
    }
    let actual_diagnostic_hash =
        minimal_failing_artifact_structured_diagnostic_hash(&artifact.structured_diagnostic)?;
    if actual_diagnostic_hash != artifact.structured_diagnostic.diagnostic_hash {
        return Err(MinimalFailingArtifactError::DiagnosticHashMismatch {
            expected: artifact.structured_diagnostic.diagnostic_hash,
            actual: actual_diagnostic_hash,
        });
    }
    let actual_artifact_hash = minimal_failing_artifact_hash(artifact)?;
    if actual_artifact_hash != artifact.artifact_hash {
        return Err(MinimalFailingArtifactError::ArtifactHashMismatch {
            expected: artifact.artifact_hash,
            actual: actual_artifact_hash,
        });
    }
    Ok(())
}

pub fn build_focused_replay_failure_artifact(
    module: impl Into<String>,
    declaration: Name,
    minimal_failing_artifact: MinimalFailingArtifact,
) -> Result<FocusedReplayFailureArtifact, MinimalFailingArtifactError> {
    validate_minimal_failing_artifact_identity(&minimal_failing_artifact)?;
    let module = module.into();
    let universe_params = focused_replay_declaration_universe_params(
        &declaration,
        &minimal_failing_artifact.checked_current_decls,
    );
    let declaration_interface_hash = focused_replay_declaration_interface_hash(
        &module,
        &declaration,
        &universe_params,
        minimal_failing_artifact.context_hash,
        minimal_failing_artifact.target_hash,
    );
    let import_identity_hash =
        focused_replay_import_identity_hash(&minimal_failing_artifact.imports);
    let checked_current_decl_interface_hash = focused_replay_checked_current_decl_interface_hash(
        &minimal_failing_artifact.checked_current_decls,
    );

    let mut artifact = FocusedReplayFailureArtifact {
        artifact_hash: [0; 32],
        schema: FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA,
        trusted: false,
        sidecar_only: true,
        proof_acceptance_state: MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly,
        declaration_interface: FocusedReplayDeclarationInterface {
            module,
            declaration,
            universe_params,
            declaration_interface_hash,
            local_context_hash: minimal_failing_artifact.context_hash,
            target_hash: minimal_failing_artifact.target_hash,
        },
        source_free_verifier_baseline: FocusedReplaySourceFreeVerifierBaseline {
            verifier_profile: "source_free_verify_module_cert.v0.1".to_owned(),
            baseline_reference: "canonical_certificate_and_import_hashes".to_owned(),
            state_fingerprint: minimal_failing_artifact.state_fingerprint,
            goal_fingerprint: minimal_failing_artifact.goal_fingerprint,
            import_identity_hash,
            checked_current_decl_interface_hash,
            certificate_verification_claim: false,
            independent_checker_claim: false,
        },
        minimal_failing_artifact,
        excluded_fields: FOCUSED_REPLAY_FAILURE_EXCLUDED_FIELDS
            .iter()
            .map(|field| (*field).to_owned())
            .collect(),
    };
    artifact.artifact_hash = focused_replay_failure_artifact_hash(&artifact)?;
    validate_focused_replay_failure_artifact_identity(&artifact)?;
    Ok(artifact)
}

pub fn validate_focused_replay_failure_artifact_identity(
    artifact: &FocusedReplayFailureArtifact,
) -> Result<(), MinimalFailingArtifactError> {
    if artifact.schema != FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA
        || artifact.trusted
        || !artifact.sidecar_only
        || artifact.proof_acceptance_state
            != MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly
        || artifact
            .source_free_verifier_baseline
            .certificate_verification_claim
        || artifact
            .source_free_verifier_baseline
            .independent_checker_claim
    {
        return Err(MinimalFailingArtifactError::ProofAcceptanceStateClaim);
    }
    validate_minimal_failing_artifact_identity(&artifact.minimal_failing_artifact)?;

    let actual_declaration_interface_hash = focused_replay_declaration_interface_hash(
        &artifact.declaration_interface.module,
        &artifact.declaration_interface.declaration,
        &artifact.declaration_interface.universe_params,
        artifact.declaration_interface.local_context_hash,
        artifact.declaration_interface.target_hash,
    );
    if actual_declaration_interface_hash
        != artifact.declaration_interface.declaration_interface_hash
    {
        return Err(
            MinimalFailingArtifactError::DeclarationInterfaceHashMismatch {
                expected: artifact.declaration_interface.declaration_interface_hash,
                actual: actual_declaration_interface_hash,
            },
        );
    }
    if artifact.declaration_interface.local_context_hash
        != artifact.minimal_failing_artifact.context_hash
        || artifact.declaration_interface.target_hash
            != artifact.minimal_failing_artifact.target_hash
    {
        return Err(MinimalFailingArtifactError::ArtifactHashMismatch {
            expected: artifact.artifact_hash,
            actual: focused_replay_failure_artifact_hash(artifact)?,
        });
    }
    if artifact.source_free_verifier_baseline.state_fingerprint
        != artifact.minimal_failing_artifact.state_fingerprint
    {
        return Err(MinimalFailingArtifactError::StateFingerprintMismatch {
            expected: artifact.source_free_verifier_baseline.state_fingerprint,
            actual: artifact.minimal_failing_artifact.state_fingerprint,
        });
    }
    if artifact.source_free_verifier_baseline.goal_fingerprint
        != artifact.minimal_failing_artifact.goal_fingerprint
    {
        return Err(MinimalFailingArtifactError::GoalFingerprintMismatch {
            expected: artifact.source_free_verifier_baseline.goal_fingerprint,
            actual: artifact.minimal_failing_artifact.goal_fingerprint,
        });
    }
    if artifact.source_free_verifier_baseline.import_identity_hash
        != focused_replay_import_identity_hash(&artifact.minimal_failing_artifact.imports)
    {
        return Err(MinimalFailingArtifactError::ImportIdentityHashMismatch {
            expected: artifact.source_free_verifier_baseline.import_identity_hash,
            actual: focused_replay_import_identity_hash(&artifact.minimal_failing_artifact.imports),
        });
    }
    let actual_checked_current_decl_interface_hash =
        focused_replay_checked_current_decl_interface_hash(
            &artifact.minimal_failing_artifact.checked_current_decls,
        );
    if artifact
        .source_free_verifier_baseline
        .checked_current_decl_interface_hash
        != actual_checked_current_decl_interface_hash
    {
        return Err(
            MinimalFailingArtifactError::CheckedCurrentDeclInterfaceHashMismatch {
                expected: artifact
                    .source_free_verifier_baseline
                    .checked_current_decl_interface_hash,
                actual: actual_checked_current_decl_interface_hash,
            },
        );
    }
    if artifact.excluded_fields
        != FOCUSED_REPLAY_FAILURE_EXCLUDED_FIELDS
            .iter()
            .map(|field| (*field).to_owned())
            .collect::<Vec<_>>()
    {
        return Err(MinimalFailingArtifactError::ExcludedFieldsMismatch);
    }
    let actual = focused_replay_failure_artifact_hash(artifact)?;
    if actual != artifact.artifact_hash {
        return Err(MinimalFailingArtifactError::ArtifactHashMismatch {
            expected: artifact.artifact_hash,
            actual,
        });
    }
    Ok(())
}

pub fn focused_replay_failure_artifact_hash(
    artifact: &FocusedReplayFailureArtifact,
) -> Result<Hash, MinimalFailingArtifactError> {
    Ok(minimal_failing_hash_with_domain(
        FOCUSED_REPLAY_FAILURE_ARTIFACT_HASH_DOMAIN,
        &focused_replay_failure_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn focused_replay_failure_artifact_canonical_bytes(
    artifact: &FocusedReplayFailureArtifact,
) -> Result<Vec<u8>, MinimalFailingArtifactError> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA);
    repair_encode_string(&mut out, artifact.schema);
    minimal_failing_encode_bool(&mut out, artifact.trusted);
    minimal_failing_encode_bool(&mut out, artifact.sidecar_only);
    repair_encode_string(&mut out, artifact.proof_acceptance_state.as_str());

    repair_encode_string(&mut out, &artifact.declaration_interface.module);
    repair_encode_string(
        &mut out,
        &artifact.declaration_interface.declaration.as_dotted(),
    );
    repair_encode_len(
        &mut out,
        artifact.declaration_interface.universe_params.len(),
    );
    for param in &artifact.declaration_interface.universe_params {
        repair_encode_string(&mut out, param);
    }
    out.extend_from_slice(&artifact.declaration_interface.declaration_interface_hash);
    out.extend_from_slice(&artifact.declaration_interface.local_context_hash);
    out.extend_from_slice(&artifact.declaration_interface.target_hash);

    repair_encode_string(
        &mut out,
        &artifact.source_free_verifier_baseline.verifier_profile,
    );
    repair_encode_string(
        &mut out,
        &artifact.source_free_verifier_baseline.baseline_reference,
    );
    out.extend_from_slice(&artifact.source_free_verifier_baseline.state_fingerprint);
    out.extend_from_slice(&artifact.source_free_verifier_baseline.goal_fingerprint);
    out.extend_from_slice(&artifact.source_free_verifier_baseline.import_identity_hash);
    out.extend_from_slice(
        &artifact
            .source_free_verifier_baseline
            .checked_current_decl_interface_hash,
    );
    minimal_failing_encode_bool(
        &mut out,
        artifact
            .source_free_verifier_baseline
            .certificate_verification_claim,
    );
    minimal_failing_encode_bool(
        &mut out,
        artifact
            .source_free_verifier_baseline
            .independent_checker_claim,
    );

    repair_encode_len(&mut out, artifact.excluded_fields.len());
    for field in &artifact.excluded_fields {
        repair_encode_string(&mut out, field);
    }
    out.extend_from_slice(&minimal_failing_artifact_canonical_bytes(
        &artifact.minimal_failing_artifact,
    )?);
    Ok(out)
}

pub fn minimal_failing_artifact_hash(
    artifact: &MinimalFailingArtifact,
) -> Result<Hash, MinimalFailingArtifactError> {
    Ok(minimal_failing_hash_with_domain(
        MINIMAL_FAILING_ARTIFACT_HASH_DOMAIN,
        &minimal_failing_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn minimal_failing_artifact_canonical_bytes(
    artifact: &MinimalFailingArtifact,
) -> Result<Vec<u8>, MinimalFailingArtifactError> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, MINIMAL_FAILING_ARTIFACT_SCHEMA);
    minimal_failing_encode_bool(&mut out, artifact.sidecar_only);
    repair_encode_string(&mut out, artifact.proof_acceptance_state.as_str());
    out.extend_from_slice(&artifact.state_fingerprint);
    repair_encode_u64(&mut out, artifact.goal_id.0);
    out.extend_from_slice(&artifact.goal_fingerprint);

    repair_encode_len(&mut out, artifact.imports.len());
    for import in &artifact.imports {
        repair_encode_string(&mut out, &import.module);
        out.extend_from_slice(&import.export_hash);
        out.extend_from_slice(&import.certificate_hash);
        minimal_failing_encode_bool(&mut out, import.visible);
        repair_encode_len(&mut out, import.exports.len());
        for export in &import.exports {
            repair_encode_string(&mut out, &export.name.as_dotted());
            repair_encode_string(&mut out, &export.kind);
            out.extend_from_slice(&export.decl_interface_hash);
            out.extend_from_slice(&export.type_hash);
            minimal_failing_encode_optional_hash(&mut out, export.body_hash);
        }
        repair_encode_len(&mut out, import.certified_env_decl_hashes.len());
        for hash in &import.certified_env_decl_hashes {
            out.extend_from_slice(hash);
        }
    }

    repair_encode_len(&mut out, artifact.checked_current_decls.len());
    for decl in &artifact.checked_current_decls {
        repair_encode_u64(&mut out, decl.source_index);
        repair_encode_string(&mut out, &decl.name.as_dotted());
        repair_encode_len(&mut out, decl.universe_params.len());
        for param in &decl.universe_params {
            repair_encode_string(&mut out, param);
        }
        out.extend_from_slice(&decl.type_hash);
        out.extend_from_slice(&decl.decl_interface_hash);
        out.extend_from_slice(&decl.core_decl_hash);
        out.extend_from_slice(&decl.prior_chain_fingerprint);
        out.extend_from_slice(&decl.checked_env_fingerprint);
    }

    repair_encode_len(&mut out, artifact.local_context.len());
    for local in &artifact.local_context {
        repair_encode_string(&mut out, &local.name);
        out.extend_from_slice(&local.type_hash);
        minimal_failing_encode_optional_hash(&mut out, local.value_hash);
    }
    out.extend_from_slice(&artifact.context_hash);
    out.extend_from_slice(&artifact.target_hash);
    repair_encode_string(
        &mut out,
        &crate::ai_search::ai_search_candidate_payload_json(&artifact.candidate),
    );
    out.extend_from_slice(&artifact.candidate_payload_hash);
    out.extend_from_slice(&tactic_budget_canonical_bytes(
        artifact.deterministic_budget,
    ));
    out.extend_from_slice(&artifact.deterministic_budget_hash);
    repair_encode_string(&mut out, artifact.expected_policy.profile_version.as_str());
    repair_encode_len(&mut out, artifact.expected_policy.required_features.len());
    for feature in &artifact.expected_policy.required_features {
        repair_encode_string(&mut out, feature.as_str());
    }
    repair_encode_string(
        &mut out,
        artifact.expected_policy.expected_error_kind.as_str(),
    );
    repair_encode_string(&mut out, artifact.expected_policy.expected_phase.as_str());
    minimal_failing_encode_bool(&mut out, artifact.expected_policy.expected_retryable);
    minimal_failing_artifact_diagnostic_canonical_bytes(&artifact.structured_diagnostic, &mut out)?;
    Ok(out)
}

fn focused_replay_declaration_universe_params(
    declaration: &Name,
    checked_current_decls: &[MinimalFailingArtifactCheckedCurrentDecl],
) -> Vec<String> {
    checked_current_decls
        .iter()
        .find(|decl| &decl.name == declaration)
        .map(|decl| decl.universe_params.clone())
        .unwrap_or_default()
}

fn focused_replay_declaration_interface_hash(
    module: &str,
    declaration: &Name,
    universe_params: &[String],
    local_context_hash: Hash,
    target_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    repair_encode_string(&mut out, "focused_replay.declaration_interface.v1");
    repair_encode_string(&mut out, module);
    repair_encode_string(&mut out, &declaration.as_dotted());
    repair_encode_len(&mut out, universe_params.len());
    for param in universe_params {
        repair_encode_string(&mut out, param);
    }
    out.extend_from_slice(&local_context_hash);
    out.extend_from_slice(&target_hash);
    minimal_failing_hash_with_domain(
        "npa.machine-api.focused-replay.declaration-interface.hash.v1",
        &out,
    )
}

fn focused_replay_import_identity_hash(imports: &[MinimalFailingArtifactImport]) -> Hash {
    let mut out = Vec::new();
    repair_encode_string(&mut out, "focused_replay.import_identity.v1");
    repair_encode_len(&mut out, imports.len());
    for import in imports {
        repair_encode_string(&mut out, &import.module);
        out.extend_from_slice(&import.export_hash);
        out.extend_from_slice(&import.certificate_hash);
        minimal_failing_encode_bool(&mut out, import.visible);
        repair_encode_len(&mut out, import.exports.len());
        for export in &import.exports {
            repair_encode_string(&mut out, &export.name.as_dotted());
            repair_encode_string(&mut out, &export.kind);
            out.extend_from_slice(&export.decl_interface_hash);
            out.extend_from_slice(&export.type_hash);
            minimal_failing_encode_optional_hash(&mut out, export.body_hash);
        }
        repair_encode_len(&mut out, import.certified_env_decl_hashes.len());
        for hash in &import.certified_env_decl_hashes {
            out.extend_from_slice(hash);
        }
    }
    minimal_failing_hash_with_domain(
        "npa.machine-api.focused-replay.import-identity.hash.v1",
        &out,
    )
}

fn focused_replay_checked_current_decl_interface_hash(
    decls: &[MinimalFailingArtifactCheckedCurrentDecl],
) -> Hash {
    let mut out = Vec::new();
    repair_encode_string(&mut out, "focused_replay.checked_current_decls.v1");
    repair_encode_len(&mut out, decls.len());
    for decl in decls {
        repair_encode_u64(&mut out, decl.source_index);
        repair_encode_string(&mut out, &decl.name.as_dotted());
        repair_encode_len(&mut out, decl.universe_params.len());
        for param in &decl.universe_params {
            repair_encode_string(&mut out, param);
        }
        out.extend_from_slice(&decl.type_hash);
        out.extend_from_slice(&decl.decl_interface_hash);
        out.extend_from_slice(&decl.core_decl_hash);
        out.extend_from_slice(&decl.prior_chain_fingerprint);
        out.extend_from_slice(&decl.checked_env_fingerprint);
    }
    minimal_failing_hash_with_domain(
        "npa.machine-api.focused-replay.checked-current-decls.hash.v1",
        &out,
    )
}

pub fn build_hard_negative_export(
    input: HardNegativeExportInput<'_>,
) -> Result<HardNegativeExport, MinimalFailingArtifactError> {
    for artifact in input.artifacts {
        validate_minimal_failing_artifact_identity(artifact)?;
    }

    let mut records = Vec::new();
    for negative in input
        .failure_memory
        .hard_negatives(input.min_occurrence_count)
    {
        records.push(HardNegativeRecord {
            kind: HardNegativeKind::ExactRepeatedFailure,
            artifact_hash: artifact_hash_for_failure_key(&negative.key, input.artifacts),
            candidate_shape_hash: Some(negative.key.candidate_shape_hash),
            diagnostic_hash: Some(negative.key.diagnostic_hash),
            error_kind: Some(negative.key.error_kind),
            repair_operator_hash: None,
            repair_chain_termination: None,
            reasons: vec!["failure_memory_exact_repeat".to_owned()],
            occurrence_count: negative.occurrence_count,
            key: Some(negative.key),
        });
    }

    if let Some(context) = input.lookup_context {
        for stale in input.failure_memory.stale_suggestions(context) {
            records.push(HardNegativeRecord {
                kind: HardNegativeKind::StaleMemorySuggestion,
                artifact_hash: artifact_hash_for_failure_key(&stale.key, input.artifacts),
                candidate_shape_hash: Some(stale.key.candidate_shape_hash),
                diagnostic_hash: Some(stale.key.diagnostic_hash),
                error_kind: Some(stale.key.error_kind),
                repair_operator_hash: None,
                repair_chain_termination: None,
                reasons: stale
                    .reasons
                    .into_iter()
                    .map(|reason| reason.as_str().to_owned())
                    .collect(),
                occurrence_count: 1,
                key: Some(stale.key),
            });
        }
    }

    for proposal in input.invalid_repair_proposals {
        let RepairProposalValidation::Rejected { error } = &proposal.validation else {
            continue;
        };
        let (error_kind, extra_reason) = repair_proposal_validation_error_summary(error);
        let mut reasons = vec![
            "invalid_repair_proposal".to_owned(),
            format!("source={}", proposal.provenance.source.as_str()),
            format!("category={}", proposal.provenance.category.as_str()),
            extra_reason,
        ];
        if let Some(operator) = proposal.operator.as_ref() {
            reasons.push(format!("operator={}", operator.kind().as_str()));
        }
        records.push(HardNegativeRecord {
            kind: HardNegativeKind::InvalidRepairProposal,
            key: None,
            artifact_hash: None,
            candidate_shape_hash: None,
            diagnostic_hash: None,
            error_kind,
            repair_operator_hash: proposal.operator_hash,
            repair_chain_termination: None,
            reasons,
            occurrence_count: 1,
        });
    }

    for report in input.repair_chains {
        let Some(reason) = hard_negative_no_progress_reason(&report.termination_reason) else {
            continue;
        };
        let (candidate_shape_hash, diagnostic_hash, occurrence_count) =
            hard_negative_repair_chain_identity(report);
        records.push(HardNegativeRecord {
            kind: HardNegativeKind::NoProgressRepairLoop,
            key: None,
            artifact_hash: None,
            candidate_shape_hash,
            diagnostic_hash,
            error_kind: None,
            repair_operator_hash: None,
            repair_chain_termination: Some(report.termination_reason.clone()),
            reasons: vec![reason],
            occurrence_count,
        });
    }

    records.sort_by(|left, right| {
        hard_negative_record_canonical_bytes(left).cmp(&hard_negative_record_canonical_bytes(right))
    });
    records.dedup_by(|left, right| {
        hard_negative_record_canonical_bytes(left) == hard_negative_record_canonical_bytes(right)
    });

    let mut export = HardNegativeExport {
        export_hash: [0; 32],
        records,
    };
    export.export_hash = hard_negative_export_hash(&export);
    Ok(export)
}

pub fn hard_negative_export_hash(export: &HardNegativeExport) -> Hash {
    minimal_failing_hash_with_domain(
        HARD_NEGATIVE_EXPORT_HASH_DOMAIN,
        &hard_negative_export_canonical_bytes(export),
    )
}

pub fn hard_negative_export_canonical_bytes(export: &HardNegativeExport) -> Vec<u8> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, HARD_NEGATIVE_EXPORT_SCHEMA);
    repair_encode_len(&mut out, export.records.len());
    for record in &export.records {
        out.extend_from_slice(&hard_negative_record_canonical_bytes(record));
    }
    out
}

fn minimal_failing_artifact_imports(
    state: &MachineProofState,
) -> Vec<MinimalFailingArtifactImport> {
    state
        .env
        .imports
        .iter()
        .map(|import| MinimalFailingArtifactImport {
            module: import.module().as_dotted(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
            visible: import.is_visible(),
            exports: import
                .exports()
                .iter()
                .map(|export| MinimalFailingArtifactImportExport {
                    name: export.name.clone(),
                    kind: minimal_failing_artifact_export_kind(&export.kind).to_owned(),
                    decl_interface_hash: export.decl_interface_hash,
                    type_hash: export.type_hash,
                    body_hash: export.body_hash,
                })
                .collect(),
            certified_env_decl_hashes: import.certified_env_decl_hashes().to_vec(),
        })
        .collect()
}

fn minimal_failing_artifact_checked_current_decls(
    state: &MachineProofState,
) -> Vec<MinimalFailingArtifactCheckedCurrentDecl> {
    state
        .env
        .checked_current_decls
        .iter()
        .map(|decl| {
            let signature = decl.signature();
            MinimalFailingArtifactCheckedCurrentDecl {
                source_index: decl.source_index(),
                name: signature.name().clone(),
                universe_params: signature.universe_params().to_vec(),
                type_hash: core_expr_hash(signature.ty()),
                decl_interface_hash: signature.decl_interface_hash(),
                core_decl_hash: decl.core_decl_hash(),
                prior_chain_fingerprint: decl.prior_chain_fingerprint(),
                checked_env_fingerprint: decl.checked_env_fingerprint(),
            }
        })
        .collect()
}

fn minimal_failing_artifact_local_context(
    goal: &npa_tactic::MachineGoal,
) -> Vec<MinimalFailingArtifactLocal> {
    goal.context
        .iter()
        .map(|local| MinimalFailingArtifactLocal {
            name: local.name.clone(),
            type_hash: core_expr_hash(&local.ty),
            value_hash: local.value.as_ref().map(core_expr_hash),
        })
        .collect()
}

fn minimal_failing_artifact_export_kind(kind: &ExportKind) -> &'static str {
    match kind {
        ExportKind::Axiom => "axiom",
        ExportKind::Def => "def",
        ExportKind::Theorem => "theorem",
        ExportKind::Inductive => "inductive",
        ExportKind::Constructor => "constructor",
        ExportKind::Recursor => "recursor",
    }
}

fn minimal_failing_artifact_structured_diagnostic_hash(
    diagnostic: &MinimalFailingArtifactDiagnostic,
) -> Result<Hash, MinimalFailingArtifactError> {
    minimal_failing_artifact_projection_from_structured_diagnostic(diagnostic)
        .diagnostic_hash()
        .map_err(|_| MinimalFailingArtifactError::DiagnosticCanonicalization)
}

fn minimal_failing_artifact_projection_from_structured_diagnostic(
    diagnostic: &MinimalFailingArtifactDiagnostic,
) -> MachineApiDiagnosticProjection {
    MachineApiDiagnosticProjection {
        kind: diagnostic.kind,
        phase: diagnostic.phase,
        retryable: diagnostic.retryable,
        goal_id: diagnostic.goal_id,
        tactic_kind: diagnostic.tactic_kind,
        primary_name: diagnostic.primary_name.clone(),
        primary_axiom_ref: diagnostic.primary_axiom_ref.clone(),
        expected_hash: diagnostic.expected_hash,
        actual_hash: diagnostic.actual_hash,
        source_message: String::new(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::UnsupportedMachineTactic,
            "structured diagnostic artifact",
        )),
    }
}

fn minimal_failing_artifact_diagnostic_canonical_bytes(
    diagnostic: &MinimalFailingArtifactDiagnostic,
    out: &mut Vec<u8>,
) -> Result<(), MinimalFailingArtifactError> {
    let actual_hash = minimal_failing_artifact_structured_diagnostic_hash(diagnostic)?;
    repair_encode_string(out, diagnostic.kind.as_str());
    repair_encode_string(out, diagnostic.phase.as_str());
    minimal_failing_encode_bool(out, diagnostic.retryable);
    minimal_failing_encode_optional_goal_id(out, diagnostic.goal_id);
    minimal_failing_encode_optional_tactic_kind(out, diagnostic.tactic_kind);
    minimal_failing_encode_optional_name(out, diagnostic.primary_name.as_ref());
    minimal_failing_encode_optional_axiom_ref(out, diagnostic.primary_axiom_ref.as_ref());
    minimal_failing_encode_optional_hash(out, diagnostic.expected_hash);
    minimal_failing_encode_optional_hash(out, diagnostic.actual_hash);
    out.extend_from_slice(&diagnostic.diagnostic_hash);
    out.extend_from_slice(&actual_hash);
    Ok(())
}

fn artifact_hash_for_failure_key(
    key: &FailureMemoryKey,
    artifacts: &[MinimalFailingArtifact],
) -> Option<Hash> {
    artifacts
        .iter()
        .find(|artifact| {
            failure_memory_candidate_shape_hash(&artifact.candidate) == key.candidate_shape_hash
                && artifact.structured_diagnostic.kind == key.error_kind
                && artifact.structured_diagnostic.diagnostic_hash == key.diagnostic_hash
        })
        .map(|artifact| artifact.artifact_hash)
}

fn repair_proposal_validation_error_summary(
    error: &RepairProposalValidationError,
) -> (Option<MachineApiErrorKind>, String) {
    match error {
        RepairProposalValidationError::NoOpenGoal => (None, "no_open_goal".to_owned()),
        RepairProposalValidationError::DisallowedOperator { category, operator } => (
            None,
            format!(
                "disallowed_operator:{}:{}",
                category.as_str(),
                operator.as_str()
            ),
        ),
        RepairProposalValidationError::OperatorNotConvertible { operator } => (
            None,
            format!("operator_not_convertible:{}", operator.as_str()),
        ),
        RepairProposalValidationError::CandidateRejected {
            operator,
            diagnostic_kind,
            phase,
        } => (
            Some(*diagnostic_kind),
            format!(
                "candidate_rejected:{}:{}",
                operator.map(RepairOperatorKind::as_str).unwrap_or("none"),
                phase.as_str()
            ),
        ),
    }
}

fn hard_negative_no_progress_reason(reason: &RepairChainTerminationReason) -> Option<String> {
    match reason {
        RepairChainTerminationReason::RepeatedDiagnosticHash { .. } => {
            Some("repeated_diagnostic_hash".to_owned())
        }
        RepairChainTerminationReason::RepeatedCandidatePayloadHash { .. } => {
            Some("repeated_candidate_payload_hash".to_owned())
        }
        RepairChainTerminationReason::RepeatedCandidateIdentity { .. } => {
            Some("repeated_candidate_identity".to_owned())
        }
        RepairChainTerminationReason::MaxRepairDepth { .. } => Some("max_repair_depth".to_owned()),
        _ => None,
    }
}

fn hard_negative_repair_chain_identity(
    report: &RepairChainReport,
) -> (Option<Hash>, Option<Hash>, u64) {
    let mut candidate_shape_hash = None;
    let mut diagnostic_hash = report.final_diagnostic_hash;
    let mut occurrence_count = report.steps.len().max(1) as u64;
    match &report.termination_reason {
        RepairChainTerminationReason::RepeatedDiagnosticHash {
            diagnostic_hash: repeated,
            count,
            ..
        } => {
            diagnostic_hash = Some(*repeated);
            occurrence_count = *count as u64;
        }
        RepairChainTerminationReason::RepeatedCandidatePayloadHash {
            candidate_payload_hash: repeated,
            count,
            ..
        } => {
            candidate_shape_hash = Some(*repeated);
            occurrence_count = *count as u64;
        }
        RepairChainTerminationReason::RepeatedCandidateIdentity { .. }
        | RepairChainTerminationReason::MaxRepairDepth { .. } => {
            for step in report.steps.iter().rev() {
                if candidate_shape_hash.is_none() {
                    candidate_shape_hash = step.executed_candidate_payload_hash;
                }
                if diagnostic_hash.is_none() {
                    diagnostic_hash = Some(step.diagnostic_hash);
                }
                if candidate_shape_hash.is_some() && diagnostic_hash.is_some() {
                    break;
                }
            }
        }
        _ => {}
    }
    (candidate_shape_hash, diagnostic_hash, occurrence_count)
}

fn hard_negative_record_canonical_bytes(record: &HardNegativeRecord) -> Vec<u8> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, record.kind.as_str());
    minimal_failing_encode_optional_failure_memory_key(&mut out, record.key.as_ref());
    minimal_failing_encode_optional_hash(&mut out, record.artifact_hash);
    minimal_failing_encode_optional_hash(&mut out, record.candidate_shape_hash);
    minimal_failing_encode_optional_hash(&mut out, record.diagnostic_hash);
    match record.error_kind {
        Some(kind) => {
            out.push(0x01);
            repair_encode_string(&mut out, kind.as_str());
        }
        None => out.push(0x00),
    }
    minimal_failing_encode_optional_hash(&mut out, record.repair_operator_hash);
    minimal_failing_encode_optional_repair_chain_reason(
        &mut out,
        record.repair_chain_termination.as_ref(),
    );
    repair_encode_len(&mut out, record.reasons.len());
    for reason in &record.reasons {
        repair_encode_string(&mut out, reason);
    }
    repair_encode_u64(&mut out, record.occurrence_count);
    out
}

fn minimal_failing_encode_optional_failure_memory_key(
    out: &mut Vec<u8>,
    key: Option<&FailureMemoryKey>,
) {
    match key {
        Some(key) => {
            out.push(0x01);
            out.extend_from_slice(&failure_memory_key_canonical_bytes(key));
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_encode_optional_repair_chain_reason(
    out: &mut Vec<u8>,
    reason: Option<&RepairChainTerminationReason>,
) {
    let Some(reason) = reason else {
        out.push(0x00);
        return;
    };
    out.push(0x01);
    match reason {
        RepairChainTerminationReason::RepairSucceeded => {
            repair_encode_string(out, "repair_succeeded");
        }
        RepairChainTerminationReason::NoRepairCategory => {
            repair_encode_string(out, "no_repair_category");
        }
        RepairChainTerminationReason::NoRepairProposals => {
            repair_encode_string(out, "no_repair_proposals");
        }
        RepairChainTerminationReason::NoExecutableProposal => {
            repair_encode_string(out, "no_executable_proposal");
        }
        RepairChainTerminationReason::MaxRepairDepth { max } => {
            repair_encode_string(out, "max_repair_depth");
            repair_encode_u64(out, *max as u64);
        }
        RepairChainTerminationReason::MaxTotalCandidates { max } => {
            repair_encode_string(out, "max_total_candidates");
            repair_encode_u64(out, *max as u64);
        }
        RepairChainTerminationReason::MaxGeneratedGoals { max, attempted } => {
            repair_encode_string(out, "max_generated_goals");
            repair_encode_u64(out, *max as u64);
            repair_encode_u64(out, *attempted as u64);
        }
        RepairChainTerminationReason::RepeatedDiagnosticHash {
            diagnostic_hash,
            count,
            max,
        } => {
            repair_encode_string(out, "repeated_diagnostic_hash");
            out.extend_from_slice(diagnostic_hash);
            repair_encode_u64(out, *count as u64);
            repair_encode_u64(out, *max as u64);
        }
        RepairChainTerminationReason::RepeatedCandidatePayloadHash {
            candidate_payload_hash,
            count,
            max,
        } => {
            repair_encode_string(out, "repeated_candidate_payload_hash");
            out.extend_from_slice(candidate_payload_hash);
            repair_encode_u64(out, *count as u64);
            repair_encode_u64(out, *max as u64);
        }
        RepairChainTerminationReason::RepeatedCandidateIdentity {
            candidate_identity_hash,
        } => {
            repair_encode_string(out, "repeated_candidate_identity");
            out.extend_from_slice(candidate_identity_hash);
        }
        RepairChainTerminationReason::PerErrorCategoryProposalLimit { category, max } => {
            repair_encode_string(out, "per_error_category_proposal_limit");
            repair_encode_string(out, category.as_str());
            repair_encode_u64(out, *max as u64);
        }
    }
}

fn minimal_failing_encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn minimal_failing_encode_optional_hash(out: &mut Vec<u8>, value: Option<Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            out.extend_from_slice(&hash);
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_encode_optional_goal_id(out: &mut Vec<u8>, value: Option<GoalId>) {
    match value {
        Some(goal_id) => {
            out.push(0x01);
            repair_encode_u64(out, goal_id.0);
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_encode_optional_tactic_kind(
    out: &mut Vec<u8>,
    value: Option<MachineApiTacticKind>,
) {
    match value {
        Some(kind) => {
            out.push(0x01);
            repair_encode_string(out, kind.as_str());
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_encode_optional_name(out: &mut Vec<u8>, value: Option<&Name>) {
    match value {
        Some(name) => {
            out.push(0x01);
            repair_encode_string(out, &name.as_dotted());
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_encode_optional_axiom_ref(
    out: &mut Vec<u8>,
    value: Option<&MachineAxiomRefWire>,
) {
    match value {
        Some(axiom_ref) => {
            out.push(0x01);
            out.extend_from_slice(&encode_machine_axiom_ref_wire(axiom_ref));
        }
        None => out.push(0x00),
    }
}

fn minimal_failing_hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    hasher.update([0]);
    hasher.update(payload);
    hasher.finalize().into()
}

fn failure_memory_stale_reasons(
    record: &FailureMemoryRecord,
    context: &FailureMemoryLookupContext,
) -> Vec<FailureMemoryStaleReason> {
    let mut reasons = Vec::new();
    if record.key.environment_hash != context.environment_hash {
        reasons.push(FailureMemoryStaleReason::EnvironmentHash);
    }
    if record.import_identity_hash != context.import_identity_hash {
        reasons.push(FailureMemoryStaleReason::ImportIdentity);
    }
    if record.key.goal_fingerprint != context.goal_fingerprint {
        reasons.push(FailureMemoryStaleReason::GoalFingerprint);
    }
    reasons
}

fn choose_failure_memory_field<T: Ord>(
    current: Option<T>,
    incoming: Option<T>,
    current_observation: FailureMemoryObservation,
    incoming_observation: FailureMemoryObservation,
) -> Option<T> {
    match (current, incoming) {
        (None, None) => None,
        (Some(value), None) | (None, Some(value)) => Some(value),
        (Some(current), Some(incoming)) => {
            if incoming_observation > current_observation
                || (incoming_observation == current_observation && incoming > current)
            {
                Some(incoming)
            } else {
                Some(current)
            }
        }
    }
}

const REPAIR_POLICY_TYPE_MISMATCH: &[RepairOperatorKind] = &[
    RepairOperatorKind::SpecializeHypothesis,
    RepairOperatorKind::SwitchStrategy,
];
const REPAIR_POLICY_EXPECTED_PI_TYPE: &[RepairOperatorKind] = &[RepairOperatorKind::SwitchStrategy];
const REPAIR_POLICY_REWRITE: &[RepairOperatorKind] = &[
    RepairOperatorKind::ReverseRewrite,
    RepairOperatorKind::SelectRewriteOccurrence,
    RepairOperatorKind::ReduceSimpSet,
    RepairOperatorKind::SwitchStrategy,
];
const REPAIR_POLICY_SIMP_NO_PROGRESS: &[RepairOperatorKind] = &[
    RepairOperatorKind::ReduceSimpSet,
    RepairOperatorKind::Unfold,
    RepairOperatorKind::Fold,
    RepairOperatorKind::SwitchStrategy,
];
const REPAIR_POLICY_IMPLICIT_ARGUMENT: &[RepairOperatorKind] = &[
    RepairOperatorKind::InstantiateArgument,
    RepairOperatorKind::InstantiateUniverse,
];
const REPAIR_POLICY_UNIVERSE_MISMATCH: &[RepairOperatorKind] =
    &[RepairOperatorKind::InstantiateUniverse];
const REPAIR_POLICY_TOO_MANY_GOALS: &[RepairOperatorKind] = &[RepairOperatorKind::SwitchStrategy];
const REPAIR_POLICY_BUDGET_EXCEEDED: &[RepairOperatorKind] = &[
    RepairOperatorKind::ReduceSimpSet,
    RepairOperatorKind::SwitchStrategy,
];
const REPAIR_POLICY_NOOP: &[RepairOperatorKind] = &[];

pub fn repair_policy_allowed_operators(
    category: RepairDiagnosticCategory,
) -> &'static [RepairOperatorKind] {
    match category {
        RepairDiagnosticCategory::UnsupportedMachineTactic
        | RepairDiagnosticCategory::InvalidReplayPlan
        | RepairDiagnosticCategory::KernelRejectedAfterVerify
        | RepairDiagnosticCategory::UnknownName => REPAIR_POLICY_NOOP,
        RepairDiagnosticCategory::TypeMismatch => REPAIR_POLICY_TYPE_MISMATCH,
        RepairDiagnosticCategory::ExpectedPiType => REPAIR_POLICY_EXPECTED_PI_TYPE,
        RepairDiagnosticCategory::RewriteRuleInvalid => REPAIR_POLICY_REWRITE,
        RepairDiagnosticCategory::SimpNoProgress => REPAIR_POLICY_SIMP_NO_PROGRESS,
        RepairDiagnosticCategory::ImplicitArgumentRequired => REPAIR_POLICY_IMPLICIT_ARGUMENT,
        RepairDiagnosticCategory::UniverseMismatch => REPAIR_POLICY_UNIVERSE_MISMATCH,
        RepairDiagnosticCategory::TooManyGoals => REPAIR_POLICY_TOO_MANY_GOALS,
        RepairDiagnosticCategory::BudgetExceeded => REPAIR_POLICY_BUDGET_EXCEEDED,
    }
}

pub fn repair_operator_is_allowed(
    category: RepairDiagnosticCategory,
    operator: RepairOperatorKind,
) -> bool {
    repair_policy_allowed_operators(category).contains(&operator)
}

pub const fn repair_operator_proposal_category(
    _operator: RepairOperatorKind,
) -> RepairProposalCategory {
    RepairProposalCategory::ProofStateRepair
}

pub fn validate_repair_operator_batch(
    category: RepairDiagnosticCategory,
    operators: &[RepairOperator],
    max_operators: usize,
) -> Result<(), RepairOperatorValidationError> {
    if operators.len() > max_operators {
        return Err(RepairOperatorValidationError::BudgetExceeded {
            actual: operators.len(),
            max: max_operators,
        });
    }

    let mut seen = BTreeSet::new();
    for operator in operators {
        if !repair_operator_is_allowed(category, operator.kind()) {
            return Err(RepairOperatorValidationError::DisallowedOperator {
                category,
                operator: operator.kind(),
            });
        }
        let operator_hash = repair_operator_hash(operator);
        if !seen.insert(operator_hash) {
            return Err(RepairOperatorValidationError::DuplicateOperator { operator_hash });
        }
    }
    Ok(())
}

pub fn repair_diagnostic_category_from_projection(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Option<RepairDiagnosticCategory> {
    if projection_has_universe_mismatch(diagnostic) {
        return Some(RepairDiagnosticCategory::UniverseMismatch);
    }

    match diagnostic.kind {
        MachineApiErrorKind::UnsupportedTactic => {
            Some(RepairDiagnosticCategory::UnsupportedMachineTactic)
        }
        MachineApiErrorKind::InvalidReplayPlan | MachineApiErrorKind::ReplayHashMismatch => {
            Some(RepairDiagnosticCategory::InvalidReplayPlan)
        }
        MachineApiErrorKind::VerifyFailed => {
            Some(RepairDiagnosticCategory::KernelRejectedAfterVerify)
        }
        MachineApiErrorKind::UnknownName => Some(RepairDiagnosticCategory::UnknownName),
        MachineApiErrorKind::TypeMismatch => Some(RepairDiagnosticCategory::TypeMismatch),
        MachineApiErrorKind::ExpectedPiType => Some(RepairDiagnosticCategory::ExpectedPiType),
        MachineApiErrorKind::RewriteRuleInvalid => {
            Some(RepairDiagnosticCategory::RewriteRuleInvalid)
        }
        MachineApiErrorKind::SimpNoProgress => Some(RepairDiagnosticCategory::SimpNoProgress),
        MachineApiErrorKind::ImplicitArgumentRequired => {
            Some(RepairDiagnosticCategory::ImplicitArgumentRequired)
        }
        MachineApiErrorKind::TooManyGoals => Some(RepairDiagnosticCategory::TooManyGoals),
        MachineApiErrorKind::BudgetExceeded => Some(RepairDiagnosticCategory::BudgetExceeded),
        _ => None,
    }
}

pub fn generate_repair_proposals(
    context: &RepairGenerationContext<'_>,
) -> Vec<RepairGeneratedProposal> {
    generate_repair_proposals_with_retrieval(context, &EmptyRepairRetrievalAdapter)
}

pub fn generate_repair_proposals_with_retrieval(
    context: &RepairGenerationContext<'_>,
    retrieval: &impl RepairRetrievalAdapter,
) -> Vec<RepairGeneratedProposal> {
    let Some(category) = repair_diagnostic_category_from_projection(context.diagnostic) else {
        return Vec::new();
    };
    let Some(goal_id) = repair_context_goal_id(context) else {
        return Vec::new();
    };

    let deterministic_budget_hash = tactic_budget_hash(context.deterministic_budget);
    let mut proposals = sorted_local_repair_operators(category, context, goal_id)
        .into_iter()
        .take(context.max_proposals)
        .map(|seed| {
            let operator_hash = repair_operator_hash(&seed.operator);
            let validation =
                validate_repair_operator_as_candidate(context, category, seed.operator.clone());
            RepairGeneratedProposal {
                provenance: RepairProposalProvenance {
                    source: RepairProposalSource::LocalOperator,
                    category,
                    diagnostic_path: seed.diagnostic_path,
                    state_fingerprint: context.state_fingerprint,
                    deterministic_budget_hash,
                },
                operator: Some(seed.operator),
                operator_hash: Some(operator_hash),
                validation,
            }
        })
        .collect::<Vec<_>>();

    let retrieval_request = RepairRetrievalRequest {
        category,
        diagnostic: context.diagnostic,
        state_fingerprint: context.state_fingerprint,
        deterministic_budget_hash,
        goal_id,
    };
    proposals.extend(
        retrieval
            .repair_candidates(&retrieval_request)
            .into_iter()
            .map(|candidate| {
                let validation = validate_repair_candidate(context, goal_id, None, candidate);
                RepairGeneratedProposal {
                    provenance: RepairProposalProvenance {
                        source: RepairProposalSource::RetrievalCandidate,
                        category,
                        diagnostic_path: Vec::new(),
                        state_fingerprint: context.state_fingerprint,
                        deterministic_budget_hash,
                    },
                    operator: None,
                    operator_hash: None,
                    validation,
                }
            }),
    );

    proposals
}

pub fn run_repair_chain(
    context: &RepairChainRunContext<'_>,
) -> Result<RepairChainReport, MachineApiDiagnosticCanonicalizationError> {
    run_repair_chain_with_retrieval(context, &EmptyRepairRetrievalAdapter)
}

pub fn run_repair_chain_with_retrieval(
    context: &RepairChainRunContext<'_>,
    retrieval: &impl RepairRetrievalAdapter,
) -> Result<RepairChainReport, MachineApiDiagnosticCanonicalizationError> {
    let mut working_state = context.state.clone();
    let mut current_diagnostic = context.diagnostic.clone();
    let mut diagnostic_counts = BTreeMap::<Hash, usize>::new();
    let mut candidate_payload_counts = BTreeMap::<Hash, usize>::new();
    let mut candidate_identity_hashes = BTreeSet::<Hash>::new();
    let mut category_proposal_counts = BTreeMap::<RepairDiagnosticCategory, usize>::new();
    let mut report = RepairChainReport {
        termination_reason: RepairChainTerminationReason::MaxRepairDepth {
            max: context.limits.max_repair_depth,
        },
        budget: RepairChainBudgetReport::default(),
        steps: Vec::new(),
        initial_state_fingerprint: context.state_fingerprint,
        final_state_fingerprint: context.state_fingerprint,
        final_diagnostic_hash: None,
    };

    for depth in 0..context.limits.max_repair_depth {
        let diagnostic_hash = current_diagnostic.diagnostic_hash()?;
        report.final_diagnostic_hash = Some(diagnostic_hash);
        report.budget.consumed_diagnostic_budget += 1;
        let diagnostic_count =
            repair_chain_increment_count(&mut diagnostic_counts, diagnostic_hash);
        if diagnostic_count > context.limits.max_repeated_diagnostic_hash_count {
            let reason = RepairChainTerminationReason::RepeatedDiagnosticHash {
                diagnostic_hash,
                count: diagnostic_count,
                max: context.limits.max_repeated_diagnostic_hash_count,
            };
            report.steps.push(repair_chain_terminated_step(
                depth,
                None,
                diagnostic_hash,
                0,
                0,
                reason.clone(),
            ));
            return Ok(repair_chain_finish(
                report,
                reason,
                working_state.fingerprint,
            ));
        }

        let Some(category) = repair_diagnostic_category_from_projection(&current_diagnostic) else {
            let reason = RepairChainTerminationReason::NoRepairCategory;
            report.steps.push(repair_chain_terminated_step(
                depth,
                None,
                diagnostic_hash,
                0,
                0,
                reason.clone(),
            ));
            return Ok(repair_chain_finish(
                report,
                reason,
                working_state.fingerprint,
            ));
        };

        let generation_context = RepairGenerationContext {
            state: &working_state,
            state_fingerprint: working_state.fingerprint,
            diagnostic: &current_diagnostic,
            deterministic_budget: context.deterministic_budget,
            profile_version: context.profile_version,
            required_features: context.required_features,
            max_proposals: DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN,
        };
        let proposals = generate_repair_proposals_with_retrieval(&generation_context, retrieval);
        let generated_proposal_count = proposals.len();
        report.budget.generated_proposal_count += generated_proposal_count;

        if proposals.is_empty() {
            let reason = RepairChainTerminationReason::NoRepairProposals;
            report.steps.push(repair_chain_terminated_step(
                depth,
                Some(category),
                diagnostic_hash,
                generated_proposal_count,
                0,
                reason.clone(),
            ));
            return Ok(repair_chain_finish(
                report,
                reason,
                working_state.fingerprint,
            ));
        }

        let mut suppressed_proposals = 0;
        let mut selected = None;

        for proposal in proposals {
            let RepairGeneratedProposal {
                provenance,
                operator_hash,
                validation,
                ..
            } = proposal;
            let category_count =
                repair_chain_increment_count(&mut category_proposal_counts, category);
            if category_count > context.limits.max_proposals_per_error_category {
                suppressed_proposals += 1;
                report.budget.suppressed_proposal_count += 1;
                let reason = RepairChainTerminationReason::PerErrorCategoryProposalLimit {
                    category,
                    max: context.limits.max_proposals_per_error_category,
                };
                report.steps.push(repair_chain_terminated_step(
                    depth,
                    Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposals,
                    reason.clone(),
                ));
                return Ok(repair_chain_finish(
                    report,
                    reason,
                    working_state.fingerprint,
                ));
            }

            let RepairProposalValidation::Candidate {
                candidate,
                validated,
            } = validation
            else {
                suppressed_proposals += 1;
                report.budget.suppressed_proposal_count += 1;
                continue;
            };

            if report.budget.considered_candidate_count >= context.limits.max_total_candidates {
                suppressed_proposals += 1;
                report.budget.suppressed_proposal_count += 1;
                let reason = RepairChainTerminationReason::MaxTotalCandidates {
                    max: context.limits.max_total_candidates,
                };
                report.steps.push(repair_chain_terminated_step(
                    depth,
                    Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposals,
                    reason.clone(),
                ));
                return Ok(repair_chain_finish(
                    report,
                    reason,
                    working_state.fingerprint,
                ));
            }
            report.budget.considered_candidate_count += 1;

            let candidate_payload_hash = failure_memory_candidate_shape_hash(&candidate);
            let payload_count =
                repair_chain_increment_count(&mut candidate_payload_counts, candidate_payload_hash);
            if payload_count > context.limits.max_repeated_candidate_payload_hash_count {
                suppressed_proposals += 1;
                report.budget.suppressed_proposal_count += 1;
                let reason = RepairChainTerminationReason::RepeatedCandidatePayloadHash {
                    candidate_payload_hash,
                    count: payload_count,
                    max: context.limits.max_repeated_candidate_payload_hash_count,
                };
                report.steps.push(repair_chain_terminated_step(
                    depth,
                    Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposals,
                    reason.clone(),
                ));
                return Ok(repair_chain_finish(
                    report,
                    reason,
                    working_state.fingerprint,
                ));
            }

            let candidate_identity_hash = repair_chain_candidate_identity_hash(
                &provenance,
                operator_hash,
                diagnostic_hash,
                validated.candidate_hash,
            );
            if !candidate_identity_hashes.insert(candidate_identity_hash) {
                suppressed_proposals += 1;
                report.budget.suppressed_proposal_count += 1;
                let reason = RepairChainTerminationReason::RepeatedCandidateIdentity {
                    candidate_identity_hash,
                };
                report.steps.push(repair_chain_terminated_step(
                    depth,
                    Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposals,
                    reason.clone(),
                ));
                return Ok(repair_chain_finish(
                    report,
                    reason,
                    working_state.fingerprint,
                ));
            }

            if selected.is_none() {
                selected = Some(RepairChainSelectedCandidate {
                    candidate_payload_hash,
                    candidate_identity_hash,
                    validated: *validated,
                });
            }
        }

        let Some(selected) = selected else {
            let reason = RepairChainTerminationReason::NoExecutableProposal;
            report.steps.push(repair_chain_terminated_step(
                depth,
                Some(category),
                diagnostic_hash,
                generated_proposal_count,
                suppressed_proposals,
                reason.clone(),
            ));
            return Ok(repair_chain_finish(
                report,
                reason,
                working_state.fingerprint,
            ));
        };

        report.budget.consumed_tactic_budget += 1;
        match machine_tactic_run_machine_tactic_with_budget(
            &working_state,
            selected.validated.tactic,
            context.deterministic_budget,
        ) {
            Ok(run) => {
                let attempted_generated_goals =
                    report.budget.generated_goal_count + run.delta.added_goals.len();
                if attempted_generated_goals > context.limits.max_generated_goals {
                    let reason = RepairChainTerminationReason::MaxGeneratedGoals {
                        max: context.limits.max_generated_goals,
                        attempted: attempted_generated_goals,
                    };
                    report.steps.push(RepairChainStepReport {
                        depth,
                        category: Some(category),
                        diagnostic_hash,
                        generated_proposal_count,
                        suppressed_proposal_count: suppressed_proposals,
                        executed_candidate_identity_hash: Some(selected.candidate_identity_hash),
                        executed_candidate_payload_hash: Some(selected.candidate_payload_hash),
                        outcome: RepairChainStepOutcome::Terminated {
                            reason: reason.clone(),
                        },
                    });
                    return Ok(repair_chain_finish(
                        report,
                        reason,
                        working_state.fingerprint,
                    ));
                }

                report.budget.generated_goal_count = attempted_generated_goals;
                let next_state_fingerprint = run.state.fingerprint;
                let generated_goals = run.delta.added_goals.len();
                working_state = run.state;
                report.steps.push(RepairChainStepReport {
                    depth,
                    category: Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposal_count: suppressed_proposals,
                    executed_candidate_identity_hash: Some(selected.candidate_identity_hash),
                    executed_candidate_payload_hash: Some(selected.candidate_payload_hash),
                    outcome: RepairChainStepOutcome::CandidateSucceeded {
                        next_state_fingerprint,
                        generated_goals,
                    },
                });
                let reason = RepairChainTerminationReason::RepairSucceeded;
                return Ok(repair_chain_finish(
                    report,
                    reason,
                    working_state.fingerprint,
                ));
            }
            Err(error) => {
                let next_diagnostic_hash = error.diagnostic.diagnostic_hash()?;
                report.final_diagnostic_hash = Some(next_diagnostic_hash);
                report.steps.push(RepairChainStepReport {
                    depth,
                    category: Some(category),
                    diagnostic_hash,
                    generated_proposal_count,
                    suppressed_proposal_count: suppressed_proposals,
                    executed_candidate_identity_hash: Some(selected.candidate_identity_hash),
                    executed_candidate_payload_hash: Some(selected.candidate_payload_hash),
                    outcome: RepairChainStepOutcome::CandidateFailed {
                        next_diagnostic_hash,
                    },
                });
                current_diagnostic = error.diagnostic;
            }
        }
    }

    let reason = RepairChainTerminationReason::MaxRepairDepth {
        max: context.limits.max_repair_depth,
    };
    if report.final_diagnostic_hash.is_none() {
        report.final_diagnostic_hash = Some(current_diagnostic.diagnostic_hash()?);
    }
    Ok(repair_chain_finish(
        report,
        reason,
        working_state.fingerprint,
    ))
}

#[derive(Clone, Debug)]
struct RepairChainSelectedCandidate {
    candidate_payload_hash: Hash,
    candidate_identity_hash: Hash,
    validated: ValidatedMachineTactic,
}

fn repair_chain_increment_count<K: Ord + Copy>(counts: &mut BTreeMap<K, usize>, key: K) -> usize {
    let count = counts.entry(key).or_insert(0);
    *count += 1;
    *count
}

fn repair_chain_candidate_identity_hash(
    provenance: &RepairProposalProvenance,
    operator_hash: Option<Hash>,
    diagnostic_hash: Hash,
    candidate_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    repair_encode_string(&mut out, provenance.source.as_str());
    repair_encode_string(&mut out, provenance.category.as_str());
    repair_encode_len(&mut out, provenance.diagnostic_path.len());
    for segment in &provenance.diagnostic_path {
        repair_encode_string(&mut out, segment);
    }
    match operator_hash {
        Some(operator_hash) => {
            out.push(0x01);
            out.extend_from_slice(&operator_hash);
        }
        None => out.push(0x00),
    }
    out.extend_from_slice(&diagnostic_hash);
    out.extend_from_slice(&provenance.state_fingerprint);
    out.extend_from_slice(&provenance.deterministic_budget_hash);
    out.extend_from_slice(&candidate_hash);
    repair_hash_with_domain(REPAIR_CHAIN_CANDIDATE_IDENTITY_HASH_DOMAIN, &out)
}

fn repair_chain_terminated_step(
    depth: usize,
    category: Option<RepairDiagnosticCategory>,
    diagnostic_hash: Hash,
    generated_proposal_count: usize,
    suppressed_proposal_count: usize,
    reason: RepairChainTerminationReason,
) -> RepairChainStepReport {
    RepairChainStepReport {
        depth,
        category,
        diagnostic_hash,
        generated_proposal_count,
        suppressed_proposal_count,
        executed_candidate_identity_hash: None,
        executed_candidate_payload_hash: None,
        outcome: RepairChainStepOutcome::Terminated { reason },
    }
}

fn repair_chain_finish(
    mut report: RepairChainReport,
    reason: RepairChainTerminationReason,
    final_state_fingerprint: Hash,
) -> RepairChainReport {
    report.termination_reason = reason;
    report.final_state_fingerprint = final_state_fingerprint;
    report
}

pub fn validate_repair_operator_as_candidate(
    context: &RepairGenerationContext<'_>,
    category: RepairDiagnosticCategory,
    operator: RepairOperator,
) -> RepairProposalValidation {
    if !repair_operator_is_allowed(category, operator.kind()) {
        return RepairProposalValidation::Rejected {
            error: RepairProposalValidationError::DisallowedOperator {
                category,
                operator: operator.kind(),
            },
        };
    }

    let Some(goal_id) =
        repair_operator_goal_id(&operator).or_else(|| repair_context_goal_id(context))
    else {
        return RepairProposalValidation::Rejected {
            error: RepairProposalValidationError::NoOpenGoal,
        };
    };

    match repair_operator_to_candidate(context.state, &operator) {
        Ok(candidate) => {
            validate_repair_candidate(context, goal_id, Some(operator.kind()), candidate)
        }
        Err(error) => RepairProposalValidation::Rejected { error },
    }
}

#[derive(Clone, Debug)]
struct RepairOperatorSeed {
    operator: RepairOperator,
    diagnostic_path: Vec<String>,
}

fn projection_has_universe_mismatch(diagnostic: &MachineApiDiagnosticProjection) -> bool {
    match &diagnostic.upstream {
        MachineApiUpstreamDiagnostic::MachineTactic(upstream) => {
            matches!(
                upstream.kind,
                MachineTacticDiagnosticKind::UniverseArgumentMismatch
            ) || upstream.universe_diagnostic().is_some()
                || upstream.unification_conflict_kind()
                    == Some(npa_tactic::UnificationDiagnosticKind::UniverseMismatch)
        }
        MachineApiUpstreamDiagnostic::Frontend(_) => false,
    }
}

fn repair_context_goal_id(context: &RepairGenerationContext<'_>) -> Option<GoalId> {
    context
        .diagnostic
        .goal_id
        .or_else(|| context.state.open_goals.first().copied())
}

fn sorted_local_repair_operators(
    category: RepairDiagnosticCategory,
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    let mut seeds = local_repair_operator_seeds(category, context, goal_id);
    seeds.retain(|seed| repair_operator_is_allowed(category, seed.operator.kind()));
    seeds.sort_by(|left, right| {
        repair_policy_priority(category, left.operator.kind())
            .cmp(&repair_policy_priority(category, right.operator.kind()))
            .then_with(|| left.diagnostic_path.cmp(&right.diagnostic_path))
            .then_with(|| {
                repair_operator_ref_identity(&left.operator)
                    .cmp(&repair_operator_ref_identity(&right.operator))
            })
            .then_with(|| {
                repair_operator_hash(&left.operator).cmp(&repair_operator_hash(&right.operator))
            })
    });
    let mut seen = BTreeSet::new();
    seeds.retain(|seed| seen.insert(repair_operator_hash(&seed.operator)));
    seeds
}

fn local_repair_operator_seeds(
    category: RepairDiagnosticCategory,
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    match category {
        RepairDiagnosticCategory::TypeMismatch => type_mismatch_repair_operators(context, goal_id),
        RepairDiagnosticCategory::ExpectedPiType => vec![RepairOperatorSeed {
            operator: RepairOperator::SwitchStrategy {
                goal_id: Some(goal_id),
                profile: RepairStrategyProfile::ApplyExact,
            },
            diagnostic_path: Vec::new(),
        }],
        RepairDiagnosticCategory::RewriteRuleInvalid | RepairDiagnosticCategory::SimpNoProgress => {
            rewrite_repair_operators(category, context, goal_id)
        }
        RepairDiagnosticCategory::ImplicitArgumentRequired => {
            implicit_argument_repair_operators(context, goal_id)
        }
        RepairDiagnosticCategory::UniverseMismatch => {
            universe_mismatch_repair_operators(context, goal_id)
        }
        RepairDiagnosticCategory::TooManyGoals => vec![RepairOperatorSeed {
            operator: RepairOperator::SwitchStrategy {
                goal_id: Some(goal_id),
                profile: RepairStrategyProfile::LowerGoalGrowth,
            },
            diagnostic_path: Vec::new(),
        }],
        RepairDiagnosticCategory::BudgetExceeded => vec![
            RepairOperatorSeed {
                operator: RepairOperator::ReduceSimpSet {
                    goal_id: Some(goal_id),
                    remove: Vec::new(),
                },
                diagnostic_path: Vec::new(),
            },
            RepairOperatorSeed {
                operator: RepairOperator::SwitchStrategy {
                    goal_id: Some(goal_id),
                    profile: RepairStrategyProfile::SmallerSimp,
                },
                diagnostic_path: Vec::new(),
            },
        ],
        RepairDiagnosticCategory::UnsupportedMachineTactic
        | RepairDiagnosticCategory::InvalidReplayPlan
        | RepairDiagnosticCategory::KernelRejectedAfterVerify
        | RepairDiagnosticCategory::UnknownName => Vec::new(),
    }
}

fn type_mismatch_repair_operators(
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    let mut seeds = Vec::new();
    if let Ok(goal) = context.state.goal(goal_id) {
        let expected = context.diagnostic.expected_hash.unwrap_or(goal.target_hash);
        for local in goal
            .context
            .iter()
            .filter(|local| core_expr_hash(&local.ty) == expected)
        {
            seeds.push(RepairOperatorSeed {
                operator: RepairOperator::SpecializeHypothesis {
                    goal_id: Some(goal_id),
                    local: RepairLocalRef {
                        name: local.name.clone(),
                    },
                    args: Vec::new(),
                },
                diagnostic_path: Vec::new(),
            });
        }
    }
    seeds.push(RepairOperatorSeed {
        operator: RepairOperator::SwitchStrategy {
            goal_id: Some(goal_id),
            profile: RepairStrategyProfile::ApplyExact,
        },
        diagnostic_path: Vec::new(),
    });
    seeds
}

fn rewrite_repair_operators(
    category: RepairDiagnosticCategory,
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    let mut seeds = Vec::new();
    if let MachineApiUpstreamDiagnostic::MachineTactic(upstream) = &context.diagnostic.upstream {
        if let Some(rewrite) = upstream.rewrite_diagnostic() {
            for site in &rewrite.sites {
                for operator in &site.repair_operators {
                    match operator {
                        npa_tactic::RewriteRepairOperator::ReverseRewrite => {
                            if category == RepairDiagnosticCategory::RewriteRuleInvalid {
                                seeds.push(RepairOperatorSeed {
                                    operator: RepairOperator::ReverseRewrite {
                                        goal_id: Some(goal_id),
                                    },
                                    diagnostic_path: site.path.clone(),
                                });
                            }
                        }
                        npa_tactic::RewriteRepairOperator::SelectRewriteOccurrence => {
                            if let Ok(path) = ExprPath::parse_wire_segments(&site.path) {
                                seeds.push(RepairOperatorSeed {
                                    operator: RepairOperator::SelectRewriteOccurrence {
                                        goal_id: Some(goal_id),
                                        path,
                                    },
                                    diagnostic_path: site.path.clone(),
                                });
                            }
                        }
                        npa_tactic::RewriteRepairOperator::ReduceSimpSet => {
                            seeds.push(RepairOperatorSeed {
                                operator: RepairOperator::ReduceSimpSet {
                                    goal_id: Some(goal_id),
                                    remove: primary_global_ref(context),
                                },
                                diagnostic_path: site.path.clone(),
                            });
                        }
                        npa_tactic::RewriteRepairOperator::Unfold => {
                            for constant in site
                                .required_unfoldings
                                .iter()
                                .map(|name| RepairGlobalRef {
                                    name: Name::from_dotted(name),
                                })
                                .chain(primary_global_ref(context))
                            {
                                seeds.push(RepairOperatorSeed {
                                    operator: RepairOperator::Unfold {
                                        goal_id: Some(goal_id),
                                        constant,
                                    },
                                    diagnostic_path: site.path.clone(),
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    if seeds.is_empty() && category == RepairDiagnosticCategory::SimpNoProgress {
        seeds.push(RepairOperatorSeed {
            operator: RepairOperator::ReduceSimpSet {
                goal_id: Some(goal_id),
                remove: primary_global_ref(context),
            },
            diagnostic_path: Vec::new(),
        });
        seeds.push(RepairOperatorSeed {
            operator: RepairOperator::SwitchStrategy {
                goal_id: Some(goal_id),
                profile: RepairStrategyProfile::SmallerSimp,
            },
            diagnostic_path: Vec::new(),
        });
    }
    seeds
}

fn implicit_argument_repair_operators(
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    context
        .diagnostic
        .expected_hash
        .map(|term_hash| RepairOperatorSeed {
            operator: RepairOperator::InstantiateArgument {
                goal_id: Some(goal_id),
                binder: 0,
                term: RepairCheckedTermPayload { term_hash },
            },
            diagnostic_path: Vec::new(),
        })
        .into_iter()
        .collect()
}

fn universe_mismatch_repair_operators(
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
) -> Vec<RepairOperatorSeed> {
    let MachineApiUpstreamDiagnostic::MachineTactic(upstream) = &context.diagnostic.upstream else {
        return Vec::new();
    };
    let Some(universe) = upstream.universe_diagnostic() else {
        return Vec::new();
    };

    universe
        .candidate_instantiations
        .iter()
        .filter(|candidate| candidate.valid && is_machine_universe_param_name(&candidate.param))
        .map(|candidate| RepairOperatorSeed {
            operator: RepairOperator::InstantiateUniverse {
                goal_id: Some(goal_id),
                param: candidate.param.clone(),
                level: candidate.level.clone(),
            },
            diagnostic_path: candidate.source_path.clone(),
        })
        .collect()
}

fn primary_global_ref(context: &RepairGenerationContext<'_>) -> Vec<RepairGlobalRef> {
    context
        .diagnostic
        .primary_name
        .as_ref()
        .map(|name| RepairGlobalRef { name: name.clone() })
        .into_iter()
        .collect()
}

fn repair_policy_priority(
    category: RepairDiagnosticCategory,
    operator: RepairOperatorKind,
) -> usize {
    repair_policy_allowed_operators(category)
        .iter()
        .position(|allowed| *allowed == operator)
        .unwrap_or(usize::MAX)
}

fn repair_operator_ref_identity(operator: &RepairOperator) -> Vec<String> {
    match operator {
        RepairOperator::InstantiateUniverse { param, .. } => vec![param.clone()],
        RepairOperator::SpecializeHypothesis { local, .. }
        | RepairOperator::Revert { local, .. } => vec![local.name.clone()],
        RepairOperator::Unfold { constant, .. } | RepairOperator::Fold { constant, .. } => {
            vec![constant.name.as_dotted()]
        }
        RepairOperator::ReduceSimpSet { remove, .. } => remove
            .iter()
            .map(|constant| constant.name.as_dotted())
            .collect(),
        _ => Vec::new(),
    }
}

fn repair_operator_goal_id(operator: &RepairOperator) -> Option<GoalId> {
    match operator {
        RepairOperator::ReverseRewrite { goal_id }
        | RepairOperator::SelectRewriteOccurrence { goal_id, .. }
        | RepairOperator::InstantiateArgument { goal_id, .. }
        | RepairOperator::InstantiateUniverse { goal_id, .. }
        | RepairOperator::IntroduceBinder { goal_id }
        | RepairOperator::SpecializeHypothesis { goal_id, .. }
        | RepairOperator::Unfold { goal_id, .. }
        | RepairOperator::Fold { goal_id, .. }
        | RepairOperator::InsertEqTransport { goal_id }
        | RepairOperator::Generalize { goal_id, .. }
        | RepairOperator::Revert { goal_id, .. }
        | RepairOperator::ChangeGoal { goal_id, .. }
        | RepairOperator::ReduceSimpSet { goal_id, .. }
        | RepairOperator::SwitchStrategy { goal_id, .. } => *goal_id,
    }
}

fn repair_operator_to_candidate(
    state: &MachineProofState,
    operator: &RepairOperator,
) -> Result<MachineTacticCandidate, RepairProposalValidationError> {
    match operator {
        RepairOperator::SpecializeHypothesis { local, args, .. } if args.is_empty() => {
            Ok(MachineTacticCandidate::Specialize(SpecializePayload {
                local_name: local.name.clone(),
                universe_args: Vec::new(),
                args: Vec::new(),
                result_name: None,
                result_policy: SpecializeResultPolicy::AddLocal,
            }))
        }
        RepairOperator::Unfold { constant, .. } => {
            let Some(head) = resolve_repair_global_head(state, &constant.name) else {
                return Err(RepairProposalValidationError::OperatorNotConvertible {
                    operator: operator.kind(),
                });
            };
            Ok(MachineTacticCandidate::Unfold(UnfoldPayload {
                target: TacticTarget::Goal,
                constant: head,
                occurrences: Vec::new(),
                max_delta_steps: Some(1),
            }))
        }
        RepairOperator::Revert { local, .. } => Ok(MachineTacticCandidate::Revert(RevertPayload {
            locals: vec![local.name.clone()],
            dependency_policy: RevertDependencyPolicy::Exact,
        })),
        RepairOperator::ReduceSimpSet { remove, .. } => Ok(MachineTacticCandidate::SimpLite {
            rules: reduced_simp_rules(state, remove),
        }),
        RepairOperator::SwitchStrategy {
            profile: RepairStrategyProfile::SmallerSimp,
            ..
        } => Ok(MachineTacticCandidate::SimpLite {
            rules: smaller_simp_rules(state),
        }),
        _ => Err(RepairProposalValidationError::OperatorNotConvertible {
            operator: operator.kind(),
        }),
    }
}

fn validate_repair_candidate(
    context: &RepairGenerationContext<'_>,
    goal_id: GoalId,
    operator: Option<RepairOperatorKind>,
    candidate: MachineTacticCandidate,
) -> RepairProposalValidation {
    match machine_tactic_validate_machine_tactic_candidate_for_state(
        context.state,
        goal_id,
        candidate.clone(),
        context.deterministic_budget,
        context.profile_version,
        context.required_features,
    ) {
        Ok(validated) => RepairProposalValidation::Candidate {
            candidate,
            validated: Box::new(validated),
        },
        Err(error) => RepairProposalValidation::Rejected {
            error: RepairProposalValidationError::CandidateRejected {
                operator,
                diagnostic_kind: error.diagnostic.kind,
                phase: error.diagnostic.phase,
            },
        },
    }
}

fn resolve_repair_global_head(state: &MachineProofState, name: &Name) -> Option<TacticHead> {
    for import in &state.env.imports {
        if !import.is_visible() {
            continue;
        }
        if let Some(export) = import.exports().iter().find(|export| &export.name == name) {
            return Some(TacticHead::Imported {
                name: export.name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            });
        }
    }

    state
        .env
        .checked_current_decls
        .iter()
        .find(|decl| decl.signature().name() == name)
        .map(|decl| TacticHead::CurrentModule {
            name: decl.signature().name().clone(),
            decl_interface_hash: decl.signature().decl_interface_hash(),
        })
}

fn reduced_simp_rules(state: &MachineProofState, remove: &[RepairGlobalRef]) -> Vec<SimpRuleRef> {
    if remove.is_empty() {
        return state.env.options.simp_rules.clone();
    }
    let remove = remove
        .iter()
        .map(|global| global.name.clone())
        .collect::<BTreeSet<_>>();
    state
        .env
        .options
        .simp_rules
        .iter()
        .filter(|rule| !remove.contains(&rule.name))
        .cloned()
        .collect()
}

fn smaller_simp_rules(state: &MachineProofState) -> Vec<SimpRuleRef> {
    let rules = &state.env.options.simp_rules;
    if rules.len() <= 1 {
        return Vec::new();
    }
    let keep = rules.len() / 2;
    rules.iter().take(keep.max(1)).cloned().collect()
}

pub fn repair_operator_canonical_bytes(operator: &RepairOperator) -> Vec<u8> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, REPAIR_OPERATOR_SCHEMA);
    repair_encode_string(&mut out, operator.kind().as_str());
    match operator {
        RepairOperator::ReverseRewrite { goal_id }
        | RepairOperator::IntroduceBinder { goal_id }
        | RepairOperator::InsertEqTransport { goal_id } => {
            repair_encode_goal_id(&mut out, *goal_id);
        }
        RepairOperator::SelectRewriteOccurrence { goal_id, path } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_expr_path(&mut out, path);
        }
        RepairOperator::InstantiateArgument {
            goal_id,
            binder,
            term,
        } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_u32(&mut out, *binder);
            repair_encode_checked_term(&mut out, term);
        }
        RepairOperator::InstantiateUniverse {
            goal_id,
            param,
            level,
        } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_string(&mut out, param);
            repair_encode_level(&mut out, level);
        }
        RepairOperator::SpecializeHypothesis {
            goal_id,
            local,
            args,
        } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_local_ref(&mut out, local);
            repair_encode_len(&mut out, args.len());
            for arg in args {
                repair_encode_checked_term(&mut out, arg);
            }
        }
        RepairOperator::Unfold { goal_id, constant }
        | RepairOperator::Fold { goal_id, constant } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_global_ref(&mut out, constant);
        }
        RepairOperator::Generalize { goal_id, term } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_checked_term(&mut out, term);
        }
        RepairOperator::Revert { goal_id, local } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_local_ref(&mut out, local);
        }
        RepairOperator::ChangeGoal { goal_id, target } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_checked_term(&mut out, target);
        }
        RepairOperator::ReduceSimpSet { goal_id, remove } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_len(&mut out, remove.len());
            for constant in remove {
                repair_encode_global_ref(&mut out, constant);
            }
        }
        RepairOperator::SwitchStrategy { goal_id, profile } => {
            repair_encode_goal_id(&mut out, *goal_id);
            repair_encode_string(&mut out, profile.as_str());
        }
    }
    out
}

pub fn repair_operator_hash(operator: &RepairOperator) -> Hash {
    repair_hash_with_domain(
        REPAIR_OPERATOR_HASH_DOMAIN,
        &repair_operator_canonical_bytes(operator),
    )
}

#[derive(Clone, Copy, Debug, Default)]
struct RunErrorCorrelation {
    unchanged_state_fingerprint: Option<Hash>,
    candidate_hash: Option<Hash>,
    deterministic_budget_hash: Option<Hash>,
    goal_id: Option<npa_tactic::GoalId>,
    tactic_kind: Option<MachineApiTacticKind>,
}

pub fn run_machine_tactic_request(
    source: &str,
    session: &mut MachineProofSession,
) -> Result<MachineTacticRunResponse, Box<MachineTacticRunError>> {
    run_machine_tactic_request_in_sessions(source, std::iter::once(session))
}

pub fn run_machine_tactic_request_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session mut MachineProofSession>,
) -> Result<MachineTacticRunResponse, Box<MachineTacticRunError>> {
    let request = parse_machine_tactic_run_request(source).map_err(request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
            RunErrorCorrelation::default(),
        ));
    };

    run_machine_tactic_request_parsed(session, request)
}

pub fn run_machine_tactic_batch_request(
    source: &str,
    session: &mut MachineProofSession,
) -> Result<MachineTacticBatchResponse, Box<MachineTacticBatchError>> {
    run_machine_tactic_batch_request_in_sessions(source, std::iter::once(session))
}

pub fn run_machine_tactic_batch_request_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session mut MachineProofSession>,
) -> Result<MachineTacticBatchResponse, Box<MachineTacticBatchError>> {
    let request = parse_machine_tactic_batch_request(source).map_err(batch_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(batch_plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
            None,
        ));
    };

    run_machine_tactic_batch_request_parsed(session, request)
}

pub fn run_machine_lazy_diagnostic_request(
    source: &str,
    session: &MachineProofSession,
    cache: Option<&mut MachineLazyDiagnosticCache>,
) -> Result<MachineLazyDiagnosticOk, MachineLazyDiagnosticError> {
    run_machine_lazy_diagnostic_request_in_sessions(source, std::iter::once(session), cache)
}

pub fn run_machine_lazy_diagnostic_request_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
    cache: Option<&mut MachineLazyDiagnosticCache>,
) -> Result<MachineLazyDiagnosticOk, MachineLazyDiagnosticError> {
    let request = parse_machine_lazy_diagnostic_request(source)
        .map_err(MachineLazyDiagnosticError::Request)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(MachineLazyDiagnosticError::UnknownSession {
            session_id: request.session_id,
        });
    };

    run_machine_lazy_diagnostic_request_parsed(session, request, cache)
}

fn run_machine_lazy_diagnostic_request_parsed(
    session: &MachineProofSession,
    request: MachineLazyDiagnosticRequest<'_>,
    mut cache: Option<&mut MachineLazyDiagnosticCache>,
) -> Result<MachineLazyDiagnosticOk, MachineLazyDiagnosticError> {
    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let entry = session
        .snapshots
        .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
        .map_err(MachineLazyDiagnosticError::SnapshotLookup)?;
    if !entry
        .materialized_view_payload
        .open_goals
        .contains(&request.goal_id)
    {
        return Err(MachineLazyDiagnosticError::GoalNotOpen {
            goal_id: request.goal_id,
        });
    }

    let deterministic_budget_hash = tactic_budget_hash(request.deterministic_budget);
    let environment_hash = machine_tactic_environment_hash(session);
    let candidate_tactic_kind = candidate_tactic_kind_for_diagnostic(request.candidate.raw);
    let candidate = parse_candidate_payload(
        request.candidate.raw,
        &session.root.universe_params,
        candidate_tactic_kind,
    )
    .map_err(MachineLazyDiagnosticError::Request)?;

    let validation = match machine_tactic_validate_machine_tactic_candidate_for_state(
        &entry.executable_state_payload,
        request.goal_id,
        candidate.clone(),
        request.deterministic_budget,
        MachineTacticProfileVersion::StructuralV2,
        STRUCTURAL_V2_REQUIRED_FEATURES,
    ) {
        Ok(validated) => LazyDiagnosticCandidateValidation::Validated(validated),
        Err(error) => {
            let candidate_payload_hash = error
                .candidate_hash
                .unwrap_or_else(|| crate::ai_search::ai_search_candidate_payload_hash(&candidate));
            LazyDiagnosticCandidateValidation::Failed {
                diagnostic: error.diagnostic,
                candidate_payload_hash,
            }
        }
    };

    let candidate_payload_hash = validation.candidate_payload_hash();
    let candidate_hash = machine_tactic_proof_candidate_identity_hash(
        session,
        request.state_fingerprint,
        request.goal_id,
        candidate_payload_hash,
        deterministic_budget_hash,
    );
    let expected_key = machine_lazy_diagnostic_cache_key(
        request.diagnostic_hash,
        request.profile,
        environment_hash,
        request.state_fingerprint,
        candidate_hash,
        deterministic_budget_hash,
    );
    let expected_metadata =
        machine_lazy_diagnostic_cache_metadata(expected_key, request.diagnostic_budget, None);

    let cache_status = match cache.as_deref_mut() {
        Some(cache) => match cache.lookup(&expected_metadata) {
            Ok(entry) => {
                return Ok(MachineLazyDiagnosticOk {
                    diagnostic_tree: entry.diagnostic_tree,
                    metadata: entry.metadata,
                    cache_status: MachineLazyDiagnosticCacheStatus::Hit,
                    counters: cache.counters(),
                });
            }
            Err(reason) => MachineLazyDiagnosticCacheStatus::Miss { reason },
        },
        None => MachineLazyDiagnosticCacheStatus::Disabled,
    };

    let diagnostic = match validation {
        LazyDiagnosticCandidateValidation::Failed { diagnostic, .. } => diagnostic,
        LazyDiagnosticCandidateValidation::Validated(validated) => {
            match machine_tactic_run_machine_tactic_with_budget(
                &entry.executable_state_payload,
                validated.tactic,
                request.deterministic_budget,
            ) {
                Ok(_) => {
                    if request.profile == DiagnosticProfile::Full {
                        if let Some(cache) = cache.as_deref_mut() {
                            cache.record_success_path_full_diagnostic_attempt();
                        }
                    }
                    return Err(MachineLazyDiagnosticError::CandidateSucceeded);
                }
                Err(error) => error.diagnostic,
            }
        }
    };

    let actual_diagnostic_hash = diagnostic
        .diagnostic_hash()
        .map_err(MachineLazyDiagnosticError::DiagnosticCanonicalization)?;
    if actual_diagnostic_hash != request.diagnostic_hash {
        return Err(MachineLazyDiagnosticError::DiagnosticHashMismatch {
            requested: request.diagnostic_hash,
            actual: actual_diagnostic_hash,
        });
    }

    let plan = plan_lazy_diagnostic_profile(
        request.profile,
        DiagnosticRequestPath::ExplicitFailureRequest,
    );
    let diagnostic_tree = machine_api_projection_diagnostic_tree(
        &diagnostic,
        MachineDiagnosticTreeAdapterContext {
            profile: plan.effective_profile,
            candidate_hash: Some(candidate_hash),
            deterministic_budget_hash: Some(deterministic_budget_hash),
            state_fingerprint: Some(request.state_fingerprint),
            diagnostic_budget: request.diagnostic_budget,
        },
    )
    .map_err(MachineLazyDiagnosticError::DiagnosticTree)?;
    let key = machine_lazy_diagnostic_cache_key(
        request.diagnostic_hash,
        plan.effective_profile,
        environment_hash,
        request.state_fingerprint,
        candidate_hash,
        deterministic_budget_hash,
    );
    let metadata = machine_lazy_diagnostic_cache_metadata(
        key,
        request.diagnostic_budget,
        diagnostic_tree.budget_report,
    );
    let entry = MachineLazyDiagnosticCacheEntry {
        metadata,
        diagnostic_tree,
    };

    let counters = match cache {
        Some(cache) => {
            if plan.effective_profile == DiagnosticProfile::Full {
                cache.record_full_diagnostic_generation();
            }
            cache.insert(entry.clone());
            cache.counters()
        }
        None => MachineLazyDiagnosticCacheCounters::default(),
    };

    Ok(MachineLazyDiagnosticOk {
        diagnostic_tree: entry.diagnostic_tree,
        metadata: entry.metadata,
        cache_status,
        counters,
    })
}

enum LazyDiagnosticCandidateValidation {
    Failed {
        diagnostic: MachineApiDiagnosticProjection,
        candidate_payload_hash: Hash,
    },
    Validated(ValidatedMachineTactic),
}

impl LazyDiagnosticCandidateValidation {
    fn candidate_payload_hash(&self) -> Hash {
        match self {
            Self::Failed {
                candidate_payload_hash,
                ..
            } => *candidate_payload_hash,
            Self::Validated(validated) => validated.candidate_hash,
        }
    }
}

pub(crate) fn machine_tactic_proof_candidate_identity_hash(
    session: &MachineProofSession,
    previous_state_fingerprint: Hash,
    goal_id: npa_tactic::GoalId,
    candidate_payload_hash: Hash,
    deterministic_budget_hash: Hash,
) -> Hash {
    let environment_hash = machine_tactic_environment_hash(session);
    let import_closure_hash =
        proof_candidate_import_closure_hash(&session.import_certificate_context);
    let axiom_policy_hash = proof_candidate_axiom_policy_hash(&session.options.allow_axioms);
    let feature_profile_hash = proof_candidate_feature_profile_hash(
        session.options.kernel_check_profile,
        session.initial_snapshot.tactic_options_fingerprint,
    );
    let statement_hash = session.root.theorem_type_core_hash;
    let identity = ProofCandidateIdentity {
        task_kind: ProofCandidateKind::MachineTactic,
        source_kind: ProofCandidateSourceKind::Payload,
        canonical_source_or_payload_hash: candidate_payload_hash,
        environment_hash,
        import_closure_hash,
        axiom_policy_hash,
        feature_profile_hash,
        statement_hash,
        goal_fingerprint: proof_candidate_goal_fingerprint(previous_state_fingerprint, goal_id),
        candidate_payload_hash,
        deterministic_budget_hash,
    };
    proof_candidate_identity_hash(&identity)
}

pub fn machine_tactic_environment_hash(session: &MachineProofSession) -> Hash {
    let import_closure_hash =
        proof_candidate_import_closure_hash(&session.import_certificate_context);
    let axiom_policy_hash = proof_candidate_axiom_policy_hash(&session.options.allow_axioms);
    let feature_profile_hash = proof_candidate_feature_profile_hash(
        session.options.kernel_check_profile,
        session.initial_snapshot.tactic_options_fingerprint,
    );
    let statement_hash = session.root.theorem_type_core_hash;
    proof_candidate_environment_hash(
        import_closure_hash,
        axiom_policy_hash,
        feature_profile_hash,
        statement_hash,
    )
}

fn machine_lazy_diagnostic_cache_key(
    diagnostic_hash: Hash,
    profile: DiagnosticProfile,
    environment_hash: Hash,
    state_fingerprint: Hash,
    candidate_hash: Hash,
    deterministic_budget_hash: Hash,
) -> MachineLazyDiagnosticCacheKey {
    MachineLazyDiagnosticCacheKey {
        diagnostic_hash,
        profile,
        environment_hash,
        state_fingerprint,
        candidate_hash,
        deterministic_budget_hash,
    }
}

fn machine_lazy_diagnostic_cache_metadata(
    key: MachineLazyDiagnosticCacheKey,
    diagnostic_budget: DiagnosticBudget,
    truncation_report: Option<DiagnosticBudgetReport>,
) -> MachineLazyDiagnosticCacheMetadata {
    MachineLazyDiagnosticCacheMetadata {
        producer_version: LAZY_DIAGNOSTIC_CACHE_PRODUCER_VERSION.to_owned(),
        key,
        diagnostic_budget,
        diagnostic_budget_hash: machine_lazy_diagnostic_budget_hash(diagnostic_budget),
        truncation_report,
    }
}

pub fn machine_lazy_diagnostic_budget_hash(budget: DiagnosticBudget) -> Hash {
    repair_hash_with_domain(
        LAZY_DIAGNOSTIC_BUDGET_HASH_DOMAIN,
        &machine_lazy_diagnostic_budget_canonical_bytes(budget),
    )
}

pub fn machine_lazy_diagnostic_budget_canonical_bytes(budget: DiagnosticBudget) -> Vec<u8> {
    let mut out = Vec::new();
    repair_encode_string(&mut out, "npa.machine-api.lazy-diagnostic-budget.v1");
    repair_encode_u64(&mut out, budget.max_graph_nodes);
    repair_encode_u64(&mut out, budget.max_expression_paths);
    repair_encode_u64(&mut out, budget.max_rewrite_site_scans);
    repair_encode_u64(&mut out, budget.max_pretty_term_bytes);
    repair_encode_u64(&mut out, budget.max_repair_proposals);
    repair_encode_u64(&mut out, budget.max_diagnostic_steps);
    out
}

pub fn parse_repair_operator_json(source: &str) -> Result<RepairOperator, MachineApiRequestError> {
    let doc = JsonDocument::parse(source).map_err(|err| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            JsonPath::root(),
            MachineApiRequestErrorReason::JsonParse {
                offset: err.offset,
                kind: err.kind,
            },
        )
    })?;
    parse_repair_operator_value(doc.root(), &JsonPath::root())
}

pub(crate) fn parse_repair_operator_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<RepairOperator, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            REPAIR_OPERATOR_TOP_FIELDS,
        ),
        path,
    )?;
    let schema = required_schema_string(&object, "schema");
    if schema != REPAIR_OPERATOR_SCHEMA {
        return Err(invalid_string_literal(
            "schema",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("schema"),
        ));
    }
    let kind = RepairOperatorKind::parse(required_schema_string(&object, "operator")).ok_or_else(
        || {
            invalid_string_literal(
                "operator",
                None,
                MachineApiErrorKind::InvalidCandidate,
                &path.field("operator"),
            )
        },
    )?;
    let payload = required_object_field(&object, "payload");
    let payload_path = path.field("payload");

    match kind {
        RepairOperatorKind::ReverseRewrite => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_GOAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::ReverseRewrite {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
            })
        }
        RepairOperatorKind::SelectRewriteOccurrence => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_PATH_FIELDS, &payload_path)?;
            Ok(RepairOperator::SelectRewriteOccurrence {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                path: parse_expr_path_field(&payload, "path", &payload_path.field("path"))?,
            })
        }
        RepairOperatorKind::InstantiateArgument => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_ARGUMENT_FIELDS, &payload_path)?;
            Ok(RepairOperator::InstantiateArgument {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                binder: required_u64(&payload, "binder")
                    .try_into()
                    .expect("schema checked binder <= u32::MAX"),
                term: parse_checked_term_payload_field(
                    &payload,
                    "term",
                    &payload_path.field("term"),
                )?,
            })
        }
        RepairOperatorKind::InstantiateUniverse => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_UNIVERSE_FIELDS, &payload_path)?;
            let param = required_schema_string(&payload, "param");
            if !is_machine_universe_param_name(param) {
                return Err(invalid_string_literal(
                    "param",
                    None,
                    MachineApiErrorKind::InvalidCandidate,
                    &payload_path.field("param"),
                ));
            }
            let level = parse_level_wire(required_schema_string(&payload, "level"), &[], true)
                .map_err(|_| {
                    invalid_string_literal(
                        "level",
                        None,
                        MachineApiErrorKind::InvalidCandidate,
                        &payload_path.field("level"),
                    )
                })?;
            Ok(RepairOperator::InstantiateUniverse {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                param: param.to_owned(),
                level,
            })
        }
        RepairOperatorKind::IntroduceBinder => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_GOAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::IntroduceBinder {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
            })
        }
        RepairOperatorKind::SpecializeHypothesis => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_SPECIALIZE_FIELDS, &payload_path)?;
            Ok(RepairOperator::SpecializeHypothesis {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                local: parse_local_ref_field(&payload, "local", &payload_path.field("local"))?,
                args: parse_checked_term_payload_array(
                    required_array_field(&payload, "args"),
                    &payload_path.field("args"),
                )?,
            })
        }
        RepairOperatorKind::Unfold => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_GLOBAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::Unfold {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                constant: parse_global_ref_field(
                    &payload,
                    "constant",
                    &payload_path.field("constant"),
                )?,
            })
        }
        RepairOperatorKind::Fold => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_GLOBAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::Fold {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                constant: parse_global_ref_field(
                    &payload,
                    "constant",
                    &payload_path.field("constant"),
                )?,
            })
        }
        RepairOperatorKind::InsertEqTransport => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_GOAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::InsertEqTransport {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
            })
        }
        RepairOperatorKind::Generalize => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_TERM_FIELDS, &payload_path)?;
            Ok(RepairOperator::Generalize {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                term: parse_checked_term_payload_field(
                    &payload,
                    "term",
                    &payload_path.field("term"),
                )?,
            })
        }
        RepairOperatorKind::Revert => {
            let payload =
                validate_repair_payload(payload, REPAIR_OPERATOR_LOCAL_FIELDS, &payload_path)?;
            Ok(RepairOperator::Revert {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                local: parse_local_ref_field(&payload, "local", &payload_path.field("local"))?,
            })
        }
        RepairOperatorKind::ChangeGoal => {
            let payload = validate_repair_payload(
                payload,
                REPAIR_OPERATOR_CHANGE_GOAL_FIELDS,
                &payload_path,
            )?;
            Ok(RepairOperator::ChangeGoal {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                target: parse_checked_term_payload_field(
                    &payload,
                    "target",
                    &payload_path.field("target"),
                )?,
            })
        }
        RepairOperatorKind::ReduceSimpSet => {
            let payload = validate_repair_payload(
                payload,
                REPAIR_OPERATOR_REDUCE_SIMP_SET_FIELDS,
                &payload_path,
            )?;
            Ok(RepairOperator::ReduceSimpSet {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                remove: parse_global_ref_array(
                    required_array_field(&payload, "remove"),
                    &payload_path.field("remove"),
                )?,
            })
        }
        RepairOperatorKind::SwitchStrategy => {
            let payload = validate_repair_payload(
                payload,
                REPAIR_OPERATOR_SWITCH_STRATEGY_FIELDS,
                &payload_path,
            )?;
            let profile = RepairStrategyProfile::parse(required_schema_string(&payload, "profile"))
                .ok_or_else(|| {
                    invalid_string_literal(
                        "profile",
                        None,
                        MachineApiErrorKind::InvalidCandidate,
                        &payload_path.field("profile"),
                    )
                })?;
            Ok(RepairOperator::SwitchStrategy {
                goal_id: parse_optional_goal_id_field(&payload, &payload_path.field("goal_id"))?,
                profile,
            })
        }
    }
}

pub fn parse_machine_tactic_run_request<'src>(
    source: &'src str,
) -> Result<MachineTacticRunRequest<'src>, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTacticRunRequest)?;
    let members = validate_run_top_level(doc.root())?;

    let session_id = SessionId::parse(required_string_member(
        members,
        "session_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("session_id"),
    )?)
    .map_err(|_| grammar_error("session_id", MachineApiErrorKind::InvalidTacticRunRequest))?;
    let snapshot_id = SnapshotId::parse(required_string_member(
        members,
        "snapshot_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("snapshot_id"),
    )?)
    .map_err(|_| grammar_error("snapshot_id", MachineApiErrorKind::InvalidTacticRunRequest))?;
    let state_fingerprint = HashString::parse(required_string_member(
        members,
        "state_fingerprint",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("state_fingerprint"),
    )?)
    .map_err(|_| {
        grammar_error(
            "state_fingerprint",
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
    })?
    .digest();
    let goal_id = parse_goal_id_wire(required_string_member(
        members,
        "goal_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("goal_id"),
    )?)
    .map_err(|_| grammar_error("goal_id", MachineApiErrorKind::InvalidTacticRunRequest))?;

    let candidate_value = required_value_member(
        members,
        "candidate",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("candidate"),
    )?;
    if candidate_value.kind() == JsonValueKind::Null {
        return Err(null_field(
            "candidate",
            MachineApiErrorKind::InvalidTacticRunRequest,
            &JsonPath::root().field("candidate"),
        ));
    }
    if candidate_value.kind() != JsonValueKind::Object {
        return Err(type_mismatch(
            "candidate",
            JsonFieldType::Object,
            candidate_value,
            MachineApiErrorKind::InvalidTacticRunRequest,
            &JsonPath::root().field("candidate"),
        ));
    }
    let candidate = delayed_json_payload(candidate_value);

    let budget_value = required_value_member(
        members,
        "deterministic_budget",
        MachineApiErrorKind::InvalidBudget,
        &JsonPath::root().field("deterministic_budget"),
    )?;
    let deterministic_budget = parse_deterministic_budget(
        budget_value,
        &JsonPath::root().field("deterministic_budget"),
    )?;

    let scheduler_limits = match member_value(members, "scheduler_limits") {
        Some(value) => {
            parse_run_scheduler_limits(value, &JsonPath::root().field("scheduler_limits"))?
        }
        None => MachineRunSchedulerLimits::default(),
    };

    Ok(MachineTacticRunRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        candidate,
        deterministic_budget,
        scheduler_limits,
    })
}

pub fn parse_machine_tactic_batch_request<'src>(
    source: &'src str,
) -> Result<MachineTacticBatchRequest<'src>, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidBatchPolicy)?;
    let members = validate_batch_top_level(doc.root())?;

    let session_id = SessionId::parse(required_string_member(
        members,
        "session_id",
        MachineApiErrorKind::InvalidBatchPolicy,
        &JsonPath::root().field("session_id"),
    )?)
    .map_err(|_| grammar_error("session_id", MachineApiErrorKind::InvalidBatchPolicy))?;
    let snapshot_id = SnapshotId::parse(required_string_member(
        members,
        "snapshot_id",
        MachineApiErrorKind::InvalidBatchPolicy,
        &JsonPath::root().field("snapshot_id"),
    )?)
    .map_err(|_| grammar_error("snapshot_id", MachineApiErrorKind::InvalidBatchPolicy))?;
    let state_fingerprint = HashString::parse(required_string_member(
        members,
        "state_fingerprint",
        MachineApiErrorKind::InvalidBatchPolicy,
        &JsonPath::root().field("state_fingerprint"),
    )?)
    .map_err(|_| grammar_error("state_fingerprint", MachineApiErrorKind::InvalidBatchPolicy))?
    .digest();
    let goal_id = parse_goal_id_wire(required_string_member(
        members,
        "goal_id",
        MachineApiErrorKind::InvalidBatchPolicy,
        &JsonPath::root().field("goal_id"),
    )?)
    .map_err(|_| grammar_error("goal_id", MachineApiErrorKind::InvalidBatchPolicy))?;

    let candidates = parse_batch_candidates(
        required_value_member(
            members,
            "candidates",
            MachineApiErrorKind::InvalidBatchPolicy,
            &JsonPath::root().field("candidates"),
        )?,
        &JsonPath::root().field("candidates"),
    )?;

    let budget_value = required_value_member(
        members,
        "deterministic_budget",
        MachineApiErrorKind::InvalidBudget,
        &JsonPath::root().field("deterministic_budget"),
    )?;
    let deterministic_budget = parse_deterministic_budget(
        budget_value,
        &JsonPath::root().field("deterministic_budget"),
    )?;

    let batch_policy = parse_batch_policy(
        required_value_member(
            members,
            "batch_policy",
            MachineApiErrorKind::InvalidBatchPolicy,
            &JsonPath::root().field("batch_policy"),
        )?,
        &JsonPath::root().field("batch_policy"),
    )?;

    let scheduler_limits = match member_value(members, "scheduler_limits") {
        Some(value) => {
            parse_batch_scheduler_limits(value, &JsonPath::root().field("scheduler_limits"))?
        }
        None => MachineBatchSchedulerLimits::default(),
    };

    Ok(MachineTacticBatchRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        candidates,
        deterministic_budget,
        batch_policy,
        scheduler_limits,
    })
}

pub fn parse_machine_lazy_diagnostic_request<'src>(
    source: &'src str,
) -> Result<MachineLazyDiagnosticRequest<'src>, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTacticRunRequest)?;
    let object = validate_json_object(
        doc.root(),
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTacticRunRequest,
            LAZY_DIAGNOSTIC_REQUEST_FIELDS,
        ),
        &JsonPath::root(),
    )?;

    let session_id = SessionId::parse(required_string_member(
        object.members(),
        "session_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("session_id"),
    )?)
    .map_err(|_| grammar_error("session_id", MachineApiErrorKind::InvalidTacticRunRequest))?;
    let snapshot_id = SnapshotId::parse(required_string_member(
        object.members(),
        "snapshot_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("snapshot_id"),
    )?)
    .map_err(|_| grammar_error("snapshot_id", MachineApiErrorKind::InvalidTacticRunRequest))?;
    let state_fingerprint = HashString::parse(required_string_member(
        object.members(),
        "state_fingerprint",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("state_fingerprint"),
    )?)
    .map_err(|_| {
        grammar_error(
            "state_fingerprint",
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
    })?
    .digest();
    let goal_id = parse_goal_id_wire(required_string_member(
        object.members(),
        "goal_id",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("goal_id"),
    )?)
    .map_err(|_| grammar_error("goal_id", MachineApiErrorKind::InvalidTacticRunRequest))?;
    let candidate_value = required_value_member(
        object.members(),
        "candidate",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("candidate"),
    )?;
    let candidate = delayed_json_payload(candidate_value);
    let deterministic_budget = parse_deterministic_budget(
        required_value_member(
            object.members(),
            "deterministic_budget",
            MachineApiErrorKind::InvalidBudget,
            &JsonPath::root().field("deterministic_budget"),
        )?,
        &JsonPath::root().field("deterministic_budget"),
    )?;
    let diagnostic_hash = HashString::parse(required_string_member(
        object.members(),
        "diagnostic_hash",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("diagnostic_hash"),
    )?)
    .map_err(|_| {
        grammar_error(
            "diagnostic_hash",
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
    })?
    .digest();
    let profile = parse_lazy_diagnostic_profile(required_string_member(
        object.members(),
        "profile",
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root().field("profile"),
    )?)?;
    let diagnostic_budget = parse_diagnostic_budget(
        required_value_member(
            object.members(),
            "diagnostic_budget",
            MachineApiErrorKind::InvalidBudget,
            &JsonPath::root().field("diagnostic_budget"),
        )?,
        &JsonPath::root().field("diagnostic_budget"),
    )?;

    Ok(MachineLazyDiagnosticRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        candidate,
        deterministic_budget,
        diagnostic_hash,
        profile,
        diagnostic_budget,
    })
}

fn run_machine_tactic_request_parsed(
    session: &mut MachineProofSession,
    request: MachineTacticRunRequest<'_>,
) -> Result<MachineTacticRunResponse, Box<MachineTacticRunError>> {
    if session.snapshots.session_id() != &session.session_id {
        return Err(plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SnapshotLookup,
            "session snapshot store belongs to a different session",
            RunErrorCorrelation::default(),
        ));
    }

    let scheduler_observation = RunSchedulerObservationContext::start();
    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let input_state = {
        let entry = session
            .snapshots
            .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
            .map_err(snapshot_lookup_error)?;
        if !entry
            .materialized_view_payload
            .open_goals
            .contains(&request.goal_id)
        {
            return Err(plain_error_with_goal(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                format!("goal {} is not open", request.goal_id.0),
                request.goal_id,
                RunErrorCorrelation::default(),
            ));
        }
        entry.executable_state_payload.clone()
    };

    let deterministic_budget_hash = tactic_budget_hash(request.deterministic_budget);
    if let Some(kind) = scheduler_observation.observe(request.scheduler_limits) {
        return Ok(scheduler_stop(
            request.state_fingerprint,
            deterministic_budget_hash,
            kind,
        ));
    }

    let candidate_tactic_kind = candidate_tactic_kind_for_diagnostic(request.candidate.raw);
    let candidate = parse_candidate_payload(
        request.candidate.raw,
        &session.root.universe_params,
        candidate_tactic_kind,
    )
    .map_err(|error| {
        candidate_request_error(
            error,
            request.state_fingerprint,
            deterministic_budget_hash,
            request.goal_id,
            candidate_tactic_kind,
        )
    })?;
    if let Some(kind) = scheduler_observation.observe(request.scheduler_limits) {
        return Ok(scheduler_stop(
            request.state_fingerprint,
            deterministic_budget_hash,
            kind,
        ));
    }

    let validated = machine_tactic_validate_machine_tactic_candidate_for_state(
        &input_state,
        request.goal_id,
        candidate,
        request.deterministic_budget,
        MachineTacticProfileVersion::StructuralV2,
        STRUCTURAL_V2_REQUIRED_FEATURES,
    )
    .map_err(|error| {
        let candidate_hash = error.candidate_hash.map(|candidate_payload_hash| {
            machine_tactic_proof_candidate_identity_hash(
                session,
                request.state_fingerprint,
                request.goal_id,
                candidate_payload_hash,
                deterministic_budget_hash,
            )
        });
        adapter_error(
            error,
            request.state_fingerprint,
            candidate_hash,
            Some(deterministic_budget_hash),
        )
    })?;
    if let Some(kind) = scheduler_observation.observe(request.scheduler_limits) {
        return Ok(scheduler_stop(
            request.state_fingerprint,
            deterministic_budget_hash,
            kind,
        ));
    }
    let tactic_kind = validated.tactic_kind;
    let candidate_payload_hash = validated.candidate_hash;
    let candidate_hash = machine_tactic_proof_candidate_identity_hash(
        session,
        request.state_fingerprint,
        request.goal_id,
        candidate_payload_hash,
        deterministic_budget_hash,
    );
    let run = machine_tactic_run_machine_tactic_with_budget(
        &input_state,
        validated.tactic,
        request.deterministic_budget,
    )
    .map_err(|error| adapter_error(error, request.state_fingerprint, Some(candidate_hash), None))?;
    if let Some(kind) = scheduler_observation.observe(request.scheduler_limits) {
        return Ok(scheduler_stop(
            request.state_fingerprint,
            deterministic_budget_hash,
            kind,
        ));
    }

    let next_snapshot = match session.snapshots.insert_state(&context, run.state) {
        Ok(snapshot) => snapshot,
        Err(MachineSnapshotStoreError::SnapshotQuotaExceeded { .. }) => {
            return Ok(scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                MachineSchedulerArtifactKind::ResourceLimitExceeded,
            ));
        }
        Err(error) => {
            return Err(next_snapshot_store_error(
                error,
                request.state_fingerprint,
                candidate_hash,
                deterministic_budget_hash,
                request.goal_id,
                tactic_kind,
            ));
        }
    };
    let new_goals =
        new_goals_in_next_snapshot_order(&next_snapshot.open_goals, &run.delta.added_goals)
            .ok_or_else(|| {
                next_snapshot_invariant_error(
                    "proof delta added_goals are not present in the next snapshot",
                    request.state_fingerprint,
                    candidate_hash,
                    deterministic_budget_hash,
                    request.goal_id,
                    tactic_kind,
                )
            })?;
    let kind = if new_goals.is_empty() {
        MachineTacticRunResultKind::Closed
    } else {
        MachineTacticRunResultKind::Expanded
    };

    Ok(MachineApiResponseEnvelope::Ok(
        crate::MachineApiOkResponse {
            status: MachineApiResponseStatus::Success,
            endpoint_fields: MachineTacticRunSuccessFields {
                result: MachineTacticRunSuccessResult {
                    kind,
                    previous_state_fingerprint: request.state_fingerprint,
                    candidate_hash,
                    deterministic_budget_hash: run.deterministic_budget_hash,
                    next_snapshot_id: next_snapshot.snapshot_id,
                    next_state_fingerprint: next_snapshot.state_fingerprint,
                    closed_goals: vec![run.delta.assigned_goal],
                    new_goals,
                    delta: MachineTacticRunDeltaSummary {
                        proof_delta_hash: run.proof_delta_hash,
                        assigned_goal: run.delta.assigned_goal,
                        assigned_proof_expr_hash: run.delta.proof_expr_hash,
                    },
                },
            },
        },
    ))
}

fn run_machine_tactic_batch_request_parsed(
    session: &mut MachineProofSession,
    request: MachineTacticBatchRequest<'_>,
) -> Result<MachineTacticBatchResponse, Box<MachineTacticBatchError>> {
    if session.snapshots.session_id() != &session.session_id {
        return Err(batch_plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SnapshotLookup,
            "session snapshot store belongs to a different session",
            None,
        ));
    }

    let mut scheduler_observation = BatchSchedulerObservationContext::start();
    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let input_state = {
        let entry = session
            .snapshots
            .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
            .map_err(batch_snapshot_lookup_error)?;
        if !entry
            .materialized_view_payload
            .open_goals
            .contains(&request.goal_id)
        {
            return Err(batch_plain_error(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                format!("goal {} is not open", request.goal_id.0),
                Some(request.goal_id),
            ));
        }
        entry.executable_state_payload.clone()
    };

    let deterministic_budget_hash = tactic_budget_hash(request.deterministic_budget);
    let candidate_count = request.candidates.len();
    let mut results = Vec::new();
    let mut success_count = 0u32;
    let mut failure_count = 0u32;
    let mut evaluated_count = 0u32;

    if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
        return Ok(batch_scheduler_stop(
            request.state_fingerprint,
            deterministic_budget_hash,
            results,
            success_count,
            failure_count,
            stop,
        ));
    }

    for (index, item) in request.candidates.into_iter().enumerate() {
        if batch_policy_stop(
            evaluated_count,
            success_count,
            failure_count,
            candidate_count,
            request.batch_policy,
        ) {
            break;
        }

        scheduler_observation.begin_candidate();
        if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
            return Ok(batch_scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
                stop,
            ));
        }

        let candidate_id = item.candidate_id;
        let candidate_tactic_kind = candidate_tactic_kind_for_diagnostic(item.candidate.raw);
        let candidate_path = JsonPath::root()
            .field("candidates")
            .index(index)
            .field("candidate");
        let candidate = match parse_candidate_payload_at(
            item.candidate.raw,
            &session.root.universe_params,
            candidate_tactic_kind,
            &candidate_path,
        ) {
            Ok(candidate) => candidate,
            Err(error) => {
                results.push(batch_candidate_request_error_item(
                    candidate_id,
                    error,
                    request.goal_id,
                    candidate_tactic_kind,
                ));
                evaluated_count += 1;
                failure_count += 1;
                if batch_policy_stop(
                    evaluated_count,
                    success_count,
                    failure_count,
                    candidate_count,
                    request.batch_policy,
                ) {
                    break;
                }
                if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
                    return Ok(batch_scheduler_stop(
                        request.state_fingerprint,
                        deterministic_budget_hash,
                        results,
                        success_count,
                        failure_count,
                        stop,
                    ));
                }
                continue;
            }
        };

        if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
            return Ok(batch_scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
                stop,
            ));
        }

        let validated = match machine_tactic_validate_machine_tactic_candidate_for_state(
            &input_state,
            request.goal_id,
            candidate,
            request.deterministic_budget,
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        ) {
            Ok(validated) => validated,
            Err(error) => {
                let candidate_hash = error.candidate_hash.map(|candidate_payload_hash| {
                    machine_tactic_proof_candidate_identity_hash(
                        session,
                        request.state_fingerprint,
                        request.goal_id,
                        candidate_payload_hash,
                        deterministic_budget_hash,
                    )
                });
                results.push(batch_adapter_error_item(
                    candidate_id,
                    error,
                    candidate_hash,
                ));
                evaluated_count += 1;
                failure_count += 1;
                if batch_policy_stop(
                    evaluated_count,
                    success_count,
                    failure_count,
                    candidate_count,
                    request.batch_policy,
                ) {
                    break;
                }
                if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
                    return Ok(batch_scheduler_stop(
                        request.state_fingerprint,
                        deterministic_budget_hash,
                        results,
                        success_count,
                        failure_count,
                        stop,
                    ));
                }
                continue;
            }
        };

        if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
            return Ok(batch_scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
                stop,
            ));
        }

        let tactic_kind = validated.tactic_kind;
        let candidate_payload_hash = validated.candidate_hash;
        let candidate_hash = machine_tactic_proof_candidate_identity_hash(
            session,
            request.state_fingerprint,
            request.goal_id,
            candidate_payload_hash,
            deterministic_budget_hash,
        );
        let run = match machine_tactic_run_machine_tactic_with_budget(
            &input_state,
            validated.tactic,
            request.deterministic_budget,
        ) {
            Ok(run) => run,
            Err(error) => {
                results.push(batch_adapter_error_item(
                    candidate_id,
                    error,
                    Some(candidate_hash),
                ));
                evaluated_count += 1;
                failure_count += 1;
                if batch_policy_stop(
                    evaluated_count,
                    success_count,
                    failure_count,
                    candidate_count,
                    request.batch_policy,
                ) {
                    break;
                }
                if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
                    return Ok(batch_scheduler_stop(
                        request.state_fingerprint,
                        deterministic_budget_hash,
                        results,
                        success_count,
                        failure_count,
                        stop,
                    ));
                }
                continue;
            }
        };

        if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
            return Ok(batch_scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
                stop,
            ));
        }

        match session.snapshots.insert_state(&context, run.state) {
            Ok(next_snapshot) => {
                results.push(MachineTacticBatchItemResponse::Success {
                    candidate_id,
                    candidate_hash,
                    next_snapshot_id: next_snapshot.snapshot_id,
                    next_state_fingerprint: next_snapshot.state_fingerprint,
                    proof_delta_hash: run.proof_delta_hash,
                });
                evaluated_count += 1;
                success_count += 1;
            }
            Err(MachineSnapshotStoreError::SnapshotQuotaExceeded { .. }) => {
                return Ok(batch_scheduler_stop(
                    request.state_fingerprint,
                    deterministic_budget_hash,
                    results,
                    success_count,
                    failure_count,
                    BatchSchedulerStop {
                        kind: MachineSchedulerArtifactKind::ResourceLimitExceeded,
                        scope: MachineSchedulerArtifactScope::Batch,
                    },
                ));
            }
            Err(error) => {
                results.push(batch_next_snapshot_error_item(
                    candidate_id,
                    error,
                    request.goal_id,
                    tactic_kind,
                    candidate_hash,
                ));
                evaluated_count += 1;
                failure_count += 1;
            }
        }

        if batch_policy_stop(
            evaluated_count,
            success_count,
            failure_count,
            candidate_count,
            request.batch_policy,
        ) {
            break;
        }
        if let Some(stop) = scheduler_observation.observe(request.scheduler_limits) {
            return Ok(batch_scheduler_stop(
                request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
                stop,
            ));
        }
    }

    Ok(MachineApiResponseEnvelope::Ok(
        crate::MachineApiOkResponse {
            status: MachineApiResponseStatus::Ok,
            endpoint_fields: MachineTacticBatchOkFields {
                previous_state_fingerprint: request.state_fingerprint,
                deterministic_budget_hash,
                results,
                success_count,
                failure_count,
            },
        },
    ))
}

fn parse_candidate_payload(
    raw: &str,
    universe_params: &[String],
    tactic_kind: Option<MachineApiTacticKind>,
) -> Result<MachineTacticCandidate, MachineApiRequestError> {
    parse_candidate_payload_at(
        raw,
        universe_params,
        tactic_kind,
        &JsonPath::root().field("candidate"),
    )
}

pub(crate) fn parse_candidate_payload_at(
    raw: &str,
    universe_params: &[String],
    tactic_kind: Option<MachineApiTacticKind>,
    path: &JsonPath,
) -> Result<MachineTacticCandidate, MachineApiRequestError> {
    parse_candidate_payload_at_with_level_policy(raw, universe_params, false, tactic_kind, path)
}

pub(crate) fn parse_candidate_wire_shape_at(
    raw: &str,
    tactic_kind: Option<MachineApiTacticKind>,
    path: &JsonPath,
) -> Result<MachineTacticCandidate, MachineApiRequestError> {
    parse_candidate_payload_at_with_level_policy(raw, &[], true, tactic_kind, path)
}

fn parse_candidate_payload_at_with_level_policy(
    raw: &str,
    universe_params: &[String],
    allow_unbound_level_params: bool,
    tactic_kind: Option<MachineApiTacticKind>,
    path: &JsonPath,
) -> Result<MachineTacticCandidate, MachineApiRequestError> {
    let doc = JsonDocument::parse(raw).map_err(|err| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::JsonParse {
                offset: err.offset,
                kind: err.kind,
            },
        )
    })?;
    parse_candidate_value(
        doc.root(),
        universe_params,
        allow_unbound_level_params,
        tactic_kind,
        path,
    )
}

fn parse_candidate_value(
    value: &JsonValue<'_>,
    universe_params: &[String],
    allow_unbound_level_params: bool,
    tactic_kind: Option<MachineApiTacticKind>,
    path: &JsonPath,
) -> Result<MachineTacticCandidate, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    let kind_value = member_value(members, "kind").ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.field("kind"),
            MachineApiRequestErrorReason::MissingField { field: "kind" },
        )
    })?;
    let kind = string_value(
        kind_value,
        "kind",
        MachineApiErrorKind::InvalidCandidate,
        &path.field("kind"),
    )?;

    match kind {
        "exact" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, EXACT_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Exact {
                term: parse_raw_machine_term(
                    required_object_field(&object, "term"),
                    &path.field("term"),
                )?,
            })
        }
        "intro" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, INTRO_FIELDS),
                path,
            )?;
            let name = required_schema_string(&object, "name");
            validate_machine_local_name(name, "name", &path.field("name"))?;
            Ok(MachineTacticCandidate::Intro {
                name: name.to_owned(),
            })
        }
        "apply" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, APPLY_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Apply {
                head: parse_tactic_head(
                    required_object_field(&object, "head"),
                    &path.field("head"),
                )?,
                universe_args: parse_level_array(
                    required_array_field(&object, "universe_args"),
                    universe_params,
                    allow_unbound_level_params,
                    &path.field("universe_args"),
                )?,
                args: parse_apply_arg_array(
                    required_array_field(&object, "args"),
                    &path.field("args"),
                )?,
            })
        }
        "rw" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, REWRITE_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Rewrite {
                rule: parse_rewrite_rule(
                    required_object_field(&object, "rule"),
                    universe_params,
                    allow_unbound_level_params,
                    &path.field("rule"),
                )?,
                direction: parse_rewrite_direction(
                    required_schema_string(&object, "direction"),
                    "direction",
                    &path.field("direction"),
                )?,
                site: parse_rewrite_site(
                    required_schema_string(&object, "site"),
                    "site",
                    &path.field("site"),
                )?,
            })
        }
        "simp-lite" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, SIMP_LITE_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::SimpLite {
                rules: parse_simp_rule_array(
                    required_array_field(&object, "rules"),
                    &path.field("rules"),
                )?,
            })
        }
        "induction-nat" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, INDUCTION_NAT_FIELDS),
                path,
            )?;
            let local_name = required_schema_string(&object, "local_name");
            validate_machine_local_name(local_name, "local_name", &path.field("local_name"))?;
            Ok(MachineTacticCandidate::InductionNat {
                local_name: local_name.to_owned(),
            })
        }
        "constructor" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CONSTRUCTOR_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Constructor(ConstructorPayload {
                selection: parse_constructor_selection(
                    required_object_field(&object, "selection"),
                    &path.field("selection"),
                )?,
                max_new_goals: optional_u64_field(&object, "max_new_goals"),
            }))
        }
        "cases" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CASES_FIELDS),
                path,
            )?;
            let major_local = required_schema_string(&object, "major_local");
            validate_machine_local_name(major_local, "major_local", &path.field("major_local"))?;
            Ok(MachineTacticCandidate::Cases(CasesPayload {
                major_local: major_local.to_owned(),
                motive: parse_optional_raw_machine_term_field(
                    &object,
                    "motive",
                    &path.field("motive"),
                )?,
                branch_names: parse_local_name_array(
                    required_array_field(&object, "branch_names"),
                    "branch_names",
                    &path.field("branch_names"),
                )?,
                max_new_goals: optional_u64_field(&object, "max_new_goals"),
            }))
        }
        "general-induction" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    GENERAL_INDUCTION_FIELDS,
                ),
                path,
            )?;
            let major_local = required_schema_string(&object, "major_local");
            validate_machine_local_name(major_local, "major_local", &path.field("major_local"))?;
            Ok(MachineTacticCandidate::GeneralInduction(
                GeneralInductionPayload {
                    major_local: major_local.to_owned(),
                    recursor: parse_tactic_head(
                        required_object_field(&object, "recursor"),
                        &path.field("recursor"),
                    )?,
                    motive: parse_optional_raw_machine_term_field(
                        &object,
                        "motive",
                        &path.field("motive"),
                    )?,
                    generalized_locals: parse_local_name_array(
                        required_array_field(&object, "generalized_locals"),
                        "generalized_locals",
                        &path.field("generalized_locals"),
                    )?,
                    branch_names: parse_local_name_array(
                        required_array_field(&object, "branch_names"),
                        "branch_names",
                        &path.field("branch_names"),
                    )?,
                    max_new_goals: required_u64(&object, "max_new_goals"),
                },
            ))
        }
        "refine" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, REFINE_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Refine(RefinePayload {
                term: parse_raw_machine_term(
                    required_object_field(&object, "term"),
                    &path.field("term"),
                )?,
                max_holes: optional_u64_field(&object, "max_holes"),
            }))
        }
        "have" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, HAVE_FIELDS),
                path,
            )?;
            let name = required_schema_string(&object, "name");
            validate_machine_local_name(name, "name", &path.field("name"))?;
            Ok(MachineTacticCandidate::Have(HavePayload {
                name: name.to_owned(),
                ty: parse_raw_machine_term(
                    required_object_field(&object, "type"),
                    &path.field("type"),
                )?,
                proof: parse_local_lemma_proof(
                    required_object_field(&object, "proof"),
                    &path.field("proof"),
                )?,
                insertion: parse_local_lemma_insertion_policy(
                    required_schema_string(&object, "insertion"),
                    &path.field("insertion"),
                )?,
            }))
        }
        "suffices" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, SUFFICES_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Suffices(SufficesPayload {
                target: parse_raw_machine_term(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                proof: parse_local_lemma_proof(
                    required_object_field(&object, "proof"),
                    &path.field("proof"),
                )?,
                continuation: parse_suffices_continuation_policy(
                    required_schema_string(&object, "continuation"),
                    &path.field("continuation"),
                )?,
            }))
        }
        "specialize" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, SPECIALIZE_FIELDS),
                path,
            )?;
            let local_name = required_schema_string(&object, "local_name");
            validate_machine_local_name(local_name, "local_name", &path.field("local_name"))?;
            Ok(MachineTacticCandidate::Specialize(SpecializePayload {
                local_name: local_name.to_owned(),
                universe_args: parse_level_array(
                    required_array_field(&object, "universe_args"),
                    universe_params,
                    allow_unbound_level_params,
                    &path.field("universe_args"),
                )?,
                args: parse_apply_arg_array(
                    required_array_field(&object, "args"),
                    &path.field("args"),
                )?,
                result_name: parse_optional_local_name_field(
                    &object,
                    "result_name",
                    &path.field("result_name"),
                )?,
                result_policy: parse_specialize_result_policy(
                    required_schema_string(&object, "result_policy"),
                    &path.field("result_policy"),
                )?,
            }))
        }
        "revert" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, REVERT_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Revert(RevertPayload {
                locals: parse_local_name_array(
                    required_array_field(&object, "locals"),
                    "locals",
                    &path.field("locals"),
                )?,
                dependency_policy: parse_revert_dependency_policy(
                    required_schema_string(&object, "dependency_policy"),
                    &path.field("dependency_policy"),
                )?,
            }))
        }
        "generalize" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, GENERALIZE_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Generalize(GeneralizePayload {
                target: parse_tactic_target(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                term: parse_raw_machine_term(
                    required_object_field(&object, "term"),
                    &path.field("term"),
                )?,
                occurrences: parse_occurrence_path_array(
                    required_array_field(&object, "occurrences"),
                    &path.field("occurrences"),
                )?,
                name_hint: parse_optional_local_name_field(
                    &object,
                    "name_hint",
                    &path.field("name_hint"),
                )?,
            }))
        }
        "change" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CHANGE_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Change(ChangePayload {
                target: parse_tactic_target(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                replacement: parse_raw_machine_term(
                    required_object_field(&object, "replacement"),
                    &path.field("replacement"),
                )?,
                occurrences: parse_occurrence_path_array(
                    required_array_field(&object, "occurrences"),
                    &path.field("occurrences"),
                )?,
            }))
        }
        "unfold" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, UNFOLD_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Unfold(UnfoldPayload {
                target: parse_tactic_target(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                constant: parse_tactic_head(
                    required_object_field(&object, "constant"),
                    &path.field("constant"),
                )?,
                occurrences: parse_occurrence_path_array(
                    required_array_field(&object, "occurrences"),
                    &path.field("occurrences"),
                )?,
                max_delta_steps: optional_u64_field(&object, "max_delta_steps"),
            }))
        }
        "congr" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CONGR_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Congr(CongrPayload {
                target: parse_tactic_target(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                max_depth: optional_u64_field(&object, "max_depth"),
                max_new_goals: optional_u64_field(&object, "max_new_goals"),
            }))
        }
        "subst" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, SUBST_FIELDS),
                path,
            )?;
            let equality_local = required_schema_string(&object, "equality_local");
            validate_machine_local_name(
                equality_local,
                "equality_local",
                &path.field("equality_local"),
            )?;
            Ok(MachineTacticCandidate::Subst(SubstPayload {
                equality_local: equality_local.to_owned(),
                target: parse_tactic_target(
                    required_object_field(&object, "target"),
                    &path.field("target"),
                )?,
                direction: parse_rewrite_direction(
                    required_schema_string(&object, "direction"),
                    "direction",
                    &path.field("direction"),
                )?,
                occurrences: parse_occurrence_path_array(
                    required_array_field(&object, "occurrences"),
                    &path.field("occurrences"),
                )?,
            }))
        }
        "contradiction" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CONTRADICTION_FIELDS),
                path,
            )?;
            Ok(MachineTacticCandidate::Contradiction(
                ContradictionPayload {
                    mode: parse_contradiction_mode(
                        required_schema_string(&object, "mode"),
                        object
                            .field("major_local")
                            .expect("schema checked major_local"),
                        &path.field("mode"),
                        &path.field("major_local"),
                    )?,
                },
            ))
        }
        "finite-decide" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    RESERVED_SOLVER_FIELDS,
                ),
                path,
            )?;
            Ok(MachineTacticCandidate::FiniteDecide)
        }
        "omega" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    RESERVED_SOLVER_FIELDS,
                ),
                path,
            )?;
            Ok(MachineTacticCandidate::Omega)
        }
        "ring" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    RESERVED_SOLVER_FIELDS,
                ),
                path,
            )?;
            Ok(MachineTacticCandidate::Ring)
        }
        "bitblast" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    RESERVED_SOLVER_FIELDS,
                ),
                path,
            )?;
            Ok(MachineTacticCandidate::Bitblast)
        }
        _ => Err(invalid_string_literal(
            "kind",
            tactic_kind,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("kind"),
        )),
    }
}

fn parse_raw_machine_term(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<RawMachineTerm, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            RAW_MACHINE_TERM_FIELDS,
        ),
        path,
    )?;
    Ok(RawMachineTerm::new(required_schema_string(
        &object, "source",
    )))
}

fn validate_repair_payload<'value, 'src>(
    value: &'value JsonValue<'src>,
    fields: &'static [FieldSpec],
    path: &JsonPath,
) -> Result<crate::validation::ValidatedObject<'value, 'src>, MachineApiRequestError> {
    validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, fields),
        path,
    )
}

fn parse_optional_goal_id_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    path: &JsonPath,
) -> Result<Option<GoalId>, MachineApiRequestError> {
    let Some(value) = object.field("goal_id") else {
        return Ok(None);
    };
    let raw = string_value(
        value,
        "goal_id",
        MachineApiErrorKind::InvalidCandidate,
        path,
    )?;
    parse_goal_id_wire(raw).map(Some).map_err(|_| {
        invalid_string_literal("goal_id", None, MachineApiErrorKind::InvalidCandidate, path)
    })
}

fn parse_expr_path_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<ExprPath, MachineApiRequestError> {
    let segments = required_array_field(object, field)
        .iter()
        .enumerate()
        .map(|(index, value)| {
            string_value(
                value,
                field,
                MachineApiErrorKind::InvalidCandidate,
                &path.index(index),
            )
            .map(ToOwned::to_owned)
        })
        .collect::<Result<Vec<_>, _>>()?;
    ExprPath::parse_wire_segments(&segments).map_err(|_| {
        invalid_string_literal(field, None, MachineApiErrorKind::InvalidCandidate, path)
    })
}

fn parse_checked_term_payload_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<RepairCheckedTermPayload, MachineApiRequestError> {
    parse_checked_term_payload(required_object_field(object, field), path)
}

fn parse_checked_term_payload(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<RepairCheckedTermPayload, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            REPAIR_CHECKED_TERM_PAYLOAD_FIELDS,
        ),
        path,
    )?;
    Ok(RepairCheckedTermPayload {
        term_hash: parse_hash_field(&object, "term_hash", &path.field("term_hash"))?,
    })
}

fn parse_checked_term_payload_array(
    elements: &[JsonValue<'_>],
    path: &JsonPath,
) -> Result<Vec<RepairCheckedTermPayload>, MachineApiRequestError> {
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_checked_term_payload(value, &path.index(index)))
        .collect()
}

fn parse_local_ref_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<RepairLocalRef, MachineApiRequestError> {
    parse_local_ref(required_object_field(object, field), path)
}

fn parse_local_ref(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<RepairLocalRef, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            REPAIR_LOCAL_REF_FIELDS,
        ),
        path,
    )?;
    let name = required_schema_string(&object, "name");
    validate_machine_local_name(name, "name", &path.field("name"))?;
    Ok(RepairLocalRef {
        name: name.to_owned(),
    })
}

fn parse_global_ref_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<RepairGlobalRef, MachineApiRequestError> {
    parse_global_ref(required_object_field(object, field), path)
}

fn parse_global_ref(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<RepairGlobalRef, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            REPAIR_GLOBAL_REF_FIELDS,
        ),
        path,
    )?;
    let name = parse_renderable_name_field(&object, "name", &path.field("name"))?;
    if !name.is_canonical() {
        return Err(invalid_string_literal(
            "name",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("name"),
        ));
    }
    Ok(RepairGlobalRef { name })
}

fn parse_global_ref_array(
    elements: &[JsonValue<'_>],
    path: &JsonPath,
) -> Result<Vec<RepairGlobalRef>, MachineApiRequestError> {
    let mut seen = BTreeSet::new();
    let mut refs = Vec::with_capacity(elements.len());
    for (index, value) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let item = parse_global_ref(value, &item_path)?;
        if !seen.insert(item.name.clone()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidCandidate,
                item_path.field("name"),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: item.name.as_dotted(),
                },
            ));
        }
        refs.push(item);
    }
    Ok(refs)
}

fn parse_optional_raw_machine_term_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Option<RawMachineTerm>, MachineApiRequestError> {
    let value = object
        .field(field)
        .expect("schema checked optional term field");
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    parse_raw_machine_term(value, path).map(Some)
}

fn parse_constructor_selection(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<ConstructorSelection, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    let mode = string_value(
        required_value_member(
            members,
            "mode",
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )?,
        "mode",
        MachineApiErrorKind::InvalidCandidate,
        &path.field("mode"),
    )?;
    match mode {
        "auto" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    CONSTRUCTOR_AUTO_SELECTION_FIELDS,
                ),
                path,
            )?;
            Ok(ConstructorSelection::Auto)
        }
        "explicit" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    CONSTRUCTOR_EXPLICIT_SELECTION_FIELDS,
                ),
                path,
            )?;
            Ok(ConstructorSelection::Explicit {
                constructor: parse_tactic_head(
                    required_object_field(&object, "constructor"),
                    &path.field("constructor"),
                )?,
            })
        }
        _ => Err(invalid_string_literal(
            "mode",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )),
    }
}

fn parse_local_lemma_proof(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<LocalLemmaProof<RawMachineTerm>, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    let mode = string_value(
        required_value_member(
            members,
            "mode",
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )?,
        "mode",
        MachineApiErrorKind::InvalidCandidate,
        &path.field("mode"),
    )?;
    match mode {
        "child-goal" => {
            validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    LOCAL_LEMMA_PROOF_CHILD_FIELDS,
                ),
                path,
            )?;
            Ok(LocalLemmaProof::ChildGoal)
        }
        "term" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidCandidate,
                    LOCAL_LEMMA_PROOF_TERM_FIELDS,
                ),
                path,
            )?;
            parse_raw_machine_term(required_object_field(&object, "term"), &path.field("term"))
                .map(LocalLemmaProof::Term)
        }
        _ => Err(invalid_string_literal(
            "mode",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )),
    }
}

fn parse_local_lemma_insertion_policy(
    value: &str,
    path: &JsonPath,
) -> Result<LocalLemmaInsertionPolicy, MachineApiRequestError> {
    match value {
        "after-current" => Ok(LocalLemmaInsertionPolicy::AfterCurrent),
        "end" => Ok(LocalLemmaInsertionPolicy::End),
        _ => Err(invalid_string_literal(
            "insertion",
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn parse_suffices_continuation_policy(
    value: &str,
    path: &JsonPath,
) -> Result<SufficesContinuationPolicy, MachineApiRequestError> {
    match value {
        "prove-intermediate-first" => Ok(SufficesContinuationPolicy::ProveIntermediateFirst),
        "prove-continuation-first" => Ok(SufficesContinuationPolicy::ProveContinuationFirst),
        _ => Err(invalid_string_literal(
            "continuation",
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn parse_specialize_result_policy(
    value: &str,
    path: &JsonPath,
) -> Result<SpecializeResultPolicy, MachineApiRequestError> {
    match value {
        "add-local" => Ok(SpecializeResultPolicy::AddLocal),
        "replace-original" => Ok(SpecializeResultPolicy::ReplaceOriginal),
        _ => Err(invalid_string_literal(
            "result_policy",
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn parse_revert_dependency_policy(
    value: &str,
    path: &JsonPath,
) -> Result<RevertDependencyPolicy, MachineApiRequestError> {
    match value {
        "exact" => Ok(RevertDependencyPolicy::Exact),
        "closure" => Ok(RevertDependencyPolicy::Closure),
        _ => Err(invalid_string_literal(
            "dependency_policy",
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn parse_tactic_target(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<TacticTarget, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    let mode = string_value(
        required_value_member(
            members,
            "mode",
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )?,
        "mode",
        MachineApiErrorKind::InvalidCandidate,
        &path.field("mode"),
    )?;
    match mode {
        "goal" => {
            validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, TARGET_GOAL_FIELDS),
                path,
            )?;
            Ok(TacticTarget::Goal)
        }
        "local" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, TARGET_LOCAL_FIELDS),
                path,
            )?;
            let name = required_schema_string(&object, "name");
            validate_machine_local_name(name, "name", &path.field("name"))?;
            Ok(TacticTarget::Local {
                name: name.to_owned(),
            })
        }
        _ => Err(invalid_string_literal(
            "mode",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )),
    }
}

fn parse_occurrence_path_array(
    elements: &[JsonValue<'_>],
    path: &JsonPath,
) -> Result<Vec<OccurrencePath>, MachineApiRequestError> {
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_occurrence_path(value, &path.index(index)))
        .collect()
}

fn parse_occurrence_path(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<OccurrencePath, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCandidate,
            OCCURRENCE_PATH_FIELDS,
        ),
        path,
    )?;
    let indices = required_array_field(&object, "indices")
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let raw = value.number_raw().ok_or_else(|| {
                type_mismatch(
                    "indices",
                    JsonFieldType::UnsignedInteger { max: u64::MAX },
                    value,
                    MachineApiErrorKind::InvalidCandidate,
                    &path.field("indices").index(index),
                )
            })?;
            parse_strict_u64_token(raw, u64::MAX).map_err(|error| {
                MachineApiRequestError::new(
                    MachineApiErrorKind::InvalidCandidate,
                    path.field("indices").index(index),
                    MachineApiRequestErrorReason::InvalidUnsignedInteger {
                        field: "indices",
                        raw: raw.to_owned(),
                        error,
                    },
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(OccurrencePath { indices })
}

fn parse_contradiction_mode(
    mode: &str,
    major_local: &JsonValue<'_>,
    mode_path: &JsonPath,
    major_local_path: &JsonPath,
) -> Result<ContradictionMode, MachineApiRequestError> {
    match mode {
        "auto" => {
            if major_local.kind() != JsonValueKind::Null {
                return Err(invalid_string_literal(
                    "major_local",
                    None,
                    MachineApiErrorKind::InvalidCandidate,
                    major_local_path,
                ));
            }
            Ok(ContradictionMode::Auto)
        }
        "local" => {
            let local = string_value(
                major_local,
                "major_local",
                MachineApiErrorKind::InvalidCandidate,
                major_local_path,
            )?;
            validate_machine_local_name(local, "major_local", major_local_path)?;
            Ok(ContradictionMode::Local {
                major_local: local.to_owned(),
            })
        }
        _ => Err(invalid_string_literal(
            "mode",
            None,
            MachineApiErrorKind::InvalidCandidate,
            mode_path,
        )),
    }
}

fn parse_tactic_head(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<TacticHead, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    if members.len() != 1 {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::MissingField { field: "head" },
        ));
    }
    let member = &members[0];
    match member.key() {
        "imported" => {
            let object = validate_json_object(
                member.value(),
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, IMPORTED_HEAD_FIELDS),
                &path.field("imported"),
            )?;
            Ok(TacticHead::Imported {
                name: parse_renderable_name_field(
                    &object,
                    "name",
                    &path.field("imported").field("name"),
                )?,
                decl_interface_hash: parse_hash_field(
                    &object,
                    "decl_interface_hash",
                    &path.field("imported").field("decl_interface_hash"),
                )?,
            })
        }
        "current_module" => {
            let object = validate_json_object(
                member.value(),
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CURRENT_HEAD_FIELDS),
                &path.field("current_module"),
            )?;
            Ok(TacticHead::CurrentModule {
                name: parse_renderable_name_field(
                    &object,
                    "name",
                    &path.field("current_module").field("name"),
                )?,
                decl_interface_hash: parse_hash_field(
                    &object,
                    "decl_interface_hash",
                    &path.field("current_module").field("decl_interface_hash"),
                )?,
            })
        }
        "local" => {
            let object = validate_json_object(
                member.value(),
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, LOCAL_HEAD_FIELDS),
                &path.field("local"),
            )?;
            let name = required_schema_string(&object, "name");
            validate_machine_local_name(name, "name", &path.field("local").field("name"))?;
            Ok(TacticHead::Local {
                name: name.to_owned(),
            })
        }
        other => Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.field(other),
            MachineApiRequestErrorReason::UnknownField {
                field: other.to_owned(),
            },
        )),
    }
}

fn parse_rewrite_rule(
    value: &JsonValue<'_>,
    universe_params: &[String],
    allow_unbound_level_params: bool,
    path: &JsonPath,
) -> Result<CandidateRewriteRuleRef, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, REWRITE_RULE_FIELDS),
        path,
    )?;
    Ok(CandidateRewriteRuleRef {
        head: parse_tactic_head(required_object_field(&object, "head"), &path.field("head"))?,
        universe_args: parse_level_array(
            required_array_field(&object, "universe_args"),
            universe_params,
            allow_unbound_level_params,
            &path.field("universe_args"),
        )?,
        args: parse_apply_arg_array(required_array_field(&object, "args"), &path.field("args"))?,
    })
}

fn parse_apply_arg_array(
    elements: &[JsonValue<'_>],
    path: &JsonPath,
) -> Result<Vec<CandidateApplyArg>, MachineApiRequestError> {
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_apply_arg(value, &path.index(index)))
        .collect()
}

fn parse_apply_arg(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<CandidateApplyArg, MachineApiRequestError> {
    let members = value.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        )
    })?;
    reject_duplicate_keys(members, MachineApiErrorKind::InvalidCandidate, path)?;
    let mode_value = member_value(members, "mode").ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidCandidate,
            path.field("mode"),
            MachineApiRequestErrorReason::MissingField { field: "mode" },
        )
    })?;
    let mode = string_value(
        mode_value,
        "mode",
        MachineApiErrorKind::InvalidCandidate,
        &path.field("mode"),
    )?;

    match mode {
        "term" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, ARG_TERM_FIELDS),
                path,
            )?;
            Ok(CandidateApplyArg::Term(parse_raw_machine_term(
                required_object_field(&object, "term"),
                &path.field("term"),
            )?))
        }
        "subgoal" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, ARG_SUBGOAL_FIELDS),
                path,
            )?;
            let name_hint = object
                .field("name_hint")
                .expect("schema checked required name_hint");
            let name_hint = match name_hint.kind() {
                JsonValueKind::Null => None,
                JsonValueKind::String => {
                    let name = name_hint
                        .string_value()
                        .expect("kind checked string name_hint");
                    validate_machine_local_name(name, "name_hint", &path.field("name_hint"))?;
                    Some(name.to_owned())
                }
                _ => unreachable!("schema checked nullable string name_hint"),
            };
            Ok(CandidateApplyArg::Subgoal { name_hint })
        }
        "infer_from_target" => {
            validate_json_object(
                value,
                ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, ARG_INFER_FIELDS),
                path,
            )?;
            Ok(CandidateApplyArg::InferFromTarget)
        }
        _ => Err(invalid_string_literal(
            "mode",
            None,
            MachineApiErrorKind::InvalidCandidate,
            &path.field("mode"),
        )),
    }
}

fn parse_simp_rule_array(
    elements: &[JsonValue<'_>],
    path: &JsonPath,
) -> Result<Vec<SimpRuleRef>, MachineApiRequestError> {
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_simp_rule(value, &path.index(index)))
        .collect()
}

fn parse_simp_rule(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<SimpRuleRef, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, SIMP_RULE_FIELDS),
        path,
    )?;
    Ok(SimpRuleRef {
        name: parse_renderable_name_field(&object, "name", &path.field("name"))?,
        decl_interface_hash: parse_hash_field(
            &object,
            "decl_interface_hash",
            &path.field("decl_interface_hash"),
        )?,
        direction: parse_rewrite_direction(
            required_schema_string(&object, "direction"),
            "direction",
            &path.field("direction"),
        )?,
    })
}

fn parse_level_array(
    elements: &[JsonValue<'_>],
    universe_params: &[String],
    allow_unbound_level_params: bool,
    path: &JsonPath,
) -> Result<Vec<Level>, MachineApiRequestError> {
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let source = string_value(
                value,
                "level",
                MachineApiErrorKind::InvalidCandidate,
                &path.index(index),
            )?;
            parse_level_wire(source, universe_params, allow_unbound_level_params).map_err(|_| {
                invalid_string_literal(
                    "level",
                    None,
                    MachineApiErrorKind::InvalidCandidate,
                    &path.index(index),
                )
            })
        })
        .collect()
}

fn parse_level_wire(
    source: &str,
    universe_params: &[String],
    allow_unbound_level_params: bool,
) -> Result<Level, ()> {
    if source.is_empty()
        || source.starts_with(' ')
        || source.ends_with(' ')
        || source.contains("  ")
    {
        return Err(());
    }
    let tokens = source.split(' ').collect::<Vec<_>>();
    let mut cursor = 0;
    let level = parse_level_tokens(
        &tokens,
        &mut cursor,
        universe_params,
        allow_unbound_level_params,
    )?;
    if cursor != tokens.len() {
        return Err(());
    }
    if render_level_wire(&level) != source {
        return Err(());
    }
    Ok(level)
}

fn parse_level_tokens(
    tokens: &[&str],
    cursor: &mut usize,
    universe_params: &[String],
    allow_unbound_level_params: bool,
) -> Result<Level, ()> {
    let token = tokens.get(*cursor).copied().ok_or(())?;
    *cursor += 1;
    match token {
        "succ" => Ok(Level::Succ(Box::new(parse_level_tokens(
            tokens,
            cursor,
            universe_params,
            allow_unbound_level_params,
        )?))),
        "max" => {
            let lhs =
                parse_level_tokens(tokens, cursor, universe_params, allow_unbound_level_params)?;
            let rhs =
                parse_level_tokens(tokens, cursor, universe_params, allow_unbound_level_params)?;
            Ok(Level::Max(Box::new(lhs), Box::new(rhs)))
        }
        "imax" => {
            let lhs =
                parse_level_tokens(tokens, cursor, universe_params, allow_unbound_level_params)?;
            let rhs =
                parse_level_tokens(tokens, cursor, universe_params, allow_unbound_level_params)?;
            Ok(Level::IMax(Box::new(lhs), Box::new(rhs)))
        }
        _ if is_canonical_decimal(token) => decimal_level(token),
        _ if is_machine_universe_param_name(token)
            && (allow_unbound_level_params
                || universe_params.iter().any(|param| param == token)) =>
        {
            Ok(Level::Param(token.to_owned()))
        }
        _ => Err(()),
    }
}

fn decimal_level(token: &str) -> Result<Level, ()> {
    let value = token.parse::<u64>().map_err(|_| ())?;
    if value > MAX_NUMERIC_UNIVERSE_LEVEL {
        return Err(());
    }
    let mut level = Level::Zero;
    for _ in 0..value {
        level = Level::Succ(Box::new(level));
    }
    Ok(level)
}

fn is_canonical_decimal(token: &str) -> bool {
    if token == "0" {
        return true;
    }
    token
        .as_bytes()
        .first()
        .is_some_and(|byte| matches!(byte, b'1'..=b'9'))
        && token.as_bytes()[1..].iter().all(u8::is_ascii_digit)
}

fn render_level_wire(level: &Level) -> String {
    if let Some(value) = level_as_nat(level) {
        return value.to_string();
    }
    match level {
        Level::Zero => "0".to_owned(),
        Level::Succ(inner) => format!("succ {}", render_level_wire(inner)),
        Level::Max(lhs, rhs) => {
            format!("max {} {}", render_level_wire(lhs), render_level_wire(rhs))
        }
        Level::IMax(lhs, rhs) => {
            format!("imax {} {}", render_level_wire(lhs), render_level_wire(rhs))
        }
        Level::Param(name) => name.clone(),
    }
}

fn level_as_nat(level: &Level) -> Option<u64> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(inner) => Some(level_as_nat(inner)? + 1),
        _ => None,
    }
}

fn parse_rewrite_direction(
    value: &str,
    field: &'static str,
    path: &JsonPath,
) -> Result<RewriteDirection, MachineApiRequestError> {
    match value {
        "forward" => Ok(RewriteDirection::Forward),
        "backward" => Ok(RewriteDirection::Backward),
        _ => Err(invalid_string_literal(
            field,
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn parse_rewrite_site(
    value: &str,
    field: &'static str,
    path: &JsonPath,
) -> Result<RewriteSite, MachineApiRequestError> {
    match value {
        "eq_target_left" => Ok(RewriteSite::EqTargetLeft),
        "eq_target_right" => Ok(RewriteSite::EqTargetRight),
        _ => Err(invalid_string_literal(
            field,
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        )),
    }
}

fn validate_run_top_level<'value, 'src>(
    root: &'value JsonValue<'src>,
) -> Result<&'value [JsonMember<'src>], MachineApiRequestError> {
    let members = root.object_members().ok_or_else(|| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidTacticRunRequest,
            JsonPath::root(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: root.kind(),
            },
        )
    })?;
    reject_duplicate_keys(
        members,
        MachineApiErrorKind::InvalidTacticRunRequest,
        &JsonPath::root(),
    )?;
    let allowed = [
        "session_id",
        "snapshot_id",
        "state_fingerprint",
        "goal_id",
        "candidate",
        "deterministic_budget",
        "scheduler_limits",
    ];
    for member in members {
        if !allowed.contains(&member.key()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidTacticRunRequest,
                JsonPath::root().field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }
    Ok(members)
}

fn validate_batch_top_level<'value, 'src>(
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
    reject_duplicate_keys(
        members,
        MachineApiErrorKind::InvalidBatchPolicy,
        &JsonPath::root(),
    )?;
    let allowed = [
        "session_id",
        "snapshot_id",
        "state_fingerprint",
        "goal_id",
        "candidates",
        "deterministic_budget",
        "batch_policy",
        "scheduler_limits",
    ];
    for member in members {
        if !allowed.contains(&member.key()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                JsonPath::root().field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }
    Ok(members)
}

fn parse_batch_candidates<'src>(
    value: &JsonValue<'src>,
    path: &JsonPath,
) -> Result<Vec<MachineTacticBatchCandidateRequest<'src>>, MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Err(null_field(
            "candidates",
            MachineApiErrorKind::InvalidBatchPolicy,
            path,
        ));
    }
    let elements = value.array_elements().ok_or_else(|| {
        type_mismatch(
            "candidates",
            JsonFieldType::Array,
            value,
            MachineApiErrorKind::InvalidBatchPolicy,
            path,
        )
    })?;
    if elements.is_empty() || elements.len() > 256 {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidBatchPolicy,
            path.clone(),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "candidates",
                expected: JsonFieldType::Array,
                actual: JsonValueKind::Array,
            },
        ));
    }

    let mut ids = BTreeSet::new();
    let mut candidates = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let members = item.object_members().ok_or_else(|| {
            MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                item_path.clone(),
                MachineApiRequestErrorReason::ExpectedObject {
                    actual: item.kind(),
                },
            )
        })?;
        reject_duplicate_keys(members, MachineApiErrorKind::InvalidBatchPolicy, &item_path)?;
        for member in members {
            if !matches!(member.key(), "candidate_id" | "candidate") {
                return Err(MachineApiRequestError::new(
                    MachineApiErrorKind::InvalidBatchPolicy,
                    item_path.field(member.key()),
                    MachineApiRequestErrorReason::UnknownField {
                        field: member.key().to_owned(),
                    },
                ));
            }
        }

        let candidate_id = string_value(
            member_value(members, "candidate_id").ok_or_else(|| {
                MachineApiRequestError::new(
                    MachineApiErrorKind::InvalidBatchPolicy,
                    item_path.field("candidate_id"),
                    MachineApiRequestErrorReason::MissingField {
                        field: "candidate_id",
                    },
                )
            })?,
            "candidate_id",
            MachineApiErrorKind::InvalidBatchPolicy,
            &item_path.field("candidate_id"),
        )?;
        validate_machine_candidate_id(candidate_id, &item_path.field("candidate_id"))?;
        if !ids.insert(candidate_id.to_owned()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                item_path.field("candidate_id"),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: candidate_id.to_owned(),
                },
            ));
        }

        let candidate = member_value(members, "candidate").ok_or_else(|| {
            MachineApiRequestError::new(
                MachineApiErrorKind::InvalidBatchPolicy,
                item_path.field("candidate"),
                MachineApiRequestErrorReason::MissingField { field: "candidate" },
            )
        })?;
        candidates.push(MachineTacticBatchCandidateRequest {
            candidate_id: candidate_id.to_owned(),
            candidate: delayed_json_payload(candidate),
        });
    }
    Ok(candidates)
}

fn parse_deterministic_budget(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<TacticBudget, MachineApiRequestError> {
    parse_deterministic_budget_with_error_kind(value, path, MachineApiErrorKind::InvalidBudget)
}

pub(crate) fn parse_deterministic_budget_with_error_kind(
    value: &JsonValue<'_>,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<TacticBudget, MachineApiRequestError> {
    let object = validate_json_object(value, ObjectSchema::new(error_kind, BUDGET_FIELDS), path)?;
    Ok(TacticBudget {
        max_tactic_steps: required_u64(&object, "max_tactic_steps"),
        max_whnf_steps: required_u64(&object, "max_whnf_steps"),
        max_conversion_steps: required_u64(&object, "max_conversion_steps"),
        max_rewrite_steps: required_u64(&object, "max_rewrite_steps"),
        max_meta_allocations: required_u64(&object, "max_meta_allocations"),
        max_expr_nodes: required_u64(&object, "max_expr_nodes"),
    })
}

fn parse_diagnostic_budget(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<DiagnosticBudget, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidBudget, DIAGNOSTIC_BUDGET_FIELDS),
        path,
    )?;
    Ok(DiagnosticBudget {
        max_graph_nodes: required_u64(&object, "max_graph_nodes"),
        max_expression_paths: required_u64(&object, "max_expression_paths"),
        max_rewrite_site_scans: required_u64(&object, "max_rewrite_site_scans"),
        max_pretty_term_bytes: required_u64(&object, "max_pretty_term_bytes"),
        max_repair_proposals: required_u64(&object, "max_repair_proposals"),
        max_diagnostic_steps: required_u64(&object, "max_diagnostic_steps"),
    })
}

fn parse_lazy_diagnostic_profile(value: &str) -> Result<DiagnosticProfile, MachineApiRequestError> {
    match value {
        "basic" => Ok(DiagnosticProfile::Basic),
        "full" => Ok(DiagnosticProfile::Full),
        _ => Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidTacticRunRequest,
            JsonPath::root().field("profile"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "profile",
                expected: JsonFieldType::String,
                actual: JsonValueKind::String,
            },
        )),
    }
}

fn parse_batch_policy(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineTacticBatchPolicy, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidBatchPolicy, BATCH_POLICY_FIELDS),
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

fn required_batch_policy_u32(
    object: &crate::validation::ValidatedObject<'_, '_>,
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

fn parse_run_scheduler_limits(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineRunSchedulerLimits, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidSchedulerLimits,
            RUN_SCHEDULER_FIELDS,
        ),
        path,
    )?;
    Ok(MachineRunSchedulerLimits {
        timeout_ms: optional_positive_u64(&object, "timeout_ms", &path.field("timeout_ms"))?,
        max_memory_mb: optional_positive_u64(
            &object,
            "max_memory_mb",
            &path.field("max_memory_mb"),
        )?,
    })
}

fn parse_batch_scheduler_limits(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineBatchSchedulerLimits, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidSchedulerLimits,
            BATCH_SCHEDULER_FIELDS,
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

#[derive(Clone, Copy)]
struct RunSchedulerObservationContext {
    started_at: Instant,
    memory_usage_bytes: fn() -> Option<u64>,
}

impl RunSchedulerObservationContext {
    fn start() -> Self {
        Self {
            started_at: Instant::now(),
            memory_usage_bytes: current_process_resident_bytes,
        }
    }

    fn observe(self, limits: MachineRunSchedulerLimits) -> Option<MachineSchedulerArtifactKind> {
        observe_run_scheduler_limits(
            limits,
            self.started_at.elapsed(),
            (self.memory_usage_bytes)(),
        )
    }
}

fn observe_run_scheduler_limits(
    limits: MachineRunSchedulerLimits,
    elapsed: Duration,
    memory_usage_bytes: Option<u64>,
) -> Option<MachineSchedulerArtifactKind> {
    if let (Some(limit_mb), Some(usage_bytes)) = (limits.max_memory_mb, memory_usage_bytes) {
        if usage_bytes > memory_limit_bytes(limit_mb) {
            return Some(MachineSchedulerArtifactKind::ResourceLimitExceeded);
        }
    }

    if let Some(timeout_ms) = limits.timeout_ms {
        if elapsed >= Duration::from_millis(timeout_ms) {
            return Some(MachineSchedulerArtifactKind::Timeout);
        }
    }

    None
}

#[derive(Clone, Copy)]
struct BatchSchedulerObservationContext {
    batch_started_at: Instant,
    candidate_started_at: Option<Instant>,
    memory_usage_bytes: fn() -> Option<u64>,
}

impl BatchSchedulerObservationContext {
    fn start() -> Self {
        Self {
            batch_started_at: Instant::now(),
            candidate_started_at: None,
            memory_usage_bytes: current_process_resident_bytes,
        }
    }

    fn begin_candidate(&mut self) {
        self.candidate_started_at = Some(Instant::now());
    }

    fn observe(self, limits: MachineBatchSchedulerLimits) -> Option<BatchSchedulerStop> {
        observe_batch_scheduler_limits(
            limits,
            self.batch_started_at.elapsed(),
            self.candidate_started_at
                .map(|started_at| started_at.elapsed()),
            (self.memory_usage_bytes)(),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BatchSchedulerStop {
    kind: MachineSchedulerArtifactKind,
    scope: MachineSchedulerArtifactScope,
}

fn observe_batch_scheduler_limits(
    limits: MachineBatchSchedulerLimits,
    batch_elapsed: Duration,
    candidate_elapsed: Option<Duration>,
    memory_usage_bytes: Option<u64>,
) -> Option<BatchSchedulerStop> {
    if let (Some(limit_mb), Some(usage_bytes)) = (limits.max_memory_mb, memory_usage_bytes) {
        if usage_bytes > memory_limit_bytes(limit_mb) {
            return Some(BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::ResourceLimitExceeded,
                scope: MachineSchedulerArtifactScope::Batch,
            });
        }
    }

    if let Some(timeout_ms) = limits.batch_timeout_ms {
        if batch_elapsed >= Duration::from_millis(timeout_ms) {
            return Some(BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Batch,
            });
        }
    }

    if let (Some(timeout_ms), Some(elapsed)) = (limits.per_candidate_timeout_ms, candidate_elapsed)
    {
        if elapsed >= Duration::from_millis(timeout_ms) {
            return Some(BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Candidate,
            });
        }
    }

    None
}

fn memory_limit_bytes(max_memory_mb: u64) -> u64 {
    max_memory_mb.saturating_mul(1024 * 1024)
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn current_process_resident_bytes() -> Option<u64> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    let resident_pages = statm.split_whitespace().nth(1)?.parse::<u64>().ok()?;
    resident_pages.checked_mul(system_page_size_bytes()?)
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn system_page_size_bytes() -> Option<u64> {
    // SAFETY: sysconf reads a process-global setting and does not dereference caller pointers.
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    u64::try_from(page_size).ok().filter(|bytes| *bytes > 0)
}

#[cfg(any(target_os = "ios", target_os = "macos"))]
fn current_process_resident_bytes() -> Option<u64> {
    let mut info = std::mem::MaybeUninit::<libc::mach_task_basic_info>::uninit();
    let mut count = libc::MACH_TASK_BASIC_INFO_COUNT;
    // SAFETY: task_info writes mach_task_basic_info into the provided buffer for the current
    // task and does not retain caller pointers after returning.
    let rc = unsafe {
        libc::task_info(
            current_mach_task_self(),
            libc::MACH_TASK_BASIC_INFO,
            info.as_mut_ptr().cast::<libc::integer_t>(),
            &mut count,
        )
    };
    if rc != libc::KERN_SUCCESS {
        return None;
    }
    // SAFETY: task_info returned success, so mach_task_basic_info has been initialized.
    let info = unsafe { info.assume_init() };
    Some(info.resident_size)
}

#[cfg(any(target_os = "ios", target_os = "macos"))]
#[allow(deprecated)]
fn current_mach_task_self() -> libc::mach_port_t {
    // SAFETY: mach_task_self reads libSystem's current-task port for this process.
    unsafe { libc::mach_task_self() }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos"
)))]
fn current_process_resident_bytes() -> Option<u64> {
    None
}

fn new_goals_in_next_snapshot_order(
    next_open_goals: &[npa_tactic::GoalId],
    added_goals: &[npa_tactic::GoalId],
) -> Option<Vec<npa_tactic::GoalId>> {
    let added = added_goals.iter().copied().collect::<BTreeSet<_>>();
    let new_goals = next_open_goals
        .iter()
        .copied()
        .filter(|goal| added.contains(goal))
        .collect::<Vec<_>>();
    (new_goals.len() == added.len()).then_some(new_goals)
}

fn batch_policy_stop(
    evaluated_count: u32,
    success_count: u32,
    failure_count: u32,
    candidate_count: usize,
    policy: MachineTacticBatchPolicy,
) -> bool {
    usize::try_from(evaluated_count).is_ok_and(|count| count >= candidate_count)
        || evaluated_count >= policy.max_evaluated_candidates
        || success_count >= policy.stop_after_successes
        || failure_count >= policy.stop_after_failures
}

fn request_error(error: MachineApiRequestError) -> Box<MachineTacticRunError> {
    plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
        RunErrorCorrelation::default(),
    )
}

fn batch_request_error(error: MachineApiRequestError) -> Box<MachineTacticBatchError> {
    batch_plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
        None,
    )
}

fn candidate_request_error(
    error: MachineApiRequestError,
    unchanged_state_fingerprint: Hash,
    deterministic_budget_hash: Hash,
    goal_id: npa_tactic::GoalId,
    tactic_kind: Option<MachineApiTacticKind>,
) -> Box<MachineTacticRunError> {
    plain_error_with_goal(
        MachineApiErrorKind::InvalidCandidate,
        MachineApiDiagnosticPhase::CandidateValidation,
        format!(
            "candidate validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
        goal_id,
        RunErrorCorrelation {
            unchanged_state_fingerprint: Some(unchanged_state_fingerprint),
            deterministic_budget_hash: Some(deterministic_budget_hash),
            tactic_kind,
            ..RunErrorCorrelation::default()
        },
    )
}

fn snapshot_lookup_error(error: MachineSnapshotLookupError) -> Box<MachineTacticRunError> {
    let kind = match error {
        MachineSnapshotLookupError::UnknownSnapshot { .. } => MachineApiErrorKind::UnknownSnapshot,
        MachineSnapshotLookupError::StateFingerprintMismatch { .. } => {
            MachineApiErrorKind::StateFingerprintMismatch
        }
        MachineSnapshotLookupError::SnapshotIdentityMismatch { .. }
        | MachineSnapshotLookupError::InvalidMachineProofState { .. }
        | MachineSnapshotLookupError::ExecutableStateFingerprintMismatch { .. }
        | MachineSnapshotLookupError::StoredSnapshotViewMismatch { .. } => {
            MachineApiErrorKind::InvalidMachineProofState
        }
    };
    plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
        RunErrorCorrelation::default(),
    )
}

fn batch_snapshot_lookup_error(error: MachineSnapshotLookupError) -> Box<MachineTacticBatchError> {
    let kind = match error {
        MachineSnapshotLookupError::UnknownSnapshot { .. } => MachineApiErrorKind::UnknownSnapshot,
        MachineSnapshotLookupError::StateFingerprintMismatch { .. } => {
            MachineApiErrorKind::StateFingerprintMismatch
        }
        MachineSnapshotLookupError::SnapshotIdentityMismatch { .. }
        | MachineSnapshotLookupError::InvalidMachineProofState { .. }
        | MachineSnapshotLookupError::ExecutableStateFingerprintMismatch { .. }
        | MachineSnapshotLookupError::StoredSnapshotViewMismatch { .. } => {
            MachineApiErrorKind::InvalidMachineProofState
        }
    };
    batch_plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
        None,
    )
}

fn adapter_error(
    error: Box<MachineTacticAdapterError>,
    unchanged_state_fingerprint: Hash,
    candidate_hash_override: Option<Hash>,
    deterministic_budget_hash_override: Option<Hash>,
) -> Box<MachineTacticRunError> {
    let deterministic_budget_hash = error
        .deterministic_budget_hash
        .or(deterministic_budget_hash_override);
    error_response(
        error.diagnostic,
        Some(unchanged_state_fingerprint),
        candidate_hash_override,
        deterministic_budget_hash,
    )
}

fn next_snapshot_store_error(
    error: MachineSnapshotStoreError,
    unchanged_state_fingerprint: Hash,
    candidate_hash: Hash,
    deterministic_budget_hash: Hash,
    goal_id: npa_tactic::GoalId,
    tactic_kind: MachineApiTacticKind,
) -> Box<MachineTacticRunError> {
    match error {
        MachineSnapshotStoreError::SnapshotQuotaExceeded { .. } => next_snapshot_invariant_error(
            "unexpected snapshot quota error after scheduler handling",
            unchanged_state_fingerprint,
            candidate_hash,
            deterministic_budget_hash,
            goal_id,
            tactic_kind,
        ),
        MachineSnapshotStoreError::Materialization(source) => next_snapshot_materialization_error(
            source,
            unchanged_state_fingerprint,
            candidate_hash,
            deterministic_budget_hash,
            goal_id,
            tactic_kind,
        ),
        MachineSnapshotStoreError::Lookup(source) => next_snapshot_invariant_error(
            format!("next snapshot store consistency check failed: {source:?}"),
            unchanged_state_fingerprint,
            candidate_hash,
            deterministic_budget_hash,
            goal_id,
            tactic_kind,
        ),
    }
}

fn next_snapshot_materialization_error(
    source: MachineSnapshotMaterializationError,
    unchanged_state_fingerprint: Hash,
    candidate_hash: Hash,
    deterministic_budget_hash: Hash,
    goal_id: npa_tactic::GoalId,
    tactic_kind: MachineApiTacticKind,
) -> Box<MachineTacticRunError> {
    next_snapshot_invariant_error(
        format!("next snapshot materialization failed: {source:?}"),
        unchanged_state_fingerprint,
        candidate_hash,
        deterministic_budget_hash,
        goal_id,
        tactic_kind,
    )
}

fn next_snapshot_invariant_error(
    message: impl Into<String>,
    unchanged_state_fingerprint: Hash,
    candidate_hash: Hash,
    deterministic_budget_hash: Hash,
    goal_id: npa_tactic::GoalId,
    tactic_kind: MachineApiTacticKind,
) -> Box<MachineTacticRunError> {
    plain_error_with_goal(
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::TacticExecution,
        message,
        goal_id,
        RunErrorCorrelation {
            unchanged_state_fingerprint: Some(unchanged_state_fingerprint),
            candidate_hash: Some(candidate_hash),
            deterministic_budget_hash: Some(deterministic_budget_hash),
            tactic_kind: Some(tactic_kind),
            ..RunErrorCorrelation::default()
        },
    )
}

fn scheduler_stop(
    previous_state_fingerprint: Hash,
    deterministic_budget_hash: Hash,
    kind: MachineSchedulerArtifactKind,
) -> MachineTacticRunResponse {
    MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
        status: MachineApiResponseStatus::SchedulerStopped,
        scheduler_artifact: MachineSchedulerArtifact {
            kind,
            scope: MachineSchedulerArtifactScope::Candidate,
            retryable: true,
        },
        endpoint_fields: MachineTacticRunSchedulerFields {
            previous_state_fingerprint,
            deterministic_budget_hash,
        },
    })
}

fn batch_scheduler_stop(
    previous_state_fingerprint: Hash,
    deterministic_budget_hash: Hash,
    results: Vec<MachineTacticBatchItemResponse>,
    success_count: u32,
    failure_count: u32,
    stop: BatchSchedulerStop,
) -> MachineTacticBatchResponse {
    let status = match stop.kind {
        MachineSchedulerArtifactKind::Timeout => MachineApiResponseStatus::PartialTimeout,
        MachineSchedulerArtifactKind::ResourceLimitExceeded => {
            MachineApiResponseStatus::PartialResourceLimit
        }
    };
    MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
        status,
        scheduler_artifact: MachineSchedulerArtifact {
            kind: stop.kind,
            scope: stop.scope,
            retryable: true,
        },
        endpoint_fields: MachineTacticBatchSchedulerFields {
            previous_state_fingerprint,
            deterministic_budget_hash,
            completed_prefix_len: results
                .len()
                .try_into()
                .expect("batch protocol caps results at 256"),
            results,
            success_count,
            failure_count,
        },
    })
}

fn batch_candidate_request_error_item(
    candidate_id: String,
    error: MachineApiRequestError,
    goal_id: npa_tactic::GoalId,
    tactic_kind: Option<MachineApiTacticKind>,
) -> MachineTacticBatchItemResponse {
    let message = format!(
        "candidate validation failed at {}: {:?}",
        json_path_display(&error.path),
        error.reason
    );
    batch_plain_item_error(
        candidate_id,
        None,
        error.kind,
        MachineApiDiagnosticPhase::CandidateValidation,
        message,
        goal_id,
        tactic_kind,
    )
}

fn batch_adapter_error_item(
    candidate_id: String,
    error: Box<MachineTacticAdapterError>,
    candidate_hash_override: Option<Hash>,
) -> MachineTacticBatchItemResponse {
    batch_error_item(candidate_id, candidate_hash_override, error.diagnostic)
}

fn batch_next_snapshot_error_item(
    candidate_id: String,
    error: MachineSnapshotStoreError,
    goal_id: npa_tactic::GoalId,
    tactic_kind: MachineApiTacticKind,
    candidate_hash: Hash,
) -> MachineTacticBatchItemResponse {
    let message = match error {
        MachineSnapshotStoreError::SnapshotQuotaExceeded { .. } => {
            "unexpected snapshot quota error after scheduler handling".to_owned()
        }
        MachineSnapshotStoreError::Materialization(source) => {
            format!("next snapshot materialization failed: {source:?}")
        }
        MachineSnapshotStoreError::Lookup(source) => {
            format!("next snapshot store consistency check failed: {source:?}")
        }
    };
    batch_plain_item_error(
        candidate_id,
        Some(candidate_hash),
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::TacticExecution,
        message,
        goal_id,
        Some(tactic_kind),
    )
}

fn batch_plain_item_error(
    candidate_id: String,
    candidate_hash: Option<Hash>,
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    goal_id: npa_tactic::GoalId,
    tactic_kind: Option<MachineApiTacticKind>,
) -> MachineTacticBatchItemResponse {
    let message = message.into();
    let diagnostic = MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id: Some(goal_id),
        tactic_kind,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            machine_tactic_kind_for_api_kind(kind),
            message,
        )),
    };
    batch_error_item(candidate_id, candidate_hash, diagnostic)
}

fn batch_error_item(
    candidate_id: String,
    candidate_hash: Option<Hash>,
    diagnostic: MachineApiDiagnosticProjection,
) -> MachineTacticBatchItemResponse {
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("batch per-candidate diagnostics must satisfy machine API wire invariants");
    MachineTacticBatchItemResponse::Error {
        candidate_id,
        candidate_hash,
        diagnostic: wire.into(),
    }
}

fn batch_plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    goal_id: Option<npa_tactic::GoalId>,
) -> Box<MachineTacticBatchError> {
    let message = message.into();
    let diagnostic = MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id,
        tactic_kind: None,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            machine_tactic_kind_for_api_kind(kind),
            message,
        )),
    };
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("batch top-level diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachineTacticBatchError {
        diagnostic,
        response,
    })
}

fn plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    correlation: RunErrorCorrelation,
) -> Box<MachineTacticRunError> {
    plain_error_projected(kind, phase, message, correlation)
}

fn plain_error_with_goal(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    goal_id: npa_tactic::GoalId,
    correlation: RunErrorCorrelation,
) -> Box<MachineTacticRunError> {
    plain_error_projected(
        kind,
        phase,
        message,
        RunErrorCorrelation {
            goal_id: Some(goal_id),
            ..correlation
        },
    )
}

fn plain_error_projected(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    correlation: RunErrorCorrelation,
) -> Box<MachineTacticRunError> {
    let message = message.into();
    let diagnostic = MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id: correlation.goal_id,
        tactic_kind: correlation.tactic_kind,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            machine_tactic_kind_for_api_kind(kind),
            message,
        )),
    };
    error_response(
        diagnostic,
        correlation.unchanged_state_fingerprint,
        correlation.candidate_hash,
        correlation.deterministic_budget_hash,
    )
}

fn error_response(
    diagnostic: MachineApiDiagnosticProjection,
    unchanged_state_fingerprint: Option<Hash>,
    candidate_hash: Option<Hash>,
    deterministic_budget_hash: Option<Hash>,
) -> Box<MachineTacticRunError> {
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("run diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: MachineTacticRunErrorObject {
            diagnostic: wire,
            candidate_hash,
            deterministic_budget_hash,
        },
        endpoint_fields: MachineTacticRunErrorFields {
            unchanged_state_fingerprint,
        },
    }));
    Box::new(MachineTacticRunError {
        diagnostic,
        response,
    })
}

fn machine_tactic_kind_for_api_kind(kind: MachineApiErrorKind) -> MachineTacticDiagnosticKind {
    match kind {
        MachineApiErrorKind::GoalNotOpen => MachineTacticDiagnosticKind::UnknownGoal,
        MachineApiErrorKind::InvalidCandidate => MachineTacticDiagnosticKind::InvalidMachineTactic,
        MachineApiErrorKind::InvalidBudget => MachineTacticDiagnosticKind::TacticFuelExhausted {
            kind: npa_tactic::TacticFuelKind::TacticStep,
        },
        _ => MachineTacticDiagnosticKind::InvalidMachineProofState,
    }
}

pub(crate) fn candidate_tactic_kind_for_diagnostic(raw: &str) -> Option<MachineApiTacticKind> {
    let doc = JsonDocument::parse(raw).ok()?;
    let members = doc.root().object_members()?;
    let kind = members
        .iter()
        .filter(|member| member.key() == "kind")
        .exactly_one()
        .ok()?
        .value()
        .string_value()?;
    tactic_kind_from_wire(kind)
}

fn tactic_kind_from_wire(value: &str) -> Option<MachineApiTacticKind> {
    match value {
        "intro" => Some(MachineApiTacticKind::Intro),
        "exact" => Some(MachineApiTacticKind::Exact),
        "apply" => Some(MachineApiTacticKind::Apply),
        "rw" => Some(MachineApiTacticKind::Rw),
        "simp-lite" => Some(MachineApiTacticKind::SimpLite),
        "induction-nat" => Some(MachineApiTacticKind::InductionNat),
        "constructor" => Some(MachineApiTacticKind::Constructor),
        "cases" => Some(MachineApiTacticKind::Cases),
        "general-induction" => Some(MachineApiTacticKind::GeneralInduction),
        "refine" => Some(MachineApiTacticKind::Refine),
        "have" => Some(MachineApiTacticKind::Have),
        "suffices" => Some(MachineApiTacticKind::Suffices),
        "specialize" => Some(MachineApiTacticKind::Specialize),
        "revert" => Some(MachineApiTacticKind::Revert),
        "generalize" => Some(MachineApiTacticKind::Generalize),
        "change" => Some(MachineApiTacticKind::Change),
        "unfold" => Some(MachineApiTacticKind::Unfold),
        "congr" => Some(MachineApiTacticKind::Congr),
        "subst" => Some(MachineApiTacticKind::Subst),
        "contradiction" => Some(MachineApiTacticKind::Contradiction),
        "finite-decide" => Some(MachineApiTacticKind::FiniteDecide),
        "omega" => Some(MachineApiTacticKind::Omega),
        "ring" => Some(MachineApiTacticKind::Ring),
        "bitblast" => Some(MachineApiTacticKind::Bitblast),
        _ => None,
    }
}

trait ExactlyOne: Iterator + Sized {
    fn exactly_one(mut self) -> Result<Self::Item, ()> {
        let Some(item) = self.next() else {
            return Err(());
        };
        if self.next().is_some() {
            return Err(());
        }
        Ok(item)
    }
}

impl<I: Iterator> ExactlyOne for I {}

fn reject_duplicate_keys(
    members: &[JsonMember<'_>],
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> Result<(), MachineApiRequestError> {
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineApiRequestError::new(
                kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    Ok(())
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

fn required_value_member<'value, 'src>(
    members: &'value [JsonMember<'src>],
    field: &'static str,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> Result<&'value JsonValue<'src>, MachineApiRequestError> {
    member_value(members, field).ok_or_else(|| {
        MachineApiRequestError::new(
            kind,
            path.clone(),
            MachineApiRequestErrorReason::MissingField { field },
        )
    })
}

fn required_string_member<'value, 'src>(
    members: &'value [JsonMember<'src>],
    field: &'static str,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> Result<&'value str, MachineApiRequestError> {
    let value = required_value_member(members, field, kind, path)?;
    string_value(value, field, kind, path)
}

fn string_value<'value>(
    value: &'value JsonValue<'_>,
    field: &'static str,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> Result<&'value str, MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Err(null_field(field, kind, path));
    }
    value
        .string_value()
        .ok_or_else(|| type_mismatch(field, JsonFieldType::String, value, kind, path))
}

fn required_object_field<'value, 'src>(
    object: &crate::validation::ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value JsonValue<'src> {
    object
        .field(field)
        .expect("schema checked required object field")
}

fn required_array_field<'value, 'src>(
    object: &crate::validation::ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value [JsonValue<'src>] {
    object
        .field(field)
        .and_then(JsonValue::array_elements)
        .expect("schema checked required array field")
}

fn required_schema_string<'value, 'src>(
    object: &crate::validation::ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value str {
    object
        .field(field)
        .and_then(JsonValue::string_value)
        .expect("schema checked required string field")
}

fn required_u64(object: &crate::validation::ValidatedObject<'_, '_>, field: &str) -> u64 {
    object
        .field(field)
        .and_then(JsonValue::number_raw)
        .and_then(|raw| parse_strict_u64_token(raw, u64::MAX).ok())
        .expect("schema checked required u64 field")
}

fn optional_u64_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &str,
) -> Option<u64> {
    object
        .field(field)
        .and_then(JsonValue::number_raw)
        .and_then(|raw| parse_strict_u64_token(raw, u64::MAX).ok())
}

fn parse_optional_local_name_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Option<String>, MachineApiRequestError> {
    let value = object.field(field).expect("schema checked nullable string");
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let value = value
        .string_value()
        .expect("schema checked nullable string");
    validate_machine_local_name(value, field, path)?;
    Ok(Some(value.to_owned()))
}

fn parse_local_name_array(
    elements: &[JsonValue<'_>],
    field: &'static str,
    path: &JsonPath,
) -> Result<Vec<String>, MachineApiRequestError> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::with_capacity(elements.len());
    for (index, value) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let name = string_value(
            value,
            field,
            MachineApiErrorKind::InvalidCandidate,
            &item_path,
        )?;
        validate_machine_local_name(name, field, &item_path)?;
        if !seen.insert(name.to_owned()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidCandidate,
                item_path,
                MachineApiRequestErrorReason::DuplicateKey {
                    key: name.to_owned(),
                },
            ));
        }
        names.push(name.to_owned());
    }
    Ok(names)
}

fn optional_positive_u64(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Option<u64>, MachineApiRequestError> {
    let Some(value) = object.field(field) else {
        return Ok(None);
    };
    let raw = value
        .number_raw()
        .expect("schema checked optional u64 field");
    let parsed = parse_strict_u64_token(raw, u64::MAX).expect("schema checked optional u64 field");
    if parsed == 0 {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidSchedulerLimits,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            },
        ));
    }
    Ok(Some(parsed))
}

fn parse_renderable_name_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Name, MachineApiRequestError> {
    parse_machine_surface_renderable_name_wire(required_schema_string(object, field)).map_err(
        |_| invalid_string_literal(field, None, MachineApiErrorKind::InvalidCandidate, path),
    )
}

fn parse_hash_field(
    object: &crate::validation::ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Hash, MachineApiRequestError> {
    HashString::parse(required_schema_string(object, field))
        .map(HashString::digest)
        .map_err(|_| {
            invalid_string_literal(field, None, MachineApiErrorKind::InvalidCandidate, path)
        })
}

fn validate_machine_local_name(
    value: &str,
    field: &'static str,
    path: &JsonPath,
) -> Result<(), MachineApiRequestError> {
    if is_machine_local_name(value) {
        Ok(())
    } else {
        Err(invalid_string_literal(
            field,
            None,
            MachineApiErrorKind::InvalidCandidate,
            path,
        ))
    }
}

fn validate_machine_candidate_id(
    value: &str,
    path: &JsonPath,
) -> Result<(), MachineApiRequestError> {
    if (1..=64).contains(&value.len())
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
    {
        Ok(())
    } else {
        Err(invalid_string_literal(
            "candidate_id",
            None,
            MachineApiErrorKind::InvalidBatchPolicy,
            path,
        ))
    }
}

fn invalid_string_literal(
    field: &'static str,
    _tactic_kind: Option<MachineApiTacticKind>,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected: JsonFieldType::String,
            actual: JsonValueKind::String,
        },
    )
}

fn grammar_error(field: &'static str, kind: MachineApiErrorKind) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        JsonPath::root().field(field),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected: JsonFieldType::String,
            actual: JsonValueKind::String,
        },
    )
}

fn null_field(
    field: &'static str,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        path.clone(),
        MachineApiRequestErrorReason::NullField { field },
    )
}

fn type_mismatch(
    field: &'static str,
    expected: JsonFieldType,
    value: &JsonValue<'_>,
    kind: MachineApiErrorKind,
    path: &JsonPath,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected,
            actual: value.kind(),
        },
    )
}

pub(crate) fn json_path_display(path: &JsonPath) -> String {
    if path.elements.is_empty() {
        return "$".to_owned();
    }
    let mut out = "$".to_owned();
    for element in &path.elements {
        match element {
            JsonPathElement::Field(field) => {
                out.push('.');
                out.push_str(field);
            }
            JsonPathElement::Index(index) => {
                out.push('[');
                out.push_str(&index.to_string());
                out.push(']');
            }
        }
    }
    out
}

fn repair_encode_goal_id(out: &mut Vec<u8>, goal_id: Option<GoalId>) {
    match goal_id {
        Some(goal_id) => {
            out.push(1);
            repair_encode_u64(out, goal_id.0);
        }
        None => out.push(0),
    }
}

fn repair_encode_local_ref(out: &mut Vec<u8>, local: &RepairLocalRef) {
    repair_encode_string(out, &local.name);
}

fn repair_encode_global_ref(out: &mut Vec<u8>, global: &RepairGlobalRef) {
    repair_encode_len(out, global.name.0.len());
    for component in &global.name.0 {
        repair_encode_string(out, component);
    }
}

fn repair_encode_checked_term(out: &mut Vec<u8>, term: &RepairCheckedTermPayload) {
    out.extend_from_slice(&term.term_hash);
}

fn repair_encode_expr_path(out: &mut Vec<u8>, path: &ExprPath) {
    let segments = path.wire_segments();
    repair_encode_len(out, segments.len());
    for segment in segments {
        repair_encode_string(out, &segment);
    }
}

fn repair_encode_level(out: &mut Vec<u8>, level: &Level) {
    match normalize_level(level.clone()) {
        Level::Zero => out.push(0),
        Level::Succ(inner) => {
            out.push(1);
            repair_encode_level(out, &inner);
        }
        Level::Max(lhs, rhs) => {
            out.push(2);
            repair_encode_level(out, &lhs);
            repair_encode_level(out, &rhs);
        }
        Level::IMax(lhs, rhs) => {
            out.push(3);
            repair_encode_level(out, &lhs);
            repair_encode_level(out, &rhs);
        }
        Level::Param(name) => {
            out.push(4);
            repair_encode_string(out, &name);
        }
    }
}

fn repair_encode_string(out: &mut Vec<u8>, value: &str) {
    repair_encode_len(out, value.len());
    out.extend_from_slice(value.as_bytes());
}

fn repair_encode_len(out: &mut Vec<u8>, len: usize) {
    repair_encode_u64(out, len as u64);
}

fn repair_encode_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn repair_encode_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn repair_hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    hasher.update(payload);
    hasher.finalize().into()
}

fn failure_memory_hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    hasher.update([0]);
    hasher.update(payload);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::format_goal_id_wire;
    use crate::{
        create_machine_session, format_hash_string, get_machine_snapshot,
        run_machine_verify_request, MachineSnapshotGetOk,
    };
    use npa_cert::{
        build_module_cert, encode_module_cert, verify_module_cert, AxiomPolicy, CoreModule,
        VerifierSession,
    };
    use npa_kernel::{ConstructorDecl, Decl, Expr, InductiveDecl};

    fn default_options_json() -> String {
        r#"{
          "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
          "allow_axioms": [],
          "tactic_options": {
            "simp_rules": [],
            "eq_family": null,
            "nat_family": null,
            "max_simp_rewrite_steps": 100,
            "max_open_goals": 32,
            "max_metas": 64
          }
        }"#
        .to_owned()
    }

    fn minimal_session_json(theorem_type: &str) -> String {
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"{theorem_type}"}}
              }},
              "import_closure":[],
              "imports":[],
              "checked_current_decls":[],
              "options":{}
            }}"#,
            default_options_json()
        )
    }

    fn budget_json() -> &'static str {
        r#"{
          "max_tactic_steps":64,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#
    }

    fn term_json(source: &str) -> String {
        format!(r#"{{"source":"{source}"}}"#)
    }

    fn imported_head_json(name: &str, hash_byte: u8) -> String {
        format!(
            r#"{{"imported":{{"name":"{name}","decl_interface_hash":"{}"}}}}"#,
            format_hash_string(&[hash_byte; 32])
        )
    }

    fn occurrence_path_json(indices: &[u64]) -> String {
        let indices = indices.iter().map(u64::to_string).collect::<Vec<_>>();
        format!(r#"{{"indices":[{}]}}"#, indices.join(","))
    }

    fn repair_term(byte: u8) -> RepairCheckedTermPayload {
        RepairCheckedTermPayload {
            term_hash: [byte; 32],
        }
    }

    fn repair_global(name: &str) -> RepairGlobalRef {
        RepairGlobalRef {
            name: Name::from_dotted(name),
        }
    }

    fn repair_local(name: &str) -> RepairLocalRef {
        RepairLocalRef {
            name: name.to_owned(),
        }
    }

    fn parse_wire_candidate(candidate: &str) -> MachineTacticCandidate {
        parse_candidate_wire_shape_at(
            candidate,
            candidate_tactic_kind_for_diagnostic(candidate),
            &JsonPath::root().field("candidate"),
        )
        .expect("candidate wire shape should parse")
    }

    fn repair_generator_state(theorem_type: Expr) -> MachineProofState {
        crate::adapter::machine_tactic_start_machine_proof(
            npa_tactic::MachineProofSpec {
                module: Name::from_dotted("Repair"),
                theorem_name: Name::from_dotted("Repair.thm"),
                source_index: 0,
                universe_params: Vec::new(),
                theorem_type,
            },
            Vec::new(),
            Vec::new(),
            npa_tactic::MachineTacticOptions::default(),
        )
        .expect("repair generator fixture state should start")
        .state
    }

    fn repair_generator_context<'a>(
        state: &'a MachineProofState,
        diagnostic: &'a MachineApiDiagnosticProjection,
    ) -> RepairGenerationContext<'a> {
        RepairGenerationContext {
            state,
            state_fingerprint: state.fingerprint,
            diagnostic,
            deterministic_budget: TacticBudget::default(),
            profile_version: MachineTacticProfileVersion::StructuralV2,
            required_features: STRUCTURAL_V2_REQUIRED_FEATURES,
            max_proposals: DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN,
        }
    }

    fn repair_chain_context<'a>(
        state: &'a MachineProofState,
        diagnostic: &'a MachineApiDiagnosticProjection,
        limits: RepairChainLimits,
    ) -> RepairChainRunContext<'a> {
        RepairChainRunContext {
            state,
            state_fingerprint: state.fingerprint,
            diagnostic,
            deterministic_budget: TacticBudget::default(),
            profile_version: MachineTacticProfileVersion::StructuralV2,
            required_features: STRUCTURAL_V2_REQUIRED_FEATURES,
            limits,
        }
    }

    fn repair_projection(
        kind: MachineApiErrorKind,
        goal_id: Option<GoalId>,
        upstream: MachineTacticDiagnostic,
    ) -> MachineApiDiagnosticProjection {
        MachineApiDiagnosticProjection {
            kind,
            phase: MachineApiDiagnosticPhase::CandidateValidation,
            retryable: false,
            goal_id,
            tactic_kind: None,
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
            source_message: "display text must be ignored".to_owned(),
            upstream: MachineApiUpstreamDiagnostic::MachineTactic(upstream),
        }
    }

    fn proposal_operator_kinds(proposals: &[RepairGeneratedProposal]) -> Vec<RepairOperatorKind> {
        proposals
            .iter()
            .filter_map(|proposal| proposal.operator.as_ref().map(RepairOperator::kind))
            .collect()
    }

    fn diagnostic_budget_report() -> npa_tactic::DiagnosticBudgetReport {
        npa_tactic::DiagnosticBudget::default().report(npa_tactic::DiagnosticBudgetUsage::default())
    }

    #[test]
    fn repair_operator_every_design_variant_is_represented_and_hashable() {
        let operators = vec![
            RepairOperator::ReverseRewrite {
                goal_id: Some(GoalId(0)),
            },
            RepairOperator::SelectRewriteOccurrence {
                goal_id: Some(GoalId(0)),
                path: ExprPath::parse_wire_segments(&["RewriteOccurrence(0)".to_owned()]).unwrap(),
            },
            RepairOperator::InstantiateArgument {
                goal_id: Some(GoalId(0)),
                binder: 1,
                term: repair_term(1),
            },
            RepairOperator::InstantiateUniverse {
                goal_id: Some(GoalId(0)),
                param: "u".to_owned(),
                level: Level::param("u"),
            },
            RepairOperator::IntroduceBinder {
                goal_id: Some(GoalId(0)),
            },
            RepairOperator::SpecializeHypothesis {
                goal_id: Some(GoalId(0)),
                local: repair_local("h"),
                args: vec![repair_term(2)],
            },
            RepairOperator::Unfold {
                goal_id: Some(GoalId(0)),
                constant: repair_global("Std.Nat.add"),
            },
            RepairOperator::Fold {
                goal_id: Some(GoalId(0)),
                constant: repair_global("Std.Nat.add"),
            },
            RepairOperator::InsertEqTransport {
                goal_id: Some(GoalId(0)),
            },
            RepairOperator::Generalize {
                goal_id: Some(GoalId(0)),
                term: repair_term(3),
            },
            RepairOperator::Revert {
                goal_id: Some(GoalId(0)),
                local: repair_local("h"),
            },
            RepairOperator::ChangeGoal {
                goal_id: Some(GoalId(0)),
                target: repair_term(4),
            },
            RepairOperator::ReduceSimpSet {
                goal_id: Some(GoalId(0)),
                remove: vec![repair_global("Std.Nat.add_zero")],
            },
            RepairOperator::SwitchStrategy {
                goal_id: Some(GoalId(0)),
                profile: RepairStrategyProfile::SmallerSimp,
            },
        ];
        let mut kinds = BTreeSet::new();
        let mut hashes = BTreeSet::new();
        for operator in &operators {
            kinds.insert(operator.kind());
            hashes.insert(repair_operator_hash(operator));
            assert!(!repair_operator_canonical_bytes(operator).is_empty());
        }
        assert_eq!(kinds.len(), 14);
        assert_eq!(hashes.len(), 14);
        assert!(operators
            .iter()
            .all(
                |operator| repair_operator_proposal_category(operator.kind())
                    == RepairProposalCategory::ProofStateRepair
            ));
        assert_eq!(
            RepairProposalCategory::ImportChangeProposal.as_str(),
            "import_change_proposal"
        );
        assert_eq!(
            RepairProposalCategory::AxiomChangeProposal.as_str(),
            "axiom_change_proposal"
        );
    }

    #[test]
    fn repair_operator_parses_structured_universe_payload_and_hashes_stably() {
        let term_hash = format_hash_string(&[7; 32]);
        let source = format!(
            r#"{{
              "schema":"{REPAIR_OPERATOR_SCHEMA}",
              "operator":"InstantiateArgument",
              "payload":{{"goal_id":"g0","binder":2,"term":{{"term_hash":"{term_hash}"}}}}
            }}"#
        );
        let parsed = parse_repair_operator_json(&source).unwrap();
        assert_eq!(
            parsed,
            RepairOperator::InstantiateArgument {
                goal_id: Some(GoalId(0)),
                binder: 2,
                term: repair_term(7),
            }
        );
        assert_eq!(
            repair_operator_hash(&parsed),
            repair_operator_hash(&parse_repair_operator_json(&source).unwrap())
        );

        let universe = parse_repair_operator_json(&format!(
            r#"{{
              "schema":"{REPAIR_OPERATOR_SCHEMA}",
              "operator":"InstantiateUniverse",
              "payload":{{"goal_id":"g0","param":"u","level":"max u 0"}}
            }}"#
        ))
        .unwrap();
        assert_eq!(
            universe,
            RepairOperator::InstantiateUniverse {
                goal_id: Some(GoalId(0)),
                param: "u".to_owned(),
                level: Level::Max(
                    Box::new(Level::Param("u".to_owned())),
                    Box::new(Level::Zero)
                ),
            }
        );
    }

    #[test]
    fn repair_operator_rejects_trusted_claims_and_free_form_tactic_text() {
        let top_level_trust = format!(
            r#"{{
              "schema":"{REPAIR_OPERATOR_SCHEMA}",
              "operator":"ReverseRewrite",
              "payload":{{}},
              "trusted_evidence":{{"status":"verified"}}
            }}"#
        );
        assert!(parse_repair_operator_json(&top_level_trust).is_err());

        let payload_trust = format!(
            r#"{{
              "schema":"{REPAIR_OPERATOR_SCHEMA}",
              "operator":"ChangeGoal",
              "payload":{{
                "target":{{"term_hash":"{}"}},
                "proof_acceptance_state":"certificate_verified"
              }}
            }}"#,
            format_hash_string(&[9; 32])
        );
        assert!(parse_repair_operator_json(&payload_trust).is_err());

        let tactic_text = format!(
            r#"{{
              "schema":"{REPAIR_OPERATOR_SCHEMA}",
              "operator":"ReverseRewrite",
              "payload":{{"goal_id":"g0","tactic_text":"rw [h]"}}
            }}"#
        );
        assert!(parse_repair_operator_json(&tactic_text).is_err());
    }

    #[test]
    fn repair_operator_policy_rejects_unrelated_and_noop_repairs() {
        let reverse = RepairOperator::ReverseRewrite {
            goal_id: Some(GoalId(0)),
        };
        assert_eq!(
            validate_repair_operator_batch(
                RepairDiagnosticCategory::UniverseMismatch,
                std::slice::from_ref(&reverse),
                DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN
            ),
            Err(RepairOperatorValidationError::DisallowedOperator {
                category: RepairDiagnosticCategory::UniverseMismatch,
                operator: RepairOperatorKind::ReverseRewrite,
            })
        );
        assert_eq!(
            validate_repair_operator_batch(
                RepairDiagnosticCategory::UnsupportedMachineTactic,
                &[reverse],
                DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN
            ),
            Err(RepairOperatorValidationError::DisallowedOperator {
                category: RepairDiagnosticCategory::UnsupportedMachineTactic,
                operator: RepairOperatorKind::ReverseRewrite,
            })
        );
        assert_eq!(
            repair_policy_allowed_operators(RepairDiagnosticCategory::InvalidReplayPlan),
            &[] as &[RepairOperatorKind]
        );
        assert_eq!(
            repair_policy_allowed_operators(RepairDiagnosticCategory::KernelRejectedAfterVerify),
            &[] as &[RepairOperatorKind]
        );

        let universe = RepairOperator::InstantiateUniverse {
            goal_id: Some(GoalId(0)),
            param: "u".to_owned(),
            level: Level::param("u"),
        };
        assert_eq!(
            validate_repair_operator_batch(
                RepairDiagnosticCategory::UniverseMismatch,
                &[universe],
                DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN
            ),
            Ok(())
        );
        assert!(!repair_operator_is_allowed(
            RepairDiagnosticCategory::ExpectedPiType,
            RepairOperatorKind::IntroduceBinder
        ));
    }

    #[test]
    fn repair_operator_batch_rejects_duplicates_and_budget_overflow() {
        let switch = RepairOperator::SwitchStrategy {
            goal_id: Some(GoalId(0)),
            profile: RepairStrategyProfile::SmallerSimp,
        };
        assert_eq!(
            validate_repair_operator_batch(
                RepairDiagnosticCategory::BudgetExceeded,
                &[switch.clone(), switch.clone()],
                DEFAULT_MAX_REPAIR_OPERATOR_BATCH_LEN
            ),
            Err(RepairOperatorValidationError::DuplicateOperator {
                operator_hash: repair_operator_hash(&switch),
            })
        );
        assert_eq!(
            validate_repair_operator_batch(RepairDiagnosticCategory::BudgetExceeded, &[switch], 0),
            Err(RepairOperatorValidationError::BudgetExceeded { actual: 1, max: 0 })
        );
    }

    fn failure_memory_test_key(byte: u8) -> FailureMemoryKey {
        FailureMemoryKey::new(
            [byte; 32],
            [byte.wrapping_add(1); 32],
            [byte.wrapping_add(2); 32],
            MachineApiErrorKind::TypeMismatch,
            [byte.wrapping_add(3); 32],
        )
    }

    fn failure_memory_test_record(
        key: FailureMemoryKey,
        import_identity_hash: Hash,
        clock: u64,
    ) -> FailureMemoryRecord {
        FailureMemoryRecord::new(
            key,
            import_identity_hash,
            FailureMemoryObservation::new(clock),
            Some("structural-test-profile".to_owned()),
            FailureMemoryBudgetClass::Normal,
        )
    }

    fn failure_memory_test_attempt(
        byte: u8,
        outcome: FailureMemoryRepairOutcome,
        clock: u64,
    ) -> FailureMemoryRepairAttempt {
        FailureMemoryRepairAttempt {
            repair_operator_hash: [byte; 32],
            outcome,
            observed_at: FailureMemoryObservation::new(clock),
        }
    }

    #[test]
    fn failure_memory_key_shape_and_schema_are_deterministic() {
        let candidate = MachineTacticCandidate::Intro {
            name: "h".to_owned(),
        };
        let changed_candidate = MachineTacticCandidate::Intro {
            name: "h2".to_owned(),
        };
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "first display message",
            ),
        );
        diagnostic.expected_hash = Some([7; 32]);
        diagnostic.actual_hash = Some([8; 32]);
        diagnostic.tactic_kind = Some(MachineApiTacticKind::Exact);

        let shape = failure_memory_candidate_shape_hash(&candidate);
        assert_eq!(shape, failure_memory_candidate_shape_hash(&candidate));
        assert_ne!(
            shape,
            failure_memory_candidate_shape_hash(&changed_candidate)
        );

        let key = failure_memory_key_from_projection([1; 32], [2; 32], shape, &diagnostic)
            .expect("structured diagnostic should hash");
        let same = failure_memory_key_from_projection([1; 32], [2; 32], shape, &diagnostic)
            .expect("structured diagnostic should hash");
        assert_eq!(key, same);
        assert_eq!(
            failure_memory_key_hash(&key),
            failure_memory_key_hash(&same)
        );
        assert!(failure_memory_key_canonical_bytes(&key)
            .windows(FAILURE_MEMORY_SCHEMA.len())
            .any(|window| window == FAILURE_MEMORY_SCHEMA.as_bytes()));
    }

    #[test]
    fn failure_memory_store_suppresses_exact_failures_and_exports_hard_negatives() {
        let key = failure_memory_test_key(10);
        let context = FailureMemoryLookupContext {
            environment_hash: key.environment_hash,
            import_identity_hash: [90; 32],
            goal_fingerprint: key.goal_fingerprint,
        };
        let mut store = FailureMemoryStore::new();

        assert_eq!(
            store.suppression_decision(&key, &context, FailureMemorySuppressionPolicy::default()),
            FailureMemorySuppressionDecision::Allow
        );

        let repair_hash = repair_operator_hash(&RepairOperator::SwitchStrategy {
            goal_id: Some(GoalId(0)),
            profile: RepairStrategyProfile::SmallerSimp,
        });
        let record = failure_memory_test_record(key.clone(), context.import_identity_hash, 1)
            .with_repair_attempt(FailureMemoryRepairAttempt {
                repair_operator_hash: repair_hash,
                outcome: FailureMemoryRepairOutcome::CandidateRejected,
                observed_at: FailureMemoryObservation::new(2),
            })
            .with_alternative_used_in_final_proof([77; 32]);
        assert_eq!(
            store.observe(record),
            FailureMemoryMergeReport {
                inserted: 1,
                merged: 0,
            }
        );

        assert_eq!(
            store.suppression_decision(&key, &context, FailureMemorySuppressionPolicy::default()),
            FailureMemorySuppressionDecision::SuppressExactRepeatedFailure {
                key: key.clone(),
                occurrence_count: 1,
            }
        );

        let mut nearby_key = key.clone();
        nearby_key.diagnostic_hash = [11; 32];
        assert_eq!(
            store.suppression_decision(
                &nearby_key,
                &context,
                FailureMemorySuppressionPolicy::default()
            ),
            FailureMemorySuppressionDecision::Allow
        );

        let hard_negatives = store.hard_negatives(1);
        assert_eq!(hard_negatives.len(), 1);
        assert_eq!(hard_negatives[0].key, key);
        assert_eq!(hard_negatives[0].repair_operator_hashes, vec![repair_hash]);
        assert_eq!(
            hard_negatives[0].alternative_used_in_final_proof,
            Some([77; 32])
        );
    }

    #[test]
    fn failure_memory_stale_suggestions_do_not_suppress_current_candidates() {
        let old_key = failure_memory_test_key(20);
        let old_import = [31; 32];
        let record = failure_memory_test_record(old_key.clone(), old_import, 1);
        let mut store = FailureMemoryStore::new();
        store.observe(record);

        let current_key = FailureMemoryKey {
            environment_hash: [99; 32],
            goal_fingerprint: old_key.goal_fingerprint,
            candidate_shape_hash: old_key.candidate_shape_hash,
            error_kind: old_key.error_kind,
            diagnostic_hash: old_key.diagnostic_hash,
        };
        let context = FailureMemoryLookupContext {
            environment_hash: current_key.environment_hash,
            import_identity_hash: [32; 32],
            goal_fingerprint: current_key.goal_fingerprint,
        };

        let decision = store.suppression_decision(
            &current_key,
            &context,
            FailureMemorySuppressionPolicy::default(),
        );

        assert!(matches!(
            decision,
            FailureMemorySuppressionDecision::AllowWithStaleSuggestions { .. }
        ));
        let FailureMemorySuppressionDecision::AllowWithStaleSuggestions { stale } = decision else {
            unreachable!("checked above")
        };
        assert_eq!(stale.len(), 1);
        assert_eq!(stale[0].key, old_key);
        assert_eq!(
            stale[0].reasons,
            vec![
                FailureMemoryStaleReason::EnvironmentHash,
                FailureMemoryStaleReason::ImportIdentity
            ]
        );
    }

    #[test]
    fn failure_memory_merge_is_deterministic_saturating_and_deduplicates_attempts() {
        let key = failure_memory_test_key(40);
        let import_identity_hash = [41; 32];
        let mut early = failure_memory_test_record(key.clone(), import_identity_hash, 1)
            .with_repair_attempt(failure_memory_test_attempt(
                1,
                FailureMemoryRepairOutcome::CandidateRejected,
                3,
            ))
            .with_successful_repair([10; 32]);
        early.occurrence_count = u64::MAX - 1;

        let mut late = failure_memory_test_record(key.clone(), import_identity_hash, 5)
            .with_repair_attempt(failure_memory_test_attempt(
                1,
                FailureMemoryRepairOutcome::CandidateRejected,
                7,
            ))
            .with_repair_attempt(failure_memory_test_attempt(
                2,
                FailureMemoryRepairOutcome::RepairSucceeded,
                8,
            ))
            .with_successful_repair([11; 32]);
        late.occurrence_count = 10;

        let mut left = FailureMemoryStore::new();
        left.observe(early.clone());
        let mut right = FailureMemoryStore::new();
        right.observe(late.clone());
        left.merge(&right);

        let mut reverse_left = FailureMemoryStore::new();
        reverse_left.observe(late);
        let mut reverse_right = FailureMemoryStore::new();
        reverse_right.observe(early);
        reverse_left.merge(&reverse_right);

        assert_eq!(left, reverse_left);
        let merged = left.record(&key).unwrap();
        assert_eq!(merged.occurrence_count, u64::MAX);
        assert_eq!(merged.first_observation, FailureMemoryObservation::new(1));
        assert_eq!(merged.last_observation, FailureMemoryObservation::new(5));
        assert_eq!(merged.repair_attempts.len(), 2);
        assert_eq!(merged.successful_repair, Some([11; 32]));
    }

    #[test]
    fn failure_memory_store_is_advisory_only_for_tactic_validation() {
        let state = repair_generator_state(type0_expr());
        let before = state.fingerprint;
        let candidate = MachineTacticCandidate::Intro {
            name: "bad-name".to_owned(),
        };
        let first = machine_tactic_validate_machine_tactic_candidate_for_state(
            &state,
            GoalId(0),
            candidate.clone(),
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect_err("invalid candidate name should fail before tactic execution");

        let key = failure_memory_key_from_projection(
            [52; 32],
            proof_candidate_goal_fingerprint(state.fingerprint, GoalId(0)),
            failure_memory_candidate_shape_hash(&candidate),
            &first.diagnostic,
        )
        .expect("diagnostic should hash");
        let mut store = FailureMemoryStore::new();
        store.observe(failure_memory_test_record(key, [53; 32], 1));

        let second = machine_tactic_validate_machine_tactic_candidate_for_state(
            &state,
            GoalId(0),
            candidate,
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect_err("failure memory must not change validation");

        assert_eq!(state.fingerprint, before);
        assert_eq!(first.diagnostic.kind, second.diagnostic.kind);
        assert_eq!(
            first.diagnostic.diagnostic_hash().unwrap(),
            second.diagnostic.diagnostic_hash().unwrap()
        );
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn minimal_failing_artifact_identity_is_deterministic() {
        let state = repair_generator_state(prop_expr());
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Prop"),
        };

        let first = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate.clone(),
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let second = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate,
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("minimal failing artifact should be deterministic");

        assert_eq!(first, second);
        assert!(first.sidecar_only);
        assert_eq!(
            first.proof_acceptance_state,
            MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly
        );
        assert_eq!(
            first.structured_diagnostic.kind,
            MachineApiErrorKind::TypeMismatch
        );
        assert_eq!(
            first.expected_policy.expected_phase,
            first.structured_diagnostic.phase
        );
        assert_eq!(
            minimal_failing_artifact_hash(&first).unwrap(),
            first.artifact_hash
        );
        assert_eq!(
            first.candidate_payload_hash,
            crate::ai_search::ai_search_candidate_payload_hash(&first.candidate)
        );
        assert_ne!(
            first.candidate_payload_hash,
            failure_memory_candidate_shape_hash(&first.candidate)
        );
        validate_minimal_failing_artifact_identity(&first)
            .expect("fresh minimal failing artifact should validate");
    }

    #[test]
    fn minimal_failing_artifact_rejects_modified_candidate_budget_and_import_hashes() {
        let state = repair_generator_state(prop_expr());
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Prop"),
        };
        let artifact = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate,
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");

        let mut modified_candidate = artifact.clone();
        modified_candidate.candidate = MachineTacticCandidate::Intro {
            name: "p".to_owned(),
        };
        assert!(matches!(
            validate_minimal_failing_artifact_identity(&modified_candidate),
            Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch { .. })
        ));

        let mut modified_budget = artifact.clone();
        modified_budget.deterministic_budget.max_tactic_steps += 1;
        assert!(matches!(
            validate_minimal_failing_artifact_identity(&modified_budget),
            Err(MinimalFailingArtifactError::DeterministicBudgetHashMismatch { .. })
        ));

        let import_fixture = constructor_fixture_module();
        let imported_state = crate::adapter::machine_tactic_start_machine_proof(
            npa_tactic::MachineProofSpec {
                module: Name::from_dotted("ImportedArtifact"),
                theorem_name: Name::from_dotted("ImportedArtifact.thm"),
                source_index: 0,
                universe_params: Vec::new(),
                theorem_type: prop_expr(),
            },
            vec![import_fixture.import_ref.clone()],
            Vec::new(),
            npa_tactic::MachineTacticOptions::default(),
        )
        .expect("imported fixture state should start")
        .state;
        let imported_artifact = build_minimal_failing_artifact(
            &imported_state,
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("imported type-mismatch should build a minimal failing artifact");
        assert_eq!(imported_artifact.imports.len(), 1);

        let mut modified_import = imported_artifact.clone();
        modified_import.imports[0].export_hash = [9; 32];
        assert_ne!(
            minimal_failing_artifact_hash(&modified_import).unwrap(),
            imported_artifact.artifact_hash
        );
        assert!(matches!(
            validate_minimal_failing_artifact_identity(&modified_import),
            Err(MinimalFailingArtifactError::ArtifactHashMismatch { .. })
        ));
    }

    fn compact_diagnostic_from_minimal(
        artifact: &MinimalFailingArtifact,
    ) -> MachineApiCompactErrorWire {
        MachineApiCompactErrorWire {
            error_kind: artifact.structured_diagnostic.kind,
            phase: artifact.structured_diagnostic.phase,
            diagnostic_hash: artifact.structured_diagnostic.diagnostic_hash,
            retryable: artifact.structured_diagnostic.retryable,
            goal_id: artifact.structured_diagnostic.goal_id,
            tactic_kind: artifact.structured_diagnostic.tactic_kind,
            primary_name: artifact.structured_diagnostic.primary_name.clone(),
            primary_axiom_ref: artifact.structured_diagnostic.primary_axiom_ref.clone(),
            expected_hash: artifact.structured_diagnostic.expected_hash,
            actual_hash: artifact.structured_diagnostic.actual_hash,
        }
    }

    #[test]
    fn focused_replay_artifact_schema_and_identity_are_deterministic() {
        let state = repair_generator_state(prop_expr());
        let minimal = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");

        let first = build_focused_replay_failure_artifact(
            "Proofs.Ai.Focus",
            Name::from_dotted("Proofs.Ai.Focus.thm"),
            minimal.clone(),
        )
        .expect("focused replay artifact should build");
        let second = build_focused_replay_failure_artifact(
            "Proofs.Ai.Focus",
            Name::from_dotted("Proofs.Ai.Focus.thm"),
            minimal,
        )
        .expect("focused replay artifact should be deterministic");

        assert_eq!(first, second);
        assert_eq!(first.schema, FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA);
        assert!(!first.trusted);
        assert!(first.sidecar_only);
        assert_eq!(
            first.proof_acceptance_state,
            MinimalFailingArtifactProofAcceptanceState::DiagnosticOnly
        );
        assert!(
            !first
                .source_free_verifier_baseline
                .certificate_verification_claim
        );
        assert!(
            !first
                .source_free_verifier_baseline
                .independent_checker_claim
        );
        for excluded in FOCUSED_REPLAY_FAILURE_EXCLUDED_FIELDS {
            assert!(
                first.excluded_fields.iter().any(|field| field == excluded),
                "focused replay artifact should exclude {excluded}"
            );
        }
        for forbidden in [
            "raw_prompts",
            "model_completions",
            "secrets",
            "broad_source_context",
            "theorem_graph_scores",
            "unrelated_filesystem_paths",
        ] {
            assert!(first.excluded_fields.contains(&forbidden.to_owned()));
        }
        assert_eq!(
            focused_replay_failure_artifact_hash(&first).unwrap(),
            first.artifact_hash
        );
        validate_focused_replay_failure_artifact_identity(&first)
            .expect("fresh focused replay artifact should validate");

        let base_hash = first.artifact_hash;
        let mut changed_import = first.clone();
        changed_import
            .minimal_failing_artifact
            .imports
            .push(MinimalFailingArtifactImport {
                module: "Proofs.Ai.Import".to_owned(),
                export_hash: [1; 32],
                certificate_hash: [2; 32],
                visible: true,
                exports: Vec::new(),
                certified_env_decl_hashes: Vec::new(),
            });
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_import).unwrap(),
            base_hash
        );

        let mut changed_declaration = first.clone();
        changed_declaration.declaration_interface.declaration =
            Name::from_dotted("Proofs.Ai.Focus.other");
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_declaration).unwrap(),
            base_hash
        );

        let mut changed_local_context = first.clone();
        changed_local_context
            .minimal_failing_artifact
            .local_context
            .push(MinimalFailingArtifactLocal {
                name: "h".to_owned(),
                type_hash: [3; 32],
                value_hash: None,
            });
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_local_context).unwrap(),
            base_hash
        );

        let mut changed_target = first.clone();
        changed_target.minimal_failing_artifact.target_hash = [4; 32];
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_target).unwrap(),
            base_hash
        );

        let mut changed_candidate = first.clone();
        changed_candidate.minimal_failing_artifact.candidate = MachineTacticCandidate::Intro {
            name: "p".to_owned(),
        };
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_candidate).unwrap(),
            base_hash
        );

        let mut changed_budget = first.clone();
        changed_budget
            .minimal_failing_artifact
            .deterministic_budget
            .max_tactic_steps += 1;
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_budget).unwrap(),
            base_hash
        );

        let mut changed_policy = first.clone();
        changed_policy
            .minimal_failing_artifact
            .expected_policy
            .expected_retryable = !changed_policy
            .minimal_failing_artifact
            .expected_policy
            .expected_retryable;
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_policy).unwrap(),
            base_hash
        );

        let mut changed_diagnostic = first;
        changed_diagnostic
            .minimal_failing_artifact
            .structured_diagnostic
            .diagnostic_hash = [5; 32];
        assert_ne!(
            focused_replay_failure_artifact_hash(&changed_diagnostic).unwrap(),
            base_hash
        );
    }

    #[test]
    fn focused_replay_artifact_rejects_modified_payload_budget_snapshot_import_and_diagnostic() {
        let state = repair_generator_state(prop_expr());
        let minimal = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let artifact = build_focused_replay_failure_artifact(
            "Proofs.Ai.Focus",
            Name::from_dotted("Proofs.Ai.Focus.thm"),
            minimal,
        )
        .expect("focused replay artifact should build");

        let mut modified_candidate = artifact.clone();
        modified_candidate.minimal_failing_artifact.candidate = MachineTacticCandidate::Intro {
            name: "p".to_owned(),
        };
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&modified_candidate),
            Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch { .. })
        ));

        let mut modified_budget = artifact.clone();
        modified_budget
            .minimal_failing_artifact
            .deterministic_budget
            .max_tactic_steps += 1;
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&modified_budget),
            Err(MinimalFailingArtifactError::DeterministicBudgetHashMismatch { .. })
        ));

        let mut stale_snapshot = artifact.clone();
        stale_snapshot.minimal_failing_artifact.state_fingerprint = [7; 32];
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&stale_snapshot),
            Err(MinimalFailingArtifactError::ArtifactHashMismatch { .. })
        ));

        let mut stale_declaration_interface = artifact.clone();
        stale_declaration_interface
            .declaration_interface
            .declaration_interface_hash = [6; 32];
        stale_declaration_interface.artifact_hash =
            focused_replay_failure_artifact_hash(&stale_declaration_interface).unwrap();
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&stale_declaration_interface),
            Err(MinimalFailingArtifactError::DeclarationInterfaceHashMismatch { .. })
        ));

        let mut changed_diagnostic = artifact.clone();
        changed_diagnostic
            .minimal_failing_artifact
            .structured_diagnostic
            .diagnostic_hash = [8; 32];
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&changed_diagnostic),
            Err(MinimalFailingArtifactError::DiagnosticHashMismatch { .. })
        ));

        let mut trust_claim = artifact;
        trust_claim
            .source_free_verifier_baseline
            .independent_checker_claim = true;
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&trust_claim),
            Err(MinimalFailingArtifactError::ProofAcceptanceStateClaim)
        ));

        let import_fixture = constructor_fixture_module();
        let imported_state = crate::adapter::machine_tactic_start_machine_proof(
            npa_tactic::MachineProofSpec {
                module: Name::from_dotted("ImportedFocusedReplay"),
                theorem_name: Name::from_dotted("ImportedFocusedReplay.thm"),
                source_index: 0,
                universe_params: Vec::new(),
                theorem_type: prop_expr(),
            },
            vec![import_fixture.import_ref.clone()],
            Vec::new(),
            npa_tactic::MachineTacticOptions::default(),
        )
        .expect("imported fixture state should start")
        .state;
        let imported_minimal = build_minimal_failing_artifact(
            &imported_state,
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("imported type-mismatch should build a minimal failing artifact");
        let imported_artifact = build_focused_replay_failure_artifact(
            "ImportedFocusedReplay",
            Name::from_dotted("ImportedFocusedReplay.thm"),
            imported_minimal,
        )
        .expect("imported focused replay artifact should build");
        assert_eq!(imported_artifact.minimal_failing_artifact.imports.len(), 1);

        let mut baseline_import_hash_mismatch = imported_artifact.clone();
        baseline_import_hash_mismatch
            .source_free_verifier_baseline
            .import_identity_hash = [10; 32];
        baseline_import_hash_mismatch.artifact_hash =
            focused_replay_failure_artifact_hash(&baseline_import_hash_mismatch).unwrap();
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&baseline_import_hash_mismatch),
            Err(MinimalFailingArtifactError::ImportIdentityHashMismatch { .. })
        ));

        let mut checked_current_hash_mismatch = imported_artifact.clone();
        checked_current_hash_mismatch
            .source_free_verifier_baseline
            .checked_current_decl_interface_hash = [11; 32];
        checked_current_hash_mismatch.artifact_hash =
            focused_replay_failure_artifact_hash(&checked_current_hash_mismatch).unwrap();
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&checked_current_hash_mismatch),
            Err(MinimalFailingArtifactError::CheckedCurrentDeclInterfaceHashMismatch { .. })
        ));

        let mut excluded_fields_mismatch = imported_artifact.clone();
        excluded_fields_mismatch.excluded_fields.pop();
        excluded_fields_mismatch.artifact_hash =
            focused_replay_failure_artifact_hash(&excluded_fields_mismatch).unwrap();
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&excluded_fields_mismatch),
            Err(MinimalFailingArtifactError::ExcludedFieldsMismatch)
        ));

        let mut import_hash_mismatch = imported_artifact;
        import_hash_mismatch.minimal_failing_artifact.imports[0].export_hash = [9; 32];
        assert!(matches!(
            validate_focused_replay_failure_artifact_identity(&import_hash_mismatch),
            Err(MinimalFailingArtifactError::ArtifactHashMismatch { .. })
        ));
    }

    #[test]
    fn focused_replay_tactic_batch_failure_helper_builds_structured_artifact() {
        let state = repair_generator_state(prop_expr());
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Prop"),
        };
        let budget = TacticBudget::default();
        let minimal = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate.clone(),
            budget,
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let diagnostic = compact_diagnostic_from_minimal(&minimal);

        let first = build_focused_replay_failure_artifact_from_tactic_batch(
            FocusedReplayTacticBatchFailureInput {
                module: "Proofs.Ai.Focus",
                declaration: Name::from_dotted("Proofs.Ai.Focus.thm"),
                state: &state,
                state_fingerprint: state.fingerprint,
                goal_id: GoalId(0),
                candidate: candidate.clone(),
                candidate_payload_hash: Some(minimal.candidate_payload_hash),
                deterministic_budget: budget,
                deterministic_budget_hash: Some(minimal.deterministic_budget_hash),
                profile_version: MachineTacticProfileVersion::StructuralV2,
                required_features: STRUCTURAL_V2_REQUIRED_FEATURES,
                diagnostic: &diagnostic,
            },
        )
        .expect("focused replay artifact should build from typed batch failure fields");
        let second = build_focused_replay_failure_artifact_from_tactic_batch(
            FocusedReplayTacticBatchFailureInput {
                module: "Proofs.Ai.Focus",
                declaration: Name::from_dotted("Proofs.Ai.Focus.thm"),
                state: &state,
                state_fingerprint: state.fingerprint,
                goal_id: GoalId(0),
                candidate,
                candidate_payload_hash: Some(minimal.candidate_payload_hash),
                deterministic_budget: budget,
                deterministic_budget_hash: Some(minimal.deterministic_budget_hash),
                profile_version: MachineTacticProfileVersion::StructuralV2,
                required_features: STRUCTURAL_V2_REQUIRED_FEATURES,
                diagnostic: &diagnostic,
            },
        )
        .expect("focused replay artifact should be deterministic");
        let expected = build_focused_replay_failure_artifact(
            "Proofs.Ai.Focus",
            Name::from_dotted("Proofs.Ai.Focus.thm"),
            minimal,
        )
        .expect("baseline focused replay artifact should build");

        assert_eq!(first, second);
        assert_eq!(first, expected);
        assert_eq!(first.schema, FOCUSED_REPLAY_FAILURE_ARTIFACT_SCHEMA);
        assert!(!first.trusted);
        assert!(first.sidecar_only);
        validate_focused_replay_failure_artifact_identity(&first)
            .expect("typed batch focused replay artifact should validate");
    }

    #[test]
    fn focused_replay_tactic_batch_failure_helper_rejects_mismatched_inputs() {
        let state = repair_generator_state(prop_expr());
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Prop"),
        };
        let budget = TacticBudget::default();
        let minimal = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate.clone(),
            budget,
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let diagnostic = compact_diagnostic_from_minimal(&minimal);

        let build = |candidate_payload_hash,
                     deterministic_budget_hash,
                     state_fingerprint,
                     diagnostic: &MachineApiCompactErrorWire| {
            build_focused_replay_failure_artifact_from_tactic_batch(
                FocusedReplayTacticBatchFailureInput {
                    module: "Proofs.Ai.Focus",
                    declaration: Name::from_dotted("Proofs.Ai.Focus.thm"),
                    state: &state,
                    state_fingerprint,
                    goal_id: GoalId(0),
                    candidate: candidate.clone(),
                    candidate_payload_hash,
                    deterministic_budget: budget,
                    deterministic_budget_hash,
                    profile_version: MachineTacticProfileVersion::StructuralV2,
                    required_features: STRUCTURAL_V2_REQUIRED_FEATURES,
                    diagnostic,
                },
            )
        };

        assert!(matches!(
            build(
                Some([9; 32]),
                Some(minimal.deterministic_budget_hash),
                state.fingerprint,
                &diagnostic
            ),
            Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch { .. })
        ));
        assert!(matches!(
            build(
                Some(minimal.candidate_payload_hash),
                Some([8; 32]),
                state.fingerprint,
                &diagnostic
            ),
            Err(MinimalFailingArtifactError::DeterministicBudgetHashMismatch { .. })
        ));
        assert!(matches!(
            build(
                Some(minimal.candidate_payload_hash),
                Some(minimal.deterministic_budget_hash),
                [7; 32],
                &diagnostic
            ),
            Err(MinimalFailingArtifactError::StateFingerprintMismatch { .. })
        ));

        let mut wrong_tactic_kind = diagnostic.clone();
        wrong_tactic_kind.tactic_kind = Some(MachineApiTacticKind::Intro);
        assert!(matches!(
            build(
                Some(minimal.candidate_payload_hash),
                Some(minimal.deterministic_budget_hash),
                state.fingerprint,
                &wrong_tactic_kind
            ),
            Err(MinimalFailingArtifactError::DiagnosticPolicyMismatch)
        ));

        let mut stale_diagnostic = diagnostic;
        stale_diagnostic.diagnostic_hash = [6; 32];
        assert!(matches!(
            build(
                Some(minimal.candidate_payload_hash),
                Some(minimal.deterministic_budget_hash),
                state.fingerprint,
                &stale_diagnostic
            ),
            Err(MinimalFailingArtifactError::DiagnosticHashMismatch { .. })
        ));
    }

    #[test]
    fn minimal_failing_artifact_hard_negative_export_is_advisory_and_deterministic() {
        let state = repair_generator_state(prop_expr());
        let artifact = build_minimal_failing_artifact(
            &state,
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let key = FailureMemoryKey::new(
            [31; 32],
            artifact.goal_fingerprint,
            failure_memory_candidate_shape_hash(&artifact.candidate),
            artifact.structured_diagnostic.kind,
            artifact.structured_diagnostic.diagnostic_hash,
        );
        let mut record = failure_memory_test_record(key.clone(), [32; 32], 1).with_repair_attempt(
            failure_memory_test_attempt(33, FailureMemoryRepairOutcome::CandidateRejected, 2),
        );
        record.occurrence_count = 2;
        let mut store = FailureMemoryStore::new();
        store.observe(record);

        let stale_context = FailureMemoryLookupContext {
            environment_hash: [99; 32],
            import_identity_hash: [98; 32],
            goal_fingerprint: [97; 32],
        };
        let expected_pi = repair_projection(
            MachineApiErrorKind::ExpectedPiType,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::ExpectedPiTarget,
                "expected-pi display text ignored",
            ),
        );
        let invalid_proposals =
            generate_repair_proposals(&repair_generator_context(&state, &expected_pi));
        assert!(invalid_proposals.iter().any(|proposal| matches!(
            proposal.validation,
            RepairProposalValidation::Rejected { .. }
        )));
        let chain = RepairChainReport {
            termination_reason: RepairChainTerminationReason::RepeatedDiagnosticHash {
                diagnostic_hash: artifact.structured_diagnostic.diagnostic_hash,
                count: 2,
                max: 1,
            },
            budget: RepairChainBudgetReport::default(),
            steps: Vec::new(),
            initial_state_fingerprint: state.fingerprint,
            final_state_fingerprint: state.fingerprint,
            final_diagnostic_hash: Some(artifact.structured_diagnostic.diagnostic_hash),
        };
        let artifacts = vec![artifact.clone()];
        let chains = vec![chain];

        let first = build_hard_negative_export(HardNegativeExportInput {
            failure_memory: &store,
            lookup_context: Some(&stale_context),
            artifacts: &artifacts,
            invalid_repair_proposals: &invalid_proposals,
            repair_chains: &chains,
            min_occurrence_count: 2,
        })
        .expect("hard negative export should build");
        let second = build_hard_negative_export(HardNegativeExportInput {
            failure_memory: &store,
            lookup_context: Some(&stale_context),
            artifacts: &artifacts,
            invalid_repair_proposals: &invalid_proposals,
            repair_chains: &chains,
            min_occurrence_count: 2,
        })
        .expect("hard negative export should be deterministic");

        assert_eq!(first, second);
        assert_eq!(hard_negative_export_hash(&first), first.export_hash);
        let kinds = first
            .records
            .iter()
            .map(|record| record.kind)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            kinds,
            BTreeSet::from([
                HardNegativeKind::ExactRepeatedFailure,
                HardNegativeKind::StaleMemorySuggestion,
                HardNegativeKind::InvalidRepairProposal,
                HardNegativeKind::NoProgressRepairLoop,
            ])
        );
        assert!(first
            .records
            .iter()
            .filter(|record| record.kind == HardNegativeKind::ExactRepeatedFailure)
            .all(|record| record.artifact_hash == Some(artifact.artifact_hash)));
        assert!(hard_negative_export_canonical_bytes(&first)
            .windows(HARD_NEGATIVE_EXPORT_SCHEMA.len())
            .any(|window| window == HARD_NEGATIVE_EXPORT_SCHEMA.as_bytes()));
    }

    #[test]
    fn repair_generator_type_mismatch_is_deterministic_and_empty_retrieval_is_neutral() {
        use std::cell::Cell;

        struct CountingEmptyRetrieval<'a>(&'a Cell<u32>);
        impl RepairRetrievalAdapter for CountingEmptyRetrieval<'_> {
            fn repair_candidates(
                &self,
                request: &RepairRetrievalRequest<'_>,
            ) -> Vec<MachineTacticCandidate> {
                assert_eq!(request.category, RepairDiagnosticCategory::TypeMismatch);
                self.0.set(self.0.get() + 1);
                Vec::new()
            }
        }

        let initial = repair_generator_state(Expr::pi("p", prop_expr(), Expr::bvar(0)));
        let (state, delta) = npa_tactic::run_machine_tactic_with_budget(
            &initial,
            npa_tactic::MachineTactic::Intro {
                goal_id: GoalId(0),
                name: "p".to_owned(),
            },
            TacticBudget::default(),
        )
        .expect("intro should create a local type-mismatch fixture");
        let goal_id = delta.added_goals[0];
        let before = state.fingerprint;
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(goal_id),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "first diagnostic text",
            ),
        );
        diagnostic.expected_hash = Some(core_expr_hash(&prop_expr()));
        let context = repair_generator_context(&state, &diagnostic);

        let first = generate_repair_proposals(&context);
        let second = generate_repair_proposals(&context);

        assert_eq!(first, second);
        assert_eq!(state.fingerprint, before);
        assert_eq!(
            proposal_operator_kinds(&first),
            vec![
                RepairOperatorKind::SpecializeHypothesis,
                RepairOperatorKind::SwitchStrategy
            ]
        );
        assert!(matches!(
            first[0].operator.as_ref().unwrap(),
            RepairOperator::SpecializeHypothesis { local, args, .. }
                if local.name == "p" && args.is_empty()
        ));

        let count = Cell::new(0);
        let with_empty_retrieval =
            generate_repair_proposals_with_retrieval(&context, &CountingEmptyRetrieval(&count));
        assert_eq!(count.get(), 1);
        assert_eq!(with_empty_retrieval, first);
    }

    #[test]
    fn repair_generator_expected_pi_and_noop_categories_do_not_execute_candidates() {
        let state = repair_generator_state(type0_expr());
        let expected_pi = repair_projection(
            MachineApiErrorKind::ExpectedPiType,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::ExpectedPiTarget,
                "first diagnostic text",
            ),
        );
        let context = repair_generator_context(&state, &expected_pi);

        let proposals = generate_repair_proposals(&context);

        assert_eq!(
            proposal_operator_kinds(&proposals),
            vec![RepairOperatorKind::SwitchStrategy]
        );
        assert!(matches!(
            proposals[0].validation,
            RepairProposalValidation::Rejected {
                error: RepairProposalValidationError::OperatorNotConvertible {
                    operator: RepairOperatorKind::SwitchStrategy
                }
            }
        ));

        let disallowed = validate_repair_operator_as_candidate(
            &context,
            RepairDiagnosticCategory::UniverseMismatch,
            RepairOperator::ReverseRewrite {
                goal_id: Some(GoalId(0)),
            },
        );
        assert!(matches!(
            disallowed,
            RepairProposalValidation::Rejected {
                error: RepairProposalValidationError::DisallowedOperator {
                    category: RepairDiagnosticCategory::UniverseMismatch,
                    operator: RepairOperatorKind::ReverseRewrite
                }
            }
        ));

        for kind in [
            MachineApiErrorKind::UnsupportedTactic,
            MachineApiErrorKind::UnknownName,
            MachineApiErrorKind::InvalidReplayPlan,
            MachineApiErrorKind::VerifyFailed,
        ] {
            let no_op = repair_projection(
                kind,
                Some(GoalId(0)),
                MachineTacticDiagnostic::new(
                    MachineTacticDiagnosticKind::UnsupportedMachineTactic,
                    "second diagnostic text",
                ),
            );
            assert!(
                generate_repair_proposals(&repair_generator_context(&state, &no_op)).is_empty()
            );
        }
    }

    #[test]
    fn repair_generator_rewrite_no_progress_uses_structured_payloads_only() {
        let state = repair_generator_state(type0_expr());
        let rewrite = npa_tactic::RewriteDiagnostic {
            subset_kind: npa_tactic::UnificationConflictSubsetKind::Reduced,
            sites: vec![
                npa_tactic::RewriteDiagnosticSite {
                    id: npa_tactic::RewriteDiagnosticId(1),
                    kind: npa_tactic::RewriteDiagnosticKind::NoProgress,
                    target_kind: npa_tactic::RewriteDiagnosticTargetKind::Goal,
                    local_name: None,
                    path: vec!["RewriteOccurrence(2)".to_owned()],
                    direction: RewriteDirection::Forward,
                    matched_side: RewriteSite::EqTargetLeft,
                    replacement_side: RewriteSite::EqTargetRight,
                    occurrence_index: Some(2),
                    required_unfoldings: Vec::new(),
                    congruence_depth: 0,
                    expected_hash: Some([7; 32]),
                    actual_hash: Some([8; 32]),
                    repair_operators: vec![npa_tactic::RewriteRepairOperator::ReduceSimpSet],
                },
                npa_tactic::RewriteDiagnosticSite {
                    id: npa_tactic::RewriteDiagnosticId(0),
                    kind: npa_tactic::RewriteDiagnosticKind::NoProgress,
                    target_kind: npa_tactic::RewriteDiagnosticTargetKind::Goal,
                    local_name: None,
                    path: vec!["RewriteOccurrence(0)".to_owned()],
                    direction: RewriteDirection::Forward,
                    matched_side: RewriteSite::EqTargetLeft,
                    replacement_side: RewriteSite::EqTargetRight,
                    occurrence_index: Some(0),
                    required_unfoldings: vec!["Scratch.f".to_owned()],
                    congruence_depth: 0,
                    expected_hash: Some([7; 32]),
                    actual_hash: Some([8; 32]),
                    repair_operators: vec![
                        npa_tactic::RewriteRepairOperator::Unfold,
                        npa_tactic::RewriteRepairOperator::ReduceSimpSet,
                    ],
                },
            ],
            forward_valid: true,
            backward_valid: false,
            forward_matches_goal: false,
            backward_matches_goal: false,
            forward_matches_hypothesis: false,
            backward_matches_hypothesis: false,
            rejected_by_budget_or_progress: false,
            complete_scan: true,
            no_progress_reason: Some(npa_tactic::RewriteNoProgressReason::EqReflFailed),
            budget_report: diagnostic_budget_report(),
        };
        let diagnostic = repair_projection(
            MachineApiErrorKind::SimpNoProgress,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::SimpNoProgress,
                "first diagnostic text",
            )
            .with_rewrite_diagnostic(rewrite),
        );
        let context = repair_generator_context(&state, &diagnostic);

        let proposals = generate_repair_proposals(&context);

        assert_eq!(
            proposal_operator_kinds(&proposals),
            vec![
                RepairOperatorKind::ReduceSimpSet,
                RepairOperatorKind::Unfold
            ]
        );
        assert_eq!(
            proposals[0].provenance.diagnostic_path,
            vec!["RewriteOccurrence(0)".to_owned()]
        );
        assert!(matches!(
            proposals[0].validation,
            RepairProposalValidation::Candidate { .. }
        ));
        assert!(matches!(
            proposals[1].validation,
            RepairProposalValidation::Rejected {
                error: RepairProposalValidationError::OperatorNotConvertible {
                    operator: RepairOperatorKind::Unfold
                }
            }
        ));
    }

    #[test]
    fn repair_generator_universe_mismatch_budget_and_implicit_categories_are_gated() {
        let state = repair_generator_state(type0_expr());
        let universe = npa_tactic::UniverseDiagnostic {
            subset_kind: npa_tactic::UnificationConflictSubsetKind::Reduced,
            core_kind: npa_tactic::UniverseDiagnosticCoreKind::Reduced,
            constraints: Vec::new(),
            unresolved_metas: Vec::new(),
            candidate_instantiations: vec![npa_tactic::UniverseInstantiationCandidate {
                param: "u".to_owned(),
                level: Level::zero(),
                source_path: vec!["AppFunction".to_owned(), "UniverseArg(0)".to_owned()],
                valid: true,
                rejection_kind: None,
            }],
            repair_operators: vec![npa_tactic::UniverseRepairOperator::InstantiateUniverse],
            complete_graph: true,
            budget_report: diagnostic_budget_report(),
        };
        let universe_projection = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::UniverseArgumentMismatch,
                "first diagnostic text",
            )
            .with_universe_diagnostic(universe),
        );
        let universe_context = repair_generator_context(&state, &universe_projection);

        let universe_proposals = generate_repair_proposals(&universe_context);

        assert_eq!(
            repair_diagnostic_category_from_projection(&universe_projection),
            Some(RepairDiagnosticCategory::UniverseMismatch)
        );
        assert_eq!(
            proposal_operator_kinds(&universe_proposals),
            vec![RepairOperatorKind::InstantiateUniverse]
        );
        assert!(matches!(
            universe_proposals[0].validation,
            RepairProposalValidation::Rejected {
                error: RepairProposalValidationError::OperatorNotConvertible {
                    operator: RepairOperatorKind::InstantiateUniverse
                }
            }
        ));

        let mut implicit_projection = repair_projection(
            MachineApiErrorKind::ImplicitArgumentRequired,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::ImplicitArgumentRequired,
                "second diagnostic text",
            ),
        );
        implicit_projection.expected_hash = Some([42; 32]);
        let implicit =
            generate_repair_proposals(&repair_generator_context(&state, &implicit_projection));
        assert_eq!(
            proposal_operator_kinds(&implicit),
            vec![RepairOperatorKind::InstantiateArgument]
        );
        assert!(matches!(
            implicit[0].validation,
            RepairProposalValidation::Rejected {
                error: RepairProposalValidationError::OperatorNotConvertible {
                    operator: RepairOperatorKind::InstantiateArgument
                }
            }
        ));

        let budget_projection = repair_projection(
            MachineApiErrorKind::BudgetExceeded,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TacticFuelExhausted {
                    kind: npa_tactic::TacticFuelKind::Rewrite,
                },
                "third diagnostic text",
            ),
        );
        let budget =
            generate_repair_proposals(&repair_generator_context(&state, &budget_projection));
        assert_eq!(
            proposal_operator_kinds(&budget),
            vec![
                RepairOperatorKind::ReduceSimpSet,
                RepairOperatorKind::SwitchStrategy
            ]
        );
        assert!(budget.iter().any(|proposal| matches!(
            proposal.validation,
            RepairProposalValidation::Candidate { .. }
        )));
    }

    #[test]
    fn repair_chain_repeated_candidate_payload_stops_without_state_mutation() {
        let state = repair_generator_state(type0_expr());
        let before = state.fingerprint;
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::BudgetExceeded,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TacticFuelExhausted {
                    kind: npa_tactic::TacticFuelKind::Rewrite,
                },
                "first display text",
            ),
        );
        diagnostic.tactic_kind = Some(MachineApiTacticKind::SimpLite);
        let limits = RepairChainLimits {
            max_repeated_candidate_payload_hash_count: 1,
            ..RepairChainLimits::default()
        };

        let report = run_repair_chain(&repair_chain_context(&state, &diagnostic, limits))
            .expect("repair chain should hash diagnostic");

        assert!(matches!(
            report.termination_reason,
            RepairChainTerminationReason::RepeatedCandidatePayloadHash {
                count: 2,
                max: 1,
                ..
            }
        ));
        assert_eq!(report.final_state_fingerprint, before);
        assert_eq!(state.fingerprint, before);
        assert_eq!(report.budget.consumed_tactic_budget, 0);
        assert_eq!(report.budget.considered_candidate_count, 2);
    }

    #[test]
    fn repair_chain_repeated_diagnostic_hash_stops_after_failed_repairs() {
        struct ExactMismatchRetrieval;
        impl RepairRetrievalAdapter for ExactMismatchRetrieval {
            fn repair_candidates(
                &self,
                request: &RepairRetrievalRequest<'_>,
            ) -> Vec<MachineTacticCandidate> {
                assert_eq!(request.category, RepairDiagnosticCategory::TypeMismatch);
                vec![MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("Prop"),
                }]
            }
        }

        let state = repair_generator_state(prop_expr());
        let before = state.fingerprint;
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "initial type-mismatch text",
            ),
        );
        diagnostic.phase = MachineApiDiagnosticPhase::TacticExecution;
        diagnostic.tactic_kind = Some(MachineApiTacticKind::Exact);
        diagnostic.expected_hash = Some(core_expr_hash(&prop_expr()));
        diagnostic.actual_hash = Some(core_expr_hash(&type0_expr()));
        let limits = RepairChainLimits {
            max_repair_depth: 4,
            max_repeated_candidate_payload_hash_count: usize::MAX,
            max_total_candidates: 8,
            ..RepairChainLimits::default()
        };

        let report = run_repair_chain_with_retrieval(
            &repair_chain_context(&state, &diagnostic, limits),
            &ExactMismatchRetrieval,
        )
        .expect("repair chain should hash diagnostic");

        assert!(
            matches!(
                report.termination_reason,
                RepairChainTerminationReason::RepeatedDiagnosticHash {
                    count: 2,
                    max: 1,
                    ..
                }
            ),
            "{report:#?}"
        );
        assert_eq!(report.final_state_fingerprint, before);
        assert_eq!(state.fingerprint, before);
        assert!(report.budget.consumed_tactic_budget >= 1);
        assert!(report
            .steps
            .iter()
            .any(|step| matches!(step.outcome, RepairChainStepOutcome::CandidateFailed { .. })));
    }

    #[test]
    fn repair_chain_total_candidate_limit_stops_before_execution() {
        struct IntroRetrieval;
        impl RepairRetrievalAdapter for IntroRetrieval {
            fn repair_candidates(
                &self,
                request: &RepairRetrievalRequest<'_>,
            ) -> Vec<MachineTacticCandidate> {
                assert_eq!(request.category, RepairDiagnosticCategory::TypeMismatch);
                vec![MachineTacticCandidate::Intro {
                    name: "p".to_owned(),
                }]
            }
        }

        let state = repair_generator_state(Expr::pi("p", prop_expr(), Expr::bvar(0)));
        let before = state.fingerprint;
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "type mismatch text",
            ),
        );
        diagnostic.tactic_kind = Some(MachineApiTacticKind::Intro);
        diagnostic.expected_hash = Some(core_expr_hash(&type0_expr()));
        diagnostic.actual_hash = Some(core_expr_hash(&prop_expr()));
        let limits = RepairChainLimits {
            max_total_candidates: 0,
            max_repeated_candidate_payload_hash_count: usize::MAX,
            ..RepairChainLimits::default()
        };

        let report = run_repair_chain_with_retrieval(
            &repair_chain_context(&state, &diagnostic, limits),
            &IntroRetrieval,
        )
        .expect("repair chain should hash diagnostic");

        assert_eq!(
            report.termination_reason,
            RepairChainTerminationReason::MaxTotalCandidates { max: 0 }
        );
        assert_eq!(report.final_state_fingerprint, before);
        assert_eq!(state.fingerprint, before);
        assert_eq!(report.budget.consumed_tactic_budget, 0);
    }

    #[test]
    fn repair_chain_zero_depth_reports_initial_diagnostic_hash() {
        let state = repair_generator_state(type0_expr());
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::BudgetExceeded,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TacticFuelExhausted {
                    kind: npa_tactic::TacticFuelKind::Rewrite,
                },
                "zero-depth display text",
            ),
        );
        diagnostic.tactic_kind = Some(MachineApiTacticKind::SimpLite);
        let limits = RepairChainLimits {
            max_repair_depth: 0,
            ..RepairChainLimits::default()
        };

        let report = run_repair_chain(&repair_chain_context(&state, &diagnostic, limits))
            .expect("repair chain should hash diagnostic");

        assert_eq!(
            report.termination_reason,
            RepairChainTerminationReason::MaxRepairDepth { max: 0 }
        );
        assert_eq!(
            report.final_diagnostic_hash,
            Some(diagnostic.diagnostic_hash().unwrap())
        );
        assert_eq!(report.budget.consumed_diagnostic_budget, 0);
        assert_eq!(report.budget.consumed_tactic_budget, 0);
    }

    #[test]
    fn repair_chain_goal_growth_limit_is_transactional() {
        struct IntroRetrieval;
        impl RepairRetrievalAdapter for IntroRetrieval {
            fn repair_candidates(
                &self,
                request: &RepairRetrievalRequest<'_>,
            ) -> Vec<MachineTacticCandidate> {
                assert_eq!(request.category, RepairDiagnosticCategory::TypeMismatch);
                vec![MachineTacticCandidate::Intro {
                    name: "p".to_owned(),
                }]
            }
        }

        let state = repair_generator_state(Expr::pi("p", prop_expr(), Expr::bvar(0)));
        let before = state.fingerprint;
        let mut diagnostic = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "type mismatch text",
            ),
        );
        diagnostic.tactic_kind = Some(MachineApiTacticKind::Intro);
        diagnostic.expected_hash = Some(core_expr_hash(&type0_expr()));
        diagnostic.actual_hash = Some(core_expr_hash(&prop_expr()));
        let limits = RepairChainLimits {
            max_generated_goals: 0,
            max_repeated_candidate_payload_hash_count: usize::MAX,
            ..RepairChainLimits::default()
        };

        let report = run_repair_chain_with_retrieval(
            &repair_chain_context(&state, &diagnostic, limits),
            &IntroRetrieval,
        )
        .expect("repair chain should hash diagnostic");

        assert_eq!(
            report.termination_reason,
            RepairChainTerminationReason::MaxGeneratedGoals {
                max: 0,
                attempted: 1,
            }
        );
        assert_eq!(report.final_state_fingerprint, before);
        assert_eq!(state.fingerprint, before);
        assert_eq!(report.budget.consumed_tactic_budget, 1);
        assert_eq!(report.budget.generated_goal_count, 0);
    }

    fn structural_v2_candidate_fixtures() -> Vec<(&'static str, String)> {
        let ctor = imported_head_json("Std.Bool.true", 1);
        let recursor = imported_head_json("Std.Nat.rec", 2);
        let unfold_const = imported_head_json("Scratch.f", 3);
        let occurrence = occurrence_path_json(&[0, 1]);
        vec![
            (
                "constructor",
                r#"{"kind":"constructor","selection":{"mode":"auto"},"max_new_goals":2}"#
                    .to_owned(),
            ),
            (
                "constructor",
                format!(
                    r#"{{"kind":"constructor","selection":{{"mode":"explicit","constructor":{ctor}}}}}"#
                ),
            ),
            (
                "cases",
                r#"{"kind":"cases","major_local":"h","motive":null,"branch_names":["l","r"],"max_new_goals":2}"#.to_owned(),
            ),
            (
                "general-induction",
                format!(
                    r#"{{"kind":"general-induction","major_local":"n","recursor":{recursor},"motive":null,"generalized_locals":["x"],"branch_names":["z","s"],"max_new_goals":2}}"#
                ),
            ),
            (
                "refine",
                format!(r#"{{"kind":"refine","term":{},"max_holes":3}}"#, term_json("Prop")),
            ),
            (
                "have",
                format!(
                    r#"{{"kind":"have","name":"h","type":{},"proof":{{"mode":"child-goal"}},"insertion":"after-current"}}"#,
                    term_json("Prop")
                ),
            ),
            (
                "suffices",
                format!(
                    r#"{{"kind":"suffices","target":{},"proof":{{"mode":"term","term":{}}},"continuation":"prove-intermediate-first"}}"#,
                    term_json("Prop"),
                    term_json("Prop")
                ),
            ),
            (
                "specialize",
                format!(
                    r#"{{"kind":"specialize","local_name":"h","universe_args":[],"args":[{{"mode":"term","term":{}}}],"result_name":null,"result_policy":"add-local"}}"#,
                    term_json("Prop")
                ),
            ),
            (
                "revert",
                r#"{"kind":"revert","locals":["h"],"dependency_policy":"exact"}"#.to_owned(),
            ),
            (
                "generalize",
                format!(
                    r#"{{"kind":"generalize","target":{{"mode":"goal"}},"term":{},"occurrences":[{occurrence}],"name_hint":"x"}}"#,
                    term_json("Prop")
                ),
            ),
            (
                "change",
                format!(
                    r#"{{"kind":"change","target":{{"mode":"local","name":"h"}},"replacement":{},"occurrences":[]}}"#,
                    term_json("Prop")
                ),
            ),
            (
                "unfold",
                format!(
                    r#"{{"kind":"unfold","target":{{"mode":"goal"}},"constant":{unfold_const},"occurrences":[{occurrence}],"max_delta_steps":4}}"#
                ),
            ),
            (
                "congr",
                r#"{"kind":"congr","target":{"mode":"goal"},"max_depth":2,"max_new_goals":3}"#
                    .to_owned(),
            ),
            (
                "subst",
                format!(
                    r#"{{"kind":"subst","equality_local":"heq","target":{{"mode":"goal"}},"direction":"forward","occurrences":[{occurrence}]}}"#
                ),
            ),
            (
                "contradiction",
                r#"{"kind":"contradiction","mode":"auto","major_local":null}"#.to_owned(),
            ),
            ("finite-decide", r#"{"kind":"finite-decide"}"#.to_owned()),
            ("omega", r#"{"kind":"omega"}"#.to_owned()),
            ("ring", r#"{"kind":"ring"}"#.to_owned()),
            ("bitblast", r#"{"kind":"bitblast"}"#.to_owned()),
        ]
    }

    struct ApiFixtureModule {
        module: Name,
        export_hash: Hash,
        certificate_hash: Hash,
        certificate_hex: String,
        import_ref: npa_tactic::VerifiedImportRef,
    }

    fn prop_expr() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0_expr() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn fixture_module(core_module: CoreModule) -> ApiFixtureModule {
        let cert = build_module_cert(core_module, &[]).expect("fixture cert should build");
        let bytes = encode_module_cert(&cert).expect("fixture cert should encode");
        let mut verifier_session = VerifierSession::new();
        let verified = verify_module_cert(&bytes, &mut verifier_session, &AxiomPolicy::normal())
            .expect("fixture cert should verify source-free");
        let import_ref = npa_tactic::VerifiedImportRef::from_verified_module(&verified)
            .expect("fixture module should become tactic import");

        ApiFixtureModule {
            module: verified.module().clone(),
            export_hash: verified.export_hash(),
            certificate_hash: verified.certificate_hash(),
            certificate_hex: hex_bytes(&bytes),
            import_ref,
        }
    }

    fn session_json_with_imports(theorem_type: &str, imports: &[ApiFixtureModule]) -> String {
        let import_closure = imports
            .iter()
            .map(|fixture| {
                format!(
                    r#"{{
                      "module":"{}",
                      "expected_export_hash":"{}",
                      "expected_certificate_hash":"{}",
                      "certificate":{{
                        "encoding":"npa.certificate.canonical.v0.1.hex",
                        "bytes":"{}"
                      }}
                    }}"#,
                    fixture.module.as_dotted(),
                    format_hash_string(&fixture.export_hash),
                    format_hash_string(&fixture.certificate_hash),
                    fixture.certificate_hex
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let direct_imports = imports
            .iter()
            .map(|fixture| {
                format!(
                    r#"{{
                      "module":"{}",
                      "expected_export_hash":"{}",
                      "expected_certificate_hash":"{}"
                    }}"#,
                    fixture.module.as_dotted(),
                    format_hash_string(&fixture.export_hash),
                    format_hash_string(&fixture.certificate_hash)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"{theorem_type}"}}
              }},
              "import_closure":[{import_closure}],
              "imports":[{direct_imports}],
              "checked_current_decls":[],
              "options":{}
            }}"#,
            default_options_json()
        )
    }

    fn fixture_imported_head_json(fixture: &ApiFixtureModule, name: &str) -> String {
        let decl_interface_hash = fixture
            .import_ref
            .exports()
            .iter()
            .find(|export| export.name == Name::from_dotted(name))
            .unwrap_or_else(|| panic!("fixture export {name} should exist"))
            .decl_interface_hash;
        format!(
            r#"{{"imported":{{"name":"{name}","decl_interface_hash":"{}"}}}}"#,
            format_hash_string(&decl_interface_hash)
        )
    }

    fn constructor_fixture_module() -> ApiFixtureModule {
        fixture_module(CoreModule {
            name: Name::from_dotted("Ctor"),
            declarations: vec![Decl::Inductive {
                name: "Ctor.True".to_owned(),
                universe_params: Vec::new(),
                ty: prop_expr(),
                data: Box::new(InductiveDecl::new(
                    "Ctor.True",
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    Level::zero(),
                    vec![ConstructorDecl::new(
                        "Ctor.True.intro",
                        Expr::konst("Ctor.True", Vec::new()),
                    )],
                    None,
                )),
            }],
        })
    }

    fn case_color() -> Expr {
        Expr::konst("Case.Color", Vec::new())
    }

    fn case_color_base() -> InductiveDecl {
        InductiveDecl::new(
            "Case.Color",
            Vec::new(),
            Vec::new(),
            Vec::new(),
            npa_kernel::type0(),
            vec![
                ConstructorDecl::new("Case.Color.red", case_color()),
                ConstructorDecl::new("Case.Color.blue", case_color()),
            ],
            None,
        )
    }

    fn cases_fixture_module() -> ApiFixtureModule {
        fixture_module(CoreModule {
            name: Name::from_dotted("Case"),
            declarations: vec![Decl::Inductive {
                name: "Case.Color".to_owned(),
                universe_params: Vec::new(),
                ty: type0_expr(),
                data: Box::new(
                    npa_cert::generate_inductive_artifacts_v1(&case_color_base())
                        .expect("case inductive artifacts should generate"),
                ),
            }],
        })
    }

    fn nat_fixture_module() -> ApiFixtureModule {
        fixture_module(CoreModule {
            name: Name::from_dotted("Std.Nat.Basic"),
            declarations: vec![Decl::Inductive {
                name: "Nat".to_owned(),
                universe_params: Vec::new(),
                ty: type0_expr(),
                data: Box::new(npa_kernel::nat_inductive()),
            }],
        })
    }

    fn hex_bytes(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            out.push(hex_digit(byte >> 4));
            out.push(hex_digit(byte & 0x0f));
        }
        out
    }

    fn hex_digit(nibble: u8) -> char {
        match nibble {
            0..=9 => (b'0' + nibble) as char,
            10..=15 => (b'a' + (nibble - 10)) as char,
            _ => unreachable!("nibble should be four bits"),
        }
    }

    fn run_json_at(
        session: &MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
        goal_id: npa_tactic::GoalId,
        candidate: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"{}",
              "candidate":{},
              "deterministic_budget":{}
            }}"#,
            session.session_id.wire(),
            snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            format_goal_id_wire(goal_id),
            candidate,
            budget_json()
        )
    }

    fn verify_json_at(
        session: &MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "mode":"certificate"
            }}"#,
            session.session_id.wire(),
            snapshot_id.wire(),
            format_hash_string(&state_fingerprint)
        )
    }

    fn run_tactic_at(
        session: &mut MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
        goal_id: npa_tactic::GoalId,
        candidate: &str,
    ) -> MachineTacticRunSuccessFields {
        let response = run_machine_tactic_request(
            &run_json_at(session, snapshot_id, state_fingerprint, goal_id, candidate),
            session,
        )
        .unwrap_or_else(|err| panic!("candidate should run: {candidate}: {err:?}"));
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected tactic success: {candidate}");
        };
        ok.endpoint_fields
    }

    fn run_on_result(
        session: &mut MachineProofSession,
        previous: &MachineTacticRunSuccessFields,
        goal_id: npa_tactic::GoalId,
        candidate: &str,
    ) -> MachineTacticRunSuccessFields {
        run_tactic_at(
            session,
            previous.result.next_snapshot_id,
            previous.result.next_state_fingerprint,
            goal_id,
            candidate,
        )
    }

    fn assert_source_free_verified(
        session: &MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
    ) {
        let response = run_machine_verify_request(
            &verify_json_at(session, snapshot_id, state_fingerprint),
            session,
        )
        .expect("closed API tactic fixture should verify source-free");
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected source-free verify success");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Verified);
        assert_eq!(ok.endpoint_fields.root_axioms_used, Vec::new());
        assert_eq!(ok.endpoint_fields.module_axioms_used, Vec::new());
        assert!(!ok.endpoint_fields.certificate.bytes.is_empty());
    }

    fn run_exact_prop_on_each_goal(
        session: &mut MachineProofSession,
        previous: MachineTacticRunSuccessFields,
    ) -> MachineTacticRunSuccessFields {
        let mut current = previous;
        for goal_id in current.result.new_goals.clone() {
            current = run_on_result(
                session,
                &current,
                goal_id,
                r#"{"kind":"exact","term":{"source":"Prop"}}"#,
            );
        }
        current
    }

    #[test]
    fn machine_tactic_api_source_has_no_untrusted_text_fallback() {
        let source = include_str!("tactic.rs");
        let forbidden = [
            ["parse_", "human"].concat(),
            ["compile_", "human"].concat(),
            ["human", "_parser"].concat(),
            ["human", "_elaborator"].concat(),
            ["Hu", "man"].concat(),
        ];

        for needle in forbidden {
            assert!(
                !source.contains(&needle),
                "machine tactic api must not contain fallback marker {needle:?}"
            );
        }
    }

    #[test]
    fn structural_tactic_integration_v2_candidate_wire_shapes_parse() {
        for (expected_kind, candidate) in structural_v2_candidate_fixtures() {
            let parsed = parse_wire_candidate(&candidate);
            assert_eq!(
                npa_tactic::machine_tactic_candidate_kind(&parsed),
                expected_kind,
                "candidate should parse as {expected_kind}: {candidate}"
            );
            let serialized = crate::ai_search::ai_search_candidate_payload_json(&parsed);
            let reparsed = parse_wire_candidate(&serialized);
            assert_eq!(
                npa_tactic::machine_tactic_candidate_kind(&reparsed),
                expected_kind,
                "serialized candidate should round-trip as {expected_kind}: {serialized}"
            );
        }
    }

    #[test]
    fn structural_v2_candidate_parser_rejects_malformed_payloads() {
        let duplicate_branch_names =
            r#"{"kind":"cases","major_local":"h","motive":null,"branch_names":["b","b"]}"#;
        let err = parse_candidate_wire_shape_at(
            duplicate_branch_names,
            candidate_tactic_kind_for_diagnostic(duplicate_branch_names),
            &JsonPath::root().field("candidate"),
        )
        .expect_err("duplicate branch names should fail closed");
        assert_eq!(err.kind, MachineApiErrorKind::InvalidCandidate);
        assert!(matches!(
            err.reason,
            MachineApiRequestErrorReason::DuplicateKey { .. }
        ));

        let malformed_local =
            r#"{"kind":"revert","locals":["bad-name"],"dependency_policy":"exact"}"#;
        let err = parse_candidate_wire_shape_at(
            malformed_local,
            candidate_tactic_kind_for_diagnostic(malformed_local),
            &JsonPath::root().field("candidate"),
        )
        .expect_err("malformed local references should fail closed");
        assert_eq!(err.kind, MachineApiErrorKind::InvalidCandidate);

        let non_identity_metadata =
            r#"{"kind":"constructor","selection":{"mode":"auto"},"display_text":"constructor"}"#;
        let err = parse_candidate_wire_shape_at(
            non_identity_metadata,
            candidate_tactic_kind_for_diagnostic(non_identity_metadata),
            &JsonPath::root().field("candidate"),
        )
        .expect_err("display metadata must not be accepted as candidate payload");
        assert_eq!(err.kind, MachineApiErrorKind::InvalidCandidate);
        assert!(matches!(
            err.reason,
            MachineApiRequestErrorReason::UnknownField { .. }
        ));
    }

    #[test]
    fn structural_tactic_integration_source_free_constructor_cases_and_induction_verify() {
        let ctor = constructor_fixture_module();
        let mut session = create_machine_session(&session_json_with_imports("Ctor.True", &[ctor]))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let run = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"constructor","selection":{"mode":"auto"},"max_new_goals":0}"#,
        );
        assert_eq!(run.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            run.result.next_snapshot_id,
            run.result.next_state_fingerprint,
        );

        let case = cases_fixture_module();
        let mut session = create_machine_session(&session_json_with_imports(
            "forall (x : Case.Color), Type 0",
            &[case],
        ))
        .unwrap()
        .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"x"}"#,
        );
        let cases = run_on_result(
            &mut session,
            &intro,
            npa_tactic::GoalId(1),
            r#"{"kind":"cases","major_local":"x","motive":null,"branch_names":["red_case","blue_case"],"max_new_goals":2}"#,
        );
        assert_eq!(cases.result.new_goals.len(), 2);
        let closed = run_exact_prop_on_each_goal(&mut session, cases);
        assert_eq!(closed.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            closed.result.next_snapshot_id,
            closed.result.next_state_fingerprint,
        );

        let nat = nat_fixture_module();
        let recursor = fixture_imported_head_json(&nat, "Nat.rec");
        let induction = format!(
            r#"{{"kind":"general-induction","major_local":"n","recursor":{recursor},"motive":null,"generalized_locals":[],"branch_names":["zero_case","succ_case"],"max_new_goals":2}}"#
        );
        let mut session = create_machine_session(&session_json_with_imports(
            "forall (n : Nat), Type 0",
            &[nat],
        ))
        .unwrap()
        .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"n"}"#,
        );
        let branches = run_on_result(&mut session, &intro, npa_tactic::GoalId(1), &induction);
        assert_eq!(branches.result.new_goals.len(), 2);
        let closed = run_exact_prop_on_each_goal(&mut session, branches);
        assert_eq!(closed.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            closed.result.next_snapshot_id,
            closed.result.next_state_fingerprint,
        );
    }

    #[test]
    fn structural_tactic_integration_source_free_refine_have_and_suffices_verify() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let refined = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"refine","term":{"source":"Prop"},"max_holes":0}"#,
        );
        assert_eq!(refined.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            refined.result.next_snapshot_id,
            refined.result.next_state_fingerprint,
        );

        let prop_id = "forall (p : Prop), forall (hp : p), p";
        let mut session = create_machine_session(&minimal_session_json(prop_id))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro_p = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"p"}"#,
        );
        let intro_hp = run_on_result(
            &mut session,
            &intro_p,
            npa_tactic::GoalId(1),
            r#"{"kind":"intro","name":"hp"}"#,
        );
        let have = run_on_result(
            &mut session,
            &intro_hp,
            npa_tactic::GoalId(2),
            r#"{"kind":"have","name":"h","type":{"source":"p"},"proof":{"mode":"term","term":{"source":"hp"}},"insertion":"end"}"#,
        );
        let closed = run_on_result(
            &mut session,
            &have,
            npa_tactic::GoalId(3),
            r#"{"kind":"exact","term":{"source":"h"}}"#,
        );
        assert_eq!(closed.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            closed.result.next_snapshot_id,
            closed.result.next_state_fingerprint,
        );

        let mut session = create_machine_session(&minimal_session_json(prop_id))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro_p = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"p"}"#,
        );
        let intro_hp = run_on_result(
            &mut session,
            &intro_p,
            npa_tactic::GoalId(1),
            r#"{"kind":"intro","name":"hp"}"#,
        );
        let suffices = run_on_result(
            &mut session,
            &intro_hp,
            npa_tactic::GoalId(2),
            r#"{"kind":"suffices","target":{"source":"p"},"proof":{"mode":"term","term":{"source":"hp"}},"continuation":"prove-intermediate-first"}"#,
        );
        let closed = run_on_result(
            &mut session,
            &suffices,
            npa_tactic::GoalId(3),
            r#"{"kind":"exact","term":{"source":"suffices"}}"#,
        );
        assert_eq!(closed.result.kind, MachineTacticRunResultKind::Closed);
        assert_source_free_verified(
            &session,
            closed.result.next_snapshot_id,
            closed.result.next_state_fingerprint,
        );
    }

    #[test]
    fn structural_tactic_integration_source_free_rejects_open_children_and_invalid_recursor() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let err = run_machine_tactic_request(
            &run_json_at(
                &session,
                initial_snapshot,
                initial_fingerprint,
                npa_tactic::GoalId(0),
                r#"{"kind":"refine","term":{"source":"_"},"max_holes":1}"#,
            ),
            &mut session,
        )
        .unwrap_err();
        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::MachineTermElaborationError
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Refine)
        );
        let MachineApiResponseEnvelope::Error(response) = err.response else {
            panic!("expected refine hole rejection");
        };
        assert_eq!(
            response.endpoint_fields.unchanged_state_fingerprint,
            Some(initial_fingerprint)
        );

        let prop_id = "forall (p : Prop), forall (hp : p), p";
        let mut session = create_machine_session(&minimal_session_json(prop_id))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro_p = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"p"}"#,
        );
        let intro_hp = run_on_result(
            &mut session,
            &intro_p,
            npa_tactic::GoalId(1),
            r#"{"kind":"intro","name":"hp"}"#,
        );
        let have = run_on_result(
            &mut session,
            &intro_hp,
            npa_tactic::GoalId(2),
            r#"{"kind":"have","name":"h","type":{"source":"p"},"proof":{"mode":"child-goal"},"insertion":"after-current"}"#,
        );
        let continuation = have.result.new_goals[1];
        let missing_child = run_on_result(
            &mut session,
            &have,
            continuation,
            r#"{"kind":"exact","term":{"source":"h"}}"#,
        );
        let err = run_machine_verify_request(
            &verify_json_at(
                &session,
                missing_child.result.next_snapshot_id,
                missing_child.result.next_state_fingerprint,
            ),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidVerifyRequest
        );

        let mut session = create_machine_session(&minimal_session_json(prop_id))
            .unwrap()
            .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro_p = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"p"}"#,
        );
        let intro_hp = run_on_result(
            &mut session,
            &intro_p,
            npa_tactic::GoalId(1),
            r#"{"kind":"intro","name":"hp"}"#,
        );
        let suffices = run_on_result(
            &mut session,
            &intro_hp,
            npa_tactic::GoalId(2),
            r#"{"kind":"suffices","target":{"source":"p"},"proof":{"mode":"child-goal"},"continuation":"prove-continuation-first"}"#,
        );
        let continuation = suffices.result.new_goals[0];
        let missing_child = run_on_result(
            &mut session,
            &suffices,
            continuation,
            r#"{"kind":"exact","term":{"source":"suffices"}}"#,
        );
        let err = run_machine_verify_request(
            &verify_json_at(
                &session,
                missing_child.result.next_snapshot_id,
                missing_child.result.next_state_fingerprint,
            ),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidVerifyRequest
        );

        let nat = nat_fixture_module();
        let mut session = create_machine_session(&session_json_with_imports(
            "forall (n : Nat), Type 0",
            &[nat],
        ))
        .unwrap()
        .session;
        let initial_snapshot = session.initial_snapshot.snapshot_id;
        let initial_fingerprint = session.initial_snapshot.state_fingerprint;
        let intro = run_tactic_at(
            &mut session,
            initial_snapshot,
            initial_fingerprint,
            npa_tactic::GoalId(0),
            r#"{"kind":"intro","name":"n"}"#,
        );
        let stale_rec = imported_head_json("Nat.rec", 0);
        let candidate = format!(
            r#"{{"kind":"general-induction","major_local":"n","recursor":{stale_rec},"motive":null,"generalized_locals":[],"branch_names":["zero_case","succ_case"],"max_new_goals":2}}"#
        );
        let err = run_machine_tactic_request(
            &run_json_at(
                &session,
                intro.result.next_snapshot_id,
                intro.result.next_state_fingerprint,
                npa_tactic::GoalId(1),
                &candidate,
            ),
            &mut session,
        )
        .unwrap_err();
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::CandidateValidation
        );
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::GeneralInduction)
        );
    }

    #[test]
    fn structural_tactic_integration_reserved_solvers_fail_as_unsupported_with_identity_hash() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        for (candidate, tactic_kind) in [
            (
                r#"{"kind":"finite-decide"}"#,
                MachineApiTacticKind::FiniteDecide,
            ),
            (r#"{"kind":"omega"}"#, MachineApiTacticKind::Omega),
            (r#"{"kind":"ring"}"#, MachineApiTacticKind::Ring),
            (r#"{"kind":"bitblast"}"#, MachineApiTacticKind::Bitblast),
        ] {
            let request = run_json(
                &session,
                session.initial_snapshot.state_fingerprint,
                candidate,
            );

            let err = run_machine_tactic_request(&request, &mut session).unwrap_err();

            assert_eq!(err.diagnostic.kind, MachineApiErrorKind::UnsupportedTactic);
            assert_eq!(
                err.diagnostic.phase,
                MachineApiDiagnosticPhase::CandidateValidation
            );
            assert_eq!(err.diagnostic.tactic_kind, Some(tactic_kind));
            let MachineApiResponseEnvelope::Error(response) = err.response else {
                panic!("expected unsupported tactic error response");
            };
            assert!(response.error.candidate_hash.is_some());
            assert!(response.error.deterministic_budget_hash.is_some());
            assert_eq!(
                response.endpoint_fields.unchanged_state_fingerprint,
                Some(session.initial_snapshot.state_fingerprint)
            );
        }
    }

    #[test]
    fn tactic_budget_validation_failure_has_identity_hash_and_keeps_state() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let initial_state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let budget = r#"{
          "max_tactic_steps":64,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":0
        }"#;
        let request = run_json_with_budget(&session, initial_state_fingerprint, candidate, budget);

        let err = run_machine_tactic_request(&request, &mut session).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::TooLargeTerm);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::CandidateValidation
        );
        assert_eq!(err.diagnostic.goal_id, Some(npa_tactic::GoalId(0)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
        let MachineApiResponseEnvelope::Error(response) = err.response else {
            panic!("expected budget validation error response");
        };
        assert!(response.error.candidate_hash.is_some());
        assert!(response.error.deterministic_budget_hash.is_some());
        assert_eq!(
            response.endpoint_fields.unchanged_state_fingerprint,
            Some(initial_state_fingerprint)
        );
        assert_eq!(
            session.initial_snapshot.state_fingerprint,
            initial_state_fingerprint
        );
    }

    fn run_json(session: &MachineProofSession, state_fingerprint: Hash, candidate: &str) -> String {
        run_json_with_budget(session, state_fingerprint, candidate, budget_json())
    }

    fn run_json_with_budget(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidate: &str,
        budget: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidate":{},
              "deterministic_budget":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            candidate,
            budget
        )
    }

    fn diagnostic_budget_json(max_diagnostic_steps: u64) -> String {
        format!(
            r#"{{
              "max_graph_nodes":4,
              "max_expression_paths":8,
              "max_rewrite_site_scans":4,
              "max_pretty_term_bytes":64,
              "max_repair_proposals":4,
              "max_diagnostic_steps":{max_diagnostic_steps}
            }}"#
        )
    }

    fn lazy_diagnostic_json(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidate: &str,
        deterministic_budget: &str,
        diagnostic_hash: Hash,
        profile: &str,
        diagnostic_budget: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidate":{},
              "deterministic_budget":{},
              "diagnostic_hash":"{}",
              "profile":"{}",
              "diagnostic_budget":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            candidate,
            deterministic_budget,
            format_hash_string(&diagnostic_hash),
            profile,
            diagnostic_budget
        )
    }

    fn exact_prop_failure_hash(session: &mut MachineProofSession) -> Hash {
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let request = run_json(
            session,
            session.initial_snapshot.state_fingerprint,
            candidate,
        );
        let err = run_machine_tactic_request(&request, session)
            .expect_err("exact Prop should fail against Prop target");
        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::TypeMismatch);
        err.diagnostic
            .diagnostic_hash()
            .expect("compact diagnostic should hash")
    }

    #[test]
    fn lazy_diagnostics_cache_miss_then_hit_returns_full_payload() {
        let mut session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let diagnostic_hash = exact_prop_failure_hash(&mut session);
        let diagnostic_budget = diagnostic_budget_json(16);
        let request = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            budget_json(),
            diagnostic_hash,
            "full",
            &diagnostic_budget,
        );
        let mut cache = MachineLazyDiagnosticCache::new();

        let first =
            run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache)).unwrap();

        assert_eq!(
            first.cache_status,
            MachineLazyDiagnosticCacheStatus::Miss {
                reason: MachineLazyDiagnosticCacheMissReason::Absent
            }
        );
        assert_eq!(first.diagnostic_tree.profile, DiagnosticProfile::Full);
        assert_eq!(first.metadata.key.diagnostic_hash, diagnostic_hash);
        assert_eq!(first.metadata.key.state_fingerprint, state_fingerprint);
        assert_eq!(
            first.metadata.producer_version,
            LAZY_DIAGNOSTIC_CACHE_PRODUCER_VERSION
        );
        assert_eq!(cache.len(), 1);
        assert_eq!(first.counters.cache_misses, 1);
        assert_eq!(first.counters.cache_hits, 0);
        assert_eq!(first.counters.full_diagnostics_generated, 1);
        assert_eq!(first.counters.full_diagnostics_generated_on_success, 0);
        assert_eq!(first.counters.theorem_graph_calls, 0);

        let second =
            run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache)).unwrap();

        assert_eq!(second.cache_status, MachineLazyDiagnosticCacheStatus::Hit);
        assert_eq!(second.diagnostic_tree, first.diagnostic_tree);
        assert_eq!(second.metadata, first.metadata);
        assert_eq!(second.counters.cache_misses, 1);
        assert_eq!(second.counters.cache_hits, 1);
        assert_eq!(second.counters.full_diagnostics_generated, 1);
        assert_eq!(second.counters.full_diagnostics_generated_on_success, 0);
        assert_eq!(second.counters.theorem_graph_calls, 0);
    }

    #[test]
    fn lazy_diagnostics_cache_rejects_changed_budget_identities() {
        let mut session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let diagnostic_hash = exact_prop_failure_hash(&mut session);
        let diagnostic_budget = diagnostic_budget_json(16);
        let request = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            budget_json(),
            diagnostic_hash,
            "basic",
            &diagnostic_budget,
        );
        let mut cache = MachineLazyDiagnosticCache::new();
        let first =
            run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache)).unwrap();
        assert_eq!(
            first.cache_status,
            MachineLazyDiagnosticCacheStatus::Miss {
                reason: MachineLazyDiagnosticCacheMissReason::Absent
            }
        );

        let changed_diagnostic_budget = diagnostic_budget_json(17);
        let changed_diagnostic_budget_request = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            budget_json(),
            diagnostic_hash,
            "basic",
            &changed_diagnostic_budget,
        );
        let changed_diagnostic_budget_ok = run_machine_lazy_diagnostic_request(
            &changed_diagnostic_budget_request,
            &session,
            Some(&mut cache),
        )
        .unwrap();
        assert_eq!(
            changed_diagnostic_budget_ok.cache_status,
            MachineLazyDiagnosticCacheStatus::Miss {
                reason: MachineLazyDiagnosticCacheMissReason::DiagnosticBudgetHashMismatch
            }
        );
        assert_ne!(
            changed_diagnostic_budget_ok.metadata.diagnostic_budget_hash,
            first.metadata.diagnostic_budget_hash
        );

        let changed_deterministic_budget = r#"{
          "max_tactic_steps":65,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#;
        let changed_deterministic_budget_request = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            changed_deterministic_budget,
            diagnostic_hash,
            "basic",
            &changed_diagnostic_budget,
        );
        let changed_deterministic_budget_ok = run_machine_lazy_diagnostic_request(
            &changed_deterministic_budget_request,
            &session,
            Some(&mut cache),
        )
        .unwrap();
        assert_eq!(
            changed_deterministic_budget_ok.cache_status,
            MachineLazyDiagnosticCacheStatus::Miss {
                reason: MachineLazyDiagnosticCacheMissReason::DeterministicBudgetHashMismatch
            }
        );
        assert_ne!(
            changed_deterministic_budget_ok
                .metadata
                .key
                .deterministic_budget_hash,
            first.metadata.key.deterministic_budget_hash
        );
        assert_eq!(cache.counters().cache_hits, 0);
        assert_eq!(cache.counters().cache_misses, 3);
    }

    #[test]
    fn lazy_diagnostics_cache_rejects_changed_candidate_identity() {
        let mut session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let diagnostic_hash = exact_prop_failure_hash(&mut session);
        let diagnostic_budget = diagnostic_budget_json(16);
        let request = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            budget_json(),
            diagnostic_hash,
            "basic",
            &diagnostic_budget,
        );
        let mut cache = MachineLazyDiagnosticCache::new();
        let first =
            run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache)).unwrap();
        let mut changed_candidate = first.metadata.clone();
        changed_candidate.key.candidate_hash = [7; 32];

        let miss = cache
            .lookup(&changed_candidate)
            .expect_err("changed candidate identity must miss");

        assert_eq!(
            miss,
            MachineLazyDiagnosticCacheMissReason::CandidateHashMismatch
        );
        assert_eq!(cache.counters().cache_hits, 0);
        assert_eq!(cache.counters().cache_misses, 2);
    }

    #[test]
    fn lazy_diagnostics_cache_rejects_stale_snapshot_before_reuse() {
        let mut session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let diagnostic_hash = exact_prop_failure_hash(&mut session);
        let diagnostic_budget = diagnostic_budget_json(16);
        let request = lazy_diagnostic_json(
            &session,
            [9; 32],
            candidate,
            budget_json(),
            diagnostic_hash,
            "full",
            &diagnostic_budget,
        );
        let mut cache = MachineLazyDiagnosticCache::new();
        let populate = lazy_diagnostic_json(
            &session,
            state_fingerprint,
            candidate,
            budget_json(),
            diagnostic_hash,
            "full",
            &diagnostic_budget,
        );
        run_machine_lazy_diagnostic_request(&populate, &session, Some(&mut cache)).unwrap();

        let err = run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache))
            .expect_err("stale snapshot fingerprint must not reuse cache");

        assert!(matches!(
            err,
            MachineLazyDiagnosticError::SnapshotLookup(
                MachineSnapshotLookupError::StateFingerprintMismatch { .. }
            )
        ));
        assert_eq!(cache.counters().cache_hits, 0);
        assert_eq!(cache.counters().cache_misses, 1);
    }

    #[test]
    fn lazy_diagnostics_cache_success_path_excludes_full_generation() {
        let session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let request = lazy_diagnostic_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            candidate,
            budget_json(),
            [0; 32],
            "full",
            &diagnostic_budget_json(16),
        );
        let mut cache = MachineLazyDiagnosticCache::new();

        let err = run_machine_lazy_diagnostic_request(&request, &session, Some(&mut cache))
            .expect_err("successful candidates cannot fetch full diagnostics");

        assert_eq!(err, MachineLazyDiagnosticError::CandidateSucceeded);
        let counters = cache.counters();
        assert_eq!(counters.success_path_full_diagnostic_attempts, 1);
        assert_eq!(counters.full_diagnostics_generated_on_success, 0);
        assert_eq!(counters.full_diagnostics_generated, 0);
        assert_eq!(counters.theorem_graph_calls, 0);
        assert!(cache.is_empty());
    }

    fn benchmark_case(
        category: RepairBenchmarkErrorCategory,
        configure: impl FnOnce(&mut RepairEffectivenessBenchmarkCase),
    ) -> RepairEffectivenessBenchmarkCase {
        let mut case = RepairEffectivenessBenchmarkCase {
            category,
            repair_succeeded: false,
            repair_depth: 0,
            repeated_failure_count: 0,
            baseline_candidate_count: 1,
            considered_candidate_count: 0,
            generated_proposal_count: 0,
            invalid_repair_proposal_count: 0,
            final_verified_before_repair: false,
            final_verified_after_repair: false,
            new_goal_growth: 0,
        };
        configure(&mut case);
        case
    }

    fn repair_effectiveness_benchmark_cases() -> Vec<RepairEffectivenessBenchmarkCase> {
        struct ExactMismatchRetrieval;
        impl RepairRetrievalAdapter for ExactMismatchRetrieval {
            fn repair_candidates(
                &self,
                request: &RepairRetrievalRequest<'_>,
            ) -> Vec<MachineTacticCandidate> {
                assert_eq!(request.category, RepairDiagnosticCategory::TypeMismatch);
                vec![MachineTacticCandidate::Exact {
                    term: RawMachineTerm::new("Prop"),
                }]
            }
        }

        let state = repair_generator_state(prop_expr());
        let mut type_mismatch = repair_projection(
            MachineApiErrorKind::TypeMismatch,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "benchmark type mismatch",
            ),
        );
        type_mismatch.phase = MachineApiDiagnosticPhase::TacticExecution;
        type_mismatch.tactic_kind = Some(MachineApiTacticKind::Exact);
        type_mismatch.expected_hash = Some(core_expr_hash(&prop_expr()));
        type_mismatch.actual_hash = Some(core_expr_hash(&type0_expr()));
        let repeated_report = run_repair_chain_with_retrieval(
            &repair_chain_context(
                &state,
                &type_mismatch,
                RepairChainLimits {
                    max_repair_depth: 4,
                    max_repeated_candidate_payload_hash_count: usize::MAX,
                    max_total_candidates: 8,
                    ..RepairChainLimits::default()
                },
            ),
            &ExactMismatchRetrieval,
        )
        .expect("benchmark repair chain should hash diagnostics");

        let expected_pi_state = repair_generator_state(type0_expr());
        let mut expected_pi = repair_projection(
            MachineApiErrorKind::ExpectedPiType,
            Some(GoalId(0)),
            MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::ExpectedPiTarget,
                "benchmark expected pi",
            ),
        );
        expected_pi.tactic_kind = Some(MachineApiTacticKind::Intro);
        let expected_pi_report = run_repair_chain(&repair_chain_context(
            &expected_pi_state,
            &expected_pi,
            RepairChainLimits::default(),
        ))
        .expect("benchmark repair chain should hash expected-pi diagnostic");

        vec![
            RepairEffectivenessBenchmarkCase::from_repair_chain(
                RepairBenchmarkErrorCategory::TypeMismatch,
                3,
                0,
                false,
                &repeated_report,
            ),
            RepairEffectivenessBenchmarkCase::from_repair_chain(
                RepairBenchmarkErrorCategory::ExpectedPiTarget,
                2,
                1,
                false,
                &expected_pi_report,
            ),
            benchmark_case(
                RepairBenchmarkErrorCategory::UnresolvedMetavariable,
                |case| {
                    case.repeated_failure_count = 1;
                    case.baseline_candidate_count = 2;
                    case.considered_candidate_count = 2;
                    case.generated_proposal_count = 2;
                    case.invalid_repair_proposal_count = 1;
                },
            ),
            benchmark_case(RepairBenchmarkErrorCategory::RewriteNoProgress, |case| {
                case.repair_depth = 1;
                case.repeated_failure_count = 1;
                case.baseline_candidate_count = 4;
                case.considered_candidate_count = 2;
                case.generated_proposal_count = 3;
            }),
            benchmark_case(RepairBenchmarkErrorCategory::InvalidRewriteRule, |case| {
                case.baseline_candidate_count = 3;
                case.generated_proposal_count = 1;
                case.invalid_repair_proposal_count = 1;
            }),
            benchmark_case(RepairBenchmarkErrorCategory::UniverseMismatch, |case| {
                case.repair_succeeded = true;
                case.repair_depth = 1;
                case.baseline_candidate_count = 3;
                case.considered_candidate_count = 1;
                case.generated_proposal_count = 2;
                case.final_verified_after_repair = true;
            }),
            benchmark_case(RepairBenchmarkErrorCategory::BudgetExceeded, |case| {
                case.baseline_candidate_count = 5;
                case.considered_candidate_count = 2;
                case.generated_proposal_count = 2;
            }),
            benchmark_case(RepairBenchmarkErrorCategory::StaleState, |_| {}),
            benchmark_case(RepairBenchmarkErrorCategory::UnsupportedTactic, |_| {}),
        ]
    }

    #[test]
    #[ignore = "opt-in sidecar benchmark harness; deterministic but not on the hot path"]
    fn diagnostic_profile_bench_repair_effectiveness_reports_design_kpis() {
        let cases = repair_effectiveness_benchmark_cases();
        let summary = repair_effectiveness_benchmark_summary(cases);
        let output = summary.sidecar_lines();

        assert_eq!(summary.schema, REPAIR_EFFECTIVENESS_BENCHMARK_SCHEMA);
        assert!(summary.sidecar_only);
        assert_eq!(
            summary.repair_success_by_error_category.len(),
            RepairBenchmarkErrorCategory::required_fixture_categories().len()
        );
        for category in RepairBenchmarkErrorCategory::required_fixture_categories() {
            assert!(
                summary
                    .repair_success_by_error_category
                    .contains_key(&category),
                "missing benchmark fixture category {}",
                category.as_str()
            );
            assert!(output.contains(category.as_str()));
        }
        for kpi in RepairEffectivenessBenchmarkSummary::reported_kpi_names() {
            assert!(output.contains(kpi), "benchmark output missing {kpi}");
        }
        assert_eq!(summary.fixture_count, 9);
        assert_eq!(summary.final_verified_rate_uplift_basis_points, 1111);
        assert!(summary.candidate_count_reduction > 0);
    }

    #[test]
    #[ignore = "opt-in sidecar benchmark harness; deterministic but not on the hot path"]
    fn diagnostic_profile_bench_compares_off_basic_full_failure_fixtures() {
        let mut session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let state_fingerprint = session.initial_snapshot.state_fingerprint;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let compact_failure = run_machine_tactic_request(
            &run_json(&session, state_fingerprint, candidate),
            &mut session,
        )
        .expect_err("off-profile fixture should fail compactly");
        let compact_hash = compact_failure
            .diagnostic
            .diagnostic_hash()
            .expect("compact diagnostic should hash");

        let diagnostic_budget = diagnostic_budget_json(16);
        let mut cache = MachineLazyDiagnosticCache::new();
        let basic = run_machine_lazy_diagnostic_request(
            &lazy_diagnostic_json(
                &session,
                state_fingerprint,
                candidate,
                budget_json(),
                compact_hash,
                "basic",
                &diagnostic_budget,
            ),
            &session,
            Some(&mut cache),
        )
        .expect("basic lazy diagnostics should be generated after failure");
        let full = run_machine_lazy_diagnostic_request(
            &lazy_diagnostic_json(
                &session,
                state_fingerprint,
                candidate,
                budget_json(),
                compact_hash,
                "full",
                &diagnostic_budget,
            ),
            &session,
            Some(&mut cache),
        )
        .expect("full lazy diagnostics should be generated after failure");

        let success_session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let success_request = lazy_diagnostic_json(
            &success_session,
            success_session.initial_snapshot.state_fingerprint,
            candidate,
            budget_json(),
            [0; 32],
            "full",
            &diagnostic_budget_json(16),
        );
        let mut success_cache = MachineLazyDiagnosticCache::new();
        assert_eq!(
            run_machine_lazy_diagnostic_request(
                &success_request,
                &success_session,
                Some(&mut success_cache),
            )
            .expect_err("successful candidate must not produce full diagnostics"),
            MachineLazyDiagnosticError::CandidateSucceeded
        );

        let summary = diagnostic_profile_benchmark_summary(vec![
            DiagnosticProfileBenchmarkRow {
                profile: DiagnosticProfile::Off,
                failure_fixture_count: 1,
                success_fixture_count: 0,
                diagnostic_tree_bytes: 0,
                full_diagnostics_generated: 0,
                full_diagnostics_generated_on_success: 0,
                theorem_graph_calls: 0,
                cache_hits: 0,
                cache_misses: 0,
            },
            DiagnosticProfileBenchmarkRow {
                profile: DiagnosticProfile::Basic,
                failure_fixture_count: 1,
                success_fixture_count: 0,
                diagnostic_tree_bytes: basic
                    .diagnostic_tree
                    .canonical_bytes()
                    .expect("basic tree should canonicalize")
                    .len() as u64,
                full_diagnostics_generated: 0,
                full_diagnostics_generated_on_success: basic
                    .counters
                    .full_diagnostics_generated_on_success,
                theorem_graph_calls: basic.counters.theorem_graph_calls,
                cache_hits: basic.counters.cache_hits,
                cache_misses: basic.counters.cache_misses,
            },
            DiagnosticProfileBenchmarkRow {
                profile: DiagnosticProfile::Full,
                failure_fixture_count: 1,
                success_fixture_count: 1,
                diagnostic_tree_bytes: full
                    .diagnostic_tree
                    .canonical_bytes()
                    .expect("full tree should canonicalize")
                    .len() as u64,
                full_diagnostics_generated: full.counters.full_diagnostics_generated,
                full_diagnostics_generated_on_success: success_cache
                    .counters()
                    .full_diagnostics_generated_on_success,
                theorem_graph_calls: full.counters.theorem_graph_calls
                    + success_cache.counters().theorem_graph_calls,
                cache_hits: full.counters.cache_hits,
                cache_misses: full.counters.cache_misses,
            },
        ]);

        assert_eq!(
            summary
                .rows
                .iter()
                .map(|row| row.profile)
                .collect::<Vec<_>>(),
            vec![
                DiagnosticProfile::Off,
                DiagnosticProfile::Basic,
                DiagnosticProfile::Full
            ]
        );
        assert_eq!(summary.full_diagnostics_generated_on_success, 0);
        assert_eq!(summary.theorem_graph_calls, 0);
        assert!(summary.sidecar_only);
        let output = summary.sidecar_lines();
        for profile in ["profile.off", "profile.basic", "profile.full"] {
            assert!(output.contains(profile));
        }
        performance_isolation_guardrail(performance_isolation_counters_from_lazy_cache(
            success_cache.counters(),
        ))
        .expect("success-path lazy diagnostic counters must pass release guardrail");
    }

    #[test]
    fn performance_isolation_normal_tactic_success_has_zero_sidecar_calls() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = run_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"{"kind":"exact","term":{"source":"Prop"}}"#,
        );
        run_machine_tactic_request(&request, &mut session)
            .expect("ordinary successful tactic should not need sidecar services");

        let report =
            performance_isolation_guardrail(MachinePerformanceIsolationCounters::default())
                .expect("ordinary verification counters should be zero");
        assert_eq!(report.schema, PERFORMANCE_ISOLATION_GUARDRAIL_SCHEMA);
        assert!(!report.release_blocked);
        assert_eq!(report.counters.theorem_graph_calls, 0);
        assert_eq!(report.counters.embedding_calls, 0);
        assert_eq!(report.counters.llm_calls, 0);
        assert_eq!(report.counters.agent_calls, 0);
        assert_eq!(report.counters.database_calls, 0);
        assert_eq!(report.counters.rich_diagnostic_graph_calls, 0);
        assert_eq!(report.counters.full_diagnostics_generated_on_success, 0);
    }

    #[test]
    fn performance_isolation_guardrail_rejects_nonzero_services() {
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                theorem_graph_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::TheoremGraphCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                embedding_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::EmbeddingCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                llm_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::LlmCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                agent_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::AgentCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                database_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::DatabaseCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                rich_diagnostic_graph_calls: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(MachinePerformanceIsolationGuardrailError::RichDiagnosticGraphCalls { count: 1 })
        );
        assert_eq!(
            performance_isolation_guardrail(MachinePerformanceIsolationCounters {
                full_diagnostics_generated_on_success: 1,
                ..MachinePerformanceIsolationCounters::default()
            }),
            Err(
                MachinePerformanceIsolationGuardrailError::FullDiagnosticsGeneratedOnSuccess {
                    count: 1
                }
            )
        );
    }

    fn run_json_with_scheduler(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidate: &str,
        scheduler_limits: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidate":{},
              "deterministic_budget":{},
              "scheduler_limits":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            candidate,
            budget_json(),
            scheduler_limits
        )
    }

    fn batch_json(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidates: &str,
    ) -> String {
        batch_json_with_policy(
            session,
            state_fingerprint,
            candidates,
            r#"{
              "max_evaluated_candidates":256,
              "stop_after_successes":256,
              "stop_after_failures":256
            }"#,
        )
    }

    fn batch_json_with_policy(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidates: &str,
        batch_policy: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":{},
              "deterministic_budget":{},
              "batch_policy":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            candidates,
            budget_json(),
            batch_policy
        )
    }

    fn batch_json_with_scheduler(
        session: &MachineProofSession,
        state_fingerprint: Hash,
        candidates: &str,
        scheduler_limits: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":{},
              "deterministic_budget":{},
              "batch_policy":{{
                "max_evaluated_candidates":256,
                "stop_after_successes":256,
                "stop_after_failures":256
              }},
              "scheduler_limits":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            candidates,
            budget_json(),
            scheduler_limits
        )
    }

    #[test]
    fn tactic_run_exact_success_stores_next_snapshot() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = run_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"{"kind":"exact","term":{"source":"Prop"}}"#,
        );

        let response = run_machine_tactic_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected success response");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Success);
        assert_eq!(
            ok.endpoint_fields.result.kind,
            MachineTacticRunResultKind::Closed
        );
        assert_eq!(
            ok.endpoint_fields.result.closed_goals,
            vec![npa_tactic::GoalId(0)]
        );
        assert!(ok.endpoint_fields.result.new_goals.is_empty());

        let get_request = format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":false
            }}"#,
            session.session_id.wire(),
            ok.endpoint_fields.result.next_snapshot_id.wire(),
            format_hash_string(&ok.endpoint_fields.result.next_state_fingerprint)
        );
        let MachineSnapshotGetOk { snapshot } =
            get_machine_snapshot(&get_request, [&session]).unwrap();
        assert!(snapshot.open_goals.is_empty());
    }

    #[test]
    fn candidate_identity_tactic_run_hash_includes_session_goal_and_budget() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let candidate_payload_hash =
            crate::adapter::machine_tactic_validate_machine_tactic_candidate(
                npa_tactic::GoalId(0),
                npa_tactic::MachineTacticCandidate::Exact {
                    term: npa_tactic::RawMachineTerm::new("Prop"),
                },
            )
            .unwrap()
            .candidate_hash;
        let initial_state_fingerprint = session.initial_snapshot.state_fingerprint;
        let request = run_json(&session, initial_state_fingerprint, candidate);

        let response = run_machine_tactic_request(&request, &mut session).unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected success response");
        };
        let expected = machine_tactic_proof_candidate_identity_hash(
            &session,
            initial_state_fingerprint,
            npa_tactic::GoalId(0),
            candidate_payload_hash,
            ok.endpoint_fields.result.deterministic_budget_hash,
        );

        assert_eq!(ok.endpoint_fields.result.candidate_hash, expected);
        assert_ne!(
            ok.endpoint_fields.result.candidate_hash,
            candidate_payload_hash
        );
    }

    #[test]
    fn tactic_batch_runs_candidates_against_same_input_and_stores_success_snapshots() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[
              {"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}},
              {"candidate_id":"c1","candidate":{"kind":"intro","name":"p"}}
            ]"#,
        );

        let response = run_machine_tactic_batch_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected batch ok response");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Ok);
        assert_eq!(
            ok.endpoint_fields.previous_state_fingerprint,
            session.initial_snapshot.state_fingerprint
        );
        assert_eq!(ok.endpoint_fields.results.len(), 2);
        assert_eq!(ok.endpoint_fields.success_count, 1);
        assert_eq!(ok.endpoint_fields.failure_count, 1);

        let first = &ok.endpoint_fields.results[0];
        let MachineTacticBatchItemResponse::Success {
            candidate_id,
            next_snapshot_id,
            next_state_fingerprint,
            ..
        } = first
        else {
            panic!("first candidate should succeed: {first:?}");
        };
        assert_eq!(candidate_id, "c0");
        let get_request = format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":false
            }}"#,
            session.session_id.wire(),
            next_snapshot_id.wire(),
            format_hash_string(next_state_fingerprint)
        );
        let MachineSnapshotGetOk { snapshot } =
            get_machine_snapshot(&get_request, [&session]).unwrap();
        assert!(snapshot.open_goals.is_empty());

        let second = &ok.endpoint_fields.results[1];
        let MachineTacticBatchItemResponse::Error {
            candidate_id,
            candidate_hash,
            diagnostic,
        } = second
        else {
            panic!("second candidate should fail independently: {second:?}");
        };
        assert_eq!(candidate_id, "c1");
        assert!(candidate_hash.is_some());
        assert_eq!(diagnostic.error_kind, MachineApiErrorKind::TypeMismatch);
        assert_eq!(
            diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(diagnostic.goal_id, Some(npa_tactic::GoalId(0)));
        assert_eq!(diagnostic.tactic_kind, Some(MachineApiTacticKind::Intro));
    }

    #[test]
    fn tactic_batch_replay_order_stays_in_input_order_when_failures_surround_success() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let initial_snapshot_count = session.snapshots.len();
        let request = batch_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[
              {"candidate_id":"c0","candidate":{"kind":"intro","name":"p"}},
              {"candidate_id":"c1","candidate":{"kind":"exact","term":{"source":"Prop"}}},
              {"candidate_id":"c2","candidate":{"kind":"exact","term":{"source":"("}}}
            ]"#,
        );

        let response = run_machine_tactic_batch_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected ordered batch ok response");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Ok);
        assert_eq!(
            ok.endpoint_fields.previous_state_fingerprint,
            session.initial_snapshot.state_fingerprint
        );
        assert_eq!(ok.endpoint_fields.success_count, 1);
        assert_eq!(ok.endpoint_fields.failure_count, 2);
        assert_eq!(ok.endpoint_fields.results.len(), 3);
        assert_eq!(
            ok.endpoint_fields
                .results
                .iter()
                .map(|item| match item {
                    MachineTacticBatchItemResponse::Success { candidate_id, .. }
                    | MachineTacticBatchItemResponse::Error { candidate_id, .. } =>
                        candidate_id.as_str(),
                })
                .collect::<Vec<_>>(),
            vec!["c0", "c1", "c2"]
        );

        let MachineTacticBatchItemResponse::Error {
            candidate_id,
            candidate_hash,
            diagnostic,
        } = &ok.endpoint_fields.results[0]
        else {
            panic!("first candidate should fail");
        };
        assert_eq!(candidate_id, "c0");
        assert!(candidate_hash.is_some());
        assert_eq!(diagnostic.error_kind, MachineApiErrorKind::TypeMismatch);
        assert_eq!(diagnostic.tactic_kind, Some(MachineApiTacticKind::Intro));

        let MachineTacticBatchItemResponse::Success {
            candidate_id,
            next_snapshot_id,
            next_state_fingerprint,
            proof_delta_hash,
            ..
        } = &ok.endpoint_fields.results[1]
        else {
            panic!("second candidate should succeed from the original input state");
        };
        assert_eq!(candidate_id, "c1");
        assert_ne!(*proof_delta_hash, [0; 32]);
        let get_request = format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":false
            }}"#,
            session.session_id.wire(),
            next_snapshot_id.wire(),
            format_hash_string(next_state_fingerprint)
        );
        let MachineSnapshotGetOk { snapshot } =
            get_machine_snapshot(&get_request, [&session]).unwrap();
        assert!(snapshot.open_goals.is_empty());

        let MachineTacticBatchItemResponse::Error {
            candidate_id,
            candidate_hash,
            diagnostic,
        } = &ok.endpoint_fields.results[2]
        else {
            panic!("third candidate should be a parse failure");
        };
        assert_eq!(candidate_id, "c2");
        assert!(candidate_hash.is_none());
        assert_eq!(
            diagnostic.error_kind,
            MachineApiErrorKind::MachineTermParseError
        );
        assert_eq!(diagnostic.tactic_kind, Some(MachineApiTacticKind::Exact));
        assert_eq!(session.snapshots.len(), initial_snapshot_count + 1);
    }

    #[test]
    fn tactic_batch_delays_inner_candidate_validation_until_after_snapshot_lookup() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json(
            &session,
            [7; 32],
            r#"[{"candidate_id":"c0","candidate":{"kind":"bogus","extra":true}}]"#,
        );

        let err = run_machine_tactic_batch_request(&request, &mut session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::StateFingerprintMismatch
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
    }

    #[test]
    fn tactic_batch_policy_stops_before_validating_prefix_external_candidates() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json_with_policy(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[
              {"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}},
              {"candidate_id":"c1","candidate":null}
            ]"#,
            r#"{
              "max_evaluated_candidates":1,
              "stop_after_successes":256,
              "stop_after_failures":256
            }"#,
        );

        let response = run_machine_tactic_batch_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected policy-limited ok response");
        };
        assert_eq!(ok.endpoint_fields.results.len(), 1);
        assert_eq!(ok.endpoint_fields.success_count, 1);
        assert_eq!(ok.endpoint_fields.failure_count, 0);
        assert!(ok.endpoint_fields.results[0].is_success());
    }

    #[test]
    fn tactic_batch_raw_term_parse_error_has_no_candidate_hash() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[{"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"("}}}]"#,
        );

        let response = run_machine_tactic_batch_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected batch ok response with per-candidate error");
        };
        assert_eq!(ok.endpoint_fields.success_count, 0);
        assert_eq!(ok.endpoint_fields.failure_count, 1);
        let MachineTacticBatchItemResponse::Error {
            candidate_id,
            candidate_hash,
            diagnostic,
        } = &ok.endpoint_fields.results[0]
        else {
            panic!("expected per-candidate parse error");
        };
        assert_eq!(candidate_id, "c0");
        assert!(candidate_hash.is_none());
        assert_eq!(
            diagnostic.error_kind,
            MachineApiErrorKind::MachineTermParseError
        );
        assert_eq!(
            diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermParse
        );
        assert_eq!(diagnostic.goal_id, Some(npa_tactic::GoalId(0)));
        assert_eq!(diagnostic.tactic_kind, Some(MachineApiTacticKind::Exact));
    }

    #[test]
    fn tactic_batch_partial_scheduler_response_preserves_completed_prefix() {
        let previous_state_fingerprint = [1; 32];
        let deterministic_budget_hash = [2; 32];
        let candidate_hash = [3; 32];
        let next_state_fingerprint = [4; 32];
        let proof_delta_hash = [5; 32];
        let result = MachineTacticBatchItemResponse::Success {
            candidate_id: "c0".to_owned(),
            candidate_hash,
            next_snapshot_id: SnapshotId::from_state_fingerprint(next_state_fingerprint),
            next_state_fingerprint,
            proof_delta_hash,
        };

        let response = batch_scheduler_stop(
            previous_state_fingerprint,
            deterministic_budget_hash,
            vec![result.clone()],
            1,
            0,
            BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Candidate,
            },
        );

        let MachineApiResponseEnvelope::SchedulerStopped(response) = response else {
            panic!("expected partial scheduler response");
        };
        assert_eq!(response.status, MachineApiResponseStatus::PartialTimeout);
        assert_eq!(
            response.scheduler_artifact.kind,
            MachineSchedulerArtifactKind::Timeout
        );
        assert_eq!(
            response.scheduler_artifact.scope,
            MachineSchedulerArtifactScope::Candidate
        );
        assert_eq!(response.endpoint_fields.completed_prefix_len, 1);
        assert_eq!(response.endpoint_fields.success_count, 1);
        assert_eq!(response.endpoint_fields.failure_count, 0);
        assert_eq!(response.endpoint_fields.results, vec![result]);
    }

    #[test]
    fn tactic_batch_rejects_duplicate_candidate_ids_as_batch_policy() {
        let session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[
              {"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}},
              {"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}}
            ]"#,
        );

        let err = parse_machine_tactic_batch_request(&request).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::DuplicateKey {
                key: "c0".to_owned()
            }
        );
    }

    #[test]
    fn tactic_batch_rejects_policy_values_outside_protocol_cap() {
        let session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json_with_policy(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[{"candidate_id":"c0","candidate":{"kind":"exact","term":{"source":"Prop"}}}]"#,
            r#"{
              "max_evaluated_candidates":257,
              "stop_after_successes":1,
              "stop_after_failures":1
            }"#,
        );

        let err = parse_machine_tactic_batch_request(&request).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBatchPolicy);
    }

    #[test]
    fn tactic_run_delays_candidate_validation_until_after_snapshot_lookup() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = run_json(&session, [7; 32], r#"{"kind":"bogus","extra":true}"#);

        let err = run_machine_tactic_request(&request, &mut session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::StateFingerprintMismatch
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
    }

    #[test]
    fn tactic_run_candidate_schema_error_keeps_state_unchanged_and_budget_hash() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = run_json(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"{"kind":"exact","term":{"source":"Prop"},"candidate_hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000"}"#,
        );

        let err = run_machine_tactic_request(&request, &mut session).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::InvalidCandidate);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::CandidateValidation
        );
        let MachineApiResponseEnvelope::Error(response) = err.response else {
            panic!("expected error response");
        };
        assert_eq!(
            response.endpoint_fields.unchanged_state_fingerprint,
            Some(session.initial_snapshot.state_fingerprint)
        );
        assert!(response.error.candidate_hash.is_none());
        assert!(response.error.deterministic_budget_hash.is_some());
    }

    #[test]
    fn diagnostic_adapter_malformed_candidate_payload_does_not_mutate_session() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let initial_state_fingerprint = session.initial_snapshot.state_fingerprint;
        let initial_snapshot_count = session.snapshots.len();
        let request = run_json(
            &session,
            initial_state_fingerprint,
            r#"{"kind":"exact","term":{"source":"Prop"},"unexpected":true}"#,
        );

        let err = run_machine_tactic_request(&request, &mut session).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::InvalidCandidate);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::CandidateValidation
        );
        let MachineApiResponseEnvelope::Error(response) = err.response else {
            panic!("expected error response");
        };
        assert_eq!(
            response.endpoint_fields.unchanged_state_fingerprint,
            Some(initial_state_fingerprint)
        );
        assert_eq!(
            session.initial_snapshot.state_fingerprint,
            initial_state_fingerprint
        );
        assert_eq!(session.snapshots.len(), initial_snapshot_count);
    }

    #[cfg(any(
        target_os = "android",
        target_os = "ios",
        target_os = "linux",
        target_os = "macos"
    ))]
    #[test]
    fn tactic_run_explicit_resource_limit_returns_scheduler_after_lookup() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = run_json_with_scheduler(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"{"kind":"bogus","extra":true}"#,
            r#"{"max_memory_mb":1}"#,
        );
        let deterministic_budget_hash = tactic_budget_hash(
            parse_machine_tactic_run_request(&request)
                .unwrap()
                .deterministic_budget,
        );

        let response = run_machine_tactic_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::SchedulerStopped(response) = response else {
            panic!("expected scheduler stop response");
        };
        assert_eq!(response.status, MachineApiResponseStatus::SchedulerStopped);
        assert_eq!(
            response.scheduler_artifact.kind,
            MachineSchedulerArtifactKind::ResourceLimitExceeded
        );
        assert_eq!(
            response.scheduler_artifact.scope,
            MachineSchedulerArtifactScope::Candidate
        );
        assert!(response.scheduler_artifact.retryable);
        assert_eq!(
            response.endpoint_fields.previous_state_fingerprint,
            session.initial_snapshot.state_fingerprint
        );
        assert_eq!(
            response.endpoint_fields.deterministic_budget_hash,
            deterministic_budget_hash
        );
    }

    #[cfg(any(
        target_os = "android",
        target_os = "ios",
        target_os = "linux",
        target_os = "macos"
    ))]
    #[test]
    fn tactic_batch_explicit_resource_limit_returns_partial_after_lookup() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = batch_json_with_scheduler(
            &session,
            session.initial_snapshot.state_fingerprint,
            r#"[{"candidate_id":"c0","candidate":{"kind":"bogus","extra":true}}]"#,
            r#"{"max_memory_mb":1}"#,
        );
        let deterministic_budget_hash = tactic_budget_hash(
            parse_machine_tactic_batch_request(&request)
                .unwrap()
                .deterministic_budget,
        );

        let response = run_machine_tactic_batch_request(&request, &mut session).unwrap();

        let MachineApiResponseEnvelope::SchedulerStopped(response) = response else {
            panic!("expected partial scheduler response");
        };
        assert_eq!(
            response.status,
            MachineApiResponseStatus::PartialResourceLimit
        );
        assert_eq!(
            response.scheduler_artifact.kind,
            MachineSchedulerArtifactKind::ResourceLimitExceeded
        );
        assert_eq!(
            response.scheduler_artifact.scope,
            MachineSchedulerArtifactScope::Batch
        );
        assert_eq!(response.endpoint_fields.completed_prefix_len, 0);
        assert!(response.endpoint_fields.results.is_empty());
        assert_eq!(
            response.endpoint_fields.previous_state_fingerprint,
            session.initial_snapshot.state_fingerprint
        );
        assert_eq!(
            response.endpoint_fields.deterministic_budget_hash,
            deterministic_budget_hash
        );
    }

    #[test]
    fn scheduler_observation_reports_timeout() {
        let kind = observe_run_scheduler_limits(
            MachineRunSchedulerLimits {
                timeout_ms: Some(5),
                max_memory_mb: None,
            },
            Duration::from_millis(5),
            None,
        );

        assert_eq!(kind, Some(MachineSchedulerArtifactKind::Timeout));
    }

    #[test]
    fn scheduler_observation_prefers_resource_limit_over_timeout() {
        let kind = observe_run_scheduler_limits(
            MachineRunSchedulerLimits {
                timeout_ms: Some(5),
                max_memory_mb: Some(1),
            },
            Duration::from_millis(5),
            Some(memory_limit_bytes(1) + 1),
        );

        assert_eq!(
            kind,
            Some(MachineSchedulerArtifactKind::ResourceLimitExceeded)
        );
    }

    #[test]
    fn scheduler_observation_allows_current_memory_below_limit() {
        let kind = observe_run_scheduler_limits(
            MachineRunSchedulerLimits {
                timeout_ms: None,
                max_memory_mb: Some(2),
            },
            Duration::ZERO,
            Some(memory_limit_bytes(1)),
        );

        assert_eq!(kind, None);
    }

    #[test]
    fn batch_scheduler_observation_prioritizes_resource_then_batch_timeout() {
        let resource = observe_batch_scheduler_limits(
            MachineBatchSchedulerLimits {
                per_candidate_timeout_ms: Some(5),
                batch_timeout_ms: Some(5),
                max_memory_mb: Some(1),
            },
            Duration::from_millis(5),
            Some(Duration::from_millis(5)),
            Some(memory_limit_bytes(1) + 1),
        );
        assert_eq!(
            resource,
            Some(BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::ResourceLimitExceeded,
                scope: MachineSchedulerArtifactScope::Batch
            })
        );

        let timeout = observe_batch_scheduler_limits(
            MachineBatchSchedulerLimits {
                per_candidate_timeout_ms: Some(5),
                batch_timeout_ms: Some(5),
                max_memory_mb: None,
            },
            Duration::from_millis(5),
            Some(Duration::from_millis(5)),
            None,
        );
        assert_eq!(
            timeout,
            Some(BatchSchedulerStop {
                kind: MachineSchedulerArtifactKind::Timeout,
                scope: MachineSchedulerArtifactScope::Batch
            })
        );
    }

    #[test]
    fn level_wire_rejects_noncanonical_succ_numeral() {
        assert!(parse_level_wire("1", &[], false).is_ok());
        assert!(parse_level_wire("succ 0", &[], false).is_err());
        assert!(parse_level_wire("max 0 0", &[], false).is_ok());
    }
}

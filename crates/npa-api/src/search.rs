use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{AxiomRef, ExportEntry, ExportKind, GlobalRef, Hash, Name, TermId, TermNode};
use npa_frontend::{MachineLocalDecl, MachineSurfaceCallableRef};
use npa_kernel::{expr::collect_apps, subst::instantiate, Ctx, Env, Expr, Level};
use npa_tactic::{
    CandidateApplyArg, CandidateRewriteRuleRef, MachineTacticCandidate, ResolvedSimpRule,
    RewriteDirection, RewriteSite, SimpRuleRef, TacticHead,
};
use sha2::{Digest, Sha256};

use crate::adapter::{
    machine_tactic_validate_machine_tactic_candidate, MachineApiDiagnosticPhase,
    MachineApiDiagnosticProjection,
};
use crate::current::{
    encode_machine_axiom_ref_wire, imported_axiom_ref_to_wire, MachineAxiomRefWire,
};
use crate::json::{JsonValue, JsonValueKind};
use crate::projection::VerifiedModuleContextEntry;
use crate::renderer::{
    render_machine_expr_view, MachineApiResolvedDisplayCoreRefOwner, MachineDisplayRenderScope,
    MachineDisplayRenderScopeEntry, MachineExprRendererContext, MachineGlobalRefView,
};
use crate::snapshot::{MachineSnapshotLookupError, MachineSnapshotMaterializationContext};
use crate::types::{
    format_goal_id_wire, format_hash_string, parse_goal_id_wire, parse_hash_string,
    parse_machine_api_name, parse_module_name_wire, HashString, MachineApiErrorResponse,
    MachineApiErrorWire, MachineApiOkResponse, MachineApiResponseEnvelope,
    MachineApiResponseStatus, MachineGoalView, MachineProofSession, SessionId, SnapshotId,
};
use crate::validation::{
    parse_request_body, parse_strict_u64_token, validate_json_object, FieldSpec, JsonFieldType,
    JsonPath, JsonPathElement, MachineApiErrorKind, MachineApiRequestError,
    MachineApiRequestErrorReason, ObjectSchema, StrictUnsignedIntegerError, ValidatedObject,
};
use crate::{
    machine_api_name_canonical_bytes, validate_machine_endpoint_envelope,
    MachineApiUpstreamDiagnostic, MachineApiVersion,
};

pub(crate) const THEOREM_INDEX_SCHEMA_VERSION: &str =
    "mvp-export-entry-v5-entry-kind-visible-heads-universe-params";
pub(crate) const SEARCH_PROFILE_VERSION: &str = "mvp-zero-score-v1";
pub(crate) const SUGGESTION_PROFILE_VERSION: &str = "mvp-suggested-candidates-v1";
pub const VERIFIED_PREMISE_IDENTITY_SCHEMA_VERSION: &str =
    "npa.machine-api.verified-premise-identity.v1";
pub const PREMISE_INDEX_ENTRY_SCHEMA_VERSION: &str = "npa.machine-api.premise-index-entry.v1";
pub const PREMISE_SEARCH_QUERY_PROFILE_VERSION: &str =
    "npa.machine-api.premise-search-query-profile.v2.axiom-aware-ranking";
pub const IMPORT_PROPOSAL_SCHEMA_VERSION: &str = "npa.machine-api.import-proposal.v1";
pub const RETRIEVAL_EVALUATION_SCHEMA_VERSION: &str = "npa.machine-api.retrieval-evaluation.v1";

const PREMISE_RANKING_BASE_SCORE: u64 = 10_000;
const DIRECT_AXIOM_USE_PENALTY: u64 = 4_000;
const TRANSITIVE_AXIOM_EXPANSION_PENALTY: u64 = 750;
const UNKNOWN_THEOREM_LEVEL_PENALTY: u64 = 2_500;
const UNVERIFIED_CANDIDATE_PENALTY: u64 = 5_000;
const HIGH_IMPORT_COST_UNIT_PENALTY: u64 = 100;
const UNRESOLVED_PREMISE_OBLIGATION_PENALTY: u64 = 100;
const GRAPH_AXIOM_PATH_PENALTY: u64 = 250;
const DISALLOWED_AXIOM_PENALTY: u64 = 100_000;

const FILTER_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("exclude_axioms", JsonFieldType::Boolean),
    FieldSpec::optional("allowed_modules", JsonFieldType::Array),
];
const VERIFIED_PREMISE_GLOBAL_REF_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("export_hash", JsonFieldType::String),
    FieldSpec::required("certificate_hash", JsonFieldType::String),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
];
const VERIFIED_PREMISE_AXIOM_SUMMARY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("direct_axioms", JsonFieldType::Array),
    FieldSpec::required("transitive_axioms", JsonFieldType::Array),
    FieldSpec::required("summary_hash", JsonFieldType::String),
];
const PREMISE_STRUCTURAL_REF_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("export_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
];
const PREMISE_STRUCTURAL_FEATURE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("target_head", JsonFieldType::Object).allow_null(),
    FieldSpec::required(
        "pi_binder_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("argument_universe_fingerprints", JsonFieldType::Array),
    FieldSpec::required("result_universe_fingerprint", JsonFieldType::String),
    FieldSpec::required("recursive_occurrences", JsonFieldType::Array),
    FieldSpec::required("equality_lhs_head", JsonFieldType::Object).allow_null(),
    FieldSpec::required("equality_rhs_head", JsonFieldType::Object).allow_null(),
    FieldSpec::required("propositional_connectives", JsonFieldType::Array),
    FieldSpec::required("referenced_inductives", JsonFieldType::Array),
    FieldSpec::required("normalized_expression_fingerprints", JsonFieldType::Array),
    FieldSpec::required("feature_hash", JsonFieldType::String),
];
const VERIFIED_PREMISE_IDENTITY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("export_hash", JsonFieldType::String),
    FieldSpec::required("certificate_hash", JsonFieldType::String),
    FieldSpec::required("global_ref", JsonFieldType::Object),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    FieldSpec::required("statement_core_hash", JsonFieldType::String),
    FieldSpec::required("axiom_summary", JsonFieldType::Object),
];
const PREMISE_RANKING_METADATA_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("score", JsonFieldType::UnsignedInteger { max: u64::MAX }),
    FieldSpec::optional("axiom_ranking", JsonFieldType::Object),
    FieldSpec::optional("type_aware", JsonFieldType::Object),
    FieldSpec::optional("mode_metadata", JsonFieldType::Array),
    FieldSpec::optional("premise_set", JsonFieldType::Object),
];
const PREMISE_AXIOM_RANKING_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("theorem_level", JsonFieldType::String),
    FieldSpec::required("candidate_verified", JsonFieldType::Boolean),
    FieldSpec::required("usable_under_axiom_policy", JsonFieldType::Boolean),
    FieldSpec::required(
        "direct_axiom_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "transitive_axiom_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "disallowed_axiom_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("axiom_paths", JsonFieldType::Array),
    FieldSpec::required("penalties", JsonFieldType::Object),
];
const PREMISE_AXIOM_PATH_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("source", JsonFieldType::String),
    FieldSpec::required("axiom", JsonFieldType::Object),
    FieldSpec::required(
        "path_length",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("graph_snapshot_hash", JsonFieldType::String).allow_null(),
];
const PREMISE_AXIOM_RANKING_PENALTY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "direct_axiom_use",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "transitive_axiom_expansion",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "unknown_theorem_level",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "unverified_candidate",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "high_import_cost",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "unresolved_premise_obligations",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "graph_axiom_path",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "disallowed_axiom",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("total", JsonFieldType::UnsignedInteger { max: u64::MAX }),
];
const PREMISE_MODE_METADATA_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("mode", JsonFieldType::String),
    FieldSpec::required("status", JsonFieldType::String),
    FieldSpec::required("reason", JsonFieldType::String),
    FieldSpec::required(
        "suggested_candidate_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "lexical_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const TYPE_AWARE_PREMISE_METADATA_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("status", JsonFieldType::String),
    FieldSpec::required("selected_mode", JsonFieldType::String).allow_null(),
    FieldSpec::required("universe_compatible", JsonFieldType::Boolean),
    FieldSpec::required("head_compatible", JsonFieldType::Boolean),
    FieldSpec::required("result_fits_goal", JsonFieldType::Boolean),
    FieldSpec::required(
        "pi_binder_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("unresolved_obligation_type_hashes", JsonFieldType::Array),
    FieldSpec::required("local_context_match_type_hashes", JsonFieldType::Array),
    FieldSpec::required("generated_argument_sources", JsonFieldType::Array),
    FieldSpec::required(
        "estimated_new_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "premise_size",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "goal_size",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const PREMISE_SET_METADATA_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "max_set_size",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("graph_snapshot_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("selected_premises", JsonFieldType::Array),
    FieldSpec::required("covered_goal_features", JsonFieldType::Array),
    FieldSpec::required("missing_goal_features", JsonFieldType::Array),
    FieldSpec::required("rejected_alternatives", JsonFieldType::Array),
    FieldSpec::required("import_requirements", JsonFieldType::Array),
    FieldSpec::required("axiom_impact", JsonFieldType::Object),
    FieldSpec::required("objective", JsonFieldType::Object),
];
const PREMISE_SET_FEATURE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("feature_hash", JsonFieldType::String),
];
const PREMISE_SET_SELECTED_PREMISE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("premise", JsonFieldType::Object),
    FieldSpec::required("added_features", JsonFieldType::Array),
    FieldSpec::required(
        "coverage_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "historical_co_use_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "graph_connectivity_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "set_size_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "import_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "axiom_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "final_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const PREMISE_SET_REJECTED_ALTERNATIVE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("premise", JsonFieldType::Object),
    FieldSpec::required("reason", JsonFieldType::String),
    FieldSpec::required("would_add_features", JsonFieldType::Array),
    FieldSpec::required(
        "coverage_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "historical_co_use_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "graph_connectivity_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "set_size_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "import_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "axiom_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "final_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const PREMISE_SET_AXIOM_IMPACT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "direct_axiom_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "transitive_axiom_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("summary_hash", JsonFieldType::String),
    FieldSpec::optional("axiom_paths", JsonFieldType::Array),
];
const PREMISE_SET_OBJECTIVE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required(
        "coverage_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "historical_co_use_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "graph_connectivity_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "set_size_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "import_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "axiom_cost_penalty",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "final_score",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];
const VERIFIED_PREMISE_INDEX_ENTRY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("identity", JsonFieldType::Object),
    FieldSpec::required("statement_core_hash", JsonFieldType::String),
    FieldSpec::required("structural_features", JsonFieldType::Object),
    FieldSpec::required("modes", JsonFieldType::Array),
    FieldSpec::required("source", JsonFieldType::String),
    FieldSpec::required("ranking_metadata", JsonFieldType::Object),
];
const UNTRUSTED_PREMISE_CANDIDATE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("candidate_hash", JsonFieldType::String),
    FieldSpec::required("source_label", JsonFieldType::String),
    FieldSpec::required("reason", JsonFieldType::String),
];
const PREMISE_INDEX_ENTRY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::optional("identity", JsonFieldType::Object),
    FieldSpec::optional("statement_core_hash", JsonFieldType::String),
    FieldSpec::optional("structural_features", JsonFieldType::Object),
    FieldSpec::optional("modes", JsonFieldType::Array),
    FieldSpec::optional("source", JsonFieldType::String),
    FieldSpec::optional("ranking_metadata", JsonFieldType::Object),
    FieldSpec::optional("candidate", JsonFieldType::Object),
];
const UNTRUSTED_PREMISE_INDEX_ENTRY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("candidate", JsonFieldType::Object),
];
const IMPORT_PROPOSAL_CANDIDATE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("source", JsonFieldType::String),
    FieldSpec::required("identity", JsonFieldType::Object),
];

pub type MachineTheoremSearchResponse =
    MachineApiResponseEnvelope<MachineTheoremSearchOkFields, MachineApiErrorWire, ()>;
pub type MachinePremiseSearchResponse =
    MachineApiResponseEnvelope<MachinePremiseSearchOkFields, MachineApiErrorWire, ()>;
pub type MachineImportProposalResponse =
    MachineApiResponseEnvelope<MachineImportProposalOkFields, MachineApiErrorWire, ()>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremSearchOkFields {
    pub query_fingerprint: Hash,
    pub theorem_index_fingerprint: Hash,
    pub search_profile_version: &'static str,
    pub suggestion_profile_version: &'static str,
    pub results: Vec<MachineTheoremSearchResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSearchOkFields {
    pub query_fingerprint: Hash,
    pub query_profile_hash: Hash,
    pub query_profile_version: &'static str,
    pub theorem_index_fingerprint: Hash,
    pub graph_snapshot_hash: Option<Hash>,
    pub visible_imports_fingerprint: Hash,
    pub retrieval_cache_key: MachineRetrievalCacheKey,
    pub selected_modes: Vec<MachineTheoremMode>,
    pub filters: MachineTheoremFilters,
    pub limit: u32,
    pub results: Vec<MachinePremiseSearchResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalOkFields {
    pub query_fingerprint: Hash,
    pub visible_imports_fingerprint: Hash,
    pub proposed_for_tasks: Vec<String>,
    pub proposals: Vec<MachineImportProposal>,
    pub rejected_candidates: Vec<MachineImportProposalRejectedCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremSearchResult {
    pub premise_id: String,
    pub global_ref: MachineTheoremGlobalRef,
    pub universe_params: Vec<String>,
    pub statement: MachineTheoremStatement,
    pub modes: Vec<MachineTheoremMode>,
    pub suggested_candidates: Vec<MachineSuggestedCandidate>,
    pub score: u64,
    pub axioms_used: Vec<MachineAxiomRefWire>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSearchResult {
    pub premise_id: String,
    pub verified_identity: MachineVerifiedPremiseIdentity,
    pub statement_core_hash: Hash,
    pub structural_features: MachinePremiseStructuralFeatures,
    pub selected_modes: Vec<MachineTheoremMode>,
    pub ranking_metadata: MachinePremiseRankingMetadata,
    pub candidate_provenance: MachinePremiseCandidateProvenance,
    pub untrusted_sidecar: MachinePremiseUntrustedSidecar,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalCacheKey {
    pub key_hash: Hash,
    pub environment_hash: Hash,
    pub goal_fingerprint: Hash,
    pub local_context_hash: Hash,
    pub query_fingerprint: Hash,
    pub query_profile_hash: Hash,
    pub theorem_index_fingerprint: Hash,
    pub graph_snapshot_hash: Option<Hash>,
    pub visible_imports_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalCacheEntry {
    pub key: MachineRetrievalCacheKey,
    pub result_identities: Vec<MachineRetrievalCacheResultIdentity>,
    pub ranking_payloads: Vec<MachineRetrievalCacheRankingPayload>,
    pub sidecar_scores: Vec<MachineRetrievalCacheSidecarScore>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalCacheResultIdentity {
    pub premise_id: String,
    pub verified_identity: MachineVerifiedPremiseIdentity,
    pub statement_core_hash: Hash,
    pub structural_features: MachinePremiseStructuralFeatures,
    pub selected_modes: Vec<MachineTheoremMode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalCacheRankingPayload {
    pub premise_id: String,
    pub ranking_metadata: MachinePremiseRankingMetadata,
    pub candidate_provenance: MachinePremiseCandidateProvenance,
    pub untrusted_sidecar: MachinePremiseUntrustedSidecar,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalCacheSidecarScore {
    pub premise_id: String,
    pub score: u64,
    pub graph_snapshot_hash: Option<Hash>,
    pub suggested_candidate_count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineRetrievalCacheRefreshError {
    KeyMismatch,
    VerifiedIdentityMismatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationFixture {
    pub schema: &'static str,
    pub cases: Vec<MachineRetrievalEvaluationCase>,
}

impl MachineRetrievalEvaluationFixture {
    pub fn new(mut cases: Vec<MachineRetrievalEvaluationCase>) -> Self {
        normalize_retrieval_evaluation_cases(&mut cases);
        Self {
            schema: RETRIEVAL_EVALUATION_SCHEMA_VERSION,
            cases,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationCase {
    pub case_id: String,
    pub goal_fingerprint: Hash,
    pub local_context_hash: Hash,
    pub expected_final_proof_premises: Vec<MachineVerifiedPremiseIdentity>,
    pub allowed_imports: Vec<MachineImportProposalImportIdentity>,
    pub axiom_policy: MachineRetrievalEvaluationAxiomPolicy,
    pub expected_theorem_index_fingerprint: Hash,
    pub theorem_index_fingerprint: Hash,
    pub graph_snapshot_hash: Option<Hash>,
    pub observed_graph_snapshot_hash: Option<Hash>,
    pub retrieved_premises: Vec<MachineRetrievalEvaluationRetrievedPremise>,
    pub import_proposals_accepted: u64,
    pub import_proposals_rejected: u64,
    pub baseline_proof_completed: Option<bool>,
    pub retrieval_proof_completed: Option<bool>,
    pub latency_micros: u64,
    pub cache_hit: bool,
    pub checker_disagreement: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationRetrievedPremise {
    pub identity: MachineVerifiedPremiseIdentity,
    pub ranking_score: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationAxiomPolicy {
    pub allowed_axioms: Vec<MachineAxiomRefWire>,
}

impl MachineRetrievalEvaluationAxiomPolicy {
    pub fn new(mut allowed_axioms: Vec<MachineAxiomRefWire>) -> Self {
        sort_dedup_axiom_refs(&mut allowed_axioms);
        Self { allowed_axioms }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationSummary {
    pub schema: &'static str,
    pub case_count: u64,
    pub evaluated_case_count: u64,
    pub rejected_cases: Vec<MachineRetrievalEvaluationRejectedCase>,
    pub metrics: MachineRetrievalEvaluationMetrics,
}

impl MachineRetrievalEvaluationSummary {
    pub fn ci_snapshot_lines(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("case_count={}\n", self.case_count));
        out.push_str(&format!(
            "evaluated_case_count={}\n",
            self.evaluated_case_count
        ));
        out.push_str(&self.metrics.ci_snapshot_lines());
        for rejected in &self.rejected_cases {
            let reasons = rejected
                .reasons
                .iter()
                .map(|reason| reason.as_str())
                .collect::<Vec<_>>()
                .join(",");
            out.push_str(&format!("rejected_case.{}={}\n", rejected.case_id, reasons));
        }
        out
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationMetrics {
    pub recall_at_1_basis_points: u64,
    pub recall_at_4_basis_points: u64,
    pub recall_at_8_basis_points: u64,
    pub recall_at_32_basis_points: u64,
    pub precision_at_1_basis_points: u64,
    pub precision_at_4_basis_points: u64,
    pub precision_at_8_basis_points: u64,
    pub precision_at_32_basis_points: u64,
    pub final_proof_premise_recall_basis_points: u64,
    pub mean_reciprocal_rank_microunits: u64,
    pub proof_completion_uplift_basis_points: i64,
    pub proof_completion_uplift_case_count: u64,
    pub unused_premise_ratio_basis_points: u64,
    pub import_proposal_acceptance_rate_basis_points: u64,
    pub axiom_policy_violation_rate_basis_points: u64,
    pub p50_latency_micros: u64,
    pub p95_latency_micros: u64,
    pub cache_hit_rate_basis_points: u64,
}

impl MachineRetrievalEvaluationMetrics {
    fn ci_snapshot_lines(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "recall_at_1_basis_points={}\n",
            self.recall_at_1_basis_points
        ));
        out.push_str(&format!(
            "recall_at_4_basis_points={}\n",
            self.recall_at_4_basis_points
        ));
        out.push_str(&format!(
            "recall_at_8_basis_points={}\n",
            self.recall_at_8_basis_points
        ));
        out.push_str(&format!(
            "recall_at_32_basis_points={}\n",
            self.recall_at_32_basis_points
        ));
        out.push_str(&format!(
            "precision_at_1_basis_points={}\n",
            self.precision_at_1_basis_points
        ));
        out.push_str(&format!(
            "precision_at_4_basis_points={}\n",
            self.precision_at_4_basis_points
        ));
        out.push_str(&format!(
            "precision_at_8_basis_points={}\n",
            self.precision_at_8_basis_points
        ));
        out.push_str(&format!(
            "precision_at_32_basis_points={}\n",
            self.precision_at_32_basis_points
        ));
        out.push_str(&format!(
            "final_proof_premise_recall_basis_points={}\n",
            self.final_proof_premise_recall_basis_points
        ));
        out.push_str(&format!(
            "mean_reciprocal_rank_microunits={}\n",
            self.mean_reciprocal_rank_microunits
        ));
        out.push_str(&format!(
            "proof_completion_uplift_basis_points={}\n",
            self.proof_completion_uplift_basis_points
        ));
        out.push_str(&format!(
            "proof_completion_uplift_case_count={}\n",
            self.proof_completion_uplift_case_count
        ));
        out.push_str(&format!(
            "unused_premise_ratio_basis_points={}\n",
            self.unused_premise_ratio_basis_points
        ));
        out.push_str(&format!(
            "import_proposal_acceptance_rate_basis_points={}\n",
            self.import_proposal_acceptance_rate_basis_points
        ));
        out.push_str(&format!(
            "axiom_policy_violation_rate_basis_points={}\n",
            self.axiom_policy_violation_rate_basis_points
        ));
        out.push_str(&format!("p50_latency_micros={}\n", self.p50_latency_micros));
        out.push_str(&format!("p95_latency_micros={}\n", self.p95_latency_micros));
        out.push_str(&format!(
            "cache_hit_rate_basis_points={}\n",
            self.cache_hit_rate_basis_points
        ));
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRetrievalEvaluationRejectedCase {
    pub case_id: String,
    pub reasons: Vec<MachineRetrievalEvaluationRejectionReason>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineRetrievalEvaluationRejectionReason {
    StaleGraphSnapshot,
    StaleTheoremIndex,
    CheckerDisagreement,
    ImportHashMismatch,
    DisallowedAxiom,
}

impl MachineRetrievalEvaluationRejectionReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StaleGraphSnapshot => "stale_graph_snapshot",
            Self::StaleTheoremIndex => "stale_theorem_index",
            Self::CheckerDisagreement => "checker_disagreement",
            Self::ImportHashMismatch => "import_hash_mismatch",
            Self::DisallowedAxiom => "disallowed_axiom",
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineRetrievalCache {
    entries: BTreeMap<Hash, MachineRetrievalCacheEntry>,
}

impl MachineRetrievalCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(
        &mut self,
        entry: MachineRetrievalCacheEntry,
    ) -> Option<MachineRetrievalCacheEntry> {
        self.entries.insert(entry.key.key_hash, entry)
    }

    pub fn get(&self, key: &MachineRetrievalCacheKey) -> Option<&MachineRetrievalCacheEntry> {
        self.entries
            .get(&key.key_hash)
            .filter(|entry| entry.key == *key)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

pub fn machine_retrieval_cache_entry_from_premise_search(
    search: &MachinePremiseSearchOkFields,
) -> MachineRetrievalCacheEntry {
    MachineRetrievalCacheEntry {
        key: search.retrieval_cache_key.clone(),
        result_identities: machine_retrieval_cache_result_identities(&search.results),
        ranking_payloads: machine_retrieval_cache_ranking_payloads(&search.results),
        sidecar_scores: machine_retrieval_cache_sidecar_scores(search),
    }
}

pub fn refresh_machine_retrieval_cache_ranking(
    entry: &MachineRetrievalCacheEntry,
    search: &MachinePremiseSearchOkFields,
) -> Result<MachineRetrievalCacheEntry, MachineRetrievalCacheRefreshError> {
    if entry.key != search.retrieval_cache_key {
        return Err(MachineRetrievalCacheRefreshError::KeyMismatch);
    }
    let result_identities = machine_retrieval_cache_result_identities(&search.results);
    if entry.result_identities != result_identities {
        return Err(MachineRetrievalCacheRefreshError::VerifiedIdentityMismatch);
    }
    Ok(MachineRetrievalCacheEntry {
        key: entry.key.clone(),
        result_identities,
        ranking_payloads: machine_retrieval_cache_ranking_payloads(&search.results),
        sidecar_scores: machine_retrieval_cache_sidecar_scores(search),
    })
}

pub fn machine_retrieval_evaluation_summary(
    fixture: &MachineRetrievalEvaluationFixture,
) -> MachineRetrievalEvaluationSummary {
    let mut cases = fixture.cases.clone();
    normalize_retrieval_evaluation_cases(&mut cases);
    let mut rejected_cases = Vec::new();
    let mut acc = MachineRetrievalEvaluationAccumulator::default();

    for case in &cases {
        acc.observe_case_side_effect_metrics(case);
        let reasons = retrieval_evaluation_rejection_reasons(case);
        if reasons.is_empty() {
            acc.observe_evaluated_case(case);
        } else {
            rejected_cases.push(MachineRetrievalEvaluationRejectedCase {
                case_id: case.case_id.clone(),
                reasons,
            });
        }
    }

    MachineRetrievalEvaluationSummary {
        schema: RETRIEVAL_EVALUATION_SCHEMA_VERSION,
        case_count: cases.len() as u64,
        evaluated_case_count: acc.evaluated_case_count,
        rejected_cases,
        metrics: acc.finish(),
    }
}

pub fn machine_retrieval_evaluation_ci_snapshot(
    summary: &MachineRetrievalEvaluationSummary,
) -> String {
    summary.ci_snapshot_lines()
}

#[derive(Default)]
struct MachineRetrievalEvaluationAccumulator {
    evaluated_case_count: u64,
    recall_hits: [u64; 4],
    recall_denominators: [u64; 4],
    precision_hits: [u64; 4],
    precision_denominators: [u64; 4],
    final_proof_hits: u64,
    final_proof_denominator: u64,
    reciprocal_rank_microunits: u64,
    reciprocal_rank_case_count: u64,
    proof_completion_delta: i64,
    proof_completion_case_count: u64,
    unused_premises: u64,
    retrieved_premises: u64,
    import_proposals_accepted: u64,
    import_proposals_total: u64,
    axiom_policy_violations: u64,
    axiom_policy_result_count: u64,
    latency_micros: Vec<u64>,
    cache_hits: u64,
}

impl MachineRetrievalEvaluationAccumulator {
    fn observe_case_side_effect_metrics(&mut self, case: &MachineRetrievalEvaluationCase) {
        self.import_proposals_accepted = self
            .import_proposals_accepted
            .saturating_add(case.import_proposals_accepted);
        self.import_proposals_total = self
            .import_proposals_total
            .saturating_add(case.import_proposals_accepted)
            .saturating_add(case.import_proposals_rejected);
        self.axiom_policy_result_count = self
            .axiom_policy_result_count
            .saturating_add(case.retrieved_premises.len() as u64);
        self.axiom_policy_violations = self
            .axiom_policy_violations
            .saturating_add(axiom_policy_violation_count(case));
    }

    fn observe_evaluated_case(&mut self, case: &MachineRetrievalEvaluationCase) {
        self.evaluated_case_count = self.evaluated_case_count.saturating_add(1);
        let expected = retrieval_evaluation_expected_keys(case);
        let ranked = case
            .retrieved_premises
            .iter()
            .map(|premise| premise.identity.identity_hash())
            .collect::<Vec<_>>();
        for (index, limit) in [1usize, 4, 8, 32].into_iter().enumerate() {
            let prefix = ranked.iter().take(limit).copied().collect::<Vec<_>>();
            let hits = retrieval_evaluation_unique_hits(&expected, &prefix);
            self.recall_hits[index] = self.recall_hits[index].saturating_add(hits);
            self.recall_denominators[index] = self.recall_denominators[index]
                .saturating_add(u64::try_from(expected.len()).unwrap_or(u64::MAX));
            self.precision_hits[index] = self.precision_hits[index].saturating_add(hits);
            self.precision_denominators[index] = self.precision_denominators[index]
                .saturating_add(u64::try_from(prefix.len()).unwrap_or(u64::MAX));
        }
        self.final_proof_hits = self
            .final_proof_hits
            .saturating_add(retrieval_evaluation_unique_hits(&expected, &ranked));
        self.final_proof_denominator = self
            .final_proof_denominator
            .saturating_add(u64::try_from(expected.len()).unwrap_or(u64::MAX));
        if !expected.is_empty() {
            self.reciprocal_rank_case_count = self.reciprocal_rank_case_count.saturating_add(1);
            self.reciprocal_rank_microunits = self.reciprocal_rank_microunits.saturating_add(
                retrieval_evaluation_reciprocal_rank_microunits(&expected, &ranked),
            );
        }
        self.unused_premises = self
            .unused_premises
            .saturating_add(ranked.iter().filter(|key| !expected.contains(*key)).count() as u64);
        self.retrieved_premises = self
            .retrieved_premises
            .saturating_add(u64::try_from(ranked.len()).unwrap_or(u64::MAX));
        if let (Some(baseline), Some(retrieval)) = (
            case.baseline_proof_completed,
            case.retrieval_proof_completed,
        ) {
            self.proof_completion_case_count = self.proof_completion_case_count.saturating_add(1);
            self.proof_completion_delta +=
                retrieval_completion_value(retrieval) - retrieval_completion_value(baseline);
        }
        self.latency_micros.push(case.latency_micros);
        if case.cache_hit {
            self.cache_hits = self.cache_hits.saturating_add(1);
        }
    }

    fn finish(mut self) -> MachineRetrievalEvaluationMetrics {
        self.latency_micros.sort_unstable();
        MachineRetrievalEvaluationMetrics {
            recall_at_1_basis_points: ratio_basis_points(
                self.recall_hits[0],
                self.recall_denominators[0],
            ),
            recall_at_4_basis_points: ratio_basis_points(
                self.recall_hits[1],
                self.recall_denominators[1],
            ),
            recall_at_8_basis_points: ratio_basis_points(
                self.recall_hits[2],
                self.recall_denominators[2],
            ),
            recall_at_32_basis_points: ratio_basis_points(
                self.recall_hits[3],
                self.recall_denominators[3],
            ),
            precision_at_1_basis_points: ratio_basis_points(
                self.precision_hits[0],
                self.precision_denominators[0],
            ),
            precision_at_4_basis_points: ratio_basis_points(
                self.precision_hits[1],
                self.precision_denominators[1],
            ),
            precision_at_8_basis_points: ratio_basis_points(
                self.precision_hits[2],
                self.precision_denominators[2],
            ),
            precision_at_32_basis_points: ratio_basis_points(
                self.precision_hits[3],
                self.precision_denominators[3],
            ),
            final_proof_premise_recall_basis_points: ratio_basis_points(
                self.final_proof_hits,
                self.final_proof_denominator,
            ),
            mean_reciprocal_rank_microunits: ratio_u64(
                self.reciprocal_rank_microunits,
                self.reciprocal_rank_case_count,
            ),
            proof_completion_uplift_basis_points: ratio_basis_points_i64(
                self.proof_completion_delta,
                self.proof_completion_case_count,
            ),
            proof_completion_uplift_case_count: self.proof_completion_case_count,
            unused_premise_ratio_basis_points: ratio_basis_points(
                self.unused_premises,
                self.retrieved_premises,
            ),
            import_proposal_acceptance_rate_basis_points: ratio_basis_points(
                self.import_proposals_accepted,
                self.import_proposals_total,
            ),
            axiom_policy_violation_rate_basis_points: ratio_basis_points(
                self.axiom_policy_violations,
                self.axiom_policy_result_count,
            ),
            p50_latency_micros: nearest_rank_percentile(&self.latency_micros, 50),
            p95_latency_micros: nearest_rank_percentile(&self.latency_micros, 95),
            cache_hit_rate_basis_points: ratio_basis_points(
                self.cache_hits,
                self.evaluated_case_count,
            ),
        }
    }
}

fn normalize_retrieval_evaluation_cases(cases: &mut [MachineRetrievalEvaluationCase]) {
    for case in cases.iter_mut() {
        case.expected_final_proof_premises
            .sort_by_key(|identity| identity.identity_hash());
        case.expected_final_proof_premises
            .dedup_by_key(|identity| identity.identity_hash());
        case.allowed_imports.sort_by_key(import_identity_key);
        case.allowed_imports
            .dedup_by(|lhs, rhs| import_identity_key(lhs) == import_identity_key(rhs));
        sort_dedup_axiom_refs(&mut case.axiom_policy.allowed_axioms);
    }
    cases.sort_by(|lhs, rhs| lhs.case_id.cmp(&rhs.case_id));
}

fn retrieval_evaluation_rejection_reasons(
    case: &MachineRetrievalEvaluationCase,
) -> Vec<MachineRetrievalEvaluationRejectionReason> {
    let mut reasons = Vec::new();
    if case.graph_snapshot_hash != case.observed_graph_snapshot_hash {
        reasons.push(MachineRetrievalEvaluationRejectionReason::StaleGraphSnapshot);
    }
    if case.expected_theorem_index_fingerprint != case.theorem_index_fingerprint {
        reasons.push(MachineRetrievalEvaluationRejectionReason::StaleTheoremIndex);
    }
    if case.checker_disagreement {
        reasons.push(MachineRetrievalEvaluationRejectionReason::CheckerDisagreement);
    }
    if retrieval_evaluation_has_import_hash_mismatch(case) {
        reasons.push(MachineRetrievalEvaluationRejectionReason::ImportHashMismatch);
    }
    if axiom_policy_violation_count(case) != 0 {
        reasons.push(MachineRetrievalEvaluationRejectionReason::DisallowedAxiom);
    }
    reasons
}

fn retrieval_evaluation_expected_keys(case: &MachineRetrievalEvaluationCase) -> BTreeSet<Hash> {
    case.expected_final_proof_premises
        .iter()
        .map(MachineVerifiedPremiseIdentity::identity_hash)
        .collect()
}

fn retrieval_evaluation_unique_hits(expected: &BTreeSet<Hash>, ranked: &[Hash]) -> u64 {
    ranked
        .iter()
        .filter(|key| expected.contains(*key))
        .copied()
        .collect::<BTreeSet<_>>()
        .len() as u64
}

fn retrieval_evaluation_reciprocal_rank_microunits(
    expected: &BTreeSet<Hash>,
    ranked: &[Hash],
) -> u64 {
    ranked
        .iter()
        .position(|key| expected.contains(key))
        .map(|index| 1_000_000 / u64::try_from(index + 1).unwrap_or(u64::MAX))
        .unwrap_or(0)
}

fn retrieval_evaluation_has_import_hash_mismatch(case: &MachineRetrievalEvaluationCase) -> bool {
    case.retrieved_premises.iter().any(|premise| {
        case.allowed_imports
            .iter()
            .find(|allowed| allowed.module == premise.identity.module)
            .is_some_and(|allowed| {
                allowed.export_hash != premise.identity.export_hash
                    || allowed.certificate_hash != premise.identity.certificate_hash
            })
    })
}

fn axiom_policy_violation_count(case: &MachineRetrievalEvaluationCase) -> u64 {
    case.retrieved_premises
        .iter()
        .filter(|premise| {
            !retrieval_evaluation_axioms_allowed(&case.axiom_policy, &premise.identity)
        })
        .count() as u64
}

fn retrieval_evaluation_axioms_allowed(
    policy: &MachineRetrievalEvaluationAxiomPolicy,
    identity: &MachineVerifiedPremiseIdentity,
) -> bool {
    let allowed = policy
        .allowed_axioms
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<BTreeSet<_>>();
    identity
        .axiom_summary
        .direct_axioms
        .iter()
        .chain(identity.axiom_summary.transitive_axioms.iter())
        .all(|axiom| allowed.contains(&encode_machine_axiom_ref_wire(axiom)))
}

fn import_identity_key(identity: &MachineImportProposalImportIdentity) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend(
        machine_api_name_canonical_bytes(&identity.module)
            .expect("import identity module names must be machine-api canonical"),
    );
    out.extend_from_slice(&identity.export_hash);
    out.extend_from_slice(&identity.certificate_hash);
    out
}

fn nearest_rank_percentile(sorted_values: &[u64], percentile: u64) -> u64 {
    if sorted_values.is_empty() {
        return 0;
    }
    let len = sorted_values.len() as u64;
    let rank = len
        .saturating_mul(percentile)
        .saturating_add(99)
        .checked_div(100)
        .unwrap_or(1)
        .max(1);
    let index = usize::try_from(rank - 1).unwrap_or(usize::MAX);
    sorted_values
        .get(index)
        .copied()
        .unwrap_or_else(|| *sorted_values.last().expect("non-empty checked above"))
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

fn ratio_u64(numerator: u64, denominator: u64) -> u64 {
    numerator.checked_div(denominator).unwrap_or(0)
}

fn retrieval_completion_value(completed: bool) -> i64 {
    if completed {
        1
    } else {
        0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseCandidateProvenance {
    pub premise_source: MachinePremiseIndexSource,
    pub suggestion_profile_version: &'static str,
    pub suggested_candidate_count: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseUntrustedSidecar {
    pub suggested_candidates: Vec<MachineSuggestedCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremGlobalRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremStatement {
    pub core_hash: Hash,
    pub head: Option<MachineGlobalRefView>,
    pub machine: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineVerifiedPremiseGlobalRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineVerifiedPremiseAxiomSummary {
    pub direct_axioms: Vec<MachineAxiomRefWire>,
    pub transitive_axioms: Vec<MachineAxiomRefWire>,
    pub summary_hash: Hash,
}

impl MachineVerifiedPremiseAxiomSummary {
    pub fn new(
        mut direct_axioms: Vec<MachineAxiomRefWire>,
        mut transitive_axioms: Vec<MachineAxiomRefWire>,
    ) -> Self {
        sort_dedup_axiom_refs(&mut direct_axioms);
        sort_dedup_axiom_refs(&mut transitive_axioms);
        let summary_hash = verified_premise_axiom_summary_hash(&direct_axioms, &transitive_axioms);
        Self {
            direct_axioms,
            transitive_axioms,
            summary_hash,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineVerifiedPremiseIdentity {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub global_ref: MachineVerifiedPremiseGlobalRef,
    pub decl_interface_hash: Hash,
    pub statement_core_hash: Hash,
    pub axiom_summary: MachineVerifiedPremiseAxiomSummary,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: npa_tactic::GoalId,
    pub proposed_for_tasks: Vec<String>,
    pub candidates: Vec<MachineImportProposalCandidate>,
    pub expected_visible_imports_fingerprint: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalCandidate {
    pub source: MachineImportProposalCandidateSource,
    pub identity: MachineVerifiedPremiseIdentity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineImportProposalCandidateSource {
    VerifiedClosure,
    PackageTheoremIndex,
}

impl MachineImportProposalCandidateSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::VerifiedClosure => "verified_closure",
            Self::PackageTheoremIndex => "package_theorem_index",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "verified_closure" => Some(Self::VerifiedClosure),
            "package_theorem_index" => Some(Self::PackageTheoremIndex),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposal {
    pub proposal_hash: Hash,
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub proposed_for_tasks: Vec<String>,
    pub new_axiom_summary: MachineVerifiedPremiseAxiomSummary,
    pub estimated_downstream_rebuild: u32,
    pub reason: MachineImportProposalReason,
    pub candidate_source: MachineImportProposalCandidateSource,
    pub candidate_identity: MachineVerifiedPremiseIdentity,
    pub visible_imports_fingerprint: Hash,
    pub approval: MachineImportProposalApprovalHook,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalApprovalHook {
    pub current_session_id: SessionId,
    pub current_session_root_hash: Hash,
    pub required_direct_import: MachineImportProposalImportIdentity,
    pub current_snapshot_id: SnapshotId,
    pub current_state_fingerprint: Hash,
    pub requires_new_snapshot: bool,
    pub requires_certificate_regeneration: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalImportIdentity {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
}

impl From<&MachineVerifiedPremiseIdentity> for MachineImportProposalImportIdentity {
    fn from(identity: &MachineVerifiedPremiseIdentity) -> Self {
        Self {
            module: identity.module.clone(),
            export_hash: identity.export_hash,
            certificate_hash: identity.certificate_hash,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalRejectedCandidate {
    pub rejection_hash: Hash,
    pub source: MachineImportProposalCandidateSource,
    pub identity: MachineVerifiedPremiseIdentity,
    pub reason: MachineImportProposalRejectionReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineImportProposalReason {
    ClosureModuleNotDirect,
    PackageCandidateNotImported,
}

impl MachineImportProposalReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ClosureModuleNotDirect => "closure_module_not_direct",
            Self::PackageCandidateNotImported => "package_candidate_not_imported",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineImportProposalRejectionReason {
    AlreadyDirectImport,
    StaleExportHash,
    StaleCertificateHash,
    DisallowedAxiom,
    IncompatiblePackage,
    CyclicImportProposal,
    IdentityMismatch,
}

impl MachineImportProposalRejectionReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AlreadyDirectImport => "already_direct_import",
            Self::StaleExportHash => "stale_export_hash",
            Self::StaleCertificateHash => "stale_certificate_hash",
            Self::DisallowedAxiom => "disallowed_axiom",
            Self::IncompatiblePackage => "incompatible_package",
            Self::CyclicImportProposal => "cyclic_import_proposal",
            Self::IdentityMismatch => "identity_mismatch",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalAcceptance {
    pub proposal_hash: Hash,
    pub rebuilt_snapshot_id: SnapshotId,
    pub rebuilt_state_fingerprint: Hash,
    pub direct_import: MachineImportProposalImportIdentity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineImportProposalAcceptanceError {
    StaleProposalIdentity,
    RebuiltSnapshotRequired,
    ProposalImportNotDirect,
    DisallowedAxiom,
}

impl MachineVerifiedPremiseIdentity {
    pub fn new(
        module: Name,
        export_hash: Hash,
        certificate_hash: Hash,
        global_ref: MachineVerifiedPremiseGlobalRef,
        decl_interface_hash: Hash,
        statement_core_hash: Hash,
        axiom_summary: MachineVerifiedPremiseAxiomSummary,
    ) -> Result<Self, MachinePremiseIndexError> {
        validate_verified_premise_identity_parts(
            &module,
            &export_hash,
            &certificate_hash,
            &global_ref,
            &decl_interface_hash,
            &axiom_summary,
            &JsonPath::root(),
        )?;
        Ok(Self {
            module,
            export_hash,
            certificate_hash,
            global_ref,
            decl_interface_hash,
            statement_core_hash,
            axiom_summary,
        })
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        verified_premise_identity_canonical_bytes(self)
    }

    pub fn identity_hash(&self) -> Hash {
        sha256(&self.canonical_bytes())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachinePremiseStructuralRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Option<Hash>,
    pub decl_interface_hash: Hash,
}

impl MachinePremiseStructuralRef {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        machine_premise_structural_ref_canonical_bytes(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremisePropositionalConnective {
    Forall,
    Implication,
    PropositionSort,
}

impl MachinePremisePropositionalConnective {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Forall => "forall",
            Self::Implication => "implication",
            Self::PropositionSort => "proposition_sort",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "forall" => Some(Self::Forall),
            "implication" => Some(Self::Implication),
            "proposition_sort" => Some(Self::PropositionSort),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseStructuralFeatures {
    pub target_head: Option<MachinePremiseStructuralRef>,
    pub pi_binder_count: u32,
    pub argument_universe_fingerprints: Vec<Hash>,
    pub result_universe_fingerprint: Hash,
    pub recursive_occurrences: Vec<MachinePremiseStructuralRef>,
    pub equality_lhs_head: Option<MachinePremiseStructuralRef>,
    pub equality_rhs_head: Option<MachinePremiseStructuralRef>,
    pub propositional_connectives: Vec<MachinePremisePropositionalConnective>,
    pub referenced_inductives: Vec<MachinePremiseStructuralRef>,
    pub normalized_expression_fingerprints: Vec<Hash>,
    pub feature_hash: Hash,
}

impl MachinePremiseStructuralFeatures {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        target_head: Option<MachinePremiseStructuralRef>,
        pi_binder_count: u32,
        argument_universe_fingerprints: Vec<Hash>,
        result_universe_fingerprint: Hash,
        mut recursive_occurrences: Vec<MachinePremiseStructuralRef>,
        equality_lhs_head: Option<MachinePremiseStructuralRef>,
        equality_rhs_head: Option<MachinePremiseStructuralRef>,
        mut propositional_connectives: Vec<MachinePremisePropositionalConnective>,
        mut referenced_inductives: Vec<MachinePremiseStructuralRef>,
        normalized_expression_fingerprints: Vec<Hash>,
    ) -> Self {
        recursive_occurrences.sort();
        recursive_occurrences.dedup();
        propositional_connectives.sort();
        propositional_connectives.dedup();
        referenced_inductives.sort();
        referenced_inductives.dedup();
        let feature_hash = machine_premise_structural_features_hash(
            target_head.as_ref(),
            pi_binder_count,
            &argument_universe_fingerprints,
            &result_universe_fingerprint,
            &recursive_occurrences,
            equality_lhs_head.as_ref(),
            equality_rhs_head.as_ref(),
            &propositional_connectives,
            &referenced_inductives,
            &normalized_expression_fingerprints,
        );
        Self {
            target_head,
            pi_binder_count,
            argument_universe_fingerprints,
            result_universe_fingerprint,
            recursive_occurrences,
            equality_lhs_head,
            equality_rhs_head,
            propositional_connectives,
            referenced_inductives,
            normalized_expression_fingerprints,
            feature_hash,
        }
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        machine_premise_structural_features_canonical_bytes(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseIndexSource {
    DirectImport,
    PackageTheoremIndex,
}

impl MachinePremiseIndexSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectImport => "direct_import",
            Self::PackageTheoremIndex => "package_theorem_index",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "direct_import" => Some(Self::DirectImport),
            "package_theorem_index" => Some(Self::PackageTheoremIndex),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseRankingMetadata {
    pub score: u64,
    pub axiom_ranking: MachinePremiseAxiomRankingMetadata,
    pub type_aware: MachineTypeAwarePremiseMetadata,
    pub mode_metadata: Vec<MachinePremiseModeMetadata>,
    pub premise_set: Option<MachinePremiseSetMetadata>,
}

impl MachinePremiseRankingMetadata {
    pub fn score_only(score: u64) -> Self {
        Self {
            score,
            axiom_ranking: MachinePremiseAxiomRankingMetadata::verified_no_axioms(),
            type_aware: MachineTypeAwarePremiseMetadata::not_evaluated(),
            mode_metadata: Vec::new(),
            premise_set: None,
        }
    }

    fn with_axiom_ranking(score: u64, axiom_ranking: MachinePremiseAxiomRankingMetadata) -> Self {
        Self {
            score,
            axiom_ranking,
            type_aware: MachineTypeAwarePremiseMetadata::not_evaluated(),
            mode_metadata: Vec::new(),
            premise_set: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseAxiomRankingMetadata {
    pub theorem_level: MachinePremiseTheoremLevel,
    pub candidate_verified: bool,
    pub usable_under_axiom_policy: bool,
    pub direct_axiom_count: u32,
    pub transitive_axiom_count: u32,
    pub disallowed_axiom_count: u32,
    pub axiom_paths: Vec<MachinePremiseAxiomPath>,
    pub penalties: MachinePremiseAxiomRankingPenalties,
}

impl MachinePremiseAxiomRankingMetadata {
    pub fn verified_no_axioms() -> Self {
        Self {
            theorem_level: MachinePremiseTheoremLevel::VerifiedCertificate,
            candidate_verified: true,
            usable_under_axiom_policy: true,
            direct_axiom_count: 0,
            transitive_axiom_count: 0,
            disallowed_axiom_count: 0,
            axiom_paths: Vec::new(),
            penalties: MachinePremiseAxiomRankingPenalties::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseTheoremLevel {
    VerifiedCertificate,
    Unknown,
}

impl MachinePremiseTheoremLevel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::VerifiedCertificate => "verified_certificate",
            Self::Unknown => "unknown",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "verified_certificate" => Some(Self::VerifiedCertificate),
            "unknown" => Some(Self::Unknown),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseAxiomPath {
    pub source: MachinePremiseAxiomPathSource,
    pub axiom: MachineAxiomRefWire,
    pub path_length: u32,
    pub graph_snapshot_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseAxiomPathSource {
    DirectAxiomUse,
    TransitiveDependency,
    GraphSnapshot,
}

impl MachinePremiseAxiomPathSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectAxiomUse => "direct_axiom_use",
            Self::TransitiveDependency => "transitive_dependency",
            Self::GraphSnapshot => "graph_snapshot",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "direct_axiom_use" => Some(Self::DirectAxiomUse),
            "transitive_dependency" => Some(Self::TransitiveDependency),
            "graph_snapshot" => Some(Self::GraphSnapshot),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachinePremiseAxiomRankingPenalties {
    pub direct_axiom_use: u64,
    pub transitive_axiom_expansion: u64,
    pub unknown_theorem_level: u64,
    pub unverified_candidate: u64,
    pub high_import_cost: u64,
    pub unresolved_premise_obligations: u64,
    pub graph_axiom_path: u64,
    pub disallowed_axiom: u64,
    pub total: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSetMetadata {
    pub max_set_size: u32,
    pub graph_snapshot_hash: Option<Hash>,
    pub selected_premises: Vec<MachinePremiseSetSelectedPremise>,
    pub covered_goal_features: Vec<MachinePremiseSetFeature>,
    pub missing_goal_features: Vec<MachinePremiseSetFeature>,
    pub rejected_alternatives: Vec<MachinePremiseSetRejectedAlternative>,
    pub import_requirements: Vec<Name>,
    pub axiom_impact: MachinePremiseSetAxiomImpact,
    pub objective: MachinePremiseSetObjective,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSetSelectedPremise {
    pub premise: MachinePremiseStructuralRef,
    pub added_features: Vec<MachinePremiseSetFeature>,
    pub objective: MachinePremiseSetObjective,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSetRejectedAlternative {
    pub premise: MachinePremiseStructuralRef,
    pub reason: MachinePremiseSetRejectedReason,
    pub would_add_features: Vec<MachinePremiseSetFeature>,
    pub objective: MachinePremiseSetObjective,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseSetRejectedReason {
    DuplicateCandidate,
    NoNewCoverage,
    MaxSetSizeReached,
    NonPositiveObjective,
}

impl MachinePremiseSetRejectedReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DuplicateCandidate => "duplicate_candidate",
            Self::NoNewCoverage => "no_new_coverage",
            Self::MaxSetSizeReached => "max_set_size_reached",
            Self::NonPositiveObjective => "non_positive_objective",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "duplicate_candidate" => Some(Self::DuplicateCandidate),
            "no_new_coverage" => Some(Self::NoNewCoverage),
            "max_set_size_reached" => Some(Self::MaxSetSizeReached),
            "non_positive_objective" => Some(Self::NonPositiveObjective),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSetAxiomImpact {
    pub direct_axiom_count: u32,
    pub transitive_axiom_count: u32,
    pub summary_hash: Hash,
    pub axiom_paths: Vec<MachinePremiseAxiomPath>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachinePremiseSetObjective {
    pub coverage_score: u64,
    pub historical_co_use_score: u64,
    pub graph_connectivity_score: u64,
    pub set_size_penalty: u64,
    pub import_cost_penalty: u64,
    pub axiom_cost_penalty: u64,
    pub final_score: u64,
}

impl MachinePremiseSetObjective {
    fn combined_reward(&self) -> u64 {
        self.coverage_score
            .saturating_add(self.historical_co_use_score)
            .saturating_add(self.graph_connectivity_score)
    }

    fn combined_penalty(&self) -> u64 {
        self.set_size_penalty
            .saturating_add(self.import_cost_penalty)
            .saturating_add(self.axiom_cost_penalty)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachinePremiseSetFeature {
    pub kind: MachinePremiseSetFeatureKind,
    pub feature_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseSetFeatureKind {
    TargetHead,
    RecursiveOccurrence,
    EqualityLhsHead,
    EqualityRhsHead,
    PropositionalConnective,
    ReferencedInductive,
    NormalizedExpression,
}

impl MachinePremiseSetFeatureKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TargetHead => "target_head",
            Self::RecursiveOccurrence => "recursive_occurrence",
            Self::EqualityLhsHead => "equality_lhs_head",
            Self::EqualityRhsHead => "equality_rhs_head",
            Self::PropositionalConnective => "propositional_connective",
            Self::ReferencedInductive => "referenced_inductive",
            Self::NormalizedExpression => "normalized_expression",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "target_head" => Some(Self::TargetHead),
            "recursive_occurrence" => Some(Self::RecursiveOccurrence),
            "equality_lhs_head" => Some(Self::EqualityLhsHead),
            "equality_rhs_head" => Some(Self::EqualityRhsHead),
            "propositional_connective" => Some(Self::PropositionalConnective),
            "referenced_inductive" => Some(Self::ReferencedInductive),
            "normalized_expression" => Some(Self::NormalizedExpression),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseModeMetadata {
    pub mode: MachineTheoremMode,
    pub status: MachinePremiseModeStatus,
    pub reason: MachinePremiseModeReason,
    pub suggested_candidate_count: u64,
    pub lexical_score: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseModeStatus {
    Supported,
    Unavailable,
}

impl MachinePremiseModeStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Supported => "supported",
            Self::Unavailable => "unavailable",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "supported" => Some(Self::Supported),
            "unavailable" => Some(Self::Unavailable),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachinePremiseModeReason {
    EntryModeMatched,
    EntryModeNotApplicable,
    TypeAwareFeasible,
    TypeAwareInfeasible,
    TypeAwareNotEvaluated,
    LexicalSignal,
    LexicalNoSignal,
    VerifiedInductiveMetadata,
    NoVerifiedInductiveMetadata,
    SidecarUnavailable,
    PremiseSetDeferred,
    PremiseSetSelected,
    PremiseSetNotSelected,
}

impl MachinePremiseModeReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EntryModeMatched => "entry_mode_matched",
            Self::EntryModeNotApplicable => "entry_mode_not_applicable",
            Self::TypeAwareFeasible => "type_aware_feasible",
            Self::TypeAwareInfeasible => "type_aware_infeasible",
            Self::TypeAwareNotEvaluated => "type_aware_not_evaluated",
            Self::LexicalSignal => "lexical_signal",
            Self::LexicalNoSignal => "lexical_no_signal",
            Self::VerifiedInductiveMetadata => "verified_inductive_metadata",
            Self::NoVerifiedInductiveMetadata => "no_verified_inductive_metadata",
            Self::SidecarUnavailable => "sidecar_unavailable",
            Self::PremiseSetDeferred => "premise_set_deferred",
            Self::PremiseSetSelected => "premise_set_selected",
            Self::PremiseSetNotSelected => "premise_set_not_selected",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "entry_mode_matched" => Some(Self::EntryModeMatched),
            "entry_mode_not_applicable" => Some(Self::EntryModeNotApplicable),
            "type_aware_feasible" => Some(Self::TypeAwareFeasible),
            "type_aware_infeasible" => Some(Self::TypeAwareInfeasible),
            "type_aware_not_evaluated" => Some(Self::TypeAwareNotEvaluated),
            "lexical_signal" => Some(Self::LexicalSignal),
            "lexical_no_signal" => Some(Self::LexicalNoSignal),
            "verified_inductive_metadata" => Some(Self::VerifiedInductiveMetadata),
            "no_verified_inductive_metadata" => Some(Self::NoVerifiedInductiveMetadata),
            "sidecar_unavailable" => Some(Self::SidecarUnavailable),
            "premise_set_deferred" => Some(Self::PremiseSetDeferred),
            "premise_set_selected" => Some(Self::PremiseSetSelected),
            "premise_set_not_selected" => Some(Self::PremiseSetNotSelected),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTypeAwarePremiseMetadata {
    pub status: MachineTypeAwarePremiseStatus,
    pub selected_mode: Option<MachineTheoremMode>,
    pub universe_compatible: bool,
    pub head_compatible: bool,
    pub result_fits_goal: bool,
    pub pi_binder_count: u64,
    pub unresolved_obligation_type_hashes: Vec<Hash>,
    pub local_context_match_type_hashes: Vec<Hash>,
    pub generated_argument_sources: Vec<MachineTypeAwareArgumentSource>,
    pub estimated_new_goals: u64,
    pub premise_size: u64,
    pub goal_size: u64,
}

impl MachineTypeAwarePremiseMetadata {
    pub fn not_evaluated() -> Self {
        Self {
            status: MachineTypeAwarePremiseStatus::NotEvaluated,
            selected_mode: None,
            universe_compatible: false,
            head_compatible: false,
            result_fits_goal: false,
            pi_binder_count: 0,
            unresolved_obligation_type_hashes: Vec::new(),
            local_context_match_type_hashes: Vec::new(),
            generated_argument_sources: Vec::new(),
            estimated_new_goals: 0,
            premise_size: 0,
            goal_size: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineTypeAwarePremiseStatus {
    NotEvaluated,
    Feasible,
    Infeasible,
}

impl MachineTypeAwarePremiseStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotEvaluated => "not_evaluated",
            Self::Feasible => "feasible",
            Self::Infeasible => "infeasible",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "not_evaluated" => Some(Self::NotEvaluated),
            "feasible" => Some(Self::Feasible),
            "infeasible" => Some(Self::Infeasible),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineTypeAwareArgumentSource {
    LocalContext,
    InferFromTarget,
}

impl MachineTypeAwareArgumentSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LocalContext => "local_context",
            Self::InferFromTarget => "infer_from_target",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "local_context" => Some(Self::LocalContext),
            "infer_from_target" => Some(Self::InferFromTarget),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineVerifiedPremiseIndexEntry {
    pub identity: MachineVerifiedPremiseIdentity,
    pub statement_core_hash: Hash,
    pub structural_features: MachinePremiseStructuralFeatures,
    pub modes: Vec<MachineTheoremMode>,
    pub source: MachinePremiseIndexSource,
    pub ranking_metadata: MachinePremiseRankingMetadata,
}

impl MachineVerifiedPremiseIndexEntry {
    pub fn new(
        identity: MachineVerifiedPremiseIdentity,
        statement_core_hash: Hash,
        structural_features: MachinePremiseStructuralFeatures,
        mut modes: Vec<MachineTheoremMode>,
        source: MachinePremiseIndexSource,
        ranking_metadata: MachinePremiseRankingMetadata,
    ) -> Result<Self, MachinePremiseIndexError> {
        if identity.statement_core_hash != statement_core_hash {
            return Err(premise_index_error(
                &JsonPath::root().field("statement_core_hash"),
                MachinePremiseIndexErrorReason::StatementCoreHashMismatch,
            ));
        }
        if structural_features.feature_hash
            != machine_premise_structural_features_computed_hash(&structural_features)
        {
            return Err(premise_index_error(
                &JsonPath::root()
                    .field("structural_features")
                    .field("feature_hash"),
                MachinePremiseIndexErrorReason::StructuralFeatureHashMismatch,
            ));
        }
        if structural_features
            .normalized_expression_fingerprints
            .first()
            != Some(&statement_core_hash)
        {
            return Err(premise_index_error(
                &JsonPath::root()
                    .field("structural_features")
                    .field("normalized_expression_fingerprints"),
                MachinePremiseIndexErrorReason::StatementCoreHashMismatch,
            ));
        }
        if modes.is_empty() {
            return Err(premise_index_error(
                &JsonPath::root().field("modes"),
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::MissingField { field: "modes" },
                ),
            ));
        }
        modes.sort();
        modes.dedup();
        Ok(Self {
            identity,
            statement_core_hash,
            structural_features,
            modes,
            source,
            ranking_metadata,
        })
    }

    pub fn stable_canonical_bytes(&self) -> Vec<u8> {
        verified_premise_index_entry_stable_canonical_bytes(self)
    }

    pub fn stable_entry_hash(&self) -> Hash {
        sha256(&self.stable_canonical_bytes())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineVerifiedPremiseIndex {
    pub entries: Vec<MachineVerifiedPremiseIndexEntry>,
    pub fingerprint: Hash,
}

impl MachineVerifiedPremiseIndex {
    pub fn new(mut entries: Vec<MachineVerifiedPremiseIndexEntry>) -> Self {
        entries.sort_by_key(MachineVerifiedPremiseIndexEntry::stable_canonical_bytes);
        let fingerprint = verified_premise_index_fingerprint(&entries);
        Self {
            entries,
            fingerprint,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineUntrustedPremiseCandidate {
    pub candidate_hash: Hash,
    pub source_label: String,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachinePremiseIndexEntry {
    Verified(Box<MachineVerifiedPremiseIndexEntry>),
    UntrustedCandidate(MachineUntrustedPremiseCandidate),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseIndexError {
    pub path: String,
    pub reason: MachinePremiseIndexErrorReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachinePremiseIndexErrorReason {
    Request(MachineApiErrorKind, MachineApiRequestErrorReason),
    InvalidSchema {
        expected: &'static str,
        actual: String,
    },
    InvalidName {
        field: &'static str,
    },
    InvalidHash {
        field: &'static str,
    },
    InvalidEnum {
        field: &'static str,
        value: String,
    },
    IdentityMismatch {
        field: &'static str,
    },
    AxiomSummaryHashMismatch,
    NonCanonicalAxiomRefs {
        field: &'static str,
    },
    StatementCoreHashMismatch,
    StructuralFeatureHashMismatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSuggestedCandidate {
    pub status: MachineSuggestedCandidateStatus,
    pub candidate_hash: Hash,
    pub candidate: MachineTacticCandidate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineSuggestedCandidateStatus {
    Validated,
}

impl MachineSuggestedCandidateStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Validated => "validated",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineTheoremMode {
    Exact,
    Apply,
    Rw,
    Simp,
    ConstructorSupport,
    InductionSupport,
    TypeAware,
    Lexical,
    GraphAware,
    Embedding,
    ProofAnalogy,
    PremiseSet,
}

impl MachineTheoremMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Apply => "apply",
            Self::Rw => "rw",
            Self::Simp => "simp",
            Self::ConstructorSupport => "constructor_support",
            Self::InductionSupport => "induction_support",
            Self::TypeAware => "type_aware",
            Self::Lexical => "lexical",
            Self::GraphAware => "graph_aware",
            Self::Embedding => "embedding",
            Self::ProofAnalogy => "proof_analogy",
            Self::PremiseSet => "premise_set",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "exact" => Some(Self::Exact),
            "apply" => Some(Self::Apply),
            "rw" => Some(Self::Rw),
            "simp" => Some(Self::Simp),
            "constructor_support" => Some(Self::ConstructorSupport),
            "induction_support" => Some(Self::InductionSupport),
            "type_aware" => Some(Self::TypeAware),
            "lexical" => Some(Self::Lexical),
            "graph_aware" => Some(Self::GraphAware),
            "embedding" => Some(Self::Embedding),
            "proof_analogy" => Some(Self::ProofAnalogy),
            "premise_set" => Some(Self::PremiseSet),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremSearchRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: npa_tactic::GoalId,
    pub modes: Vec<MachineTheoremMode>,
    pub limit: u32,
    pub filters: MachineTheoremFilters,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSearchRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: npa_tactic::GoalId,
    pub modes: Vec<MachineTheoremMode>,
    pub limit: u32,
    pub filters: MachineTheoremFilters,
    pub expected_theorem_index_fingerprint: Option<Hash>,
    pub graph_snapshot_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremFilters {
    pub exclude_axioms: bool,
    pub allowed_modules: MachineAllowedModulesFilter,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineAllowedModulesFilter {
    AllDirect,
    Explicit(Vec<Name>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineAllowedModulesValidationError {
    pub module: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTheoremSearchError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachineTheoremSearchResponse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePremiseSearchError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachinePremiseSearchResponse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportProposalError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachineImportProposalResponse,
}

#[derive(Clone, Debug)]
struct TheoremIndex {
    entries: Vec<TheoremIndexEntry>,
    fingerprint: Hash,
}

#[derive(Clone, Debug)]
struct TheoremIndexEntry {
    global_ref: MachineTheoremGlobalRef,
    export_kind: ExportKind,
    #[allow(dead_code)]
    certificate_hash: Hash,
    universe_params: Vec<String>,
    statement_type: Expr,
    statement_display_scope: MachineDisplayRenderScope,
    statement_core_hash: Hash,
    head: Option<MachineGlobalRefView>,
    #[allow(dead_code)]
    structural_features: MachinePremiseStructuralFeatures,
    axioms_used: Vec<MachineAxiomRefWire>,
    modes: Vec<MachineTheoremMode>,
    canonical_bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
pub(crate) struct MachineTheoremSelection {
    pub query_fingerprint: Hash,
    pub theorem_index_fingerprint: Hash,
    pub results: Vec<MachineTheoremSearchResult>,
}

#[derive(Clone, Debug)]
pub(crate) struct MachinePremiseSelection {
    pub query_fingerprint: Hash,
    pub query_profile_hash: Hash,
    pub theorem_index_fingerprint: Hash,
    pub graph_snapshot_hash: Option<Hash>,
    pub visible_imports_fingerprint: Hash,
    pub retrieval_cache_key: MachineRetrievalCacheKey,
    pub selected_modes: Vec<MachineTheoremMode>,
    pub results: Vec<MachinePremiseSearchResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MachinePremiseSetRetrievalPlan {
    selected_sort_keys: BTreeSet<Vec<u8>>,
    selected_sort_order: Vec<Vec<u8>>,
    metadata: MachinePremiseSetMetadata,
}

#[derive(Clone, Debug)]
struct MachinePremiseSetCandidate<'a> {
    entry: &'a TheoremIndexEntry,
    premise: MachinePremiseStructuralRef,
    sort_key: Vec<u8>,
    features: BTreeSet<MachinePremiseSetFeature>,
    import_cost: u64,
    axiom_cost: u64,
}

#[derive(Clone, Debug)]
struct MachinePremiseSetCandidateScore {
    added_features: Vec<MachinePremiseSetFeature>,
    objective: MachinePremiseSetObjective,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MachinePremiseSearchSelectionError {
    Build(TheoremSearchBuildError),
    TheoremIndexFingerprintMismatch { expected: Hash, actual: Hash },
}

impl From<TheoremSearchBuildError> for MachinePremiseSearchSelectionError {
    fn from(value: TheoremSearchBuildError) -> Self {
        Self::Build(value)
    }
}

pub fn search_machine_theorems_for_goal(
    source: &str,
    session: &MachineProofSession,
) -> Result<MachineTheoremSearchResponse, Box<MachineTheoremSearchError>> {
    search_machine_theorems_for_goal_in_sessions(source, std::iter::once(session))
}

pub fn search_machine_theorems_for_goal_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
) -> Result<MachineTheoremSearchResponse, Box<MachineTheoremSearchError>> {
    let request = parse_machine_theorem_search_request(source).map_err(search_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(search_plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
        ));
    };

    search_machine_theorems_for_goal_parsed(session, request)
}

pub fn search_machine_premises_for_goal(
    source: &str,
    session: &MachineProofSession,
) -> Result<MachinePremiseSearchResponse, Box<MachinePremiseSearchError>> {
    search_machine_premises_for_goal_in_sessions(source, std::iter::once(session))
}

pub fn search_machine_premises_for_goal_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
) -> Result<MachinePremiseSearchResponse, Box<MachinePremiseSearchError>> {
    let request =
        parse_machine_premise_search_request(source).map_err(premise_search_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(premise_search_plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
        ));
    };

    search_machine_premises_for_goal_parsed(session, request)
}

pub fn propose_machine_imports_for_goal(
    source: &str,
    session: &MachineProofSession,
) -> Result<MachineImportProposalResponse, Box<MachineImportProposalError>> {
    propose_machine_imports_for_goal_in_sessions(source, std::iter::once(session))
}

pub fn propose_machine_imports_for_goal_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
) -> Result<MachineImportProposalResponse, Box<MachineImportProposalError>> {
    let request =
        parse_machine_import_proposal_request(source).map_err(import_proposal_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(import_proposal_plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
        ));
    };

    propose_machine_imports_for_goal_parsed(session, request)
}

pub fn parse_machine_theorem_search_request(
    source: &str,
) -> Result<MachineTheoremSearchRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTheoremQuery)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        crate::MachineApiEndpoint::SearchForGoal,
        &JsonPath::root(),
    )?;

    let session_id = SessionId::parse(required_string(&envelope, "session_id"))
        .expect("endpoint validation checked session_id grammar");
    let snapshot_id = SnapshotId::parse(required_string(&envelope, "snapshot_id"))
        .expect("endpoint validation checked snapshot_id grammar");
    let state_fingerprint = HashString::parse(required_string(&envelope, "state_fingerprint"))
        .expect("endpoint validation checked state_fingerprint grammar")
        .digest();
    let goal_id = parse_goal_id_wire(required_string(&envelope, "goal_id"))
        .expect("endpoint validation checked goal_id grammar");
    let modes = parse_theorem_modes(
        required_field(&envelope, "modes"),
        &JsonPath::root().field("modes"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;
    let limit = parse_theorem_limit(
        required_field(&envelope, "limit"),
        &JsonPath::root().field("limit"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;
    let filters = parse_theorem_filters(
        required_field(&envelope, "filters"),
        &JsonPath::root().field("filters"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;

    Ok(MachineTheoremSearchRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        modes,
        limit,
        filters,
    })
}

pub fn parse_machine_premise_search_request(
    source: &str,
) -> Result<MachinePremiseSearchRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTheoremQuery)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        crate::MachineApiEndpoint::PremisesSearch,
        &JsonPath::root(),
    )?;

    let session_id = SessionId::parse(required_string(&envelope, "session_id"))
        .expect("endpoint validation checked session_id grammar");
    let snapshot_id = SnapshotId::parse(required_string(&envelope, "snapshot_id"))
        .expect("endpoint validation checked snapshot_id grammar");
    let state_fingerprint = HashString::parse(required_string(&envelope, "state_fingerprint"))
        .expect("endpoint validation checked state_fingerprint grammar")
        .digest();
    let goal_id = parse_goal_id_wire(required_string(&envelope, "goal_id"))
        .expect("endpoint validation checked goal_id grammar");
    let modes = parse_theorem_modes(
        required_field(&envelope, "modes"),
        &JsonPath::root().field("modes"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;
    let limit = parse_theorem_limit(
        required_field(&envelope, "limit"),
        &JsonPath::root().field("limit"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;
    let filters = parse_theorem_filters(
        required_field(&envelope, "filters"),
        &JsonPath::root().field("filters"),
        MachineApiErrorKind::InvalidTheoremQuery,
    )?;
    let expected_theorem_index_fingerprint =
        optional_hash(&envelope, "expected_theorem_index_fingerprint");
    let graph_snapshot_hash = optional_hash(&envelope, "graph_snapshot_hash");

    Ok(MachinePremiseSearchRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        modes,
        limit,
        filters,
        expected_theorem_index_fingerprint,
        graph_snapshot_hash,
    })
}

pub fn parse_machine_import_proposal_request(
    source: &str,
) -> Result<MachineImportProposalRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTheoremQuery)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        crate::MachineApiEndpoint::ImportProposals,
        &JsonPath::root(),
    )?;

    let session_id = SessionId::parse(required_string(&envelope, "session_id"))
        .expect("endpoint validation checked session_id grammar");
    let snapshot_id = SnapshotId::parse(required_string(&envelope, "snapshot_id"))
        .expect("endpoint validation checked snapshot_id grammar");
    let state_fingerprint = HashString::parse(required_string(&envelope, "state_fingerprint"))
        .expect("endpoint validation checked state_fingerprint grammar")
        .digest();
    let goal_id = parse_goal_id_wire(required_string(&envelope, "goal_id"))
        .expect("endpoint validation checked goal_id grammar");
    let proposed_for_tasks = parse_import_proposal_task_refs(
        required_field(&envelope, "proposed_for_tasks"),
        &JsonPath::root().field("proposed_for_tasks"),
    )?;
    let candidates = parse_import_proposal_candidates(
        required_field(&envelope, "candidates"),
        &JsonPath::root().field("candidates"),
    )?;
    let expected_visible_imports_fingerprint =
        optional_hash(&envelope, "expected_visible_imports_fingerprint");

    Ok(MachineImportProposalRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        proposed_for_tasks,
        candidates,
        expected_visible_imports_fingerprint,
    })
}

fn search_machine_theorems_for_goal_parsed(
    session: &MachineProofSession,
    mut request: MachineTheoremSearchRequest,
) -> Result<MachineTheoremSearchResponse, Box<MachineTheoremSearchError>> {
    canonicalize_allowed_modules_for_session(session, &mut request.filters).map_err(|error| {
        search_plain_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            MachineApiDiagnosticPhase::RequestValidation,
            format!(
                "allowed module {} is not a direct import of the session",
                error.module.as_dotted()
            ),
        )
    })?;

    if session.snapshots.session_id() != &session.session_id {
        return Err(search_plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SnapshotLookup,
            "session snapshot store belongs to a different session",
        ));
    }

    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let entry = session
        .snapshots
        .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
        .map_err(search_snapshot_lookup_error)?;
    let goal = entry
        .materialized_view_payload
        .goals
        .iter()
        .find(|goal| goal.goal_id == request.goal_id)
        .ok_or_else(|| {
            search_goal_error(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                request.goal_id,
                format!("goal {} is not open", format_goal_id_wire(request.goal_id)),
            )
        })?;
    let input_state = &entry.executable_state_payload;

    let selection = select_machine_theorem_results_for_goal(
        session,
        input_state,
        goal,
        &request.modes,
        &request.filters,
        request.limit,
        true,
    )
    .map_err(search_theorem_index_error)?;

    Ok(MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
        status: MachineApiResponseStatus::Ok,
        endpoint_fields: MachineTheoremSearchOkFields {
            query_fingerprint: selection.query_fingerprint,
            theorem_index_fingerprint: selection.theorem_index_fingerprint,
            search_profile_version: SEARCH_PROFILE_VERSION,
            suggestion_profile_version: SUGGESTION_PROFILE_VERSION,
            results: selection.results,
        },
    }))
}

fn propose_machine_imports_for_goal_parsed(
    session: &MachineProofSession,
    request: MachineImportProposalRequest,
) -> Result<MachineImportProposalResponse, Box<MachineImportProposalError>> {
    if session.snapshots.session_id() != &session.session_id {
        return Err(import_proposal_plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SnapshotLookup,
            "session snapshot store belongs to a different session",
        ));
    }

    let visible_imports_fingerprint = visible_imports_fingerprint(session);
    if let Some(expected) = request.expected_visible_imports_fingerprint {
        if expected != visible_imports_fingerprint {
            return Err(import_proposal_plain_error(
                MachineApiErrorKind::InvalidTheoremQuery,
                MachineApiDiagnosticPhase::RequestValidation,
                format!(
                    "visible imports fingerprint mismatch: expected {}, actual {}",
                    format_hash_string(&expected),
                    format_hash_string(&visible_imports_fingerprint)
                ),
            ));
        }
    }

    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let entry = session
        .snapshots
        .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
        .map_err(import_proposal_snapshot_lookup_error)?;
    let goal = entry
        .materialized_view_payload
        .goals
        .iter()
        .find(|goal| goal.goal_id == request.goal_id)
        .ok_or_else(|| {
            import_proposal_goal_error(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                request.goal_id,
                format!("goal {} is not open", format_goal_id_wire(request.goal_id)),
            )
        })?;

    let mut proposals = Vec::new();
    let mut rejected_candidates = Vec::new();
    for candidate in &request.candidates {
        match import_proposal_for_candidate(
            session,
            candidate,
            &request.proposed_for_tasks,
            request.snapshot_id,
            request.state_fingerprint,
            visible_imports_fingerprint,
        ) {
            Ok(proposal) => proposals.push(proposal),
            Err(reason) => rejected_candidates.push(MachineImportProposalRejectedCandidate {
                rejection_hash: import_proposal_rejection_hash(candidate, reason),
                source: candidate.source,
                identity: candidate.identity.clone(),
                reason,
            }),
        }
    }
    proposals.sort_by_key(machine_import_proposal_canonical_bytes);
    rejected_candidates.sort_by_key(machine_import_proposal_rejection_canonical_bytes);

    let query_fingerprint = import_proposal_query_fingerprint(
        session.protocol_version,
        request.state_fingerprint,
        request.goal_id,
        goal.goal_fingerprint,
        visible_imports_fingerprint,
        &request.proposed_for_tasks,
        &request.candidates,
    );

    Ok(MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
        status: MachineApiResponseStatus::Ok,
        endpoint_fields: MachineImportProposalOkFields {
            query_fingerprint,
            visible_imports_fingerprint,
            proposed_for_tasks: request.proposed_for_tasks,
            proposals,
            rejected_candidates,
        },
    }))
}

fn search_machine_premises_for_goal_parsed(
    session: &MachineProofSession,
    mut request: MachinePremiseSearchRequest,
) -> Result<MachinePremiseSearchResponse, Box<MachinePremiseSearchError>> {
    canonicalize_allowed_modules_for_session(session, &mut request.filters).map_err(|error| {
        premise_search_plain_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            MachineApiDiagnosticPhase::RequestValidation,
            format!(
                "allowed module {} is not a direct import of the session",
                error.module.as_dotted()
            ),
        )
    })?;

    if session.snapshots.session_id() != &session.session_id {
        return Err(premise_search_plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SnapshotLookup,
            "session snapshot store belongs to a different session",
        ));
    }

    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let entry = session
        .snapshots
        .lookup_checked(&context, request.snapshot_id, request.state_fingerprint)
        .map_err(premise_search_snapshot_lookup_error)?;
    let goal = entry
        .materialized_view_payload
        .goals
        .iter()
        .find(|goal| goal.goal_id == request.goal_id)
        .ok_or_else(|| {
            premise_search_goal_error(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                request.goal_id,
                format!("goal {} is not open", format_goal_id_wire(request.goal_id)),
            )
        })?;
    let input_state = &entry.executable_state_payload;

    let selection = select_machine_premise_results_for_goal(
        session,
        input_state,
        goal,
        &request.modes,
        &request.filters,
        request.limit,
        request.expected_theorem_index_fingerprint,
        request.graph_snapshot_hash,
    )
    .map_err(premise_search_selection_error)?;

    Ok(MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
        status: MachineApiResponseStatus::Ok,
        endpoint_fields: MachinePremiseSearchOkFields {
            query_fingerprint: selection.query_fingerprint,
            query_profile_hash: selection.query_profile_hash,
            query_profile_version: PREMISE_SEARCH_QUERY_PROFILE_VERSION,
            theorem_index_fingerprint: selection.theorem_index_fingerprint,
            graph_snapshot_hash: selection.graph_snapshot_hash,
            visible_imports_fingerprint: selection.visible_imports_fingerprint,
            retrieval_cache_key: selection.retrieval_cache_key,
            selected_modes: selection.selected_modes,
            filters: request.filters,
            limit: request.limit,
            results: selection.results,
        },
    }))
}

pub(crate) fn select_machine_theorem_results_for_goal(
    session: &MachineProofSession,
    input_state: &npa_tactic::MachineProofState,
    goal: &MachineGoalView,
    modes: &[MachineTheoremMode],
    filters: &MachineTheoremFilters,
    limit: u32,
    include_suggested_candidates: bool,
) -> Result<MachineTheoremSelection, TheoremSearchBuildError> {
    let index = build_theorem_index(session, input_state)?;
    let query_fingerprint = theorem_query_fingerprint(QueryFingerprintInput {
        protocol_version: session.protocol_version,
        state_fingerprint: input_state.fingerprint,
        goal_id: goal.goal_id,
        goal_fingerprint: goal.goal_fingerprint,
        theorem_index_fingerprint: index.fingerprint,
        modes,
        filters,
        limit,
    });

    let mut eligible = index
        .entries
        .iter()
        .filter(|entry| theorem_entry_matches_query(entry, modes, filters))
        .collect::<Vec<_>>();
    eligible.sort_by_key(|entry| theorem_entry_sort_key(entry));
    eligible.truncate(limit as usize);

    let mut results = Vec::with_capacity(eligible.len());
    for (index, entry) in eligible.into_iter().enumerate() {
        let statement = render_statement(session, entry)?;
        let suggested_candidates = if include_suggested_candidates {
            suggested_candidates_for_entry(entry, modes, input_state, goal.goal_id)?
        } else {
            Vec::new()
        };
        results.push(MachineTheoremSearchResult {
            premise_id: format!("prem_{index}"),
            global_ref: entry.global_ref.clone(),
            universe_params: entry.universe_params.clone(),
            statement,
            modes: entry.modes.clone(),
            suggested_candidates,
            score: 0,
            axioms_used: entry.axioms_used.clone(),
        });
    }

    Ok(MachineTheoremSelection {
        query_fingerprint,
        theorem_index_fingerprint: index.fingerprint,
        results,
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn select_machine_premise_results_for_goal(
    session: &MachineProofSession,
    input_state: &npa_tactic::MachineProofState,
    goal: &MachineGoalView,
    modes: &[MachineTheoremMode],
    filters: &MachineTheoremFilters,
    limit: u32,
    expected_theorem_index_fingerprint: Option<Hash>,
    graph_snapshot_hash: Option<Hash>,
) -> Result<MachinePremiseSelection, MachinePremiseSearchSelectionError> {
    let theorem_index = build_theorem_index(session, input_state)?;
    let verified_entries = theorem_index
        .entries
        .iter()
        .map(verified_premise_entry_from_theorem_index_entry)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| TheoremSearchBuildError::PremiseIndexProjection)?;
    let verified_index = MachineVerifiedPremiseIndex::new(verified_entries);
    let theorem_index_fingerprint = verified_index.fingerprint;
    if let Some(expected) = expected_theorem_index_fingerprint {
        if expected != theorem_index_fingerprint {
            return Err(
                MachinePremiseSearchSelectionError::TheoremIndexFingerprintMismatch {
                    expected,
                    actual: theorem_index_fingerprint,
                },
            );
        }
    }

    let query_profile_hash =
        premise_search_query_profile_hash(PREMISE_SEARCH_QUERY_PROFILE_VERSION);
    let visible_imports_fingerprint = visible_imports_fingerprint(session);
    let local_context_hash =
        retrieval_local_context_hash(goal.context_hash, goal.local_name_map_hash);
    let query_fingerprint = premise_query_fingerprint(PremiseQueryFingerprintInput {
        protocol_version: session.protocol_version,
        state_fingerprint: input_state.fingerprint,
        goal_id: goal.goal_id,
        goal_fingerprint: goal.goal_fingerprint,
        goal_context_hash: goal.context_hash,
        local_name_map_hash: goal.local_name_map_hash,
        visible_imports_fingerprint,
        theorem_index_fingerprint,
        query_profile_hash,
        graph_snapshot_hash,
        modes,
        filters,
        limit,
    });
    let retrieval_cache_key = machine_retrieval_cache_key(MachineRetrievalCacheKeyInput {
        environment_hash: session.session_root_hash,
        goal_fingerprint: goal.goal_fingerprint,
        local_context_hash,
        query_fingerprint,
        query_profile_hash,
        theorem_index_fingerprint,
        graph_snapshot_hash,
        visible_imports_fingerprint,
    });

    let premise_set_plan = if modes.contains(&MachineTheoremMode::PremiseSet) {
        Some(select_machine_premise_set_for_goal(
            session,
            input_state,
            goal.goal_id,
            &theorem_index.entries,
            filters,
            limit,
            graph_snapshot_hash,
        )?)
    } else {
        None
    };

    let verified_by_sort_key = verified_index
        .entries
        .into_iter()
        .map(|entry| {
            let sort_key = verified_premise_entry_sort_key(&entry);
            (sort_key, entry)
        })
        .collect::<BTreeMap<_, _>>();
    let ordinary_eligible = theorem_index
        .entries
        .iter()
        .filter(|entry| {
            premise_entry_matches_query(entry, modes, filters)
                && !premise_set_plan.as_ref().is_some_and(|plan| {
                    plan.selected_sort_keys
                        .contains(&theorem_entry_sort_key(entry))
                })
        })
        .collect::<Vec<_>>();
    let mut ordinary_ranked = ordinary_eligible
        .into_iter()
        .map(|entry| {
            let selected_modes = selected_retrieval_modes_for_entry(entry, modes, false);
            let ranking_metadata = type_aware_ranking_metadata_for_entry(
                &MachinePremiseRankingMetadata::score_only(0),
                entry,
                PremiseRankingContext {
                    state: input_state,
                    goal_id: goal.goal_id,
                    requested_modes: modes,
                    selected_modes: &selected_modes,
                    suggested_candidates: &[],
                    allowed_axioms: Some(&session.options.allow_axioms),
                    graph_snapshot_hash,
                    source: MachinePremiseIndexSource::DirectImport,
                    import_cost: 0,
                },
            );
            (entry, ranking_metadata.score, theorem_entry_sort_key(entry))
        })
        .collect::<Vec<_>>();
    ordinary_ranked.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.2.cmp(&right.2)));

    let entries_by_sort_key = theorem_index
        .entries
        .iter()
        .map(|entry| (theorem_entry_sort_key(entry), entry))
        .collect::<BTreeMap<_, _>>();
    let mut eligible = Vec::new();
    if let Some(plan) = &premise_set_plan {
        for key in &plan.selected_sort_order {
            if let Some(entry) = entries_by_sort_key.get(key) {
                eligible.push(*entry);
            }
        }
    }
    for (entry, _, _) in ordinary_ranked {
        if eligible.len() >= limit as usize {
            break;
        }
        eligible.push(entry);
    }

    let mut results = Vec::with_capacity(eligible.len());
    for (index, theorem_entry) in eligible.into_iter().enumerate() {
        let sort_key = theorem_entry_sort_key(theorem_entry);
        let verified_entry = verified_by_sort_key
            .get(&sort_key)
            .ok_or(TheoremSearchBuildError::PremiseIndexProjection)?;
        let premise_set_selected = premise_set_plan
            .as_ref()
            .is_some_and(|plan| plan.selected_sort_keys.contains(&sort_key));
        let selected_modes =
            selected_retrieval_modes_for_entry(theorem_entry, modes, premise_set_selected);
        let suggested_candidates =
            suggested_candidates_for_entry(theorem_entry, modes, input_state, goal.goal_id)?;
        let suggested_candidate_count =
            u32::try_from(suggested_candidates.len()).unwrap_or(u32::MAX);
        let mut ranking_metadata = type_aware_ranking_metadata_for_entry(
            &verified_entry.ranking_metadata,
            theorem_entry,
            PremiseRankingContext {
                state: input_state,
                goal_id: goal.goal_id,
                requested_modes: modes,
                selected_modes: &selected_modes,
                suggested_candidates: &suggested_candidates,
                allowed_axioms: Some(&session.options.allow_axioms),
                graph_snapshot_hash,
                source: verified_entry.source,
                import_cost: 0,
            },
        );
        if premise_set_selected {
            ranking_metadata.premise_set =
                premise_set_plan.as_ref().map(|plan| plan.metadata.clone());
        }
        results.push(MachinePremiseSearchResult {
            premise_id: format!("prem_{index}"),
            verified_identity: verified_entry.identity.clone(),
            statement_core_hash: verified_entry.statement_core_hash,
            structural_features: verified_entry.structural_features.clone(),
            selected_modes,
            ranking_metadata,
            candidate_provenance: MachinePremiseCandidateProvenance {
                premise_source: verified_entry.source,
                suggestion_profile_version: SUGGESTION_PROFILE_VERSION,
                suggested_candidate_count,
            },
            untrusted_sidecar: MachinePremiseUntrustedSidecar {
                suggested_candidates,
            },
        });
    }

    Ok(MachinePremiseSelection {
        query_fingerprint,
        query_profile_hash,
        theorem_index_fingerprint,
        graph_snapshot_hash,
        visible_imports_fingerprint,
        retrieval_cache_key,
        selected_modes: modes.to_vec(),
        results,
    })
}

fn import_proposal_for_candidate(
    session: &MachineProofSession,
    candidate: &MachineImportProposalCandidate,
    proposed_for_tasks: &[String],
    current_snapshot_id: SnapshotId,
    current_state_fingerprint: Hash,
    visible_imports_fingerprint: Hash,
) -> Result<MachineImportProposal, MachineImportProposalRejectionReason> {
    if candidate.identity.module == session.root.module {
        return Err(MachineImportProposalRejectionReason::CyclicImportProposal);
    }

    if direct_import_key_matches_identity(session, &candidate.identity) {
        return Err(MachineImportProposalRejectionReason::AlreadyDirectImport);
    }

    let reason = match candidate.source {
        MachineImportProposalCandidateSource::VerifiedClosure => {
            let entry = verified_closure_entry_for_identity(session, &candidate.identity)?;
            validate_verified_closure_identity(session, entry, &candidate.identity)?;
            MachineImportProposalReason::ClosureModuleNotDirect
        }
        MachineImportProposalCandidateSource::PackageTheoremIndex => {
            match verified_closure_entry_for_identity(session, &candidate.identity) {
                Ok(entry) => {
                    validate_verified_closure_identity(session, entry, &candidate.identity)?;
                    MachineImportProposalReason::ClosureModuleNotDirect
                }
                Err(MachineImportProposalRejectionReason::IncompatiblePackage) => {
                    MachineImportProposalReason::PackageCandidateNotImported
                }
                Err(other) => return Err(other),
            }
        }
    };

    if !import_proposal_axioms_allowed(session, &candidate.identity.axiom_summary) {
        return Err(MachineImportProposalRejectionReason::DisallowedAxiom);
    }

    let required_direct_import = MachineImportProposalImportIdentity::from(&candidate.identity);
    let approval = MachineImportProposalApprovalHook {
        current_session_id: session.session_id.clone(),
        current_session_root_hash: session.session_root_hash,
        required_direct_import: required_direct_import.clone(),
        current_snapshot_id,
        current_state_fingerprint,
        requires_new_snapshot: true,
        requires_certificate_regeneration: true,
    };
    let mut proposal = MachineImportProposal {
        proposal_hash: [0; 32],
        module: candidate.identity.module.clone(),
        export_hash: candidate.identity.export_hash,
        certificate_hash: candidate.identity.certificate_hash,
        proposed_for_tasks: proposed_for_tasks.to_vec(),
        new_axiom_summary: candidate.identity.axiom_summary.clone(),
        estimated_downstream_rebuild: estimated_downstream_rebuild(session),
        reason,
        candidate_source: candidate.source,
        candidate_identity: candidate.identity.clone(),
        visible_imports_fingerprint,
        approval,
    };
    proposal.proposal_hash = machine_import_proposal_hash(&proposal);
    Ok(proposal)
}

fn direct_import_key_matches_identity(
    session: &MachineProofSession,
    identity: &MachineVerifiedPremiseIdentity,
) -> bool {
    session
        .import_certificate_context
        .direct_import_keys()
        .iter()
        .any(|key| {
            key.module == identity.module
                && key.export_hash == identity.export_hash
                && key.certificate_hash == identity.certificate_hash
        })
}

fn verified_closure_entry_for_identity<'session>(
    session: &'session MachineProofSession,
    identity: &MachineVerifiedPremiseIdentity,
) -> Result<&'session VerifiedModuleContextEntry, MachineImportProposalRejectionReason> {
    let same_module = session
        .import_certificate_context
        .verified_modules()
        .iter()
        .filter(|entry| entry.key.module == identity.module)
        .collect::<Vec<_>>();
    if same_module.is_empty() {
        return Err(MachineImportProposalRejectionReason::IncompatiblePackage);
    }
    let same_export = same_module
        .iter()
        .copied()
        .filter(|entry| entry.key.export_hash == identity.export_hash)
        .collect::<Vec<_>>();
    if same_export.is_empty() {
        return Err(MachineImportProposalRejectionReason::StaleExportHash);
    }
    same_export
        .into_iter()
        .find(|entry| entry.key.certificate_hash == identity.certificate_hash)
        .ok_or(MachineImportProposalRejectionReason::StaleCertificateHash)
}

fn validate_verified_closure_identity(
    session: &MachineProofSession,
    entry: &VerifiedModuleContextEntry,
    identity: &MachineVerifiedPremiseIdentity,
) -> Result<(), MachineImportProposalRejectionReason> {
    let export = entry
        .export_block
        .iter()
        .find(|export| {
            export_name(entry, export)
                .ok()
                .is_some_and(|name| name == identity.global_ref.name)
        })
        .ok_or(MachineImportProposalRejectionReason::IdentityMismatch)?;
    if !matches!(export.kind, ExportKind::Axiom | ExportKind::Theorem) {
        return Err(MachineImportProposalRejectionReason::IdentityMismatch);
    }
    if export.decl_interface_hash != identity.decl_interface_hash
        || export.decl_interface_hash != identity.global_ref.decl_interface_hash
        || export.type_hash != identity.statement_core_hash
    {
        return Err(MachineImportProposalRejectionReason::IdentityMismatch);
    }
    let mut axioms = export
        .axiom_dependencies
        .iter()
        .map(|axiom| {
            imported_axiom_ref_to_wire(0, &session.import_certificate_context, entry, axiom)
                .map_err(|_| MachineImportProposalRejectionReason::IdentityMismatch)
        })
        .collect::<Result<Vec<_>, _>>()?;
    sort_dedup_axiom_refs(&mut axioms);
    let actual_summary = MachineVerifiedPremiseAxiomSummary::new(Vec::new(), axioms);
    if actual_summary != identity.axiom_summary {
        return Err(MachineImportProposalRejectionReason::IdentityMismatch);
    }
    Ok(())
}

fn import_proposal_axioms_allowed(
    session: &MachineProofSession,
    summary: &MachineVerifiedPremiseAxiomSummary,
) -> bool {
    let allowed = session
        .options
        .allow_axioms
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<BTreeSet<_>>();
    summary
        .direct_axioms
        .iter()
        .chain(summary.transitive_axioms.iter())
        .all(|axiom| allowed.contains(&encode_machine_axiom_ref_wire(axiom)))
}

fn estimated_downstream_rebuild(session: &MachineProofSession) -> u32 {
    let checked_current_decls =
        u32::try_from(session.checked_current_decls.decl_index_table().len())
            .unwrap_or(u32::MAX - 1);
    checked_current_decls.saturating_add(1)
}

pub fn validate_machine_import_proposal_acceptance(
    proposal: &MachineImportProposal,
    current_session: &MachineProofSession,
    rebuilt_session: &MachineProofSession,
) -> Result<MachineImportProposalAcceptance, MachineImportProposalAcceptanceError> {
    if proposal.proposal_hash != machine_import_proposal_hash(proposal)
        || !import_proposal_shape_matches_candidate(proposal)
        || proposal.approval.current_session_id != current_session.session_id
        || proposal.approval.current_session_root_hash != current_session.session_root_hash
        || proposal.visible_imports_fingerprint != visible_imports_fingerprint(current_session)
    {
        return Err(MachineImportProposalAcceptanceError::StaleProposalIdentity);
    }
    let context = MachineSnapshotMaterializationContext {
        session_id: &current_session.session_id,
        display_scope: &current_session.machine_display_render_scope,
        callable_interface_table: &current_session.machine_surface_callable_interface_table,
    };
    if current_session
        .snapshots
        .lookup_checked(
            &context,
            proposal.approval.current_snapshot_id,
            proposal.approval.current_state_fingerprint,
        )
        .is_err()
    {
        return Err(MachineImportProposalAcceptanceError::StaleProposalIdentity);
    }
    if current_session.session_root_hash == rebuilt_session.session_root_hash {
        return Err(MachineImportProposalAcceptanceError::RebuiltSnapshotRequired);
    }
    if !import_proposal_direct_import_present(
        rebuilt_session,
        &proposal.approval.required_direct_import,
    ) {
        return Err(MachineImportProposalAcceptanceError::ProposalImportNotDirect);
    }
    if !import_proposal_axioms_allowed(rebuilt_session, &proposal.new_axiom_summary) {
        return Err(MachineImportProposalAcceptanceError::DisallowedAxiom);
    }
    Ok(MachineImportProposalAcceptance {
        proposal_hash: proposal.proposal_hash,
        rebuilt_snapshot_id: rebuilt_session.initial_snapshot.snapshot_id,
        rebuilt_state_fingerprint: rebuilt_session.initial_snapshot.state_fingerprint,
        direct_import: proposal.approval.required_direct_import.clone(),
    })
}

fn import_proposal_shape_matches_candidate(proposal: &MachineImportProposal) -> bool {
    let expected_import = MachineImportProposalImportIdentity::from(&proposal.candidate_identity);
    proposal.module == proposal.candidate_identity.module
        && proposal.export_hash == proposal.candidate_identity.export_hash
        && proposal.certificate_hash == proposal.candidate_identity.certificate_hash
        && proposal.new_axiom_summary == proposal.candidate_identity.axiom_summary
        && proposal.approval.required_direct_import == expected_import
        && proposal.approval.requires_new_snapshot
        && proposal.approval.requires_certificate_regeneration
}

fn import_proposal_direct_import_present(
    session: &MachineProofSession,
    import: &MachineImportProposalImportIdentity,
) -> bool {
    session
        .import_certificate_context
        .direct_import_keys()
        .iter()
        .any(|key| {
            key.module == import.module
                && key.export_hash == import.export_hash
                && key.certificate_hash == import.certificate_hash
        })
}

fn select_machine_premise_set_for_goal(
    session: &MachineProofSession,
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    entries: &[TheoremIndexEntry],
    filters: &MachineTheoremFilters,
    max_set_size: u32,
    graph_snapshot_hash: Option<Hash>,
) -> Result<MachinePremiseSetRetrievalPlan, TheoremSearchBuildError> {
    let goal_features = premise_set_features_from_structural_features(
        &goal_premise_structural_features(session, state, goal_id)?,
    );
    let mut candidates = entries
        .iter()
        .filter(|entry| theorem_entry_passes_filters(entry, filters))
        .map(machine_premise_set_candidate)
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| left.sort_key.cmp(&right.sort_key));
    Ok(greedy_machine_premise_set_plan(
        &goal_features,
        candidates,
        max_set_size,
        graph_snapshot_hash,
    ))
}

fn greedy_machine_premise_set_plan(
    goal_features: &BTreeSet<MachinePremiseSetFeature>,
    candidates: Vec<MachinePremiseSetCandidate<'_>>,
    max_set_size: u32,
    graph_snapshot_hash: Option<Hash>,
) -> MachinePremiseSetRetrievalPlan {
    let mut unique_candidates = Vec::new();
    let mut duplicate_rejections = Vec::new();
    let mut seen_sort_keys = BTreeSet::new();
    for candidate in candidates {
        if seen_sort_keys.insert(candidate.sort_key.clone()) {
            unique_candidates.push(candidate);
        } else {
            let score = premise_set_candidate_score(
                &candidate,
                goal_features,
                &BTreeSet::new(),
                0,
                graph_snapshot_hash,
            );
            duplicate_rejections.push(MachinePremiseSetRejectedAlternative {
                premise: candidate.premise,
                reason: MachinePremiseSetRejectedReason::DuplicateCandidate,
                would_add_features: score.added_features,
                objective: score.objective,
            });
        }
    }

    let mut covered = BTreeSet::new();
    let mut selected_indices = BTreeSet::new();
    let mut selected_order_indices = Vec::new();
    let mut selected_premises = Vec::new();
    let max_set_len = max_set_size as usize;
    while selected_indices.len() < max_set_len {
        let mut best: Option<(usize, MachinePremiseSetCandidateScore)> = None;
        for (index, candidate) in unique_candidates.iter().enumerate() {
            if selected_indices.contains(&index) {
                continue;
            }
            let score = premise_set_candidate_score(
                candidate,
                goal_features,
                &covered,
                selected_indices.len(),
                graph_snapshot_hash,
            );
            if score.added_features.is_empty() || score.objective.final_score == 0 {
                continue;
            }
            let is_better = match &best {
                Some((best_index, best_score)) => premise_set_score_is_better(
                    &score,
                    &candidate.sort_key,
                    best_score,
                    &unique_candidates[*best_index].sort_key,
                ),
                None => true,
            };
            if is_better {
                best = Some((index, score));
            }
        }
        let Some((index, score)) = best else {
            break;
        };
        selected_indices.insert(index);
        selected_order_indices.push(index);
        covered.extend(score.added_features.iter().cloned());
        selected_premises.push(MachinePremiseSetSelectedPremise {
            premise: unique_candidates[index].premise.clone(),
            added_features: score.added_features,
            objective: score.objective,
        });
    }

    let selected_sort_order = selected_order_indices
        .iter()
        .map(|index| unique_candidates[*index].sort_key.clone())
        .collect::<Vec<_>>();
    let selected_sort_keys = selected_sort_order.iter().cloned().collect::<BTreeSet<_>>();

    let mut rejected_alternatives = duplicate_rejections;
    for (index, candidate) in unique_candidates.iter().enumerate() {
        if selected_indices.contains(&index) {
            continue;
        }
        let score = premise_set_candidate_score(
            candidate,
            goal_features,
            &covered,
            selected_indices.len(),
            graph_snapshot_hash,
        );
        let reason = if score.added_features.is_empty() {
            MachinePremiseSetRejectedReason::NoNewCoverage
        } else if selected_indices.len() >= max_set_len {
            MachinePremiseSetRejectedReason::MaxSetSizeReached
        } else if score.objective.final_score == 0 {
            MachinePremiseSetRejectedReason::NonPositiveObjective
        } else {
            MachinePremiseSetRejectedReason::NoNewCoverage
        };
        rejected_alternatives.push(MachinePremiseSetRejectedAlternative {
            premise: candidate.premise.clone(),
            reason,
            would_add_features: score.added_features,
            objective: score.objective,
        });
    }

    let selected_candidates = selected_order_indices
        .iter()
        .map(|index| &unique_candidates[*index])
        .collect::<Vec<_>>();
    let covered_goal_features = covered.iter().cloned().collect::<Vec<_>>();
    let missing_goal_features = goal_features
        .difference(&covered)
        .cloned()
        .collect::<Vec<_>>();
    let objective = premise_set_selected_objective(&selected_premises);
    let metadata = MachinePremiseSetMetadata {
        max_set_size,
        graph_snapshot_hash,
        selected_premises,
        covered_goal_features,
        missing_goal_features,
        rejected_alternatives,
        import_requirements: premise_set_import_requirements(&selected_candidates),
        axiom_impact: premise_set_axiom_impact(&selected_candidates, graph_snapshot_hash),
        objective,
    };

    MachinePremiseSetRetrievalPlan {
        selected_sort_keys,
        selected_sort_order,
        metadata,
    }
}

fn premise_set_score_is_better(
    candidate: &MachinePremiseSetCandidateScore,
    candidate_sort_key: &[u8],
    current: &MachinePremiseSetCandidateScore,
    current_sort_key: &[u8],
) -> bool {
    if candidate.objective.final_score != current.objective.final_score {
        return candidate.objective.final_score > current.objective.final_score;
    }
    if candidate.objective.coverage_score != current.objective.coverage_score {
        return candidate.objective.coverage_score > current.objective.coverage_score;
    }
    if candidate.objective.combined_penalty() != current.objective.combined_penalty() {
        return candidate.objective.combined_penalty() < current.objective.combined_penalty();
    }
    candidate_sort_key < current_sort_key
}

fn machine_premise_set_candidate(entry: &TheoremIndexEntry) -> MachinePremiseSetCandidate<'_> {
    MachinePremiseSetCandidate {
        entry,
        premise: MachinePremiseStructuralRef {
            module: entry.global_ref.module.clone(),
            name: entry.global_ref.name.clone(),
            export_hash: Some(entry.global_ref.export_hash),
            decl_interface_hash: entry.global_ref.decl_interface_hash,
        },
        sort_key: theorem_entry_sort_key(entry),
        features: premise_set_features_from_structural_features(&entry.structural_features),
        import_cost: 0,
        axiom_cost: theorem_entry_all_axiom_refs(entry).len() as u64,
    }
}

fn premise_set_candidate_score(
    candidate: &MachinePremiseSetCandidate<'_>,
    goal_features: &BTreeSet<MachinePremiseSetFeature>,
    covered_features: &BTreeSet<MachinePremiseSetFeature>,
    selected_count: usize,
    graph_snapshot_hash: Option<Hash>,
) -> MachinePremiseSetCandidateScore {
    let added_features = candidate
        .features
        .iter()
        .filter(|feature| goal_features.contains(*feature) && !covered_features.contains(*feature))
        .cloned()
        .collect::<Vec<_>>();
    let coverage_score = added_features.len() as u64 * 1_000;
    let historical_co_use_score = 0;
    let graph_connectivity_score = 0;
    let set_size_penalty = 10 + selected_count as u64;
    let import_cost_penalty = candidate.import_cost * 100;
    let graph_axiom_path_penalty = if graph_snapshot_hash.is_some() {
        candidate
            .axiom_cost
            .saturating_mul(GRAPH_AXIOM_PATH_PENALTY)
    } else {
        0
    };
    let axiom_cost_penalty = candidate
        .axiom_cost
        .saturating_mul(50)
        .saturating_add(graph_axiom_path_penalty);
    let reward = coverage_score
        .saturating_add(historical_co_use_score)
        .saturating_add(graph_connectivity_score);
    let penalty = set_size_penalty
        .saturating_add(import_cost_penalty)
        .saturating_add(axiom_cost_penalty);
    MachinePremiseSetCandidateScore {
        added_features,
        objective: MachinePremiseSetObjective {
            coverage_score,
            historical_co_use_score,
            graph_connectivity_score,
            set_size_penalty,
            import_cost_penalty,
            axiom_cost_penalty,
            final_score: reward.saturating_sub(penalty),
        },
    }
}

fn premise_set_selected_objective(
    premises: &[MachinePremiseSetSelectedPremise],
) -> MachinePremiseSetObjective {
    let mut objective = MachinePremiseSetObjective::default();
    for premise in premises {
        objective.coverage_score = objective
            .coverage_score
            .saturating_add(premise.objective.coverage_score);
        objective.historical_co_use_score = objective
            .historical_co_use_score
            .saturating_add(premise.objective.historical_co_use_score);
        objective.graph_connectivity_score = objective
            .graph_connectivity_score
            .saturating_add(premise.objective.graph_connectivity_score);
        objective.set_size_penalty = objective
            .set_size_penalty
            .saturating_add(premise.objective.set_size_penalty);
        objective.import_cost_penalty = objective
            .import_cost_penalty
            .saturating_add(premise.objective.import_cost_penalty);
        objective.axiom_cost_penalty = objective
            .axiom_cost_penalty
            .saturating_add(premise.objective.axiom_cost_penalty);
    }
    objective.final_score = objective
        .combined_reward()
        .saturating_sub(objective.combined_penalty());
    objective
}

fn premise_set_import_requirements(candidates: &[&MachinePremiseSetCandidate<'_>]) -> Vec<Name> {
    let mut modules = candidates
        .iter()
        .map(|candidate| candidate.entry.global_ref.module.clone())
        .collect::<Vec<_>>();
    modules.sort();
    modules.dedup();
    modules
}

fn premise_set_axiom_impact(
    candidates: &[&MachinePremiseSetCandidate<'_>],
    graph_snapshot_hash: Option<Hash>,
) -> MachinePremiseSetAxiomImpact {
    let mut direct_axioms = candidates
        .iter()
        .flat_map(|candidate| theorem_entry_direct_axiom_refs(candidate.entry))
        .collect::<Vec<_>>();
    let mut transitive_axioms = candidates
        .iter()
        .flat_map(|candidate| theorem_entry_transitive_axiom_refs(candidate.entry))
        .collect::<Vec<_>>();
    sort_dedup_axiom_refs(&mut direct_axioms);
    sort_dedup_axiom_refs(&mut transitive_axioms);
    let axiom_paths =
        premise_axiom_paths_for_refs(&direct_axioms, &transitive_axioms, graph_snapshot_hash);
    MachinePremiseSetAxiomImpact {
        direct_axiom_count: direct_axioms.len().min(u32::MAX as usize) as u32,
        transitive_axiom_count: transitive_axioms.len().min(u32::MAX as usize) as u32,
        summary_hash: verified_premise_axiom_summary_hash(&direct_axioms, &transitive_axioms),
        axiom_paths,
    }
}

fn goal_premise_structural_features(
    session: &MachineProofSession,
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
) -> Result<MachinePremiseStructuralFeatures, TheoremSearchBuildError> {
    let goal = state
        .goal(goal_id)
        .map_err(|_| TheoremSearchBuildError::PremiseIndexProjection)?;
    let eq_structural_head = resolved_eq_head(session, state)?
        .as_ref()
        .map(machine_premise_structural_ref_from_global_ref_view);
    let display_scope = &session.machine_display_render_scope;
    let target_head = expression_head_structural_ref(&goal.target, display_scope);
    let all_refs = collect_expression_structural_refs(&goal.target, display_scope);
    let referenced_inductives = all_refs
        .iter()
        .filter(|reference| {
            verified_export_kind_for_structural_ref(session, reference)
                == Some(ExportKind::Inductive)
        })
        .cloned()
        .collect::<Vec<_>>();
    let (equality_lhs_head, equality_rhs_head) =
        equality_side_heads(&goal.target, display_scope, eq_structural_head.as_ref());
    Ok(MachinePremiseStructuralFeatures::new(
        target_head,
        0,
        Vec::new(),
        expression_universe_fingerprint(&goal.target),
        Vec::new(),
        equality_lhs_head,
        equality_rhs_head,
        expression_propositional_connectives(&goal.target),
        referenced_inductives,
        vec![goal.target_hash],
    ))
}

#[allow(dead_code)]
pub(crate) fn build_verified_premise_index_for_state(
    session: &MachineProofSession,
    input_state: &npa_tactic::MachineProofState,
) -> Result<MachineVerifiedPremiseIndex, TheoremSearchBuildError> {
    let theorem_index = build_theorem_index(session, input_state)?;
    let entries = theorem_index
        .entries
        .iter()
        .map(verified_premise_entry_from_theorem_index_entry)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| TheoremSearchBuildError::PremiseIndexProjection)?;
    Ok(MachineVerifiedPremiseIndex::new(entries))
}

#[allow(dead_code)]
fn verified_premise_entry_from_theorem_index_entry(
    entry: &TheoremIndexEntry,
) -> Result<MachineVerifiedPremiseIndexEntry, MachinePremiseIndexError> {
    let global_ref = MachineVerifiedPremiseGlobalRef {
        module: entry.global_ref.module.clone(),
        name: entry.global_ref.name.clone(),
        export_hash: entry.global_ref.export_hash,
        certificate_hash: entry.certificate_hash,
        decl_interface_hash: entry.global_ref.decl_interface_hash,
    };
    let identity = MachineVerifiedPremiseIdentity::new(
        entry.global_ref.module.clone(),
        entry.global_ref.export_hash,
        entry.certificate_hash,
        global_ref,
        entry.global_ref.decl_interface_hash,
        entry.statement_core_hash,
        MachineVerifiedPremiseAxiomSummary::new(Vec::new(), entry.axioms_used.clone()),
    )?;
    MachineVerifiedPremiseIndexEntry::new(
        identity,
        entry.statement_core_hash,
        entry.structural_features.clone(),
        entry.modes.clone(),
        MachinePremiseIndexSource::DirectImport,
        MachinePremiseRankingMetadata::score_only(0),
    )
}

pub fn project_package_theorem_index_entry_to_verified_premise_entry(
    entry: &npa_package::PackageTheoremIndexEntry,
) -> Result<MachineVerifiedPremiseIndexEntry, MachinePremiseIndexError> {
    let global_ref = MachineVerifiedPremiseGlobalRef {
        module: entry.global_ref.module.clone(),
        name: entry.global_ref.name.clone(),
        export_hash: entry.global_ref.export_hash.into_bytes(),
        certificate_hash: entry.global_ref.certificate_hash.into_bytes(),
        decl_interface_hash: entry.global_ref.decl_interface_hash.into_bytes(),
    };
    let transitive_axioms = entry
        .axiom_dependencies
        .iter()
        .map(package_axiom_ref_to_machine_axiom_ref)
        .collect::<Vec<_>>();
    let mut transitive_axioms = transitive_axioms;
    sort_dedup_axiom_refs(&mut transitive_axioms);
    let identity = MachineVerifiedPremiseIdentity::new(
        entry.global_ref.module.clone(),
        entry.global_ref.export_hash.into_bytes(),
        entry.global_ref.certificate_hash.into_bytes(),
        global_ref,
        entry.global_ref.decl_interface_hash.into_bytes(),
        entry.statement.core_hash.into_bytes(),
        MachineVerifiedPremiseAxiomSummary::new(Vec::new(), transitive_axioms.clone()),
    )?;
    let modes = entry
        .modes
        .iter()
        .map(package_theorem_index_mode_to_machine_mode)
        .collect::<Vec<_>>();
    MachineVerifiedPremiseIndexEntry::new(
        identity,
        entry.statement.core_hash.into_bytes(),
        package_theorem_index_structural_features(entry),
        modes,
        MachinePremiseIndexSource::PackageTheoremIndex,
        {
            let axiom_ranking = package_projection_axiom_ranking_metadata(&transitive_axioms);
            MachinePremiseRankingMetadata::with_axiom_ranking(
                ranking_score_after_axiom_penalties(&axiom_ranking),
                axiom_ranking,
            )
        },
    )
}

pub fn verified_premise_identity_json(identity: &MachineVerifiedPremiseIdentity) -> String {
    json_object_in_order(vec![
        (
            "schema",
            json_string(VERIFIED_PREMISE_IDENTITY_SCHEMA_VERSION),
        ),
        ("module", json_string(&identity.module.as_dotted())),
        ("export_hash", hash_json(&identity.export_hash)),
        ("certificate_hash", hash_json(&identity.certificate_hash)),
        (
            "global_ref",
            verified_premise_global_ref_json(&identity.global_ref),
        ),
        (
            "decl_interface_hash",
            hash_json(&identity.decl_interface_hash),
        ),
        (
            "statement_core_hash",
            hash_json(&identity.statement_core_hash),
        ),
        (
            "axiom_summary",
            verified_premise_axiom_summary_json(&identity.axiom_summary),
        ),
    ])
}

pub fn parse_verified_premise_identity_json(
    source: &str,
) -> Result<MachineVerifiedPremiseIdentity, MachinePremiseIndexError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTheoremIndex)?;
    parse_verified_premise_identity_value(doc.root(), &JsonPath::root())
}

pub fn premise_index_entry_json(entry: &MachinePremiseIndexEntry) -> String {
    match entry {
        MachinePremiseIndexEntry::Verified(entry) => verified_premise_index_entry_json(entry),
        MachinePremiseIndexEntry::UntrustedCandidate(candidate) => json_object_in_order(vec![
            ("schema", json_string(PREMISE_INDEX_ENTRY_SCHEMA_VERSION)),
            ("kind", json_string("untrusted_candidate")),
            ("candidate", untrusted_premise_candidate_json(candidate)),
        ]),
    }
}

pub fn parse_premise_index_entry_json(
    source: &str,
) -> Result<MachinePremiseIndexEntry, MachinePremiseIndexError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidTheoremIndex)?;
    parse_premise_index_entry_value(doc.root(), &JsonPath::root())
}

fn package_axiom_ref_to_machine_axiom_ref(
    axiom: &npa_package::PackageAxiomReference,
) -> MachineAxiomRefWire {
    MachineAxiomRefWire::Imported {
        module: axiom.module.clone(),
        name: axiom.name.clone(),
        export_hash: axiom.export_hash.into_bytes(),
        decl_interface_hash: axiom.decl_interface_hash.into_bytes(),
    }
}

fn package_theorem_index_mode_to_machine_mode(
    mode: &npa_package::PackageTheoremIndexMode,
) -> MachineTheoremMode {
    match mode {
        npa_package::PackageTheoremIndexMode::Exact => MachineTheoremMode::Exact,
        npa_package::PackageTheoremIndexMode::Apply => MachineTheoremMode::Apply,
        npa_package::PackageTheoremIndexMode::Rw => MachineTheoremMode::Rw,
        npa_package::PackageTheoremIndexMode::Simp => MachineTheoremMode::Simp,
    }
}

fn verified_premise_index_entry_json(entry: &MachineVerifiedPremiseIndexEntry) -> String {
    json_object_in_order(vec![
        ("schema", json_string(PREMISE_INDEX_ENTRY_SCHEMA_VERSION)),
        ("kind", json_string("verified")),
        ("identity", verified_premise_identity_json(&entry.identity)),
        ("statement_core_hash", hash_json(&entry.statement_core_hash)),
        (
            "structural_features",
            premise_structural_features_json(&entry.structural_features),
        ),
        (
            "modes",
            json_array(
                entry
                    .modes
                    .iter()
                    .map(|mode| json_string(mode.as_str()))
                    .collect(),
            ),
        ),
        ("source", json_string(entry.source.as_str())),
        (
            "ranking_metadata",
            premise_ranking_metadata_json(&entry.ranking_metadata),
        ),
    ])
}

fn premise_ranking_metadata_json(ranking: &MachinePremiseRankingMetadata) -> String {
    let mut fields = vec![
        ("score", ranking.score.to_string()),
        (
            "axiom_ranking",
            premise_axiom_ranking_metadata_json(&ranking.axiom_ranking),
        ),
        (
            "type_aware",
            type_aware_premise_metadata_json(&ranking.type_aware),
        ),
        (
            "mode_metadata",
            premise_mode_metadata_array_json(&ranking.mode_metadata),
        ),
    ];
    if let Some(premise_set) = &ranking.premise_set {
        fields.push(("premise_set", premise_set_metadata_json(premise_set)));
    }
    json_object_in_order(fields)
}

fn premise_axiom_ranking_metadata_json(ranking: &MachinePremiseAxiomRankingMetadata) -> String {
    json_object_in_order(vec![
        ("theorem_level", json_string(ranking.theorem_level.as_str())),
        ("candidate_verified", ranking.candidate_verified.to_string()),
        (
            "usable_under_axiom_policy",
            ranking.usable_under_axiom_policy.to_string(),
        ),
        ("direct_axiom_count", ranking.direct_axiom_count.to_string()),
        (
            "transitive_axiom_count",
            ranking.transitive_axiom_count.to_string(),
        ),
        (
            "disallowed_axiom_count",
            ranking.disallowed_axiom_count.to_string(),
        ),
        (
            "axiom_paths",
            json_array(
                ranking
                    .axiom_paths
                    .iter()
                    .map(premise_axiom_path_json)
                    .collect(),
            ),
        ),
        (
            "penalties",
            premise_axiom_ranking_penalties_json(&ranking.penalties),
        ),
    ])
}

fn premise_axiom_path_json(path: &MachinePremiseAxiomPath) -> String {
    json_object_in_order(vec![
        ("source", json_string(path.source.as_str())),
        ("axiom", machine_axiom_ref_json(&path.axiom)),
        ("path_length", path.path_length.to_string()),
        (
            "graph_snapshot_hash",
            path.graph_snapshot_hash
                .map(|hash| hash_json(&hash))
                .unwrap_or_else(|| "null".to_owned()),
        ),
    ])
}

fn premise_axiom_ranking_penalties_json(penalties: &MachinePremiseAxiomRankingPenalties) -> String {
    json_object_in_order(vec![
        ("direct_axiom_use", penalties.direct_axiom_use.to_string()),
        (
            "transitive_axiom_expansion",
            penalties.transitive_axiom_expansion.to_string(),
        ),
        (
            "unknown_theorem_level",
            penalties.unknown_theorem_level.to_string(),
        ),
        (
            "unverified_candidate",
            penalties.unverified_candidate.to_string(),
        ),
        ("high_import_cost", penalties.high_import_cost.to_string()),
        (
            "unresolved_premise_obligations",
            penalties.unresolved_premise_obligations.to_string(),
        ),
        ("graph_axiom_path", penalties.graph_axiom_path.to_string()),
        ("disallowed_axiom", penalties.disallowed_axiom.to_string()),
        ("total", penalties.total.to_string()),
    ])
}

fn premise_set_metadata_json(metadata: &MachinePremiseSetMetadata) -> String {
    json_object_in_order(vec![
        ("max_set_size", metadata.max_set_size.to_string()),
        (
            "graph_snapshot_hash",
            metadata
                .graph_snapshot_hash
                .map(|hash| hash_json(&hash))
                .unwrap_or_else(|| "null".to_owned()),
        ),
        (
            "selected_premises",
            json_array(
                metadata
                    .selected_premises
                    .iter()
                    .map(premise_set_selected_premise_json)
                    .collect(),
            ),
        ),
        (
            "covered_goal_features",
            premise_set_feature_array_json(&metadata.covered_goal_features),
        ),
        (
            "missing_goal_features",
            premise_set_feature_array_json(&metadata.missing_goal_features),
        ),
        (
            "rejected_alternatives",
            json_array(
                metadata
                    .rejected_alternatives
                    .iter()
                    .map(premise_set_rejected_alternative_json)
                    .collect(),
            ),
        ),
        (
            "import_requirements",
            json_array(
                metadata
                    .import_requirements
                    .iter()
                    .map(|module| json_string(&module.as_dotted()))
                    .collect(),
            ),
        ),
        (
            "axiom_impact",
            premise_set_axiom_impact_json(&metadata.axiom_impact),
        ),
        ("objective", premise_set_objective_json(&metadata.objective)),
    ])
}

fn premise_set_selected_premise_json(premise: &MachinePremiseSetSelectedPremise) -> String {
    json_object_in_order(vec![
        ("premise", premise_structural_ref_json(&premise.premise)),
        (
            "added_features",
            premise_set_feature_array_json(&premise.added_features),
        ),
        (
            "coverage_score",
            premise.objective.coverage_score.to_string(),
        ),
        (
            "historical_co_use_score",
            premise.objective.historical_co_use_score.to_string(),
        ),
        (
            "graph_connectivity_score",
            premise.objective.graph_connectivity_score.to_string(),
        ),
        (
            "set_size_penalty",
            premise.objective.set_size_penalty.to_string(),
        ),
        (
            "import_cost_penalty",
            premise.objective.import_cost_penalty.to_string(),
        ),
        (
            "axiom_cost_penalty",
            premise.objective.axiom_cost_penalty.to_string(),
        ),
        ("final_score", premise.objective.final_score.to_string()),
    ])
}

fn premise_set_rejected_alternative_json(
    alternative: &MachinePremiseSetRejectedAlternative,
) -> String {
    json_object_in_order(vec![
        ("premise", premise_structural_ref_json(&alternative.premise)),
        ("reason", json_string(alternative.reason.as_str())),
        (
            "would_add_features",
            premise_set_feature_array_json(&alternative.would_add_features),
        ),
        (
            "coverage_score",
            alternative.objective.coverage_score.to_string(),
        ),
        (
            "historical_co_use_score",
            alternative.objective.historical_co_use_score.to_string(),
        ),
        (
            "graph_connectivity_score",
            alternative.objective.graph_connectivity_score.to_string(),
        ),
        (
            "set_size_penalty",
            alternative.objective.set_size_penalty.to_string(),
        ),
        (
            "import_cost_penalty",
            alternative.objective.import_cost_penalty.to_string(),
        ),
        (
            "axiom_cost_penalty",
            alternative.objective.axiom_cost_penalty.to_string(),
        ),
        ("final_score", alternative.objective.final_score.to_string()),
    ])
}

fn premise_set_feature_array_json(features: &[MachinePremiseSetFeature]) -> String {
    json_array(features.iter().map(premise_set_feature_json).collect())
}

fn premise_set_feature_json(feature: &MachinePremiseSetFeature) -> String {
    json_object_in_order(vec![
        ("kind", json_string(feature.kind.as_str())),
        ("feature_hash", hash_json(&feature.feature_hash)),
    ])
}

fn premise_set_axiom_impact_json(impact: &MachinePremiseSetAxiomImpact) -> String {
    json_object_in_order(vec![
        ("direct_axiom_count", impact.direct_axiom_count.to_string()),
        (
            "transitive_axiom_count",
            impact.transitive_axiom_count.to_string(),
        ),
        ("summary_hash", hash_json(&impact.summary_hash)),
        (
            "axiom_paths",
            json_array(
                impact
                    .axiom_paths
                    .iter()
                    .map(premise_axiom_path_json)
                    .collect(),
            ),
        ),
    ])
}

fn premise_set_objective_json(objective: &MachinePremiseSetObjective) -> String {
    json_object_in_order(vec![
        ("coverage_score", objective.coverage_score.to_string()),
        (
            "historical_co_use_score",
            objective.historical_co_use_score.to_string(),
        ),
        (
            "graph_connectivity_score",
            objective.graph_connectivity_score.to_string(),
        ),
        ("set_size_penalty", objective.set_size_penalty.to_string()),
        (
            "import_cost_penalty",
            objective.import_cost_penalty.to_string(),
        ),
        (
            "axiom_cost_penalty",
            objective.axiom_cost_penalty.to_string(),
        ),
        ("final_score", objective.final_score.to_string()),
    ])
}

fn premise_mode_metadata_array_json(metadata: &[MachinePremiseModeMetadata]) -> String {
    json_array(metadata.iter().map(premise_mode_metadata_json).collect())
}

fn premise_mode_metadata_json(metadata: &MachinePremiseModeMetadata) -> String {
    json_object_in_order(vec![
        ("mode", json_string(metadata.mode.as_str())),
        ("status", json_string(metadata.status.as_str())),
        ("reason", json_string(metadata.reason.as_str())),
        (
            "suggested_candidate_count",
            metadata.suggested_candidate_count.to_string(),
        ),
        ("lexical_score", metadata.lexical_score.to_string()),
    ])
}

fn type_aware_premise_metadata_json(metadata: &MachineTypeAwarePremiseMetadata) -> String {
    json_object_in_order(vec![
        ("status", json_string(metadata.status.as_str())),
        (
            "selected_mode",
            metadata
                .selected_mode
                .map(|mode| json_string(mode.as_str()))
                .unwrap_or_else(|| "null".to_owned()),
        ),
        (
            "universe_compatible",
            metadata.universe_compatible.to_string(),
        ),
        ("head_compatible", metadata.head_compatible.to_string()),
        ("result_fits_goal", metadata.result_fits_goal.to_string()),
        ("pi_binder_count", metadata.pi_binder_count.to_string()),
        (
            "unresolved_obligation_type_hashes",
            hash_array_json(&metadata.unresolved_obligation_type_hashes),
        ),
        (
            "local_context_match_type_hashes",
            hash_array_json(&metadata.local_context_match_type_hashes),
        ),
        (
            "generated_argument_sources",
            type_aware_argument_source_array_json(&metadata.generated_argument_sources),
        ),
        (
            "estimated_new_goals",
            metadata.estimated_new_goals.to_string(),
        ),
        ("premise_size", metadata.premise_size.to_string()),
        ("goal_size", metadata.goal_size.to_string()),
    ])
}

fn type_aware_argument_source_array_json(sources: &[MachineTypeAwareArgumentSource]) -> String {
    json_array(
        sources
            .iter()
            .map(|source| json_string(source.as_str()))
            .collect(),
    )
}

fn premise_structural_features_json(features: &MachinePremiseStructuralFeatures) -> String {
    json_object_in_order(vec![
        (
            "target_head",
            optional_premise_structural_ref_json(features.target_head.as_ref()),
        ),
        ("pi_binder_count", features.pi_binder_count.to_string()),
        (
            "argument_universe_fingerprints",
            hash_array_json(&features.argument_universe_fingerprints),
        ),
        (
            "result_universe_fingerprint",
            hash_json(&features.result_universe_fingerprint),
        ),
        (
            "recursive_occurrences",
            premise_structural_ref_array_json(&features.recursive_occurrences),
        ),
        (
            "equality_lhs_head",
            optional_premise_structural_ref_json(features.equality_lhs_head.as_ref()),
        ),
        (
            "equality_rhs_head",
            optional_premise_structural_ref_json(features.equality_rhs_head.as_ref()),
        ),
        (
            "propositional_connectives",
            json_array(
                features
                    .propositional_connectives
                    .iter()
                    .map(|connective| json_string(connective.as_str()))
                    .collect(),
            ),
        ),
        (
            "referenced_inductives",
            premise_structural_ref_array_json(&features.referenced_inductives),
        ),
        (
            "normalized_expression_fingerprints",
            hash_array_json(&features.normalized_expression_fingerprints),
        ),
        ("feature_hash", hash_json(&features.feature_hash)),
    ])
}

fn optional_premise_structural_ref_json(value: Option<&MachinePremiseStructuralRef>) -> String {
    value
        .map(premise_structural_ref_json)
        .unwrap_or_else(|| "null".to_owned())
}

fn premise_structural_ref_array_json(refs: &[MachinePremiseStructuralRef]) -> String {
    json_array(refs.iter().map(premise_structural_ref_json).collect())
}

fn premise_structural_ref_json(reference: &MachinePremiseStructuralRef) -> String {
    json_object_in_order(vec![
        ("module", json_string(&reference.module.as_dotted())),
        ("name", json_string(&reference.name.as_dotted())),
        (
            "export_hash",
            reference
                .export_hash
                .as_ref()
                .map(hash_json)
                .unwrap_or_else(|| "null".to_owned()),
        ),
        (
            "decl_interface_hash",
            hash_json(&reference.decl_interface_hash),
        ),
    ])
}

fn hash_array_json(hashes: &[Hash]) -> String {
    json_array(hashes.iter().map(hash_json).collect())
}

fn untrusted_premise_candidate_json(candidate: &MachineUntrustedPremiseCandidate) -> String {
    json_object_in_order(vec![
        ("candidate_hash", hash_json(&candidate.candidate_hash)),
        ("source_label", json_string(&candidate.source_label)),
        ("reason", json_string(&candidate.reason)),
    ])
}

fn verified_premise_global_ref_json(global_ref: &MachineVerifiedPremiseGlobalRef) -> String {
    json_object_in_order(vec![
        ("module", json_string(&global_ref.module.as_dotted())),
        ("name", json_string(&global_ref.name.as_dotted())),
        ("export_hash", hash_json(&global_ref.export_hash)),
        ("certificate_hash", hash_json(&global_ref.certificate_hash)),
        (
            "decl_interface_hash",
            hash_json(&global_ref.decl_interface_hash),
        ),
    ])
}

fn verified_premise_axiom_summary_json(summary: &MachineVerifiedPremiseAxiomSummary) -> String {
    json_object_in_order(vec![
        (
            "direct_axioms",
            json_array(
                summary
                    .direct_axioms
                    .iter()
                    .map(machine_axiom_ref_json)
                    .collect(),
            ),
        ),
        (
            "transitive_axioms",
            json_array(
                summary
                    .transitive_axioms
                    .iter()
                    .map(machine_axiom_ref_json)
                    .collect(),
            ),
        ),
        ("summary_hash", hash_json(&summary.summary_hash)),
    ])
}

fn machine_axiom_ref_json(axiom: &MachineAxiomRefWire) -> String {
    match axiom {
        MachineAxiomRefWire::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
        } => json_object_in_order(vec![
            ("kind", json_string("imported")),
            ("module", json_string(&module.as_dotted())),
            ("name", json_string(&name.as_dotted())),
            ("export_hash", hash_json(export_hash)),
            ("decl_interface_hash", hash_json(decl_interface_hash)),
        ]),
        MachineAxiomRefWire::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
        } => json_object_in_order(vec![
            ("kind", json_string("current_module")),
            ("module", json_string(&module.as_dotted())),
            ("name", json_string(&name.as_dotted())),
            ("source_index", source_index.to_string()),
            ("decl_interface_hash", hash_json(decl_interface_hash)),
        ]),
        MachineAxiomRefWire::Builtin {
            name,
            decl_interface_hash,
        } => json_object_in_order(vec![
            ("kind", json_string("builtin")),
            ("name", json_string(&name.as_dotted())),
            ("decl_interface_hash", hash_json(decl_interface_hash)),
        ]),
    }
}

fn parse_premise_index_entry_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseIndexEntry, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_INDEX_ENTRY_FIELDS,
        ),
        path,
    )?;
    let schema = premise_required_string(&object, "schema", path)?;
    if schema != PREMISE_INDEX_ENTRY_SCHEMA_VERSION {
        return Err(premise_index_error(
            &path.field("schema"),
            MachinePremiseIndexErrorReason::InvalidSchema {
                expected: PREMISE_INDEX_ENTRY_SCHEMA_VERSION,
                actual: schema.to_owned(),
            },
        ));
    }
    let kind = premise_required_string(&object, "kind", path)?;
    match kind {
        "verified" => parse_verified_premise_index_entry_value(value, path)
            .map(Box::new)
            .map(MachinePremiseIndexEntry::Verified),
        "untrusted_candidate" => parse_untrusted_premise_index_entry_value(value, path),
        _ => Err(premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "kind",
                value: kind.to_owned(),
            },
        )),
    }
}

fn parse_untrusted_premise_index_entry_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseIndexEntry, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            UNTRUSTED_PREMISE_INDEX_ENTRY_FIELDS,
        ),
        path,
    )?;
    let schema = premise_required_string(&object, "schema", path)?;
    if schema != PREMISE_INDEX_ENTRY_SCHEMA_VERSION {
        return Err(premise_index_error(
            &path.field("schema"),
            MachinePremiseIndexErrorReason::InvalidSchema {
                expected: PREMISE_INDEX_ENTRY_SCHEMA_VERSION,
                actual: schema.to_owned(),
            },
        ));
    }
    let kind = premise_required_string(&object, "kind", path)?;
    if kind != "untrusted_candidate" {
        return Err(premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "kind",
                value: kind.to_owned(),
            },
        ));
    }
    Ok(MachinePremiseIndexEntry::UntrustedCandidate(
        parse_untrusted_premise_candidate_value(
            premise_required_field(&object, "candidate"),
            &path.field("candidate"),
        )?,
    ))
}

fn parse_verified_premise_index_entry_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineVerifiedPremiseIndexEntry, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            VERIFIED_PREMISE_INDEX_ENTRY_FIELDS,
        ),
        path,
    )?;
    let schema = premise_required_string(&object, "schema", path)?;
    if schema != PREMISE_INDEX_ENTRY_SCHEMA_VERSION {
        return Err(premise_index_error(
            &path.field("schema"),
            MachinePremiseIndexErrorReason::InvalidSchema {
                expected: PREMISE_INDEX_ENTRY_SCHEMA_VERSION,
                actual: schema.to_owned(),
            },
        ));
    }
    let kind = premise_required_string(&object, "kind", path)?;
    if kind != "verified" {
        return Err(premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "kind",
                value: kind.to_owned(),
            },
        ));
    }
    let identity = parse_verified_premise_identity_value(
        premise_required_field(&object, "identity"),
        &path.field("identity"),
    )?;
    let statement_core_hash = premise_required_hash(
        &object,
        "statement_core_hash",
        &path.field("statement_core_hash"),
    )?;
    let structural_features = parse_premise_structural_features_value(
        premise_required_field(&object, "structural_features"),
        &path.field("structural_features"),
    )?;
    let modes = parse_theorem_modes(
        premise_required_field(&object, "modes"),
        &path.field("modes"),
        MachineApiErrorKind::InvalidTheoremIndex,
    )?;
    let source_text = premise_required_string(&object, "source", path)?;
    let source = MachinePremiseIndexSource::parse(source_text).ok_or_else(|| {
        premise_index_error(
            &path.field("source"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "source",
                value: source_text.to_owned(),
            },
        )
    })?;
    let ranking_metadata = parse_premise_ranking_metadata_value(
        premise_required_field(&object, "ranking_metadata"),
        &path.field("ranking_metadata"),
    )?;
    MachineVerifiedPremiseIndexEntry::new(
        identity,
        statement_core_hash,
        structural_features,
        modes,
        source,
        ranking_metadata,
    )
}

fn parse_premise_structural_features_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseStructuralFeatures, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_STRUCTURAL_FEATURE_FIELDS,
        ),
        path,
    )?;
    let target_head = parse_optional_premise_structural_ref_value(
        premise_required_field(&object, "target_head"),
        &path.field("target_head"),
    )?;
    let raw_pi_binder_count =
        premise_required_u64(&object, "pi_binder_count", &path.field("pi_binder_count"))?;
    let pi_binder_count = u32::try_from(raw_pi_binder_count).map_err(|_| {
        premise_index_error(
            &path.field("pi_binder_count"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "pi_binder_count",
                value: raw_pi_binder_count.to_string(),
            },
        )
    })?;
    let argument_universe_fingerprints = parse_hash_array(
        premise_required_field(&object, "argument_universe_fingerprints"),
        &path.field("argument_universe_fingerprints"),
        "argument_universe_fingerprints",
    )?;
    let result_universe_fingerprint = premise_required_hash(
        &object,
        "result_universe_fingerprint",
        &path.field("result_universe_fingerprint"),
    )?;
    let recursive_occurrences = parse_premise_structural_ref_array(
        premise_required_field(&object, "recursive_occurrences"),
        &path.field("recursive_occurrences"),
        "recursive_occurrences",
    )?;
    let equality_lhs_head = parse_optional_premise_structural_ref_value(
        premise_required_field(&object, "equality_lhs_head"),
        &path.field("equality_lhs_head"),
    )?;
    let equality_rhs_head = parse_optional_premise_structural_ref_value(
        premise_required_field(&object, "equality_rhs_head"),
        &path.field("equality_rhs_head"),
    )?;
    let propositional_connectives = parse_premise_propositional_connective_array(
        premise_required_field(&object, "propositional_connectives"),
        &path.field("propositional_connectives"),
    )?;
    let referenced_inductives = parse_premise_structural_ref_array(
        premise_required_field(&object, "referenced_inductives"),
        &path.field("referenced_inductives"),
        "referenced_inductives",
    )?;
    let normalized_expression_fingerprints = parse_hash_array(
        premise_required_field(&object, "normalized_expression_fingerprints"),
        &path.field("normalized_expression_fingerprints"),
        "normalized_expression_fingerprints",
    )?;
    let feature_hash = premise_required_hash(&object, "feature_hash", &path.field("feature_hash"))?;
    let features = MachinePremiseStructuralFeatures::new(
        target_head,
        pi_binder_count,
        argument_universe_fingerprints,
        result_universe_fingerprint,
        recursive_occurrences,
        equality_lhs_head,
        equality_rhs_head,
        propositional_connectives,
        referenced_inductives,
        normalized_expression_fingerprints,
    );
    if features.feature_hash != feature_hash {
        return Err(premise_index_error(
            &path.field("feature_hash"),
            MachinePremiseIndexErrorReason::StructuralFeatureHashMismatch,
        ));
    }
    Ok(features)
}

fn parse_optional_premise_structural_ref_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Option<MachinePremiseStructuralRef>, MachinePremiseIndexError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    parse_premise_structural_ref_value(value, path).map(Some)
}

fn parse_premise_structural_ref_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Vec<MachinePremiseStructuralRef>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field,
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    elements
        .iter()
        .enumerate()
        .map(|(index, item)| parse_premise_structural_ref_value(item, &path.index(index)))
        .collect()
}

fn parse_premise_structural_ref_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseStructuralRef, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_STRUCTURAL_REF_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseStructuralRef {
        module: premise_required_module(&object, "module", &path.field("module"))?,
        name: premise_required_name(&object, "name", &path.field("name"))?,
        export_hash: premise_required_nullable_hash(
            &object,
            "export_hash",
            &path.field("export_hash"),
        )?,
        decl_interface_hash: premise_required_hash(
            &object,
            "decl_interface_hash",
            &path.field("decl_interface_hash"),
        )?,
    })
}

fn parse_premise_propositional_connective_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremisePropositionalConnective>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "propositional_connectives",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut values = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let Some(text) = item.string_value() else {
            return Err(premise_index_error(
                &item_path,
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::TypeMismatch {
                        field: "propositional_connectives",
                        expected: JsonFieldType::String,
                        actual: item.kind(),
                    },
                ),
            ));
        };
        let Some(connective) = MachinePremisePropositionalConnective::parse(text) else {
            return Err(premise_index_error(
                &item_path,
                MachinePremiseIndexErrorReason::InvalidEnum {
                    field: "propositional_connectives",
                    value: text.to_owned(),
                },
            ));
        };
        values.push(connective);
    }
    Ok(values)
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Vec<Hash>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field,
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    elements
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let item_path = path.index(index);
            let text = item.string_value().ok_or_else(|| {
                premise_index_error(
                    &item_path,
                    MachinePremiseIndexErrorReason::Request(
                        MachineApiErrorKind::InvalidTheoremIndex,
                        MachineApiRequestErrorReason::TypeMismatch {
                            field,
                            expected: JsonFieldType::String,
                            actual: item.kind(),
                        },
                    ),
                )
            })?;
            parse_hash_string(text).map_err(|_| {
                premise_index_error(
                    &item_path,
                    MachinePremiseIndexErrorReason::InvalidHash { field },
                )
            })
        })
        .collect()
}

fn parse_verified_premise_identity_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineVerifiedPremiseIdentity, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            VERIFIED_PREMISE_IDENTITY_FIELDS,
        ),
        path,
    )?;
    let schema = premise_required_string(&object, "schema", path)?;
    if schema != VERIFIED_PREMISE_IDENTITY_SCHEMA_VERSION {
        return Err(premise_index_error(
            &path.field("schema"),
            MachinePremiseIndexErrorReason::InvalidSchema {
                expected: VERIFIED_PREMISE_IDENTITY_SCHEMA_VERSION,
                actual: schema.to_owned(),
            },
        ));
    }
    let module = premise_required_module(&object, "module", &path.field("module"))?;
    let export_hash = premise_required_hash(&object, "export_hash", &path.field("export_hash"))?;
    let certificate_hash =
        premise_required_hash(&object, "certificate_hash", &path.field("certificate_hash"))?;
    let global_ref = parse_verified_premise_global_ref_value(
        premise_required_field(&object, "global_ref"),
        &path.field("global_ref"),
    )?;
    let decl_interface_hash = premise_required_hash(
        &object,
        "decl_interface_hash",
        &path.field("decl_interface_hash"),
    )?;
    let statement_core_hash = premise_required_hash(
        &object,
        "statement_core_hash",
        &path.field("statement_core_hash"),
    )?;
    let axiom_summary = parse_verified_premise_axiom_summary_value(
        premise_required_field(&object, "axiom_summary"),
        &path.field("axiom_summary"),
    )?;
    validate_verified_premise_identity_parts(
        &module,
        &export_hash,
        &certificate_hash,
        &global_ref,
        &decl_interface_hash,
        &axiom_summary,
        path,
    )?;
    Ok(MachineVerifiedPremiseIdentity {
        module,
        export_hash,
        certificate_hash,
        global_ref,
        decl_interface_hash,
        statement_core_hash,
        axiom_summary,
    })
}

fn parse_verified_premise_global_ref_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineVerifiedPremiseGlobalRef, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            VERIFIED_PREMISE_GLOBAL_REF_FIELDS,
        ),
        path,
    )?;
    Ok(MachineVerifiedPremiseGlobalRef {
        module: premise_required_module(&object, "module", &path.field("module"))?,
        name: premise_required_name(&object, "name", &path.field("name"))?,
        export_hash: premise_required_hash(&object, "export_hash", &path.field("export_hash"))?,
        certificate_hash: premise_required_hash(
            &object,
            "certificate_hash",
            &path.field("certificate_hash"),
        )?,
        decl_interface_hash: premise_required_hash(
            &object,
            "decl_interface_hash",
            &path.field("decl_interface_hash"),
        )?,
    })
}

fn parse_verified_premise_axiom_summary_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineVerifiedPremiseAxiomSummary, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            VERIFIED_PREMISE_AXIOM_SUMMARY_FIELDS,
        ),
        path,
    )?;
    let direct_axioms = parse_machine_axiom_ref_array(
        premise_required_field(&object, "direct_axioms"),
        &path.field("direct_axioms"),
        "direct_axioms",
    )?;
    let transitive_axioms = parse_machine_axiom_ref_array(
        premise_required_field(&object, "transitive_axioms"),
        &path.field("transitive_axioms"),
        "transitive_axioms",
    )?;
    let summary_hash = premise_required_hash(&object, "summary_hash", &path.field("summary_hash"))?;
    let computed = verified_premise_axiom_summary_hash(&direct_axioms, &transitive_axioms);
    if computed != summary_hash {
        return Err(premise_index_error(
            &path.field("summary_hash"),
            MachinePremiseIndexErrorReason::AxiomSummaryHashMismatch,
        ));
    }
    Ok(MachineVerifiedPremiseAxiomSummary {
        direct_axioms,
        transitive_axioms,
        summary_hash,
    })
}

fn parse_machine_axiom_ref_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Vec<MachineAxiomRefWire>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field,
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut refs = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        refs.push(parse_machine_axiom_ref_value(item, &path.index(index))?);
    }
    if !machine_axiom_refs_are_canonical(&refs) {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::NonCanonicalAxiomRefs { field },
        ));
    }
    Ok(refs)
}

fn parse_machine_axiom_ref_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineAxiomRefWire, MachinePremiseIndexError> {
    const IMPORTED_AXIOM_FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("module", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required("export_hash", JsonFieldType::String),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    const CURRENT_AXIOM_FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("module", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required(
            "source_index",
            JsonFieldType::UnsignedInteger { max: u64::MAX },
        ),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    const BUILTIN_AXIOM_FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    let Some(kind) = value
        .object_members()
        .and_then(|members| members.iter().find(|member| member.key() == "kind"))
        .and_then(|member| member.value().string_value())
    else {
        return Err(premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::MissingField { field: "kind" },
            ),
        ));
    };
    match kind {
        "imported" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    IMPORTED_AXIOM_FIELDS,
                ),
                path,
            )?;
            Ok(MachineAxiomRefWire::Imported {
                module: premise_required_module(&object, "module", &path.field("module"))?,
                name: premise_required_name(&object, "name", &path.field("name"))?,
                export_hash: premise_required_hash(
                    &object,
                    "export_hash",
                    &path.field("export_hash"),
                )?,
                decl_interface_hash: premise_required_hash(
                    &object,
                    "decl_interface_hash",
                    &path.field("decl_interface_hash"),
                )?,
            })
        }
        "current_module" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    CURRENT_AXIOM_FIELDS,
                ),
                path,
            )?;
            Ok(MachineAxiomRefWire::CurrentModule {
                module: premise_required_module(&object, "module", &path.field("module"))?,
                name: premise_required_name(&object, "name", &path.field("name"))?,
                source_index: premise_required_u64(
                    &object,
                    "source_index",
                    &path.field("source_index"),
                )?,
                decl_interface_hash: premise_required_hash(
                    &object,
                    "decl_interface_hash",
                    &path.field("decl_interface_hash"),
                )?,
            })
        }
        "builtin" => {
            let object = validate_json_object(
                value,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    BUILTIN_AXIOM_FIELDS,
                ),
                path,
            )?;
            Ok(MachineAxiomRefWire::Builtin {
                name: premise_required_name(&object, "name", &path.field("name"))?,
                decl_interface_hash: premise_required_hash(
                    &object,
                    "decl_interface_hash",
                    &path.field("decl_interface_hash"),
                )?,
            })
        }
        _ => Err(premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "kind",
                value: kind.to_owned(),
            },
        )),
    }
}

fn parse_untrusted_premise_candidate_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineUntrustedPremiseCandidate, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            UNTRUSTED_PREMISE_CANDIDATE_FIELDS,
        ),
        path,
    )?;
    Ok(MachineUntrustedPremiseCandidate {
        candidate_hash: premise_required_hash(
            &object,
            "candidate_hash",
            &path.field("candidate_hash"),
        )?,
        source_label: premise_required_string(&object, "source_label", path)?.to_owned(),
        reason: premise_required_string(&object, "reason", path)?.to_owned(),
    })
}

fn parse_premise_ranking_metadata_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseRankingMetadata, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_RANKING_METADATA_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseRankingMetadata {
        score: premise_required_u64(&object, "score", &path.field("score"))?,
        axiom_ranking: match object.field("axiom_ranking") {
            Some(value) => {
                parse_premise_axiom_ranking_metadata_value(value, &path.field("axiom_ranking"))?
            }
            None => MachinePremiseAxiomRankingMetadata::verified_no_axioms(),
        },
        type_aware: match object.field("type_aware") {
            Some(value) => {
                parse_type_aware_premise_metadata_value(value, &path.field("type_aware"))?
            }
            None => MachineTypeAwarePremiseMetadata::not_evaluated(),
        },
        mode_metadata: match object.field("mode_metadata") {
            Some(value) => parse_premise_mode_metadata_array(value, &path.field("mode_metadata"))?,
            None => Vec::new(),
        },
        premise_set: match object.field("premise_set") {
            Some(value) => Some(parse_premise_set_metadata_value(
                value,
                &path.field("premise_set"),
            )?),
            None => None,
        },
    })
}

fn parse_premise_axiom_ranking_metadata_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseAxiomRankingMetadata, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_AXIOM_RANKING_FIELDS,
        ),
        path,
    )?;
    let theorem_level_text =
        premise_required_string(&object, "theorem_level", &path.field("theorem_level"))?;
    let theorem_level = MachinePremiseTheoremLevel::parse(theorem_level_text).ok_or_else(|| {
        premise_index_error(
            &path.field("theorem_level"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "theorem_level",
                value: theorem_level_text.to_owned(),
            },
        )
    })?;
    Ok(MachinePremiseAxiomRankingMetadata {
        theorem_level,
        candidate_verified: premise_required_bool(
            &object,
            "candidate_verified",
            &path.field("candidate_verified"),
        ),
        usable_under_axiom_policy: premise_required_bool(
            &object,
            "usable_under_axiom_policy",
            &path.field("usable_under_axiom_policy"),
        ),
        direct_axiom_count: premise_required_u32(
            &object,
            "direct_axiom_count",
            &path.field("direct_axiom_count"),
        )?,
        transitive_axiom_count: premise_required_u32(
            &object,
            "transitive_axiom_count",
            &path.field("transitive_axiom_count"),
        )?,
        disallowed_axiom_count: premise_required_u32(
            &object,
            "disallowed_axiom_count",
            &path.field("disallowed_axiom_count"),
        )?,
        axiom_paths: parse_premise_axiom_path_array(
            premise_required_field(&object, "axiom_paths"),
            &path.field("axiom_paths"),
        )?,
        penalties: parse_premise_axiom_ranking_penalties_value(
            premise_required_field(&object, "penalties"),
            &path.field("penalties"),
        )?,
    })
}

fn parse_premise_axiom_path_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremiseAxiomPath>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "axiom_paths",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut paths = elements
        .iter()
        .enumerate()
        .map(|(index, item)| parse_premise_axiom_path_value(item, &path.index(index)))
        .collect::<Result<Vec<_>, _>>()?;
    sort_dedup_premise_axiom_paths(&mut paths);
    Ok(paths)
}

fn parse_premise_axiom_path_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseAxiomPath, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_AXIOM_PATH_FIELDS,
        ),
        path,
    )?;
    let source_text = premise_required_string(&object, "source", &path.field("source"))?;
    let source = MachinePremiseAxiomPathSource::parse(source_text).ok_or_else(|| {
        premise_index_error(
            &path.field("source"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "source",
                value: source_text.to_owned(),
            },
        )
    })?;
    Ok(MachinePremiseAxiomPath {
        source,
        axiom: parse_machine_axiom_ref_value(
            premise_required_field(&object, "axiom"),
            &path.field("axiom"),
        )?,
        path_length: premise_required_u32(&object, "path_length", &path.field("path_length"))?,
        graph_snapshot_hash: premise_required_nullable_hash(
            &object,
            "graph_snapshot_hash",
            &path.field("graph_snapshot_hash"),
        )?,
    })
}

fn parse_premise_axiom_ranking_penalties_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseAxiomRankingPenalties, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_AXIOM_RANKING_PENALTY_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseAxiomRankingPenalties {
        direct_axiom_use: premise_required_u64(
            &object,
            "direct_axiom_use",
            &path.field("direct_axiom_use"),
        )?,
        transitive_axiom_expansion: premise_required_u64(
            &object,
            "transitive_axiom_expansion",
            &path.field("transitive_axiom_expansion"),
        )?,
        unknown_theorem_level: premise_required_u64(
            &object,
            "unknown_theorem_level",
            &path.field("unknown_theorem_level"),
        )?,
        unverified_candidate: premise_required_u64(
            &object,
            "unverified_candidate",
            &path.field("unverified_candidate"),
        )?,
        high_import_cost: premise_required_u64(
            &object,
            "high_import_cost",
            &path.field("high_import_cost"),
        )?,
        unresolved_premise_obligations: premise_required_u64(
            &object,
            "unresolved_premise_obligations",
            &path.field("unresolved_premise_obligations"),
        )?,
        graph_axiom_path: premise_required_u64(
            &object,
            "graph_axiom_path",
            &path.field("graph_axiom_path"),
        )?,
        disallowed_axiom: premise_required_u64(
            &object,
            "disallowed_axiom",
            &path.field("disallowed_axiom"),
        )?,
        total: premise_required_u64(&object, "total", &path.field("total"))?,
    })
}

fn parse_premise_set_metadata_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetMetadata, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_METADATA_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseSetMetadata {
        max_set_size: premise_required_u32(&object, "max_set_size", &path.field("max_set_size"))?,
        graph_snapshot_hash: premise_required_nullable_hash(
            &object,
            "graph_snapshot_hash",
            &path.field("graph_snapshot_hash"),
        )?,
        selected_premises: parse_premise_set_selected_premise_array(
            premise_required_field(&object, "selected_premises"),
            &path.field("selected_premises"),
        )?,
        covered_goal_features: parse_premise_set_feature_array(
            premise_required_field(&object, "covered_goal_features"),
            &path.field("covered_goal_features"),
        )?,
        missing_goal_features: parse_premise_set_feature_array(
            premise_required_field(&object, "missing_goal_features"),
            &path.field("missing_goal_features"),
        )?,
        rejected_alternatives: parse_premise_set_rejected_alternative_array(
            premise_required_field(&object, "rejected_alternatives"),
            &path.field("rejected_alternatives"),
        )?,
        import_requirements: parse_premise_set_import_requirements(
            premise_required_field(&object, "import_requirements"),
            &path.field("import_requirements"),
        )?,
        axiom_impact: parse_premise_set_axiom_impact_value(
            premise_required_field(&object, "axiom_impact"),
            &path.field("axiom_impact"),
        )?,
        objective: parse_premise_set_objective_value(
            premise_required_field(&object, "objective"),
            &path.field("objective"),
        )?,
    })
}

fn parse_premise_set_selected_premise_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremiseSetSelectedPremise>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "selected_premises",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_premise_set_selected_premise_value(value, &path.index(index)))
        .collect()
}

fn parse_premise_set_selected_premise_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetSelectedPremise, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_SELECTED_PREMISE_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseSetSelectedPremise {
        premise: parse_premise_structural_ref_value(
            premise_required_field(&object, "premise"),
            &path.field("premise"),
        )?,
        added_features: parse_premise_set_feature_array(
            premise_required_field(&object, "added_features"),
            &path.field("added_features"),
        )?,
        objective: parse_premise_set_objective_fields(&object, path)?,
    })
}

fn parse_premise_set_rejected_alternative_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremiseSetRejectedAlternative>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "rejected_alternatives",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_premise_set_rejected_alternative_value(value, &path.index(index))
        })
        .collect()
}

fn parse_premise_set_rejected_alternative_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetRejectedAlternative, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_REJECTED_ALTERNATIVE_FIELDS,
        ),
        path,
    )?;
    let reason_text = premise_required_string(&object, "reason", &path.field("reason"))?;
    let reason = MachinePremiseSetRejectedReason::parse(reason_text).ok_or_else(|| {
        premise_index_error(
            &path.field("reason"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "reason",
                value: reason_text.to_owned(),
            },
        )
    })?;
    Ok(MachinePremiseSetRejectedAlternative {
        premise: parse_premise_structural_ref_value(
            premise_required_field(&object, "premise"),
            &path.field("premise"),
        )?,
        reason,
        would_add_features: parse_premise_set_feature_array(
            premise_required_field(&object, "would_add_features"),
            &path.field("would_add_features"),
        )?,
        objective: parse_premise_set_objective_fields(&object, path)?,
    })
}

fn parse_premise_set_feature_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremiseSetFeature>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "features",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut out = elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_premise_set_feature_value(value, &path.index(index)))
        .collect::<Result<Vec<_>, _>>()?;
    out.sort();
    out.dedup();
    Ok(out)
}

fn parse_premise_set_feature_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetFeature, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_FEATURE_FIELDS,
        ),
        path,
    )?;
    let kind_text = premise_required_string(&object, "kind", &path.field("kind"))?;
    let kind = MachinePremiseSetFeatureKind::parse(kind_text).ok_or_else(|| {
        premise_index_error(
            &path.field("kind"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "kind",
                value: kind_text.to_owned(),
            },
        )
    })?;
    Ok(MachinePremiseSetFeature {
        kind,
        feature_hash: premise_required_hash(&object, "feature_hash", &path.field("feature_hash"))?,
    })
}

fn parse_premise_set_import_requirements(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<Name>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "import_requirements",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut out = elements
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let item_path = path.index(index);
            let Some(text) = value.string_value() else {
                return Err(premise_index_error(
                    &item_path,
                    MachinePremiseIndexErrorReason::Request(
                        MachineApiErrorKind::InvalidTheoremIndex,
                        MachineApiRequestErrorReason::TypeMismatch {
                            field: "import_requirements",
                            expected: JsonFieldType::String,
                            actual: value.kind(),
                        },
                    ),
                ));
            };
            parse_machine_api_name(text).map_err(|_| {
                premise_index_error(
                    &item_path,
                    MachinePremiseIndexErrorReason::InvalidName {
                        field: "import_requirements",
                    },
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    out.sort();
    out.dedup();
    Ok(out)
}

fn parse_premise_set_axiom_impact_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetAxiomImpact, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_AXIOM_IMPACT_FIELDS,
        ),
        path,
    )?;
    Ok(MachinePremiseSetAxiomImpact {
        direct_axiom_count: premise_required_u32(
            &object,
            "direct_axiom_count",
            &path.field("direct_axiom_count"),
        )?,
        transitive_axiom_count: premise_required_u32(
            &object,
            "transitive_axiom_count",
            &path.field("transitive_axiom_count"),
        )?,
        summary_hash: premise_required_hash(&object, "summary_hash", &path.field("summary_hash"))?,
        axiom_paths: match object.field("axiom_paths") {
            Some(value) => parse_premise_axiom_path_array(value, &path.field("axiom_paths"))?,
            None => Vec::new(),
        },
    })
}

fn parse_premise_set_objective_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetObjective, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_SET_OBJECTIVE_FIELDS,
        ),
        path,
    )?;
    parse_premise_set_objective_fields(&object, path)
}

fn parse_premise_set_objective_fields(
    object: &ValidatedObject<'_, '_>,
    path: &JsonPath,
) -> Result<MachinePremiseSetObjective, MachinePremiseIndexError> {
    Ok(MachinePremiseSetObjective {
        coverage_score: premise_required_u64(
            object,
            "coverage_score",
            &path.field("coverage_score"),
        )?,
        historical_co_use_score: premise_required_u64(
            object,
            "historical_co_use_score",
            &path.field("historical_co_use_score"),
        )?,
        graph_connectivity_score: premise_required_u64(
            object,
            "graph_connectivity_score",
            &path.field("graph_connectivity_score"),
        )?,
        set_size_penalty: premise_required_u64(
            object,
            "set_size_penalty",
            &path.field("set_size_penalty"),
        )?,
        import_cost_penalty: premise_required_u64(
            object,
            "import_cost_penalty",
            &path.field("import_cost_penalty"),
        )?,
        axiom_cost_penalty: premise_required_u64(
            object,
            "axiom_cost_penalty",
            &path.field("axiom_cost_penalty"),
        )?,
        final_score: premise_required_u64(object, "final_score", &path.field("final_score"))?,
    })
}

fn parse_premise_mode_metadata_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachinePremiseModeMetadata>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "mode_metadata",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut out = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let metadata = parse_premise_mode_metadata_value(item, &item_path)?;
        if !seen.insert(metadata.mode) {
            return Err(premise_index_error(
                &item_path.field("mode"),
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::DuplicateKey {
                        key: metadata.mode.as_str().to_owned(),
                    },
                ),
            ));
        }
        out.push(metadata);
    }
    Ok(out)
}

fn parse_premise_mode_metadata_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePremiseModeMetadata, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            PREMISE_MODE_METADATA_FIELDS,
        ),
        path,
    )?;
    let mode_text = premise_required_string(&object, "mode", path)?;
    let mode = MachineTheoremMode::parse(mode_text).ok_or_else(|| {
        premise_index_error(
            &path.field("mode"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "mode",
                value: mode_text.to_owned(),
            },
        )
    })?;
    let status_text = premise_required_string(&object, "status", path)?;
    let status = MachinePremiseModeStatus::parse(status_text).ok_or_else(|| {
        premise_index_error(
            &path.field("status"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "status",
                value: status_text.to_owned(),
            },
        )
    })?;
    let reason_text = premise_required_string(&object, "reason", path)?;
    let reason = MachinePremiseModeReason::parse(reason_text).ok_or_else(|| {
        premise_index_error(
            &path.field("reason"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "reason",
                value: reason_text.to_owned(),
            },
        )
    })?;
    Ok(MachinePremiseModeMetadata {
        mode,
        status,
        reason,
        suggested_candidate_count: premise_required_u64(
            &object,
            "suggested_candidate_count",
            &path.field("suggested_candidate_count"),
        )?,
        lexical_score: premise_required_u64(
            &object,
            "lexical_score",
            &path.field("lexical_score"),
        )?,
    })
}

fn parse_type_aware_premise_metadata_value(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineTypeAwarePremiseMetadata, MachinePremiseIndexError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremIndex,
            TYPE_AWARE_PREMISE_METADATA_FIELDS,
        ),
        path,
    )?;
    let status_text = premise_required_string(&object, "status", &path.field("status"))?;
    let status = MachineTypeAwarePremiseStatus::parse(status_text).ok_or_else(|| {
        premise_index_error(
            &path.field("status"),
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "status",
                value: status_text.to_owned(),
            },
        )
    })?;
    Ok(MachineTypeAwarePremiseMetadata {
        status,
        selected_mode: parse_optional_type_aware_mode(
            premise_required_field(&object, "selected_mode"),
            &path.field("selected_mode"),
        )?,
        universe_compatible: premise_required_bool(
            &object,
            "universe_compatible",
            &path.field("universe_compatible"),
        ),
        head_compatible: premise_required_bool(
            &object,
            "head_compatible",
            &path.field("head_compatible"),
        ),
        result_fits_goal: premise_required_bool(
            &object,
            "result_fits_goal",
            &path.field("result_fits_goal"),
        ),
        pi_binder_count: premise_required_u64(
            &object,
            "pi_binder_count",
            &path.field("pi_binder_count"),
        )?,
        unresolved_obligation_type_hashes: parse_hash_array(
            premise_required_field(&object, "unresolved_obligation_type_hashes"),
            &path.field("unresolved_obligation_type_hashes"),
            "unresolved_obligation_type_hashes",
        )?,
        local_context_match_type_hashes: parse_hash_array(
            premise_required_field(&object, "local_context_match_type_hashes"),
            &path.field("local_context_match_type_hashes"),
            "local_context_match_type_hashes",
        )?,
        generated_argument_sources: parse_type_aware_argument_source_array(
            premise_required_field(&object, "generated_argument_sources"),
            &path.field("generated_argument_sources"),
        )?,
        estimated_new_goals: premise_required_u64(
            &object,
            "estimated_new_goals",
            &path.field("estimated_new_goals"),
        )?,
        premise_size: premise_required_u64(&object, "premise_size", &path.field("premise_size"))?,
        goal_size: premise_required_u64(&object, "goal_size", &path.field("goal_size"))?,
    })
}

fn parse_optional_type_aware_mode(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Option<MachineTheoremMode>, MachinePremiseIndexError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let Some(text) = value.string_value() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "selected_mode",
                    expected: JsonFieldType::String,
                    actual: value.kind(),
                },
            ),
        ));
    };
    MachineTheoremMode::parse(text).map(Some).ok_or_else(|| {
        premise_index_error(
            path,
            MachinePremiseIndexErrorReason::InvalidEnum {
                field: "selected_mode",
                value: text.to_owned(),
            },
        )
    })
}

fn parse_type_aware_argument_source_array(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachineTypeAwareArgumentSource>, MachinePremiseIndexError> {
    let Some(elements) = value.array_elements() else {
        return Err(premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "generated_argument_sources",
                    expected: JsonFieldType::Array,
                    actual: value.kind(),
                },
            ),
        ));
    };
    let mut sources = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let Some(text) = item.string_value() else {
            return Err(premise_index_error(
                &item_path,
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::TypeMismatch {
                        field: "generated_argument_sources",
                        expected: JsonFieldType::String,
                        actual: item.kind(),
                    },
                ),
            ));
        };
        let Some(source) = MachineTypeAwareArgumentSource::parse(text) else {
            return Err(premise_index_error(
                &item_path,
                MachinePremiseIndexErrorReason::InvalidEnum {
                    field: "generated_argument_sources",
                    value: text.to_owned(),
                },
            ));
        };
        sources.push(source);
    }
    Ok(sources)
}

fn validate_verified_premise_identity_parts(
    module: &Name,
    export_hash: &Hash,
    certificate_hash: &Hash,
    global_ref: &MachineVerifiedPremiseGlobalRef,
    decl_interface_hash: &Hash,
    axiom_summary: &MachineVerifiedPremiseAxiomSummary,
    path: &JsonPath,
) -> Result<(), MachinePremiseIndexError> {
    if module != &global_ref.module {
        return Err(premise_index_error(
            &path.field("module"),
            MachinePremiseIndexErrorReason::IdentityMismatch { field: "module" },
        ));
    }
    if export_hash != &global_ref.export_hash {
        return Err(premise_index_error(
            &path.field("export_hash"),
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "export_hash",
            },
        ));
    }
    if certificate_hash != &global_ref.certificate_hash {
        return Err(premise_index_error(
            &path.field("certificate_hash"),
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "certificate_hash",
            },
        ));
    }
    if decl_interface_hash != &global_ref.decl_interface_hash {
        return Err(premise_index_error(
            &path.field("decl_interface_hash"),
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "decl_interface_hash",
            },
        ));
    }
    if !machine_axiom_refs_are_canonical(&axiom_summary.direct_axioms) {
        return Err(premise_index_error(
            &path.field("axiom_summary").field("direct_axioms"),
            MachinePremiseIndexErrorReason::NonCanonicalAxiomRefs {
                field: "direct_axioms",
            },
        ));
    }
    if !machine_axiom_refs_are_canonical(&axiom_summary.transitive_axioms) {
        return Err(premise_index_error(
            &path.field("axiom_summary").field("transitive_axioms"),
            MachinePremiseIndexErrorReason::NonCanonicalAxiomRefs {
                field: "transitive_axioms",
            },
        ));
    }
    let expected_summary_hash = verified_premise_axiom_summary_hash(
        &axiom_summary.direct_axioms,
        &axiom_summary.transitive_axioms,
    );
    if expected_summary_hash != axiom_summary.summary_hash {
        return Err(premise_index_error(
            &path.field("axiom_summary").field("summary_hash"),
            MachinePremiseIndexErrorReason::AxiomSummaryHashMismatch,
        ));
    }
    Ok(())
}

fn verified_premise_identity_canonical_bytes(identity: &MachineVerifiedPremiseIdentity) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, VERIFIED_PREMISE_IDENTITY_SCHEMA_VERSION);
    encode_name(&mut out, &identity.module);
    out.extend(identity.export_hash);
    out.extend(identity.certificate_hash);
    encode_verified_premise_global_ref(&mut out, &identity.global_ref);
    out.extend(identity.decl_interface_hash);
    out.extend(identity.statement_core_hash);
    encode_verified_premise_axiom_summary(&mut out, &identity.axiom_summary);
    out
}

fn verified_premise_index_entry_stable_canonical_bytes(
    entry: &MachineVerifiedPremiseIndexEntry,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, PREMISE_INDEX_ENTRY_SCHEMA_VERSION);
    encode_string(&mut out, "verified");
    out.extend(entry.identity.canonical_bytes());
    out.extend(entry.statement_core_hash);
    out.extend(entry.structural_features.canonical_bytes());
    encode_list_len(&mut out, entry.modes.len());
    for mode in &entry.modes {
        encode_string(&mut out, mode.as_str());
    }
    encode_string(&mut out, entry.source.as_str());
    out
}

fn verified_premise_index_fingerprint(entries: &[MachineVerifiedPremiseIndexEntry]) -> Hash {
    let mut stable_entries = entries
        .iter()
        .map(MachineVerifiedPremiseIndexEntry::stable_canonical_bytes)
        .collect::<Vec<_>>();
    stable_entries.sort();
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.verified-premise-index.v1");
    encode_string(&mut out, PREMISE_INDEX_ENTRY_SCHEMA_VERSION);
    encode_list_len(&mut out, stable_entries.len());
    for entry in stable_entries {
        out.extend(entry);
    }
    sha256(&out)
}

#[allow(clippy::too_many_arguments)]
fn machine_premise_structural_features_hash(
    target_head: Option<&MachinePremiseStructuralRef>,
    pi_binder_count: u32,
    argument_universe_fingerprints: &[Hash],
    result_universe_fingerprint: &Hash,
    recursive_occurrences: &[MachinePremiseStructuralRef],
    equality_lhs_head: Option<&MachinePremiseStructuralRef>,
    equality_rhs_head: Option<&MachinePremiseStructuralRef>,
    propositional_connectives: &[MachinePremisePropositionalConnective],
    referenced_inductives: &[MachinePremiseStructuralRef],
    normalized_expression_fingerprints: &[Hash],
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.premise-structural-features.v1");
    encode_option_premise_structural_ref(&mut out, target_head);
    encode_uvar(&mut out, u64::from(pi_binder_count));
    encode_hash_list(&mut out, argument_universe_fingerprints);
    out.extend(result_universe_fingerprint);
    encode_premise_structural_ref_list(&mut out, recursive_occurrences);
    encode_option_premise_structural_ref(&mut out, equality_lhs_head);
    encode_option_premise_structural_ref(&mut out, equality_rhs_head);
    encode_list_len(&mut out, propositional_connectives.len());
    for connective in propositional_connectives {
        encode_string(&mut out, connective.as_str());
    }
    encode_premise_structural_ref_list(&mut out, referenced_inductives);
    encode_hash_list(&mut out, normalized_expression_fingerprints);
    sha256(&out)
}

fn machine_premise_structural_features_computed_hash(
    features: &MachinePremiseStructuralFeatures,
) -> Hash {
    machine_premise_structural_features_hash(
        features.target_head.as_ref(),
        features.pi_binder_count,
        &features.argument_universe_fingerprints,
        &features.result_universe_fingerprint,
        &features.recursive_occurrences,
        features.equality_lhs_head.as_ref(),
        features.equality_rhs_head.as_ref(),
        &features.propositional_connectives,
        &features.referenced_inductives,
        &features.normalized_expression_fingerprints,
    )
}

fn premise_set_features_from_structural_features(
    features: &MachinePremiseStructuralFeatures,
) -> BTreeSet<MachinePremiseSetFeature> {
    let mut out = BTreeSet::new();
    if let Some(reference) = &features.target_head {
        out.insert(premise_set_feature_from_structural_ref(
            MachinePremiseSetFeatureKind::TargetHead,
            reference,
        ));
    }
    for reference in &features.recursive_occurrences {
        out.insert(premise_set_feature_from_structural_ref(
            MachinePremiseSetFeatureKind::RecursiveOccurrence,
            reference,
        ));
    }
    if let Some(reference) = &features.equality_lhs_head {
        out.insert(premise_set_feature_from_structural_ref(
            MachinePremiseSetFeatureKind::EqualityLhsHead,
            reference,
        ));
    }
    if let Some(reference) = &features.equality_rhs_head {
        out.insert(premise_set_feature_from_structural_ref(
            MachinePremiseSetFeatureKind::EqualityRhsHead,
            reference,
        ));
    }
    for connective in &features.propositional_connectives {
        let mut bytes = Vec::new();
        encode_string(&mut bytes, connective.as_str());
        out.insert(premise_set_feature_from_bytes(
            MachinePremiseSetFeatureKind::PropositionalConnective,
            &bytes,
        ));
    }
    for reference in &features.referenced_inductives {
        out.insert(premise_set_feature_from_structural_ref(
            MachinePremiseSetFeatureKind::ReferencedInductive,
            reference,
        ));
    }
    for fingerprint in &features.normalized_expression_fingerprints {
        out.insert(premise_set_feature_from_hash(
            MachinePremiseSetFeatureKind::NormalizedExpression,
            fingerprint,
        ));
    }
    out
}

fn premise_set_feature_from_structural_ref(
    kind: MachinePremiseSetFeatureKind,
    reference: &MachinePremiseStructuralRef,
) -> MachinePremiseSetFeature {
    premise_set_feature_from_bytes(kind, &reference.canonical_bytes())
}

fn premise_set_feature_from_hash(
    kind: MachinePremiseSetFeatureKind,
    hash: &Hash,
) -> MachinePremiseSetFeature {
    premise_set_feature_from_bytes(kind, hash)
}

fn premise_set_feature_from_bytes(
    kind: MachinePremiseSetFeatureKind,
    bytes: &[u8],
) -> MachinePremiseSetFeature {
    let mut payload = Vec::new();
    encode_string(&mut payload, "npa.machine-api.premise-set-feature.v1");
    encode_string(&mut payload, kind.as_str());
    encode_uvar(&mut payload, bytes.len() as u64);
    payload.extend(bytes);
    MachinePremiseSetFeature {
        kind,
        feature_hash: sha256(&payload),
    }
}

fn machine_premise_structural_features_canonical_bytes(
    features: &MachinePremiseStructuralFeatures,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_option_premise_structural_ref(&mut out, features.target_head.as_ref());
    encode_uvar(&mut out, u64::from(features.pi_binder_count));
    encode_hash_list(&mut out, &features.argument_universe_fingerprints);
    out.extend(features.result_universe_fingerprint);
    encode_premise_structural_ref_list(&mut out, &features.recursive_occurrences);
    encode_option_premise_structural_ref(&mut out, features.equality_lhs_head.as_ref());
    encode_option_premise_structural_ref(&mut out, features.equality_rhs_head.as_ref());
    encode_list_len(&mut out, features.propositional_connectives.len());
    for connective in &features.propositional_connectives {
        encode_string(&mut out, connective.as_str());
    }
    encode_premise_structural_ref_list(&mut out, &features.referenced_inductives);
    encode_hash_list(&mut out, &features.normalized_expression_fingerprints);
    out.extend(features.feature_hash);
    out
}

fn machine_premise_structural_ref_canonical_bytes(
    reference: &MachinePremiseStructuralRef,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_premise_structural_ref(&mut out, reference);
    out
}

fn encode_option_premise_structural_ref(
    out: &mut Vec<u8>,
    reference: Option<&MachinePremiseStructuralRef>,
) {
    match reference {
        Some(reference) => {
            out.push(0x01);
            encode_premise_structural_ref(out, reference);
        }
        None => out.push(0x00),
    }
}

fn encode_premise_structural_ref_list(out: &mut Vec<u8>, refs: &[MachinePremiseStructuralRef]) {
    encode_list_len(out, refs.len());
    for reference in refs {
        encode_premise_structural_ref(out, reference);
    }
}

fn encode_premise_structural_ref(out: &mut Vec<u8>, reference: &MachinePremiseStructuralRef) {
    encode_name(out, &reference.module);
    encode_name(out, &reference.name);
    match reference.export_hash {
        Some(export_hash) => {
            out.push(0x01);
            out.extend(export_hash);
        }
        None => out.push(0x00),
    }
    out.extend(reference.decl_interface_hash);
}

fn encode_hash_list(out: &mut Vec<u8>, hashes: &[Hash]) {
    encode_list_len(out, hashes.len());
    for hash in hashes {
        out.extend(hash);
    }
}

fn verified_premise_axiom_summary_hash(
    direct_axioms: &[MachineAxiomRefWire],
    transitive_axioms: &[MachineAxiomRefWire],
) -> Hash {
    let mut out = Vec::new();
    encode_string(
        &mut out,
        "npa.machine-api.verified-premise-axiom-summary.v1",
    );
    encode_machine_axiom_ref_list(&mut out, direct_axioms);
    encode_machine_axiom_ref_list(&mut out, transitive_axioms);
    sha256(&out)
}

fn encode_verified_premise_global_ref(
    out: &mut Vec<u8>,
    global_ref: &MachineVerifiedPremiseGlobalRef,
) {
    encode_name(out, &global_ref.module);
    encode_name(out, &global_ref.name);
    out.extend(global_ref.export_hash);
    out.extend(global_ref.certificate_hash);
    out.extend(global_ref.decl_interface_hash);
}

fn encode_verified_premise_axiom_summary(
    out: &mut Vec<u8>,
    summary: &MachineVerifiedPremiseAxiomSummary,
) {
    encode_machine_axiom_ref_list(out, &summary.direct_axioms);
    encode_machine_axiom_ref_list(out, &summary.transitive_axioms);
    out.extend(summary.summary_hash);
}

fn encode_machine_axiom_ref_list(out: &mut Vec<u8>, axioms: &[MachineAxiomRefWire]) {
    encode_list_len(out, axioms.len());
    for axiom in axioms {
        out.extend(encode_machine_axiom_ref_wire(axiom));
    }
}

fn machine_axiom_refs_are_canonical(axioms: &[MachineAxiomRefWire]) -> bool {
    axioms.windows(2).all(|window| {
        encode_machine_axiom_ref_wire(&window[0]) < encode_machine_axiom_ref_wire(&window[1])
    })
}

fn premise_required_field<'value, 'src>(
    object: &ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value JsonValue<'src> {
    object
        .field(field)
        .expect("premise schema checked required field")
}

fn premise_required_string<'value, 'src>(
    object: &ValidatedObject<'value, 'src>,
    field: &'static str,
    path: &JsonPath,
) -> Result<&'value str, MachinePremiseIndexError> {
    premise_required_field(object, field)
        .string_value()
        .ok_or_else(|| {
            premise_index_error(
                &path.field(field),
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::TypeMismatch {
                        field,
                        expected: JsonFieldType::String,
                        actual: premise_required_field(object, field).kind(),
                    },
                ),
            )
        })
}

fn premise_required_module(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Name, MachinePremiseIndexError> {
    let text = premise_required_string(object, field, path)?;
    parse_module_name_wire(text).map_err(|_| {
        premise_index_error(path, MachinePremiseIndexErrorReason::InvalidName { field })
    })
}

fn premise_required_name(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Name, MachinePremiseIndexError> {
    let text = premise_required_string(object, field, path)?;
    parse_machine_api_name(text).map_err(|_| {
        premise_index_error(path, MachinePremiseIndexErrorReason::InvalidName { field })
    })
}

fn premise_required_hash(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Hash, MachinePremiseIndexError> {
    let text = premise_required_string(object, field, path)?;
    parse_hash_string(text).map_err(|_| {
        premise_index_error(path, MachinePremiseIndexErrorReason::InvalidHash { field })
    })
}

fn premise_required_nullable_hash(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Option<Hash>, MachinePremiseIndexError> {
    let value = premise_required_field(object, field);
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let text = value.string_value().ok_or_else(|| {
        premise_index_error(
            path,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::TypeMismatch {
                    field,
                    expected: JsonFieldType::String,
                    actual: value.kind(),
                },
            ),
        )
    })?;
    parse_hash_string(text).map(Some).map_err(|_| {
        premise_index_error(path, MachinePremiseIndexErrorReason::InvalidHash { field })
    })
}

fn premise_required_bool(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> bool {
    premise_required_field(object, field)
        .bool_value()
        .unwrap_or_else(|| panic!("premise index schema checked {field} bool at {path:?}"))
}

fn premise_required_u64(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<u64, MachinePremiseIndexError> {
    let raw = premise_required_field(object, field)
        .number_raw()
        .ok_or_else(|| {
            premise_index_error(
                path,
                MachinePremiseIndexErrorReason::Request(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiRequestErrorReason::TypeMismatch {
                        field,
                        expected: JsonFieldType::UnsignedInteger { max: u64::MAX },
                        actual: premise_required_field(object, field).kind(),
                    },
                ),
            )
        })?;
    parse_strict_u64_token(raw, u64::MAX).map_err(|_| {
        premise_index_error(
            path,
            MachinePremiseIndexErrorReason::InvalidEnum {
                field,
                value: raw.to_owned(),
            },
        )
    })
}

fn premise_required_u32(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<u32, MachinePremiseIndexError> {
    let value = premise_required_u64(object, field, path)?;
    u32::try_from(value).map_err(|_| {
        premise_index_error(
            path,
            MachinePremiseIndexErrorReason::InvalidEnum {
                field,
                value: value.to_string(),
            },
        )
    })
}

fn premise_index_error(
    path: &JsonPath,
    reason: MachinePremiseIndexErrorReason,
) -> MachinePremiseIndexError {
    MachinePremiseIndexError {
        path: json_path_display(path),
        reason,
    }
}

impl From<MachineApiRequestError> for MachinePremiseIndexError {
    fn from(error: MachineApiRequestError) -> Self {
        let path = json_path_display(&error.path);
        let kind = error.kind;
        let reason = error.reason;
        Self {
            path,
            reason: MachinePremiseIndexErrorReason::Request(kind, reason),
        }
    }
}

fn json_object_in_order(fields: Vec<(&str, String)>) -> String {
    let mut out = String::new();
    out.push('{');
    for (index, (key, value)) in fields.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(key));
        out.push(':');
        out.push_str(value);
    }
    out.push('}');
    out
}

fn json_array(values: Vec<String>) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(value);
    }
    out.push(']');
    out
}

fn hash_json(hash: &Hash) -> String {
    json_string(&format_hash_string(hash))
}

fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str("\\u00");
                out.push(json_hex_digit((ch as u8) >> 4));
                out.push(json_hex_digit((ch as u8) & 0x0f));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn json_hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex digit out of range"),
    }
}

fn build_theorem_index(
    session: &MachineProofSession,
    state: &npa_tactic::MachineProofState,
) -> Result<TheoremIndex, TheoremSearchBuildError> {
    let mut entries = Vec::new();
    let mut public_names = BTreeSet::new();
    let eq_head = resolved_eq_head(session, state)?;
    let eq_structural_head = eq_head
        .as_ref()
        .map(machine_premise_structural_ref_from_global_ref_view);
    for import in session.import_certificate_context.direct_import_entries() {
        let kernel_decls = npa_cert::verified_module_to_kernel_decls(&import.verified_module)
            .map_err(|_| TheoremSearchBuildError::InvalidVerifiedImport)?;
        let kernel_decls_by_name = kernel_decls
            .iter()
            .map(|decl| (decl.name().to_owned(), decl))
            .collect::<BTreeMap<_, _>>();
        for export in &import.export_block {
            if !matches!(export.kind, ExportKind::Axiom | ExportKind::Theorem) {
                continue;
            }
            let name = export_name(import, export)?;
            if !public_names.insert(name.clone()) {
                return Err(TheoremSearchBuildError::DuplicatePublicName);
            }
            let universe_params = export_universe_params(import, export)?;
            let statement_type = kernel_decls_by_name
                .get(&name.as_dotted())
                .ok_or(TheoremSearchBuildError::MissingKernelDecl)?
                .ty()
                .clone();
            let head = theorem_statement_head(session, import, export.ty)?;
            let statement_display_scope =
                theorem_statement_display_scope(session, import, export.ty)?;
            let mut modes = vec![MachineTheoremMode::Exact];
            if has_leading_pi(&statement_type) {
                modes.push(MachineTheoremMode::Apply);
            }
            if eq_head
                .as_ref()
                .zip(head.as_ref())
                .is_some_and(|(eq_head, head)| eq_head.canonical_bytes() == head.canonical_bytes())
            {
                modes.push(MachineTheoremMode::Rw);
            }
            if has_matching_imported_simp_rule(state, &name, &export.decl_interface_hash) {
                modes.push(MachineTheoremMode::Simp);
            }

            let mut axioms_used = export
                .axiom_dependencies
                .iter()
                .map(|axiom| {
                    imported_axiom_ref_to_wire(
                        0,
                        &session.import_certificate_context,
                        import,
                        axiom,
                    )
                    .map_err(|_| TheoremSearchBuildError::InvalidAxiomRef)
                })
                .collect::<Result<Vec<_>, _>>()?;
            sort_dedup_axiom_refs(&mut axioms_used);
            let axiom_dependencies_hash = axiom_dependencies_hash(&export.axiom_dependencies);
            let global_ref = MachineTheoremGlobalRef {
                module: import.key.module.clone(),
                name,
                export_hash: import.key.export_hash,
                decl_interface_hash: export.decl_interface_hash,
            };
            let structural_features = extract_direct_premise_structural_features(
                session,
                &statement_type,
                export.type_hash,
                &statement_display_scope,
                eq_structural_head.as_ref(),
                &machine_premise_structural_ref_from_theorem_global_ref(&global_ref),
            );
            let canonical_bytes = theorem_index_entry_canonical_bytes(
                &global_ref,
                export.kind,
                &universe_params,
                export.type_hash,
                head.as_ref(),
                axiom_dependencies_hash,
                &modes,
            );
            entries.push(TheoremIndexEntry {
                global_ref,
                export_kind: export.kind,
                certificate_hash: import.key.certificate_hash,
                universe_params,
                statement_type,
                statement_display_scope,
                statement_core_hash: export.type_hash,
                head,
                structural_features,
                axioms_used,
                modes,
                canonical_bytes,
            });
        }
    }
    entries.sort_by_key(theorem_entry_sort_key);
    let fingerprint = theorem_index_fingerprint(session, &entries);
    Ok(TheoremIndex {
        entries,
        fingerprint,
    })
}

fn suggested_candidates_for_entry(
    entry: &TheoremIndexEntry,
    request_modes: &[MachineTheoremMode],
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
) -> Result<Vec<MachineSuggestedCandidate>, TheoremSearchBuildError> {
    if !entry.universe_params.is_empty() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    for mode in canonical_mode_intersection(request_modes, &entry.modes) {
        match mode {
            MachineTheoremMode::Exact
            | MachineTheoremMode::Apply
            | MachineTheoremMode::ConstructorSupport
            | MachineTheoremMode::InductionSupport
            | MachineTheoremMode::TypeAware
            | MachineTheoremMode::Lexical
            | MachineTheoremMode::GraphAware
            | MachineTheoremMode::Embedding
            | MachineTheoremMode::ProofAnalogy
            | MachineTheoremMode::PremiseSet => {}
            MachineTheoremMode::Rw => {
                if let Some(rule) = first_matching_simp_rule(
                    state,
                    &entry.global_ref.name,
                    &entry.global_ref.decl_interface_hash,
                    Some(RewriteDirection::Forward),
                ) {
                    let candidate = MachineTacticCandidate::Rewrite {
                        rule: CandidateRewriteRuleRef {
                            head: premise_tactic_head(&entry.global_ref),
                            universe_args: Vec::new(),
                            args: rule
                                .rule_telescope
                                .iter()
                                .map(|_| CandidateApplyArg::InferFromTarget)
                                .collect(),
                        },
                        direction: RewriteDirection::Forward,
                        site: RewriteSite::EqTargetLeft,
                    };
                    if let Some(candidate) = validate_suggested_candidate(
                        state,
                        goal_id,
                        candidate,
                        Some(rule),
                        &entry.global_ref,
                    )? {
                        out.push(candidate);
                    }
                }
            }
            MachineTheoremMode::Simp => {
                if let Some(rule) = first_matching_simp_rule(
                    state,
                    &entry.global_ref.name,
                    &entry.global_ref.decl_interface_hash,
                    None,
                ) {
                    let candidate = MachineTacticCandidate::SimpLite {
                        rules: vec![rule.key.clone()],
                    };
                    if let Some(candidate) = validate_suggested_candidate(
                        state,
                        goal_id,
                        candidate,
                        Some(rule),
                        &entry.global_ref,
                    )? {
                        out.push(candidate);
                    }
                }
            }
        }
    }
    Ok(out)
}

#[derive(Clone, Copy)]
struct PremiseRankingContext<'a> {
    state: &'a npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    requested_modes: &'a [MachineTheoremMode],
    selected_modes: &'a [MachineTheoremMode],
    suggested_candidates: &'a [MachineSuggestedCandidate],
    allowed_axioms: Option<&'a [MachineAxiomRefWire]>,
    graph_snapshot_hash: Option<Hash>,
    source: MachinePremiseIndexSource,
    import_cost: u64,
}

fn type_aware_ranking_metadata_for_entry(
    base: &MachinePremiseRankingMetadata,
    entry: &TheoremIndexEntry,
    context: PremiseRankingContext<'_>,
) -> MachinePremiseRankingMetadata {
    let mut ranking = base.clone();
    let goal = context.state.goal(context.goal_id).ok();
    ranking.type_aware = goal
        .as_ref()
        .map(|goal| {
            type_aware_premise_metadata_for_goal(
                entry,
                context.state.env.kernel_env(),
                &context.state.root.universe_params,
                goal,
                context.selected_modes,
            )
        })
        .unwrap_or_else(MachineTypeAwarePremiseMetadata::not_evaluated);
    ranking.mode_metadata = premise_mode_metadata_for_entry(
        entry,
        context.requested_modes,
        &ranking.type_aware,
        context.suggested_candidates,
        goal.as_ref(),
        context.selected_modes,
    );
    let unresolved_premise_obligations =
        ranking.type_aware.unresolved_obligation_type_hashes.len() as u64;
    ranking.axiom_ranking = theorem_entry_axiom_ranking_metadata(
        entry,
        context.source,
        context.allowed_axioms,
        context.graph_snapshot_hash,
        context.import_cost,
        unresolved_premise_obligations,
    );
    ranking.score = ranking_score_after_axiom_penalties(&ranking.axiom_ranking);
    ranking
}

fn premise_mode_metadata_for_entry(
    entry: &TheoremIndexEntry,
    requested_modes: &[MachineTheoremMode],
    type_aware: &MachineTypeAwarePremiseMetadata,
    suggested_candidates: &[MachineSuggestedCandidate],
    goal: Option<&npa_tactic::MachineGoal>,
    selected_modes: &[MachineTheoremMode],
) -> Vec<MachinePremiseModeMetadata> {
    let lexical_score = goal
        .map(|goal| lexical_score_for_entry(entry, &goal.target))
        .unwrap_or(0);
    canonical_modes()
        .into_iter()
        .filter(|mode| requested_modes.contains(mode))
        .map(|mode| {
            premise_mode_metadata(
                entry,
                mode,
                type_aware,
                suggested_candidates,
                lexical_score,
                selected_modes.contains(&MachineTheoremMode::PremiseSet),
            )
        })
        .collect()
}

fn premise_mode_metadata(
    entry: &TheoremIndexEntry,
    mode: MachineTheoremMode,
    type_aware: &MachineTypeAwarePremiseMetadata,
    suggested_candidates: &[MachineSuggestedCandidate],
    lexical_score: u64,
    premise_set_selected: bool,
) -> MachinePremiseModeMetadata {
    let (status, reason) = match mode {
        MachineTheoremMode::Exact
        | MachineTheoremMode::Apply
        | MachineTheoremMode::Rw
        | MachineTheoremMode::Simp => {
            if entry.modes.contains(&mode) {
                (
                    MachinePremiseModeStatus::Supported,
                    MachinePremiseModeReason::EntryModeMatched,
                )
            } else {
                (
                    MachinePremiseModeStatus::Unavailable,
                    MachinePremiseModeReason::EntryModeNotApplicable,
                )
            }
        }
        MachineTheoremMode::ConstructorSupport | MachineTheoremMode::InductionSupport => {
            if entry_has_verified_inductive_metadata(entry) {
                (
                    MachinePremiseModeStatus::Supported,
                    MachinePremiseModeReason::VerifiedInductiveMetadata,
                )
            } else {
                (
                    MachinePremiseModeStatus::Unavailable,
                    MachinePremiseModeReason::NoVerifiedInductiveMetadata,
                )
            }
        }
        MachineTheoremMode::TypeAware => match type_aware.status {
            MachineTypeAwarePremiseStatus::Feasible => (
                MachinePremiseModeStatus::Supported,
                MachinePremiseModeReason::TypeAwareFeasible,
            ),
            MachineTypeAwarePremiseStatus::Infeasible => (
                MachinePremiseModeStatus::Supported,
                MachinePremiseModeReason::TypeAwareInfeasible,
            ),
            MachineTypeAwarePremiseStatus::NotEvaluated => (
                MachinePremiseModeStatus::Unavailable,
                MachinePremiseModeReason::TypeAwareNotEvaluated,
            ),
        },
        MachineTheoremMode::Lexical => {
            if lexical_score > 0 {
                (
                    MachinePremiseModeStatus::Supported,
                    MachinePremiseModeReason::LexicalSignal,
                )
            } else {
                (
                    MachinePremiseModeStatus::Supported,
                    MachinePremiseModeReason::LexicalNoSignal,
                )
            }
        }
        MachineTheoremMode::GraphAware
        | MachineTheoremMode::Embedding
        | MachineTheoremMode::ProofAnalogy => (
            MachinePremiseModeStatus::Unavailable,
            MachinePremiseModeReason::SidecarUnavailable,
        ),
        MachineTheoremMode::PremiseSet => {
            if premise_set_selected {
                (
                    MachinePremiseModeStatus::Supported,
                    MachinePremiseModeReason::PremiseSetSelected,
                )
            } else {
                (
                    MachinePremiseModeStatus::Unavailable,
                    MachinePremiseModeReason::PremiseSetNotSelected,
                )
            }
        }
    };
    MachinePremiseModeMetadata {
        mode,
        status,
        reason,
        suggested_candidate_count: suggested_candidate_count_for_mode(suggested_candidates, mode),
        lexical_score: if mode == MachineTheoremMode::Lexical {
            lexical_score
        } else {
            0
        },
    }
}

fn suggested_candidate_count_for_mode(
    suggested_candidates: &[MachineSuggestedCandidate],
    mode: MachineTheoremMode,
) -> u64 {
    suggested_candidates
        .iter()
        .filter(|candidate| {
            matches!(
                (&candidate.candidate, mode),
                (
                    MachineTacticCandidate::Rewrite { .. },
                    MachineTheoremMode::Rw
                ) | (
                    MachineTacticCandidate::SimpLite { .. },
                    MachineTheoremMode::Simp
                )
            )
        })
        .count() as u64
}

fn lexical_score_for_entry(entry: &TheoremIndexEntry, goal: &Expr) -> u64 {
    let entry_tokens = name_lexical_tokens(&entry.global_ref.name);
    let mut goal_tokens = BTreeSet::new();
    collect_expr_lexical_tokens(goal, &mut goal_tokens);
    entry_tokens
        .iter()
        .filter(|token| goal_tokens.contains(*token))
        .count() as u64
}

fn collect_expr_lexical_tokens(expr: &Expr, out: &mut BTreeSet<String>) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            extend_lexical_tokens(name, out);
        }
        Expr::App(fun, arg) => {
            collect_expr_lexical_tokens(fun, out);
            collect_expr_lexical_tokens(arg, out);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expr_lexical_tokens(ty, out);
            collect_expr_lexical_tokens(body, out);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expr_lexical_tokens(ty, out);
            collect_expr_lexical_tokens(value, out);
            collect_expr_lexical_tokens(body, out);
        }
    }
}

fn name_lexical_tokens(name: &Name) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for component in &name.0 {
        extend_lexical_tokens(component, &mut out);
    }
    out
}

fn extend_lexical_tokens(value: &str, out: &mut BTreeSet<String>) {
    for token in value
        .split(|ch: char| !ch.is_ascii_alphanumeric())
        .filter(|token| !token.is_empty())
    {
        out.insert(token.to_ascii_lowercase());
    }
}

fn type_aware_premise_metadata_for_goal(
    entry: &TheoremIndexEntry,
    env: &Env,
    root_universe_params: &[String],
    goal: &npa_tactic::MachineGoal,
    selected_modes: &[MachineTheoremMode],
) -> MachineTypeAwarePremiseMetadata {
    let ctx = machine_goal_kernel_context(goal);
    let goal_whnf = whnf_or_clone(env, &ctx, root_universe_params, &goal.target);
    let mut premise_current =
        whnf_or_clone(env, &ctx, &entry.universe_params, &entry.statement_type);
    let premise_size = expr_node_count(&entry.statement_type);
    let goal_size = expr_node_count(&goal.target);
    let universe_param_set = entry
        .universe_params
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let match_context = TypeAwareMatchContext {
        env,
        ctx: &ctx,
        root_universe_params,
        entry_universe_params: &entry.universe_params,
        universe_param_set: &universe_param_set,
    };
    let mut universe_bindings = BTreeMap::new();
    let mut universe_compatible = true;
    let mut pi_binder_count = 0u64;
    let mut unresolved_obligation_type_hashes = Vec::new();
    let mut local_context_match_type_hashes = Vec::new();
    let mut generated_argument_sources = Vec::new();

    while let Expr::Pi { ty, body, .. } = premise_current.clone() {
        pi_binder_count = pi_binder_count.saturating_add(1);
        let domain = whnf_or_clone(env, &ctx, &entry.universe_params, ty.as_ref());
        match first_matching_local_context_index(
            &match_context,
            &mut universe_bindings,
            &goal.context,
            &domain,
        ) {
            Some(index) => {
                local_context_match_type_hashes.push(npa_cert::core_expr_hash(&domain));
                generated_argument_sources.push(MachineTypeAwareArgumentSource::LocalContext);
                let arg = local_context_bvar(goal.context.len(), index);
                premise_current =
                    instantiate(body.as_ref(), &arg).unwrap_or_else(|_| body.as_ref().clone());
            }
            None => {
                unresolved_obligation_type_hashes.push(npa_cert::core_expr_hash(&domain));
                if expr_contains_bvar(body.as_ref(), 0) {
                    premise_current = body.as_ref().clone();
                } else {
                    premise_current = instantiate(body.as_ref(), &Expr::bvar(0))
                        .unwrap_or_else(|_| body.as_ref().clone());
                }
            }
        }
        premise_current = whnf_or_clone(env, &ctx, &entry.universe_params, &premise_current);
    }

    let compatibility = type_aware_expr_compatibility(
        &match_context,
        &mut universe_bindings,
        &premise_current,
        &goal_whnf,
    );
    universe_compatible &= compatibility.universe_compatible;
    let rewrite_feasible = type_aware_rewrite_feasible(entry, &goal.target);
    let result_fits_goal = compatibility.shape_compatible && compatibility.universe_compatible;
    let head_compatible = result_fits_goal
        || compatibility.head_compatible
        || (rewrite_feasible && type_aware_goal_accepts_rewrite(entry, &goal.target));
    if result_fits_goal {
        for _ in 0..universe_bindings.len() {
            generated_argument_sources.push(MachineTypeAwareArgumentSource::InferFromTarget);
        }
    }
    let selected_mode = type_aware_selected_mode(
        selected_modes,
        pi_binder_count,
        result_fits_goal,
        rewrite_feasible,
        universe_compatible,
    );
    let feasible =
        selected_mode.is_some() && universe_compatible && (result_fits_goal || rewrite_feasible);

    MachineTypeAwarePremiseMetadata {
        status: if feasible {
            MachineTypeAwarePremiseStatus::Feasible
        } else {
            MachineTypeAwarePremiseStatus::Infeasible
        },
        selected_mode,
        universe_compatible,
        head_compatible,
        result_fits_goal,
        pi_binder_count,
        estimated_new_goals: unresolved_obligation_type_hashes.len() as u64,
        unresolved_obligation_type_hashes,
        local_context_match_type_hashes,
        generated_argument_sources,
        premise_size,
        goal_size,
    }
}

fn machine_goal_kernel_context(goal: &npa_tactic::MachineGoal) -> Ctx {
    let mut ctx = Ctx::new();
    for local in &goal.context {
        match &local.value {
            Some(value) => ctx.push_definition(local.name.clone(), local.ty.clone(), value.clone()),
            None => ctx.push_assumption(local.name.clone(), local.ty.clone()),
        }
    }
    ctx
}

fn whnf_or_clone(env: &Env, ctx: &Ctx, delta: &[String], term: &Expr) -> Expr {
    env.whnf(ctx, delta, term).unwrap_or_else(|_| term.clone())
}

struct TypeAwareMatchContext<'a> {
    env: &'a Env,
    ctx: &'a Ctx,
    root_universe_params: &'a [String],
    entry_universe_params: &'a [String],
    universe_param_set: &'a BTreeSet<String>,
}

fn first_matching_local_context_index(
    match_context: &TypeAwareMatchContext<'_>,
    universe_bindings: &mut BTreeMap<String, Level>,
    locals: &[npa_tactic::MachineLocalDecl],
    domain: &Expr,
) -> Option<usize> {
    for (index, local) in locals.iter().enumerate() {
        let local_ty = whnf_or_clone(
            match_context.env,
            match_context.ctx,
            match_context.root_universe_params,
            &local.ty,
        );
        if match_context.entry_universe_params.is_empty()
            && match_context
                .env
                .is_defeq(
                    match_context.ctx,
                    match_context.root_universe_params,
                    domain,
                    &local_ty,
                )
                .unwrap_or(false)
        {
            return Some(index);
        }
        let mut candidate_bindings = universe_bindings.clone();
        let compatibility = structural_expr_compatibility(
            domain,
            &local_ty,
            match_context.universe_param_set,
            &mut candidate_bindings,
        );
        if compatibility.shape_compatible && compatibility.universe_compatible {
            *universe_bindings = candidate_bindings;
            return Some(index);
        }
    }
    None
}

fn local_context_bvar(local_count: usize, local_index: usize) -> Expr {
    Expr::bvar(local_count.saturating_sub(1).saturating_sub(local_index) as u32)
}

fn type_aware_expr_compatibility(
    match_context: &TypeAwareMatchContext<'_>,
    universe_bindings: &mut BTreeMap<String, Level>,
    premise: &Expr,
    goal: &Expr,
) -> TypeAwareExprCompatibility {
    if match_context.entry_universe_params.is_empty()
        && (quick_expr_equal_or_defeq(
            match_context.env,
            match_context.ctx,
            match_context.root_universe_params,
            premise,
            goal,
        ))
    {
        return TypeAwareExprCompatibility {
            shape_compatible: true,
            head_compatible: true,
            universe_compatible: true,
        };
    }
    structural_expr_compatibility(
        premise,
        goal,
        match_context.universe_param_set,
        universe_bindings,
    )
}

fn quick_expr_equal_or_defeq(
    env: &Env,
    ctx: &Ctx,
    delta: &[String],
    lhs: &Expr,
    rhs: &Expr,
) -> bool {
    npa_kernel::expr::quick_syntactic_eq(lhs, rhs)
        || env.is_defeq(ctx, delta, lhs, rhs).unwrap_or(false)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TypeAwareExprCompatibility {
    shape_compatible: bool,
    head_compatible: bool,
    universe_compatible: bool,
}

fn structural_expr_compatibility(
    premise: &Expr,
    goal: &Expr,
    universe_param_set: &BTreeSet<String>,
    universe_bindings: &mut BTreeMap<String, Level>,
) -> TypeAwareExprCompatibility {
    let head_compatible = expr_heads_compatible(
        premise,
        goal,
        universe_param_set,
        &mut universe_bindings.clone(),
    );
    let (shape_compatible, universe_compatible) =
        structural_expr_shape_and_universes(premise, goal, universe_param_set, universe_bindings);
    TypeAwareExprCompatibility {
        shape_compatible,
        head_compatible,
        universe_compatible,
    }
}

fn expr_heads_compatible(
    premise: &Expr,
    goal: &Expr,
    universe_param_set: &BTreeSet<String>,
    universe_bindings: &mut BTreeMap<String, Level>,
) -> bool {
    let (premise_head, _) = collect_apps(premise);
    let (goal_head, _) = collect_apps(goal);
    match (&premise_head, &goal_head) {
        (
            Expr::Const {
                name: lhs,
                levels: lhs_levels,
            },
            Expr::Const {
                name: rhs,
                levels: rhs_levels,
            },
        ) => {
            lhs == rhs
                && lhs_levels.len() == rhs_levels.len()
                && lhs_levels
                    .iter()
                    .zip(rhs_levels)
                    .all(|(lhs, rhs)| match_level(lhs, rhs, universe_param_set, universe_bindings))
        }
        (Expr::Sort(lhs), Expr::Sort(rhs)) => {
            match_level(lhs, rhs, universe_param_set, universe_bindings)
        }
        (Expr::BVar(lhs), Expr::BVar(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn structural_expr_shape_and_universes(
    premise: &Expr,
    goal: &Expr,
    universe_param_set: &BTreeSet<String>,
    universe_bindings: &mut BTreeMap<String, Level>,
) -> (bool, bool) {
    match (premise, goal) {
        (Expr::Sort(lhs), Expr::Sort(rhs)) => {
            let compatible = match_level(lhs, rhs, universe_param_set, universe_bindings);
            (true, compatible)
        }
        (Expr::BVar(lhs), Expr::BVar(rhs)) => (lhs == rhs, true),
        (
            Expr::Const {
                name: lhs_name,
                levels: lhs_levels,
            },
            Expr::Const {
                name: rhs_name,
                levels: rhs_levels,
            },
        ) => {
            if lhs_name != rhs_name || lhs_levels.len() != rhs_levels.len() {
                return (false, true);
            }
            let universe_compatible = lhs_levels
                .iter()
                .zip(rhs_levels)
                .all(|(lhs, rhs)| match_level(lhs, rhs, universe_param_set, universe_bindings));
            (true, universe_compatible)
        }
        (Expr::App(lhs_fun, lhs_arg), Expr::App(rhs_fun, rhs_arg)) => {
            let (fun_shape, fun_universe) = structural_expr_shape_and_universes(
                lhs_fun,
                rhs_fun,
                universe_param_set,
                universe_bindings,
            );
            let (arg_shape, arg_universe) = structural_expr_shape_and_universes(
                lhs_arg,
                rhs_arg,
                universe_param_set,
                universe_bindings,
            );
            (fun_shape && arg_shape, fun_universe && arg_universe)
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
            let (ty_shape, ty_universe) = structural_expr_shape_and_universes(
                lhs_ty,
                rhs_ty,
                universe_param_set,
                universe_bindings,
            );
            let (body_shape, body_universe) = structural_expr_shape_and_universes(
                lhs_body,
                rhs_body,
                universe_param_set,
                universe_bindings,
            );
            (ty_shape && body_shape, ty_universe && body_universe)
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
            let (ty_shape, ty_universe) = structural_expr_shape_and_universes(
                lhs_ty,
                rhs_ty,
                universe_param_set,
                universe_bindings,
            );
            let (value_shape, value_universe) = structural_expr_shape_and_universes(
                lhs_value,
                rhs_value,
                universe_param_set,
                universe_bindings,
            );
            let (body_shape, body_universe) = structural_expr_shape_and_universes(
                lhs_body,
                rhs_body,
                universe_param_set,
                universe_bindings,
            );
            (
                ty_shape && value_shape && body_shape,
                ty_universe && value_universe && body_universe,
            )
        }
        _ => (false, true),
    }
}

fn match_level(
    premise: &Level,
    goal: &Level,
    universe_param_set: &BTreeSet<String>,
    universe_bindings: &mut BTreeMap<String, Level>,
) -> bool {
    match premise {
        Level::Param(param) if universe_param_set.contains(param) => {
            if level_contains_param(goal, param)
                && !matches!(goal, Level::Param(goal_param) if goal_param == param)
            {
                return false;
            }
            match universe_bindings.get(param) {
                Some(bound) => bound == goal,
                None => {
                    universe_bindings.insert(param.clone(), goal.clone());
                    true
                }
            }
        }
        Level::Param(param) => matches!(goal, Level::Param(goal_param) if goal_param == param),
        Level::Zero => matches!(goal, Level::Zero),
        Level::Succ(lhs) => match goal {
            Level::Succ(rhs) => match_level(lhs, rhs, universe_param_set, universe_bindings),
            _ => false,
        },
        Level::Max(lhs_a, lhs_b) => match goal {
            Level::Max(rhs_a, rhs_b) => {
                match_level(lhs_a, rhs_a, universe_param_set, universe_bindings)
                    && match_level(lhs_b, rhs_b, universe_param_set, universe_bindings)
            }
            _ => false,
        },
        Level::IMax(lhs_a, lhs_b) => match goal {
            Level::IMax(rhs_a, rhs_b) => {
                match_level(lhs_a, rhs_a, universe_param_set, universe_bindings)
                    && match_level(lhs_b, rhs_b, universe_param_set, universe_bindings)
            }
            _ => false,
        },
    }
}

fn level_contains_param(level: &Level, param: &str) -> bool {
    match level {
        Level::Param(candidate) => candidate == param,
        Level::Zero => false,
        Level::Succ(inner) => level_contains_param(inner, param),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            level_contains_param(lhs, param) || level_contains_param(rhs, param)
        }
    }
}

fn type_aware_rewrite_feasible(entry: &TheoremIndexEntry, goal: &Expr) -> bool {
    (entry.structural_features.equality_lhs_head.is_some()
        || entry.structural_features.equality_rhs_head.is_some())
        && type_aware_goal_accepts_rewrite(entry, goal)
}

fn type_aware_goal_accepts_rewrite(entry: &TheoremIndexEntry, goal: &Expr) -> bool {
    let goal_refs = collect_expression_structural_refs(goal, &entry.statement_display_scope);
    entry
        .structural_features
        .equality_lhs_head
        .iter()
        .chain(entry.structural_features.equality_rhs_head.iter())
        .any(|side| goal_refs.iter().any(|goal_ref| goal_ref == side))
}

fn type_aware_selected_mode(
    selected_modes: &[MachineTheoremMode],
    pi_binder_count: u64,
    result_fits_goal: bool,
    rewrite_feasible: bool,
    universe_compatible: bool,
) -> Option<MachineTheoremMode> {
    if !universe_compatible {
        return None;
    }
    if rewrite_feasible {
        if selected_modes.contains(&MachineTheoremMode::Rw) {
            return Some(MachineTheoremMode::Rw);
        }
        if selected_modes.contains(&MachineTheoremMode::Simp) {
            return Some(MachineTheoremMode::Simp);
        }
        if selected_modes.contains(&MachineTheoremMode::TypeAware) {
            return Some(MachineTheoremMode::TypeAware);
        }
    }
    if result_fits_goal {
        if pi_binder_count == 0 && selected_modes.contains(&MachineTheoremMode::Exact) {
            return Some(MachineTheoremMode::Exact);
        }
        if selected_modes.contains(&MachineTheoremMode::Apply) {
            return Some(MachineTheoremMode::Apply);
        }
        if selected_modes.contains(&MachineTheoremMode::TypeAware) {
            return Some(MachineTheoremMode::TypeAware);
        }
    }
    None
}

fn expr_node_count(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => 1,
        Expr::App(fun, arg) => 1 + expr_node_count(fun) + expr_node_count(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            1 + expr_node_count(ty) + expr_node_count(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => 1 + expr_node_count(ty) + expr_node_count(value) + expr_node_count(body),
    }
}

fn validate_suggested_candidate(
    state: &npa_tactic::MachineProofState,
    goal_id: npa_tactic::GoalId,
    candidate: MachineTacticCandidate,
    rule: Option<&ResolvedSimpRule>,
    global_ref: &MachineTheoremGlobalRef,
) -> Result<Option<MachineSuggestedCandidate>, TheoremSearchBuildError> {
    if !candidate_head_and_rule_resolve(state, &candidate, rule, global_ref) {
        return Ok(None);
    }
    let validated = machine_tactic_validate_machine_tactic_candidate(goal_id, candidate.clone())
        .map_err(|_| TheoremSearchBuildError::SuggestedCandidateInvalid)?;
    Ok(Some(MachineSuggestedCandidate {
        status: MachineSuggestedCandidateStatus::Validated,
        candidate_hash: validated.candidate_hash,
        candidate,
    }))
}

fn candidate_head_and_rule_resolve(
    state: &npa_tactic::MachineProofState,
    candidate: &MachineTacticCandidate,
    rule: Option<&ResolvedSimpRule>,
    global_ref: &MachineTheoremGlobalRef,
) -> bool {
    match candidate {
        MachineTacticCandidate::Rewrite {
            rule: rewrite_rule,
            direction: RewriteDirection::Forward,
            site: RewriteSite::EqTargetLeft,
        } => {
            let Some(rule) = rule else {
                return false;
            };
            rewrite_rule.head == premise_tactic_head(global_ref)
                && rewrite_rule.universe_args.is_empty()
                && rewrite_rule.args.len() == rule.rule_telescope.len()
                && rewrite_rule
                    .args
                    .iter()
                    .all(|arg| matches!(arg, CandidateApplyArg::InferFromTarget))
                && matches_imported_simp_rule(
                    rule,
                    &global_ref.name,
                    &global_ref.decl_interface_hash,
                    Some(RewriteDirection::Forward),
                )
                && imported_head_resolves(state, &global_ref.name, &global_ref.decl_interface_hash)
        }
        MachineTacticCandidate::SimpLite { rules } => {
            let [candidate_rule] = rules.as_slice() else {
                return false;
            };
            state
                .env
                .simp_registry
                .rules
                .iter()
                .any(|resolved| resolved.key == *candidate_rule)
        }
        _ => false,
    }
}

fn render_statement(
    session: &MachineProofSession,
    entry: &TheoremIndexEntry,
) -> Result<MachineTheoremStatement, TheoremSearchBuildError> {
    let context = MachineExprRendererContext {
        display_scope: &entry.statement_display_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
        base_context: &[] as &[MachineLocalDecl],
        universe_params: &entry.universe_params,
    };
    let view = render_machine_expr_view(&entry.statement_type, &context)
        .map_err(|_| TheoremSearchBuildError::RenderFailed)?;
    Ok(MachineTheoremStatement {
        core_hash: entry.statement_core_hash,
        head: entry.head.clone(),
        machine: view.machine,
    })
}

fn theorem_entry_matches_query(
    entry: &TheoremIndexEntry,
    modes: &[MachineTheoremMode],
    filters: &MachineTheoremFilters,
) -> bool {
    theorem_entry_passes_filters(entry, filters)
        && entry.modes.iter().any(|mode| modes.contains(mode))
}

fn premise_entry_matches_query(
    entry: &TheoremIndexEntry,
    modes: &[MachineTheoremMode],
    filters: &MachineTheoremFilters,
) -> bool {
    theorem_entry_passes_filters(entry, filters)
        && modes
            .iter()
            .any(|mode| theorem_entry_supports_requested_mode(entry, *mode, false))
}

fn theorem_entry_passes_filters(
    entry: &TheoremIndexEntry,
    filters: &MachineTheoremFilters,
) -> bool {
    if filters.exclude_axioms
        && (entry.export_kind == ExportKind::Axiom || !entry.axioms_used.is_empty())
    {
        return false;
    }
    match &filters.allowed_modules {
        MachineAllowedModulesFilter::AllDirect => {}
        MachineAllowedModulesFilter::Explicit(modules) => {
            if !modules.contains(&entry.global_ref.module) {
                return false;
            }
        }
    }
    true
}

fn canonical_mode_intersection(
    lhs: &[MachineTheoremMode],
    rhs: &[MachineTheoremMode],
) -> Vec<MachineTheoremMode> {
    canonical_modes()
        .into_iter()
        .filter(|mode| lhs.contains(mode) && rhs.contains(mode))
        .collect()
}

fn selected_retrieval_modes_for_entry(
    entry: &TheoremIndexEntry,
    requested_modes: &[MachineTheoremMode],
    premise_set_selected: bool,
) -> Vec<MachineTheoremMode> {
    canonical_modes()
        .into_iter()
        .filter(|mode| {
            requested_modes.contains(mode)
                && theorem_entry_supports_requested_mode(entry, *mode, premise_set_selected)
        })
        .collect()
}

fn theorem_entry_supports_requested_mode(
    entry: &TheoremIndexEntry,
    mode: MachineTheoremMode,
    premise_set_selected: bool,
) -> bool {
    match mode {
        MachineTheoremMode::Exact
        | MachineTheoremMode::Apply
        | MachineTheoremMode::Rw
        | MachineTheoremMode::Simp => entry.modes.contains(&mode),
        MachineTheoremMode::ConstructorSupport | MachineTheoremMode::InductionSupport => {
            entry_has_verified_inductive_metadata(entry)
        }
        MachineTheoremMode::TypeAware | MachineTheoremMode::Lexical => true,
        MachineTheoremMode::GraphAware
        | MachineTheoremMode::Embedding
        | MachineTheoremMode::ProofAnalogy => false,
        MachineTheoremMode::PremiseSet => premise_set_selected,
    }
}

fn entry_has_verified_inductive_metadata(entry: &TheoremIndexEntry) -> bool {
    !entry.structural_features.referenced_inductives.is_empty()
}

fn first_matching_simp_rule<'a>(
    state: &'a npa_tactic::MachineProofState,
    name: &Name,
    decl_interface_hash: &Hash,
    direction: Option<RewriteDirection>,
) -> Option<&'a ResolvedSimpRule> {
    state
        .env
        .simp_registry
        .rules
        .iter()
        .filter(|rule| matches_imported_simp_rule(rule, name, decl_interface_hash, direction))
        .min_by_key(|rule| simp_rule_ref_canonical_bytes(&rule.key))
}

fn matches_imported_simp_rule(
    rule: &ResolvedSimpRule,
    name: &Name,
    decl_interface_hash: &Hash,
    direction: Option<RewriteDirection>,
) -> bool {
    matches!(
        &rule.source,
        TacticHead::Imported {
            name: source_name,
            decl_interface_hash: source_hash,
        } if source_name == name && source_hash == decl_interface_hash
    ) && direction.is_none_or(|direction| rule.key.direction == direction)
}

fn has_matching_imported_simp_rule(
    state: &npa_tactic::MachineProofState,
    name: &Name,
    decl_interface_hash: &Hash,
) -> bool {
    first_matching_simp_rule(state, name, decl_interface_hash, None).is_some()
}

fn imported_head_resolves(
    state: &npa_tactic::MachineProofState,
    name: &Name,
    decl_interface_hash: &Hash,
) -> bool {
    state
        .env
        .imports
        .iter()
        .flat_map(|import| import.exports())
        .filter(|export| export.name == *name && export.decl_interface_hash == *decl_interface_hash)
        .count()
        == 1
}

fn premise_tactic_head(global_ref: &MachineTheoremGlobalRef) -> TacticHead {
    TacticHead::Imported {
        name: global_ref.name.clone(),
        decl_interface_hash: global_ref.decl_interface_hash,
    }
}

fn resolved_eq_head(
    session: &MachineProofSession,
    state: &npa_tactic::MachineProofState,
) -> Result<Option<MachineGlobalRefView>, TheoremSearchBuildError> {
    let Some(eq_family) = state.env.options.eq_family.as_ref() else {
        return Ok(None);
    };
    let mut matches = session
        .import_certificate_context
        .direct_import_entries()
        .into_iter()
        .flat_map(|import| {
            import
                .export_block
                .iter()
                .filter(move |export| {
                    export.kind != ExportKind::Constructor
                        && export.kind != ExportKind::Recursor
                        && export.decl_interface_hash == eq_family.eq_interface_hash
                })
                .filter_map(move |export| {
                    export_name(import, export)
                        .ok()
                        .filter(|name| *name == eq_family.eq_name)
                        .map(|name| MachineGlobalRefView::Imported {
                            module: import.key.module.clone(),
                            name,
                            export_hash: import.key.export_hash,
                            decl_interface_hash: export.decl_interface_hash,
                            public_export: true,
                            tactic_head_visible: true,
                        })
                })
        })
        .collect::<Vec<_>>();
    Ok(match matches.len() {
        1 => matches.pop(),
        _ => None,
    })
}

fn theorem_statement_head(
    session: &MachineProofSession,
    owner: &VerifiedModuleContextEntry,
    ty: TermId,
) -> Result<Option<MachineGlobalRefView>, TheoremSearchBuildError> {
    let mut conclusion = ty;
    while let TermNode::Pi { body, .. } = term_node(owner, conclusion)? {
        conclusion = *body;
    }
    syntactic_term_head(owner, conclusion)?
        .map(|global_ref| normalized_global_ref_view(session, owner, &global_ref))
        .transpose()
}

fn syntactic_term_head(
    owner: &VerifiedModuleContextEntry,
    term: TermId,
) -> Result<Option<GlobalRef>, TheoremSearchBuildError> {
    let mut current = term;
    while let TermNode::App(func, _) = term_node(owner, current)? {
        current = *func;
    }
    Ok(match term_node(owner, current)? {
        TermNode::Const { global_ref, .. } => Some(global_ref.clone()),
        _ => None,
    })
}

fn theorem_statement_display_scope(
    session: &MachineProofSession,
    owner: &VerifiedModuleContextEntry,
    term: TermId,
) -> Result<MachineDisplayRenderScope, TheoremSearchBuildError> {
    let mut entries = session.machine_display_render_scope.entries().to_vec();
    let mut views_by_name = entries
        .iter()
        .map(|entry| (entry.name.as_dotted(), entry.view.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut visited = BTreeSet::new();
    collect_term_display_scope_entries(
        session,
        owner,
        term,
        &mut visited,
        &mut views_by_name,
        &mut entries,
    )?;
    MachineDisplayRenderScope::from_entries(entries)
        .map_err(|_| TheoremSearchBuildError::DisplayRefMismatch)
}

fn collect_term_display_scope_entries(
    session: &MachineProofSession,
    owner: &VerifiedModuleContextEntry,
    term: TermId,
    visited: &mut BTreeSet<TermId>,
    views_by_name: &mut BTreeMap<String, MachineGlobalRefView>,
    entries: &mut Vec<MachineDisplayRenderScopeEntry>,
) -> Result<(), TheoremSearchBuildError> {
    if !visited.insert(term) {
        return Ok(());
    }
    match term_node(owner, term)?.clone() {
        TermNode::Sort(_) | TermNode::BVar(_) => Ok(()),
        TermNode::Const { global_ref, .. } => {
            let view = normalized_global_ref_view(session, owner, &global_ref)?;
            push_statement_display_entry(owner, view, views_by_name, entries)
        }
        TermNode::App(func, arg) => {
            collect_term_display_scope_entries(
                session,
                owner,
                func,
                visited,
                views_by_name,
                entries,
            )?;
            collect_term_display_scope_entries(session, owner, arg, visited, views_by_name, entries)
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_term_display_scope_entries(
                session,
                owner,
                ty,
                visited,
                views_by_name,
                entries,
            )?;
            collect_term_display_scope_entries(
                session,
                owner,
                body,
                visited,
                views_by_name,
                entries,
            )
        }
        TermNode::Let { ty, value, body } => {
            collect_term_display_scope_entries(
                session,
                owner,
                ty,
                visited,
                views_by_name,
                entries,
            )?;
            collect_term_display_scope_entries(
                session,
                owner,
                value,
                visited,
                views_by_name,
                entries,
            )?;
            collect_term_display_scope_entries(
                session,
                owner,
                body,
                visited,
                views_by_name,
                entries,
            )
        }
    }
}

fn push_statement_display_entry(
    owner: &VerifiedModuleContextEntry,
    view: MachineGlobalRefView,
    views_by_name: &mut BTreeMap<String, MachineGlobalRefView>,
    entries: &mut Vec<MachineDisplayRenderScopeEntry>,
) -> Result<(), TheoremSearchBuildError> {
    let dotted = view.name().as_dotted();
    if let Some(existing) = views_by_name.get(&dotted) {
        if existing == &view {
            return Ok(());
        }
        return Err(TheoremSearchBuildError::DisplayRefMismatch);
    }

    let callable_ref = display_callable_ref_for_view(&view)?;
    let entry = MachineDisplayRenderScopeEntry::new(
        view.clone(),
        MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
            owner_module: owner.key.module.clone(),
            owner_export_hash: owner.key.export_hash,
        },
        callable_ref,
    );
    views_by_name.insert(dotted, view);
    entries.push(entry);
    Ok(())
}

fn display_callable_ref_for_view(
    view: &MachineGlobalRefView,
) -> Result<MachineSurfaceCallableRef, TheoremSearchBuildError> {
    match view {
        MachineGlobalRefView::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
            ..
        } => Ok(MachineSurfaceCallableRef::Imported {
            module: module.clone(),
            name: name.clone(),
            export_hash: *export_hash,
            decl_interface_hash: *decl_interface_hash,
        }),
        MachineGlobalRefView::LocalGenerated {
            module,
            export_hash: Some(export_hash),
            name,
            decl_interface_hash,
            ..
        } => Ok(MachineSurfaceCallableRef::Imported {
            module: module.clone(),
            name: name.clone(),
            export_hash: *export_hash,
            decl_interface_hash: *decl_interface_hash,
        }),
        MachineGlobalRefView::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
        } => Ok(MachineSurfaceCallableRef::CurrentModule {
            module: module.clone(),
            name: name.clone(),
            source_index: *source_index,
            decl_interface_hash: *decl_interface_hash,
        }),
        MachineGlobalRefView::LocalGenerated {
            export_hash: None, ..
        } => Err(TheoremSearchBuildError::DisplayRefMissing),
    }
}

fn normalized_global_ref_view(
    session: &MachineProofSession,
    owner: &VerifiedModuleContextEntry,
    global_ref: &GlobalRef,
) -> Result<MachineGlobalRefView, TheoremSearchBuildError> {
    match global_ref {
        GlobalRef::Local { decl_index } => {
            let decl = owner
                .decl_index_table
                .get(*decl_index)
                .ok_or(TheoremSearchBuildError::MissingDeclIndex)?;
            let public_export =
                ordinary_public_export(owner, &decl.name, &decl.hashes.decl_interface_hash)?
                    .is_some();
            let tactic_head_visible = public_export
                && direct_public_tactic_head_visible(
                    session,
                    &owner.key.module,
                    &decl.name,
                    &owner.key.export_hash,
                    &decl.hashes.decl_interface_hash,
                );
            Ok(MachineGlobalRefView::Imported {
                module: owner.key.module.clone(),
                name: decl.name.clone(),
                export_hash: owner.key.export_hash,
                decl_interface_hash: decl.hashes.decl_interface_hash,
                public_export,
                tactic_head_visible,
            })
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            let generated_name = name_from_owner(owner, *name)?;
            let generated = owner
                .generated_decl_table
                .iter()
                .find(|entry| {
                    entry.parent_decl_index == *decl_index && entry.name == generated_name
                })
                .ok_or(TheoremSearchBuildError::MissingGeneratedDecl)?;
            let parent = owner
                .decl_index_table
                .get(generated.parent_decl_index)
                .ok_or(TheoremSearchBuildError::MissingDeclIndex)?;
            let tactic_head_visible = direct_public_tactic_head_visible(
                session,
                &owner.key.module,
                &generated.name,
                &owner.key.export_hash,
                &generated.export.decl_interface_hash,
            );
            Ok(MachineGlobalRefView::LocalGenerated {
                module: owner.key.module.clone(),
                export_hash: Some(owner.key.export_hash),
                parent_name: parent.name.clone(),
                name: generated.name.clone(),
                parent_decl_interface_hash: parent.hashes.decl_interface_hash,
                decl_interface_hash: generated.export.decl_interface_hash,
                public_export: true,
                tactic_head_visible,
            })
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let key = owner
                .certificate_import_table
                .get(*import_index)
                .ok_or(TheoremSearchBuildError::MissingImportTableEntry)?;
            let imported = session
                .import_certificate_context
                .verified_modules()
                .iter()
                .find(|entry| &entry.key == key)
                .ok_or(TheoremSearchBuildError::MissingImportedModule)?;
            let imported_name = name_from_owner(owner, *name)?;
            imported_public_export_view(session, imported, &imported_name, decl_interface_hash)
        }
        GlobalRef::Builtin { .. } => Err(TheoremSearchBuildError::BuiltinGlobalRefUnsupported),
    }
}

fn imported_public_export_view(
    session: &MachineProofSession,
    import: &VerifiedModuleContextEntry,
    name: &Name,
    decl_interface_hash: &Hash,
) -> Result<MachineGlobalRefView, TheoremSearchBuildError> {
    let export = unique_public_export(import, name, decl_interface_hash)?
        .ok_or(TheoremSearchBuildError::MissingPublicExport)?;
    match export.kind {
        ExportKind::Constructor | ExportKind::Recursor => {
            let generated = import
                .generated_decl_table
                .iter()
                .find(|entry| {
                    entry.name == *name
                        && entry.export.kind == export.kind
                        && entry.export.decl_interface_hash == *decl_interface_hash
                })
                .ok_or(TheoremSearchBuildError::MissingGeneratedDecl)?;
            let parent = import
                .decl_index_table
                .get(generated.parent_decl_index)
                .ok_or(TheoremSearchBuildError::MissingDeclIndex)?;
            Ok(MachineGlobalRefView::LocalGenerated {
                module: import.key.module.clone(),
                export_hash: Some(import.key.export_hash),
                parent_name: parent.name.clone(),
                name: generated.name.clone(),
                parent_decl_interface_hash: parent.hashes.decl_interface_hash,
                decl_interface_hash: generated.export.decl_interface_hash,
                public_export: true,
                tactic_head_visible: direct_public_tactic_head_visible(
                    session,
                    &import.key.module,
                    &generated.name,
                    &import.key.export_hash,
                    &generated.export.decl_interface_hash,
                ),
            })
        }
        ExportKind::Axiom | ExportKind::Def | ExportKind::Theorem | ExportKind::Inductive => {
            Ok(MachineGlobalRefView::Imported {
                module: import.key.module.clone(),
                name: name.clone(),
                export_hash: import.key.export_hash,
                decl_interface_hash: *decl_interface_hash,
                public_export: true,
                tactic_head_visible: direct_public_tactic_head_visible(
                    session,
                    &import.key.module,
                    name,
                    &import.key.export_hash,
                    decl_interface_hash,
                ),
            })
        }
    }
}

fn ordinary_public_export<'a>(
    import: &'a VerifiedModuleContextEntry,
    name: &Name,
    decl_interface_hash: &Hash,
) -> Result<Option<&'a ExportEntry>, TheoremSearchBuildError> {
    let export = unique_public_export(import, name, decl_interface_hash)?;
    Ok(
        export
            .filter(|entry| !matches!(entry.kind, ExportKind::Constructor | ExportKind::Recursor)),
    )
}

fn unique_public_export<'a>(
    import: &'a VerifiedModuleContextEntry,
    name: &Name,
    decl_interface_hash: &Hash,
) -> Result<Option<&'a ExportEntry>, TheoremSearchBuildError> {
    let mut matches = import.export_block.iter().filter(|export| {
        export.decl_interface_hash == *decl_interface_hash
            && export_name(import, export).is_ok_and(|export_name| export_name == *name)
    });
    let first = matches.next();
    if matches.next().is_some() {
        return Err(TheoremSearchBuildError::DuplicatePublicName);
    }
    Ok(first)
}

fn direct_public_tactic_head_visible(
    session: &MachineProofSession,
    module: &Name,
    name: &Name,
    export_hash: &Hash,
    decl_interface_hash: &Hash,
) -> bool {
    session
        .import_certificate_context
        .direct_import_entries()
        .into_iter()
        .any(|entry| {
            entry.key.module == *module
                && entry.key.export_hash == *export_hash
                && unique_public_export(entry, name, decl_interface_hash)
                    .is_ok_and(|export| export.is_some())
        })
}

fn term_node(
    owner: &VerifiedModuleContextEntry,
    term: TermId,
) -> Result<&TermNode, TheoremSearchBuildError> {
    owner
        .verified_module
        .term_table()
        .get(term)
        .ok_or(TheoremSearchBuildError::MissingTerm)
}

fn name_from_owner(
    owner: &VerifiedModuleContextEntry,
    name: npa_cert::NameId,
) -> Result<Name, TheoremSearchBuildError> {
    owner
        .decoded_name_table
        .get(name)
        .cloned()
        .ok_or(TheoremSearchBuildError::MissingName)
}

fn has_leading_pi(expr: &Expr) -> bool {
    matches!(expr, Expr::Pi { .. })
}

fn extract_direct_premise_structural_features(
    session: &MachineProofSession,
    statement_type: &Expr,
    statement_core_hash: Hash,
    display_scope: &MachineDisplayRenderScope,
    eq_head: Option<&MachinePremiseStructuralRef>,
    own_ref: &MachinePremiseStructuralRef,
) -> MachinePremiseStructuralFeatures {
    let (argument_types, result_type) = split_pi_spine(statement_type);
    let pi_binder_count = argument_types.len().min(u32::MAX as usize) as u32;
    let argument_universe_fingerprints = argument_types
        .iter()
        .map(|expr| expression_universe_fingerprint(expr))
        .collect::<Vec<_>>();
    let result_universe_fingerprint = expression_universe_fingerprint(result_type);
    let target_head = expression_head_structural_ref(result_type, display_scope);
    let all_refs = collect_expression_structural_refs(statement_type, display_scope);
    let recursive_occurrences = all_refs
        .iter()
        .filter(|reference| *reference == own_ref)
        .cloned()
        .collect::<Vec<_>>();
    let referenced_inductives = all_refs
        .iter()
        .filter(|reference| {
            verified_export_kind_for_structural_ref(session, reference)
                == Some(ExportKind::Inductive)
        })
        .cloned()
        .collect::<Vec<_>>();
    let (equality_lhs_head, equality_rhs_head) =
        equality_side_heads(result_type, display_scope, eq_head);
    let propositional_connectives = expression_propositional_connectives(statement_type);
    let mut normalized_expression_fingerprints =
        Vec::with_capacity(argument_types.len().saturating_add(2));
    normalized_expression_fingerprints.push(statement_core_hash);
    normalized_expression_fingerprints.extend(
        argument_types
            .iter()
            .map(|expr| npa_cert::core_expr_hash(expr)),
    );
    normalized_expression_fingerprints.push(npa_cert::core_expr_hash(result_type));

    MachinePremiseStructuralFeatures::new(
        target_head,
        pi_binder_count,
        argument_universe_fingerprints,
        result_universe_fingerprint,
        recursive_occurrences,
        equality_lhs_head,
        equality_rhs_head,
        propositional_connectives,
        referenced_inductives,
        normalized_expression_fingerprints,
    )
}

fn package_theorem_index_structural_features(
    entry: &npa_package::PackageTheoremIndexEntry,
) -> MachinePremiseStructuralFeatures {
    let target_head = entry
        .statement
        .head
        .as_ref()
        .map(machine_premise_structural_ref_from_package_global_ref_view);
    let constants = entry
        .statement
        .constants
        .iter()
        .map(machine_premise_structural_ref_from_package_global_ref_view)
        .collect::<Vec<_>>();
    let own_ref = machine_premise_structural_ref_from_package_global_ref(&entry.global_ref);
    let recursive_occurrences = constants
        .iter()
        .filter(|reference| *reference == &own_ref)
        .cloned()
        .collect::<Vec<_>>();

    MachinePremiseStructuralFeatures::new(
        target_head,
        0,
        Vec::new(),
        empty_universe_fingerprint(),
        recursive_occurrences,
        None,
        None,
        Vec::new(),
        Vec::new(),
        vec![entry.statement.core_hash.into_bytes()],
    )
}

fn split_pi_spine(expr: &Expr) -> (Vec<&Expr>, &Expr) {
    let mut current = expr;
    let mut arguments = Vec::new();
    while let Expr::Pi { ty, body, .. } = current {
        arguments.push(ty.as_ref());
        current = body.as_ref();
    }
    (arguments, current)
}

fn equality_side_heads(
    expr: &Expr,
    display_scope: &MachineDisplayRenderScope,
    eq_head: Option<&MachinePremiseStructuralRef>,
) -> (
    Option<MachinePremiseStructuralRef>,
    Option<MachinePremiseStructuralRef>,
) {
    let Some(eq_head) = eq_head else {
        return (None, None);
    };
    let (head, args) = decompose_app(expr);
    let Some(head_ref) = expression_head_structural_ref(head, display_scope) else {
        return (None, None);
    };
    if &head_ref != eq_head || args.len() < 2 {
        return (None, None);
    }
    let lhs = args[args.len() - 2];
    let rhs = args[args.len() - 1];
    (
        expression_head_structural_ref(lhs, display_scope),
        expression_head_structural_ref(rhs, display_scope),
    )
}

fn expression_head_structural_ref(
    expr: &Expr,
    display_scope: &MachineDisplayRenderScope,
) -> Option<MachinePremiseStructuralRef> {
    let (head, _) = decompose_app(expr);
    let Expr::Const { name, .. } = head else {
        return None;
    };
    display_scope
        .entry_for_name(name)
        .map(|entry| machine_premise_structural_ref_from_global_ref_view(&entry.view))
}

fn collect_expression_structural_refs(
    expr: &Expr,
    display_scope: &MachineDisplayRenderScope,
) -> Vec<MachinePremiseStructuralRef> {
    let mut refs = Vec::new();
    collect_expression_structural_refs_into(expr, display_scope, &mut refs);
    refs.sort();
    refs.dedup();
    refs
}

fn collect_expression_structural_refs_into(
    expr: &Expr,
    display_scope: &MachineDisplayRenderScope,
    refs: &mut Vec<MachinePremiseStructuralRef>,
) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            if let Some(entry) = display_scope.entry_for_name(name) {
                refs.push(machine_premise_structural_ref_from_global_ref_view(
                    &entry.view,
                ));
            }
        }
        Expr::App(func, arg) => {
            collect_expression_structural_refs_into(func, display_scope, refs);
            collect_expression_structural_refs_into(arg, display_scope, refs);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expression_structural_refs_into(ty, display_scope, refs);
            collect_expression_structural_refs_into(body, display_scope, refs);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expression_structural_refs_into(ty, display_scope, refs);
            collect_expression_structural_refs_into(value, display_scope, refs);
            collect_expression_structural_refs_into(body, display_scope, refs);
        }
    }
}

fn expression_propositional_connectives(expr: &Expr) -> Vec<MachinePremisePropositionalConnective> {
    let mut out = Vec::new();
    collect_expression_propositional_connectives(expr, &mut out);
    out.sort();
    out.dedup();
    out
}

fn collect_expression_propositional_connectives(
    expr: &Expr,
    out: &mut Vec<MachinePremisePropositionalConnective>,
) {
    match expr {
        Expr::Sort(Level::Zero) => {
            out.push(MachinePremisePropositionalConnective::PropositionSort);
        }
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => {}
        Expr::App(func, arg) => {
            collect_expression_propositional_connectives(func, out);
            collect_expression_propositional_connectives(arg, out);
        }
        Expr::Lam { ty, body, .. } => {
            collect_expression_propositional_connectives(ty, out);
            collect_expression_propositional_connectives(body, out);
        }
        Expr::Pi { ty, body, .. } => {
            out.push(MachinePremisePropositionalConnective::Forall);
            if !expr_contains_bvar(body, 0) {
                out.push(MachinePremisePropositionalConnective::Implication);
            }
            collect_expression_propositional_connectives(ty, out);
            collect_expression_propositional_connectives(body, out);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expression_propositional_connectives(ty, out);
            collect_expression_propositional_connectives(value, out);
            collect_expression_propositional_connectives(body, out);
        }
    }
}

fn expr_contains_bvar(expr: &Expr, index: u32) -> bool {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => false,
        Expr::BVar(found) => *found == index,
        Expr::App(func, arg) => expr_contains_bvar(func, index) || expr_contains_bvar(arg, index),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_contains_bvar(ty, index) || expr_contains_bvar(body, index.saturating_add(1))
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_contains_bvar(ty, index)
                || expr_contains_bvar(value, index)
                || expr_contains_bvar(body, index.saturating_add(1))
        }
    }
}

fn expression_universe_fingerprint(expr: &Expr) -> Hash {
    let mut levels = Vec::new();
    collect_expression_level_bytes(expr, &mut levels);
    levels.sort();
    levels.dedup();
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.premise-expression-universes.v1");
    encode_list_len(&mut out, levels.len());
    for level in levels {
        encode_list_len(&mut out, level.len());
        out.extend(level);
    }
    sha256(&out)
}

fn empty_universe_fingerprint() -> Hash {
    expression_universe_fingerprint(&Expr::BVar(0))
}

fn collect_expression_level_bytes(expr: &Expr, out: &mut Vec<Vec<u8>>) {
    match expr {
        Expr::Sort(level) => out.push(level_canonical_bytes(level)),
        Expr::BVar(_) => {}
        Expr::Const { levels, .. } => {
            out.extend(levels.iter().map(level_canonical_bytes));
        }
        Expr::App(func, arg) => {
            collect_expression_level_bytes(func, out);
            collect_expression_level_bytes(arg, out);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expression_level_bytes(ty, out);
            collect_expression_level_bytes(body, out);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expression_level_bytes(ty, out);
            collect_expression_level_bytes(value, out);
            collect_expression_level_bytes(body, out);
        }
    }
}

fn level_canonical_bytes(level: &Level) -> Vec<u8> {
    let mut out = Vec::new();
    encode_level(&mut out, &npa_kernel::level::normalize_level(level.clone()));
    out
}

fn encode_level(out: &mut Vec<u8>, level: &Level) {
    match level {
        Level::Zero => out.push(0x00),
        Level::Succ(inner) => {
            out.push(0x01);
            encode_level(out, inner);
        }
        Level::Max(lhs, rhs) => {
            out.push(0x02);
            encode_level(out, lhs);
            encode_level(out, rhs);
        }
        Level::IMax(lhs, rhs) => {
            out.push(0x03);
            encode_level(out, lhs);
            encode_level(out, rhs);
        }
        Level::Param(name) => {
            out.push(0x04);
            encode_string(out, name);
        }
    }
}

fn decompose_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let Expr::App(func, arg) = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}

fn verified_export_kind_for_structural_ref(
    session: &MachineProofSession,
    reference: &MachinePremiseStructuralRef,
) -> Option<ExportKind> {
    session
        .import_certificate_context
        .verified_modules()
        .iter()
        .filter(|import| {
            import.key.module == reference.module
                && reference
                    .export_hash
                    .is_some_and(|export_hash| import.key.export_hash == export_hash)
        })
        .flat_map(|import| {
            import.export_block.iter().filter_map(move |export| {
                let name = export_name(import, export).ok()?;
                (name == reference.name
                    && export.decl_interface_hash == reference.decl_interface_hash)
                    .then_some(export.kind)
            })
        })
        .next()
}

fn machine_premise_structural_ref_from_theorem_global_ref(
    global_ref: &MachineTheoremGlobalRef,
) -> MachinePremiseStructuralRef {
    MachinePremiseStructuralRef {
        module: global_ref.module.clone(),
        name: global_ref.name.clone(),
        export_hash: Some(global_ref.export_hash),
        decl_interface_hash: global_ref.decl_interface_hash,
    }
}

fn machine_premise_structural_ref_from_global_ref_view(
    view: &MachineGlobalRefView,
) -> MachinePremiseStructuralRef {
    match view {
        MachineGlobalRefView::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
            ..
        } => MachinePremiseStructuralRef {
            module: module.clone(),
            name: name.clone(),
            export_hash: Some(*export_hash),
            decl_interface_hash: *decl_interface_hash,
        },
        MachineGlobalRefView::CurrentModule {
            module,
            name,
            decl_interface_hash,
            ..
        } => MachinePremiseStructuralRef {
            module: module.clone(),
            name: name.clone(),
            export_hash: None,
            decl_interface_hash: *decl_interface_hash,
        },
        MachineGlobalRefView::LocalGenerated {
            module,
            export_hash,
            name,
            decl_interface_hash,
            ..
        } => MachinePremiseStructuralRef {
            module: module.clone(),
            name: name.clone(),
            export_hash: *export_hash,
            decl_interface_hash: *decl_interface_hash,
        },
    }
}

fn machine_premise_structural_ref_from_package_global_ref(
    global_ref: &npa_package::PackageGlobalRef,
) -> MachinePremiseStructuralRef {
    MachinePremiseStructuralRef {
        module: global_ref.module.clone(),
        name: global_ref.name.clone(),
        export_hash: Some(global_ref.export_hash.into_bytes()),
        decl_interface_hash: global_ref.decl_interface_hash.into_bytes(),
    }
}

fn machine_premise_structural_ref_from_package_global_ref_view(
    view: &npa_package::PackageGlobalRefView,
) -> MachinePremiseStructuralRef {
    MachinePremiseStructuralRef {
        module: view.module.clone(),
        name: view.name.clone(),
        export_hash: Some(view.export_hash.into_bytes()),
        decl_interface_hash: view.decl_interface_hash.into_bytes(),
    }
}

fn export_name(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
) -> Result<Name, TheoremSearchBuildError> {
    import
        .decoded_name_table
        .get(export.name)
        .cloned()
        .ok_or(TheoremSearchBuildError::MissingName)
}

fn export_universe_params(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
) -> Result<Vec<String>, TheoremSearchBuildError> {
    export
        .universe_params
        .iter()
        .map(|name_id| {
            let name = import
                .decoded_name_table
                .get(*name_id)
                .ok_or(TheoremSearchBuildError::MissingName)?;
            let [component] = name.0.as_slice() else {
                return Err(TheoremSearchBuildError::InvalidUniverseParamName);
            };
            if crate::is_machine_universe_param_name(component) {
                Ok(component.clone())
            } else {
                Err(TheoremSearchBuildError::InvalidUniverseParamName)
            }
        })
        .collect()
}

pub(crate) fn parse_theorem_modes(
    value: &JsonValue<'_>,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<Vec<MachineTheoremMode>, MachineApiRequestError> {
    let elements = value.array_elements().ok_or_else(|| {
        request_error(
            error_kind,
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "modes",
                expected: JsonFieldType::Array,
                actual: value.kind(),
            },
        )
    })?;
    if elements.is_empty() {
        return Err(request_error(
            error_kind,
            path,
            MachineApiRequestErrorReason::MissingField { field: "modes" },
        ));
    }
    let mut seen = BTreeSet::new();
    let mut modes = Vec::new();
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let Some(text) = item.string_value() else {
            return Err(request_error(
                error_kind,
                &item_path,
                if item.kind() == JsonValueKind::Null {
                    MachineApiRequestErrorReason::NullField { field: "modes" }
                } else {
                    MachineApiRequestErrorReason::TypeMismatch {
                        field: "modes",
                        expected: JsonFieldType::String,
                        actual: item.kind(),
                    }
                },
            ));
        };
        let Some(mode) = MachineTheoremMode::parse(text) else {
            return Err(request_error(
                error_kind,
                &item_path,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "modes",
                    expected: JsonFieldType::String,
                    actual: JsonValueKind::String,
                },
            ));
        };
        if !seen.insert(mode) {
            return Err(request_error(
                error_kind,
                &item_path,
                MachineApiRequestErrorReason::DuplicateKey {
                    key: text.to_owned(),
                },
            ));
        }
        modes.push(mode);
    }
    modes.sort();
    Ok(modes)
}

pub(crate) fn parse_theorem_limit(
    value: &JsonValue<'_>,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<u32, MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Err(request_error(
            error_kind,
            path,
            MachineApiRequestErrorReason::NullField { field: "limit" },
        ));
    }
    let Some(raw) = value.number_raw() else {
        return Err(request_error(
            error_kind,
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "limit",
                expected: JsonFieldType::UnsignedInteger { max: 256 },
                actual: value.kind(),
            },
        ));
    };
    let parsed = parse_strict_u64_token(raw, 256)
        .and_then(|value| {
            if value >= 1 {
                Ok(value)
            } else {
                Err(StrictUnsignedIntegerError::InvalidGrammar)
            }
        })
        .map_err(|error| {
            request_error(
                error_kind,
                path,
                MachineApiRequestErrorReason::InvalidUnsignedInteger {
                    field: "limit",
                    raw: raw.to_owned(),
                    error,
                },
            )
        })?;
    Ok(parsed as u32)
}

pub(crate) fn parse_theorem_filters(
    value: &JsonValue<'_>,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<MachineTheoremFilters, MachineApiRequestError> {
    let object = validate_json_object(value, ObjectSchema::new(error_kind, FILTER_FIELDS), path)?;
    let exclude_axioms = object
        .field("exclude_axioms")
        .and_then(JsonValue::bool_value)
        .expect("filter schema checked exclude_axioms bool");
    let allowed_modules = match object.field("allowed_modules") {
        Some(value) => {
            let elements = value.array_elements().ok_or_else(|| {
                request_error(
                    error_kind,
                    &path.field("allowed_modules"),
                    MachineApiRequestErrorReason::TypeMismatch {
                        field: "allowed_modules",
                        expected: JsonFieldType::Array,
                        actual: value.kind(),
                    },
                )
            })?;
            let mut modules = Vec::with_capacity(elements.len());
            for (index, item) in elements.iter().enumerate() {
                let item_path = path.field("allowed_modules").index(index);
                let Some(text) = item.string_value() else {
                    return Err(request_error(
                        error_kind,
                        &item_path,
                        if item.kind() == JsonValueKind::Null {
                            MachineApiRequestErrorReason::NullField {
                                field: "allowed_modules",
                            }
                        } else {
                            MachineApiRequestErrorReason::TypeMismatch {
                                field: "allowed_modules",
                                expected: JsonFieldType::String,
                                actual: item.kind(),
                            }
                        },
                    ));
                };
                let module = parse_module_name_wire(text).map_err(|_| {
                    request_error(
                        error_kind,
                        &item_path,
                        MachineApiRequestErrorReason::TypeMismatch {
                            field: "allowed_modules",
                            expected: JsonFieldType::String,
                            actual: JsonValueKind::String,
                        },
                    )
                })?;
                modules.push(module);
            }
            modules
                .sort_by_key(|module| machine_api_name_canonical_bytes(module).unwrap_or_default());
            modules.dedup();
            MachineAllowedModulesFilter::Explicit(modules)
        }
        None => MachineAllowedModulesFilter::AllDirect,
    };
    Ok(MachineTheoremFilters {
        exclude_axioms,
        allowed_modules,
    })
}

fn parse_import_proposal_task_refs(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<String>, MachineApiRequestError> {
    let elements = value.array_elements().ok_or_else(|| {
        request_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "proposed_for_tasks",
                expected: JsonFieldType::Array,
                actual: value.kind(),
            },
        )
    })?;
    let mut tasks = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let Some(text) = item.string_value() else {
            return Err(request_error(
                MachineApiErrorKind::InvalidTheoremQuery,
                &item_path,
                if item.kind() == JsonValueKind::Null {
                    MachineApiRequestErrorReason::NullField {
                        field: "proposed_for_tasks",
                    }
                } else {
                    MachineApiRequestErrorReason::TypeMismatch {
                        field: "proposed_for_tasks",
                        expected: JsonFieldType::String,
                        actual: item.kind(),
                    }
                },
            ));
        };
        if text.is_empty() {
            return Err(request_error(
                MachineApiErrorKind::InvalidTheoremQuery,
                &item_path,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "proposed_for_tasks",
                    expected: JsonFieldType::String,
                    actual: JsonValueKind::String,
                },
            ));
        }
        tasks.push(text.to_owned());
    }
    tasks.sort();
    tasks.dedup();
    Ok(tasks)
}

fn parse_import_proposal_candidates(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachineImportProposalCandidate>, MachineApiRequestError> {
    let elements = value.array_elements().ok_or_else(|| {
        request_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "candidates",
                expected: JsonFieldType::Array,
                actual: value.kind(),
            },
        )
    })?;
    let mut candidates = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        candidates.push(parse_import_proposal_candidate(item, &path.index(index))?);
    }
    candidates.sort_by_key(machine_import_proposal_candidate_canonical_bytes);
    candidates.dedup_by(|lhs, rhs| {
        machine_import_proposal_candidate_canonical_bytes(lhs)
            == machine_import_proposal_candidate_canonical_bytes(rhs)
    });
    Ok(candidates)
}

fn parse_import_proposal_candidate(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineImportProposalCandidate, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidTheoremQuery,
            IMPORT_PROPOSAL_CANDIDATE_FIELDS,
        ),
        path,
    )?;
    let source_text = object
        .field("source")
        .and_then(JsonValue::string_value)
        .expect("import proposal candidate schema checked source string");
    let Some(source) = MachineImportProposalCandidateSource::parse(source_text) else {
        return Err(request_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            &path.field("source"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "source",
                expected: JsonFieldType::String,
                actual: JsonValueKind::String,
            },
        ));
    };
    let identity_value = object
        .field("identity")
        .expect("import proposal candidate schema checked identity object");
    let identity = parse_verified_premise_identity_value(identity_value, &path.field("identity"))
        .map_err(|_| {
        request_error(
            MachineApiErrorKind::InvalidTheoremQuery,
            &path.field("identity"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "identity",
                expected: JsonFieldType::Object,
                actual: identity_value.kind(),
            },
        )
    })?;
    Ok(MachineImportProposalCandidate { source, identity })
}

pub(crate) fn canonicalize_allowed_modules_for_session(
    session: &MachineProofSession,
    filters: &mut MachineTheoremFilters,
) -> Result<(), MachineAllowedModulesValidationError> {
    let mut direct_modules = session
        .import_certificate_context
        .direct_import_entries()
        .into_iter()
        .map(|entry| entry.key.module.clone())
        .collect::<Vec<_>>();
    direct_modules
        .sort_by_key(|module| machine_api_name_canonical_bytes(module).unwrap_or_default());
    direct_modules.dedup();

    if let MachineAllowedModulesFilter::Explicit(modules) = &mut filters.allowed_modules {
        for module in modules.iter() {
            if !direct_modules.contains(module) {
                return Err(MachineAllowedModulesValidationError {
                    module: module.clone(),
                });
            }
        }
        if *modules == direct_modules {
            filters.allowed_modules = MachineAllowedModulesFilter::AllDirect;
        }
    }
    Ok(())
}

fn required_field<'value, 'src>(
    envelope: &crate::MachineValidatedEndpointEnvelope<'value, 'src>,
    field: &str,
) -> &'value JsonValue<'src> {
    envelope
        .field(field)
        .expect("endpoint validation checked required field")
}

fn required_string<'value, 'src>(
    envelope: &crate::MachineValidatedEndpointEnvelope<'value, 'src>,
    field: &str,
) -> &'value str {
    required_field(envelope, field)
        .string_value()
        .expect("endpoint validation checked required string field")
}

fn optional_hash(
    envelope: &crate::MachineValidatedEndpointEnvelope<'_, '_>,
    field: &str,
) -> Option<Hash> {
    envelope.field(field).map(|value| {
        HashString::parse(
            value
                .string_value()
                .expect("endpoint validation checked optional hash string field"),
        )
        .expect("endpoint validation checked optional hash grammar")
        .digest()
    })
}

fn request_error(
    error_kind: MachineApiErrorKind,
    path: &JsonPath,
    reason: MachineApiRequestErrorReason,
) -> MachineApiRequestError {
    MachineApiRequestError::new(error_kind, path.clone(), reason)
}

fn theorem_index_fingerprint(session: &MachineProofSession, entries: &[TheoremIndexEntry]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.theorem-index.v1");
    encode_string(&mut out, session.protocol_version.as_str());
    out.extend(session.session_root_hash);
    encode_string(&mut out, THEOREM_INDEX_SCHEMA_VERSION);
    encode_list_len(&mut out, entries.len());
    for entry in entries {
        out.extend(&entry.canonical_bytes);
    }
    sha256(&out)
}

fn theorem_index_entry_canonical_bytes(
    global_ref: &MachineTheoremGlobalRef,
    export_kind: ExportKind,
    universe_params: &[String],
    statement_core_hash: Hash,
    head: Option<&MachineGlobalRefView>,
    axiom_dependencies_hash: Hash,
    modes: &[MachineTheoremMode],
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.theorem-index-entry.v1");
    encode_theorem_global_ref(&mut out, global_ref);
    encode_string(
        &mut out,
        match export_kind {
            ExportKind::Axiom => "axiom",
            ExportKind::Def => "def",
            ExportKind::Theorem => "theorem",
            ExportKind::Inductive => "inductive",
            ExportKind::Constructor => "constructor",
            ExportKind::Recursor => "recursor",
        },
    );
    encode_list_len(&mut out, universe_params.len());
    for param in universe_params {
        encode_string(&mut out, param);
    }
    out.extend(statement_core_hash);
    encode_option_global_ref_view(&mut out, head);
    out.extend(axiom_dependencies_hash);
    encode_list_len(&mut out, modes.len());
    for mode in modes {
        encode_string(&mut out, mode.as_str());
    }
    out
}

struct QueryFingerprintInput<'a> {
    protocol_version: MachineApiVersion,
    state_fingerprint: Hash,
    goal_id: npa_tactic::GoalId,
    goal_fingerprint: Hash,
    theorem_index_fingerprint: Hash,
    modes: &'a [MachineTheoremMode],
    filters: &'a MachineTheoremFilters,
    limit: u32,
}

struct PremiseQueryFingerprintInput<'a> {
    protocol_version: MachineApiVersion,
    state_fingerprint: Hash,
    goal_id: npa_tactic::GoalId,
    goal_fingerprint: Hash,
    goal_context_hash: Hash,
    local_name_map_hash: Hash,
    visible_imports_fingerprint: Hash,
    theorem_index_fingerprint: Hash,
    query_profile_hash: Hash,
    graph_snapshot_hash: Option<Hash>,
    modes: &'a [MachineTheoremMode],
    filters: &'a MachineTheoremFilters,
    limit: u32,
}

struct MachineRetrievalCacheKeyInput {
    environment_hash: Hash,
    goal_fingerprint: Hash,
    local_context_hash: Hash,
    query_fingerprint: Hash,
    query_profile_hash: Hash,
    theorem_index_fingerprint: Hash,
    graph_snapshot_hash: Option<Hash>,
    visible_imports_fingerprint: Hash,
}

fn theorem_query_fingerprint(input: QueryFingerprintInput<'_>) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.theorem-query.v1");
    encode_string(&mut out, input.protocol_version.as_str());
    out.extend(input.state_fingerprint);
    out.extend(npa_tactic::goal_id_canonical_bytes(input.goal_id));
    out.extend(input.goal_fingerprint);
    out.extend(input.theorem_index_fingerprint);
    encode_list_len(&mut out, input.modes.len());
    for mode in input.modes {
        encode_string(&mut out, mode.as_str());
    }
    encode_filters(&mut out, input.filters);
    encode_string(&mut out, SEARCH_PROFILE_VERSION);
    encode_string(&mut out, SUGGESTION_PROFILE_VERSION);
    encode_uvar(&mut out, u64::from(input.limit));
    sha256(&out)
}

fn premise_query_fingerprint(input: PremiseQueryFingerprintInput<'_>) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.premise-query.v1");
    encode_string(&mut out, input.protocol_version.as_str());
    out.extend(input.state_fingerprint);
    out.extend(npa_tactic::goal_id_canonical_bytes(input.goal_id));
    out.extend(input.goal_fingerprint);
    out.extend(input.goal_context_hash);
    out.extend(input.local_name_map_hash);
    out.extend(input.visible_imports_fingerprint);
    out.extend(input.theorem_index_fingerprint);
    out.extend(input.query_profile_hash);
    match input.graph_snapshot_hash {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
    encode_list_len(&mut out, input.modes.len());
    for mode in input.modes {
        encode_string(&mut out, mode.as_str());
    }
    encode_filters(&mut out, input.filters);
    encode_uvar(&mut out, u64::from(input.limit));
    sha256(&out)
}

fn premise_search_query_profile_hash(profile_version: &str) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.premise-query-profile.v1");
    encode_string(&mut out, profile_version);
    sha256(&out)
}

fn retrieval_local_context_hash(goal_context_hash: Hash, local_name_map_hash: Hash) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.retrieval-local-context.v1");
    out.extend(goal_context_hash);
    out.extend(local_name_map_hash);
    sha256(&out)
}

fn machine_retrieval_cache_key(input: MachineRetrievalCacheKeyInput) -> MachineRetrievalCacheKey {
    let mut key = MachineRetrievalCacheKey {
        key_hash: [0; 32],
        environment_hash: input.environment_hash,
        goal_fingerprint: input.goal_fingerprint,
        local_context_hash: input.local_context_hash,
        query_fingerprint: input.query_fingerprint,
        query_profile_hash: input.query_profile_hash,
        theorem_index_fingerprint: input.theorem_index_fingerprint,
        graph_snapshot_hash: input.graph_snapshot_hash,
        visible_imports_fingerprint: input.visible_imports_fingerprint,
    };
    key.key_hash = machine_retrieval_cache_key_hash(&key);
    key
}

fn machine_retrieval_cache_key_hash(key: &MachineRetrievalCacheKey) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.retrieval-cache-key.v1");
    out.extend(key.environment_hash);
    out.extend(key.goal_fingerprint);
    out.extend(key.local_context_hash);
    out.extend(key.query_fingerprint);
    out.extend(key.query_profile_hash);
    out.extend(key.theorem_index_fingerprint);
    match key.graph_snapshot_hash {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
    out.extend(key.visible_imports_fingerprint);
    sha256(&out)
}

fn machine_retrieval_cache_result_identities(
    results: &[MachinePremiseSearchResult],
) -> Vec<MachineRetrievalCacheResultIdentity> {
    results
        .iter()
        .map(|result| MachineRetrievalCacheResultIdentity {
            premise_id: result.premise_id.clone(),
            verified_identity: result.verified_identity.clone(),
            statement_core_hash: result.statement_core_hash,
            structural_features: result.structural_features.clone(),
            selected_modes: result.selected_modes.clone(),
        })
        .collect()
}

fn machine_retrieval_cache_ranking_payloads(
    results: &[MachinePremiseSearchResult],
) -> Vec<MachineRetrievalCacheRankingPayload> {
    results
        .iter()
        .map(|result| MachineRetrievalCacheRankingPayload {
            premise_id: result.premise_id.clone(),
            ranking_metadata: result.ranking_metadata.clone(),
            candidate_provenance: result.candidate_provenance.clone(),
            untrusted_sidecar: result.untrusted_sidecar.clone(),
        })
        .collect()
}

fn machine_retrieval_cache_sidecar_scores(
    search: &MachinePremiseSearchOkFields,
) -> Vec<MachineRetrievalCacheSidecarScore> {
    search
        .results
        .iter()
        .map(|result| MachineRetrievalCacheSidecarScore {
            premise_id: result.premise_id.clone(),
            score: result.ranking_metadata.score,
            graph_snapshot_hash: result
                .ranking_metadata
                .premise_set
                .as_ref()
                .and_then(|metadata| metadata.graph_snapshot_hash)
                .or(search.graph_snapshot_hash),
            suggested_candidate_count: result.candidate_provenance.suggested_candidate_count,
        })
        .collect()
}

fn import_proposal_query_fingerprint(
    protocol_version: MachineApiVersion,
    state_fingerprint: Hash,
    goal_id: npa_tactic::GoalId,
    goal_fingerprint: Hash,
    visible_imports_fingerprint: Hash,
    proposed_for_tasks: &[String],
    candidates: &[MachineImportProposalCandidate],
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.import-proposal-query.v1");
    encode_string(&mut out, protocol_version.as_str());
    out.extend(state_fingerprint);
    out.extend(npa_tactic::goal_id_canonical_bytes(goal_id));
    out.extend(goal_fingerprint);
    out.extend(visible_imports_fingerprint);
    encode_string(&mut out, IMPORT_PROPOSAL_SCHEMA_VERSION);
    encode_string_list(&mut out, proposed_for_tasks);
    encode_list_len(&mut out, candidates.len());
    for candidate in candidates {
        out.extend(machine_import_proposal_candidate_canonical_bytes(candidate));
    }
    sha256(&out)
}

fn visible_imports_fingerprint(session: &MachineProofSession) -> Hash {
    let mut entries = session.import_certificate_context.direct_import_entries();
    entries.sort_by_key(|entry| verified_import_entry_canonical_bytes(entry));
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.visible-imports.v1");
    encode_list_len(&mut out, entries.len());
    for entry in entries {
        out.extend(verified_import_entry_canonical_bytes(entry));
    }
    sha256(&out)
}

fn machine_import_proposal_hash(proposal: &MachineImportProposal) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, IMPORT_PROPOSAL_SCHEMA_VERSION);
    encode_import_proposal_import_identity(
        &mut out,
        &MachineImportProposalImportIdentity {
            module: proposal.module.clone(),
            export_hash: proposal.export_hash,
            certificate_hash: proposal.certificate_hash,
        },
    );
    encode_string_list(&mut out, &proposal.proposed_for_tasks);
    encode_verified_premise_axiom_summary(&mut out, &proposal.new_axiom_summary);
    encode_uvar(&mut out, u64::from(proposal.estimated_downstream_rebuild));
    encode_string(&mut out, proposal.reason.as_str());
    encode_string(&mut out, proposal.candidate_source.as_str());
    out.extend(proposal.candidate_identity.canonical_bytes());
    out.extend(proposal.visible_imports_fingerprint);
    encode_import_proposal_approval_hook(&mut out, &proposal.approval);
    sha256(&out)
}

fn import_proposal_rejection_hash(
    candidate: &MachineImportProposalCandidate,
    reason: MachineImportProposalRejectionReason,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.import-proposal-rejection.v1");
    out.extend(machine_import_proposal_candidate_canonical_bytes(candidate));
    encode_string(&mut out, reason.as_str());
    sha256(&out)
}

fn machine_import_proposal_canonical_bytes(proposal: &MachineImportProposal) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend(proposal.proposal_hash);
    encode_name(&mut out, &proposal.module);
    out.extend(proposal.export_hash);
    out.extend(proposal.certificate_hash);
    out
}

fn machine_import_proposal_rejection_canonical_bytes(
    rejection: &MachineImportProposalRejectedCandidate,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend(rejection.rejection_hash);
    out.extend(machine_import_proposal_candidate_identity_bytes(
        rejection.source,
        &rejection.identity,
    ));
    encode_string(&mut out, rejection.reason.as_str());
    out
}

fn machine_import_proposal_candidate_canonical_bytes(
    candidate: &MachineImportProposalCandidate,
) -> Vec<u8> {
    machine_import_proposal_candidate_identity_bytes(candidate.source, &candidate.identity)
}

fn machine_import_proposal_candidate_identity_bytes(
    source: MachineImportProposalCandidateSource,
    identity: &MachineVerifiedPremiseIdentity,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.import-proposal-candidate.v1");
    encode_string(&mut out, source.as_str());
    out.extend(identity.canonical_bytes());
    out
}

fn encode_import_proposal_approval_hook(
    out: &mut Vec<u8>,
    hook: &MachineImportProposalApprovalHook,
) {
    let current_session_id = hook.current_session_id.wire();
    encode_string(out, current_session_id);
    out.extend(hook.current_session_root_hash);
    encode_import_proposal_import_identity(out, &hook.required_direct_import);
    let current_snapshot_id = hook.current_snapshot_id.wire();
    encode_string(out, current_snapshot_id.as_str());
    out.extend(hook.current_state_fingerprint);
    encode_bool(out, hook.requires_new_snapshot);
    encode_bool(out, hook.requires_certificate_regeneration);
}

fn encode_import_proposal_import_identity(
    out: &mut Vec<u8>,
    import: &MachineImportProposalImportIdentity,
) {
    encode_name(out, &import.module);
    out.extend(import.export_hash);
    out.extend(import.certificate_hash);
}

fn encode_string_list(out: &mut Vec<u8>, values: &[String]) {
    encode_list_len(out, values.len());
    for value in values {
        encode_string(out, value);
    }
}

fn verified_import_entry_canonical_bytes(entry: &VerifiedModuleContextEntry) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, &entry.key.module);
    out.extend(entry.key.export_hash);
    out.extend(entry.key.certificate_hash);
    out.extend(sha256(&entry.certificate_bytes));
    out
}

fn verified_premise_entry_sort_key(entry: &MachineVerifiedPremiseIndexEntry) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, &entry.identity.global_ref.module);
    encode_name(&mut out, &entry.identity.global_ref.name);
    out.extend(entry.identity.global_ref.export_hash);
    out.extend(entry.identity.global_ref.decl_interface_hash);
    out
}

fn encode_filters(out: &mut Vec<u8>, filters: &MachineTheoremFilters) {
    encode_string(out, "npa.machine-api.theorem-filters.v1");
    encode_bool(out, filters.exclude_axioms);
    match &filters.allowed_modules {
        MachineAllowedModulesFilter::AllDirect => out.push(0x00),
        MachineAllowedModulesFilter::Explicit(modules) => {
            out.push(0x01);
            encode_list_len(out, modules.len());
            for module in modules {
                encode_name(out, module);
            }
        }
    }
}

fn encode_theorem_global_ref(out: &mut Vec<u8>, global_ref: &MachineTheoremGlobalRef) {
    encode_name(out, &global_ref.module);
    encode_name(out, &global_ref.name);
    out.extend(global_ref.export_hash);
    out.extend(global_ref.decl_interface_hash);
}

fn encode_option_global_ref_view(out: &mut Vec<u8>, value: Option<&MachineGlobalRefView>) {
    match value {
        Some(value) => {
            out.push(0x01);
            out.extend(value.canonical_bytes());
        }
        None => out.push(0x00),
    }
}

fn axiom_dependencies_hash(axioms: &[AxiomRef]) -> Hash {
    let mut ordered = axioms.to_vec();
    ordered.sort();
    let mut out = Vec::new();
    encode_list_len(&mut out, ordered.len());
    for axiom in &ordered {
        encode_global_ref(&mut out, &axiom.global_ref);
        encode_uvar(&mut out, axiom.name as u64);
        out.extend(axiom.decl_interface_hash);
    }
    sha256(&out)
}

fn sort_dedup_axiom_refs(entries: &mut Vec<MachineAxiomRefWire>) {
    entries.sort_by_key(encode_machine_axiom_ref_wire);
    entries.dedup_by(|lhs, rhs| {
        encode_machine_axiom_ref_wire(lhs) == encode_machine_axiom_ref_wire(rhs)
    });
}

fn theorem_entry_direct_axiom_refs(entry: &TheoremIndexEntry) -> Vec<MachineAxiomRefWire> {
    if entry.export_kind != ExportKind::Axiom {
        return Vec::new();
    }
    let mut direct = vec![MachineAxiomRefWire::Imported {
        module: entry.global_ref.module.clone(),
        name: entry.global_ref.name.clone(),
        export_hash: entry.global_ref.export_hash,
        decl_interface_hash: entry.global_ref.decl_interface_hash,
    }];
    sort_dedup_axiom_refs(&mut direct);
    direct
}

fn theorem_entry_transitive_axiom_refs(entry: &TheoremIndexEntry) -> Vec<MachineAxiomRefWire> {
    let direct_keys = theorem_entry_direct_axiom_refs(entry)
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<BTreeSet<_>>();
    let mut transitive = entry
        .axioms_used
        .iter()
        .filter(|axiom| !direct_keys.contains(&encode_machine_axiom_ref_wire(axiom)))
        .cloned()
        .collect::<Vec<_>>();
    sort_dedup_axiom_refs(&mut transitive);
    transitive
}

fn theorem_entry_all_axiom_refs(entry: &TheoremIndexEntry) -> Vec<MachineAxiomRefWire> {
    let mut axioms = theorem_entry_direct_axiom_refs(entry);
    axioms.extend(theorem_entry_transitive_axiom_refs(entry));
    sort_dedup_axiom_refs(&mut axioms);
    axioms
}

fn premise_axiom_paths_for_refs(
    direct_axioms: &[MachineAxiomRefWire],
    transitive_axioms: &[MachineAxiomRefWire],
    graph_snapshot_hash: Option<Hash>,
) -> Vec<MachinePremiseAxiomPath> {
    let mut paths = Vec::new();
    paths.extend(
        direct_axioms
            .iter()
            .cloned()
            .map(|axiom| MachinePremiseAxiomPath {
                source: MachinePremiseAxiomPathSource::DirectAxiomUse,
                axiom,
                path_length: 1,
                graph_snapshot_hash: None,
            }),
    );
    paths.extend(
        transitive_axioms
            .iter()
            .cloned()
            .map(|axiom| MachinePremiseAxiomPath {
                source: MachinePremiseAxiomPathSource::TransitiveDependency,
                axiom,
                path_length: 2,
                graph_snapshot_hash: None,
            }),
    );
    if let Some(graph_hash) = graph_snapshot_hash {
        paths.extend(
            direct_axioms
                .iter()
                .chain(transitive_axioms)
                .cloned()
                .map(|axiom| MachinePremiseAxiomPath {
                    source: MachinePremiseAxiomPathSource::GraphSnapshot,
                    axiom,
                    path_length: 2,
                    graph_snapshot_hash: Some(graph_hash),
                }),
        );
    }
    sort_dedup_premise_axiom_paths(&mut paths);
    paths
}

fn theorem_entry_axiom_paths(
    entry: &TheoremIndexEntry,
    graph_snapshot_hash: Option<Hash>,
) -> Vec<MachinePremiseAxiomPath> {
    premise_axiom_paths_for_refs(
        &theorem_entry_direct_axiom_refs(entry),
        &theorem_entry_transitive_axiom_refs(entry),
        graph_snapshot_hash,
    )
}

fn sort_dedup_premise_axiom_paths(paths: &mut Vec<MachinePremiseAxiomPath>) {
    paths.sort_by_key(machine_premise_axiom_path_sort_key);
    paths.dedup_by(|left, right| {
        machine_premise_axiom_path_sort_key(left) == machine_premise_axiom_path_sort_key(right)
    });
}

fn machine_premise_axiom_path_sort_key(path: &MachinePremiseAxiomPath) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, path.source.as_str());
    out.extend(encode_machine_axiom_ref_wire(&path.axiom));
    encode_uvar(&mut out, u64::from(path.path_length));
    match path.graph_snapshot_hash {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
    out
}

fn disallowed_axiom_count(
    axioms: &[MachineAxiomRefWire],
    allowed_axioms: Option<&[MachineAxiomRefWire]>,
) -> u32 {
    let Some(allowed_axioms) = allowed_axioms else {
        return 0;
    };
    let allowed = allowed_axioms
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<BTreeSet<_>>();
    axioms
        .iter()
        .filter(|axiom| !allowed.contains(&encode_machine_axiom_ref_wire(axiom)))
        .count()
        .min(u32::MAX as usize) as u32
}

#[allow(clippy::too_many_arguments)]
fn premise_axiom_ranking_metadata(
    theorem_level: MachinePremiseTheoremLevel,
    candidate_verified: bool,
    direct_axioms: &[MachineAxiomRefWire],
    transitive_axioms: &[MachineAxiomRefWire],
    axiom_paths: Vec<MachinePremiseAxiomPath>,
    disallowed_axiom_count: u32,
    import_cost: u64,
    unresolved_premise_obligations: u64,
) -> MachinePremiseAxiomRankingMetadata {
    let direct_axiom_count = direct_axioms.len().min(u32::MAX as usize) as u32;
    let transitive_axiom_count = transitive_axioms.len().min(u32::MAX as usize) as u32;
    let graph_axiom_path_count = axiom_paths
        .iter()
        .filter(|path| path.source == MachinePremiseAxiomPathSource::GraphSnapshot)
        .count() as u64;
    let mut penalties = MachinePremiseAxiomRankingPenalties {
        direct_axiom_use: u64::from(direct_axiom_count).saturating_mul(DIRECT_AXIOM_USE_PENALTY),
        transitive_axiom_expansion: u64::from(transitive_axiom_count)
            .saturating_mul(TRANSITIVE_AXIOM_EXPANSION_PENALTY),
        unknown_theorem_level: if theorem_level == MachinePremiseTheoremLevel::Unknown {
            UNKNOWN_THEOREM_LEVEL_PENALTY
        } else {
            0
        },
        unverified_candidate: if candidate_verified {
            0
        } else {
            UNVERIFIED_CANDIDATE_PENALTY
        },
        high_import_cost: import_cost.saturating_mul(HIGH_IMPORT_COST_UNIT_PENALTY),
        unresolved_premise_obligations: unresolved_premise_obligations
            .saturating_mul(UNRESOLVED_PREMISE_OBLIGATION_PENALTY),
        graph_axiom_path: graph_axiom_path_count.saturating_mul(GRAPH_AXIOM_PATH_PENALTY),
        disallowed_axiom: u64::from(disallowed_axiom_count)
            .saturating_mul(DISALLOWED_AXIOM_PENALTY),
        total: 0,
    };
    penalties.total = penalties
        .direct_axiom_use
        .saturating_add(penalties.transitive_axiom_expansion)
        .saturating_add(penalties.unknown_theorem_level)
        .saturating_add(penalties.unverified_candidate)
        .saturating_add(penalties.high_import_cost)
        .saturating_add(penalties.unresolved_premise_obligations)
        .saturating_add(penalties.graph_axiom_path)
        .saturating_add(penalties.disallowed_axiom);
    MachinePremiseAxiomRankingMetadata {
        theorem_level,
        candidate_verified,
        usable_under_axiom_policy: disallowed_axiom_count == 0,
        direct_axiom_count,
        transitive_axiom_count,
        disallowed_axiom_count,
        axiom_paths,
        penalties,
    }
}

fn ranking_score_after_axiom_penalties(axiom_ranking: &MachinePremiseAxiomRankingMetadata) -> u64 {
    PREMISE_RANKING_BASE_SCORE.saturating_sub(axiom_ranking.penalties.total)
}

fn theorem_entry_axiom_ranking_metadata(
    entry: &TheoremIndexEntry,
    source: MachinePremiseIndexSource,
    allowed_axioms: Option<&[MachineAxiomRefWire]>,
    graph_snapshot_hash: Option<Hash>,
    import_cost: u64,
    unresolved_premise_obligations: u64,
) -> MachinePremiseAxiomRankingMetadata {
    let direct_axioms = theorem_entry_direct_axiom_refs(entry);
    let transitive_axioms = theorem_entry_transitive_axiom_refs(entry);
    let mut all_axioms = direct_axioms.clone();
    all_axioms.extend(transitive_axioms.iter().cloned());
    sort_dedup_axiom_refs(&mut all_axioms);
    premise_axiom_ranking_metadata(
        match source {
            MachinePremiseIndexSource::DirectImport => {
                MachinePremiseTheoremLevel::VerifiedCertificate
            }
            MachinePremiseIndexSource::PackageTheoremIndex => MachinePremiseTheoremLevel::Unknown,
        },
        source == MachinePremiseIndexSource::DirectImport,
        &direct_axioms,
        &transitive_axioms,
        theorem_entry_axiom_paths(entry, graph_snapshot_hash),
        disallowed_axiom_count(&all_axioms, allowed_axioms),
        import_cost,
        unresolved_premise_obligations,
    )
}

fn package_projection_axiom_ranking_metadata(
    transitive_axioms: &[MachineAxiomRefWire],
) -> MachinePremiseAxiomRankingMetadata {
    premise_axiom_ranking_metadata(
        MachinePremiseTheoremLevel::Unknown,
        false,
        &[],
        transitive_axioms,
        premise_axiom_paths_for_refs(&[], transitive_axioms, None),
        0,
        1,
        0,
    )
}

fn theorem_entry_sort_key(entry: &TheoremIndexEntry) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, &entry.global_ref.module);
    encode_name(&mut out, &entry.global_ref.name);
    out.extend(entry.global_ref.export_hash);
    out.extend(entry.global_ref.decl_interface_hash);
    out
}

fn simp_rule_ref_canonical_bytes(rule: &SimpRuleRef) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, &rule.name);
    out.extend(rule.decl_interface_hash);
    out.push(match rule.direction {
        RewriteDirection::Forward => 0x00,
        RewriteDirection::Backward => 0x01,
    });
    out
}

fn canonical_modes() -> Vec<MachineTheoremMode> {
    vec![
        MachineTheoremMode::Exact,
        MachineTheoremMode::Apply,
        MachineTheoremMode::Rw,
        MachineTheoremMode::Simp,
        MachineTheoremMode::ConstructorSupport,
        MachineTheoremMode::InductionSupport,
        MachineTheoremMode::TypeAware,
        MachineTheoremMode::Lexical,
        MachineTheoremMode::GraphAware,
        MachineTheoremMode::Embedding,
        MachineTheoremMode::ProofAnalogy,
        MachineTheoremMode::PremiseSet,
    ]
}

fn encode_global_ref(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar(out, *import_index as u64);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar(out, *decl_index as u64);
            encode_uvar(out, *name as u64);
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
    }
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_list_len(out: &mut Vec<u8>, len: usize) {
    encode_uvar(out, len as u64);
}

fn encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(if value { 0x01 } else { 0x00 });
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TheoremSearchBuildError {
    InvalidVerifiedImport,
    DuplicatePublicName,
    MissingKernelDecl,
    MissingTerm,
    MissingName,
    MissingDeclIndex,
    MissingGeneratedDecl,
    MissingImportTableEntry,
    MissingImportedModule,
    MissingPublicExport,
    InvalidUniverseParamName,
    BuiltinGlobalRefUnsupported,
    DisplayRefMissing,
    DisplayRefMismatch,
    InvalidAxiomRef,
    RenderFailed,
    SuggestedCandidateInvalid,
    #[allow(dead_code)]
    PremiseIndexProjection,
}

fn search_request_error(error: MachineApiRequestError) -> Box<MachineTheoremSearchError> {
    search_plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
    )
}

fn search_snapshot_lookup_error(
    error: MachineSnapshotLookupError,
) -> Box<MachineTheoremSearchError> {
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
    search_plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
    )
}

fn search_theorem_index_error(error: TheoremSearchBuildError) -> Box<MachineTheoremSearchError> {
    search_plain_error(
        MachineApiErrorKind::InvalidTheoremIndex,
        MachineApiDiagnosticPhase::TheoremSearch,
        format!("theorem index construction failed: {error:?}"),
    )
}

fn search_plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachineTheoremSearchError> {
    search_error(kind, phase, None, message)
}

fn search_goal_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: npa_tactic::GoalId,
    message: impl Into<String>,
) -> Box<MachineTheoremSearchError> {
    search_error(kind, phase, Some(goal_id), message)
}

fn search_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<npa_tactic::GoalId>,
    message: impl Into<String>,
) -> Box<MachineTheoremSearchError> {
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
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(
            npa_tactic::MachineTacticDiagnostic::new(
                npa_tactic::MachineTacticDiagnosticKind::InvalidMachineProofState,
                message,
            ),
        ),
    };
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("search diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachineTheoremSearchError {
        diagnostic,
        response,
    })
}

fn premise_search_request_error(error: MachineApiRequestError) -> Box<MachinePremiseSearchError> {
    premise_search_plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
    )
}

fn premise_search_snapshot_lookup_error(
    error: MachineSnapshotLookupError,
) -> Box<MachinePremiseSearchError> {
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
    premise_search_plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
    )
}

fn premise_search_selection_error(
    error: MachinePremiseSearchSelectionError,
) -> Box<MachinePremiseSearchError> {
    match error {
        MachinePremiseSearchSelectionError::Build(error) => premise_search_plain_error(
            MachineApiErrorKind::InvalidTheoremIndex,
            MachineApiDiagnosticPhase::TheoremSearch,
            format!("theorem index construction failed: {error:?}"),
        ),
        MachinePremiseSearchSelectionError::TheoremIndexFingerprintMismatch {
            expected,
            actual,
        } => premise_search_plain_error(
            MachineApiErrorKind::TheoremIndexFingerprintMismatch,
            MachineApiDiagnosticPhase::RequestValidation,
            format!(
                "theorem index fingerprint mismatch: expected {}, actual {}",
                format_hash_string(&expected),
                format_hash_string(&actual)
            ),
        ),
    }
}

fn premise_search_plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachinePremiseSearchError> {
    premise_search_error(kind, phase, None, message)
}

fn premise_search_goal_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: npa_tactic::GoalId,
    message: impl Into<String>,
) -> Box<MachinePremiseSearchError> {
    premise_search_error(kind, phase, Some(goal_id), message)
}

fn premise_search_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<npa_tactic::GoalId>,
    message: impl Into<String>,
) -> Box<MachinePremiseSearchError> {
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
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(
            npa_tactic::MachineTacticDiagnostic::new(
                npa_tactic::MachineTacticDiagnosticKind::InvalidMachineProofState,
                message,
            ),
        ),
    };
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("premise search diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachinePremiseSearchError {
        diagnostic,
        response,
    })
}

fn import_proposal_request_error(error: MachineApiRequestError) -> Box<MachineImportProposalError> {
    import_proposal_plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
    )
}

fn import_proposal_snapshot_lookup_error(
    error: MachineSnapshotLookupError,
) -> Box<MachineImportProposalError> {
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
    import_proposal_plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
    )
}

fn import_proposal_plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachineImportProposalError> {
    import_proposal_error(kind, phase, None, message)
}

fn import_proposal_goal_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: npa_tactic::GoalId,
    message: impl Into<String>,
) -> Box<MachineImportProposalError> {
    import_proposal_error(kind, phase, Some(goal_id), message)
}

fn import_proposal_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<npa_tactic::GoalId>,
    message: impl Into<String>,
) -> Box<MachineImportProposalError> {
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
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(
            npa_tactic::MachineTacticDiagnostic::new(
                npa_tactic::MachineTacticDiagnosticKind::InvalidMachineProofState,
                message,
            ),
        ),
    };
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("import proposal diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachineImportProposalError {
        diagnostic,
        response,
    })
}

fn json_path_display(path: &JsonPath) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        create_machine_session, format_hash_string, project_import_certificate_context,
        run_machine_tactic_batch_request, run_machine_tactic_request,
        MachineApiResolvedDisplayCoreRefOwner, MachineDisplayRenderScope,
        MachineDisplayRenderScopeEntry, MachineTacticBatchItemResponse, MachineTacticRunResultKind,
        VerifiedImportKey, VerifiedModuleCertificateInput,
    };
    use npa_cert::{
        build_module_cert, encode_module_cert, verify_module_cert, AxiomPolicy, CoreModule,
        VerifiedModule, VerifierSession,
    };
    use npa_frontend::{MachineGlobalScopeEntry, MachineSurfaceCallableRef};
    use npa_kernel::{Binder, ConstructorDecl, Decl, InductiveDecl, Level, Reducibility};

    #[derive(Clone)]
    struct FixtureModule {
        verified: VerifiedModule,
        bytes: Vec<u8>,
    }

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn imported_axiom_type() -> Expr {
        Expr::pi("p", prop(), prop())
    }

    fn test_hash(seed: u8) -> Hash {
        [seed; 32]
    }

    fn test_package_hash(seed: u8) -> npa_package::PackageHash {
        npa_package::PackageHash::new(test_hash(seed))
    }

    fn test_imported_axiom(seed: u8) -> MachineAxiomRefWire {
        MachineAxiomRefWire::Imported {
            module: Name::from_dotted("Axiom.Mod"),
            name: Name::from_dotted("Axiom.Mod.ax"),
            export_hash: test_hash(seed),
            decl_interface_hash: test_hash(seed + 1),
        }
    }

    fn test_verified_premise_identity(
        name: &str,
        export_seed: u8,
        certificate_seed: u8,
        decl_seed: u8,
        statement_seed: u8,
    ) -> MachineVerifiedPremiseIdentity {
        let module = Name::from_dotted("Pkg.Mod");
        let export_hash = test_hash(export_seed);
        let certificate_hash = test_hash(certificate_seed);
        let decl_interface_hash = test_hash(decl_seed);
        let global_ref = MachineVerifiedPremiseGlobalRef {
            module: module.clone(),
            name: Name::from_dotted(name),
            export_hash,
            certificate_hash,
            decl_interface_hash,
        };
        MachineVerifiedPremiseIdentity::new(
            module,
            export_hash,
            certificate_hash,
            global_ref,
            decl_interface_hash,
            test_hash(statement_seed),
            MachineVerifiedPremiseAxiomSummary::new(
                vec![test_imported_axiom(60)],
                vec![test_imported_axiom(60), test_imported_axiom(62)],
            ),
        )
        .unwrap()
    }

    fn test_verified_premise_identity_with_axioms(
        name: &str,
        export_seed: u8,
        certificate_seed: u8,
        decl_seed: u8,
        statement_seed: u8,
        axioms: Vec<MachineAxiomRefWire>,
    ) -> MachineVerifiedPremiseIdentity {
        let module = Name::from_dotted("Eval.Mod");
        let export_hash = test_hash(export_seed);
        let certificate_hash = test_hash(certificate_seed);
        let decl_interface_hash = test_hash(decl_seed);
        let global_ref = MachineVerifiedPremiseGlobalRef {
            module: module.clone(),
            name: Name::from_dotted(name),
            export_hash,
            certificate_hash,
            decl_interface_hash,
        };
        MachineVerifiedPremiseIdentity::new(
            module,
            export_hash,
            certificate_hash,
            global_ref,
            decl_interface_hash,
            test_hash(statement_seed),
            MachineVerifiedPremiseAxiomSummary::new(Vec::new(), axioms),
        )
        .unwrap()
    }

    fn test_evaluation_identity(name: &str, seed: u8) -> MachineVerifiedPremiseIdentity {
        test_verified_premise_identity_with_axioms(
            name,
            seed,
            seed.wrapping_add(1),
            seed.wrapping_add(2),
            seed.wrapping_add(3),
            Vec::new(),
        )
    }

    fn test_retrieved_premise(
        identity: &MachineVerifiedPremiseIdentity,
        score: u64,
    ) -> MachineRetrievalEvaluationRetrievedPremise {
        MachineRetrievalEvaluationRetrievedPremise {
            identity: identity.clone(),
            ranking_score: score,
        }
    }

    fn test_evaluation_case(
        case_id: &str,
        expected_final_proof_premises: Vec<MachineVerifiedPremiseIdentity>,
        retrieved_premises: Vec<MachineRetrievalEvaluationRetrievedPremise>,
    ) -> MachineRetrievalEvaluationCase {
        MachineRetrievalEvaluationCase {
            case_id: case_id.to_owned(),
            goal_fingerprint: test_hash(210),
            local_context_hash: test_hash(211),
            expected_final_proof_premises,
            allowed_imports: Vec::new(),
            axiom_policy: MachineRetrievalEvaluationAxiomPolicy::new(Vec::new()),
            expected_theorem_index_fingerprint: test_hash(212),
            theorem_index_fingerprint: test_hash(212),
            graph_snapshot_hash: None,
            observed_graph_snapshot_hash: None,
            retrieved_premises,
            import_proposals_accepted: 0,
            import_proposals_rejected: 0,
            baseline_proof_completed: None,
            retrieval_proof_completed: None,
            latency_micros: 0,
            cache_hit: false,
            checker_disagreement: false,
        }
    }

    fn test_structural_ref(seed: u8) -> MachinePremiseStructuralRef {
        MachinePremiseStructuralRef {
            module: Name::from_dotted("Pkg.Mod"),
            name: Name::from_dotted("Pkg.Mod.head"),
            export_hash: Some(test_hash(seed)),
            decl_interface_hash: test_hash(seed + 1),
        }
    }

    fn test_structural_features(
        seed: u8,
        statement_hash: Hash,
    ) -> MachinePremiseStructuralFeatures {
        MachinePremiseStructuralFeatures::new(
            Some(test_structural_ref(seed)),
            1,
            vec![test_hash(seed + 10)],
            test_hash(seed + 11),
            vec![test_structural_ref(seed + 12)],
            Some(test_structural_ref(seed + 14)),
            Some(test_structural_ref(seed + 16)),
            vec![
                MachinePremisePropositionalConnective::Forall,
                MachinePremisePropositionalConnective::PropositionSort,
            ],
            vec![test_structural_ref(seed + 18)],
            vec![statement_hash, test_hash(seed + 21)],
        )
    }

    fn test_verified_premise_entry(score: u64) -> MachineVerifiedPremiseIndexEntry {
        let identity = test_verified_premise_identity("Pkg.Mod.same", 1, 2, 3, 4);
        MachineVerifiedPremiseIndexEntry::new(
            identity.clone(),
            identity.statement_core_hash,
            test_structural_features(70, identity.statement_core_hash),
            vec![MachineTheoremMode::Apply, MachineTheoremMode::Exact],
            MachinePremiseIndexSource::DirectImport,
            MachinePremiseRankingMetadata::score_only(score),
        )
        .unwrap()
    }

    fn test_type_aware_entry(
        statement_type: Expr,
        universe_params: Vec<String>,
        modes: Vec<MachineTheoremMode>,
    ) -> TheoremIndexEntry {
        let statement_core_hash = npa_cert::core_expr_hash(&statement_type);
        TheoremIndexEntry {
            global_ref: MachineTheoremGlobalRef {
                module: Name::from_dotted("Test"),
                name: Name::from_dotted("Test.premise"),
                export_hash: test_hash(120),
                decl_interface_hash: test_hash(121),
            },
            export_kind: ExportKind::Theorem,
            certificate_hash: test_hash(122),
            universe_params,
            statement_type,
            statement_display_scope: MachineDisplayRenderScope::empty(),
            statement_core_hash,
            head: None,
            structural_features: MachinePremiseStructuralFeatures::new(
                None,
                0,
                Vec::new(),
                empty_universe_fingerprint(),
                Vec::new(),
                None,
                None,
                Vec::new(),
                Vec::new(),
                vec![statement_core_hash],
            ),
            axioms_used: Vec::new(),
            modes,
            canonical_bytes: Vec::new(),
        }
    }

    fn test_premise_set_structural_features(
        fingerprints: Vec<Hash>,
    ) -> MachinePremiseStructuralFeatures {
        MachinePremiseStructuralFeatures::new(
            None,
            0,
            Vec::new(),
            empty_universe_fingerprint(),
            Vec::new(),
            None,
            None,
            Vec::new(),
            Vec::new(),
            fingerprints,
        )
    }

    fn test_premise_set_entry(
        name: &str,
        fingerprints: Vec<Hash>,
        axioms_used: Vec<MachineAxiomRefWire>,
    ) -> TheoremIndexEntry {
        let statement_type = prop();
        let statement_core_hash = npa_cert::core_expr_hash(&statement_type);
        let name_seed = name.bytes().fold(0u8, u8::wrapping_add);
        TheoremIndexEntry {
            global_ref: MachineTheoremGlobalRef {
                module: Name::from_dotted("Set.Premises"),
                name: Name::from_dotted(name),
                export_hash: test_hash(name_seed.wrapping_add(1)),
                decl_interface_hash: test_hash(name_seed.wrapping_add(2)),
            },
            export_kind: ExportKind::Theorem,
            certificate_hash: test_hash(name_seed.wrapping_add(3)),
            universe_params: Vec::new(),
            statement_type,
            statement_display_scope: MachineDisplayRenderScope::empty(),
            statement_core_hash,
            head: None,
            structural_features: test_premise_set_structural_features(fingerprints),
            axioms_used,
            modes: vec![MachineTheoremMode::Exact],
            canonical_bytes: Vec::new(),
        }
    }

    fn premise_set_goal_features(fingerprints: Vec<Hash>) -> BTreeSet<MachinePremiseSetFeature> {
        premise_set_features_from_structural_features(&test_premise_set_structural_features(
            fingerprints,
        ))
    }

    fn premise_set_candidates(
        entries: &[TheoremIndexEntry],
    ) -> Vec<MachinePremiseSetCandidate<'_>> {
        entries.iter().map(machine_premise_set_candidate).collect()
    }

    fn initial_machine_state(session: &MachineProofSession) -> npa_tactic::MachineProofState {
        let snapshot_context = MachineSnapshotMaterializationContext {
            session_id: &session.session_id,
            display_scope: &session.machine_display_render_scope,
            callable_interface_table: &session.machine_surface_callable_interface_table,
        };
        session
            .snapshots
            .lookup_checked(
                &snapshot_context,
                session.initial_snapshot.snapshot_id,
                session.initial_snapshot.state_fingerprint,
            )
            .unwrap()
            .executable_state_payload
            .clone()
    }

    fn type0_level() -> Level {
        npa_kernel::type0()
    }

    fn nat() -> Expr {
        npa_kernel::nat()
    }

    fn nat_zero() -> Expr {
        npa_kernel::nat_zero()
    }

    fn nat_succ(arg: Expr) -> Expr {
        npa_kernel::nat_succ(arg)
    }

    fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
        npa_kernel::eq(type0_level(), nat(), lhs, rhs)
    }

    fn eq_refl_nat(value: Expr) -> Expr {
        npa_kernel::eq_refl(type0_level(), nat(), value)
    }

    fn list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let list_a = |level: Level, a: Expr| Expr::app(Expr::konst("List", vec![level]), a);
        InductiveDecl::new(
            "List",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![
                ConstructorDecl::new(
                    "List.nil",
                    Expr::pi("A", Expr::sort(u.clone()), list_a(u.clone(), Expr::bvar(0))),
                ),
                ConstructorDecl::new(
                    "List.cons",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "x",
                            Expr::bvar(0),
                            Expr::pi(
                                "xs",
                                list_a(u.clone(), Expr::bvar(1)),
                                list_a(u.clone(), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            ],
            None,
        )
    }

    fn fixture_module(module: CoreModule, imports: &[VerifiedModule]) -> FixtureModule {
        let cert = build_module_cert(module, imports).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        FixtureModule { verified, bytes }
    }

    fn nat_fixture_module() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Std.Nat.Basic"),
                declarations: vec![Decl::Inductive {
                    name: "Nat".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0_level()),
                    data: Box::new(npa_kernel::nat_inductive()),
                }],
            },
            &[],
        )
    }

    fn eq_fixture_module() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Std.Logic.Eq"),
                declarations: vec![
                    Decl::Inductive {
                        name: "Eq".to_owned(),
                        universe_params: vec!["u".to_owned()],
                        ty: npa_kernel::eq_type(Level::param("u")),
                        data: Box::new(npa_kernel::eq_inductive()),
                    },
                    Decl::Axiom {
                        name: "Eq.rec".to_owned(),
                        universe_params: vec!["u".to_owned(), "v".to_owned()],
                        ty: npa_kernel::eq_rec_type(Level::param("u"), Level::param("v")),
                    },
                ],
            },
            &[],
        )
    }

    fn list_fixture_module() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Std.List.Basic"),
                declarations: vec![Decl::Inductive {
                    name: "List".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::pi(
                        "A",
                        Expr::sort(Level::param("u")),
                        Expr::sort(Level::param("u")),
                    ),
                    data: Box::new(list_inductive()),
                }],
            },
            &[],
        )
    }

    fn retrieval_fixture_module(imports: &[VerifiedModule]) -> FixtureModule {
        let one = Expr::konst("Lib.one", Vec::new());
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Lib.Simp"),
                declarations: vec![
                    Decl::Def {
                        name: "Lib.one".to_owned(),
                        universe_params: Vec::new(),
                        ty: nat(),
                        value: nat_succ(nat_zero()),
                        reducibility: Reducibility::Reducible,
                    },
                    Decl::Theorem {
                        name: "Lib.one_unfold".to_owned(),
                        universe_params: Vec::new(),
                        ty: eq_nat(one, nat_succ(nat_zero())),
                        proof: eq_refl_nat(nat_succ(nat_zero())),
                    },
                ],
            },
            imports,
        )
    }

    fn default_options_json(allow_axioms: &str) -> String {
        format!(
            r#"{{
              "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
              "allow_axioms": {allow_axioms},
              "tactic_options": {{
                "simp_rules": [],
                "eq_family": null,
                "nat_family": null,
                "max_simp_rewrite_steps": 100,
                "max_open_goals": 32,
                "max_metas": 64
              }}
            }}"#
        )
    }

    fn ai_search_retrieval_options_json(
        eq: &FixtureModule,
        rule: &FixtureModule,
        allow_axioms: &str,
    ) -> String {
        format!(
            r#"{{
              "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
              "allow_axioms": {allow_axioms},
              "tactic_options": {{
                "simp_rules": [{{
                  "name":"Lib.one_unfold",
                  "decl_interface_hash":"{}",
                  "direction":"forward"
                }}],
                "eq_family": {{
                  "eq_name":"Eq",
                  "eq_interface_hash":"{}",
                  "refl_name":"Eq.refl",
                  "refl_interface_hash":"{}",
                  "rec_name":"Eq.rec",
                  "rec_interface_hash":"{}"
                }},
                "nat_family": null,
                "max_simp_rewrite_steps": 100,
                "max_open_goals": 32,
                "max_metas": 64
              }}
            }}"#,
            format_hash_string(&export_interface_hash(rule, "Lib.one_unfold")),
            format_hash_string(&export_interface_hash(eq, "Eq")),
            format_hash_string(&export_interface_hash(eq, "Eq.refl")),
            format_hash_string(&export_interface_hash(eq, "Eq.rec")),
        )
    }

    fn export_interface_hash(module: &FixtureModule, name: &str) -> Hash {
        let name = Name::from_dotted(name);
        *module
            .verified
            .export_block()
            .iter()
            .find_map(|export| {
                let export_name = module.verified.name_table().get(export.name)?;
                (export_name == &name).then_some(&export.decl_interface_hash)
            })
            .expect("fixture export should exist")
    }

    fn eq_rec_allow_axioms_json(eq: &FixtureModule) -> String {
        format!(
            r#"[{{
              "kind":"imported",
              "module":"Std.Logic.Eq",
              "name":"Eq.rec",
              "export_hash":"{}",
              "decl_interface_hash":"{}"
            }}]"#,
            format_hash_string(&eq.verified.export_hash()),
            format_hash_string(&export_interface_hash(eq, "Eq.rec")),
        )
    }

    fn imported_axiom_allowlist_json(module: &FixtureModule, name: &str) -> String {
        format!(
            r#"[{{
              "kind":"imported",
              "module":"{}",
              "name":"{}",
              "export_hash":"{}",
              "decl_interface_hash":"{}"
            }}]"#,
            module.verified.module().as_dotted(),
            name,
            format_hash_string(&module.verified.export_hash()),
            format_hash_string(&export_interface_hash(module, name)),
        )
    }

    fn module_certificate_json(module: &FixtureModule) -> String {
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
            module.verified.module().as_dotted(),
            format_hash_string(&module.verified.export_hash()),
            format_hash_string(&module.verified.certificate_hash()),
            hex_bytes(&module.bytes),
        )
    }

    fn module_import_json(module: &FixtureModule) -> String {
        format!(
            r#"{{
              "module":"{}",
              "expected_export_hash":"{}",
              "expected_certificate_hash":"{}"
            }}"#,
            module.verified.module().as_dotted(),
            format_hash_string(&module.verified.export_hash()),
            format_hash_string(&module.verified.certificate_hash()),
        )
    }

    fn session_json_for_modules(
        theorem_type: &str,
        import_closure: &[&FixtureModule],
        imports: &[&FixtureModule],
        options_json: &str,
    ) -> String {
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
              "import_closure":[{}],
              "imports":[{}],
              "checked_current_decls":[],
              "options":{}
            }}"#,
            import_closure
                .iter()
                .map(|module| module_certificate_json(module))
                .collect::<Vec<_>>()
                .join(","),
            imports
                .iter()
                .map(|module| module_import_json(module))
                .collect::<Vec<_>>()
                .join(","),
            options_json
        )
    }

    fn ai_search_retrieval_session() -> MachineProofSession {
        let nat = nat_fixture_module();
        let eq = eq_fixture_module();
        let list = list_fixture_module();
        let simp = retrieval_fixture_module(&[nat.verified.clone(), eq.verified.clone()]);
        let allow_axioms = eq_rec_allow_axioms_json(&eq);
        let options = ai_search_retrieval_options_json(&eq, &simp, &allow_axioms);
        create_machine_session(&session_json_for_modules(
            "Eq.{1} Nat Lib.one Nat.zero",
            &[&nat, &eq, &list, &simp],
            &[&nat, &eq, &list, &simp],
            &options,
        ))
        .unwrap()
        .session
    }

    fn ai_search_exact_session(theorem_type: &str) -> MachineProofSession {
        let nat = nat_fixture_module();
        let eq = eq_fixture_module();
        let list = list_fixture_module();
        let allow_axioms = eq_rec_allow_axioms_json(&eq);
        let options = default_options_json(&allow_axioms);
        create_machine_session(&session_json_for_modules(
            theorem_type,
            &[&nat, &eq, &list],
            &[&nat, &eq, &list],
            &options,
        ))
        .unwrap()
        .session
    }

    fn imported_axiom_session() -> MachineProofSession {
        let module = CoreModule {
            name: Name::from_dotted("A"),
            declarations: vec![Decl::Axiom {
                name: "A.id".to_owned(),
                universe_params: Vec::new(),
                ty: imported_axiom_type(),
            }],
        };
        let cert = build_module_cert(module, &[]).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut verifier = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy.allowlisted_axioms.insert(Name::from_dotted("A.id"));
        let verified = verify_module_cert(&bytes, &mut verifier, &policy).unwrap();
        let export_hash = format_hash_string(&verified.export_hash());
        let certificate_hash = format_hash_string(&verified.certificate_hash());
        let decl_interface_hash =
            format_hash_string(&verified.declarations()[0].hashes.decl_interface_hash);
        let cert_hex = hex_bytes(&bytes);
        let allow_axioms = format!(
            r#"[{{
              "kind":"imported",
              "module":"A",
              "name":"A.id",
              "export_hash":"{export_hash}",
              "decl_interface_hash":"{decl_interface_hash}"
            }}]"#
        );
        let body = format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"Prop"}}
              }},
              "import_closure":[{{
                "module":"A",
                "expected_export_hash":"{export_hash}",
                "expected_certificate_hash":"{certificate_hash}",
                "certificate":{{
                  "encoding":"npa.certificate.canonical.v0.1.hex",
                  "bytes":"{cert_hex}"
                }}
              }}],
              "imports":[{{
                "module":"A",
                "expected_export_hash":"{export_hash}",
                "expected_certificate_hash":"{certificate_hash}"
              }}],
              "checked_current_decls":[],
              "options":{}
            }}"#,
            default_options_json(&allow_axioms)
        );
        create_machine_session(&body).unwrap().session
    }

    fn high_trust_fixture_module(module: CoreModule, imports: &[VerifiedModule]) -> FixtureModule {
        let cert = build_module_cert(module, imports).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        let mut policy = AxiomPolicy::high_trust();
        policy.allowlisted_axioms.extend(
            cert.name_table
                .iter()
                .filter_map(|name| name.is_canonical().then_some(name.clone())),
        );
        let verified = verify_module_cert(&bytes, &mut session, &policy).unwrap();
        FixtureModule { verified, bytes }
    }

    fn closure_only_theorem_import_proposal_fixture() -> (
        MachineProofSession,
        MachineProofSession,
        MachineVerifiedPremiseIdentity,
    ) {
        let premise = high_trust_fixture_module(
            CoreModule {
                name: Name::from_dotted("P"),
                declarations: vec![Decl::Axiom {
                    name: "P.ax".to_owned(),
                    universe_params: Vec::new(),
                    ty: prop(),
                }],
            },
            &[],
        );
        let bridge = fixture_module(
            CoreModule {
                name: Name::from_dotted("A.ImportP"),
                declarations: Vec::new(),
            },
            std::slice::from_ref(&premise.verified),
        );
        let allow_axioms = imported_axiom_allowlist_json(&premise, "P.ax");
        let options = default_options_json(&allow_axioms);
        let session = create_machine_session(&session_json_for_modules(
            "Prop",
            &[&premise, &bridge],
            &[&bridge],
            &options,
        ))
        .unwrap()
        .session;
        let rebuilt_session = create_machine_session(&session_json_for_modules(
            "Prop",
            &[&premise, &bridge],
            &[&premise, &bridge],
            &options,
        ))
        .unwrap()
        .session;
        let identity = identity_for_closure_export(&session, "P", "P.ax");
        (session, rebuilt_session, identity)
    }

    fn identity_for_closure_export(
        session: &MachineProofSession,
        module: &str,
        name: &str,
    ) -> MachineVerifiedPremiseIdentity {
        let module = Name::from_dotted(module);
        let name = Name::from_dotted(name);
        let entry = session
            .import_certificate_context
            .verified_modules()
            .iter()
            .find(|entry| entry.key.module == module)
            .unwrap();
        let export = entry
            .export_block
            .iter()
            .find(|export| export_name(entry, export).unwrap() == name)
            .unwrap();
        let mut axioms = export
            .axiom_dependencies
            .iter()
            .map(|axiom| {
                imported_axiom_ref_to_wire(0, &session.import_certificate_context, entry, axiom)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        sort_dedup_axiom_refs(&mut axioms);
        let global_ref = MachineVerifiedPremiseGlobalRef {
            module: entry.key.module.clone(),
            name,
            export_hash: entry.key.export_hash,
            certificate_hash: entry.key.certificate_hash,
            decl_interface_hash: export.decl_interface_hash,
        };
        MachineVerifiedPremiseIdentity::new(
            entry.key.module.clone(),
            entry.key.export_hash,
            entry.key.certificate_hash,
            global_ref,
            export.decl_interface_hash,
            export.type_hash,
            MachineVerifiedPremiseAxiomSummary::new(Vec::new(), axioms),
        )
        .unwrap()
    }

    fn package_import_proposal_identity() -> MachineVerifiedPremiseIdentity {
        let module = Name::from_dotted("Pkg.Missing");
        let export_hash = test_hash(211);
        let certificate_hash = test_hash(212);
        let decl_interface_hash = test_hash(213);
        let global_ref = MachineVerifiedPremiseGlobalRef {
            module: module.clone(),
            name: Name::from_dotted("Pkg.Missing.thm"),
            export_hash,
            certificate_hash,
            decl_interface_hash,
        };
        MachineVerifiedPremiseIdentity::new(
            module,
            export_hash,
            certificate_hash,
            global_ref,
            decl_interface_hash,
            test_hash(214),
            MachineVerifiedPremiseAxiomSummary::new(Vec::new(), Vec::new()),
        )
        .unwrap()
    }

    fn package_import_proposal_identity_with_disallowed_axiom() -> MachineVerifiedPremiseIdentity {
        let mut identity = package_import_proposal_identity();
        identity.axiom_summary =
            MachineVerifiedPremiseAxiomSummary::new(Vec::new(), vec![test_imported_axiom(220)]);
        identity
    }

    fn import_proposal_candidate_json(
        source: MachineImportProposalCandidateSource,
        identity: &MachineVerifiedPremiseIdentity,
    ) -> String {
        json_object_in_order(vec![
            ("source", json_string(source.as_str())),
            ("identity", verified_premise_identity_json(identity)),
        ])
    }

    fn import_proposal_json(
        session: &MachineProofSession,
        candidates: &str,
        proposed_for_tasks: &str,
        extra_fields: &str,
    ) -> String {
        let extra = if extra_fields.is_empty() {
            String::new()
        } else {
            format!(",{extra_fields}")
        };
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "proposed_for_tasks":{},
              "candidates":{}{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            proposed_for_tasks,
            candidates,
            extra,
        )
    }

    fn import_proposal_ok_fields(
        response: MachineImportProposalResponse,
    ) -> MachineImportProposalOkFields {
        match response {
            MachineApiResponseEnvelope::Ok(ok) => ok.endpoint_fields,
            MachineApiResponseEnvelope::Error(_) => panic!("import proposal should succeed"),
            MachineApiResponseEnvelope::SchedulerStopped(_) => {
                panic!("import proposal should not schedule")
            }
        }
    }

    fn premise_search_ok_fields(
        response: MachinePremiseSearchResponse,
    ) -> MachinePremiseSearchOkFields {
        match response {
            MachineApiResponseEnvelope::Ok(ok) => ok.endpoint_fields,
            MachineApiResponseEnvelope::Error(_) => panic!("premise search should succeed"),
            MachineApiResponseEnvelope::SchedulerStopped(_) => {
                panic!("premise search should not schedule")
            }
        }
    }

    fn retrieval_cache_key_variant(
        key: &MachineRetrievalCacheKey,
        mutate: impl FnOnce(&mut MachineRetrievalCacheKey),
    ) -> MachineRetrievalCacheKey {
        let mut changed = key.clone();
        mutate(&mut changed);
        changed.key_hash = machine_retrieval_cache_key_hash(&changed);
        changed
    }

    fn head_collision_context() -> crate::MachineImportCertificateContext {
        let mut verifier = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy.allowlisted_axioms.insert(Name::from_dotted("X"));
        policy.allowlisted_axioms.insert(Name::from_dotted("A.t"));

        let p_module = CoreModule {
            name: Name::from_dotted("P"),
            declarations: vec![Decl::Axiom {
                name: "X".to_owned(),
                universe_params: Vec::new(),
                ty: prop(),
            }],
        };
        let p_cert = build_module_cert(p_module, &[]).unwrap();
        let p_bytes = encode_module_cert(&p_cert).unwrap();
        let p_verified = verify_module_cert(&p_bytes, &mut verifier, &policy).unwrap();

        let a_module = CoreModule {
            name: Name::from_dotted("A"),
            declarations: vec![Decl::Axiom {
                name: "A.t".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::konst("X", Vec::new()),
            }],
        };
        let a_cert = build_module_cert(a_module, std::slice::from_ref(&p_verified)).unwrap();
        let a_bytes = encode_module_cert(&a_cert).unwrap();
        let a_verified = verify_module_cert(&a_bytes, &mut verifier, &policy).unwrap();

        let b_module = CoreModule {
            name: Name::from_dotted("B"),
            declarations: vec![Decl::Axiom {
                name: "X".to_owned(),
                universe_params: Vec::new(),
                ty: prop(),
            }],
        };
        let b_cert = build_module_cert(b_module, &[]).unwrap();
        let b_bytes = encode_module_cert(&b_cert).unwrap();
        let b_verified = verify_module_cert(&b_bytes, &mut verifier, &policy).unwrap();

        let p_name = Name::from_dotted("P");
        let a_name = Name::from_dotted("A");
        let b_name = Name::from_dotted("B");
        let closure = vec![
            VerifiedModuleCertificateInput {
                module: &p_name,
                expected_export_hash: p_verified.export_hash(),
                expected_certificate_hash: p_verified.certificate_hash(),
                certificate_bytes: &p_bytes,
            },
            VerifiedModuleCertificateInput {
                module: &a_name,
                expected_export_hash: a_verified.export_hash(),
                expected_certificate_hash: a_verified.certificate_hash(),
                certificate_bytes: &a_bytes,
            },
            VerifiedModuleCertificateInput {
                module: &b_name,
                expected_export_hash: b_verified.export_hash(),
                expected_certificate_hash: b_verified.certificate_hash(),
                certificate_bytes: &b_bytes,
            },
        ];
        let direct = vec![
            VerifiedImportKey::new(
                a_name.clone(),
                a_verified.export_hash(),
                a_verified.certificate_hash(),
            ),
            VerifiedImportKey::new(
                b_name.clone(),
                b_verified.export_hash(),
                b_verified.certificate_hash(),
            ),
        ];
        project_import_certificate_context(&closure, &direct, &policy).unwrap()
    }

    fn direct_axiom_display_scope(
        context: &crate::MachineImportCertificateContext,
        module: &str,
    ) -> MachineDisplayRenderScope {
        let module = Name::from_dotted(module);
        let (import_index, entry) = context
            .direct_import_entries()
            .into_iter()
            .enumerate()
            .find(|(_, entry)| entry.key.module == module)
            .unwrap();
        let export = entry
            .export_block
            .iter()
            .find(|export| matches!(export.kind, ExportKind::Axiom))
            .unwrap();
        let export_name = export_name(entry, export).unwrap();
        let view = MachineGlobalRefView::Imported {
            module: entry.key.module.clone(),
            name: export_name.clone(),
            export_hash: entry.key.export_hash,
            decl_interface_hash: export.decl_interface_hash,
            public_export: true,
            tactic_head_visible: true,
        };
        MachineDisplayRenderScope::from_entries([MachineDisplayRenderScopeEntry::new(
            view,
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: entry.key.module.clone(),
                owner_export_hash: entry.key.export_hash,
            },
            MachineSurfaceCallableRef::Imported {
                module: entry.key.module.clone(),
                name: export_name.clone(),
                export_hash: entry.key.export_hash,
                decl_interface_hash: export.decl_interface_hash,
            },
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::Imported {
            name: export_name,
            import_index: import_index as u32,
            decl_interface_hash: export.decl_interface_hash,
        })])
        .unwrap()
    }

    fn head_collision_context_and_scope() -> (
        crate::MachineImportCertificateContext,
        MachineDisplayRenderScope,
    ) {
        let context = head_collision_context();
        let display_scope = direct_axiom_display_scope(&context, "B");
        (context, display_scope)
    }

    fn search_json(session: &MachineProofSession, filters: &str) -> String {
        search_json_for_goal(session, "g0", filters)
    }

    fn search_json_for_goal(session: &MachineProofSession, goal_id: &str, filters: &str) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"{}",
              "modes":["apply","exact","rw","simp"],
              "limit":20,
              "filters":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            goal_id,
            filters
        )
    }

    fn premise_search_json(
        session: &MachineProofSession,
        filters: &str,
        extra_fields: &str,
    ) -> String {
        premise_search_json_for_goal(session, "g0", filters, extra_fields)
    }

    fn premise_search_json_for_goal(
        session: &MachineProofSession,
        goal_id: &str,
        filters: &str,
        extra_fields: &str,
    ) -> String {
        premise_search_json_full(
            session,
            goal_id,
            r#"["apply","exact","rw","simp"]"#,
            filters,
            &format_hash_string(&session.initial_snapshot.state_fingerprint),
            extra_fields,
        )
    }

    fn premise_search_json_full(
        session: &MachineProofSession,
        goal_id: &str,
        modes: &str,
        filters: &str,
        state_fingerprint: &str,
        extra_fields: &str,
    ) -> String {
        let extra = if extra_fields.is_empty() {
            String::new()
        } else {
            format!(",{extra_fields}")
        };
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"{}",
              "modes":{},
              "limit":20,
              "filters":{}{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            state_fingerprint,
            goal_id,
            modes,
            filters,
            extra
        )
    }

    fn premise_mode_metadata(
        result: &MachinePremiseSearchResult,
        mode: MachineTheoremMode,
    ) -> &MachinePremiseModeMetadata {
        result
            .ranking_metadata
            .mode_metadata
            .iter()
            .find(|metadata| metadata.mode == mode)
            .unwrap_or_else(|| panic!("missing mode metadata for {}", mode.as_str()))
    }

    fn ai_search_budget_json() -> &'static str {
        r#"{
          "max_tactic_steps":100,
          "max_whnf_steps":100,
          "max_conversion_steps":100,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#
    }

    fn ai_search_run_json(session: &MachineProofSession, candidate: &str) -> String {
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
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            candidate,
            ai_search_budget_json(),
        )
    }

    fn ai_search_batch_json(session: &MachineProofSession, candidates: &str) -> String {
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
              }}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            candidates,
            ai_search_budget_json(),
        )
    }

    fn exact_candidate_json(source: &str) -> String {
        format!(r#"{{"kind":"exact","term":{{"source":"{source}"}}}}"#)
    }

    fn batch_candidate_json(candidate_id: &str, candidate_json: &str) -> String {
        format!(r#"{{"candidate_id":"{candidate_id}","candidate":{candidate_json}}}"#)
    }

    fn suggested_candidate_json(candidate: &MachineTacticCandidate) -> String {
        match candidate {
            MachineTacticCandidate::Rewrite {
                rule,
                direction,
                site,
            } => {
                assert!(rule.universe_args.is_empty());
                format!(
                    r#"{{"kind":"rw","rule":{{"head":{},"universe_args":[],"args":[{}]}},"direction":"{}","site":"{}"}}"#,
                    tactic_head_json(&rule.head),
                    rule.args
                        .iter()
                        .map(apply_arg_json)
                        .collect::<Vec<_>>()
                        .join(","),
                    rewrite_direction_json(*direction),
                    rewrite_site_json(*site),
                )
            }
            MachineTacticCandidate::SimpLite { rules } => {
                format!(
                    r#"{{"kind":"simp-lite","rules":[{}]}}"#,
                    rules
                        .iter()
                        .map(simp_rule_json)
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            _ => panic!("ai_search fixture serializes only rw/simp search suggestions"),
        }
    }

    fn tactic_head_json(head: &TacticHead) -> String {
        match head {
            TacticHead::Imported {
                name,
                decl_interface_hash,
            } => format!(
                r#"{{"imported":{{"name":"{}","decl_interface_hash":"{}"}}}}"#,
                name.as_dotted(),
                format_hash_string(decl_interface_hash),
            ),
            _ => panic!("ai_search fixture expects imported tactic heads"),
        }
    }

    fn apply_arg_json(arg: &CandidateApplyArg) -> String {
        match arg {
            CandidateApplyArg::InferFromTarget => r#"{"mode":"infer_from_target"}"#.to_owned(),
            _ => panic!("ai_search fixture expects infer_from_target rw args"),
        }
    }

    fn simp_rule_json(rule: &SimpRuleRef) -> String {
        format!(
            r#"{{"name":"{}","decl_interface_hash":"{}","direction":"{}"}}"#,
            rule.name.as_dotted(),
            format_hash_string(&rule.decl_interface_hash),
            rewrite_direction_json(rule.direction),
        )
    }

    fn rewrite_direction_json(direction: RewriteDirection) -> &'static str {
        match direction {
            RewriteDirection::Forward => "forward",
            RewriteDirection::Backward => "backward",
        }
    }

    fn rewrite_site_json(site: RewriteSite) -> &'static str {
        match site {
            RewriteSite::EqTargetLeft => "eq_target_left",
            RewriteSite::EqTargetRight => "eq_target_right",
        }
    }

    #[test]
    fn import_proposal_returns_hash_bound_closure_candidate_without_visible_premise_use() {
        let (session, rebuilt_session, identity) = closure_only_theorem_import_proposal_fixture();
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &identity,
        )]);
        let body = import_proposal_json(
            &session,
            &candidates,
            r#"["PUA-M06-T10","PUA-M06-T10"]"#,
            "",
        );

        let first =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());
        let second =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert_eq!(first, second);
        assert_eq!(first.proposed_for_tasks, vec!["PUA-M06-T10".to_owned()]);
        assert!(first.rejected_candidates.is_empty());
        assert_eq!(first.proposals.len(), 1);
        let proposal = &first.proposals[0];
        assert_eq!(proposal.module, identity.module);
        assert_eq!(proposal.export_hash, identity.export_hash);
        assert_eq!(proposal.certificate_hash, identity.certificate_hash);
        assert_eq!(
            proposal.reason,
            MachineImportProposalReason::ClosureModuleNotDirect
        );
        assert_eq!(proposal.new_axiom_summary, identity.axiom_summary);
        assert!(proposal.approval.requires_new_snapshot);
        assert!(proposal.approval.requires_certificate_regeneration);

        let filters = r#"{"exclude_axioms":false,"allowed_modules":["P"]}"#;
        let err =
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap_err();
        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidTheoremQuery
        );

        let visible = search_machine_premises_for_goal(
            &premise_search_json(
                &session,
                r#"{"exclude_axioms":false,"allowed_modules":["A.ImportP"]}"#,
                "",
            ),
            &session,
        )
        .unwrap();
        match visible {
            MachineApiResponseEnvelope::Ok(ok) => {
                assert!(ok.endpoint_fields.results.is_empty());
            }
            MachineApiResponseEnvelope::Error(_) => panic!("premise search should succeed"),
            MachineApiResponseEnvelope::SchedulerStopped(_) => panic!("premise search should run"),
        }

        let accepted =
            validate_machine_import_proposal_acceptance(proposal, &session, &rebuilt_session)
                .unwrap();
        assert_eq!(accepted.proposal_hash, proposal.proposal_hash);
        assert_eq!(accepted.direct_import.module, Name::from_dotted("P"));
    }

    #[test]
    fn import_proposal_package_candidate_is_proposal_only_until_rebuilt() {
        let (session, _, _) = closure_only_theorem_import_proposal_fixture();
        let identity = package_import_proposal_identity();
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::PackageTheoremIndex,
            &identity,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["pkg-task"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.rejected_candidates.is_empty());
        assert_eq!(fields.proposals.len(), 1);
        assert_eq!(
            fields.proposals[0].reason,
            MachineImportProposalReason::PackageCandidateNotImported
        );
        assert_eq!(
            validate_machine_import_proposal_acceptance(&fields.proposals[0], &session, &session,),
            Err(MachineImportProposalAcceptanceError::RebuiltSnapshotRequired)
        );
    }

    #[test]
    fn import_proposal_rejects_cyclic_import_proposal() {
        let (session, _, identity) = closure_only_theorem_import_proposal_fixture();
        let mut cyclic = identity.clone();
        cyclic.module = session.root.module.clone();
        cyclic.global_ref.module = session.root.module.clone();
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &cyclic,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["cycle"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.proposals.is_empty());
        assert_eq!(fields.rejected_candidates.len(), 1);
        assert_eq!(
            fields.rejected_candidates[0].reason,
            MachineImportProposalRejectionReason::CyclicImportProposal
        );
    }

    #[test]
    fn import_proposal_rejects_stale_export_hash() {
        let (session, _, identity) = closure_only_theorem_import_proposal_fixture();
        let mut stale = identity.clone();
        stale.export_hash = test_hash(201);
        stale.global_ref.export_hash = stale.export_hash;
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &stale,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["stale-export"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.proposals.is_empty());
        assert_eq!(
            fields.rejected_candidates[0].reason,
            MachineImportProposalRejectionReason::StaleExportHash
        );
    }

    #[test]
    fn import_proposal_rejects_stale_certificate_hash() {
        let (session, _, identity) = closure_only_theorem_import_proposal_fixture();
        let mut stale = identity.clone();
        stale.certificate_hash = test_hash(202);
        stale.global_ref.certificate_hash = stale.certificate_hash;
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &stale,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["stale-cert"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.proposals.is_empty());
        assert_eq!(
            fields.rejected_candidates[0].reason,
            MachineImportProposalRejectionReason::StaleCertificateHash
        );
    }

    #[test]
    fn import_proposal_rejects_disallowed_axiom() {
        let (session, _, _) = closure_only_theorem_import_proposal_fixture();
        let identity = package_import_proposal_identity_with_disallowed_axiom();
        assert!(!identity.axiom_summary.transitive_axioms.is_empty());
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::PackageTheoremIndex,
            &identity,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["axiom-policy"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.proposals.is_empty());
        assert_eq!(
            fields.rejected_candidates[0].reason,
            MachineImportProposalRejectionReason::DisallowedAxiom
        );
    }

    #[test]
    fn import_proposal_rejects_incompatible_verified_closure_candidate() {
        let (session, _, _) = closure_only_theorem_import_proposal_fixture();
        let identity = package_import_proposal_identity();
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &identity,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["missing-closure"]"#, "");

        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());

        assert!(fields.proposals.is_empty());
        assert_eq!(
            fields.rejected_candidates[0].reason,
            MachineImportProposalRejectionReason::IncompatiblePackage
        );
    }

    #[test]
    fn import_proposal_acceptance_rejects_same_snapshot_and_stale_hash() {
        let (session, rebuilt_session, identity) = closure_only_theorem_import_proposal_fixture();
        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &identity,
        )]);
        let body = import_proposal_json(&session, &candidates, r#"["accept"]"#, "");
        let fields =
            import_proposal_ok_fields(propose_machine_imports_for_goal(&body, &session).unwrap());
        let proposal = fields.proposals[0].clone();

        assert_eq!(
            validate_machine_import_proposal_acceptance(&proposal, &session, &session),
            Err(MachineImportProposalAcceptanceError::RebuiltSnapshotRequired)
        );

        let mut stale = proposal.clone();
        stale.certificate_hash = test_hash(203);
        assert_eq!(
            validate_machine_import_proposal_acceptance(&stale, &session, &rebuilt_session),
            Err(MachineImportProposalAcceptanceError::StaleProposalIdentity)
        );
    }

    #[test]
    fn premise_identity_round_trips_json_and_distinguishes_same_name_hashes() {
        let first = test_verified_premise_identity("Pkg.Mod.same", 1, 2, 3, 4);
        let second = test_verified_premise_identity("Pkg.Mod.same", 11, 12, 13, 14);

        assert_eq!(first.global_ref.name, second.global_ref.name);
        assert_ne!(first.identity_hash(), second.identity_hash());

        let json = verified_premise_identity_json(&first);
        let parsed = parse_verified_premise_identity_json(&json).unwrap();

        assert_eq!(parsed, first);
        assert_eq!(verified_premise_identity_json(&parsed), json);
    }

    #[test]
    fn premise_identity_rejects_stale_verified_hash_mismatches() {
        let identity = test_verified_premise_identity("Pkg.Mod.same", 1, 2, 3, 4);

        let stale_export = verified_premise_identity_json(&identity).replacen(
            &format_hash_string(&identity.export_hash),
            &format_hash_string(&test_hash(90)),
            1,
        );
        assert!(matches!(
            parse_verified_premise_identity_json(&stale_export)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "export_hash"
            }
        ));

        let stale_certificate = verified_premise_identity_json(&identity).replacen(
            &format_hash_string(&identity.certificate_hash),
            &format_hash_string(&test_hash(91)),
            1,
        );
        assert!(matches!(
            parse_verified_premise_identity_json(&stale_certificate)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "certificate_hash"
            }
        ));

        let stale_decl = verified_premise_identity_json(&identity).replacen(
            &format_hash_string(&identity.decl_interface_hash),
            &format_hash_string(&test_hash(92)),
            1,
        );
        assert!(matches!(
            parse_verified_premise_identity_json(&stale_decl)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::IdentityMismatch {
                field: "decl_interface_hash"
            }
        ));
    }

    #[test]
    fn premise_index_entry_keeps_identity_stable_when_ranking_changes() {
        let first = test_verified_premise_entry(0);
        let mut second = first.clone();
        second.ranking_metadata.score = 99;

        assert_eq!(
            first.identity.identity_hash(),
            second.identity.identity_hash()
        );
        assert_eq!(first.stable_entry_hash(), second.stable_entry_hash());
        assert_ne!(
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(first.clone()))),
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(second)))
        );

        let json =
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(first.clone())));
        let parsed = parse_premise_index_entry_json(&json).unwrap();
        assert_eq!(parsed, MachinePremiseIndexEntry::Verified(Box::new(first)));
    }

    #[test]
    fn premise_index_entry_rejects_stale_statement_core_hash_mismatch() {
        let entry = test_verified_premise_entry(0);
        let json =
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(entry.clone())));
        let stale_statement = json.replacen(
            &format_hash_string(&entry.identity.statement_core_hash),
            &format_hash_string(&test_hash(93)),
            1,
        );

        assert!(matches!(
            parse_premise_index_entry_json(&stale_statement)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::StatementCoreHashMismatch
        ));
    }

    #[test]
    fn premise_index_entry_rejects_stale_structural_feature_hash() {
        let entry = test_verified_premise_entry(0);
        let json =
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(entry.clone())));
        let stale_feature_hash = json.replacen(
            &format_hash_string(&entry.structural_features.feature_hash),
            &format_hash_string(&test_hash(94)),
            1,
        );

        assert!(matches!(
            parse_premise_index_entry_json(&stale_feature_hash)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::StructuralFeatureHashMismatch
        ));
    }

    #[test]
    fn premise_index_fingerprint_tracks_verified_identity_and_structural_fields() {
        let base = test_verified_premise_entry(0);
        let base_index = MachineVerifiedPremiseIndex::new(vec![base.clone()]);

        let changed_export = MachineVerifiedPremiseIndexEntry::new(
            test_verified_premise_identity("Pkg.Mod.same", 90, 2, 3, 4),
            base.statement_core_hash,
            base.structural_features.clone(),
            base.modes.clone(),
            base.source,
            base.ranking_metadata.clone(),
        )
        .unwrap();
        let changed_certificate = MachineVerifiedPremiseIndexEntry::new(
            test_verified_premise_identity("Pkg.Mod.same", 1, 91, 3, 4),
            base.statement_core_hash,
            base.structural_features.clone(),
            base.modes.clone(),
            base.source,
            base.ranking_metadata.clone(),
        )
        .unwrap();
        let mut changed_axiom_identity = base.identity.clone();
        changed_axiom_identity.axiom_summary = MachineVerifiedPremiseAxiomSummary::new(
            vec![test_imported_axiom(61)],
            vec![test_imported_axiom(61), test_imported_axiom(63)],
        );
        let changed_axioms = MachineVerifiedPremiseIndexEntry::new(
            changed_axiom_identity,
            base.statement_core_hash,
            base.structural_features.clone(),
            base.modes.clone(),
            base.source,
            base.ranking_metadata.clone(),
        )
        .unwrap();
        let changed_structural = MachineVerifiedPremiseIndexEntry::new(
            base.identity.clone(),
            base.statement_core_hash,
            test_structural_features(95, base.statement_core_hash),
            base.modes.clone(),
            base.source,
            base.ranking_metadata.clone(),
        )
        .unwrap();
        let mut changed_ranking = base.clone();
        changed_ranking.ranking_metadata.score = 777;

        assert_ne!(
            base_index.fingerprint,
            MachineVerifiedPremiseIndex::new(vec![changed_export]).fingerprint
        );
        assert_ne!(
            base_index.fingerprint,
            MachineVerifiedPremiseIndex::new(vec![changed_certificate]).fingerprint
        );
        assert_ne!(
            base_index.fingerprint,
            MachineVerifiedPremiseIndex::new(vec![changed_axioms]).fingerprint
        );
        assert_ne!(
            base_index.fingerprint,
            MachineVerifiedPremiseIndex::new(vec![changed_structural]).fingerprint
        );
        assert_eq!(
            base_index.fingerprint,
            MachineVerifiedPremiseIndex::new(vec![changed_ranking]).fingerprint
        );
    }

    #[test]
    fn premise_index_fingerprint_is_stable_across_entry_ordering() {
        let first = test_verified_premise_entry(0);
        let mut second = test_verified_premise_entry(1);
        second.identity = test_verified_premise_identity("Pkg.Mod.other", 11, 12, 13, 14);
        second.statement_core_hash = second.identity.statement_core_hash;
        second.structural_features = test_structural_features(80, second.statement_core_hash);

        let forward = MachineVerifiedPremiseIndex::new(vec![first.clone(), second.clone()]);
        let reverse = MachineVerifiedPremiseIndex::new(vec![second, first]);

        assert_eq!(forward.fingerprint, reverse.fingerprint);
        assert_eq!(forward.entries, reverse.entries);
    }

    #[test]
    fn premise_index_entry_untrusted_candidate_has_distinct_marker() {
        let entry =
            MachinePremiseIndexEntry::UntrustedCandidate(MachineUntrustedPremiseCandidate {
                candidate_hash: test_hash(44),
                source_label: "model-sidecar".to_owned(),
                reason: "not verified metadata".to_owned(),
            });

        let json = premise_index_entry_json(&entry);
        assert!(json.contains(r#""kind":"untrusted_candidate""#));
        assert!(!json.contains(r#""identity":"#));

        let parsed = parse_premise_index_entry_json(&json).unwrap();
        assert_eq!(parsed, entry);

        let polluted = json.replacen(r#""candidate":"#, r#""identity":{},"candidate":"#, 1);
        assert!(matches!(
            parse_premise_index_entry_json(&polluted).unwrap_err().reason,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::UnknownField { ref field }
            ) if field == "identity"
        ));
    }

    #[test]
    fn package_theorem_index_entry_projects_to_verified_premise_identity_without_statement_parsing()
    {
        let statement_head = npa_package::PackageGlobalRefView {
            module: Name::from_dotted("Pkg.Struct"),
            name: Name::from_dotted("Pkg.Struct.Head"),
            export_hash: test_package_hash(20),
            decl_interface_hash: test_package_hash(21),
        };
        let package_entry = npa_package::PackageTheoremIndexEntry {
            global_ref: npa_package::PackageGlobalRef {
                module: Name::from_dotted("Pkg.Mod"),
                name: Name::from_dotted("Pkg.Mod.same"),
                export_hash: test_package_hash(1),
                certificate_hash: test_package_hash(2),
                decl_interface_hash: test_package_hash(3),
            },
            kind: npa_package::PackageTheoremIndexKind::Theorem,
            statement: npa_package::PackageTheoremStatement {
                core_hash: test_package_hash(4),
                head: Some(statement_head.clone()),
                constants: vec![statement_head],
            },
            modes: vec![
                npa_package::PackageTheoremIndexMode::Apply,
                npa_package::PackageTheoremIndexMode::Exact,
            ],
            tags: vec!["group".to_owned()],
            axiom_dependencies: vec![npa_package::PackageAxiomReference {
                module: Name::from_dotted("Pkg.Axiom"),
                name: Name::from_dotted("Pkg.Axiom.choice"),
                export_hash: test_package_hash(5),
                decl_interface_hash: test_package_hash(6),
            }],
            module_axiom_report_hash: test_package_hash(7),
            artifact: npa_package::PackageTheoremIndexArtifact {
                origin: npa_package::PackageArtifactOrigin::Local,
                certificate: npa_package::PackagePath::new("Pkg/Mod/same.npcert"),
            },
        };

        let projected =
            project_package_theorem_index_entry_to_verified_premise_entry(&package_entry).unwrap();

        assert_eq!(
            projected.source,
            MachinePremiseIndexSource::PackageTheoremIndex
        );
        assert_eq!(projected.identity.module, package_entry.global_ref.module);
        assert_eq!(
            projected.identity.certificate_hash,
            package_entry.global_ref.certificate_hash.into_bytes()
        );
        assert_eq!(
            projected.identity.statement_core_hash,
            package_entry.statement.core_hash.into_bytes()
        );
        assert!(projected.identity.axiom_summary.direct_axioms.is_empty());
        assert_eq!(projected.identity.axiom_summary.transitive_axioms.len(), 1);
        assert_eq!(
            projected.modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply]
        );
        assert_eq!(
            projected.structural_features.target_head,
            Some(machine_premise_structural_ref_from_package_global_ref_view(
                package_entry.statement.head.as_ref().unwrap()
            ))
        );
        assert_eq!(
            projected
                .structural_features
                .normalized_expression_fingerprints,
            vec![package_entry.statement.core_hash.into_bytes()]
        );

        let json = premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(
            projected.clone(),
        )));
        assert_eq!(
            parse_premise_index_entry_json(&json).unwrap(),
            MachinePremiseIndexEntry::Verified(Box::new(projected))
        );
    }

    #[test]
    fn package_theorem_index_projection_rejects_malformed_source_free_modes() {
        let package_entry = npa_package::PackageTheoremIndexEntry {
            global_ref: npa_package::PackageGlobalRef {
                module: Name::from_dotted("Pkg.Mod"),
                name: Name::from_dotted("Pkg.Mod.same"),
                export_hash: test_package_hash(1),
                certificate_hash: test_package_hash(2),
                decl_interface_hash: test_package_hash(3),
            },
            kind: npa_package::PackageTheoremIndexKind::Theorem,
            statement: npa_package::PackageTheoremStatement {
                core_hash: test_package_hash(4),
                head: None,
                constants: Vec::new(),
            },
            modes: Vec::new(),
            tags: Vec::new(),
            axiom_dependencies: Vec::new(),
            module_axiom_report_hash: test_package_hash(7),
            artifact: npa_package::PackageTheoremIndexArtifact {
                origin: npa_package::PackageArtifactOrigin::Local,
                certificate: npa_package::PackagePath::new("Pkg/Mod/same.npcert"),
            },
        };

        assert!(matches!(
            project_package_theorem_index_entry_to_verified_premise_entry(&package_entry)
                .unwrap_err()
                .reason,
            MachinePremiseIndexErrorReason::Request(
                MachineApiErrorKind::InvalidTheoremIndex,
                MachineApiRequestErrorReason::MissingField { field: "modes" }
            )
        ));
    }

    #[test]
    fn ai_search_nat_and_list_exact_fixtures_must_reenter_machine_api_run() {
        let mut nat_session = ai_search_exact_session("Nat");
        let nat_run = run_machine_tactic_request(
            &ai_search_run_json(&nat_session, &exact_candidate_json("Nat.zero")),
            &mut nat_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(nat_ok) = nat_run else {
            panic!("Nat exact candidate should close through machine API run");
        };
        assert_eq!(
            nat_ok.endpoint_fields.result.kind,
            MachineTacticRunResultKind::Closed
        );

        let mut list_session = ai_search_exact_session("List.{1} Nat");
        let list_run = run_machine_tactic_request(
            &ai_search_run_json(&list_session, &exact_candidate_json("@List.nil.{1} Nat")),
            &mut list_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(list_ok) = list_run else {
            panic!("List exact candidate should close through machine API run");
        };
        assert_eq!(
            list_ok.endpoint_fields.result.kind,
            MachineTacticRunResultKind::Closed
        );
    }

    #[test]
    fn ai_search_retrieval_fixtures_reproduce_rw_and_simp_candidate_sources() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let first =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();
        let second =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();

        let (first_fields, second_fields) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("ai_search retrieval search should succeed"),
        };

        assert_eq!(
            first_fields.query_fingerprint,
            second_fields.query_fingerprint
        );
        assert_eq!(
            first_fields.theorem_index_fingerprint,
            second_fields.theorem_index_fingerprint
        );
        assert_eq!(
            format_hash_string(&first_fields.query_fingerprint),
            "sha256:5823ed1b23d68ee836bc8c7fc970f2177b821316c210b38a31f95402d19758f6"
        );
        assert_eq!(
            format_hash_string(&first_fields.theorem_index_fingerprint),
            "sha256:76c9a3cb4074d9afc7e42a222611112c6650ed5725f55b603bd0a272654959d6"
        );
        assert_eq!(first_fields.results, second_fields.results);
        assert_eq!(first_fields.results.len(), 1);

        let result = &first_fields.results[0];
        assert_eq!(result.global_ref.module, Name::from_dotted("Lib.Simp"));
        assert_eq!(result.global_ref.name, Name::from_dotted("Lib.one_unfold"));
        assert_eq!(
            result.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp
            ]
        );
        assert_eq!(result.suggested_candidates.len(), 2);
        assert!(matches!(
            result.suggested_candidates[0].candidate,
            MachineTacticCandidate::Rewrite { .. }
        ));
        assert!(matches!(
            result.suggested_candidates[1].candidate,
            MachineTacticCandidate::SimpLite { .. }
        ));
        assert_eq!(
            result
                .suggested_candidates
                .iter()
                .map(|candidate| candidate.status)
                .collect::<Vec<_>>(),
            vec![
                MachineSuggestedCandidateStatus::Validated,
                MachineSuggestedCandidateStatus::Validated
            ]
        );

        let batch_candidates = result
            .suggested_candidates
            .iter()
            .enumerate()
            .map(|(index, candidate)| {
                batch_candidate_json(
                    &format!("cand_{index}"),
                    &suggested_candidate_json(&candidate.candidate),
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let mut batch_session = ai_search_retrieval_session();
        let batch_response = run_machine_tactic_batch_request(
            &ai_search_batch_json(&batch_session, &format!("[{batch_candidates}]")),
            &mut batch_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(batch_ok) = batch_response else {
            panic!("ai_search suggested candidates should re-enter machine API batch");
        };
        assert_eq!(
            batch_ok.endpoint_fields.success_count + batch_ok.endpoint_fields.failure_count,
            2
        );
        for (index, item) in batch_ok.endpoint_fields.results.iter().enumerate() {
            let candidate_hash = match item {
                MachineTacticBatchItemResponse::Success { candidate_hash, .. } => *candidate_hash,
                MachineTacticBatchItemResponse::Error {
                    candidate_hash: Some(candidate_hash),
                    ..
                } => *candidate_hash,
                MachineTacticBatchItemResponse::Error {
                    candidate_hash: None,
                    ..
                } => panic!("candidate {index} should canonicalize before execution"),
            };
            let suggested = &result.suggested_candidates[index];
            let payload_hash = machine_tactic_validate_machine_tactic_candidate(
                session.initial_snapshot.open_goals[0],
                suggested.candidate.clone(),
            )
            .unwrap()
            .candidate_hash;
            assert_eq!(suggested.candidate_hash, payload_hash);
            assert_ne!(candidate_hash, suggested.candidate_hash);
        }
    }

    #[test]
    fn search_query_fingerprint_premise_route_is_versioned_adapter_route() {
        assert_eq!(
            crate::MachineApiEndpoint::PremisesSearch.as_str(),
            "POST /v1/npa/premises/search"
        );
        assert_eq!(
            crate::MachineApiEndpoint::SearchForGoal.as_str(),
            "POST /machine/search/for_goal"
        );
        assert_eq!(
            crate::machine_endpoint_envelope_spec(crate::MachineApiEndpoint::PremisesSearch)
                .fields
                .iter()
                .map(|field| field.name)
                .collect::<Vec<_>>(),
            vec![
                "session_id",
                "snapshot_id",
                "state_fingerprint",
                "goal_id",
                "modes",
                "limit",
                "filters",
                "expected_theorem_index_fingerprint",
                "graph_snapshot_hash",
            ]
        );
    }

    #[test]
    fn search_query_fingerprint_premise_search_contract_is_deterministic() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let graph_hash = test_hash(211);
        let extra = format!(
            r#""graph_snapshot_hash":"{}""#,
            format_hash_string(&graph_hash)
        );
        let first = search_machine_premises_for_goal(
            &premise_search_json(&session, filters, &extra),
            &session,
        )
        .unwrap();
        let second = search_machine_premises_for_goal(
            &premise_search_json(&session, filters, &extra),
            &session,
        )
        .unwrap();

        let (first_fields, second_fields) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("premise search should succeed"),
        };

        assert_eq!(
            first_fields.query_fingerprint,
            second_fields.query_fingerprint
        );
        assert_eq!(first_fields.results, second_fields.results);
        assert_eq!(
            first_fields.query_profile_hash,
            premise_search_query_profile_hash(PREMISE_SEARCH_QUERY_PROFILE_VERSION)
        );
        assert_eq!(first_fields.graph_snapshot_hash, Some(graph_hash));
        assert_eq!(
            first_fields.selected_modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp
            ]
        );
        assert_eq!(first_fields.results.len(), 1);

        let result = &first_fields.results[0];
        assert_eq!(
            result.verified_identity.module,
            Name::from_dotted("Lib.Simp")
        );
        assert_eq!(
            result.verified_identity.global_ref.name,
            Name::from_dotted("Lib.one_unfold")
        );
        assert_eq!(
            result.selected_modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp
            ]
        );
        assert_eq!(result.ranking_metadata.score, PREMISE_RANKING_BASE_SCORE);
        assert!(result.ranking_metadata.axiom_ranking.axiom_paths.is_empty());
        assert_eq!(
            result.candidate_provenance.premise_source,
            MachinePremiseIndexSource::DirectImport
        );
        assert_eq!(
            result.candidate_provenance.suggestion_profile_version,
            SUGGESTION_PROFILE_VERSION
        );
        assert_eq!(
            usize::try_from(result.candidate_provenance.suggested_candidate_count).unwrap(),
            result.untrusted_sidecar.suggested_candidates.len()
        );
        assert_eq!(result.untrusted_sidecar.suggested_candidates.len(), 2);
    }

    #[test]
    fn retrieval_cache_key_uses_required_components_and_hits_byte_identical_key() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let graph_hash = test_hash(211);
        let extra = format!(
            r#""graph_snapshot_hash":"{}""#,
            format_hash_string(&graph_hash)
        );
        let fields = premise_search_ok_fields(
            search_machine_premises_for_goal(
                &premise_search_json(&session, filters, &extra),
                &session,
            )
            .unwrap(),
        );
        let goal = &session.initial_snapshot.goals[0];
        let key = &fields.retrieval_cache_key;

        assert_eq!(key.environment_hash, session.session_root_hash);
        assert_eq!(key.goal_fingerprint, goal.goal_fingerprint);
        assert_eq!(
            key.local_context_hash,
            retrieval_local_context_hash(goal.context_hash, goal.local_name_map_hash)
        );
        assert_eq!(key.query_fingerprint, fields.query_fingerprint);
        assert_eq!(key.query_profile_hash, fields.query_profile_hash);
        assert_eq!(
            key.theorem_index_fingerprint,
            fields.theorem_index_fingerprint
        );
        assert_eq!(key.graph_snapshot_hash, Some(graph_hash));
        assert_eq!(
            key.visible_imports_fingerprint,
            fields.visible_imports_fingerprint
        );
        assert_eq!(key.key_hash, machine_retrieval_cache_key_hash(key));

        let entry = machine_retrieval_cache_entry_from_premise_search(&fields);
        let mut cache = MachineRetrievalCache::new();
        assert!(cache.is_empty());
        assert!(cache.insert(entry.clone()).is_none());
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(key), Some(&entry));

        let changed_graph =
            retrieval_cache_key_variant(key, |key| key.graph_snapshot_hash = Some(test_hash(212)));
        assert!(cache.get(&changed_graph).is_none());
    }

    #[test]
    fn retrieval_cache_key_invalidates_each_key_component() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let fields = premise_search_ok_fields(
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap(),
        );
        let entry = machine_retrieval_cache_entry_from_premise_search(&fields);
        let mut cache = MachineRetrievalCache::new();
        cache.insert(entry);
        let base = fields.retrieval_cache_key;

        let changed_keys = [
            retrieval_cache_key_variant(&base, |key| key.environment_hash = test_hash(31)),
            retrieval_cache_key_variant(&base, |key| key.goal_fingerprint = test_hash(32)),
            retrieval_cache_key_variant(&base, |key| key.local_context_hash = test_hash(33)),
            retrieval_cache_key_variant(&base, |key| key.query_fingerprint = test_hash(34)),
            retrieval_cache_key_variant(&base, |key| key.query_profile_hash = test_hash(35)),
            retrieval_cache_key_variant(&base, |key| key.theorem_index_fingerprint = test_hash(36)),
            retrieval_cache_key_variant(&base, |key| key.graph_snapshot_hash = Some(test_hash(37))),
            retrieval_cache_key_variant(&base, |key| {
                key.visible_imports_fingerprint = test_hash(38)
            }),
        ];

        for changed in changed_keys {
            assert_ne!(base.key_hash, changed.key_hash);
            assert!(cache.get(&changed).is_none());
        }
    }

    #[test]
    fn retrieval_cache_entry_separates_identity_from_refreshable_ranking_payloads() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let mut fields = premise_search_ok_fields(
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap(),
        );
        let entry = machine_retrieval_cache_entry_from_premise_search(&fields);
        let original_identities = entry.result_identities.clone();
        let original_ranking = entry.ranking_payloads.clone();

        fields.results[0].ranking_metadata.score = 9001;
        fields.results[0]
            .untrusted_sidecar
            .suggested_candidates
            .clear();
        fields.results[0]
            .candidate_provenance
            .suggested_candidate_count = 0;
        let refreshed = refresh_machine_retrieval_cache_ranking(&entry, &fields).unwrap();

        assert_eq!(refreshed.result_identities, original_identities);
        assert_ne!(refreshed.ranking_payloads, original_ranking);
        assert_eq!(refreshed.ranking_payloads[0].ranking_metadata.score, 9001);
        assert_eq!(refreshed.sidecar_scores[0].score, 9001);
        assert_eq!(refreshed.sidecar_scores[0].suggested_candidate_count, 0);

        fields.results[0].verified_identity.statement_core_hash = test_hash(230);
        assert_eq!(
            refresh_machine_retrieval_cache_ranking(&entry, &fields),
            Err(MachineRetrievalCacheRefreshError::VerifiedIdentityMismatch)
        );
    }

    #[test]
    fn retrieval_metrics_summary_reports_deterministic_quality_latency_and_cache_rates() {
        let premise_a = test_evaluation_identity("Eval.Mod.a", 1);
        let premise_b = test_evaluation_identity("Eval.Mod.b", 11);
        let premise_c = test_evaluation_identity("Eval.Mod.c", 21);
        let premise_d = test_evaluation_identity("Eval.Mod.d", 31);
        let premise_e = test_evaluation_identity("Eval.Mod.e", 41);

        let mut case_one = test_evaluation_case(
            "case-one",
            vec![premise_a.clone(), premise_b.clone()],
            vec![
                test_retrieved_premise(&premise_a, 900),
                test_retrieved_premise(&premise_c, 800),
                test_retrieved_premise(&premise_b, 700),
            ],
        );
        case_one.import_proposals_accepted = 1;
        case_one.import_proposals_rejected = 1;
        case_one.baseline_proof_completed = Some(false);
        case_one.retrieval_proof_completed = Some(true);
        case_one.latency_micros = 10;
        case_one.cache_hit = true;

        let mut case_two = test_evaluation_case(
            "case-two",
            vec![premise_d.clone()],
            vec![
                test_retrieved_premise(&premise_e, 600),
                test_retrieved_premise(&premise_d, 500),
            ],
        );
        case_two.import_proposals_accepted = 1;
        case_two.baseline_proof_completed = Some(false);
        case_two.retrieval_proof_completed = Some(false);
        case_two.latency_micros = 30;

        let fixture = MachineRetrievalEvaluationFixture::new(vec![case_two, case_one]);
        let summary = machine_retrieval_evaluation_summary(&fixture);

        assert_eq!(summary.schema, RETRIEVAL_EVALUATION_SCHEMA_VERSION);
        assert_eq!(summary.case_count, 2);
        assert_eq!(summary.evaluated_case_count, 2);
        assert!(summary.rejected_cases.is_empty());
        assert_eq!(summary.metrics.recall_at_1_basis_points, 3333);
        assert_eq!(summary.metrics.recall_at_4_basis_points, 10000);
        assert_eq!(summary.metrics.recall_at_8_basis_points, 10000);
        assert_eq!(summary.metrics.recall_at_32_basis_points, 10000);
        assert_eq!(summary.metrics.precision_at_1_basis_points, 5000);
        assert_eq!(summary.metrics.precision_at_4_basis_points, 6000);
        assert_eq!(summary.metrics.precision_at_8_basis_points, 6000);
        assert_eq!(summary.metrics.precision_at_32_basis_points, 6000);
        assert_eq!(
            summary.metrics.final_proof_premise_recall_basis_points,
            10000
        );
        assert_eq!(summary.metrics.mean_reciprocal_rank_microunits, 750_000);
        assert_eq!(summary.metrics.proof_completion_uplift_basis_points, 5000);
        assert_eq!(summary.metrics.proof_completion_uplift_case_count, 2);
        assert_eq!(summary.metrics.unused_premise_ratio_basis_points, 4000);
        assert_eq!(
            summary.metrics.import_proposal_acceptance_rate_basis_points,
            6666
        );
        assert_eq!(summary.metrics.axiom_policy_violation_rate_basis_points, 0);
        assert_eq!(summary.metrics.p50_latency_micros, 10);
        assert_eq!(summary.metrics.p95_latency_micros, 30);
        assert_eq!(summary.metrics.cache_hit_rate_basis_points, 5000);

        let snapshot = machine_retrieval_evaluation_ci_snapshot(&summary);
        assert!(snapshot.contains("recall_at_1_basis_points=3333\n"));
        assert!(snapshot.contains("p95_latency_micros=30\n"));
    }

    #[test]
    fn retrieval_evaluation_runs_without_graph_or_embedding_and_latency_does_not_rank() {
        let expected = test_evaluation_identity("Eval.Mod.goal", 51);
        let distractor = test_evaluation_identity("Eval.Mod.distractor", 61);
        let mut case = test_evaluation_case(
            "no-sidecars",
            vec![expected.clone()],
            vec![
                test_retrieved_premise(&distractor, 1000),
                test_retrieved_premise(&expected, 10),
            ],
        );
        case.graph_snapshot_hash = None;
        case.observed_graph_snapshot_hash = None;
        case.latency_micros = 5;
        let base = MachineRetrievalEvaluationFixture::new(vec![case.clone()]);
        let base_summary = machine_retrieval_evaluation_summary(&base);

        case.latency_micros = 5000;
        let slow = MachineRetrievalEvaluationFixture::new(vec![case]);
        let slow_summary = machine_retrieval_evaluation_summary(&slow);

        assert_eq!(base_summary.rejected_cases, Vec::new());
        assert_eq!(base_summary.metrics.recall_at_1_basis_points, 0);
        assert_eq!(base_summary.metrics.recall_at_4_basis_points, 10000);
        assert_eq!(
            base_summary.metrics.mean_reciprocal_rank_microunits,
            slow_summary.metrics.mean_reciprocal_rank_microunits
        );
        assert_eq!(
            base_summary.metrics.final_proof_premise_recall_basis_points,
            slow_summary.metrics.final_proof_premise_recall_basis_points
        );
        assert_ne!(
            base_summary.metrics.p50_latency_micros,
            slow_summary.metrics.p50_latency_micros
        );
    }

    #[test]
    fn retrieval_evaluation_negative_fixtures_report_required_rejections() {
        let clean = test_evaluation_identity("Eval.Mod.clean", 71);
        let disallowed_axiom = test_imported_axiom(88);
        let axiom_premise = test_verified_premise_identity_with_axioms(
            "Eval.Mod.axiom",
            81,
            82,
            83,
            84,
            vec![disallowed_axiom],
        );

        let mut stale_graph = test_evaluation_case(
            "stale-graph",
            Vec::new(),
            vec![test_retrieved_premise(&clean, 1)],
        );
        stale_graph.graph_snapshot_hash = Some(test_hash(90));
        stale_graph.observed_graph_snapshot_hash = Some(test_hash(91));

        let mut stale_index = test_evaluation_case("stale-index", Vec::new(), Vec::new());
        stale_index.expected_theorem_index_fingerprint = test_hash(92);
        stale_index.theorem_index_fingerprint = test_hash(93);

        let mut checker = test_evaluation_case("checker", Vec::new(), Vec::new());
        checker.checker_disagreement = true;

        let mut import_hash = test_evaluation_case(
            "import-hash",
            Vec::new(),
            vec![test_retrieved_premise(&clean, 1)],
        );
        import_hash.allowed_imports = vec![MachineImportProposalImportIdentity {
            module: clean.module.clone(),
            export_hash: test_hash(94),
            certificate_hash: clean.certificate_hash,
        }];

        let disallowed = test_evaluation_case(
            "disallowed-axiom",
            Vec::new(),
            vec![test_retrieved_premise(&axiom_premise, 10_000)],
        );

        let fixture = MachineRetrievalEvaluationFixture::new(vec![
            import_hash,
            stale_index,
            disallowed,
            checker,
            stale_graph,
        ]);
        let summary = machine_retrieval_evaluation_summary(&fixture);

        assert_eq!(summary.case_count, 5);
        assert_eq!(summary.evaluated_case_count, 0);
        assert_eq!(
            summary
                .rejected_cases
                .iter()
                .map(|case| (case.case_id.as_str(), case.reasons.clone()))
                .collect::<Vec<_>>(),
            vec![
                (
                    "checker",
                    vec![MachineRetrievalEvaluationRejectionReason::CheckerDisagreement],
                ),
                (
                    "disallowed-axiom",
                    vec![MachineRetrievalEvaluationRejectionReason::DisallowedAxiom],
                ),
                (
                    "import-hash",
                    vec![MachineRetrievalEvaluationRejectionReason::ImportHashMismatch],
                ),
                (
                    "stale-graph",
                    vec![MachineRetrievalEvaluationRejectionReason::StaleGraphSnapshot],
                ),
                (
                    "stale-index",
                    vec![MachineRetrievalEvaluationRejectionReason::StaleTheoremIndex],
                ),
            ]
        );
        assert_eq!(
            summary.metrics.axiom_policy_violation_rate_basis_points,
            3333
        );
        assert!(machine_retrieval_evaluation_ci_snapshot(&summary)
            .contains("rejected_case.disallowed-axiom=disallowed_axiom\n"));
    }

    #[test]
    fn retrieval_cache_invalidates_changed_imports_axiom_policy_and_stale_import_proposal() {
        let (session, rebuilt_session, identity) = closure_only_theorem_import_proposal_fixture();
        let filters = r#"{"exclude_axioms":false}"#;
        let before = premise_search_ok_fields(
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap(),
        );
        let mut cache = MachineRetrievalCache::new();
        cache.insert(machine_retrieval_cache_entry_from_premise_search(&before));

        let candidates = json_array(vec![import_proposal_candidate_json(
            MachineImportProposalCandidateSource::VerifiedClosure,
            &identity,
        )]);
        let mut proposal_fields = import_proposal_ok_fields(
            propose_machine_imports_for_goal(
                &import_proposal_json(&session, &candidates, r#"["cache-import"]"#, ""),
                &session,
            )
            .unwrap(),
        );
        let proposal = proposal_fields.proposals.remove(0);
        assert!(
            validate_machine_import_proposal_acceptance(&proposal, &session, &rebuilt_session)
                .is_ok()
        );

        let after = premise_search_ok_fields(
            search_machine_premises_for_goal(
                &premise_search_json(&rebuilt_session, filters, ""),
                &rebuilt_session,
            )
            .unwrap(),
        );
        assert_ne!(
            before.retrieval_cache_key.environment_hash,
            after.retrieval_cache_key.environment_hash
        );
        assert_ne!(
            before.retrieval_cache_key.visible_imports_fingerprint,
            after.retrieval_cache_key.visible_imports_fingerprint
        );
        assert!(cache.get(&after.retrieval_cache_key).is_none());

        let mut stale = proposal.clone();
        stale.proposal_hash = test_hash(240);
        assert_eq!(
            validate_machine_import_proposal_acceptance(&stale, &session, &rebuilt_session),
            Err(MachineImportProposalAcceptanceError::StaleProposalIdentity)
        );

        let premise = high_trust_fixture_module(
            CoreModule {
                name: Name::from_dotted("Policy.P"),
                declarations: vec![Decl::Axiom {
                    name: "Policy.P.ax".to_owned(),
                    universe_params: Vec::new(),
                    ty: prop(),
                }],
            },
            &[],
        );
        let allow_axiom = imported_axiom_allowlist_json(&premise, "Policy.P.ax");
        let eq_rec_hash = format_hash_string(
            &npa_cert::builtin_decl_interface_hash(&Name::from_dotted("Eq.rec")).unwrap(),
        );
        let allow_axiom_plus_builtin = format!(
            r#"[{{
              "kind":"imported",
              "module":"Policy.P",
              "name":"Policy.P.ax",
              "export_hash":"{}",
              "decl_interface_hash":"{}"
            }},{{
              "kind":"builtin",
              "name":"Eq.rec",
              "decl_interface_hash":"{}"
            }}]"#,
            format_hash_string(&premise.verified.export_hash()),
            format_hash_string(&export_interface_hash(&premise, "Policy.P.ax")),
            eq_rec_hash
        );
        let policy_base = create_machine_session(&session_json_for_modules(
            "Prop",
            &[&premise],
            &[&premise],
            &default_options_json(&allow_axiom),
        ))
        .unwrap()
        .session;
        let policy_changed = create_machine_session(&session_json_for_modules(
            "Prop",
            &[&premise],
            &[&premise],
            &default_options_json(&allow_axiom_plus_builtin),
        ))
        .unwrap()
        .session;
        let policy_base_fields = premise_search_ok_fields(
            search_machine_premises_for_goal(
                &premise_search_json(&policy_base, filters, ""),
                &policy_base,
            )
            .unwrap(),
        );
        let policy_changed_fields = premise_search_ok_fields(
            search_machine_premises_for_goal(
                &premise_search_json(&policy_changed, filters, ""),
                &policy_changed,
            )
            .unwrap(),
        );

        assert_ne!(
            policy_base_fields.retrieval_cache_key.environment_hash,
            policy_changed_fields.retrieval_cache_key.environment_hash
        );
        assert_ne!(
            policy_base_fields.retrieval_cache_key.key_hash,
            policy_changed_fields.retrieval_cache_key.key_hash
        );
    }

    #[test]
    fn axiom_aware_ranking_prefers_axiom_free_candidate_when_comparable() {
        let session = ai_search_exact_session("Prop");
        let state = initial_machine_state(&session);
        let requested_modes = vec![MachineTheoremMode::Exact];
        let free_entry = test_type_aware_entry(prop(), Vec::new(), requested_modes.clone());
        let mut axiom_entry = free_entry.clone();
        axiom_entry.export_kind = ExportKind::Axiom;
        axiom_entry.global_ref.name = Name::from_dotted("Test.ax");
        let allowed_axioms = theorem_entry_direct_axiom_refs(&axiom_entry);

        let free_ranking = type_aware_ranking_metadata_for_entry(
            &MachinePremiseRankingMetadata::score_only(0),
            &free_entry,
            PremiseRankingContext {
                state: &state,
                goal_id: npa_tactic::GoalId(0),
                requested_modes: &requested_modes,
                selected_modes: &requested_modes,
                suggested_candidates: &[],
                allowed_axioms: Some(&allowed_axioms),
                graph_snapshot_hash: None,
                source: MachinePremiseIndexSource::DirectImport,
                import_cost: 0,
            },
        );
        let axiom_ranking = type_aware_ranking_metadata_for_entry(
            &MachinePremiseRankingMetadata::score_only(0),
            &axiom_entry,
            PremiseRankingContext {
                state: &state,
                goal_id: npa_tactic::GoalId(0),
                requested_modes: &requested_modes,
                selected_modes: &requested_modes,
                suggested_candidates: &[],
                allowed_axioms: Some(&allowed_axioms),
                graph_snapshot_hash: None,
                source: MachinePremiseIndexSource::DirectImport,
                import_cost: 0,
            },
        );

        assert!(free_ranking.score > axiom_ranking.score);
        assert_eq!(free_ranking.axiom_ranking.direct_axiom_count, 0);
        assert_eq!(axiom_ranking.axiom_ranking.direct_axiom_count, 1);
        assert!(axiom_ranking.axiom_ranking.usable_under_axiom_policy);
        assert!(axiom_ranking.axiom_ranking.penalties.direct_axiom_use > 0);
    }

    #[test]
    fn axiom_aware_ranking_marks_disallowed_axiom_candidate_unusable() {
        let session = ai_search_exact_session("Prop");
        let state = initial_machine_state(&session);
        let requested_modes = vec![MachineTheoremMode::Exact];
        let mut axiom_entry = test_type_aware_entry(prop(), Vec::new(), requested_modes.clone());
        axiom_entry.export_kind = ExportKind::Axiom;
        axiom_entry.global_ref.name = Name::from_dotted("Test.disallowed_ax");
        let empty_allowlist = Vec::new();

        let ranking = type_aware_ranking_metadata_for_entry(
            &MachinePremiseRankingMetadata::score_only(0),
            &axiom_entry,
            PremiseRankingContext {
                state: &state,
                goal_id: npa_tactic::GoalId(0),
                requested_modes: &requested_modes,
                selected_modes: &requested_modes,
                suggested_candidates: &[],
                allowed_axioms: Some(&empty_allowlist),
                graph_snapshot_hash: None,
                source: MachinePremiseIndexSource::DirectImport,
                import_cost: 0,
            },
        );

        assert!(!ranking.axiom_ranking.usable_under_axiom_policy);
        assert_eq!(ranking.axiom_ranking.disallowed_axiom_count, 1);
        assert!(ranking.axiom_ranking.penalties.disallowed_axiom > 0);
        assert_eq!(ranking.score, 0);
        assert!(!theorem_entry_passes_filters(
            &axiom_entry,
            &MachineTheoremFilters {
                exclude_axioms: true,
                allowed_modules: MachineAllowedModulesFilter::AllDirect,
            }
        ));
    }

    #[test]
    fn axiom_aware_ranking_marks_unknown_package_theorem_level_and_round_trips() {
        let package_entry = npa_package::PackageTheoremIndexEntry {
            global_ref: npa_package::PackageGlobalRef {
                module: Name::from_dotted("Pkg.Unknown"),
                name: Name::from_dotted("Pkg.Unknown.t"),
                export_hash: test_package_hash(31),
                certificate_hash: test_package_hash(32),
                decl_interface_hash: test_package_hash(33),
            },
            kind: npa_package::PackageTheoremIndexKind::Theorem,
            statement: npa_package::PackageTheoremStatement {
                core_hash: test_package_hash(34),
                head: None,
                constants: Vec::new(),
            },
            modes: vec![npa_package::PackageTheoremIndexMode::Exact],
            tags: Vec::new(),
            axiom_dependencies: vec![npa_package::PackageAxiomReference {
                module: Name::from_dotted("Pkg.Axiom"),
                name: Name::from_dotted("Pkg.Axiom.choice"),
                export_hash: test_package_hash(36),
                decl_interface_hash: test_package_hash(37),
            }],
            module_axiom_report_hash: test_package_hash(35),
            artifact: npa_package::PackageTheoremIndexArtifact {
                origin: npa_package::PackageArtifactOrigin::Local,
                certificate: npa_package::PackagePath::new("Pkg/Unknown/t.npcert"),
            },
        };

        let projected =
            project_package_theorem_index_entry_to_verified_premise_entry(&package_entry).unwrap();

        assert_eq!(
            projected.ranking_metadata.axiom_ranking.theorem_level,
            MachinePremiseTheoremLevel::Unknown
        );
        assert!(!projected.ranking_metadata.axiom_ranking.candidate_verified);
        assert_eq!(
            projected
                .ranking_metadata
                .axiom_ranking
                .penalties
                .unknown_theorem_level,
            UNKNOWN_THEOREM_LEVEL_PENALTY
        );
        assert_eq!(
            projected
                .ranking_metadata
                .axiom_ranking
                .penalties
                .unverified_candidate,
            UNVERIFIED_CANDIDATE_PENALTY
        );
        assert_eq!(
            projected
                .ranking_metadata
                .axiom_ranking
                .penalties
                .high_import_cost,
            HIGH_IMPORT_COST_UNIT_PENALTY
        );
        assert_eq!(
            projected
                .ranking_metadata
                .axiom_ranking
                .penalties
                .transitive_axiom_expansion,
            TRANSITIVE_AXIOM_EXPANSION_PENALTY
        );
        assert!(projected
            .ranking_metadata
            .axiom_ranking
            .axiom_paths
            .iter()
            .any(|path| path.source == MachinePremiseAxiomPathSource::TransitiveDependency));
        assert!(projected.ranking_metadata.score < PREMISE_RANKING_BASE_SCORE);

        let json = premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(
            projected.clone(),
        )));
        assert_eq!(
            parse_premise_index_entry_json(&json).unwrap(),
            MachinePremiseIndexEntry::Verified(Box::new(projected))
        );
    }

    #[test]
    fn axiom_aware_ranking_graph_axiom_paths_are_penalized_in_premise_sets() {
        let graph_hash = test_hash(222);
        let goal_features = premise_set_goal_features(vec![test_hash(61)]);
        let entries = vec![test_premise_set_entry(
            "Set.Premises.axiom_path",
            vec![test_hash(61)],
            vec![test_imported_axiom(70)],
        )];

        let without_graph = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            None,
        );
        let with_graph = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            Some(graph_hash),
        );

        assert_eq!(with_graph.metadata.axiom_impact.direct_axiom_count, 0);
        assert_eq!(with_graph.metadata.axiom_impact.transitive_axiom_count, 1);
        assert!(with_graph
            .metadata
            .axiom_impact
            .axiom_paths
            .iter()
            .any(
                |path| path.source == MachinePremiseAxiomPathSource::GraphSnapshot
                    && path.graph_snapshot_hash == Some(graph_hash)
            ));
        assert!(
            with_graph.metadata.objective.axiom_cost_penalty
                > without_graph.metadata.objective.axiom_cost_penalty
        );
    }

    #[test]
    fn type_aware_retrieval_apply_records_unresolved_obligations() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;
        let response =
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("premise search should succeed");
        };
        let [result] = ok.endpoint_fields.results.as_slice() else {
            panic!("expected one premise result");
        };
        let metadata = &result.ranking_metadata.type_aware;

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Feasible);
        assert_eq!(metadata.selected_mode, Some(MachineTheoremMode::Apply));
        assert!(metadata.universe_compatible);
        assert!(metadata.head_compatible);
        assert!(metadata.result_fits_goal);
        assert_eq!(metadata.pi_binder_count, 1);
        assert_eq!(metadata.unresolved_obligation_type_hashes.len(), 1);
        assert!(metadata.local_context_match_type_hashes.is_empty());
        assert!(metadata.generated_argument_sources.is_empty());
        assert_eq!(metadata.estimated_new_goals, 1);
        assert!(metadata.premise_size > 0);
        assert!(metadata.goal_size > 0);
        assert_eq!(
            result
                .ranking_metadata
                .axiom_ranking
                .penalties
                .unresolved_premise_obligations,
            UNRESOLVED_PREMISE_OBLIGATION_PENALTY
        );
    }

    #[test]
    fn type_aware_retrieval_rewrite_records_feasible_rewrite_without_solving_goal() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let response =
            search_machine_premises_for_goal(&premise_search_json(&session, filters, ""), &session)
                .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("premise search should succeed");
        };
        let [result] = ok.endpoint_fields.results.as_slice() else {
            panic!("expected one premise result");
        };
        let metadata = &result.ranking_metadata.type_aware;

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Feasible);
        assert_eq!(metadata.selected_mode, Some(MachineTheoremMode::Rw));
        assert!(metadata.universe_compatible);
        assert!(metadata.head_compatible);
        assert!(!metadata.result_fits_goal);
        assert_eq!(metadata.pi_binder_count, 0);
        assert!(metadata.unresolved_obligation_type_hashes.is_empty());
        assert_eq!(metadata.estimated_new_goals, 0);
    }

    #[test]
    fn type_aware_retrieval_local_context_generates_argument_candidate() {
        let session = imported_axiom_session();
        let state = initial_machine_state(&session);
        let entry = test_type_aware_entry(
            Expr::pi("h", prop(), prop()),
            Vec::new(),
            vec![MachineTheoremMode::Apply],
        );
        let goal = npa_tactic::MachineGoal {
            id: npa_tactic::GoalId(0),
            meta_id: npa_tactic::MetaVarId(0),
            context: vec![npa_tactic::MachineLocalDecl::assumption("hp", prop())],
            context_hash: test_hash(201),
            target: prop(),
            target_hash: npa_cert::core_expr_hash(&prop()),
        };
        let metadata = type_aware_premise_metadata_for_goal(
            &entry,
            state.env.kernel_env(),
            &state.root.universe_params,
            &goal,
            &[MachineTheoremMode::Apply],
        );

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Feasible);
        assert_eq!(metadata.selected_mode, Some(MachineTheoremMode::Apply));
        assert!(metadata.unresolved_obligation_type_hashes.is_empty());
        assert_eq!(metadata.local_context_match_type_hashes.len(), 1);
        assert_eq!(
            metadata.generated_argument_sources,
            vec![MachineTypeAwareArgumentSource::LocalContext]
        );
        assert_eq!(metadata.estimated_new_goals, 0);
    }

    #[test]
    fn type_aware_retrieval_universe_argument_can_be_inferred_from_target() {
        let session = imported_axiom_session();
        let state = initial_machine_state(&session);
        let entry = test_type_aware_entry(
            Expr::konst("P", vec![Level::param("u")]),
            vec!["u".to_owned()],
            vec![MachineTheoremMode::Exact],
        );
        let target = Expr::konst("P", vec![Level::zero()]);
        let goal = npa_tactic::MachineGoal {
            id: npa_tactic::GoalId(0),
            meta_id: npa_tactic::MetaVarId(0),
            context: Vec::new(),
            context_hash: test_hash(204),
            target: target.clone(),
            target_hash: npa_cert::core_expr_hash(&target),
        };
        let metadata = type_aware_premise_metadata_for_goal(
            &entry,
            state.env.kernel_env(),
            &state.root.universe_params,
            &goal,
            &[MachineTheoremMode::Exact],
        );

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Feasible);
        assert_eq!(metadata.selected_mode, Some(MachineTheoremMode::Exact));
        assert!(metadata.universe_compatible);
        assert!(metadata.result_fits_goal);
        assert_eq!(
            metadata.generated_argument_sources,
            vec![MachineTypeAwareArgumentSource::InferFromTarget]
        );
    }

    #[test]
    fn type_aware_retrieval_incompatible_heads_are_infeasible() {
        let session = imported_axiom_session();
        let state = initial_machine_state(&session);
        let entry = test_type_aware_entry(
            nat(),
            Vec::new(),
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply],
        );
        let goal = npa_tactic::MachineGoal {
            id: npa_tactic::GoalId(0),
            meta_id: npa_tactic::MetaVarId(0),
            context: Vec::new(),
            context_hash: test_hash(202),
            target: prop(),
            target_hash: npa_cert::core_expr_hash(&prop()),
        };
        let metadata = type_aware_premise_metadata_for_goal(
            &entry,
            state.env.kernel_env(),
            &state.root.universe_params,
            &goal,
            &[MachineTheoremMode::Exact, MachineTheoremMode::Apply],
        );

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Infeasible);
        assert_eq!(metadata.selected_mode, None);
        assert!(metadata.universe_compatible);
        assert!(!metadata.head_compatible);
        assert!(!metadata.result_fits_goal);
    }

    #[test]
    fn type_aware_retrieval_rejects_incompatible_universe_constraints() {
        let session = imported_axiom_session();
        let state = initial_machine_state(&session);
        let entry = test_type_aware_entry(
            Expr::konst("P", vec![Level::param("u"), Level::param("u")]),
            vec!["u".to_owned()],
            vec![MachineTheoremMode::Exact],
        );
        let target = Expr::konst("P", vec![Level::zero(), Level::succ(Level::zero())]);
        let goal = npa_tactic::MachineGoal {
            id: npa_tactic::GoalId(0),
            meta_id: npa_tactic::MetaVarId(0),
            context: Vec::new(),
            context_hash: test_hash(203),
            target: target.clone(),
            target_hash: npa_cert::core_expr_hash(&target),
        };
        let metadata = type_aware_premise_metadata_for_goal(
            &entry,
            state.env.kernel_env(),
            &state.root.universe_params,
            &goal,
            &[MachineTheoremMode::Exact],
        );

        assert_eq!(metadata.status, MachineTypeAwarePremiseStatus::Infeasible);
        assert_eq!(metadata.selected_mode, None);
        assert!(!metadata.universe_compatible);
        assert!(!metadata.result_fits_goal);
    }

    #[test]
    fn retrieval_modes_parse_all_modes_in_canonical_order() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;
        let request = parse_machine_premise_search_request(&premise_search_json_full(
            &session,
            "g0",
            r#"[
                "premise_set",
                "lexical",
                "rw",
                "constructor_support",
                "exact",
                "proof_analogy",
                "type_aware",
                "simp",
                "graph_aware",
                "apply",
                "embedding",
                "induction_support"
            ]"#,
            filters,
            &format_hash_string(&session.initial_snapshot.state_fingerprint),
            "",
        ))
        .unwrap();

        assert_eq!(
            request.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
                MachineTheoremMode::ConstructorSupport,
                MachineTheoremMode::InductionSupport,
                MachineTheoremMode::TypeAware,
                MachineTheoremMode::Lexical,
                MachineTheoremMode::GraphAware,
                MachineTheoremMode::Embedding,
                MachineTheoremMode::ProofAnalogy,
                MachineTheoremMode::PremiseSet,
            ]
        );
    }

    #[test]
    fn retrieval_modes_combined_request_reports_stable_mode_metadata() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let modes = r#"[
            "lexical",
            "type_aware",
            "rw",
            "simp",
            "graph_aware",
            "embedding",
            "proof_analogy",
            "premise_set",
            "constructor_support",
            "induction_support"
        ]"#;
        let first = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                modes,
                filters,
                &format_hash_string(&session.initial_snapshot.state_fingerprint),
                "",
            ),
            &session,
        )
        .unwrap();
        let second = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                modes,
                filters,
                &format_hash_string(&session.initial_snapshot.state_fingerprint),
                "",
            ),
            &session,
        )
        .unwrap();

        let (first_fields, second_fields) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("combined retrieval-mode premise search should succeed"),
        };
        assert_eq!(first_fields.results, second_fields.results);
        let [result] = first_fields.results.as_slice() else {
            panic!("expected one premise result");
        };

        assert_eq!(
            result.selected_modes,
            vec![
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
                MachineTheoremMode::ConstructorSupport,
                MachineTheoremMode::InductionSupport,
                MachineTheoremMode::TypeAware,
                MachineTheoremMode::Lexical,
                MachineTheoremMode::PremiseSet,
            ]
        );
        assert_eq!(
            result
                .ranking_metadata
                .mode_metadata
                .iter()
                .map(|metadata| metadata.mode)
                .collect::<Vec<_>>(),
            vec![
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
                MachineTheoremMode::ConstructorSupport,
                MachineTheoremMode::InductionSupport,
                MachineTheoremMode::TypeAware,
                MachineTheoremMode::Lexical,
                MachineTheoremMode::GraphAware,
                MachineTheoremMode::Embedding,
                MachineTheoremMode::ProofAnalogy,
                MachineTheoremMode::PremiseSet,
            ]
        );

        let rw = premise_mode_metadata(result, MachineTheoremMode::Rw);
        assert_eq!(rw.status, MachinePremiseModeStatus::Supported);
        assert_eq!(rw.reason, MachinePremiseModeReason::EntryModeMatched);
        assert_eq!(rw.suggested_candidate_count, 1);

        let simp = premise_mode_metadata(result, MachineTheoremMode::Simp);
        assert_eq!(simp.status, MachinePremiseModeStatus::Supported);
        assert_eq!(simp.reason, MachinePremiseModeReason::EntryModeMatched);
        assert_eq!(simp.suggested_candidate_count, 1);

        for mode in [
            MachineTheoremMode::ConstructorSupport,
            MachineTheoremMode::InductionSupport,
        ] {
            let metadata = premise_mode_metadata(result, mode);
            assert_eq!(metadata.status, MachinePremiseModeStatus::Supported);
            assert_eq!(
                metadata.reason,
                MachinePremiseModeReason::VerifiedInductiveMetadata
            );
        }

        let type_aware = premise_mode_metadata(result, MachineTheoremMode::TypeAware);
        assert_eq!(type_aware.status, MachinePremiseModeStatus::Supported);
        assert_eq!(
            type_aware.reason,
            MachinePremiseModeReason::TypeAwareFeasible
        );
        assert_eq!(
            result.ranking_metadata.type_aware.selected_mode,
            Some(MachineTheoremMode::Rw)
        );

        let lexical = premise_mode_metadata(result, MachineTheoremMode::Lexical);
        assert_eq!(lexical.status, MachinePremiseModeStatus::Supported);
        assert_eq!(lexical.reason, MachinePremiseModeReason::LexicalSignal);
        assert!(lexical.lexical_score > 0);

        for mode in [
            MachineTheoremMode::GraphAware,
            MachineTheoremMode::Embedding,
            MachineTheoremMode::ProofAnalogy,
        ] {
            let metadata = premise_mode_metadata(result, mode);
            assert_eq!(metadata.status, MachinePremiseModeStatus::Unavailable);
            assert_eq!(
                metadata.reason,
                MachinePremiseModeReason::SidecarUnavailable
            );
            assert_eq!(metadata.suggested_candidate_count, 0);
        }
        let premise_set = premise_mode_metadata(result, MachineTheoremMode::PremiseSet);
        assert_eq!(premise_set.status, MachinePremiseModeStatus::Supported);
        assert_eq!(
            premise_set.reason,
            MachinePremiseModeReason::PremiseSetSelected
        );
        assert!(result.ranking_metadata.premise_set.is_some());
        assert_eq!(result.untrusted_sidecar.suggested_candidates.len(), 2);
    }

    #[test]
    fn retrieval_modes_sidecar_only_request_uses_premise_set_without_graph_sidecar() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let response = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                r#"["graph_aware","embedding","proof_analogy","premise_set"]"#,
                filters,
                &format_hash_string(&session.initial_snapshot.state_fingerprint),
                "",
            ),
            &session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("sidecar-only retrieval-mode request should succeed");
        };

        assert_eq!(
            ok.endpoint_fields.selected_modes,
            vec![
                MachineTheoremMode::GraphAware,
                MachineTheoremMode::Embedding,
                MachineTheoremMode::ProofAnalogy,
                MachineTheoremMode::PremiseSet,
            ]
        );
        let [result] = ok.endpoint_fields.results.as_slice() else {
            panic!("premise-set should run even when graph-like sidecars are unavailable");
        };
        assert_eq!(result.selected_modes, vec![MachineTheoremMode::PremiseSet]);
        assert_eq!(
            result
                .ranking_metadata
                .premise_set
                .as_ref()
                .unwrap()
                .graph_snapshot_hash,
            None
        );
    }

    #[test]
    fn retrieval_modes_lexical_preserves_verified_identity_boundary() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;
        let response = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                r#"["lexical"]"#,
                filters,
                &format_hash_string(&session.initial_snapshot.state_fingerprint),
                "",
            ),
            &session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("lexical retrieval-mode request should succeed");
        };
        let [result] = ok.endpoint_fields.results.as_slice() else {
            panic!("expected one lexical premise result");
        };

        assert_eq!(result.selected_modes, vec![MachineTheoremMode::Lexical]);
        assert_eq!(result.verified_identity.module, Name::from_dotted("A"));
        assert_eq!(
            result.verified_identity.global_ref.name,
            Name::from_dotted("A.id")
        );
        assert_eq!(
            result.verified_identity.statement_core_hash,
            result.statement_core_hash
        );
        assert_eq!(
            result.candidate_provenance.premise_source,
            MachinePremiseIndexSource::DirectImport
        );
        assert!(result.untrusted_sidecar.suggested_candidates.is_empty());

        let lexical = premise_mode_metadata(result, MachineTheoremMode::Lexical);
        assert_eq!(lexical.status, MachinePremiseModeStatus::Supported);
        assert_eq!(lexical.reason, MachinePremiseModeReason::LexicalNoSignal);
        assert_eq!(lexical.lexical_score, 0);
    }

    #[test]
    fn retrieval_modes_inductive_support_requires_verified_structural_metadata() {
        let axiom_session = imported_axiom_session();
        let axiom_filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;
        let axiom_response = search_machine_premises_for_goal(
            &premise_search_json_full(
                &axiom_session,
                "g0",
                r#"["constructor_support","induction_support"]"#,
                axiom_filters,
                &format_hash_string(&axiom_session.initial_snapshot.state_fingerprint),
                "",
            ),
            &axiom_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(axiom_ok) = axiom_response else {
            panic!("constructor/induction request should succeed");
        };
        assert!(axiom_ok.endpoint_fields.results.is_empty());

        let simp_session = ai_search_retrieval_session();
        let simp_filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let simp_response = search_machine_premises_for_goal(
            &premise_search_json_full(
                &simp_session,
                "g0",
                r#"["constructor_support","induction_support"]"#,
                simp_filters,
                &format_hash_string(&simp_session.initial_snapshot.state_fingerprint),
                "",
            ),
            &simp_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(simp_ok) = simp_response else {
            panic!("verified inductive metadata request should succeed");
        };
        let [result] = simp_ok.endpoint_fields.results.as_slice() else {
            panic!("expected one inductive-support premise result");
        };

        assert_eq!(
            result.selected_modes,
            vec![
                MachineTheoremMode::ConstructorSupport,
                MachineTheoremMode::InductionSupport,
            ]
        );
        for mode in [
            MachineTheoremMode::ConstructorSupport,
            MachineTheoremMode::InductionSupport,
        ] {
            let metadata = premise_mode_metadata(result, mode);
            assert_eq!(metadata.status, MachinePremiseModeStatus::Supported);
            assert_eq!(
                metadata.reason,
                MachinePremiseModeReason::VerifiedInductiveMetadata
            );
        }
    }

    #[test]
    fn premise_set_retrieval_empty_candidate_set_reports_missing_goal_features() {
        let goal_features = premise_set_goal_features(vec![test_hash(1), test_hash(2)]);

        let plan = greedy_machine_premise_set_plan(&goal_features, Vec::new(), 4, None);

        assert!(plan.selected_sort_keys.is_empty());
        assert!(plan.metadata.selected_premises.is_empty());
        assert!(plan.metadata.covered_goal_features.is_empty());
        assert_eq!(
            plan.metadata.missing_goal_features,
            goal_features.iter().cloned().collect::<Vec<_>>()
        );
        assert!(plan.metadata.rejected_alternatives.is_empty());
        assert_eq!(plan.metadata.objective.final_score, 0);
    }

    #[test]
    fn premise_set_retrieval_rejects_duplicate_candidates_without_double_counting() {
        let goal_features = premise_set_goal_features(vec![test_hash(11)]);
        let first = test_premise_set_entry("Set.Premises.same", vec![test_hash(11)], Vec::new());
        let duplicate = first.clone();
        let entries = vec![first, duplicate];

        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            None,
        );

        assert_eq!(plan.metadata.selected_premises.len(), 1);
        assert_eq!(plan.metadata.covered_goal_features.len(), 1);
        assert_eq!(plan.metadata.rejected_alternatives.len(), 1);
        assert_eq!(
            plan.metadata.rejected_alternatives[0].reason,
            MachinePremiseSetRejectedReason::DuplicateCandidate
        );
    }

    #[test]
    fn premise_set_retrieval_respects_maximum_set_size_and_records_rejected_alternative() {
        let goal_features = premise_set_goal_features(vec![test_hash(21), test_hash(22)]);
        let first = test_premise_set_entry("Set.Premises.a", vec![test_hash(21)], Vec::new());
        let second = test_premise_set_entry("Set.Premises.b", vec![test_hash(22)], Vec::new());
        let entries = vec![first, second];

        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            1,
            None,
        );

        assert_eq!(plan.metadata.max_set_size, 1);
        assert_eq!(plan.metadata.selected_premises.len(), 1);
        assert_eq!(plan.metadata.covered_goal_features.len(), 1);
        assert_eq!(plan.metadata.missing_goal_features.len(), 1);
        assert_eq!(plan.metadata.rejected_alternatives.len(), 1);
        assert_eq!(
            plan.metadata.rejected_alternatives[0].reason,
            MachinePremiseSetRejectedReason::MaxSetSizeReached
        );
    }

    #[test]
    fn premise_set_retrieval_runs_without_graph_sidecar_and_includes_cost_penalties() {
        let goal_features = premise_set_goal_features(vec![test_hash(31)]);
        let entry = test_premise_set_entry(
            "Set.Premises.axiom_cost",
            vec![test_hash(31)],
            vec![test_imported_axiom(80)],
        );
        let entries = vec![entry];

        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            None,
        );

        let selected = &plan.metadata.selected_premises[0];
        assert_eq!(plan.metadata.graph_snapshot_hash, None);
        assert_eq!(selected.objective.graph_connectivity_score, 0);
        assert_eq!(selected.objective.historical_co_use_score, 0);
        assert_eq!(selected.objective.import_cost_penalty, 0);
        assert_eq!(selected.objective.axiom_cost_penalty, 50);
        assert_eq!(plan.metadata.axiom_impact.transitive_axiom_count, 1);
    }

    #[test]
    fn premise_set_retrieval_explains_positive_coverage_rejected_by_cost() {
        let goal_features = premise_set_goal_features(vec![test_hash(36)]);
        let expensive = test_premise_set_entry(
            "Set.Premises.expensive_axioms",
            vec![test_hash(36)],
            (0..25).map(test_imported_axiom).collect(),
        );
        let entries = vec![expensive];

        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            None,
        );

        assert!(plan.metadata.selected_premises.is_empty());
        let [rejected] = plan.metadata.rejected_alternatives.as_slice() else {
            panic!("expected one rejected alternative");
        };
        assert_eq!(
            rejected.reason,
            MachinePremiseSetRejectedReason::NonPositiveObjective
        );
        assert_eq!(rejected.would_add_features.len(), 1);
        assert_eq!(rejected.objective.final_score, 0);
    }

    #[test]
    fn premise_set_retrieval_disconnected_graph_hash_keeps_graph_score_zero() {
        let goal_features = premise_set_goal_features(vec![test_hash(41)]);
        let entry =
            test_premise_set_entry("Set.Premises.graphless", vec![test_hash(41)], Vec::new());
        let entries = vec![entry];
        let graph_hash = test_hash(44);

        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            Some(graph_hash),
        );

        assert_eq!(plan.metadata.graph_snapshot_hash, Some(graph_hash));
        assert_eq!(plan.metadata.objective.graph_connectivity_score, 0);
        assert_eq!(plan.metadata.selected_premises.len(), 1);
    }

    #[test]
    fn premise_set_retrieval_tie_breaks_by_verified_premise_identity() {
        let goal_features = premise_set_goal_features(vec![test_hash(51)]);
        let later =
            test_premise_set_entry("Set.Premises.b_earlier", vec![test_hash(51)], Vec::new());
        let earlier =
            test_premise_set_entry("Set.Premises.a_earlier", vec![test_hash(51)], Vec::new());
        let entries = vec![later, earlier];

        let first = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            1,
            None,
        );
        let second = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            1,
            None,
        );

        assert_eq!(first, second);
        assert_eq!(
            first.metadata.selected_premises[0].premise.name,
            Name::from_dotted("Set.Premises.a_earlier")
        );
    }

    #[test]
    fn premise_set_retrieval_search_mode_returns_verified_visible_set_metadata() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let response = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                r#"["premise_set"]"#,
                filters,
                &format_hash_string(&session.initial_snapshot.state_fingerprint),
                "",
            ),
            &session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("premise-set retrieval should succeed");
        };
        let [result] = ok.endpoint_fields.results.as_slice() else {
            panic!("expected one selected premise-set result");
        };

        assert_eq!(result.selected_modes, vec![MachineTheoremMode::PremiseSet]);
        assert_eq!(
            result.candidate_provenance.premise_source,
            MachinePremiseIndexSource::DirectImport
        );
        assert!(result.untrusted_sidecar.suggested_candidates.is_empty());
        let premise_set = result
            .ranking_metadata
            .premise_set
            .as_ref()
            .expect("selected premise-set result records set metadata");
        assert_eq!(premise_set.selected_premises.len(), 1);
        assert_eq!(
            premise_set.import_requirements,
            vec![Name::from_dotted("Lib.Simp")]
        );
        assert!(premise_set.objective.coverage_score > 0);
        let metadata = premise_mode_metadata(result, MachineTheoremMode::PremiseSet);
        assert_eq!(metadata.status, MachinePremiseModeStatus::Supported);
        assert_eq!(
            metadata.reason,
            MachinePremiseModeReason::PremiseSetSelected
        );
    }

    #[test]
    fn premise_set_retrieval_metadata_round_trips_through_verified_index_json() {
        let goal_features = premise_set_goal_features(vec![test_hash(61)]);
        let candidate =
            test_premise_set_entry("Set.Premises.roundtrip", vec![test_hash(61)], Vec::new());
        let entries = vec![candidate];
        let plan = greedy_machine_premise_set_plan(
            &goal_features,
            premise_set_candidates(&entries),
            4,
            None,
        );
        let mut entry = test_verified_premise_entry(7);
        entry.ranking_metadata.premise_set = Some(plan.metadata);

        let json =
            premise_index_entry_json(&MachinePremiseIndexEntry::Verified(Box::new(entry.clone())));
        let parsed = parse_premise_index_entry_json(&json).unwrap();

        assert_eq!(parsed, MachinePremiseIndexEntry::Verified(Box::new(entry)));
    }

    #[test]
    fn search_query_fingerprint_changes_for_required_inputs() {
        let filters = MachineTheoremFilters {
            exclude_axioms: false,
            allowed_modules: MachineAllowedModulesFilter::Explicit(vec![Name::from_dotted("A")]),
        };
        let excluded_axiom_filters = MachineTheoremFilters {
            exclude_axioms: true,
            allowed_modules: MachineAllowedModulesFilter::Explicit(vec![Name::from_dotted("A")]),
        };
        let modes = vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply];
        let exact_only_modes = vec![MachineTheoremMode::Exact];
        let profile_hash = premise_search_query_profile_hash(PREMISE_SEARCH_QUERY_PROFILE_VERSION);
        let fingerprint = |state_fingerprint: Hash,
                           goal_id: npa_tactic::GoalId,
                           goal_fingerprint: Hash,
                           goal_context_hash: Hash,
                           local_name_map_hash: Hash,
                           visible_imports_fingerprint: Hash,
                           theorem_index_fingerprint: Hash,
                           query_profile_hash: Hash,
                           graph_snapshot_hash: Option<Hash>,
                           modes: &[MachineTheoremMode],
                           filters: &MachineTheoremFilters,
                           limit: u32| {
            premise_query_fingerprint(PremiseQueryFingerprintInput {
                protocol_version: crate::MachineApiVersion::V1,
                state_fingerprint,
                goal_id,
                goal_fingerprint,
                goal_context_hash,
                local_name_map_hash,
                visible_imports_fingerprint,
                theorem_index_fingerprint,
                query_profile_hash,
                graph_snapshot_hash,
                modes,
                filters,
                limit,
            })
        };
        let base = fingerprint(
            test_hash(1),
            npa_tactic::GoalId(0),
            test_hash(2),
            test_hash(3),
            test_hash(4),
            test_hash(5),
            test_hash(6),
            profile_hash,
            None,
            &modes,
            &filters,
            20,
        );

        for changed in [
            fingerprint(
                test_hash(11),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(1),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(12),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(13),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(14),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(15),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(16),
                profile_hash,
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                premise_search_query_profile_hash(
                    "npa.machine-api.premise-search-query-profile.v2",
                ),
                None,
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                Some(test_hash(17)),
                &modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &exact_only_modes,
                &filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &excluded_axiom_filters,
                20,
            ),
            fingerprint(
                test_hash(1),
                npa_tactic::GoalId(0),
                test_hash(2),
                test_hash(3),
                test_hash(4),
                test_hash(5),
                test_hash(6),
                profile_hash,
                None,
                &modes,
                &filters,
                21,
            ),
        ] {
            assert_ne!(base, changed);
        }
    }

    #[test]
    fn search_query_fingerprint_premise_search_errors_are_typed() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;

        let invalid_mode = parse_machine_premise_search_request(&premise_search_json_full(
            &session,
            "g0",
            r#"["not_a_mode"]"#,
            filters,
            &format_hash_string(&session.initial_snapshot.state_fingerprint),
            "",
        ))
        .unwrap_err();
        assert_eq!(invalid_mode.kind, MachineApiErrorKind::InvalidTheoremQuery);

        let stale_state = search_machine_premises_for_goal(
            &premise_search_json_full(
                &session,
                "g0",
                r#"["exact"]"#,
                filters,
                &format_hash_string(&test_hash(222)),
                "",
            ),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            stale_state.diagnostic.kind,
            MachineApiErrorKind::StateFingerprintMismatch
        );

        let unknown_goal = search_machine_premises_for_goal(
            &premise_search_json_for_goal(&session, "g99", filters, ""),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            unknown_goal.diagnostic.kind,
            MachineApiErrorKind::GoalNotOpen
        );

        let invalid_module = search_machine_premises_for_goal(
            &premise_search_json(
                &session,
                r#"{"exclude_axioms":false,"allowed_modules":["Missing"]}"#,
                "",
            ),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            invalid_module.diagnostic.kind,
            MachineApiErrorKind::InvalidTheoremQuery
        );

        let mismatch_extra = format!(
            r#""expected_theorem_index_fingerprint":"{}""#,
            format_hash_string(&test_hash(223))
        );
        let mismatch = search_machine_premises_for_goal(
            &premise_search_json(&session, filters, &mismatch_extra),
            &session,
        )
        .unwrap_err();
        assert_eq!(
            mismatch.diagnostic.kind,
            MachineApiErrorKind::TheoremIndexFingerprintMismatch
        );
    }

    #[test]
    fn ai_search_stale_global_ref_candidate_is_rejected_by_machine_api_batch() {
        let session = ai_search_retrieval_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Lib.Simp"]}"#;
        let response =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("ai_search retrieval search should succeed");
        };
        let result = &ok.endpoint_fields.results[0];
        let mut candidate = result.suggested_candidates[0].candidate.clone();
        let MachineTacticCandidate::Rewrite { rule, .. } = &mut candidate else {
            panic!("first candidate should be rw");
        };
        let TacticHead::Imported {
            decl_interface_hash,
            ..
        } = &mut rule.head
        else {
            panic!("rw head should be imported");
        };
        decl_interface_hash[0] ^= 0x80;
        let stale_candidate = suggested_candidate_json(&candidate);
        let mut batch_session = ai_search_retrieval_session();
        let batch_response = run_machine_tactic_batch_request(
            &ai_search_batch_json(
                &batch_session,
                &format!("[{}]", batch_candidate_json("stale", &stale_candidate)),
            ),
            &mut batch_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(batch_ok) = batch_response else {
            panic!("batch should report stale candidate as item error");
        };
        assert_eq!(batch_ok.endpoint_fields.success_count, 0);
        assert_eq!(batch_ok.endpoint_fields.failure_count, 1);
        let [MachineTacticBatchItemResponse::Error {
            candidate_hash: Some(_),
            diagnostic,
            ..
        }] = batch_ok.endpoint_fields.results.as_slice()
        else {
            panic!("stale global ref should be rejected after candidate canonicalization");
        };
        assert_eq!(diagnostic.error_kind, MachineApiErrorKind::InvalidCandidate);
    }

    #[test]
    fn search_returns_direct_imported_axiom_metadata_deterministically() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#;
        let first =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();
        let second =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();

        let (first_fields, second_fields) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("search should succeed"),
        };

        assert_eq!(
            first_fields.query_fingerprint,
            second_fields.query_fingerprint
        );
        assert_eq!(
            first_fields.theorem_index_fingerprint,
            second_fields.theorem_index_fingerprint
        );
        assert_eq!(first_fields.results.len(), 1);

        let result = &first_fields.results[0];
        assert_eq!(result.premise_id, "prem_0");
        assert_eq!(result.global_ref.module, Name::from_dotted("A"));
        assert_eq!(result.global_ref.name, Name::from_dotted("A.id"));
        assert_eq!(
            result.modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply]
        );
        assert_eq!(result.statement.machine, "forall (x : Prop), Prop");
        assert_eq!(result.suggested_candidates, Vec::new());
        assert_eq!(result.score, 0);
        assert_eq!(result.axioms_used.len(), 1);
    }

    #[test]
    fn premise_index_direct_import_builder_records_structural_features_deterministically() {
        let session = imported_axiom_session();
        let snapshot_context = MachineSnapshotMaterializationContext {
            session_id: &session.session_id,
            display_scope: &session.machine_display_render_scope,
            callable_interface_table: &session.machine_surface_callable_interface_table,
        };
        let state = session
            .snapshots
            .lookup_checked(
                &snapshot_context,
                session.initial_snapshot.snapshot_id,
                session.initial_snapshot.state_fingerprint,
            )
            .unwrap()
            .executable_state_payload
            .clone();

        let first = build_verified_premise_index_for_state(&session, &state).unwrap();
        let second = build_verified_premise_index_for_state(&session, &state).unwrap();

        assert_eq!(first, second);
        assert_eq!(first.entries.len(), 1);
        let entry = &first.entries[0];
        assert_eq!(entry.source, MachinePremiseIndexSource::DirectImport);
        assert_eq!(entry.identity.module, Name::from_dotted("A"));
        assert_eq!(entry.identity.global_ref.name, Name::from_dotted("A.id"));
        assert_eq!(entry.structural_features.pi_binder_count, 1);
        assert_eq!(
            entry
                .structural_features
                .argument_universe_fingerprints
                .len(),
            1
        );
        assert_eq!(
            entry
                .structural_features
                .normalized_expression_fingerprints
                .len(),
            3
        );
        assert!(entry
            .structural_features
            .propositional_connectives
            .contains(&MachinePremisePropositionalConnective::Forall));
        assert!(entry.structural_features.target_head.is_none());
        assert!(entry.structural_features.referenced_inductives.is_empty());
    }

    #[test]
    fn premise_index_direct_import_builder_extracts_equality_and_inductive_features() {
        let session = ai_search_retrieval_session();
        let snapshot_context = MachineSnapshotMaterializationContext {
            session_id: &session.session_id,
            display_scope: &session.machine_display_render_scope,
            callable_interface_table: &session.machine_surface_callable_interface_table,
        };
        let state = session
            .snapshots
            .lookup_checked(
                &snapshot_context,
                session.initial_snapshot.snapshot_id,
                session.initial_snapshot.state_fingerprint,
            )
            .unwrap()
            .executable_state_payload
            .clone();

        let index = build_verified_premise_index_for_state(&session, &state).unwrap();
        let entry = index
            .entries
            .iter()
            .find(|entry| entry.identity.global_ref.name == Name::from_dotted("Lib.one_unfold"))
            .expect("retrieval fixture theorem should be indexed");
        let features = &entry.structural_features;

        assert!(features
            .target_head
            .as_ref()
            .is_some_and(|reference| reference.name == Name::from_dotted("Eq")));
        assert!(features
            .equality_lhs_head
            .as_ref()
            .is_some_and(|reference| reference.name == Name::from_dotted("Lib.one")));
        assert!(features
            .equality_rhs_head
            .as_ref()
            .is_some_and(|reference| reference.name == Name::from_dotted("Nat.succ")));
        assert!(features
            .referenced_inductives
            .iter()
            .any(|reference| reference.name == Name::from_dotted("Eq")));
        assert!(features
            .referenced_inductives
            .iter()
            .any(|reference| reference.name == Name::from_dotted("Nat")));
    }

    #[test]
    fn search_exclude_axioms_filters_axiom_dependencies() {
        let session = imported_axiom_session();
        let filters = r#"{"exclude_axioms":true,"allowed_modules":["A"]}"#;
        let response =
            search_machine_theorems_for_goal(&search_json(&session, filters), &session).unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("search should succeed");
        };
        assert!(ok.endpoint_fields.results.is_empty());
    }

    #[test]
    fn search_rejects_non_direct_allowed_module_before_snapshot_lookup() {
        let session = imported_axiom_session();
        let body = search_json(
            &session,
            r#"{"exclude_axioms":false,"allowed_modules":["Missing"]}"#,
        );
        let err = search_machine_theorems_for_goal(&body, &session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidTheoremQuery
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::RequestValidation
        );
    }

    #[test]
    fn search_rejects_non_direct_allowed_module_before_snapshot_store_invariant() {
        let mut session = imported_axiom_session();
        let body = search_json(
            &session,
            r#"{"exclude_axioms":false,"allowed_modules":["Missing"]}"#,
        );
        session.snapshots =
            crate::MachineSnapshotStore::new(SessionId::new_unchecked("msess_other"));

        let err = search_machine_theorems_for_goal(&body, &session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidTheoremQuery
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::RequestValidation
        );
    }

    #[test]
    fn search_goal_not_open_returns_structured_error() {
        let session = imported_axiom_session();
        let body = search_json_for_goal(
            &session,
            "g99",
            r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#,
        );
        let err = search_machine_theorems_for_goal(&body, &session).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::GoalNotOpen);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
        assert_eq!(err.diagnostic.goal_id, Some(npa_tactic::GoalId(99)));
        match err.response {
            MachineApiResponseEnvelope::Error(error) => {
                assert_eq!(error.error.kind, MachineApiErrorKind::GoalNotOpen);
                assert_eq!(error.error.goal_id, Some(npa_tactic::GoalId(99)));
            }
            MachineApiResponseEnvelope::Ok(_) => panic!("search should fail"),
            MachineApiResponseEnvelope::SchedulerStopped(_) => panic!("search should fail"),
        }
    }

    #[test]
    fn search_renders_transitive_statement_ref_with_display_extension() {
        let base = imported_axiom_session();
        let snapshot_context = MachineSnapshotMaterializationContext {
            session_id: &base.session_id,
            display_scope: &base.machine_display_render_scope,
            callable_interface_table: &base.machine_surface_callable_interface_table,
        };
        let state = base
            .snapshots
            .lookup_checked(
                &snapshot_context,
                base.initial_snapshot.snapshot_id,
                base.initial_snapshot.state_fingerprint,
            )
            .unwrap()
            .executable_state_payload
            .clone();
        let context = head_collision_context();
        let display_scope = direct_axiom_display_scope(&context, "A");
        let mut session = base;
        session.import_certificate_context = context;
        session.machine_display_render_scope = display_scope;

        let index = build_theorem_index(&session, &state).unwrap();
        let entry = index
            .entries
            .iter()
            .find(|entry| entry.global_ref.name == Name::from_dotted("A.t"))
            .unwrap();
        let Some(MachineGlobalRefView::Imported {
            module,
            name,
            public_export,
            tactic_head_visible,
            ..
        }) = entry.head.as_ref()
        else {
            panic!("transitive theorem statement head should resolve to an imported ref");
        };

        assert_eq!(module, &Name::from_dotted("P"));
        assert_eq!(name, &Name::from_dotted("X"));
        assert!(*public_export);
        assert!(!*tactic_head_visible);
        assert_eq!(render_statement(&session, entry).unwrap().machine, "X");
    }

    #[test]
    fn search_rejects_head_name_collision_with_transitive_owner() {
        let base = imported_axiom_session();
        let snapshot_context = MachineSnapshotMaterializationContext {
            session_id: &base.session_id,
            display_scope: &base.machine_display_render_scope,
            callable_interface_table: &base.machine_surface_callable_interface_table,
        };
        let state = base
            .snapshots
            .lookup_checked(
                &snapshot_context,
                base.initial_snapshot.snapshot_id,
                base.initial_snapshot.state_fingerprint,
            )
            .unwrap()
            .executable_state_payload
            .clone();
        let (context, display_scope) = head_collision_context_and_scope();
        let mut session = base;
        session.import_certificate_context = context;
        session.machine_display_render_scope = display_scope;

        assert_eq!(
            build_theorem_index(&session, &state).unwrap_err(),
            TheoremSearchBuildError::DisplayRefMismatch
        );
    }

    fn hex_bytes(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            out.push(hex_digit(byte >> 4));
            out.push(hex_digit(byte & 0x0f));
        }
        out
    }

    fn hex_digit(value: u8) -> char {
        match value {
            0..=9 => char::from(b'0' + value),
            10..=15 => char::from(b'a' + (value - 10)),
            _ => unreachable!("hex nybble is in range"),
        }
    }
}

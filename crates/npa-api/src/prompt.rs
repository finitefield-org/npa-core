use npa_cert::{Hash, Name};
use npa_tactic::{
    goal_id_canonical_bytes, GoalId, MachineTacticDiagnostic, MachineTacticDiagnosticKind,
};
use sha2::{Digest, Sha256};

use crate::adapter::{
    MachineApiDiagnosticPhase, MachineApiDiagnosticProjection, MachineApiTacticKind,
};
use crate::current::{encode_machine_axiom_ref_wire, MachineAxiomRefWire};
use crate::json::{JsonValue, JsonValueKind};
use crate::search::{
    canonicalize_allowed_modules_for_session, parse_theorem_filters, parse_theorem_limit,
    parse_theorem_modes, select_machine_premise_results_for_goal,
    select_machine_theorem_results_for_goal, MachineImportProposalCandidateSource,
    MachinePremiseCandidateProvenance, MachinePremiseIndexSource, MachinePremiseRankingMetadata,
    MachinePremiseSearchResult, MachinePremiseSetAxiomImpact, MachinePremiseStructuralFeatures,
    MachineRetrievalCacheKey, MachineTheoremFilters, MachineTheoremGlobalRef, MachineTheoremMode,
    MachineTheoremSearchResult, MachineTheoremStatement, MachineVerifiedPremiseIdentity,
    PREMISE_SEARCH_QUERY_PROFILE_VERSION, SEARCH_PROFILE_VERSION, SUGGESTION_PROFILE_VERSION,
};
use crate::snapshot::{MachineSnapshotLookupError, MachineSnapshotMaterializationContext};
use crate::types::{
    format_goal_id_wire, parse_goal_id_wire, HashString, MachineApiEndpoint,
    MachineApiErrorResponse, MachineApiErrorWire, MachineApiOkResponse, MachineApiResponseEnvelope,
    MachineApiResponseStatus, MachineGoalView, MachineProofSession, SessionId, SnapshotId,
    MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA,
};
use crate::validation::{
    parse_request_body, validate_json_object, FieldSpec, JsonFieldType, JsonPath, JsonPathElement,
    MachineApiErrorKind, MachineApiRequestError, MachineApiRequestErrorReason, ObjectSchema,
    ValidatedObject,
};
use crate::{validate_machine_endpoint_envelope, MachineApiUpstreamDiagnostic, MachineApiVersion};

const PROMPT_PAYLOAD_TAG: &str = "npa.machine-api.prompt-payload.v1";
const PROMPT_RENDERED_CONTENT_TAG: &str = "npa.machine-api.prompt-rendered-content.v1";

const PREMISE_SELECTION_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("modes", JsonFieldType::Array),
    FieldSpec::required("limit", JsonFieldType::UnsignedInteger { max: 256 }),
    FieldSpec::required("filters", JsonFieldType::Object),
];

const FAILED_CANDIDATE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("candidate_hash", JsonFieldType::String),
    FieldSpec::required("error_kind", JsonFieldType::String),
    FieldSpec::required("diagnostic_hash", JsonFieldType::String),
];

pub type MachinePromptPayloadResponse =
    MachineApiResponseEnvelope<MachinePromptPayloadOkFields, MachineApiErrorWire, ()>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPayloadOkFields {
    pub payload_fingerprint: Hash,
    pub premise_query_fingerprint: Hash,
    pub premise_query_profile_hash: Hash,
    pub premise_query_profile_version: &'static str,
    pub theorem_index_fingerprint: Hash,
    pub retrieval_cache_key: MachineRetrievalCacheKey,
    pub visible_imports_fingerprint: Hash,
    pub search_profile_version: &'static str,
    pub suggestion_profile_version: &'static str,
    pub goal: MachinePromptGoal,
    pub premises: Vec<MachinePromptPremise>,
    pub import_proposals: Vec<MachinePromptImportProposal>,
    pub failed_candidates: Vec<FailedCandidatePromptItem>,
    pub allowed_tactics: Vec<MachineApiTacticKind>,
    pub output_schema: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptGoal {
    pub target_machine: String,
    pub target_pretty: Option<String>,
    pub context: Vec<MachinePromptLocal>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptLocal {
    pub machine_name: String,
    pub display_name: Option<String>,
    pub type_machine: String,
    pub value_machine: Option<String>,
    pub value_pretty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPremise {
    pub premise_id: String,
    pub global_ref: MachineTheoremGlobalRef,
    pub universe_params: Vec<String>,
    pub statement: MachineTheoremStatement,
    pub modes: Vec<MachineTheoremMode>,
    pub axioms_used: Vec<MachineAxiomRefWire>,
    pub retrieval: MachinePromptPremiseRetrievalMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPremiseRetrievalMetadata {
    pub verified_identity: MachineVerifiedPremiseIdentity,
    pub statement_core_hash: Hash,
    pub structural_features: MachinePremiseStructuralFeatures,
    pub selected_modes: Vec<MachineTheoremMode>,
    pub ranking_metadata: MachinePremiseRankingMetadata,
    pub candidate_provenance: MachinePremiseCandidateProvenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptImportProposal {
    pub source_premise_id: String,
    pub candidate_source: MachineImportProposalCandidateSource,
    pub candidate_identity: MachineVerifiedPremiseIdentity,
    pub visible_imports_fingerprint: Hash,
    pub axiom_impact: MachinePremiseSetAxiomImpact,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailedCandidatePromptItem {
    pub candidate_hash: Hash,
    pub error_kind: FailedCandidateErrorKind,
    pub diagnostic_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FailedCandidateErrorKind {
    UnsupportedTactic,
    MachineTermElaborationError,
    UnknownName,
    ImplicitArgumentRequired,
    TypeMismatch,
    ExpectedPiType,
    RewriteRuleInvalid,
    SimpNoProgress,
    InductionTargetNotNat,
    BudgetExceeded,
    TooManyGoals,
    TooLargeTerm,
}

impl FailedCandidateErrorKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedTactic => "unsupported_tactic",
            Self::MachineTermElaborationError => "machine_term_elaboration_error",
            Self::UnknownName => "unknown_name",
            Self::ImplicitArgumentRequired => "implicit_argument_required",
            Self::TypeMismatch => "type_mismatch",
            Self::ExpectedPiType => "expected_pi_type",
            Self::RewriteRuleInvalid => "rewrite_rule_invalid",
            Self::SimpNoProgress => "simp_no_progress",
            Self::InductionTargetNotNat => "induction_target_not_nat",
            Self::BudgetExceeded => "budget_exceeded",
            Self::TooManyGoals => "too_many_goals",
            Self::TooLargeTerm => "too_large_term",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "unsupported_tactic" => Some(Self::UnsupportedTactic),
            "machine_term_elaboration_error" => Some(Self::MachineTermElaborationError),
            "unknown_name" => Some(Self::UnknownName),
            "implicit_argument_required" => Some(Self::ImplicitArgumentRequired),
            "type_mismatch" => Some(Self::TypeMismatch),
            "expected_pi_type" => Some(Self::ExpectedPiType),
            "rewrite_rule_invalid" => Some(Self::RewriteRuleInvalid),
            "simp_no_progress" => Some(Self::SimpNoProgress),
            "induction_target_not_nat" => Some(Self::InductionTargetNotNat),
            "budget_exceeded" => Some(Self::BudgetExceeded),
            "too_many_goals" => Some(Self::TooManyGoals),
            "too_large_term" => Some(Self::TooLargeTerm),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPayloadRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub include_pretty: bool,
    pub include_failed_candidates: bool,
    pub premise_selection: MachinePromptPremiseSelection,
    pub failed_candidates: Vec<FailedCandidatePromptItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPremiseSelection {
    pub modes: Vec<MachineTheoremMode>,
    pub limit: u32,
    pub filters: MachineTheoremFilters,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachinePromptPayloadError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachinePromptPayloadResponse,
}

pub fn parse_machine_prompt_payload_request(
    source: &str,
) -> Result<MachinePromptPayloadRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidPromptPayloadRequest)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        MachineApiEndpoint::PromptPayload,
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
    let include_pretty = required_field(&envelope, "include_pretty")
        .bool_value()
        .expect("endpoint validation checked include_pretty bool");
    let include_failed_candidates = required_field(&envelope, "include_failed_candidates")
        .bool_value()
        .expect("endpoint validation checked include_failed_candidates bool");
    let premise_selection = parse_premise_selection(
        required_field(&envelope, "premise_selection"),
        &JsonPath::root().field("premise_selection"),
    )?;
    let failed_candidates = parse_failed_candidates(
        required_field(&envelope, "failed_candidates"),
        include_failed_candidates,
        &JsonPath::root().field("failed_candidates"),
    )?;

    Ok(MachinePromptPayloadRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        goal_id,
        include_pretty,
        include_failed_candidates,
        premise_selection,
        failed_candidates,
    })
}

pub fn build_machine_prompt_payload(
    source: &str,
    session: &MachineProofSession,
) -> Result<MachinePromptPayloadResponse, Box<MachinePromptPayloadError>> {
    build_machine_prompt_payload_in_sessions(source, std::iter::once(session))
}

pub fn build_machine_prompt_payload_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
) -> Result<MachinePromptPayloadResponse, Box<MachinePromptPayloadError>> {
    let mut request = parse_machine_prompt_payload_request(source).map_err(prompt_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(prompt_plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
        ));
    };

    build_machine_prompt_payload_parsed(session, &mut request)
}

fn build_machine_prompt_payload_parsed(
    session: &MachineProofSession,
    request: &mut MachinePromptPayloadRequest,
) -> Result<MachinePromptPayloadResponse, Box<MachinePromptPayloadError>> {
    canonicalize_allowed_modules_for_session(session, &mut request.premise_selection.filters)
        .map_err(|error| {
            prompt_plain_error(
                MachineApiErrorKind::InvalidPromptPayloadRequest,
                MachineApiDiagnosticPhase::RequestValidation,
                format!(
                    "allowed module {} is not a direct import of the session",
                    error.module.as_dotted()
                ),
            )
        })?;

    if session.snapshots.session_id() != &session.session_id {
        return Err(prompt_plain_error(
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
        .map_err(prompt_snapshot_lookup_error)?;
    let goal = entry
        .materialized_view_payload
        .goals
        .iter()
        .find(|goal| goal.goal_id == request.goal_id)
        .ok_or_else(|| {
            prompt_goal_error(
                MachineApiErrorKind::GoalNotOpen,
                MachineApiDiagnosticPhase::SnapshotLookup,
                request.goal_id,
                format!("goal {} is not open", format_goal_id_wire(request.goal_id)),
            )
        })?;

    let display_modes = prompt_display_theorem_modes();
    let display_selection = select_machine_theorem_results_for_goal(
        session,
        &entry.executable_state_payload,
        goal,
        &display_modes,
        &request.premise_selection.filters,
        256,
        false,
    )
    .map_err(prompt_theorem_index_error)?;
    let retrieval_selection = select_machine_premise_results_for_goal(
        session,
        &entry.executable_state_payload,
        goal,
        &request.premise_selection.modes,
        &request.premise_selection.filters,
        request.premise_selection.limit,
        None,
        None,
    )
    .map_err(prompt_premise_search_selection_error)?;

    let prompt_goal = prompt_goal_from_view(goal, request.include_pretty);
    let premises = retrieval_selection
        .results
        .iter()
        .map(|retrieval| {
            let Some(display) = display_selection
                .results
                .iter()
                .find(|result| prompt_retrieval_result_matches_theorem(result, retrieval))
            else {
                return Err(prompt_plain_error(
                    MachineApiErrorKind::InvalidTheoremIndex,
                    MachineApiDiagnosticPhase::TheoremSearch,
                    "premise search result could not be rendered from the verified theorem index",
                ));
            };
            Ok(prompt_premise_from_search_result(display, retrieval))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let import_proposals = prompt_import_proposals_from_retrieval(
        &retrieval_selection.results,
        retrieval_selection.visible_imports_fingerprint,
    );
    let mut allowed_tactics = goal.allowed_tactics.clone();
    allowed_tactics.sort();
    let failed_candidates = if request.include_failed_candidates {
        request.failed_candidates.clone()
    } else {
        Vec::new()
    };
    let rendered_content = prompt_rendered_content_canonical_bytes(
        &prompt_goal,
        &premises,
        &import_proposals,
        &failed_candidates,
        &allowed_tactics,
        MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA,
    );
    let payload_fingerprint = prompt_payload_fingerprint(PromptPayloadFingerprintInput {
        protocol_version: session.protocol_version,
        session_root_hash: session.session_root_hash,
        state_fingerprint: request.state_fingerprint,
        goal_id: request.goal_id,
        include_pretty: request.include_pretty,
        include_failed_candidates: request.include_failed_candidates,
        theorem_index_fingerprint: retrieval_selection.theorem_index_fingerprint,
        premise_query_fingerprint: retrieval_selection.query_fingerprint,
        rendered_content: &rendered_content,
    });

    Ok(MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
        status: MachineApiResponseStatus::Ok,
        endpoint_fields: MachinePromptPayloadOkFields {
            payload_fingerprint,
            premise_query_fingerprint: retrieval_selection.query_fingerprint,
            premise_query_profile_hash: retrieval_selection.query_profile_hash,
            premise_query_profile_version: PREMISE_SEARCH_QUERY_PROFILE_VERSION,
            theorem_index_fingerprint: retrieval_selection.theorem_index_fingerprint,
            retrieval_cache_key: retrieval_selection.retrieval_cache_key,
            visible_imports_fingerprint: retrieval_selection.visible_imports_fingerprint,
            search_profile_version: SEARCH_PROFILE_VERSION,
            suggestion_profile_version: SUGGESTION_PROFILE_VERSION,
            goal: prompt_goal,
            premises,
            import_proposals,
            failed_candidates,
            allowed_tactics,
            output_schema: MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA,
        },
    }))
}

fn parse_premise_selection(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachinePromptPremiseSelection, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            PREMISE_SELECTION_FIELDS,
        ),
        path,
    )?;
    let modes = parse_theorem_modes(
        required_object_field(&object, "modes"),
        &path.field("modes"),
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    )?;
    let limit = parse_theorem_limit(
        required_object_field(&object, "limit"),
        &path.field("limit"),
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    )?;
    let filters = parse_theorem_filters(
        required_object_field(&object, "filters"),
        &path.field("filters"),
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    )?;
    Ok(MachinePromptPremiseSelection {
        modes,
        limit,
        filters,
    })
}

fn parse_failed_candidates(
    value: &JsonValue<'_>,
    include_failed_candidates: bool,
    path: &JsonPath,
) -> Result<Vec<FailedCandidatePromptItem>, MachineApiRequestError> {
    let elements = value.array_elements().ok_or_else(|| {
        request_error(
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "failed_candidates",
                expected: JsonFieldType::Array,
                actual: value.kind(),
            },
        )
    })?;
    if !include_failed_candidates && !elements.is_empty() {
        return Err(request_error(
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "failed_candidates",
                expected: JsonFieldType::Array,
                actual: JsonValueKind::Array,
            },
        ));
    }
    elements
        .iter()
        .enumerate()
        .map(|(index, item)| parse_failed_candidate(item, &path.index(index)))
        .collect()
}

fn parse_failed_candidate(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<FailedCandidatePromptItem, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            FAILED_CANDIDATE_FIELDS,
        ),
        path,
    )?;
    let candidate_hash = parse_hash_field(
        required_object_field(&object, "candidate_hash"),
        "candidate_hash",
        &path.field("candidate_hash"),
    )?;
    let diagnostic_hash = parse_hash_field(
        required_object_field(&object, "diagnostic_hash"),
        "diagnostic_hash",
        &path.field("diagnostic_hash"),
    )?;
    let error_kind_value = required_object_field(&object, "error_kind");
    let Some(error_kind_text) = error_kind_value.string_value() else {
        return Err(request_error(
            &path.field("error_kind"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "error_kind",
                expected: JsonFieldType::String,
                actual: error_kind_value.kind(),
            },
        ));
    };
    let Some(error_kind) = FailedCandidateErrorKind::parse(error_kind_text) else {
        return Err(request_error(
            &path.field("error_kind"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "error_kind",
                expected: JsonFieldType::String,
                actual: JsonValueKind::String,
            },
        ));
    };

    Ok(FailedCandidatePromptItem {
        candidate_hash,
        error_kind,
        diagnostic_hash,
    })
}

fn parse_hash_field(
    value: &JsonValue<'_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Hash, MachineApiRequestError> {
    let Some(text) = value.string_value() else {
        return Err(request_error(
            path,
            MachineApiRequestErrorReason::TypeMismatch {
                field,
                expected: JsonFieldType::String,
                actual: value.kind(),
            },
        ));
    };
    HashString::parse(text)
        .map(HashString::digest)
        .map_err(|_| {
            request_error(
                path,
                MachineApiRequestErrorReason::TypeMismatch {
                    field,
                    expected: JsonFieldType::String,
                    actual: JsonValueKind::String,
                },
            )
        })
}

fn prompt_goal_from_view(goal: &MachineGoalView, include_pretty: bool) -> MachinePromptGoal {
    MachinePromptGoal {
        target_machine: goal.target.machine.clone(),
        target_pretty: include_pretty.then(|| {
            goal.target
                .pretty
                .clone()
                .unwrap_or_else(|| goal.target.machine.clone())
        }),
        context: goal
            .context
            .iter()
            .map(|local| MachinePromptLocal {
                machine_name: local.machine_name.clone(),
                display_name: include_pretty.then(|| local.display_name.clone()),
                type_machine: local.ty.machine.clone(),
                value_machine: local.value.as_ref().map(|value| value.machine.clone()),
                value_pretty: if include_pretty {
                    local.value.as_ref().map(|value| {
                        value
                            .pretty
                            .clone()
                            .unwrap_or_else(|| value.machine.clone())
                    })
                } else {
                    None
                },
            })
            .collect(),
    }
}

fn prompt_display_theorem_modes() -> [MachineTheoremMode; 4] {
    [
        MachineTheoremMode::Exact,
        MachineTheoremMode::Apply,
        MachineTheoremMode::Rw,
        MachineTheoremMode::Simp,
    ]
}

fn prompt_premise_from_search_result(
    result: &MachineTheoremSearchResult,
    retrieval: &MachinePremiseSearchResult,
) -> MachinePromptPremise {
    MachinePromptPremise {
        premise_id: retrieval.premise_id.clone(),
        global_ref: result.global_ref.clone(),
        universe_params: result.universe_params.clone(),
        statement: result.statement.clone(),
        modes: result.modes.clone(),
        axioms_used: result.axioms_used.clone(),
        retrieval: MachinePromptPremiseRetrievalMetadata {
            verified_identity: retrieval.verified_identity.clone(),
            statement_core_hash: retrieval.statement_core_hash,
            structural_features: retrieval.structural_features.clone(),
            selected_modes: retrieval.selected_modes.clone(),
            ranking_metadata: retrieval.ranking_metadata.clone(),
            candidate_provenance: retrieval.candidate_provenance.clone(),
        },
    }
}

fn prompt_retrieval_result_matches_theorem(
    theorem: &MachineTheoremSearchResult,
    retrieval: &MachinePremiseSearchResult,
) -> bool {
    retrieval.verified_identity.module == theorem.global_ref.module
        && retrieval.verified_identity.export_hash == theorem.global_ref.export_hash
        && retrieval.verified_identity.global_ref.name == theorem.global_ref.name
        && retrieval.verified_identity.global_ref.decl_interface_hash
            == theorem.global_ref.decl_interface_hash
        && retrieval.statement_core_hash == theorem.statement.core_hash
}

fn prompt_import_proposals_from_retrieval(
    retrieval_results: &[MachinePremiseSearchResult],
    visible_imports_fingerprint: Hash,
) -> Vec<MachinePromptImportProposal> {
    retrieval_results
        .iter()
        .filter_map(|result| {
            let candidate_source = match result.candidate_provenance.premise_source {
                MachinePremiseIndexSource::DirectImport => return None,
                MachinePremiseIndexSource::PackageTheoremIndex => {
                    MachineImportProposalCandidateSource::PackageTheoremIndex
                }
            };
            let axiom_impact = result
                .ranking_metadata
                .premise_set
                .as_ref()
                .map(|premise_set| premise_set.axiom_impact.clone())
                .unwrap_or_else(|| MachinePremiseSetAxiomImpact {
                    direct_axiom_count: result.ranking_metadata.axiom_ranking.direct_axiom_count,
                    transitive_axiom_count: result
                        .ranking_metadata
                        .axiom_ranking
                        .transitive_axiom_count,
                    summary_hash: result.verified_identity.axiom_summary.summary_hash,
                    axiom_paths: result.ranking_metadata.axiom_ranking.axiom_paths.clone(),
                });
            Some(MachinePromptImportProposal {
                source_premise_id: result.premise_id.clone(),
                candidate_source,
                candidate_identity: result.verified_identity.clone(),
                visible_imports_fingerprint,
                axiom_impact,
            })
        })
        .collect()
}

struct PromptPayloadFingerprintInput<'a> {
    protocol_version: MachineApiVersion,
    session_root_hash: Hash,
    state_fingerprint: Hash,
    goal_id: GoalId,
    include_pretty: bool,
    include_failed_candidates: bool,
    theorem_index_fingerprint: Hash,
    premise_query_fingerprint: Hash,
    rendered_content: &'a [u8],
}

fn prompt_payload_fingerprint(input: PromptPayloadFingerprintInput<'_>) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMPT_PAYLOAD_TAG);
    encode_string(&mut out, input.protocol_version.as_str());
    out.extend(input.session_root_hash);
    out.extend(input.state_fingerprint);
    out.extend(goal_id_canonical_bytes(input.goal_id));
    encode_bool(&mut out, input.include_pretty);
    encode_bool(&mut out, input.include_failed_candidates);
    out.extend(input.theorem_index_fingerprint);
    out.extend(input.premise_query_fingerprint);
    out.extend(input.rendered_content);
    sha256(&out)
}

fn prompt_rendered_content_canonical_bytes(
    goal: &MachinePromptGoal,
    premises: &[MachinePromptPremise],
    import_proposals: &[MachinePromptImportProposal],
    failed_candidates: &[FailedCandidatePromptItem],
    allowed_tactics: &[MachineApiTacticKind],
    output_schema: &str,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, PROMPT_RENDERED_CONTENT_TAG);
    encode_string(&mut out, &goal.target_machine);
    encode_option_string(&mut out, goal.target_pretty.as_deref());
    encode_list_len(&mut out, goal.context.len());
    for local in &goal.context {
        encode_string(&mut out, &local.machine_name);
        encode_option_string(&mut out, local.display_name.as_deref());
        encode_string(&mut out, &local.type_machine);
        encode_option_string(&mut out, local.value_machine.as_deref());
        encode_option_string(&mut out, local.value_pretty.as_deref());
    }
    encode_list_len(&mut out, premises.len());
    for premise in premises {
        encode_string(&mut out, &premise.premise_id);
        encode_theorem_global_ref(&mut out, &premise.global_ref);
        encode_list_len(&mut out, premise.universe_params.len());
        for param in &premise.universe_params {
            encode_string(&mut out, param);
        }
        out.extend(premise.statement.core_hash);
        encode_option_global_ref_view(&mut out, premise.statement.head.as_ref());
        encode_string(&mut out, &premise.statement.machine);
        encode_list_len(&mut out, premise.modes.len());
        for mode in &premise.modes {
            encode_string(&mut out, mode.as_str());
        }
        encode_list_len(&mut out, premise.axioms_used.len());
        for axiom in &premise.axioms_used {
            out.extend(encode_machine_axiom_ref_wire(axiom));
        }
        out.extend(premise.retrieval.verified_identity.identity_hash());
        out.extend(premise.retrieval.statement_core_hash);
        out.extend(premise.retrieval.structural_features.feature_hash);
        encode_list_len(&mut out, premise.retrieval.selected_modes.len());
        for mode in &premise.retrieval.selected_modes {
            encode_string(&mut out, mode.as_str());
        }
        encode_prompt_ranking_metadata(&mut out, &premise.retrieval.ranking_metadata);
        encode_string(
            &mut out,
            premise
                .retrieval
                .candidate_provenance
                .premise_source
                .as_str(),
        );
        encode_string(
            &mut out,
            premise
                .retrieval
                .candidate_provenance
                .suggestion_profile_version,
        );
        encode_uvar(
            &mut out,
            u64::from(
                premise
                    .retrieval
                    .candidate_provenance
                    .suggested_candidate_count,
            ),
        );
    }
    encode_list_len(&mut out, import_proposals.len());
    for proposal in import_proposals {
        encode_string(&mut out, &proposal.source_premise_id);
        encode_string(&mut out, proposal.candidate_source.as_str());
        out.extend(proposal.candidate_identity.identity_hash());
        out.extend(proposal.visible_imports_fingerprint);
        encode_prompt_premise_set_axiom_impact(&mut out, &proposal.axiom_impact);
    }
    encode_list_len(&mut out, failed_candidates.len());
    for failed in failed_candidates {
        out.extend(failed.candidate_hash);
        encode_string(&mut out, failed.error_kind.as_str());
        out.extend(failed.diagnostic_hash);
    }
    encode_list_len(&mut out, allowed_tactics.len());
    for tactic in allowed_tactics {
        encode_string(&mut out, tactic.as_str());
    }
    encode_string(&mut out, output_schema);
    out
}

fn encode_prompt_ranking_metadata(out: &mut Vec<u8>, ranking: &MachinePremiseRankingMetadata) {
    encode_uvar(out, ranking.score);
    encode_string(out, ranking.axiom_ranking.theorem_level.as_str());
    encode_bool(out, ranking.axiom_ranking.candidate_verified);
    encode_bool(out, ranking.axiom_ranking.usable_under_axiom_policy);
    encode_uvar(out, u64::from(ranking.axiom_ranking.direct_axiom_count));
    encode_uvar(out, u64::from(ranking.axiom_ranking.transitive_axiom_count));
    encode_uvar(out, u64::from(ranking.axiom_ranking.disallowed_axiom_count));
    encode_list_len(out, ranking.axiom_ranking.axiom_paths.len());
    for path in &ranking.axiom_ranking.axiom_paths {
        encode_string(out, path.source.as_str());
        out.extend(encode_machine_axiom_ref_wire(&path.axiom));
        encode_uvar(out, u64::from(path.path_length));
        encode_optional_hash(out, path.graph_snapshot_hash);
    }
    encode_uvar(out, ranking.axiom_ranking.penalties.total);
    encode_string(out, ranking.type_aware.status.as_str());
    encode_option_string(
        out,
        ranking
            .type_aware
            .selected_mode
            .map(MachineTheoremMode::as_str),
    );
    encode_bool(out, ranking.type_aware.universe_compatible);
    encode_bool(out, ranking.type_aware.head_compatible);
    encode_bool(out, ranking.type_aware.result_fits_goal);
    encode_uvar(out, ranking.type_aware.pi_binder_count);
    encode_uvar(out, ranking.type_aware.estimated_new_goals);
    encode_uvar(out, ranking.type_aware.premise_size);
    encode_uvar(out, ranking.type_aware.goal_size);
    match &ranking.premise_set {
        Some(premise_set) => {
            out.push(0x01);
            encode_uvar(out, u64::from(premise_set.max_set_size));
            encode_optional_hash(out, premise_set.graph_snapshot_hash);
            encode_list_len(out, premise_set.selected_premises.len());
            encode_list_len(out, premise_set.import_requirements.len());
            for module in &premise_set.import_requirements {
                encode_name(out, module);
            }
            encode_prompt_premise_set_axiom_impact(out, &premise_set.axiom_impact);
            encode_uvar(out, premise_set.objective.final_score);
        }
        None => out.push(0x00),
    }
}

fn encode_prompt_premise_set_axiom_impact(
    out: &mut Vec<u8>,
    impact: &MachinePremiseSetAxiomImpact,
) {
    encode_uvar(out, u64::from(impact.direct_axiom_count));
    encode_uvar(out, u64::from(impact.transitive_axiom_count));
    out.extend(impact.summary_hash);
    encode_list_len(out, impact.axiom_paths.len());
    for path in &impact.axiom_paths {
        encode_string(out, path.source.as_str());
        out.extend(encode_machine_axiom_ref_wire(&path.axiom));
        encode_uvar(out, u64::from(path.path_length));
        encode_optional_hash(out, path.graph_snapshot_hash);
    }
}

fn encode_optional_hash(out: &mut Vec<u8>, value: Option<Hash>) {
    match value {
        Some(value) => {
            out.push(0x01);
            out.extend(value);
        }
        None => out.push(0x00),
    }
}

fn encode_theorem_global_ref(out: &mut Vec<u8>, global_ref: &MachineTheoremGlobalRef) {
    encode_name(out, &global_ref.module);
    encode_name(out, &global_ref.name);
    out.extend(global_ref.export_hash);
    out.extend(global_ref.decl_interface_hash);
}

fn encode_option_global_ref_view(out: &mut Vec<u8>, value: Option<&crate::MachineGlobalRefView>) {
    match value {
        Some(value) => {
            out.push(0x01);
            out.extend(value.canonical_bytes());
        }
        None => out.push(0x00),
    }
}

fn encode_option_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_string(out, value);
        }
        None => out.push(0x00),
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

fn prompt_request_error(error: MachineApiRequestError) -> Box<MachinePromptPayloadError> {
    prompt_plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
    )
}

fn prompt_snapshot_lookup_error(
    error: MachineSnapshotLookupError,
) -> Box<MachinePromptPayloadError> {
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
    prompt_plain_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {error:?}"),
    )
}

fn prompt_theorem_index_error(
    error: crate::search::TheoremSearchBuildError,
) -> Box<MachinePromptPayloadError> {
    prompt_plain_error(
        MachineApiErrorKind::InvalidTheoremIndex,
        MachineApiDiagnosticPhase::TheoremSearch,
        format!("theorem index construction failed: {error:?}"),
    )
}

fn prompt_premise_search_selection_error(
    error: crate::search::MachinePremiseSearchSelectionError,
) -> Box<MachinePromptPayloadError> {
    prompt_plain_error(
        MachineApiErrorKind::InvalidTheoremIndex,
        MachineApiDiagnosticPhase::TheoremSearch,
        format!("premise search selection failed: {error:?}"),
    )
}

fn prompt_plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachinePromptPayloadError> {
    prompt_error(kind, phase, None, message)
}

fn prompt_goal_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: GoalId,
    message: impl Into<String>,
) -> Box<MachinePromptPayloadError> {
    prompt_error(kind, phase, Some(goal_id), message)
}

fn prompt_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<GoalId>,
    message: impl Into<String>,
) -> Box<MachinePromptPayloadError> {
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
            MachineTacticDiagnosticKind::InvalidMachineProofState,
            message,
        )),
    };
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("prompt payload diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachinePromptPayloadError {
        diagnostic,
        response,
    })
}

fn request_error(path: &JsonPath, reason: MachineApiRequestErrorReason) -> MachineApiRequestError {
    MachineApiRequestError::new(
        MachineApiErrorKind::InvalidPromptPayloadRequest,
        path.clone(),
        reason,
    )
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

fn required_object_field<'value, 'src>(
    object: &ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value JsonValue<'src> {
    object
        .field(field)
        .expect("object validation checked required field")
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
    use crate::{create_machine_session, format_hash_string, MachineApiResponseEnvelope};
    use npa_cert::{
        build_module_cert, encode_module_cert, verify_module_cert, AxiomPolicy, CoreModule, Name,
        VerifierSession,
    };
    use npa_kernel::{Decl, Expr, Level};

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn imported_axiom_type() -> Expr {
        Expr::pi("p", prop(), prop())
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

    fn prompt_json(
        session: &MachineProofSession,
        include_pretty: bool,
        include_failed_candidates: bool,
        failed_candidates: &str,
        filters: &str,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "include_pretty":{},
              "include_failed_candidates":{},
              "premise_selection":{{
                "modes":["apply","exact","rw","simp"],
                "limit":20,
                "filters":{}
              }},
              "failed_candidates":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            include_pretty,
            include_failed_candidates,
            filters,
            failed_candidates
        )
    }

    #[test]
    fn prompt_payload_returns_deterministic_ai_search_context() {
        let session = imported_axiom_session();
        let reusable_hash = format_hash_string(&session.initial_snapshot.state_fingerprint);
        let failed_candidates = format!(
            r#"[{{
              "candidate_hash":"{reusable_hash}",
              "error_kind":"type_mismatch",
              "diagnostic_hash":"{reusable_hash}"
            }}]"#
        );
        let body = prompt_json(
            &session,
            true,
            true,
            &failed_candidates,
            r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#,
        );
        let first = build_machine_prompt_payload(&body, &session).unwrap();
        let second = build_machine_prompt_payload(&body, &session).unwrap();
        let (first, second) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("prompt payload should succeed"),
        };

        assert_eq!(first.payload_fingerprint, second.payload_fingerprint);
        assert_eq!(
            first.premise_query_fingerprint,
            second.premise_query_fingerprint
        );
        assert_eq!(
            first.theorem_index_fingerprint,
            second.theorem_index_fingerprint
        );
        assert_eq!(first.goal.target_machine, "Prop");
        assert_eq!(first.goal.target_pretty.as_deref(), Some("Prop"));
        assert!(first.goal.context.is_empty());
        assert_eq!(first.premises.len(), 1);
        assert_eq!(first.premises[0].premise_id, "prem_0");
        assert_eq!(first.premises[0].global_ref.module, Name::from_dotted("A"));
        assert_eq!(first.premises[0].global_ref.name, Name::from_dotted("A.id"));
        assert_eq!(
            first.premises[0].statement.machine,
            "forall (x : Prop), Prop"
        );
        assert_eq!(
            first.premises[0].modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply]
        );
        assert_eq!(first.failed_candidates.len(), 1);
        assert_eq!(
            first.failed_candidates[0].error_kind,
            FailedCandidateErrorKind::TypeMismatch
        );
        assert_eq!(
            first.allowed_tactics,
            vec![
                MachineApiTacticKind::Intro,
                MachineApiTacticKind::Exact,
                MachineApiTacticKind::Apply,
                MachineApiTacticKind::Rw,
                MachineApiTacticKind::SimpLite
            ]
        );
        assert_eq!(first.output_schema, MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA);
        assert_eq!(first.search_profile_version, SEARCH_PROFILE_VERSION);
        assert_eq!(first.suggestion_profile_version, SUGGESTION_PROFILE_VERSION);
    }

    #[test]
    fn prompt_premise_payload_includes_verified_metadata_and_separates_import_proposals() {
        let session = imported_axiom_session();
        let body = prompt_json(
            &session,
            true,
            false,
            "[]",
            r#"{"exclude_axioms":false,"allowed_modules":["A"]}"#,
        );
        let response = build_machine_prompt_payload(&body, &session).unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("prompt payload should succeed");
        };
        let payload = ok.endpoint_fields;
        let [premise] = payload.premises.as_slice() else {
            panic!("expected one visible premise");
        };

        assert_eq!(
            payload.premise_query_fingerprint,
            payload.retrieval_cache_key.query_fingerprint
        );
        assert_eq!(
            payload.visible_imports_fingerprint,
            payload.retrieval_cache_key.visible_imports_fingerprint
        );
        assert_eq!(
            payload.premise_query_profile_version,
            PREMISE_SEARCH_QUERY_PROFILE_VERSION
        );
        assert_eq!(premise.global_ref.name, Name::from_dotted("A.id"));
        assert_eq!(
            premise.retrieval.verified_identity.global_ref.name,
            Name::from_dotted("A.id")
        );
        assert_eq!(
            premise.retrieval.verified_identity.decl_interface_hash,
            premise.global_ref.decl_interface_hash
        );
        assert_eq!(
            premise.retrieval.statement_core_hash,
            premise.statement.core_hash
        );
        assert_eq!(
            premise
                .retrieval
                .ranking_metadata
                .axiom_ranking
                .theorem_level,
            crate::MachinePremiseTheoremLevel::VerifiedCertificate
        );
        assert!(
            premise
                .retrieval
                .ranking_metadata
                .axiom_ranking
                .candidate_verified
        );
        assert!(
            premise
                .retrieval
                .ranking_metadata
                .axiom_ranking
                .usable_under_axiom_policy
        );
        assert_eq!(
            premise
                .retrieval
                .candidate_provenance
                .suggested_candidate_count,
            0
        );
        assert!(payload.import_proposals.is_empty());
    }

    #[test]
    fn prompt_rejects_failed_candidates_when_disabled_before_session_lookup() {
        let hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
        let body = format!(
            r#"{{
              "session_id":"msess_missing",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"{hash}",
              "goal_id":"g0",
              "include_pretty":false,
              "include_failed_candidates":false,
              "premise_selection":{{
                "modes":["exact"],
                "limit":1,
                "filters":{{"exclude_axioms":false,"allowed_modules":[]}}
              }},
              "failed_candidates":[{{
                "candidate_hash":"{hash}",
                "error_kind":"type_mismatch",
                "diagnostic_hash":"{hash}"
              }}]
            }}"#
        );
        let err = build_machine_prompt_payload_in_sessions(&body, std::iter::empty()).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidPromptPayloadRequest
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::RequestValidation
        );
    }

    #[test]
    fn prompt_rejects_non_direct_allowed_module_before_snapshot_lookup() {
        let session = imported_axiom_session();
        let body = prompt_json(
            &session,
            false,
            false,
            "[]",
            r#"{"exclude_axioms":false,"allowed_modules":["Missing"]}"#,
        );
        let err = build_machine_prompt_payload(&body, &session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidPromptPayloadRequest
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::RequestValidation
        );
    }

    #[test]
    fn prompt_rejects_non_direct_allowed_module_before_snapshot_store_invariant() {
        let mut session = imported_axiom_session();
        let body = prompt_json(
            &session,
            false,
            false,
            "[]",
            r#"{"exclude_axioms":false,"allowed_modules":["Missing"]}"#,
        );
        session.snapshots =
            crate::MachineSnapshotStore::new(crate::SessionId::new_unchecked("msess_other"));

        let err = build_machine_prompt_payload(&body, &session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidPromptPayloadRequest
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::RequestValidation
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

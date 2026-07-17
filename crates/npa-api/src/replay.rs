use npa_cert::Hash;
use npa_tactic::{
    tactic_budget_hash, GoalId, MachineProofState, MachineTacticDiagnostic,
    MachineTacticDiagnosticKind, MachineTacticProfileVersion, TacticBudget,
};

use crate::adapter::{
    machine_tactic_run_machine_tactic_with_budget,
    machine_tactic_validate_machine_tactic_candidate_for_state, MachineApiDiagnosticPhase,
    MachineApiDiagnosticProjection, MachineApiTacticKind, MachineTacticAdapterError,
};
use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::snapshot::{
    MachineSnapshotLookupError, MachineSnapshotMaterializationContext, MachineSnapshotStoreError,
};
use crate::tactic::{
    candidate_tactic_kind_for_diagnostic, json_path_display,
    machine_tactic_proof_candidate_identity_hash,
    minimal_failing_artifact_diagnostic_from_projection, parse_candidate_payload_at,
    parse_candidate_wire_shape_at, parse_deterministic_budget_with_error_kind,
    validate_focused_replay_failure_artifact_identity, validate_minimal_failing_artifact_identity,
    FocusedReplayFailureArtifact, MinimalFailingArtifact, MinimalFailingArtifactError,
    STRUCTURAL_V2_REQUIRED_FEATURES,
};
use crate::trust::proof_candidate_goal_fingerprint;
use crate::types::{
    HashString, MachineApiEndpoint, MachineApiErrorResponse, MachineApiErrorWire,
    MachineApiOkResponse, MachineApiResponseEnvelope, MachineApiResponseStatus,
    MachineApiSchedulerResponse, MachineApiVersion, MachineProofSession, MachineSchedulerArtifact,
    MachineSchedulerArtifactKind, MachineSchedulerArtifactScope, SessionId, SnapshotId,
};
use crate::validation::{
    delayed_json_payload, parse_request_body, validate_json_object, DelayedJsonPayload, FieldSpec,
    JsonFieldType, JsonPath, MachineApiErrorKind, MachineApiRequestError,
    MachineApiRequestErrorReason, ObjectSchema,
};
use crate::{validate_machine_endpoint_envelope, MachineApiUpstreamDiagnostic};

const MAX_REPLAY_STEPS: usize = 4096;

const REPLAY_PLAN_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("protocol_version", JsonFieldType::String),
    FieldSpec::required("session_root_hash", JsonFieldType::String),
    FieldSpec::required("initial_state_fingerprint", JsonFieldType::String),
    FieldSpec::required("steps", JsonFieldType::Array),
    FieldSpec::required("final_state_fingerprint", JsonFieldType::String),
];

const REPLAY_STEP_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("previous_state_fingerprint", JsonFieldType::String),
    FieldSpec::required("goal_id", JsonFieldType::String),
    FieldSpec::required("candidate", JsonFieldType::Object),
    FieldSpec::required("deterministic_budget", JsonFieldType::Object),
    FieldSpec::required("candidate_hash", JsonFieldType::String),
    FieldSpec::required("deterministic_budget_hash", JsonFieldType::String),
    FieldSpec::required("proof_delta_hash", JsonFieldType::String),
    FieldSpec::required("next_state_fingerprint", JsonFieldType::String),
];

pub type MachineReplayResponse =
    MachineApiResponseEnvelope<MachineReplayOkFields, MachineApiErrorWire, (), ()>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineReplayOkFields {
    pub final_snapshot_id: SnapshotId,
    pub final_state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineReplayError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub response: MachineReplayResponse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineReplayRequest<'src> {
    pub session_id: SessionId,
    pub plan: DelayedJsonPayload<'src>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineReplayPlan<'src> {
    pub protocol_version: MachineApiVersion,
    pub session_root_hash: Hash,
    pub initial_state_fingerprint: Hash,
    pub steps: Vec<MachineReplayStep<'src>>,
    pub final_state_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineReplayStep<'src> {
    pub previous_state_fingerprint: Hash,
    pub goal_id: GoalId,
    pub candidate: DelayedJsonPayload<'src>,
    pub deterministic_budget: TacticBudget,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
    pub proof_delta_hash: Hash,
    pub next_state_fingerprint: Hash,
}

pub fn parse_machine_replay_request<'src>(
    source: &'src str,
) -> Result<MachineReplayRequest<'src>, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidReplayPlan)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        MachineApiEndpoint::Replay,
        &JsonPath::root(),
    )?;

    let session_value = envelope
        .field("session_id")
        .expect("endpoint envelope checked required session_id");
    let session_id = SessionId::parse(
        session_value
            .string_value()
            .expect("endpoint envelope checked session_id string"),
    )
    .map_err(|_| invalid_string_literal("session_id", &JsonPath::root().field("session_id")))?;
    let plan = delayed_json_payload(
        envelope
            .field("plan")
            .expect("endpoint envelope checked required plan"),
    );

    Ok(MachineReplayRequest { session_id, plan })
}

pub fn run_machine_replay_request(
    source: &str,
    session: &mut MachineProofSession,
) -> Result<MachineReplayResponse, Box<MachineReplayError>> {
    run_machine_replay_request_in_sessions(source, std::iter::once(session))
}

pub fn run_machine_replay_request_in_sessions<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session mut MachineProofSession>,
) -> Result<MachineReplayResponse, Box<MachineReplayError>> {
    let request = parse_machine_replay_request(source).map_err(request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(plain_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
            None,
            None,
        ));
    };

    let plan = parse_machine_replay_plan(request.plan.raw).map_err(replay_validation_error)?;
    run_machine_replay_plan(session, plan)
}

fn parse_machine_replay_plan<'src>(
    raw: &'src str,
) -> Result<MachineReplayPlan<'src>, MachineApiRequestError> {
    let plan_path = JsonPath::root().field("plan");
    let doc = JsonDocument::parse(raw).map_err(|err| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidReplayPlan,
            plan_path.clone(),
            MachineApiRequestErrorReason::JsonParse {
                offset: err.offset,
                kind: err.kind,
            },
        )
    })?;
    let object = validate_json_object(
        doc.root(),
        ObjectSchema::new(MachineApiErrorKind::InvalidReplayPlan, REPLAY_PLAN_FIELDS),
        &plan_path,
    )?;

    let protocol_version = parse_protocol_version_field(
        required_field(&object, "protocol_version"),
        &plan_path.field("protocol_version"),
    )?;
    let session_root_hash = parse_hash_field(
        required_field(&object, "session_root_hash"),
        "session_root_hash",
        &plan_path.field("session_root_hash"),
    )?;
    let initial_state_fingerprint = parse_hash_field(
        required_field(&object, "initial_state_fingerprint"),
        "initial_state_fingerprint",
        &plan_path.field("initial_state_fingerprint"),
    )?;
    let final_state_fingerprint = parse_hash_field(
        required_field(&object, "final_state_fingerprint"),
        "final_state_fingerprint",
        &plan_path.field("final_state_fingerprint"),
    )?;
    let step_values = required_field(&object, "steps")
        .array_elements()
        .expect("schema checked steps array");
    if step_values.len() > MAX_REPLAY_STEPS {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidReplayPlan,
            plan_path.field("steps"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "steps",
                expected: JsonFieldType::Array,
                actual: JsonValueKind::Array,
            },
        ));
    }

    let steps = step_values
        .iter()
        .enumerate()
        .map(|(index, value)| parse_replay_step(value, &plan_path.field("steps").index(index)))
        .collect::<Result<Vec<_>, _>>()?;

    let plan = MachineReplayPlan {
        protocol_version,
        session_root_hash,
        initial_state_fingerprint,
        steps,
        final_state_fingerprint,
    };
    validate_replay_chain(&plan)?;
    Ok(plan)
}

fn parse_replay_step<'src>(
    value: &JsonValue<'src>,
    path: &JsonPath,
) -> Result<MachineReplayStep<'src>, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidReplayPlan, REPLAY_STEP_FIELDS),
        path,
    )?;
    let previous_state_fingerprint = parse_hash_field(
        required_field(&object, "previous_state_fingerprint"),
        "previous_state_fingerprint",
        &path.field("previous_state_fingerprint"),
    )?;
    let goal_id = crate::parse_goal_id_wire(required_string_field(&object, "goal_id"))
        .map_err(|_| invalid_string_literal("goal_id", &path.field("goal_id")))?;
    let candidate_value = required_field(&object, "candidate");
    let candidate = delayed_json_payload(candidate_value);
    let tactic_kind = candidate_tactic_kind_for_diagnostic(candidate.raw);
    parse_candidate_wire_shape_at(candidate.raw, tactic_kind, &path.field("candidate"))
        .map_err(as_invalid_replay_plan)?;

    let deterministic_budget = parse_deterministic_budget_with_error_kind(
        required_field(&object, "deterministic_budget"),
        &path.field("deterministic_budget"),
        MachineApiErrorKind::InvalidReplayPlan,
    )?;
    let candidate_hash = parse_hash_field(
        required_field(&object, "candidate_hash"),
        "candidate_hash",
        &path.field("candidate_hash"),
    )?;
    let deterministic_budget_hash = parse_hash_field(
        required_field(&object, "deterministic_budget_hash"),
        "deterministic_budget_hash",
        &path.field("deterministic_budget_hash"),
    )?;
    let proof_delta_hash = parse_hash_field(
        required_field(&object, "proof_delta_hash"),
        "proof_delta_hash",
        &path.field("proof_delta_hash"),
    )?;
    let next_state_fingerprint = parse_hash_field(
        required_field(&object, "next_state_fingerprint"),
        "next_state_fingerprint",
        &path.field("next_state_fingerprint"),
    )?;

    Ok(MachineReplayStep {
        previous_state_fingerprint,
        goal_id,
        candidate,
        deterministic_budget,
        candidate_hash,
        deterministic_budget_hash,
        proof_delta_hash,
        next_state_fingerprint,
    })
}

fn validate_replay_chain(plan: &MachineReplayPlan<'_>) -> Result<(), MachineApiRequestError> {
    if plan.protocol_version != MachineApiVersion::V1 {
        return Err(invalid_string_literal(
            "protocol_version",
            &JsonPath::root().field("plan").field("protocol_version"),
        ));
    }

    if plan.steps.is_empty() {
        if plan.final_state_fingerprint != plan.initial_state_fingerprint {
            return Err(invalid_chain(
                "final_state_fingerprint",
                &JsonPath::root()
                    .field("plan")
                    .field("final_state_fingerprint"),
            ));
        }
        return Ok(());
    }

    if plan.steps[0].previous_state_fingerprint != plan.initial_state_fingerprint {
        return Err(invalid_chain(
            "previous_state_fingerprint",
            &JsonPath::root()
                .field("plan")
                .field("steps")
                .index(0)
                .field("previous_state_fingerprint"),
        ));
    }

    for (index, pair) in plan.steps.windows(2).enumerate() {
        if pair[0].next_state_fingerprint != pair[1].previous_state_fingerprint {
            return Err(invalid_chain(
                "previous_state_fingerprint",
                &JsonPath::root()
                    .field("plan")
                    .field("steps")
                    .index(index + 1)
                    .field("previous_state_fingerprint"),
            ));
        }
    }

    let last = plan.steps.last().expect("non-empty steps checked above");
    if plan.final_state_fingerprint != last.next_state_fingerprint {
        return Err(invalid_chain(
            "final_state_fingerprint",
            &JsonPath::root()
                .field("plan")
                .field("final_state_fingerprint"),
        ));
    }

    for (index, step) in plan.steps.iter().enumerate() {
        let actual = tactic_budget_hash(step.deterministic_budget);
        if step.deterministic_budget_hash != actual {
            return Err(invalid_chain(
                "deterministic_budget_hash",
                &JsonPath::root()
                    .field("plan")
                    .field("steps")
                    .index(index)
                    .field("deterministic_budget_hash"),
            ));
        }
    }

    Ok(())
}

fn run_machine_replay_plan(
    session: &mut MachineProofSession,
    plan: MachineReplayPlan<'_>,
) -> Result<MachineReplayResponse, Box<MachineReplayError>> {
    if plan.session_root_hash != session.session_root_hash {
        return Err(plain_error(
            MachineApiErrorKind::SessionRootHashMismatch,
            MachineApiDiagnosticPhase::ReplayValidation,
            "replay plan session_root_hash does not match current session",
            None,
            None,
        ));
    }
    if plan.initial_state_fingerprint != session.initial_snapshot.state_fingerprint {
        return Err(plain_error(
            MachineApiErrorKind::StateFingerprintMismatch,
            MachineApiDiagnosticPhase::ReplayValidation,
            "replay plan initial_state_fingerprint does not match current session",
            None,
            None,
        ));
    }
    if session.snapshots.session_id() != &session.session_id {
        return Err(plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::ReplayExecution,
            "session snapshot store belongs to a different session",
            None,
            None,
        ));
    }

    let context = MachineSnapshotMaterializationContext {
        session_id: &session.session_id,
        display_scope: &session.machine_display_render_scope,
        callable_interface_table: &session.machine_surface_callable_interface_table,
    };
    let mut current_state =
        initial_replay_state(session, &context, plan.initial_state_fingerprint)?;

    for step in plan.steps {
        current_state = replay_step(session, current_state, step)?;
    }

    let final_snapshot = match session.snapshots.insert_state(&context, current_state) {
        Ok(snapshot) => snapshot,
        Err(MachineSnapshotStoreError::SnapshotQuotaExceeded { .. }) => {
            return Ok(replay_scheduler_stop(
                MachineSchedulerArtifactKind::ResourceLimitExceeded,
            ));
        }
        Err(error) => return Err(final_snapshot_store_error(error)),
    };
    if final_snapshot.state_fingerprint != plan.final_state_fingerprint {
        return Err(plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::ReplayExecution,
            "final replay snapshot fingerprint differs from replay plan",
            None,
            None,
        ));
    }

    Ok(MachineApiResponseEnvelope::Ok(MachineApiOkResponse {
        status: MachineApiResponseStatus::Ok,
        endpoint_fields: MachineReplayOkFields {
            final_snapshot_id: final_snapshot.snapshot_id,
            final_state_fingerprint: final_snapshot.state_fingerprint,
        },
    }))
}

fn initial_replay_state(
    session: &MachineProofSession,
    context: &MachineSnapshotMaterializationContext<'_>,
    initial_state_fingerprint: Hash,
) -> Result<MachineProofState, Box<MachineReplayError>> {
    session
        .snapshots
        .lookup_checked(
            context,
            session.initial_snapshot.snapshot_id,
            initial_state_fingerprint,
        )
        .map(|entry| entry.executable_state_payload.clone())
        .map_err(initial_snapshot_lookup_error)
}

fn replay_step(
    session: &MachineProofSession,
    current_state: MachineProofState,
    step: MachineReplayStep<'_>,
) -> Result<MachineProofState, Box<MachineReplayError>> {
    let tactic_kind = candidate_tactic_kind_for_diagnostic(step.candidate.raw);
    if current_state.fingerprint != step.previous_state_fingerprint {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "current replay state does not match step.previous_state_fingerprint",
        ));
    }
    if !current_state.open_goals.contains(&step.goal_id) {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "replay step goal is not open in current state",
        ));
    }

    let candidate = parse_candidate_payload_at(
        step.candidate.raw,
        &session.root.universe_params,
        tactic_kind,
        &JsonPath::root()
            .field("plan")
            .field("steps")
            .field("candidate"),
    )
    .map_err(|error| {
        replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            format!(
                "replay candidate payload no longer canonicalizes at {}: {:?}",
                json_path_display(&error.path),
                error.reason
            ),
        )
    })?;
    let validated = machine_tactic_validate_machine_tactic_candidate_for_state(
        &current_state,
        step.goal_id,
        candidate,
        step.deterministic_budget,
        MachineTacticProfileVersion::StructuralV2,
        STRUCTURAL_V2_REQUIRED_FEATURES,
    )
    .map_err(|error| replay_adapter_error(error, step.goal_id, tactic_kind))?;
    let tactic_kind = Some(validated.tactic_kind);
    let candidate_payload_hash = validated.candidate_hash;
    let candidate_hash = machine_tactic_proof_candidate_identity_hash(
        session,
        current_state.fingerprint,
        step.goal_id,
        candidate_payload_hash,
        step.deterministic_budget_hash,
    );
    if candidate_hash != step.candidate_hash {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "recomputed candidate_hash does not match replay plan",
        ));
    }

    let run = machine_tactic_run_machine_tactic_with_budget(
        &current_state,
        validated.tactic,
        step.deterministic_budget,
    )
    .map_err(|error| replay_adapter_error(error, step.goal_id, tactic_kind))?;
    if run.deterministic_budget_hash != step.deterministic_budget_hash {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "recomputed deterministic_budget_hash does not match replay plan",
        ));
    }
    if run.candidate_hash != candidate_payload_hash {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "executed candidate payload hash does not match replay candidate",
        ));
    }
    if run.proof_delta_hash != step.proof_delta_hash {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "recomputed proof_delta_hash does not match replay plan",
        ));
    }
    if run.next_state_fingerprint != step.next_state_fingerprint {
        return Err(replay_hash_mismatch(
            step.goal_id,
            tactic_kind,
            "recomputed next_state_fingerprint does not match replay plan",
        ));
    }

    Ok(run.state)
}

pub fn replay_minimal_failing_artifact(
    state: &MachineProofState,
    artifact: &MinimalFailingArtifact,
) -> Result<MachineApiDiagnosticProjection, MinimalFailingArtifactError> {
    validate_minimal_failing_artifact_identity(artifact)?;
    if state.fingerprint != artifact.state_fingerprint {
        return Err(MinimalFailingArtifactError::StateFingerprintMismatch {
            expected: artifact.state_fingerprint,
            actual: state.fingerprint,
        });
    }
    state
        .goal(artifact.goal_id)
        .map_err(|_| MinimalFailingArtifactError::UnknownGoal {
            goal_id: artifact.goal_id,
        })?;
    let actual_goal_fingerprint =
        proof_candidate_goal_fingerprint(state.fingerprint, artifact.goal_id);
    if actual_goal_fingerprint != artifact.goal_fingerprint {
        return Err(MinimalFailingArtifactError::GoalFingerprintMismatch {
            expected: artifact.goal_fingerprint,
            actual: actual_goal_fingerprint,
        });
    }

    let diagnostic = match machine_tactic_validate_machine_tactic_candidate_for_state(
        state,
        artifact.goal_id,
        artifact.candidate.clone(),
        artifact.deterministic_budget,
        artifact.expected_policy.profile_version,
        &artifact.expected_policy.required_features,
    ) {
        Err(error) => error.diagnostic,
        Ok(validated) => match machine_tactic_run_machine_tactic_with_budget(
            state,
            validated.tactic,
            artifact.deterministic_budget,
        ) {
            Err(error) => error.diagnostic,
            Ok(_) => return Err(MinimalFailingArtifactError::CandidateUnexpectedlySucceeded),
        },
    };
    let structured = minimal_failing_artifact_diagnostic_from_projection(&diagnostic)?;
    if structured != artifact.structured_diagnostic {
        return Err(MinimalFailingArtifactError::DiagnosticHashMismatch {
            expected: artifact.structured_diagnostic.diagnostic_hash,
            actual: structured.diagnostic_hash,
        });
    }
    Ok(diagnostic)
}

pub fn replay_focused_replay_failure_artifact(
    state: &MachineProofState,
    artifact: &FocusedReplayFailureArtifact,
) -> Result<MachineApiDiagnosticProjection, MinimalFailingArtifactError> {
    validate_focused_replay_failure_artifact_identity(artifact)?;
    replay_minimal_failing_artifact(state, &artifact.minimal_failing_artifact)
}

fn replay_adapter_error(
    error: Box<MachineTacticAdapterError>,
    goal_id: GoalId,
    fallback_tactic_kind: Option<MachineApiTacticKind>,
) -> Box<MachineReplayError> {
    let tactic_kind = error.diagnostic.tactic_kind.or(fallback_tactic_kind);
    if error.diagnostic.kind == MachineApiErrorKind::InvalidMachineProofState {
        return plain_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::ReplayExecution,
            "replay step hit a machine API / machine tactic invariant failure",
            Some(goal_id),
            tactic_kind,
        );
    }
    replay_hash_mismatch(
        goal_id,
        tactic_kind,
        "replay step deterministic execution no longer matches the plan",
    )
}

fn initial_snapshot_lookup_error(error: MachineSnapshotLookupError) -> Box<MachineReplayError> {
    plain_error(
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::ReplayExecution,
        format!("initial replay snapshot lookup failed: {error:?}"),
        None,
        None,
    )
}

fn final_snapshot_store_error(error: MachineSnapshotStoreError) -> Box<MachineReplayError> {
    plain_error(
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::ReplayExecution,
        format!("final replay snapshot materialization failed: {error:?}"),
        None,
        None,
    )
}

fn replay_hash_mismatch(
    goal_id: GoalId,
    tactic_kind: Option<MachineApiTacticKind>,
    message: impl Into<String>,
) -> Box<MachineReplayError> {
    plain_error(
        MachineApiErrorKind::ReplayHashMismatch,
        MachineApiDiagnosticPhase::ReplayExecution,
        message,
        Some(goal_id),
        tactic_kind,
    )
}

fn request_error(error: MachineApiRequestError) -> Box<MachineReplayError> {
    plain_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
        None,
        None,
    )
}

fn replay_validation_error(error: MachineApiRequestError) -> Box<MachineReplayError> {
    plain_error(
        MachineApiErrorKind::InvalidReplayPlan,
        MachineApiDiagnosticPhase::ReplayValidation,
        format!(
            "replay plan validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
        None,
        None,
    )
}

fn plain_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
    goal_id: Option<GoalId>,
    tactic_kind: Option<MachineApiTacticKind>,
) -> Box<MachineReplayError> {
    let message = message.into();
    let diagnostic = MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id,
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
    let wire = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("replay diagnostics must satisfy machine API wire invariants");
    let response = MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
        status: MachineApiResponseStatus::Error,
        error: wire,
        endpoint_fields: (),
    }));
    Box::new(MachineReplayError {
        diagnostic,
        response,
    })
}

fn replay_scheduler_stop(kind: MachineSchedulerArtifactKind) -> MachineReplayResponse {
    MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
        status: MachineApiResponseStatus::SchedulerStopped,
        scheduler_artifact: MachineSchedulerArtifact {
            kind,
            scope: MachineSchedulerArtifactScope::Replay,
            retryable: true,
        },
        endpoint_fields: (),
    })
}

fn machine_tactic_kind_for_api_kind(kind: MachineApiErrorKind) -> MachineTacticDiagnosticKind {
    match kind {
        MachineApiErrorKind::ReplayHashMismatch
        | MachineApiErrorKind::InvalidReplayPlan
        | MachineApiErrorKind::SessionRootHashMismatch
        | MachineApiErrorKind::StateFingerprintMismatch
        | MachineApiErrorKind::UnknownSession
        | MachineApiErrorKind::InvalidMachineProofState => {
            MachineTacticDiagnosticKind::InvalidMachineProofState
        }
        _ => MachineTacticDiagnosticKind::InvalidMachineProofState,
    }
}

fn required_field<'value, 'src>(
    object: &crate::validation::ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value JsonValue<'src> {
    object.field(field).expect("schema checked required field")
}

fn required_string_field<'value, 'src>(
    object: &crate::validation::ValidatedObject<'value, 'src>,
    field: &str,
) -> &'value str {
    required_field(object, field)
        .string_value()
        .expect("schema checked string field")
}

fn parse_protocol_version_field(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineApiVersion, MachineApiRequestError> {
    MachineApiVersion::parse(
        value
            .string_value()
            .expect("schema checked protocol_version string"),
    )
    .map_err(|_| invalid_string_literal("protocol_version", path))
}

fn parse_hash_field(
    value: &JsonValue<'_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<Hash, MachineApiRequestError> {
    HashString::parse(value.string_value().expect("schema checked hash string"))
        .map(HashString::digest)
        .map_err(|_| invalid_string_literal(field, path))
}

fn invalid_chain(field: &'static str, path: &JsonPath) -> MachineApiRequestError {
    MachineApiRequestError::new(
        MachineApiErrorKind::InvalidReplayPlan,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected: JsonFieldType::String,
            actual: JsonValueKind::String,
        },
    )
}

fn invalid_string_literal(field: &'static str, path: &JsonPath) -> MachineApiRequestError {
    MachineApiRequestError::new(
        MachineApiErrorKind::InvalidReplayPlan,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected: JsonFieldType::String,
            actual: JsonValueKind::String,
        },
    )
}

fn as_invalid_replay_plan(error: MachineApiRequestError) -> MachineApiRequestError {
    MachineApiRequestError::new(
        MachineApiErrorKind::InvalidReplayPlan,
        error.path,
        error.reason,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        format_goal_id_wire, format_hash_string, get_machine_snapshot, run_machine_tactic_request,
        run_machine_verify_request, MachineSnapshotGetOk, MachineTacticRunSuccessFields,
        MachineVerifyOkFields,
    };

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

    fn budget_hash_wire() -> String {
        format_hash_string(&tactic_budget_hash(TacticBudget {
            max_tactic_steps: 64,
            max_whnf_steps: 10000,
            max_conversion_steps: 10000,
            max_rewrite_steps: 100,
            max_meta_allocations: 8,
            max_expr_nodes: 20000,
        }))
    }

    fn run_json(
        session: &MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
        goal_id: GoalId,
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

    fn replay_json(
        session: &MachineProofSession,
        steps: &str,
        final_state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "plan":{{
                "protocol_version":"npa.machine-api.v1",
                "session_root_hash":"{}",
                "initial_state_fingerprint":"{}",
                "steps":{},
                "final_state_fingerprint":"{}"
              }}
            }}"#,
            session.session_id.wire(),
            format_hash_string(&session.session_root_hash),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            steps,
            format_hash_string(&final_state_fingerprint)
        )
    }

    fn snapshot_get_json(
        session: &MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":false
            }}"#,
            session.session_id.wire(),
            snapshot_id.wire(),
            format_hash_string(&state_fingerprint)
        )
    }

    fn verify_json(
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

    fn unwrap_run_ok(response: crate::MachineTacticRunResponse) -> MachineTacticRunSuccessFields {
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected tactic run success");
        };
        ok.endpoint_fields
    }

    fn unwrap_verify_ok(response: crate::MachineVerifyResponse) -> MachineVerifyOkFields {
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected verify success");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Verified);
        ok.endpoint_fields
    }

    fn minimal_failing_artifact_replay_state(theorem_type: npa_kernel::Expr) -> MachineProofState {
        crate::adapter::machine_tactic_start_machine_proof(
            npa_tactic::MachineProofSpec {
                module: npa_cert::Name::from_dotted("ReplayArtifact"),
                theorem_name: npa_cert::Name::from_dotted("ReplayArtifact.thm"),
                source_index: 0,
                universe_params: Vec::new(),
                theorem_type,
            },
            Vec::new(),
            Vec::new(),
            npa_tactic::MachineTacticOptions::default(),
        )
        .expect("minimal failing artifact replay fixture state should start")
        .state
    }

    fn prop_expr() -> npa_kernel::Expr {
        npa_kernel::Expr::sort(npa_kernel::Level::zero())
    }

    fn type0_expr() -> npa_kernel::Expr {
        npa_kernel::Expr::sort(npa_kernel::Level::succ(npa_kernel::Level::zero()))
    }

    #[test]
    fn focused_replay_equivalence_failure_replays_same_structured_diagnostic() {
        let state = minimal_failing_artifact_replay_state(prop_expr());
        let candidate = npa_tactic::MachineTacticCandidate::Exact {
            term: npa_tactic::RawMachineTerm::new("Prop"),
        };
        let budget = TacticBudget::default();
        let baseline = match machine_tactic_validate_machine_tactic_candidate_for_state(
            &state,
            GoalId(0),
            candidate.clone(),
            budget,
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        ) {
            Err(error) => error.diagnostic,
            Ok(validated) => {
                machine_tactic_run_machine_tactic_with_budget(&state, validated.tactic, budget)
                    .expect_err("fixture candidate should fail under the same budget")
                    .diagnostic
            }
        };
        let minimal = crate::build_minimal_failing_artifact(
            &state,
            GoalId(0),
            candidate,
            budget,
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let focused = crate::build_focused_replay_failure_artifact(
            "ReplayArtifact",
            npa_cert::Name::from_dotted("ReplayArtifact.thm"),
            minimal.clone(),
        )
        .expect("focused replay failure artifact should build");

        let minimal_replay = replay_minimal_failing_artifact(&state, &minimal)
            .expect("minimal failing artifact should replay");
        let focused_replay = replay_focused_replay_failure_artifact(&state, &focused)
            .expect("focused replay artifact should replay");

        assert_eq!(minimal_replay, baseline);
        assert_eq!(focused_replay, baseline);
        assert_eq!(
            focused_replay.diagnostic_hash().unwrap(),
            focused
                .minimal_failing_artifact
                .structured_diagnostic
                .diagnostic_hash
        );
    }

    #[test]
    fn focused_replay_equivalence_success_replay_verifies_like_baseline() {
        let mut builder = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let run = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &builder,
                    builder.initial_snapshot.snapshot_id,
                    builder.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    candidate,
                ),
                &mut builder,
            )
            .unwrap(),
        )
        .result;
        let baseline_verify = unwrap_verify_ok(
            run_machine_verify_request(
                &verify_json(&builder, run.next_snapshot_id, run.next_state_fingerprint),
                &builder,
            )
            .expect("baseline closed snapshot should verify source-free"),
        );
        let step = exact_step_json(
            builder.initial_snapshot.state_fingerprint,
            GoalId(0),
            candidate,
            &run,
        );

        let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let replay = run_machine_replay_request(
            &replay_json(
                &replay_session,
                &format!("[{step}]"),
                run.next_state_fingerprint,
            ),
            &mut replay_session,
        )
        .expect("equivalent replay should succeed");
        let MachineApiResponseEnvelope::Ok(replay_ok) = replay else {
            panic!("expected replay ok response");
        };
        let replay_verify = unwrap_verify_ok(
            run_machine_verify_request(
                &verify_json(
                    &replay_session,
                    replay_ok.endpoint_fields.final_snapshot_id,
                    replay_ok.endpoint_fields.final_state_fingerprint,
                ),
                &replay_session,
            )
            .expect("replayed closed snapshot should verify source-free"),
        );

        assert_eq!(replay_verify, baseline_verify);
    }

    #[test]
    fn focused_replay_equivalence_negative_fixtures_are_structured_and_deterministic() {
        let state = minimal_failing_artifact_replay_state(prop_expr());
        let minimal = crate::build_minimal_failing_artifact(
            &state,
            GoalId(0),
            npa_tactic::MachineTacticCandidate::Exact {
                term: npa_tactic::RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");
        let focused = crate::build_focused_replay_failure_artifact(
            "ReplayArtifact",
            npa_cert::Name::from_dotted("ReplayArtifact.thm"),
            minimal,
        )
        .expect("focused replay failure artifact should build");

        let stale_state = minimal_failing_artifact_replay_state(type0_expr());
        assert!(matches!(
            replay_focused_replay_failure_artifact(&stale_state, &focused),
            Err(MinimalFailingArtifactError::StateFingerprintMismatch { .. })
        ));

        let mut modified_candidate = focused.clone();
        modified_candidate.minimal_failing_artifact.candidate =
            npa_tactic::MachineTacticCandidate::Intro {
                name: "p".to_owned(),
            };
        assert!(matches!(
            replay_focused_replay_failure_artifact(&state, &modified_candidate),
            Err(MinimalFailingArtifactError::CandidatePayloadHashMismatch { .. })
        ));

        let mut modified_budget = focused.clone();
        modified_budget
            .minimal_failing_artifact
            .deterministic_budget
            .max_tactic_steps += 1;
        assert!(matches!(
            replay_focused_replay_failure_artifact(&state, &modified_budget),
            Err(MinimalFailingArtifactError::DeterministicBudgetHashMismatch { .. })
        ));

        let mut import_mismatch = focused.clone();
        import_mismatch
            .source_free_verifier_baseline
            .import_identity_hash = [10; 32];
        import_mismatch.artifact_hash =
            crate::focused_replay_failure_artifact_hash(&import_mismatch).unwrap();
        assert!(matches!(
            replay_focused_replay_failure_artifact(&state, &import_mismatch),
            Err(MinimalFailingArtifactError::ImportIdentityHashMismatch { .. })
        ));

        let mut checker_claim = focused;
        checker_claim
            .source_free_verifier_baseline
            .independent_checker_claim = true;
        assert!(matches!(
            replay_focused_replay_failure_artifact(&state, &checker_claim),
            Err(MinimalFailingArtifactError::ProofAcceptanceStateClaim)
        ));

        let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let open_verify_first = run_machine_verify_request(
            &verify_json(
                &replay_session,
                replay_session.initial_snapshot.snapshot_id,
                replay_session.initial_snapshot.state_fingerprint,
            ),
            &replay_session,
        )
        .unwrap_err();
        let open_replay = run_machine_replay_request(
            &replay_json(
                &replay_session,
                "[]",
                replay_session.initial_snapshot.state_fingerprint,
            ),
            &mut replay_session,
        )
        .expect("empty replay only rematerializes the same open state");
        let MachineApiResponseEnvelope::Ok(open_replay_ok) = open_replay else {
            panic!("expected open replay ok response");
        };
        let open_verify_second = run_machine_verify_request(
            &verify_json(
                &replay_session,
                open_replay_ok.endpoint_fields.final_snapshot_id,
                open_replay_ok.endpoint_fields.final_state_fingerprint,
            ),
            &replay_session,
        )
        .unwrap_err();
        assert_eq!(
            open_verify_first.diagnostic.kind,
            MachineApiErrorKind::InvalidVerifyRequest
        );
        assert_eq!(open_verify_first.diagnostic, open_verify_second.diagnostic);
        assert_eq!(
            open_verify_first.diagnostic.diagnostic_hash().unwrap(),
            open_verify_second.diagnostic.diagnostic_hash().unwrap()
        );
    }

    #[test]
    fn focused_replay_equivalence_replay_plan_negative_hashes_are_deterministic() {
        let mut builder =
            crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                .unwrap()
                .session;
        let intro_candidate = r#"{"kind":"intro","name":"p"}"#;
        let intro = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &builder,
                    builder.initial_snapshot.snapshot_id,
                    builder.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    intro_candidate,
                ),
                &mut builder,
            )
            .unwrap(),
        )
        .result;
        let step = exact_step_json(
            builder.initial_snapshot.state_fingerprint,
            GoalId(0),
            intro_candidate,
            &intro,
        );

        let modified_candidate_step = step.replace(
            r#""kind":"intro","name":"p""#,
            r#""kind":"intro","name":"q""#,
        );
        assert_ne!(modified_candidate_step, step);
        let first = {
            let mut session =
                crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                    .unwrap()
                    .session;
            run_machine_replay_request(
                &replay_json(
                    &session,
                    &format!("[{modified_candidate_step}]"),
                    intro.next_state_fingerprint,
                ),
                &mut session,
            )
            .unwrap_err()
        };
        let second = {
            let mut session =
                crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                    .unwrap()
                    .session;
            run_machine_replay_request(
                &replay_json(
                    &session,
                    &format!("[{modified_candidate_step}]"),
                    intro.next_state_fingerprint,
                ),
                &mut session,
            )
            .unwrap_err()
        };
        assert_eq!(first.diagnostic, second.diagnostic);
        assert_eq!(
            first.diagnostic.kind,
            MachineApiErrorKind::ReplayHashMismatch
        );
        assert_eq!(
            first.diagnostic.diagnostic_hash().unwrap(),
            second.diagnostic.diagnostic_hash().unwrap()
        );

        let wrong_budget_hash_step = replace_replay_hash_field(
            &step,
            "deterministic_budget_hash",
            intro.deterministic_budget_hash,
            [0; 32],
        );
        let mut session =
            crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                .unwrap()
                .session;
        let budget_err = run_machine_replay_request(
            &replay_json(
                &session,
                &format!("[{wrong_budget_hash_step}]"),
                intro.next_state_fingerprint,
            ),
            &mut session,
        )
        .unwrap_err();
        assert_eq!(
            budget_err.diagnostic.kind,
            MachineApiErrorKind::InvalidReplayPlan
        );
        assert_eq!(
            budget_err.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayValidation
        );

        let stale_next = [9u8; 32];
        let stale_path_step = replace_replay_hash_field(
            &step,
            "next_state_fingerprint",
            intro.next_state_fingerprint,
            stale_next,
        );
        let first = {
            let mut session =
                crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                    .unwrap()
                    .session;
            run_machine_replay_request(
                &replay_json(&session, &format!("[{stale_path_step}]"), stale_next),
                &mut session,
            )
            .unwrap_err()
        };
        let second = {
            let mut session =
                crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                    .unwrap()
                    .session;
            run_machine_replay_request(
                &replay_json(&session, &format!("[{stale_path_step}]"), stale_next),
                &mut session,
            )
            .unwrap_err()
        };
        assert_eq!(first.diagnostic, second.diagnostic);
        assert_eq!(
            first.diagnostic.kind,
            MachineApiErrorKind::ReplayHashMismatch
        );
        assert_eq!(
            first.diagnostic.diagnostic_hash().unwrap(),
            second.diagnostic.diagnostic_hash().unwrap()
        );
    }

    #[test]
    fn minimal_failing_artifact_replays_structured_diagnostic_and_rejects_stale_snapshot() {
        let state = minimal_failing_artifact_replay_state(prop_expr());
        let artifact = crate::build_minimal_failing_artifact(
            &state,
            GoalId(0),
            npa_tactic::MachineTacticCandidate::Exact {
                term: npa_tactic::RawMachineTerm::new("Prop"),
            },
            TacticBudget::default(),
            MachineTacticProfileVersion::StructuralV2,
            STRUCTURAL_V2_REQUIRED_FEATURES,
        )
        .expect("type-mismatched exact should build a minimal failing artifact");

        let diagnostic = replay_minimal_failing_artifact(&state, &artifact)
            .expect("artifact should focused-replay the same failure");

        assert_eq!(
            diagnostic.diagnostic_hash().unwrap(),
            artifact.structured_diagnostic.diagnostic_hash
        );
        let stale_state = minimal_failing_artifact_replay_state(type0_expr());
        assert!(matches!(
            replay_minimal_failing_artifact(&stale_state, &artifact),
            Err(MinimalFailingArtifactError::StateFingerprintMismatch { .. })
        ));
    }

    fn exact_step_json(
        previous_state_fingerprint: Hash,
        goal_id: GoalId,
        candidate: &str,
        result: &crate::MachineTacticRunSuccessResult,
    ) -> String {
        format!(
            r#"{{
              "previous_state_fingerprint":"{}",
              "goal_id":"{}",
              "candidate":{},
              "deterministic_budget":{},
              "candidate_hash":"{}",
              "deterministic_budget_hash":"{}",
              "proof_delta_hash":"{}",
              "next_state_fingerprint":"{}"
            }}"#,
            format_hash_string(&previous_state_fingerprint),
            format_goal_id_wire(goal_id),
            candidate,
            budget_json(),
            format_hash_string(&result.candidate_hash),
            format_hash_string(&result.deterministic_budget_hash),
            format_hash_string(&result.delta.proof_delta_hash),
            format_hash_string(&result.next_state_fingerprint)
        )
    }

    fn replace_replay_hash_field(
        source: &str,
        field: &str,
        expected: Hash,
        replacement: Hash,
    ) -> String {
        let needle = format!(r#""{field}":"{}""#, format_hash_string(&expected));
        let replacement = format!(r#""{field}":"{}""#, format_hash_string(&replacement));
        assert!(
            source.contains(&needle),
            "replay fixture should contain hash field {field}"
        );
        source.replace(&needle, &replacement)
    }

    #[test]
    fn replay_reexecutes_plan_from_initial_and_materializes_only_final_snapshot() {
        let mut builder =
            crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                .unwrap()
                .session;
        let intro_candidate = r#"{"kind":"intro","name":"p"}"#;
        let intro_response = run_machine_tactic_request(
            &run_json(
                &builder,
                builder.initial_snapshot.snapshot_id,
                builder.initial_snapshot.state_fingerprint,
                GoalId(0),
                intro_candidate,
            ),
            &mut builder,
        )
        .unwrap();
        let intro = unwrap_run_ok(intro_response).result;
        let introduced_goal = intro.new_goals[0];

        let exact_candidate = r#"{"kind":"exact","term":{"source":"p"}}"#;
        let exact_response = run_machine_tactic_request(
            &run_json(
                &builder,
                intro.next_snapshot_id,
                intro.next_state_fingerprint,
                introduced_goal,
                exact_candidate,
            ),
            &mut builder,
        )
        .unwrap();
        let exact = unwrap_run_ok(exact_response).result;

        let steps = format!(
            "[{},{}]",
            exact_step_json(
                builder.initial_snapshot.state_fingerprint,
                GoalId(0),
                intro_candidate,
                &intro
            ),
            exact_step_json(
                intro.next_state_fingerprint,
                introduced_goal,
                exact_candidate,
                &exact
            )
        );
        let mut replay_session =
            crate::create_machine_session(&minimal_session_json("forall (p : Prop), Prop"))
                .unwrap()
                .session;
        assert_eq!(replay_session.session_root_hash, builder.session_root_hash);
        assert_eq!(
            replay_session.initial_snapshot.state_fingerprint,
            builder.initial_snapshot.state_fingerprint
        );
        assert_eq!(replay_session.snapshots.len(), 1);

        let response = run_machine_replay_request(
            &replay_json(&replay_session, &steps, exact.next_state_fingerprint),
            &mut replay_session,
        )
        .unwrap();

        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("expected replay ok response");
        };
        assert_eq!(ok.status, MachineApiResponseStatus::Ok);
        assert_eq!(
            ok.endpoint_fields.final_state_fingerprint,
            exact.next_state_fingerprint
        );
        assert_eq!(replay_session.snapshots.len(), 2);

        let final_snapshot = get_machine_snapshot(
            &snapshot_get_json(
                &replay_session,
                ok.endpoint_fields.final_snapshot_id,
                exact.next_state_fingerprint,
            ),
            [&replay_session],
        )
        .unwrap();
        let MachineSnapshotGetOk { snapshot } = final_snapshot;
        assert!(snapshot.open_goals.is_empty());

        let intermediate = get_machine_snapshot(
            &snapshot_get_json(
                &replay_session,
                intro.next_snapshot_id,
                intro.next_state_fingerprint,
            ),
            [&replay_session],
        )
        .unwrap_err();
        assert_eq!(
            intermediate.diagnostic.kind,
            MachineApiErrorKind::UnknownSnapshot
        );
    }

    #[test]
    fn replay_hash_mismatch_uses_replay_diagnostic_not_candidate_error() {
        let mut builder = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let run = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &builder,
                    builder.initial_snapshot.snapshot_id,
                    builder.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    candidate,
                ),
                &mut builder,
            )
            .unwrap(),
        )
        .result;
        let mut step = exact_step_json(
            builder.initial_snapshot.state_fingerprint,
            GoalId(0),
            candidate,
            &run,
        );
        step = step.replace(
            &format_hash_string(&run.delta.proof_delta_hash),
            "sha256:0000000000000000000000000000000000000000000000000000000000000000",
        );
        let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;

        let err = run_machine_replay_request(
            &replay_json(
                &replay_session,
                &format!("[{step}]"),
                run.next_state_fingerprint,
            ),
            &mut replay_session,
        )
        .unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::ReplayHashMismatch);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayExecution
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(0)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
    }

    #[test]
    fn replay_stale_next_state_fingerprint_failure_is_deterministic() {
        let mut builder = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let run = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &builder,
                    builder.initial_snapshot.snapshot_id,
                    builder.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    candidate,
                ),
                &mut builder,
            )
            .unwrap(),
        )
        .result;
        let stale_next = [9u8; 32];
        let step = exact_step_json(
            builder.initial_snapshot.state_fingerprint,
            GoalId(0),
            candidate,
            &run,
        )
        .replace(
            &format_hash_string(&run.next_state_fingerprint),
            &format_hash_string(&stale_next),
        );

        let first = {
            let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
                .unwrap()
                .session;
            run_machine_replay_request(
                &replay_json(&replay_session, &format!("[{step}]"), stale_next),
                &mut replay_session,
            )
            .unwrap_err()
        };
        let second = {
            let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
                .unwrap()
                .session;
            run_machine_replay_request(
                &replay_json(&replay_session, &format!("[{step}]"), stale_next),
                &mut replay_session,
            )
            .unwrap_err()
        };

        assert_eq!(first.diagnostic, second.diagnostic);
        assert_eq!(
            first.diagnostic.kind,
            MachineApiErrorKind::ReplayHashMismatch
        );
        assert_eq!(
            first.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayExecution
        );
        assert_eq!(first.diagnostic.goal_id, Some(GoalId(0)));
        assert_eq!(
            first.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
    }

    #[test]
    fn replay_candidate_hash_rejects_payload_hash_in_identity_slot() {
        let mut builder = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let run = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &builder,
                    builder.initial_snapshot.snapshot_id,
                    builder.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    candidate,
                ),
                &mut builder,
            )
            .unwrap(),
        )
        .result;
        let payload_hash = crate::adapter::machine_tactic_validate_machine_tactic_candidate(
            GoalId(0),
            npa_tactic::MachineTacticCandidate::Exact {
                term: npa_tactic::RawMachineTerm::new("Prop"),
            },
        )
        .unwrap()
        .candidate_hash;
        assert_ne!(run.candidate_hash, payload_hash);

        let mut step = exact_step_json(
            builder.initial_snapshot.state_fingerprint,
            GoalId(0),
            candidate,
            &run,
        );
        step = step.replace(
            &format_hash_string(&run.candidate_hash),
            &format_hash_string(&payload_hash),
        );
        let mut replay_session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;

        let err = run_machine_replay_request(
            &replay_json(
                &replay_session,
                &format!("[{step}]"),
                run.next_state_fingerprint,
            ),
            &mut replay_session,
        )
        .unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::ReplayHashMismatch);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayExecution
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(0)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
    }

    #[test]
    fn replay_plan_chain_validation_precedes_session_binding() {
        let session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = format!(
            r#"{{
              "session_id":"{}",
              "plan":{{
                "protocol_version":"npa.machine-api.v1",
                "session_root_hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
                "initial_state_fingerprint":"{}",
                "steps":[],
                "final_state_fingerprint":"sha256:1111111111111111111111111111111111111111111111111111111111111111"
              }}
            }}"#,
            session.session_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint)
        );
        let mut session = session;

        let err = run_machine_replay_request(&request, &mut session).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::InvalidReplayPlan);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayValidation
        );
    }

    #[test]
    fn replay_wire_validation_does_not_resolve_level_params_before_binding() {
        let mut session = crate::create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let next_state = [9u8; 32];
        let request = format!(
            r#"{{
              "session_id":"{}",
              "plan":{{
                "protocol_version":"npa.machine-api.v1",
                "session_root_hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
                "initial_state_fingerprint":"{}",
                "steps":[{{
                  "previous_state_fingerprint":"{}",
                  "goal_id":"g0",
                  "candidate":{{
                    "kind":"apply",
                    "head":{{"local":{{"name":"f"}}}},
                    "universe_args":["u"],
                    "args":[]
                  }},
                  "deterministic_budget":{},
                  "candidate_hash":"sha256:1111111111111111111111111111111111111111111111111111111111111111",
                  "deterministic_budget_hash":"{}",
                  "proof_delta_hash":"sha256:2222222222222222222222222222222222222222222222222222222222222222",
                  "next_state_fingerprint":"{}"
                }}],
                "final_state_fingerprint":"{}"
              }}
            }}"#,
            session.session_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            budget_json(),
            budget_hash_wire(),
            format_hash_string(&next_state),
            format_hash_string(&next_state)
        );

        let err = run_machine_replay_request(&request, &mut session).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::SessionRootHashMismatch
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::ReplayValidation
        );
    }
}

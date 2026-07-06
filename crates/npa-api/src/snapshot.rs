use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Hash;
use npa_frontend::MachineSurfaceCallableInterfaceTable;
use npa_tactic::{
    core_expr_hash, goal_id_canonical_bytes, machine_local_context_hash,
    machine_tactic_options_hash, meta_var_id_canonical_bytes, proof_expr_hash,
    validate_machine_proof_state, GoalId, MachineLocalDecl, MachineProofState,
    MachineTacticDiagnostic, MachineTacticDiagnosticKind, MetaVarId,
};
use sha2::{Digest, Sha256};

use crate::adapter::MachineApiTacticKind;
use crate::renderer::{
    render_machine_expr_view, LocalId, MachineDisplayRenderScope, MachineExprRendererContext,
    MachineExprRendererError, MachineExprView, MachineGlobalRefView,
};
use crate::types::{
    MachineApiEndpoint, MachineApiErrorWire, MachineGoalView, MachineLocalView,
    MachineProofSession, MachineProofSnapshot, SessionId, SnapshotId,
};
use crate::validation::{
    parse_request_body, JsonPath, JsonPathElement, MachineApiErrorKind, MachineApiRequestError,
};
use crate::{
    validate_machine_endpoint_envelope, HashString, MachineApiDiagnosticPhase,
    MachineApiDiagnosticProjection, MachineApiUpstreamDiagnostic,
};

const STORED_SNAPSHOT_VIEW_TAG: &str = "npa.machine-api.stored-snapshot-view.v1";
const STORED_EXPR_VIEW_TAG: &str = "npa.machine-api.stored-expr-view.v1";
const LOCAL_NAME_MAP_TAG: &str = "npa.machine-api.local-name-map.v1";
const GOAL_FINGERPRINT_TAG: &str = "npa.machine-api.goal-fingerprint.v1";

#[derive(Clone, Copy, Debug)]
pub struct MachineSnapshotMaterializationContext<'a> {
    pub session_id: &'a SessionId,
    pub display_scope: &'a MachineDisplayRenderScope,
    pub callable_interface_table: &'a MachineSurfaceCallableInterfaceTable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredSnapshotView {
    pub state_fingerprint: Hash,
    pub tactic_options_fingerprint: Hash,
    pub open_goals: Vec<GoalId>,
    pub goals: Vec<MachineGoalView>,
    pub proof_skeleton_hash: Hash,
}

impl StoredSnapshotView {
    pub fn snapshot_id(&self) -> SnapshotId {
        SnapshotId::from_state_fingerprint(self.state_fingerprint)
    }

    pub fn to_snapshot(&self, session_id: &SessionId) -> MachineProofSnapshot {
        MachineProofSnapshot {
            snapshot_id: self.snapshot_id(),
            session_id: session_id.clone(),
            state_fingerprint: self.state_fingerprint,
            tactic_options_fingerprint: self.tactic_options_fingerprint,
            open_goals: self.open_goals.clone(),
            goals: self.goals.clone(),
            proof_skeleton_hash: self.proof_skeleton_hash,
        }
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        stored_snapshot_view_canonical_bytes(self)
    }
}

#[derive(Clone, Debug)]
pub struct StoredSnapshotEntry {
    pub executable_state_payload: MachineProofState,
    pub materialized_view_payload: StoredSnapshotView,
    pub materialized_view_canonical_bytes: Vec<u8>,
}

impl StoredSnapshotEntry {
    pub fn snapshot(&self, session_id: &SessionId) -> MachineProofSnapshot {
        self.materialized_view_payload.to_snapshot(session_id)
    }
}

#[derive(Clone, Debug)]
pub struct MachineSnapshotStore {
    session_id: SessionId,
    max_snapshots: Option<usize>,
    entries: BTreeMap<SnapshotId, StoredSnapshotEntry>,
}

impl MachineSnapshotStore {
    pub fn new(session_id: SessionId) -> Self {
        Self {
            session_id,
            max_snapshots: None,
            entries: BTreeMap::new(),
        }
    }

    pub fn with_max_snapshots(session_id: SessionId, max_snapshots: usize) -> Self {
        Self {
            session_id,
            max_snapshots: Some(max_snapshots),
            entries: BTreeMap::new(),
        }
    }

    pub fn session_id(&self) -> &SessionId {
        &self.session_id
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn insert_state(
        &mut self,
        context: &MachineSnapshotMaterializationContext<'_>,
        state: MachineProofState,
    ) -> Result<MachineProofSnapshot, MachineSnapshotStoreError> {
        let new_entry = materialize_stored_snapshot_entry(context, state)
            .map_err(MachineSnapshotStoreError::Materialization)?;
        let snapshot_id = new_entry.materialized_view_payload.snapshot_id();

        if let Some(existing) = self.entries.get(&snapshot_id) {
            self.self_check_entry(context, snapshot_id, existing)
                .map_err(MachineSnapshotStoreError::Lookup)?;
            if existing.materialized_view_canonical_bytes
                != new_entry.materialized_view_canonical_bytes
            {
                return Err(MachineSnapshotStoreError::Lookup(
                    MachineSnapshotLookupError::StoredSnapshotViewMismatch { snapshot_id },
                ));
            }
            return Ok(existing.snapshot(&self.session_id));
        }

        if self
            .max_snapshots
            .is_some_and(|max_snapshots| self.entries.len() >= max_snapshots)
        {
            return Err(MachineSnapshotStoreError::SnapshotQuotaExceeded {
                max_snapshots: self.max_snapshots.expect("checked above"),
            });
        }

        self.self_check_entry(context, snapshot_id, &new_entry)
            .map_err(MachineSnapshotStoreError::Lookup)?;
        let snapshot = new_entry.snapshot(&self.session_id);
        self.entries.insert(snapshot_id, new_entry);
        Ok(snapshot)
    }

    pub fn lookup_checked(
        &self,
        context: &MachineSnapshotMaterializationContext<'_>,
        snapshot_id: SnapshotId,
        requested_state_fingerprint: Hash,
    ) -> Result<&StoredSnapshotEntry, MachineSnapshotLookupError> {
        let entry = self
            .entries
            .get(&snapshot_id)
            .ok_or(MachineSnapshotLookupError::UnknownSnapshot { snapshot_id })?;
        self.self_check_entry(context, snapshot_id, entry)?;
        if entry.materialized_view_payload.state_fingerprint != requested_state_fingerprint {
            return Err(MachineSnapshotLookupError::StateFingerprintMismatch {
                snapshot_id,
                requested: requested_state_fingerprint,
                actual: entry.materialized_view_payload.state_fingerprint,
            });
        }
        Ok(entry)
    }

    fn self_check_entry(
        &self,
        context: &MachineSnapshotMaterializationContext<'_>,
        snapshot_id: SnapshotId,
        entry: &StoredSnapshotEntry,
    ) -> Result<(), MachineSnapshotLookupError> {
        if entry.materialized_view_payload.snapshot_id() != snapshot_id {
            return Err(MachineSnapshotLookupError::SnapshotIdentityMismatch {
                snapshot_id,
                state_fingerprint: entry.materialized_view_payload.state_fingerprint,
            });
        }

        let stored_view_bytes =
            stored_snapshot_view_canonical_bytes(&entry.materialized_view_payload);
        if stored_view_bytes != entry.materialized_view_canonical_bytes {
            return Err(MachineSnapshotLookupError::StoredSnapshotViewMismatch { snapshot_id });
        }

        let rematerialized =
            materialize_stored_snapshot_entry(context, entry.executable_state_payload.clone())
                .map_err(
                    |source| MachineSnapshotLookupError::InvalidMachineProofState {
                        snapshot_id,
                        source,
                    },
                )?;
        if rematerialized.materialized_view_payload.state_fingerprint
            != entry.materialized_view_payload.state_fingerprint
        {
            return Err(
                MachineSnapshotLookupError::ExecutableStateFingerprintMismatch {
                    snapshot_id,
                    expected: entry.materialized_view_payload.state_fingerprint,
                    actual: rematerialized.materialized_view_payload.state_fingerprint,
                },
            );
        }
        if rematerialized.materialized_view_canonical_bytes
            != entry.materialized_view_canonical_bytes
        {
            return Err(MachineSnapshotLookupError::StoredSnapshotViewMismatch { snapshot_id });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSnapshotStoreError {
    Materialization(MachineSnapshotMaterializationError),
    Lookup(MachineSnapshotLookupError),
    SnapshotQuotaExceeded { max_snapshots: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSnapshotLookupError {
    UnknownSnapshot {
        snapshot_id: SnapshotId,
    },
    SnapshotIdentityMismatch {
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
    },
    InvalidMachineProofState {
        snapshot_id: SnapshotId,
        source: MachineSnapshotMaterializationError,
    },
    ExecutableStateFingerprintMismatch {
        snapshot_id: SnapshotId,
        expected: Hash,
        actual: Hash,
    },
    StoredSnapshotViewMismatch {
        snapshot_id: SnapshotId,
    },
    StateFingerprintMismatch {
        snapshot_id: SnapshotId,
        requested: Hash,
        actual: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSnapshotMaterializationError {
    InvalidMachineProofState {
        diagnostic: Box<MachineTacticDiagnostic>,
    },
    RenderFailed {
        source: Box<MachineExprRendererError>,
    },
    GoalOrderMismatch {
        open_goals: Vec<GoalId>,
        materialized_goals: Vec<GoalId>,
    },
    TargetHashMismatch {
        goal_id: GoalId,
        expected: Hash,
        actual: Hash,
    },
    LocalIdMismatch {
        goal_id: GoalId,
        expected: LocalId,
        actual: LocalId,
    },
    BinderIndexMismatch {
        goal_id: GoalId,
        local_id: LocalId,
        expected: u32,
        actual: u32,
    },
    InvalidLocalDependency {
        goal_id: GoalId,
        local_id: LocalId,
        dependency: LocalId,
    },
    DuplicateAllowedTactic {
        tactic: MachineApiTacticKind,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSnapshotGetRequest {
    pub session_id: SessionId,
    pub snapshot_id: SnapshotId,
    pub state_fingerprint: Hash,
    pub include_pretty: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSnapshotGetOk {
    pub snapshot: MachineProofSnapshot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSnapshotGetError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub error: MachineApiErrorWire,
}

pub fn get_machine_snapshot<'session>(
    source: &str,
    sessions: impl IntoIterator<Item = &'session MachineProofSession>,
) -> Result<MachineSnapshotGetOk, Box<MachineSnapshotGetError>> {
    let request = parse_machine_snapshot_get_request(source).map_err(snapshot_request_error)?;
    let Some(session) = sessions
        .into_iter()
        .find(|session| session.session_id == request.session_id)
    else {
        return Err(snapshot_semantic_error(
            MachineApiErrorKind::UnknownSession,
            MachineApiDiagnosticPhase::SessionLookup,
            format!("unknown session {}", request.session_id.wire()),
        ));
    };

    get_machine_snapshot_from_session_request(session, request)
}

pub fn get_machine_snapshot_from_session(
    source: &str,
    session: &MachineProofSession,
) -> Result<MachineSnapshotGetOk, Box<MachineSnapshotGetError>> {
    get_machine_snapshot(source, std::iter::once(session))
}

pub fn parse_machine_snapshot_get_request(
    source: &str,
) -> Result<MachineSnapshotGetRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidSnapshotRequest)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        MachineApiEndpoint::SnapshotGet,
        &JsonPath::root(),
    )?;
    let session_id = SessionId::parse(required_string(&envelope, "session_id"))
        .expect("endpoint validation checked session_id grammar");
    let snapshot_id = SnapshotId::parse(required_string(&envelope, "snapshot_id"))
        .expect("endpoint validation checked snapshot_id grammar");
    let state_fingerprint = HashString::parse(required_string(&envelope, "state_fingerprint"))
        .expect("endpoint validation checked state_fingerprint grammar")
        .digest();
    let include_pretty = envelope
        .field("include_pretty")
        .and_then(crate::JsonValue::bool_value)
        .expect("endpoint validation checked include_pretty bool");

    Ok(MachineSnapshotGetRequest {
        session_id,
        snapshot_id,
        state_fingerprint,
        include_pretty,
    })
}

fn get_machine_snapshot_from_session_request(
    session: &MachineProofSession,
    request: MachineSnapshotGetRequest,
) -> Result<MachineSnapshotGetOk, Box<MachineSnapshotGetError>> {
    if session.snapshots.session_id() != &session.session_id {
        return Err(snapshot_semantic_error(
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
        .map_err(snapshot_lookup_error)?;
    let mut snapshot = entry
        .materialized_view_payload
        .to_snapshot(&session.session_id);
    if request.include_pretty {
        attach_pretty_projection(&mut snapshot);
    }
    Ok(MachineSnapshotGetOk { snapshot })
}

pub fn materialize_machine_proof_snapshot(
    context: &MachineSnapshotMaterializationContext<'_>,
    state: &MachineProofState,
) -> Result<MachineProofSnapshot, MachineSnapshotMaterializationError> {
    let entry = materialize_stored_snapshot_entry(context, state.clone())?;
    Ok(entry.snapshot(context.session_id))
}

fn materialize_stored_snapshot_entry(
    context: &MachineSnapshotMaterializationContext<'_>,
    state: MachineProofState,
) -> Result<StoredSnapshotEntry, MachineSnapshotMaterializationError> {
    let view = materialize_stored_snapshot_view(context, &state)?;
    let materialized_view_canonical_bytes = stored_snapshot_view_canonical_bytes(&view);
    Ok(StoredSnapshotEntry {
        executable_state_payload: state,
        materialized_view_payload: view,
        materialized_view_canonical_bytes,
    })
}

fn materialize_stored_snapshot_view(
    context: &MachineSnapshotMaterializationContext<'_>,
    state: &MachineProofState,
) -> Result<StoredSnapshotView, MachineSnapshotMaterializationError> {
    validate_machine_proof_state(state).map_err(|diagnostic| {
        MachineSnapshotMaterializationError::InvalidMachineProofState {
            diagnostic: Box::new(diagnostic),
        }
    })?;

    let allowed_tactics = allowed_tactics(state)?;
    let mut goals = Vec::with_capacity(state.open_goals.len());
    for goal_id in &state.open_goals {
        goals.push(materialize_goal_view(
            context,
            state,
            *goal_id,
            &allowed_tactics,
        )?);
    }
    validate_goal_order(&state.open_goals, &goals)?;

    Ok(StoredSnapshotView {
        state_fingerprint: state.fingerprint,
        tactic_options_fingerprint: machine_tactic_options_hash(&state.env.options),
        open_goals: state.open_goals.clone(),
        goals,
        proof_skeleton_hash: proof_expr_hash(&state.root.body),
    })
}

fn materialize_goal_view(
    context: &MachineSnapshotMaterializationContext<'_>,
    state: &MachineProofState,
    goal_id: GoalId,
    allowed_tactics: &[MachineApiTacticKind],
) -> Result<MachineGoalView, MachineSnapshotMaterializationError> {
    let goal = state.goal(goal_id).map_err(|diagnostic| {
        MachineSnapshotMaterializationError::InvalidMachineProofState {
            diagnostic: Box::new(diagnostic),
        }
    })?;
    let renderer_context_locals = goal
        .context
        .iter()
        .map(frontend_local_decl)
        .collect::<Vec<_>>();
    let mut locals = Vec::with_capacity(goal.context.len());
    for (index, local) in goal.context.iter().enumerate() {
        locals.push(materialize_local_view(
            context,
            state,
            goal_id,
            &renderer_context_locals,
            index,
            local,
        )?);
    }
    let target_context = MachineExprRendererContext {
        display_scope: context.display_scope,
        callable_interface_table: context.callable_interface_table,
        base_context: &renderer_context_locals,
        universe_params: &state.root.universe_params,
    };
    let target = render_machine_expr_view(&goal.target, &target_context).map_err(|source| {
        MachineSnapshotMaterializationError::RenderFailed {
            source: Box::new(source),
        }
    })?;
    if target.core_hash != goal.target_hash {
        return Err(MachineSnapshotMaterializationError::TargetHashMismatch {
            goal_id,
            expected: goal.target_hash,
            actual: target.core_hash,
        });
    }
    if core_expr_hash(&goal.target) != goal.target_hash {
        return Err(MachineSnapshotMaterializationError::TargetHashMismatch {
            goal_id,
            expected: goal.target_hash,
            actual: core_expr_hash(&goal.target),
        });
    }
    let local_name_map_hash = local_name_map_hash(&locals);
    let goal_fingerprint = goal_fingerprint(
        goal.id,
        goal.meta_id,
        goal.context_hash,
        goal.target_hash,
        local_name_map_hash,
    );

    Ok(MachineGoalView {
        goal_id: goal.id,
        meta_id: goal.meta_id,
        context_hash: machine_local_context_hash(&goal.context),
        local_name_map_hash,
        context: locals,
        target,
        target_hash: goal.target_hash,
        goal_fingerprint,
        allowed_tactics: allowed_tactics.to_vec(),
    })
}

fn materialize_local_view(
    context: &MachineSnapshotMaterializationContext<'_>,
    state: &MachineProofState,
    goal_id: GoalId,
    renderer_context_locals: &[npa_frontend::MachineLocalDecl],
    index: usize,
    local: &MachineLocalDecl,
) -> Result<MachineLocalView, MachineSnapshotMaterializationError> {
    let local_id = LocalId(u32::try_from(index).map_err(|_| {
        MachineSnapshotMaterializationError::InvalidLocalDependency {
            goal_id,
            local_id: LocalId(u32::MAX),
            dependency: LocalId(u32::MAX),
        }
    })?);
    let base_context = &renderer_context_locals[..index];
    let ty_context = MachineExprRendererContext {
        display_scope: context.display_scope,
        callable_interface_table: context.callable_interface_table,
        base_context,
        universe_params: &state.root.universe_params,
    };
    let ty = render_machine_expr_view(&local.ty, &ty_context).map_err(|source| {
        MachineSnapshotMaterializationError::RenderFailed {
            source: Box::new(source),
        }
    })?;
    let value = local
        .value
        .as_ref()
        .map(|value| {
            render_machine_expr_view(value, &ty_context).map_err(|source| {
                MachineSnapshotMaterializationError::RenderFailed {
                    source: Box::new(source),
                }
            })
        })
        .transpose()?;
    let depends_on = local_depends_on(goal_id, local_id, index, &ty, value.as_ref())?;
    let binder_index = u32::try_from(index).map_err(|_| {
        MachineSnapshotMaterializationError::BinderIndexMismatch {
            goal_id,
            local_id,
            expected: u32::MAX,
            actual: u32::MAX,
        }
    })?;

    Ok(MachineLocalView {
        local_id,
        machine_name: local.name.clone(),
        display_name: local.name.clone(),
        ty,
        value,
        depends_on,
        binder_index,
    })
}

fn frontend_local_decl(local: &MachineLocalDecl) -> npa_frontend::MachineLocalDecl {
    npa_frontend::MachineLocalDecl {
        name: local.name.clone(),
        ty: local.ty.clone(),
        value: local.value.clone(),
    }
}

fn local_depends_on(
    goal_id: GoalId,
    local_id: LocalId,
    context_index: usize,
    ty: &MachineExprView,
    value: Option<&MachineExprView>,
) -> Result<Vec<LocalId>, MachineSnapshotMaterializationError> {
    let mut deps = BTreeSet::new();
    for dependency in ty
        .free_locals
        .iter()
        .chain(value.into_iter().flat_map(|view| view.free_locals.iter()))
    {
        if dependency.0 as usize >= context_index {
            return Err(
                MachineSnapshotMaterializationError::InvalidLocalDependency {
                    goal_id,
                    local_id,
                    dependency: *dependency,
                },
            );
        }
        deps.insert(*dependency);
    }
    Ok(deps.into_iter().collect())
}

fn validate_goal_order(
    open_goals: &[GoalId],
    goals: &[MachineGoalView],
) -> Result<(), MachineSnapshotMaterializationError> {
    let materialized_goals = goals.iter().map(|goal| goal.goal_id).collect::<Vec<_>>();
    if open_goals != materialized_goals {
        return Err(MachineSnapshotMaterializationError::GoalOrderMismatch {
            open_goals: open_goals.to_vec(),
            materialized_goals,
        });
    }
    Ok(())
}

fn allowed_tactics(
    state: &MachineProofState,
) -> Result<Vec<MachineApiTacticKind>, MachineSnapshotMaterializationError> {
    let mut tactics = vec![
        MachineApiTacticKind::Intro,
        MachineApiTacticKind::Exact,
        MachineApiTacticKind::Apply,
    ];
    if state.env.eq_family.is_some() {
        tactics.push(MachineApiTacticKind::Rw);
        tactics.push(MachineApiTacticKind::SimpLite);
    }
    if state.env.nat_family.is_some() {
        tactics.push(MachineApiTacticKind::InductionNat);
    }
    tactics.sort();
    let mut seen = BTreeSet::new();
    for tactic in &tactics {
        if !seen.insert(*tactic) {
            return Err(
                MachineSnapshotMaterializationError::DuplicateAllowedTactic { tactic: *tactic },
            );
        }
    }
    Ok(tactics)
}

fn local_name_map_hash(locals: &[MachineLocalView]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_NAME_MAP_TAG);
    encode_list_len(&mut out, locals.len());
    for (index, local) in locals.iter().enumerate() {
        let expected = LocalId(index as u32);
        debug_assert_eq!(local.local_id, expected);
        out.extend(local.local_id.canonical_bytes());
        encode_uvar(&mut out, u64::from(local.binder_index));
        encode_string(&mut out, &local.machine_name);
    }
    sha256(&out)
}

fn goal_fingerprint(
    goal_id: GoalId,
    meta_id: MetaVarId,
    context_hash: Hash,
    target_hash: Hash,
    local_name_map_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, GOAL_FINGERPRINT_TAG);
    out.extend(goal_id_canonical_bytes(goal_id));
    out.extend(meta_var_id_canonical_bytes(meta_id));
    out.extend(context_hash);
    out.extend(target_hash);
    out.extend(local_name_map_hash);
    sha256(&out)
}

pub fn stored_snapshot_view_canonical_bytes(view: &StoredSnapshotView) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, STORED_SNAPSHOT_VIEW_TAG);
    out.extend(view.state_fingerprint);
    out.extend(view.tactic_options_fingerprint);
    encode_list_len(&mut out, view.open_goals.len());
    for goal_id in &view.open_goals {
        out.extend(goal_id_canonical_bytes(*goal_id));
    }
    encode_list_len(&mut out, view.goals.len());
    for goal in &view.goals {
        encode_goal_view(&mut out, goal);
    }
    out.extend(view.proof_skeleton_hash);
    out
}

fn encode_goal_view(out: &mut Vec<u8>, goal: &MachineGoalView) {
    out.extend(goal_id_canonical_bytes(goal.goal_id));
    out.extend(meta_var_id_canonical_bytes(goal.meta_id));
    out.extend(goal.context_hash);
    out.extend(goal.local_name_map_hash);
    encode_list_len(out, goal.context.len());
    for local in &goal.context {
        encode_local_view(out, local);
    }
    encode_expr_view(out, &goal.target);
    out.extend(goal.target_hash);
    out.extend(goal.goal_fingerprint);
    encode_list_len(out, goal.allowed_tactics.len());
    for tactic in &goal.allowed_tactics {
        encode_string(out, tactic.as_str());
    }
}

fn encode_local_view(out: &mut Vec<u8>, local: &MachineLocalView) {
    out.extend(local.local_id.canonical_bytes());
    encode_string(out, &local.machine_name);
    encode_string(out, &local.display_name);
    encode_expr_view(out, &local.ty);
    match &local.value {
        Some(value) => {
            out.push(0x01);
            encode_expr_view(out, value);
        }
        None => out.push(0x00),
    }
    encode_list_len(out, local.depends_on.len());
    for dependency in &local.depends_on {
        out.extend(dependency.canonical_bytes());
    }
    encode_uvar(out, u64::from(local.binder_index));
}

fn encode_expr_view(out: &mut Vec<u8>, view: &MachineExprView) {
    encode_string(out, STORED_EXPR_VIEW_TAG);
    out.extend(view.core_hash);
    match &view.head {
        Some(head) => {
            out.push(0x01);
            encode_global_ref_view(out, head);
        }
        None => out.push(0x00),
    }
    encode_list_len(out, view.constants.len());
    for constant in &view.constants {
        encode_global_ref_view(out, constant);
    }
    encode_list_len(out, view.free_locals.len());
    for local in &view.free_locals {
        out.extend(local.canonical_bytes());
    }
    encode_uvar(out, u64::from(view.size));
    encode_string(out, &view.machine);
}

fn encode_global_ref_view(out: &mut Vec<u8>, view: &MachineGlobalRefView) {
    out.extend(view.canonical_bytes());
}

fn attach_pretty_projection(snapshot: &mut MachineProofSnapshot) {
    for goal in &mut snapshot.goals {
        attach_expr_pretty(&mut goal.target);
        for local in &mut goal.context {
            attach_expr_pretty(&mut local.ty);
            if let Some(value) = &mut local.value {
                attach_expr_pretty(value);
            }
        }
    }
}

fn attach_expr_pretty(view: &mut MachineExprView) {
    view.pretty = Some(view.machine.clone());
}

fn snapshot_request_error(error: MachineApiRequestError) -> Box<MachineSnapshotGetError> {
    snapshot_semantic_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        format!(
            "request validation failed at {}: {:?}",
            json_path_display(&error.path),
            error.reason
        ),
    )
}

fn snapshot_lookup_error(err: MachineSnapshotLookupError) -> Box<MachineSnapshotGetError> {
    let kind = match err {
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
    snapshot_semantic_error(
        kind,
        MachineApiDiagnosticPhase::SnapshotLookup,
        format!("snapshot lookup failed: {err:?}"),
    )
}

fn snapshot_semantic_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachineSnapshotGetError> {
    let message = message.into();
    let diagnostic = MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id: None,
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
    let error = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("snapshot get diagnostics must satisfy machine API wire invariants");
    Box::new(MachineSnapshotGetError { diagnostic, error })
}

fn required_string<'value, 'src>(
    envelope: &crate::MachineValidatedEndpointEnvelope<'value, 'src>,
    field: &str,
) -> &'value str {
    envelope
        .field(field)
        .and_then(crate::JsonValue::string_value)
        .expect("endpoint validation checked required string field")
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

fn sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn encode_list_len(out: &mut Vec<u8>, len: usize) {
    encode_uvar(out, len as u64);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{create_machine_session, format_hash_string};
    use npa_frontend::MachineSurfaceCallableInterfaceTable;
    use npa_kernel::{Expr, Level};
    use npa_tactic::{
        run_machine_tactic, start_machine_proof, MachineProofSpec, MachineTactic,
        MachineTacticOptions,
    };

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn pi_prop_prop() -> Expr {
        Expr::pi("p", prop(), prop())
    }

    fn start_state(theorem_type: Expr) -> MachineProofState {
        start_machine_proof(
            MachineProofSpec {
                module: npa_cert::Name::from_dotted("Test"),
                theorem_name: npa_cert::Name::from_dotted("Test.thm"),
                source_index: 0,
                universe_params: Vec::new(),
                theorem_type,
            },
            Vec::new(),
            Vec::new(),
            MachineTacticOptions::default(),
        )
        .unwrap()
    }

    fn context<'a>(
        session_id: &'a SessionId,
        display_scope: &'a MachineDisplayRenderScope,
        callable_table: &'a MachineSurfaceCallableInterfaceTable,
    ) -> MachineSnapshotMaterializationContext<'a> {
        MachineSnapshotMaterializationContext {
            session_id,
            display_scope,
            callable_interface_table: callable_table,
        }
    }

    fn empty_callable_table() -> MachineSurfaceCallableInterfaceTable {
        MachineSurfaceCallableInterfaceTable::from_entries(Vec::new()).unwrap()
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
            default_options_json("[]")
        )
    }

    fn snapshot_get_json(
        session_id: &SessionId,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
        include_pretty: bool,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":{}
            }}"#,
            session_id.wire(),
            snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
            include_pretty
        )
    }

    #[test]
    fn snapshot_materialization_is_deterministic_and_content_addressed() {
        let state = start_state(prop());
        let session_id = SessionId::new_unchecked("msess_test");
        let display_scope = MachineDisplayRenderScope::empty();
        let callable_table = empty_callable_table();
        let context = context(&session_id, &display_scope, &callable_table);

        let first = materialize_stored_snapshot_entry(&context, state.clone()).unwrap();
        let second = materialize_stored_snapshot_entry(&context, state).unwrap();

        assert_eq!(
            first.materialized_view_canonical_bytes,
            second.materialized_view_canonical_bytes
        );
        assert_eq!(
            first.materialized_view_payload.state_fingerprint,
            first.executable_state_payload.fingerprint
        );
        assert_eq!(
            first.materialized_view_payload.snapshot_id(),
            SnapshotId::from_state_fingerprint(first.executable_state_payload.fingerprint)
        );
        assert_eq!(
            first.materialized_view_payload.proof_skeleton_hash,
            proof_expr_hash(&first.executable_state_payload.root.body)
        );
    }

    #[test]
    fn snapshot_goal_view_materializes_local_name_map_and_allowed_tactics() {
        let state = start_state(pi_prop_prop());
        let (state, _) = run_machine_tactic(
            &state,
            MachineTactic::Intro {
                goal_id: GoalId(0),
                name: "p".to_owned(),
            },
        )
        .unwrap();
        let session_id = SessionId::new_unchecked("msess_test");
        let display_scope = MachineDisplayRenderScope::empty();
        let callable_table = empty_callable_table();
        let context = context(&session_id, &display_scope, &callable_table);

        let snapshot = materialize_machine_proof_snapshot(&context, &state).unwrap();

        assert_eq!(snapshot.open_goals, vec![GoalId(1)]);
        assert_eq!(snapshot.goals.len(), 1);
        let goal = &snapshot.goals[0];
        assert_eq!(goal.context.len(), 1);
        assert_eq!(goal.context[0].local_id, LocalId(0));
        assert_eq!(goal.context[0].binder_index, 0);
        assert_eq!(goal.context[0].machine_name, "p");
        assert_eq!(goal.context[0].display_name, "p");
        assert!(goal.context[0].depends_on.is_empty());
        assert!(goal.allowed_tactics.starts_with(&[
            MachineApiTacticKind::Intro,
            MachineApiTacticKind::Exact,
            MachineApiTacticKind::Apply
        ]));
        assert_eq!(
            goal.allowed_tactics
                .windows(2)
                .filter(|window| window[0] > window[1])
                .count(),
            0
        );
        assert_ne!(goal.local_name_map_hash, [0; 32]);
        assert_ne!(goal.goal_fingerprint, [0; 32]);
    }

    #[test]
    fn store_lookup_checks_snapshot_before_request_fingerprint_mismatch() {
        let state = start_state(type0());
        let session_id = SessionId::new_unchecked("msess_test");
        let display_scope = MachineDisplayRenderScope::empty();
        let callable_table = empty_callable_table();
        let context = context(&session_id, &display_scope, &callable_table);
        let mut store = MachineSnapshotStore::new(session_id.clone());
        let snapshot = store.insert_state(&context, state).unwrap();

        let entry = store.entries.get_mut(&snapshot.snapshot_id).unwrap();
        entry.materialized_view_payload.proof_skeleton_hash = [9; 32];
        entry.materialized_view_canonical_bytes =
            stored_snapshot_view_canonical_bytes(&entry.materialized_view_payload);

        let err = store
            .lookup_checked(&context, snapshot.snapshot_id, [7; 32])
            .unwrap_err();

        assert!(matches!(
            err,
            MachineSnapshotLookupError::StoredSnapshotViewMismatch { .. }
        ));
    }

    #[test]
    fn store_lookup_reports_state_fingerprint_mismatch_after_self_check() {
        let state = start_state(type0());
        let session_id = SessionId::new_unchecked("msess_test");
        let display_scope = MachineDisplayRenderScope::empty();
        let callable_table = empty_callable_table();
        let context = context(&session_id, &display_scope, &callable_table);
        let mut store = MachineSnapshotStore::new(session_id.clone());
        let snapshot = store.insert_state(&context, state).unwrap();

        let err = store
            .lookup_checked(&context, snapshot.snapshot_id, [7; 32])
            .unwrap_err();

        assert!(matches!(
            err,
            MachineSnapshotLookupError::StateFingerprintMismatch { .. }
        ));
    }

    #[test]
    fn store_reuses_same_snapshot_without_overwriting_corrupt_existing_entry() {
        let state = start_state(type0());
        let session_id = SessionId::new_unchecked("msess_test");
        let display_scope = MachineDisplayRenderScope::empty();
        let callable_table = empty_callable_table();
        let context = context(&session_id, &display_scope, &callable_table);
        let mut store = MachineSnapshotStore::new(session_id.clone());
        let snapshot = store.insert_state(&context, state.clone()).unwrap();

        let entry = store.entries.get_mut(&snapshot.snapshot_id).unwrap();
        entry.materialized_view_payload.proof_skeleton_hash = [8; 32];
        entry.materialized_view_canonical_bytes =
            stored_snapshot_view_canonical_bytes(&entry.materialized_view_payload);

        let err = store.insert_state(&context, state).unwrap_err();

        assert!(matches!(
            err,
            MachineSnapshotStoreError::Lookup(
                MachineSnapshotLookupError::StoredSnapshotViewMismatch { .. }
            )
        ));
    }

    #[test]
    fn snapshot_get_returns_stored_snapshot_and_pretty_projection() {
        let session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let request = snapshot_get_json(
            &session.session_id,
            session.initial_snapshot.snapshot_id,
            session.initial_snapshot.state_fingerprint,
            false,
        );

        let ok = get_machine_snapshot(&request, [&session]).unwrap();

        assert_eq!(ok.snapshot, session.initial_snapshot);
        assert_eq!(ok.snapshot.goals[0].target.pretty, None);

        let pretty_request = snapshot_get_json(
            &session.session_id,
            session.initial_snapshot.snapshot_id,
            session.initial_snapshot.state_fingerprint,
            true,
        );
        let pretty = get_machine_snapshot(&pretty_request, [&session]).unwrap();

        assert_eq!(
            pretty.snapshot.state_fingerprint,
            session.initial_snapshot.state_fingerprint
        );
        assert_eq!(pretty.snapshot.goals[0].target.machine, "Prop");
        assert_eq!(
            pretty.snapshot.goals[0].target.pretty.as_deref(),
            Some("Prop")
        );
        assert_eq!(session.initial_snapshot.goals[0].target.pretty, None);
    }

    #[test]
    fn snapshot_get_maps_unknown_session_after_request_validation() {
        let session = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let request = snapshot_get_json(
            &SessionId::new_unchecked("msess_missing"),
            session.initial_snapshot.snapshot_id,
            session.initial_snapshot.state_fingerprint,
            false,
        );

        let err = get_machine_snapshot(&request, [&session]).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::UnknownSession);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SessionLookup
        );
    }

    #[test]
    fn snapshot_get_checks_store_before_request_fingerprint_mismatch() {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let snapshot = session.initial_snapshot.clone();
        let entry = session
            .snapshots
            .entries
            .get_mut(&snapshot.snapshot_id)
            .unwrap();
        entry.materialized_view_payload.proof_skeleton_hash = [9; 32];
        entry.materialized_view_canonical_bytes =
            stored_snapshot_view_canonical_bytes(&entry.materialized_view_payload);
        let request = snapshot_get_json(&session.session_id, snapshot.snapshot_id, [7; 32], false);

        let err = get_machine_snapshot(&request, [&session]).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidMachineProofState
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
    }

    #[test]
    fn snapshot_get_reports_state_fingerprint_mismatch_after_self_check() {
        let session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let request = snapshot_get_json(
            &session.session_id,
            session.initial_snapshot.snapshot_id,
            [7; 32],
            false,
        );

        let err = get_machine_snapshot(&request, [&session]).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::StateFingerprintMismatch
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
    }
}

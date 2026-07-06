//! Diagnostic-only counters for the local proof-authoring loop.
//!
//! These measurements are authoring sidecars. They are deliberately not inputs
//! to candidate hashes, replay plan hashes, certificate hashes, verifier
//! verdicts, or checker decisions.

use std::collections::BTreeMap;

use crate::tactic::{
    MachineTacticBatchOkFields, MachineTacticBatchSchedulerFields, MachineTacticRunSuccessFields,
};

pub const FAST_LOOP_MEASUREMENT_SCHEMA: &str = "npa.fast-loop-measurement.v1";
pub const FAST_LOOP_MEASUREMENT_TRUST_BOUNDARY: &str =
    "authoring diagnostic sidecar only; not proof evidence and not checker input";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FastLoopMeasurementMode {
    Disabled,
    Enabled,
}

impl FastLoopMeasurementMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Enabled => "enabled",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FastLoopMeasurementLabel {
    SnapshotLatency,
    RetrievalResultCount,
    CandidateStageCount,
    CandidateBatchElapsed,
    FocusedReplayArtifactBytes,
    ModuleBuildElapsed,
    SourceFreeVerificationElapsed,
}

impl FastLoopMeasurementLabel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SnapshotLatency => "snapshot_latency_ms",
            Self::RetrievalResultCount => "retrieval_result_count",
            Self::CandidateStageCount => "candidate_stage_count",
            Self::CandidateBatchElapsed => "candidate_batch_elapsed_ms",
            Self::FocusedReplayArtifactBytes => "focused_replay_artifact_bytes",
            Self::ModuleBuildElapsed => "module_build_elapsed_ms",
            Self::SourceFreeVerificationElapsed => "source_free_verification_elapsed_ms",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FastLoopMeasurementUnit {
    Count,
    Bytes,
    Milliseconds,
}

impl FastLoopMeasurementUnit {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Count => "count",
            Self::Bytes => "bytes",
            Self::Milliseconds => "ms",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FastLoopCandidateStage {
    Retrieved,
    Generated,
    Validated,
    Executed,
    Accepted,
    Rejected,
}

impl FastLoopCandidateStage {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Retrieved => "retrieved",
            Self::Generated => "generated",
            Self::Validated => "validated",
            Self::Executed => "executed",
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FastLoopAuthoringCacheStatus {
    NotObserved,
    Disabled,
    Hit,
    Miss,
    SchemaMiss,
    Stale,
}

impl FastLoopAuthoringCacheStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotObserved => "not_observed",
            Self::Disabled => "disabled",
            Self::Hit => "hit",
            Self::Miss => "miss",
            Self::SchemaMiss => "schema_miss",
            Self::Stale => "stale",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastLoopMeasurementCounter {
    pub label: FastLoopMeasurementLabel,
    pub stage: Option<FastLoopCandidateStage>,
    pub unit: FastLoopMeasurementUnit,
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastLoopPuaM13HandoffItem {
    pub need: &'static str,
    pub reason: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastLoopMeasurementReport {
    pub schema: &'static str,
    pub mode: FastLoopMeasurementMode,
    pub counters: Vec<FastLoopMeasurementCounter>,
    pub authoring_cache_status: FastLoopAuthoringCacheStatus,
    pub pua_m13_handoff: Vec<FastLoopPuaM13HandoffItem>,
    pub trust_boundary: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastLoopMeasurementRecorder {
    mode: FastLoopMeasurementMode,
    counters: BTreeMap<(FastLoopMeasurementLabel, Option<FastLoopCandidateStage>), u64>,
    authoring_cache_status: FastLoopAuthoringCacheStatus,
}

impl FastLoopMeasurementRecorder {
    pub fn disabled() -> Self {
        Self {
            mode: FastLoopMeasurementMode::Disabled,
            counters: BTreeMap::new(),
            authoring_cache_status: FastLoopAuthoringCacheStatus::Disabled,
        }
    }

    pub fn enabled() -> Self {
        Self {
            mode: FastLoopMeasurementMode::Enabled,
            counters: BTreeMap::new(),
            authoring_cache_status: FastLoopAuthoringCacheStatus::NotObserved,
        }
    }

    pub const fn mode(&self) -> FastLoopMeasurementMode {
        self.mode
    }

    pub const fn is_enabled(&self) -> bool {
        matches!(self.mode, FastLoopMeasurementMode::Enabled)
    }

    pub fn observe_snapshot_latency_ms(&mut self, elapsed_ms: u64) {
        self.add_counter(FastLoopMeasurementLabel::SnapshotLatency, None, elapsed_ms);
    }

    pub fn observe_retrieval_result_count(&mut self, count: u64) {
        self.add_counter(FastLoopMeasurementLabel::RetrievalResultCount, None, count);
    }

    pub fn observe_candidate_stage_count(&mut self, stage: FastLoopCandidateStage, count: u64) {
        self.add_counter(
            FastLoopMeasurementLabel::CandidateStageCount,
            Some(stage),
            count,
        );
    }

    pub fn observe_candidate_batch_elapsed_ms(&mut self, elapsed_ms: u64) {
        self.add_counter(
            FastLoopMeasurementLabel::CandidateBatchElapsed,
            None,
            elapsed_ms,
        );
    }

    pub fn observe_focused_replay_artifact_bytes(&mut self, bytes: u64) {
        self.add_counter(
            FastLoopMeasurementLabel::FocusedReplayArtifactBytes,
            None,
            bytes,
        );
    }

    pub fn observe_focused_replay_artifact_source(&mut self, source: &str) {
        self.observe_focused_replay_artifact_bytes(
            source
                .len()
                .try_into()
                .expect("artifact source length fits in u64"),
        );
    }

    pub fn observe_module_build_elapsed_ms(&mut self, elapsed_ms: u64) {
        self.add_counter(
            FastLoopMeasurementLabel::ModuleBuildElapsed,
            None,
            elapsed_ms,
        );
    }

    pub fn observe_source_free_verification_elapsed_ms(&mut self, elapsed_ms: u64) {
        self.add_counter(
            FastLoopMeasurementLabel::SourceFreeVerificationElapsed,
            None,
            elapsed_ms,
        );
    }

    pub fn observe_authoring_cache_status(&mut self, status: FastLoopAuthoringCacheStatus) {
        if self.is_enabled() {
            self.authoring_cache_status = status;
        }
    }

    pub fn observe_tactic_run_success(&mut self, _fields: &MachineTacticRunSuccessFields) {
        self.observe_candidate_stage_count(FastLoopCandidateStage::Generated, 1);
        self.observe_candidate_stage_count(FastLoopCandidateStage::Validated, 1);
        self.observe_candidate_stage_count(FastLoopCandidateStage::Executed, 1);
        self.observe_candidate_stage_count(FastLoopCandidateStage::Accepted, 1);
    }

    pub fn observe_tactic_batch_ok(
        &mut self,
        requested_candidate_count: usize,
        fields: &MachineTacticBatchOkFields,
    ) {
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Generated,
            requested_candidate_count
                .try_into()
                .expect("candidate count fits in u64"),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Executed,
            fields
                .results
                .len()
                .try_into()
                .expect("candidate result count fits in u64"),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Accepted,
            u64::from(fields.success_count),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Rejected,
            u64::from(fields.failure_count),
        );
    }

    pub fn observe_tactic_batch_scheduler_stop(
        &mut self,
        requested_candidate_count: usize,
        fields: &MachineTacticBatchSchedulerFields,
    ) {
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Generated,
            requested_candidate_count
                .try_into()
                .expect("candidate count fits in u64"),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Executed,
            fields.completed_prefix_len.into(),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Accepted,
            u64::from(fields.success_count),
        );
        self.observe_candidate_stage_count(
            FastLoopCandidateStage::Rejected,
            u64::from(fields.failure_count),
        );
    }

    pub fn report(&self) -> Option<FastLoopMeasurementReport> {
        if !self.is_enabled() {
            return None;
        }

        let counters = self
            .counters
            .iter()
            .map(|((label, stage), value)| FastLoopMeasurementCounter {
                label: *label,
                stage: *stage,
                unit: unit_for_label(*label),
                value: *value,
            })
            .collect();
        Some(FastLoopMeasurementReport {
            schema: FAST_LOOP_MEASUREMENT_SCHEMA,
            mode: self.mode,
            counters,
            authoring_cache_status: self.authoring_cache_status,
            pua_m13_handoff: fast_loop_pua_m13_handoff_items(),
            trust_boundary: FAST_LOOP_MEASUREMENT_TRUST_BOUNDARY,
        })
    }

    fn add_counter(
        &mut self,
        label: FastLoopMeasurementLabel,
        stage: Option<FastLoopCandidateStage>,
        value: u64,
    ) {
        if !self.is_enabled() {
            return;
        }
        *self.counters.entry((label, stage)).or_default() += value;
    }
}

pub fn fast_loop_pua_m13_handoff_items() -> Vec<FastLoopPuaM13HandoffItem> {
    vec![
        FastLoopPuaM13HandoffItem {
            need: "true_batching",
            reason: "share parsing, local-context projection, and validation work across same-snapshot candidates",
        },
        FastLoopPuaM13HandoffItem {
            need: "replay_prefix_cache",
            reason: "reuse verified replay prefixes without treating cache hits as proof evidence",
        },
        FastLoopPuaM13HandoffItem {
            need: "verification_cache",
            reason: "extend authoring-only source-free cache policy without changing verifier authority",
        },
        FastLoopPuaM13HandoffItem {
            need: "sharding",
            reason: "measure stable partition keys and deterministic merge reporting for larger changed sets",
        },
        FastLoopPuaM13HandoffItem {
            need: "performance_gates",
            reason: "turn repeated timing runs into release-blocking KPI checks outside PUA-M07",
        },
    ]
}

pub fn fast_loop_measurement_report_json(report: &FastLoopMeasurementReport) -> String {
    let counters = report
        .counters
        .iter()
        .map(|counter| {
            let stage = counter
                .stage
                .map(|stage| format!(",\"stage\":\"{}\"", json_escape(stage.as_str())))
                .unwrap_or_default();
            format!(
                "{{\"label\":\"{}\"{},\"unit\":\"{}\",\"value\":{}}}",
                json_escape(counter.label.as_str()),
                stage,
                json_escape(counter.unit.as_str()),
                counter.value
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let handoff = report
        .pua_m13_handoff
        .iter()
        .map(|item| {
            format!(
                "{{\"need\":\"{}\",\"reason\":\"{}\"}}",
                json_escape(item.need),
                json_escape(item.reason)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"schema\":\"{}\",\"trusted\":false,\"mode\":\"{}\",\"counters\":[{}],\"authoring_cache_status\":\"{}\",\"pua_m13_handoff\":[{}],\"trust_boundary\":\"{}\"}}",
        json_escape(report.schema),
        json_escape(report.mode.as_str()),
        counters,
        json_escape(report.authoring_cache_status.as_str()),
        handoff,
        json_escape(report.trust_boundary)
    )
}

fn unit_for_label(label: FastLoopMeasurementLabel) -> FastLoopMeasurementUnit {
    match label {
        FastLoopMeasurementLabel::FocusedReplayArtifactBytes => FastLoopMeasurementUnit::Bytes,
        FastLoopMeasurementLabel::SnapshotLatency
        | FastLoopMeasurementLabel::CandidateBatchElapsed
        | FastLoopMeasurementLabel::ModuleBuildElapsed
        | FastLoopMeasurementLabel::SourceFreeVerificationElapsed => {
            FastLoopMeasurementUnit::Milliseconds
        }
        FastLoopMeasurementLabel::RetrievalResultCount
        | FastLoopMeasurementLabel::CandidateStageCount => FastLoopMeasurementUnit::Count,
    }
}

fn json_escape(value: &str) -> String {
    let mut out = String::new();
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        create_machine_session, format_goal_id_wire, format_hash_string, get_machine_snapshot,
        run_machine_replay_request, run_machine_tactic_request, run_machine_verify_request,
        MachineApiResponseEnvelope, MachineApiResponseStatus, MachineTacticRunSuccessResult,
        MachineVerifyOkFields,
    };
    use npa_cert::Hash;
    use npa_tactic::GoalId;
    use sha2::{Digest, Sha256};

    #[derive(Debug, PartialEq, Eq)]
    struct FastLoopSemanticIdentity {
        candidate_hash: Hash,
        deterministic_budget_hash: Hash,
        proof_delta_hash: Hash,
        next_state_fingerprint: Hash,
        replay_plan_hash: Hash,
        replay_final_state_fingerprint: Hash,
        verify_fields: MachineVerifyOkFields,
    }

    #[test]
    fn fast_loop_measurement_report_uses_stable_labels_and_handoff() {
        let mut recorder = FastLoopMeasurementRecorder::enabled();
        recorder.observe_snapshot_latency_ms(3);
        recorder.observe_retrieval_result_count(2);
        recorder.observe_candidate_stage_count(FastLoopCandidateStage::Retrieved, 2);
        recorder.observe_candidate_stage_count(FastLoopCandidateStage::Generated, 4);
        recorder.observe_candidate_stage_count(FastLoopCandidateStage::Validated, 3);
        recorder.observe_candidate_batch_elapsed_ms(5);
        recorder.observe_focused_replay_artifact_bytes(89);
        recorder.observe_module_build_elapsed_ms(13);
        recorder.observe_source_free_verification_elapsed_ms(21);
        recorder.observe_authoring_cache_status(FastLoopAuthoringCacheStatus::Miss);

        let report = recorder.report().expect("enabled recorder should report");
        assert_eq!(report.schema, FAST_LOOP_MEASUREMENT_SCHEMA);
        assert_eq!(report.trust_boundary, FAST_LOOP_MEASUREMENT_TRUST_BOUNDARY);
        assert!(report.counters.iter().any(|counter| counter.label
            == FastLoopMeasurementLabel::SnapshotLatency
            && counter.unit == FastLoopMeasurementUnit::Milliseconds
            && counter.value == 3));
        assert!(report.counters.iter().any(|counter| counter.label
            == FastLoopMeasurementLabel::CandidateStageCount
            && counter.stage == Some(FastLoopCandidateStage::Retrieved)
            && counter.value == 2));
        assert!(report
            .pua_m13_handoff
            .iter()
            .any(|item| item.need == "true_batching"));
        assert!(report
            .pua_m13_handoff
            .iter()
            .any(|item| item.need == "performance_gates"));

        let json = fast_loop_measurement_report_json(&report);
        assert!(json.contains("\"schema\":\"npa.fast-loop-measurement.v1\""));
        assert!(json.contains("\"trusted\":false"));
        assert!(json.contains("\"label\":\"focused_replay_artifact_bytes\""));
        assert!(json.contains("\"authoring_cache_status\":\"miss\""));
        assert!(json.contains("\"need\":\"replay_prefix_cache\""));
        assert!(json.contains("not proof evidence"));
    }

    #[test]
    fn fast_loop_measurement_disabled_recorder_emits_no_sidecar() {
        let mut recorder = FastLoopMeasurementRecorder::disabled();
        recorder.observe_snapshot_latency_ms(3);
        recorder.observe_retrieval_result_count(2);
        recorder.observe_candidate_stage_count(FastLoopCandidateStage::Generated, 4);
        recorder.observe_candidate_batch_elapsed_ms(5);
        recorder.observe_focused_replay_artifact_bytes(89);
        recorder.observe_module_build_elapsed_ms(13);
        recorder.observe_source_free_verification_elapsed_ms(21);
        recorder.observe_authoring_cache_status(FastLoopAuthoringCacheStatus::Miss);

        assert_eq!(recorder.mode(), FastLoopMeasurementMode::Disabled);
        assert!(recorder.report().is_none());
    }

    #[test]
    fn fast_loop_measurement_disabled_output_does_not_change_semantic_results() {
        let mut disabled = FastLoopMeasurementRecorder::disabled();
        let disabled_identity = run_semantic_authoring_flow(&mut disabled);
        assert!(disabled.report().is_none());

        let mut enabled = FastLoopMeasurementRecorder::enabled();
        let enabled_identity = run_semantic_authoring_flow(&mut enabled);
        let report = enabled.report().expect("enabled measurement should report");

        assert_eq!(enabled_identity, disabled_identity);
        assert!(report.counters.iter().any(
            |counter| counter.label == FastLoopMeasurementLabel::SourceFreeVerificationElapsed
        ));
        assert_eq!(
            report.authoring_cache_status,
            FastLoopAuthoringCacheStatus::Disabled
        );
    }

    fn run_semantic_authoring_flow(
        recorder: &mut FastLoopMeasurementRecorder,
    ) -> FastLoopSemanticIdentity {
        let mut session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let _snapshot = get_machine_snapshot(
            &snapshot_get_json(
                &session,
                session.initial_snapshot.snapshot_id,
                session.initial_snapshot.state_fingerprint,
            ),
            std::iter::once(&session),
        )
        .expect("initial snapshot should materialize");
        recorder.observe_snapshot_latency_ms(1);
        recorder.observe_retrieval_result_count(0);

        let candidate = r#"{"kind":"exact","term":{"source":"Prop"}}"#;
        let run_fields = unwrap_run_ok(
            run_machine_tactic_request(
                &run_json(
                    &session,
                    session.initial_snapshot.snapshot_id,
                    session.initial_snapshot.state_fingerprint,
                    GoalId(0),
                    candidate,
                ),
                &mut session,
            )
            .expect("candidate should close Type 0 target"),
        );
        recorder.observe_tactic_run_success(&run_fields);
        recorder.observe_candidate_batch_elapsed_ms(2);

        let step = exact_step_json(
            session.initial_snapshot.state_fingerprint,
            GoalId(0),
            candidate,
            &run_fields.result,
        );
        let mut replay_session = create_machine_session(&minimal_session_json("Type 0"))
            .unwrap()
            .session;
        let replay_plan_source = replay_plan_json(
            &replay_session,
            &format!("[{step}]"),
            run_fields.result.next_state_fingerprint,
        );
        let replay_request = replay_request_json(&replay_session, &replay_plan_source);
        recorder.observe_focused_replay_artifact_source(&replay_request);
        let replay_plan_hash = test_sha256(&replay_plan_source);

        let replay = run_machine_replay_request(&replay_request, &mut replay_session)
            .expect("same replay plan should replay");
        let MachineApiResponseEnvelope::Ok(replay_ok) = replay else {
            panic!("expected replay ok response");
        };
        assert_eq!(replay_ok.status, MachineApiResponseStatus::Ok);

        let verify_fields = unwrap_verify_ok(
            run_machine_verify_request(
                &verify_json(
                    &replay_session,
                    replay_ok.endpoint_fields.final_snapshot_id,
                    replay_ok.endpoint_fields.final_state_fingerprint,
                ),
                &replay_session,
            )
            .expect("replayed closed snapshot should verify"),
        );
        recorder.observe_source_free_verification_elapsed_ms(3);
        recorder.observe_module_build_elapsed_ms(0);
        recorder.observe_authoring_cache_status(FastLoopAuthoringCacheStatus::Disabled);

        FastLoopSemanticIdentity {
            candidate_hash: run_fields.result.candidate_hash,
            deterministic_budget_hash: run_fields.result.deterministic_budget_hash,
            proof_delta_hash: run_fields.result.delta.proof_delta_hash,
            next_state_fingerprint: run_fields.result.next_state_fingerprint,
            replay_plan_hash,
            replay_final_state_fingerprint: replay_ok.endpoint_fields.final_state_fingerprint,
            verify_fields,
        }
    }

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

    fn budget_json() -> String {
        r#"{
          "max_tactic_steps":64,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
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

    fn snapshot_get_json(
        session: &crate::MachineProofSession,
        snapshot_id: crate::SnapshotId,
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

    fn run_json(
        session: &crate::MachineProofSession,
        snapshot_id: crate::SnapshotId,
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

    fn replay_plan_json(
        session: &crate::MachineProofSession,
        steps: &str,
        final_state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "session_root_hash":"{}",
              "initial_state_fingerprint":"{}",
              "steps":{},
              "final_state_fingerprint":"{}"
            }}"#,
            format_hash_string(&session.session_root_hash),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            steps,
            format_hash_string(&final_state_fingerprint)
        )
    }

    fn replay_request_json(session: &crate::MachineProofSession, plan: &str) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "plan":{}
            }}"#,
            session.session_id.wire(),
            plan
        )
    }

    fn verify_json(
        session: &crate::MachineProofSession,
        snapshot_id: crate::SnapshotId,
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

    fn exact_step_json(
        previous_state_fingerprint: Hash,
        goal_id: GoalId,
        candidate: &str,
        result: &MachineTacticRunSuccessResult,
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

    fn test_sha256(source: &str) -> Hash {
        let mut hasher = Sha256::new();
        hasher.update(source.as_bytes());
        hasher.finalize().into()
    }
}

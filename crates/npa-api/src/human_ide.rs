//! Human IDE API boundary.
//!
//! Phase 5 Human (`develop/phase5-human.md`) owns IDE-facing source, display, and
//! state APIs. Phase 5 AI (`develop/phase5-ai.md`) and Phase 7 AI
//! (`develop/phase7-ai.md`) own the deterministic `/machine/*` fast path used by
//! proof search. This module is the P5H-00 boundary marker between those
//! surfaces.
//!
//! The Human IDE API is library-only metadata at this milestone. It does not
//! create `MachineProofSession` implicitly, parse Human text tactics for
//! `/machine/*`, or add Human-only fields to `MachineProofSnapshot` /
//! `MachineTacticCandidate`.

/// Stable profile name for the Human IDE API surface.
///
/// This is intentionally distinct from `MACHINE_API_VERSION`. Human IDE APIs
/// may adapt source text, display payloads, and future IDE state, but they must
/// not implicitly allocate Machine sessions or widen `/machine/*` request
/// grammar.
pub const HUMAN_IDE_API_PROFILE: &str = "npa.human-ide-api.v1";

/// Human IDE API boundary descriptor exported separately from Machine API.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanIdeApiBoundary {
    /// Human IDE profile identifier.
    pub profile: &'static str,
    /// Policy for interaction with Machine proof sessions.
    pub machine_session_policy: HumanIdeMachineSessionPolicy,
    /// Policy for preserving AI proof-search fast paths.
    pub machine_fast_path_policy: HumanIdeMachineFastPathPolicy,
}

/// Human IDE APIs do not create Machine sessions behind the caller's back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanIdeMachineSessionPolicy {
    /// Machine session creation remains an explicit Machine API operation.
    ExplicitMachineSessionOnly,
}

impl HumanIdeMachineSessionPolicy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExplicitMachineSessionOnly => "explicit_machine_session_only",
        }
    }
}

/// Human IDE APIs preserve the deterministic Machine API grammar and hashes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanIdeMachineFastPathPolicy {
    /// Human-only state, display, source span, and assistant payloads stay out of `/machine/*`.
    PreserveMachineApiGrammar,
}

impl HumanIdeMachineFastPathPolicy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PreserveMachineApiGrammar => "preserve_machine_api_grammar",
        }
    }
}

/// Return the Phase 5 Human IDE API boundary descriptor.
///
/// This call is metadata only. It does not create a `MachineProofSession`, does
/// not parse Human text tactics, and does not alter Machine `state_fingerprint`,
/// `candidate_hash`, or `deterministic_budget_hash` semantics.
pub const fn human_ide_api_boundary() -> HumanIdeApiBoundary {
    HumanIdeApiBoundary {
        profile: HUMAN_IDE_API_PROFILE,
        machine_session_policy: HumanIdeMachineSessionPolicy::ExplicitMachineSessionOnly,
        machine_fast_path_policy: HumanIdeMachineFastPathPolicy::PreserveMachineApiGrammar,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        parse_machine_snapshot_get_request, parse_machine_tactic_batch_request,
        parse_machine_tactic_run_request, JsonPath, JsonPathElement, MachineApiErrorKind,
        MachineApiRequestError, MachineApiRequestErrorReason, MachineApiTacticKind,
        MachineProofSnapshot, SessionId, SnapshotId, MACHINE_API_VERSION,
    };
    use npa_tactic::{
        CandidateRewriteRuleRef, MachineTacticCandidate, RawMachineTerm, RewriteDirection,
        RewriteSite, TacticHead,
    };

    use super::*;

    const ZERO_DIGEST: &str = "0000000000000000000000000000000000000000000000000000000000000000";
    const HUMAN_ONLY_FIELD_MARKERS: &[&str] = &[
        "human",
        "source_span",
        "lsp",
        "assistant",
        "pretty_text",
        "text_tactic",
    ];

    #[test]
    fn phase5_human_ide_boundary_exports_distinct_non_session_profile() {
        let boundary = human_ide_api_boundary();

        assert_eq!(boundary.profile, HUMAN_IDE_API_PROFILE);
        assert_ne!(boundary.profile, MACHINE_API_VERSION);
        assert_eq!(
            boundary.machine_session_policy,
            HumanIdeMachineSessionPolicy::ExplicitMachineSessionOnly
        );
        assert_eq!(
            boundary.machine_session_policy.as_str(),
            "explicit_machine_session_only"
        );
        assert_eq!(
            boundary.machine_fast_path_policy,
            HumanIdeMachineFastPathPolicy::PreserveMachineApiGrammar
        );
        assert_eq!(
            boundary.machine_fast_path_policy.as_str(),
            "preserve_machine_api_grammar"
        );
    }

    #[test]
    fn phase5_ai_machine_endpoint_grammar_rejects_human_only_fields() {
        assert_unknown_field(
            parse_machine_tactic_run_request(&machine_tactic_run_with_human_field()).unwrap_err(),
            MachineApiErrorKind::InvalidTacticRunRequest,
            "human_tactic_text",
        );
        assert_unknown_field(
            parse_machine_tactic_batch_request(&machine_tactic_batch_with_human_field())
                .unwrap_err(),
            MachineApiErrorKind::InvalidBatchPolicy,
            "human_tactic_text",
        );
        assert_unknown_field(
            parse_machine_snapshot_get_request(&machine_snapshot_get_with_human_field())
                .unwrap_err(),
            MachineApiErrorKind::InvalidSnapshotRequest,
            "human_source_span",
        );
    }

    #[test]
    fn phase7_ai_machine_candidate_wire_shape_rejects_human_only_fields() {
        let err = crate::tactic::parse_candidate_wire_shape_at(
            r#"{"kind":"intro","name":"x","human_tactic_text":"intro x"}"#,
            Some(MachineApiTacticKind::Intro),
            &JsonPath::root().field("candidate"),
        )
        .unwrap_err();

        assert_unknown_field(
            err,
            MachineApiErrorKind::InvalidCandidate,
            "human_tactic_text",
        );
    }

    #[test]
    fn phase7_ai_machine_snapshot_type_guard_has_no_human_only_fields() {
        let snapshot = MachineProofSnapshot {
            snapshot_id: SnapshotId::from_digest([0; 32]),
            session_id: SessionId::new_unchecked("msess_p5h00"),
            state_fingerprint: [0; 32],
            tactic_options_fingerprint: [0; 32],
            open_goals: Vec::new(),
            goals: Vec::new(),
            proof_skeleton_hash: [0; 32],
        };

        assert_no_human_only_markers(&format!("{snapshot:?}"));
    }

    #[test]
    fn phase7_ai_machine_tactic_candidate_type_guard_has_no_human_only_fields() {
        let local_head = TacticHead::Local {
            name: "h".to_owned(),
        };
        let candidates = [
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("x"),
            },
            MachineTacticCandidate::Intro {
                name: "x".to_owned(),
            },
            MachineTacticCandidate::Apply {
                head: local_head.clone(),
                universe_args: Vec::new(),
                args: Vec::new(),
            },
            MachineTacticCandidate::Rewrite {
                rule: CandidateRewriteRuleRef {
                    head: local_head,
                    universe_args: Vec::new(),
                    args: Vec::new(),
                },
                direction: RewriteDirection::Forward,
                site: RewriteSite::EqTargetLeft,
            },
            MachineTacticCandidate::SimpLite { rules: Vec::new() },
            MachineTacticCandidate::InductionNat {
                local_name: "n".to_owned(),
            },
        ];

        for candidate in candidates {
            assert_no_human_only_markers(&format!("{candidate:?}"));
        }
    }

    fn assert_unknown_field(
        error: MachineApiRequestError,
        expected_kind: MachineApiErrorKind,
        field: &str,
    ) {
        assert_eq!(error.kind, expected_kind);
        assert_eq!(
            error.reason,
            MachineApiRequestErrorReason::UnknownField {
                field: field.to_owned()
            }
        );
        assert_eq!(
            error.path.elements.last(),
            Some(&JsonPathElement::Field(field.to_owned()))
        );
    }

    fn assert_no_human_only_markers(debug: &str) {
        let normalized = debug.to_ascii_lowercase();
        for marker in HUMAN_ONLY_FIELD_MARKERS {
            assert!(
                !normalized.contains(marker),
                "Machine fast-path type debug output contains Human-only marker {marker:?}: {debug}"
            );
        }
    }

    fn machine_tactic_run_with_human_field() -> String {
        format!(
            r#"{{
              "session_id":"msess_p5h00",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidate":{{"kind":"intro","name":"x"}},
              "deterministic_budget":{},
              "human_tactic_text":"intro x"
            }}"#,
            zero_snapshot_id(),
            zero_hash_string(),
            deterministic_budget_json()
        )
    }

    fn machine_tactic_batch_with_human_field() -> String {
        format!(
            r#"{{
              "session_id":"msess_p5h00",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":[{{"kind":"intro","name":"x"}}],
              "deterministic_budget":{},
              "batch_policy":{{
                "max_evaluated_candidates":1,
                "stop_after_successes":1,
                "stop_after_failures":1
              }},
              "human_tactic_text":"intro x"
            }}"#,
            zero_snapshot_id(),
            zero_hash_string(),
            deterministic_budget_json()
        )
    }

    fn machine_snapshot_get_with_human_field() -> String {
        format!(
            r#"{{
              "session_id":"msess_p5h00",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "include_pretty":false,
              "human_source_span":{{"start":0,"end":7}}
            }}"#,
            zero_snapshot_id(),
            zero_hash_string()
        )
    }

    fn deterministic_budget_json() -> &'static str {
        r#"{
          "max_tactic_steps":64,
          "max_whnf_steps":10000,
          "max_conversion_steps":10000,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#
    }

    fn zero_snapshot_id() -> String {
        format!("mst_{ZERO_DIGEST}")
    }

    fn zero_hash_string() -> String {
        format!("sha256:{ZERO_DIGEST}")
    }
}

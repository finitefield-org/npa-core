use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const RESEARCH_TARGET_API_VERSION: &str = "npa.research-target.v1";
pub const RESEARCH_TARGET_HASH_DOMAIN: &str = "npa.research-target.identity.v1";
pub const RESEARCH_TARGET_FORMALIZATION_CANDIDATE_HASH_DOMAIN: &str =
    "npa.research-target.formalization-candidate.v1";
pub const RESEARCH_TARGET_STATE_TRANSITION_HASH_DOMAIN: &str =
    "npa.research-target.state-transition.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "target_key",
    "informal_statement",
    "source_reference",
    "formalization_candidates",
    "exact_formal_statement_review_status",
    "target_state",
    "known_results",
    "assumptions",
    "owner",
    "campaign_scope",
    "budget",
    "publication_policy",
    "state_transition",
    "claim_gate",
    "advisory",
];
const INFORMAL_STATEMENT_FIELDS: &[&str] = &["statement_hash", "display_text"];
const FORMALIZATION_CANDIDATE_FIELDS: &[&str] = &[
    "candidate_hash",
    "statement_hash",
    "review_status",
    "no_theorem_declaration",
    "proof_corpus_theorem_declaration",
    "verified_artifact_hash",
    "display_text",
];
const KNOWN_RESULT_FIELDS: &[&str] = &[
    "result_hash",
    "statement_hash",
    "relationship",
    "verified_artifact_hash",
    "display_text",
];
const ASSUMPTION_FIELDS: &[&str] = &["assumption_hash", "scope", "disclosure_hash"];
const BUDGET_FIELDS: &[&str] = &["max_tasks", "max_compute_units", "max_wall_clock_hours"];
const STATE_TRANSITION_FIELDS: &[&str] = &[
    "from_state",
    "to_state",
    "actor",
    "claim_gate_record_hash",
    "checked_evidence_hash",
    "counterexample_or_refutation_hash",
    "reviewed_formal_statement_hash",
];
const CLAIM_GATE_FIELDS: &[&str] = &[
    "record_hash",
    "claim_class",
    "reviewed_formal_statement_hash",
    "checked_evidence_hash",
    "independent_checker_hash",
    "assumption_disclosure_hash",
    "human_review_hash",
    "barrier_review_hash",
    "counterexample_or_refutation_hash",
];
const ADVISORY_FIELDS: &[&str] = &[
    "display_title",
    "display_summary",
    "display_order",
    "model_output_hash",
    "notebook_event_index",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTarget {
    pub api_version: String,
    pub target_key: String,
    pub informal_statement: ResearchTargetInformalStatement,
    pub source_reference: String,
    pub formalization_candidates: Vec<ResearchTargetFormalizationCandidate>,
    pub exact_formal_statement_review_status: ResearchTargetFormalStatementReviewStatus,
    pub target_state: ResearchTargetState,
    pub known_results: Vec<ResearchTargetKnownResult>,
    pub assumptions: Vec<ResearchTargetAssumption>,
    pub owner: String,
    pub campaign_scope: String,
    pub budget: ResearchTargetBudget,
    pub publication_policy: ResearchTargetPublicationPolicy,
    pub state_transition: Option<ResearchTargetStateTransition>,
    pub claim_gate: Option<ResearchTargetClaimGate>,
    pub advisory: Option<ResearchTargetAdvisory>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetInformalStatement {
    pub statement_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetFormalizationCandidate {
    pub candidate_hash: Hash,
    pub statement_hash: Hash,
    pub review_status: ResearchTargetFormalStatementReviewStatus,
    pub no_theorem_declaration: bool,
    pub proof_corpus_theorem_declaration: Option<String>,
    pub verified_artifact_hash: Option<Hash>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetKnownResult {
    pub result_hash: Hash,
    pub statement_hash: Hash,
    pub relationship: ResearchTargetKnownResultRelationship,
    pub verified_artifact_hash: Option<Hash>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetAssumption {
    pub assumption_hash: Hash,
    pub scope: String,
    pub disclosure_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetBudget {
    pub max_tasks: u64,
    pub max_compute_units: Option<u64>,
    pub max_wall_clock_hours: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetStateTransition {
    pub from_state: ResearchTargetState,
    pub to_state: ResearchTargetState,
    pub actor: ResearchTargetTransitionActor,
    pub claim_gate_record_hash: Option<Hash>,
    pub checked_evidence_hash: Option<Hash>,
    pub counterexample_or_refutation_hash: Option<Hash>,
    pub reviewed_formal_statement_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetClaimGate {
    pub record_hash: Hash,
    pub claim_class: ResearchTargetClaimClass,
    pub reviewed_formal_statement_hash: Hash,
    pub checked_evidence_hash: Hash,
    pub independent_checker_hash: Hash,
    pub assumption_disclosure_hash: Hash,
    pub human_review_hash: Hash,
    pub barrier_review_hash: Hash,
    pub counterexample_or_refutation_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetAdvisory {
    pub display_title: Option<String>,
    pub display_summary: Option<String>,
    pub display_order: Option<u64>,
    pub model_output_hash: Option<Hash>,
    pub notebook_event_index: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetState {
    Informal,
    FormalizationCandidates,
    Formalized,
    MappedKnownResults,
    ActiveResearch,
    ConditionalProgress,
    SpecialCaseProgress,
    CounterexampleFound,
    Resolved,
    Refuted,
    Archived,
}

impl ResearchTargetState {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Informal => "informal",
            Self::FormalizationCandidates => "formalization_candidates",
            Self::Formalized => "formalized",
            Self::MappedKnownResults => "mapped_known_results",
            Self::ActiveResearch => "active_research",
            Self::ConditionalProgress => "conditional_progress",
            Self::SpecialCaseProgress => "special_case_progress",
            Self::CounterexampleFound => "counterexample_found",
            Self::Resolved => "resolved",
            Self::Refuted => "refuted",
            Self::Archived => "archived",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "informal" => Some(Self::Informal),
            "formalization_candidates" => Some(Self::FormalizationCandidates),
            "formalized" => Some(Self::Formalized),
            "mapped_known_results" => Some(Self::MappedKnownResults),
            "active_research" => Some(Self::ActiveResearch),
            "conditional_progress" => Some(Self::ConditionalProgress),
            "special_case_progress" => Some(Self::SpecialCaseProgress),
            "counterexample_found" => Some(Self::CounterexampleFound),
            "resolved" => Some(Self::Resolved),
            "refuted" => Some(Self::Refuted),
            "archived" => Some(Self::Archived),
            _ => None,
        }
    }

    pub const fn is_claim_terminal(self) -> bool {
        matches!(self, Self::Resolved | Self::Refuted)
    }

    pub const fn is_terminal(self) -> bool {
        matches!(self, Self::Resolved | Self::Refuted | Self::Archived)
    }

    pub const fn requires_reviewed_formal_statement(self) -> bool {
        matches!(
            self,
            Self::Formalized
                | Self::MappedKnownResults
                | Self::ActiveResearch
                | Self::ConditionalProgress
                | Self::SpecialCaseProgress
                | Self::CounterexampleFound
                | Self::Resolved
                | Self::Refuted
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetFormalStatementReviewStatus {
    Unreviewed,
    CandidateReview,
    ReviewedExact,
    Rejected,
}

impl ResearchTargetFormalStatementReviewStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Unreviewed => "unreviewed",
            Self::CandidateReview => "candidate_review",
            Self::ReviewedExact => "reviewed_exact",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "unreviewed" => Some(Self::Unreviewed),
            "candidate_review" => Some(Self::CandidateReview),
            "reviewed_exact" => Some(Self::ReviewedExact),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetKnownResultRelationship {
    KnownRelated,
    SpecialCase,
    Conditional,
    Barrier,
    Blocker,
}

impl ResearchTargetKnownResultRelationship {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::KnownRelated => "known_related",
            Self::SpecialCase => "special_case",
            Self::Conditional => "conditional",
            Self::Barrier => "barrier",
            Self::Blocker => "blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "known_related" => Some(Self::KnownRelated),
            "special_case" => Some(Self::SpecialCase),
            "conditional" => Some(Self::Conditional),
            "barrier" => Some(Self::Barrier),
            "blocker" => Some(Self::Blocker),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetPublicationPolicy {
    Private,
    InternalReview,
    PublicAfterClaimGate,
}

impl ResearchTargetPublicationPolicy {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Private => "private",
            Self::InternalReview => "internal_review",
            Self::PublicAfterClaimGate => "public_after_claim_gate",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "private" => Some(Self::Private),
            "internal_review" => Some(Self::InternalReview),
            "public_after_claim_gate" => Some(Self::PublicAfterClaimGate),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetTransitionActor {
    User,
    Agent,
    ClaimPublicationGate,
}

impl ResearchTargetTransitionActor {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::User => "user",
            Self::Agent => "agent",
            Self::ClaimPublicationGate => "claim_publication_gate",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "user" => Some(Self::User),
            "agent" => Some(Self::Agent),
            "claim_publication_gate" => Some(Self::ClaimPublicationGate),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchTargetClaimClass {
    Resolution,
    Refutation,
    ConditionalProgress,
    SpecialCaseProgress,
}

impl ResearchTargetClaimClass {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Resolution => "resolution",
            Self::Refutation => "refutation",
            Self::ConditionalProgress => "conditional_progress",
            Self::SpecialCaseProgress => "special_case_progress",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "resolution" => Some(Self::Resolution),
            "refutation" => Some(Self::Refutation),
            "conditional_progress" => Some(Self::ConditionalProgress),
            "special_case_progress" => Some(Self::SpecialCaseProgress),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetSchemaError {
    path: String,
    kind: ResearchTargetSchemaErrorKind,
}

impl ResearchTargetSchemaError {
    fn new(path: impl Into<String>, kind: ResearchTargetSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ResearchTargetSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchTargetSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ResearchTargetSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchTargetSchemaErrorKind {
    JsonParse { offset: usize },
    ExpectedObject { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    ExpectedInteger { actual: JsonValueKind },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidApiVersion { value: String },
    InvalidHash { value: String },
    InvalidState { value: String },
    InvalidReviewStatus { value: String },
    InvalidKnownResultRelationship { value: String },
    InvalidPublicationPolicy { value: String },
    InvalidTransitionActor { value: String },
    InvalidClaimClass { value: String },
    InvalidInteger { value: String },
}

impl fmt::Display for ResearchTargetSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "json parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, found {actual:?}"),
            Self::ExpectedInteger { actual } => write!(f, "expected integer, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidState { value } => write!(f, "invalid research target state `{value}`"),
            Self::InvalidReviewStatus { value } => {
                write!(f, "invalid formal statement review status `{value}`")
            }
            Self::InvalidKnownResultRelationship { value } => {
                write!(f, "invalid known result relationship `{value}`")
            }
            Self::InvalidPublicationPolicy { value } => {
                write!(f, "invalid publication policy `{value}`")
            }
            Self::InvalidTransitionActor { value } => {
                write!(f, "invalid transition actor `{value}`")
            }
            Self::InvalidClaimClass { value } => write!(f, "invalid claim class `{value}`"),
            Self::InvalidInteger { value } => write!(f, "invalid integer `{value}`"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchTargetValidationError {
    kind: ResearchTargetValidationErrorKind,
}

impl ResearchTargetValidationError {
    fn new(kind: ResearchTargetValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ResearchTargetValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchTargetValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::error::Error for ResearchTargetValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchTargetValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    DuplicateFormalizationCandidate {
        candidate_hash: String,
    },
    FormalizationCandidateHashMismatch {
        declared: String,
        computed: String,
    },
    TheoremClaimWithoutCertificate {
        candidate_hash: String,
    },
    MissingFormalStatementReview {
        state: ResearchTargetState,
    },
    MissingAssumptionRecord {
        state: ResearchTargetState,
    },
    ClaimGateRequired {
        state: ResearchTargetState,
    },
    ClaimGateClassMismatch {
        expected: ResearchTargetClaimClass,
        actual: ResearchTargetClaimClass,
    },
    ClaimGateFormalStatementMismatch {
        statement_hash: String,
    },
    RefutedRequiresCheckedCounterexampleLink,
    InvalidStateTransition {
        from: ResearchTargetState,
        to: ResearchTargetState,
    },
    TransitionTargetMismatch {
        transition_to: ResearchTargetState,
        record_state: ResearchTargetState,
    },
    DirectTerminalStateEditWithoutClaimGate {
        to: ResearchTargetState,
        actor: ResearchTargetTransitionActor,
    },
    TransitionClaimGateMismatch,
}

impl fmt::Display for ResearchTargetValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::DuplicateFormalizationCandidate { candidate_hash } => {
                write!(f, "duplicate formalization candidate `{candidate_hash}`")
            }
            Self::FormalizationCandidateHashMismatch { declared, computed } => write!(
                f,
                "formalization candidate hash `{declared}` does not match computed hash `{computed}`"
            ),
            Self::TheoremClaimWithoutCertificate { candidate_hash } => write!(
                f,
                "formalization candidate `{candidate_hash}` claims a theorem without a certificate"
            ),
            Self::MissingFormalStatementReview { state } => write!(
                f,
                "state `{}` requires a reviewed exact formal statement",
                state.wire()
            ),
            Self::MissingAssumptionRecord { state } => {
                write!(f, "state `{}` requires assumption records", state.wire())
            }
            Self::ClaimGateRequired { state } => {
                write!(f, "state `{}` requires the claim-publication gate", state.wire())
            }
            Self::ClaimGateClassMismatch { expected, actual } => write!(
                f,
                "claim gate class `{}` does not match expected `{}`",
                actual.wire(),
                expected.wire()
            ),
            Self::ClaimGateFormalStatementMismatch { statement_hash } => write!(
                f,
                "claim gate reviewed formal statement `{statement_hash}` does not match a reviewed formalization candidate"
            ),
            Self::RefutedRequiresCheckedCounterexampleLink => write!(
                f,
                "refuted target requires checked counterexample or refutation evidence linked to the reviewed formal statement"
            ),
            Self::InvalidStateTransition { from, to } => {
                write!(f, "invalid transition `{}` -> `{}`", from.wire(), to.wire())
            }
            Self::TransitionTargetMismatch {
                transition_to,
                record_state,
            } => write!(
                f,
                "transition target `{}` does not match record state `{}`",
                transition_to.wire(),
                record_state.wire()
            ),
            Self::DirectTerminalStateEditWithoutClaimGate { to, actor } => write!(
                f,
                "actor `{}` cannot directly edit target to terminal claim state `{}`",
                actor.wire(),
                to.wire()
            ),
            Self::TransitionClaimGateMismatch => {
                write!(f, "transition claim gate hash does not match record claim gate")
            }
        }
    }
}

pub fn parse_research_target(source: &str) -> Result<ResearchTarget, ResearchTargetSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;

    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != RESEARCH_TARGET_API_VERSION {
        return Err(ResearchTargetSchemaError::new(
            "$.api_version",
            ResearchTargetSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ResearchTarget {
        api_version,
        target_key: required_string(&root, "target_key", "$")?,
        informal_statement: parse_informal_statement(required_value(
            &root,
            "informal_statement",
            "$",
        )?)?,
        source_reference: required_string(&root, "source_reference", "$")?,
        formalization_candidates: parse_formalization_candidates(required_value(
            &root,
            "formalization_candidates",
            "$",
        )?)?,
        exact_formal_statement_review_status: parse_review_status_value(
            required_value(&root, "exact_formal_statement_review_status", "$")?,
            "$.exact_formal_statement_review_status",
        )?,
        target_state: parse_state_value(
            required_value(&root, "target_state", "$")?,
            "$.target_state",
        )?,
        known_results: parse_known_results(required_value(&root, "known_results", "$")?)?,
        assumptions: parse_assumptions(required_value(&root, "assumptions", "$")?)?,
        owner: required_string(&root, "owner", "$")?,
        campaign_scope: required_string(&root, "campaign_scope", "$")?,
        budget: parse_budget(required_value(&root, "budget", "$")?)?,
        publication_policy: parse_publication_policy_value(
            required_value(&root, "publication_policy", "$")?,
            "$.publication_policy",
        )?,
        state_transition: optional_value(&root, "state_transition")
            .map(|value| parse_state_transition(value, "$.state_transition"))
            .transpose()?,
        claim_gate: optional_value(&root, "claim_gate")
            .map(|value| parse_claim_gate(value, "$.claim_gate"))
            .transpose()?,
        advisory: optional_value(&root, "advisory")
            .map(|value| parse_advisory(value, "$.advisory"))
            .transpose()?,
    })
}

pub fn validate_research_target(
    target: &ResearchTarget,
) -> Result<(), ResearchTargetValidationError> {
    require_non_empty(&target.target_key, "target_key")?;
    require_non_empty(&target.source_reference, "source_reference")?;
    require_non_empty(&target.owner, "owner")?;
    require_non_empty(&target.campaign_scope, "campaign_scope")?;

    let mut candidate_hashes = BTreeSet::new();
    let mut reviewed_exact_candidate = false;
    for candidate in &target.formalization_candidates {
        let computed_candidate_hash = research_target_formalization_candidate_hash(candidate);
        if candidate.candidate_hash != computed_candidate_hash {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::FormalizationCandidateHashMismatch {
                    declared: format_hash_string(&candidate.candidate_hash),
                    computed: format_hash_string(&computed_candidate_hash),
                },
            ));
        }
        if !candidate_hashes.insert(candidate.candidate_hash) {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::DuplicateFormalizationCandidate {
                    candidate_hash: format_hash_string(&candidate.candidate_hash),
                },
            ));
        }
        if candidate.review_status == ResearchTargetFormalStatementReviewStatus::ReviewedExact {
            reviewed_exact_candidate = true;
        }
        if (!candidate.no_theorem_declaration
            || candidate.proof_corpus_theorem_declaration.is_some())
            && candidate.verified_artifact_hash.is_none()
        {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::TheoremClaimWithoutCertificate {
                    candidate_hash: format_hash_string(&candidate.candidate_hash),
                },
            ));
        }
    }

    if target.target_state.requires_reviewed_formal_statement()
        && (target.exact_formal_statement_review_status
            != ResearchTargetFormalStatementReviewStatus::ReviewedExact
            || !reviewed_exact_candidate)
    {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::MissingFormalStatementReview {
                state: target.target_state,
            },
        ));
    }

    if let Some(transition) = &target.state_transition {
        validate_research_target_state_transition(transition)?;
        if transition.to_state != target.target_state {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::TransitionTargetMismatch {
                    transition_to: transition.to_state,
                    record_state: target.target_state,
                },
            ));
        }
        if let Some(claim_gate) = &target.claim_gate {
            if (transition.claim_gate_record_hash.is_some()
                && transition.claim_gate_record_hash != Some(claim_gate.record_hash))
                || (transition.checked_evidence_hash.is_some()
                    && transition.checked_evidence_hash != Some(claim_gate.checked_evidence_hash))
                || (transition.reviewed_formal_statement_hash.is_some()
                    && transition.reviewed_formal_statement_hash
                        != Some(claim_gate.reviewed_formal_statement_hash))
                || (transition.counterexample_or_refutation_hash.is_some()
                    && transition.counterexample_or_refutation_hash
                        != claim_gate.counterexample_or_refutation_hash)
            {
                return Err(ResearchTargetValidationError::new(
                    ResearchTargetValidationErrorKind::TransitionClaimGateMismatch,
                ));
            }
        }
    }

    if target.target_state.is_claim_terminal() && target.assumptions.is_empty() {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::MissingAssumptionRecord {
                state: target.target_state,
            },
        ));
    }

    if target.target_state.is_claim_terminal() {
        let claim_gate = target.claim_gate.as_ref().ok_or_else(|| {
            ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::ClaimGateRequired {
                    state: target.target_state,
                },
            )
        })?;
        validate_claim_gate_for_terminal_state(target, claim_gate)?;
    }

    Ok(())
}

pub fn research_target_state_transition_allowed(
    from: ResearchTargetState,
    to: ResearchTargetState,
) -> bool {
    if from == to {
        return true;
    }
    match from {
        ResearchTargetState::Informal => matches!(
            to,
            ResearchTargetState::FormalizationCandidates | ResearchTargetState::Archived
        ),
        ResearchTargetState::FormalizationCandidates => matches!(
            to,
            ResearchTargetState::Informal
                | ResearchTargetState::Formalized
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::Formalized => matches!(
            to,
            ResearchTargetState::MappedKnownResults
                | ResearchTargetState::ActiveResearch
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::MappedKnownResults => matches!(
            to,
            ResearchTargetState::Formalized
                | ResearchTargetState::ActiveResearch
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::ActiveResearch => matches!(
            to,
            ResearchTargetState::ConditionalProgress
                | ResearchTargetState::SpecialCaseProgress
                | ResearchTargetState::CounterexampleFound
                | ResearchTargetState::Resolved
                | ResearchTargetState::Refuted
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::ConditionalProgress => matches!(
            to,
            ResearchTargetState::ActiveResearch
                | ResearchTargetState::SpecialCaseProgress
                | ResearchTargetState::Resolved
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::SpecialCaseProgress => matches!(
            to,
            ResearchTargetState::ActiveResearch
                | ResearchTargetState::ConditionalProgress
                | ResearchTargetState::Resolved
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::CounterexampleFound => matches!(
            to,
            ResearchTargetState::ActiveResearch
                | ResearchTargetState::Refuted
                | ResearchTargetState::Archived
        ),
        ResearchTargetState::Resolved
        | ResearchTargetState::Refuted
        | ResearchTargetState::Archived => false,
    }
}

pub fn validate_research_target_state_transition(
    transition: &ResearchTargetStateTransition,
) -> Result<(), ResearchTargetValidationError> {
    if !research_target_state_transition_allowed(transition.from_state, transition.to_state) {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::InvalidStateTransition {
                from: transition.from_state,
                to: transition.to_state,
            },
        ));
    }
    if transition.to_state.is_claim_terminal() {
        if transition.actor != ResearchTargetTransitionActor::ClaimPublicationGate
            || transition.claim_gate_record_hash.is_none()
            || transition.checked_evidence_hash.is_none()
            || transition.reviewed_formal_statement_hash.is_none()
        {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::DirectTerminalStateEditWithoutClaimGate {
                    to: transition.to_state,
                    actor: transition.actor,
                },
            ));
        }
        if transition.to_state == ResearchTargetState::Refuted
            && transition.counterexample_or_refutation_hash.is_none()
        {
            return Err(ResearchTargetValidationError::new(
                ResearchTargetValidationErrorKind::RefutedRequiresCheckedCounterexampleLink,
            ));
        }
    }
    Ok(())
}

pub fn research_target_canonical_identity_bytes(target: &ResearchTarget) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, RESEARCH_TARGET_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &target.api_version);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &target.target_key);
    encode_string_to(&mut out, "informal_statement_hash");
    encode_hash_to(&mut out, &target.informal_statement.statement_hash);
    encode_string_to(&mut out, "source_reference");
    encode_string_to(&mut out, &target.source_reference);
    encode_string_to(&mut out, "formalization_candidates");
    let mut candidates = target.formalization_candidates.clone();
    candidates.sort_by_key(|candidate| candidate.candidate_hash);
    encode_len_to(&mut out, candidates.len());
    for candidate in &candidates {
        encode_formalization_candidate_to(&mut out, candidate);
    }
    encode_string_to(&mut out, "exact_formal_statement_review_status");
    encode_string_to(&mut out, target.exact_formal_statement_review_status.wire());
    encode_string_to(&mut out, "known_results");
    let mut known_results = target.known_results.clone();
    known_results.sort_by_key(|result| result.result_hash);
    encode_len_to(&mut out, known_results.len());
    for result in &known_results {
        encode_known_result_to(&mut out, result);
    }
    encode_string_to(&mut out, "assumptions");
    let mut assumptions = target.assumptions.clone();
    assumptions.sort_by_key(|assumption| assumption.assumption_hash);
    encode_len_to(&mut out, assumptions.len());
    for assumption in &assumptions {
        encode_assumption_to(&mut out, assumption);
    }
    out
}

pub fn research_target_hash(target: &ResearchTarget) -> Hash {
    let digest = Sha256::digest(research_target_canonical_identity_bytes(target));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn research_target_hash_string(target: &ResearchTarget) -> String {
    format_hash_string(&research_target_hash(target))
}

pub fn research_target_formalization_candidate_canonical_identity_bytes(
    candidate: &ResearchTargetFormalizationCandidate,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(
        &mut out,
        RESEARCH_TARGET_FORMALIZATION_CANDIDATE_HASH_DOMAIN,
    );
    encode_formalization_candidate_content_to(&mut out, candidate);
    out
}

pub fn research_target_formalization_candidate_hash(
    candidate: &ResearchTargetFormalizationCandidate,
) -> Hash {
    let digest =
        Sha256::digest(research_target_formalization_candidate_canonical_identity_bytes(candidate));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn research_target_state_transition_canonical_identity_bytes(
    transition: &ResearchTargetStateTransition,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, RESEARCH_TARGET_STATE_TRANSITION_HASH_DOMAIN);
    encode_state_transition_to(&mut out, transition);
    out
}

pub fn research_target_state_transition_hash(transition: &ResearchTargetStateTransition) -> Hash {
    let digest = Sha256::digest(research_target_state_transition_canonical_identity_bytes(
        transition,
    ));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

fn validate_claim_gate_for_terminal_state(
    target: &ResearchTarget,
    claim_gate: &ResearchTargetClaimGate,
) -> Result<(), ResearchTargetValidationError> {
    let expected = match target.target_state {
        ResearchTargetState::Resolved => ResearchTargetClaimClass::Resolution,
        ResearchTargetState::Refuted => ResearchTargetClaimClass::Refutation,
        _ => return Ok(()),
    };
    if claim_gate.claim_class != expected {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::ClaimGateClassMismatch {
                expected,
                actual: claim_gate.claim_class,
            },
        ));
    }
    if !target.formalization_candidates.iter().any(|candidate| {
        candidate.review_status == ResearchTargetFormalStatementReviewStatus::ReviewedExact
            && candidate.statement_hash == claim_gate.reviewed_formal_statement_hash
    }) {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::ClaimGateFormalStatementMismatch {
                statement_hash: format_hash_string(&claim_gate.reviewed_formal_statement_hash),
            },
        ));
    }
    if target.target_state == ResearchTargetState::Refuted
        && claim_gate.counterexample_or_refutation_hash.is_none()
    {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::RefutedRequiresCheckedCounterexampleLink,
        ));
    }
    Ok(())
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ResearchTargetValidationError> {
    if value.trim().is_empty() {
        return Err(ResearchTargetValidationError::new(
            ResearchTargetValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn parse_informal_statement(
    value: &JsonValue<'_>,
) -> Result<ResearchTargetInformalStatement, ResearchTargetSchemaError> {
    let members = object_map(value, "$.informal_statement", INFORMAL_STATEMENT_FIELDS)?;
    Ok(ResearchTargetInformalStatement {
        statement_hash: required_hash(&members, "statement_hash", "$.informal_statement")?,
        display_text: optional_string(&members, "display_text", "$.informal_statement")?,
    })
}

fn parse_formalization_candidates(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchTargetFormalizationCandidate>, ResearchTargetSchemaError> {
    let elements = array_elements(value, "$.formalization_candidates")?;
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_formalization_candidate(value, &format!("$.formalization_candidates[{index}]"))
        })
        .collect()
}

fn parse_formalization_candidate(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetFormalizationCandidate, ResearchTargetSchemaError> {
    let members = object_map(value, path, FORMALIZATION_CANDIDATE_FIELDS)?;
    Ok(ResearchTargetFormalizationCandidate {
        candidate_hash: required_hash(&members, "candidate_hash", path)?,
        statement_hash: required_hash(&members, "statement_hash", path)?,
        review_status: parse_review_status_value(
            required_value(&members, "review_status", path)?,
            &format!("{path}.review_status"),
        )?,
        no_theorem_declaration: required_bool(&members, "no_theorem_declaration", path)?,
        proof_corpus_theorem_declaration: optional_string(
            &members,
            "proof_corpus_theorem_declaration",
            path,
        )?,
        verified_artifact_hash: optional_hash(&members, "verified_artifact_hash", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_known_results(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchTargetKnownResult>, ResearchTargetSchemaError> {
    let elements = array_elements(value, "$.known_results")?;
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_known_result(value, &format!("$.known_results[{index}]")))
        .collect()
}

fn parse_known_result(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetKnownResult, ResearchTargetSchemaError> {
    let members = object_map(value, path, KNOWN_RESULT_FIELDS)?;
    Ok(ResearchTargetKnownResult {
        result_hash: required_hash(&members, "result_hash", path)?,
        statement_hash: required_hash(&members, "statement_hash", path)?,
        relationship: parse_known_result_relationship_value(
            required_value(&members, "relationship", path)?,
            &format!("{path}.relationship"),
        )?,
        verified_artifact_hash: optional_hash(&members, "verified_artifact_hash", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_assumptions(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchTargetAssumption>, ResearchTargetSchemaError> {
    let elements = array_elements(value, "$.assumptions")?;
    elements
        .iter()
        .enumerate()
        .map(|(index, value)| parse_assumption(value, &format!("$.assumptions[{index}]")))
        .collect()
}

fn parse_assumption(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetAssumption, ResearchTargetSchemaError> {
    let members = object_map(value, path, ASSUMPTION_FIELDS)?;
    Ok(ResearchTargetAssumption {
        assumption_hash: required_hash(&members, "assumption_hash", path)?,
        scope: required_string(&members, "scope", path)?,
        disclosure_hash: required_hash(&members, "disclosure_hash", path)?,
    })
}

fn parse_budget(value: &JsonValue<'_>) -> Result<ResearchTargetBudget, ResearchTargetSchemaError> {
    let members = object_map(value, "$.budget", BUDGET_FIELDS)?;
    Ok(ResearchTargetBudget {
        max_tasks: required_u64(&members, "max_tasks", "$.budget")?,
        max_compute_units: optional_u64(&members, "max_compute_units", "$.budget")?,
        max_wall_clock_hours: optional_u64(&members, "max_wall_clock_hours", "$.budget")?,
    })
}

fn parse_state_transition(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetStateTransition, ResearchTargetSchemaError> {
    let members = object_map(value, path, STATE_TRANSITION_FIELDS)?;
    Ok(ResearchTargetStateTransition {
        from_state: parse_state_value(
            required_value(&members, "from_state", path)?,
            &format!("{path}.from_state"),
        )?,
        to_state: parse_state_value(
            required_value(&members, "to_state", path)?,
            &format!("{path}.to_state"),
        )?,
        actor: parse_transition_actor_value(
            required_value(&members, "actor", path)?,
            &format!("{path}.actor"),
        )?,
        claim_gate_record_hash: optional_hash(&members, "claim_gate_record_hash", path)?,
        checked_evidence_hash: optional_hash(&members, "checked_evidence_hash", path)?,
        counterexample_or_refutation_hash: optional_hash(
            &members,
            "counterexample_or_refutation_hash",
            path,
        )?,
        reviewed_formal_statement_hash: optional_hash(
            &members,
            "reviewed_formal_statement_hash",
            path,
        )?,
    })
}

fn parse_claim_gate(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetClaimGate, ResearchTargetSchemaError> {
    let members = object_map(value, path, CLAIM_GATE_FIELDS)?;
    Ok(ResearchTargetClaimGate {
        record_hash: required_hash(&members, "record_hash", path)?,
        claim_class: parse_claim_class_value(
            required_value(&members, "claim_class", path)?,
            &format!("{path}.claim_class"),
        )?,
        reviewed_formal_statement_hash: required_hash(
            &members,
            "reviewed_formal_statement_hash",
            path,
        )?,
        checked_evidence_hash: required_hash(&members, "checked_evidence_hash", path)?,
        independent_checker_hash: required_hash(&members, "independent_checker_hash", path)?,
        assumption_disclosure_hash: required_hash(&members, "assumption_disclosure_hash", path)?,
        human_review_hash: required_hash(&members, "human_review_hash", path)?,
        barrier_review_hash: required_hash(&members, "barrier_review_hash", path)?,
        counterexample_or_refutation_hash: optional_hash(
            &members,
            "counterexample_or_refutation_hash",
            path,
        )?,
    })
}

fn parse_advisory(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetAdvisory, ResearchTargetSchemaError> {
    let members = object_map(value, path, ADVISORY_FIELDS)?;
    Ok(ResearchTargetAdvisory {
        display_title: optional_string(&members, "display_title", path)?,
        display_summary: optional_string(&members, "display_summary", path)?,
        display_order: optional_u64(&members, "display_order", path)?,
        model_output_hash: optional_hash(&members, "model_output_hash", path)?,
        notebook_event_index: optional_u64(&members, "notebook_event_index", path)?,
    })
}

fn parse_state_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetState, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetState::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidState { value: wire },
        )
    })
}

fn parse_review_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetFormalStatementReviewStatus, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetFormalStatementReviewStatus::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidReviewStatus { value: wire },
        )
    })
}

fn parse_known_result_relationship_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetKnownResultRelationship, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetKnownResultRelationship::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidKnownResultRelationship { value: wire },
        )
    })
}

fn parse_publication_policy_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetPublicationPolicy, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetPublicationPolicy::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidPublicationPolicy { value: wire },
        )
    })
}

fn parse_transition_actor_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetTransitionActor, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetTransitionActor::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidTransitionActor { value: wire },
        )
    })
}

fn parse_claim_class_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetClaimClass, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetClaimClass::parse(&wire).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidClaimClass { value: wire },
        )
    })
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ResearchTargetSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ResearchTargetSchemaError::new(
            "$",
            ResearchTargetSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ResearchTargetSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ResearchTargetSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchTargetSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ResearchTargetSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchTargetSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ResearchTargetSchemaError> {
    value.array_elements().ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ResearchTargetSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ResearchTargetSchemaError::new(
            format!("{path}.{field}"),
            ResearchTargetSchemaErrorKind::MissingField { field },
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
) -> Result<String, ResearchTargetSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ResearchTargetSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ResearchTargetSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ResearchTargetSchemaError> {
    let value = required_value(members, field, path)?;
    value.bool_value().ok_or_else(|| {
        ResearchTargetSchemaError::new(
            format!("{path}.{field}"),
            ResearchTargetSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ResearchTargetSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ResearchTargetSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ResearchTargetSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn required_u64(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<u64, ResearchTargetSchemaError> {
    parse_u64(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_u64(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<u64>, ResearchTargetSchemaError> {
    optional_value(members, field)
        .map(|value| parse_u64(value, &format!("{path}.{field}")))
        .transpose()
}

fn parse_u64(value: &JsonValue<'_>, path: &str) -> Result<u64, ResearchTargetSchemaError> {
    let raw = value.number_raw().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::ExpectedInteger {
                actual: value.kind(),
            },
        )
    })?;
    if raw.is_empty() || raw.bytes().any(|byte| !byte.is_ascii_digit()) {
        return Err(ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidInteger { value: raw },
        ));
    }
    raw.parse().map_err(|_| {
        ResearchTargetSchemaError::new(
            path,
            ResearchTargetSchemaErrorKind::InvalidInteger { value: raw },
        )
    })
}

fn encode_formalization_candidate_to(
    out: &mut Vec<u8>,
    candidate: &ResearchTargetFormalizationCandidate,
) {
    encode_string_to(out, "candidate_hash");
    encode_hash_to(out, &candidate.candidate_hash);
    encode_formalization_candidate_content_to(out, candidate);
}

fn encode_formalization_candidate_content_to(
    out: &mut Vec<u8>,
    candidate: &ResearchTargetFormalizationCandidate,
) {
    encode_string_to(out, "statement_hash");
    encode_hash_to(out, &candidate.statement_hash);
    encode_string_to(out, "review_status");
    encode_string_to(out, candidate.review_status.wire());
    encode_string_to(out, "no_theorem_declaration");
    encode_bool_to(out, candidate.no_theorem_declaration);
    encode_option_string_to(
        out,
        "proof_corpus_theorem_declaration",
        candidate.proof_corpus_theorem_declaration.as_deref(),
    );
    encode_option_hash_to(
        out,
        "verified_artifact_hash",
        candidate.verified_artifact_hash.as_ref(),
    );
}

fn encode_known_result_to(out: &mut Vec<u8>, result: &ResearchTargetKnownResult) {
    encode_string_to(out, "result_hash");
    encode_hash_to(out, &result.result_hash);
    encode_string_to(out, "statement_hash");
    encode_hash_to(out, &result.statement_hash);
    encode_string_to(out, "relationship");
    encode_string_to(out, result.relationship.wire());
    encode_option_hash_to(
        out,
        "verified_artifact_hash",
        result.verified_artifact_hash.as_ref(),
    );
}

fn encode_assumption_to(out: &mut Vec<u8>, assumption: &ResearchTargetAssumption) {
    encode_string_to(out, "assumption_hash");
    encode_hash_to(out, &assumption.assumption_hash);
    encode_string_to(out, "scope");
    encode_string_to(out, &assumption.scope);
    encode_string_to(out, "disclosure_hash");
    encode_hash_to(out, &assumption.disclosure_hash);
}

fn encode_state_transition_to(out: &mut Vec<u8>, transition: &ResearchTargetStateTransition) {
    encode_string_to(out, "from_state");
    encode_string_to(out, transition.from_state.wire());
    encode_string_to(out, "to_state");
    encode_string_to(out, transition.to_state.wire());
    encode_string_to(out, "actor");
    encode_string_to(out, transition.actor.wire());
    encode_option_hash_to(
        out,
        "claim_gate_record_hash",
        transition.claim_gate_record_hash.as_ref(),
    );
    encode_option_hash_to(
        out,
        "checked_evidence_hash",
        transition.checked_evidence_hash.as_ref(),
    );
    encode_option_hash_to(
        out,
        "counterexample_or_refutation_hash",
        transition.counterexample_or_refutation_hash.as_ref(),
    );
    encode_option_hash_to(
        out,
        "reviewed_formal_statement_hash",
        transition.reviewed_formal_statement_hash.as_ref(),
    );
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

fn encode_bool_to(out: &mut Vec<u8>, value: bool) {
    out.push(b'b');
    out.push(u8::from(value));
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
            .join("testdata/proof-using-agents/fixtures/pua-m16-research-target")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("research target fixture should exist")
    }

    fn parse_fixture(name: &str) -> ResearchTarget {
        parse_research_target(&fixture(name)).expect("fixture should parse")
    }

    fn validate_fixture(name: &str) -> Result<(), ResearchTargetValidationErrorKind> {
        validate_research_target(&parse_fixture(name)).map_err(|error| error.kind().clone())
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    #[test]
    fn research_target_state_machine() {
        assert!(research_target_state_transition_allowed(
            ResearchTargetState::Informal,
            ResearchTargetState::FormalizationCandidates
        ));
        assert!(research_target_state_transition_allowed(
            ResearchTargetState::FormalizationCandidates,
            ResearchTargetState::Formalized
        ));
        assert!(research_target_state_transition_allowed(
            ResearchTargetState::CounterexampleFound,
            ResearchTargetState::Refuted
        ));
        assert!(!ResearchTargetState::CounterexampleFound.is_terminal());
        assert!(!research_target_state_transition_allowed(
            ResearchTargetState::Informal,
            ResearchTargetState::ActiveResearch
        ));
        assert!(matches!(
            validate_fixture("invalid-state-transition.json"),
            Err(ResearchTargetValidationErrorKind::InvalidStateTransition { .. })
        ));
        assert!(matches!(
            validate_fixture("direct-terminal-edit-without-claim-gate.json"),
            Err(ResearchTargetValidationErrorKind::DirectTerminalStateEditWithoutClaimGate { .. })
        ));
        assert!(matches!(
            validate_fixture("missing-formal-statement-review.json"),
            Err(ResearchTargetValidationErrorKind::MissingFormalStatementReview { .. })
        ));
        assert!(matches!(
            validate_fixture("missing-assumption-record.json"),
            Err(ResearchTargetValidationErrorKind::MissingAssumptionRecord { .. })
        ));

        let p_equals_np = parse_fixture("p-equals-np-research-target.json");
        validate_research_target(&p_equals_np).expect("P = NP research target should validate");
        assert_eq!(p_equals_np.target_key, "PEqualsNP");
        assert!(p_equals_np
            .formalization_candidates
            .iter()
            .all(|candidate| candidate.no_theorem_declaration));

        let p_not_equals_np = parse_fixture("p-not-equals-np-research-target.json");
        validate_research_target(&p_not_equals_np)
            .expect("P != NP research target should validate");
        assert_eq!(p_not_equals_np.target_key, "PNotEqualsNP");

        let mut advisory_only = p_equals_np.clone();
        advisory_only.informal_statement.display_text = Some("Different display text".to_owned());
        advisory_only.formalization_candidates[0].display_text =
            Some("Reordered display-only formalization text".to_owned());
        advisory_only.advisory = Some(ResearchTargetAdvisory {
            display_title: Some("Changed title".to_owned()),
            display_summary: Some("Changed model-facing summary".to_owned()),
            display_order: Some(99),
            model_output_hash: Some(hash(0x99)),
            notebook_event_index: Some(42),
        });
        assert_eq!(
            research_target_hash(&p_equals_np),
            research_target_hash(&advisory_only)
        );

        let mut identity_changed = p_equals_np.clone();
        identity_changed.informal_statement.statement_hash = hash(0x9a);
        assert_ne!(
            research_target_hash(&p_equals_np),
            research_target_hash(&identity_changed)
        );
    }

    #[test]
    fn research_target_rejects_theorem_claim_without_certificate() {
        assert!(matches!(
            validate_fixture("unresolved-target-as-theorem.json"),
            Err(ResearchTargetValidationErrorKind::TheoremClaimWithoutCertificate { .. })
        ));

        let target = parse_fixture("p-equals-np-research-target.json");
        let candidate = &target.formalization_candidates[0];
        let mut display_changed = candidate.clone();
        display_changed.display_text = Some("display-only candidate text".to_owned());
        assert_eq!(
            research_target_formalization_candidate_hash(candidate),
            research_target_formalization_candidate_hash(&display_changed)
        );

        let mut declared_address_changed = candidate.clone();
        declared_address_changed.candidate_hash = hash(0x78);
        assert_eq!(
            research_target_formalization_candidate_hash(candidate),
            research_target_formalization_candidate_hash(&declared_address_changed)
        );
        assert!(matches!(
            validate_research_target(&ResearchTarget {
                formalization_candidates: vec![declared_address_changed],
                ..target.clone()
            }),
            Err(error)
                if matches!(
                    error.kind(),
                    ResearchTargetValidationErrorKind::FormalizationCandidateHashMismatch { .. }
                )
        ));

        let mut statement_changed = candidate.clone();
        statement_changed.statement_hash = hash(0x77);
        assert_ne!(
            research_target_formalization_candidate_hash(candidate),
            research_target_formalization_candidate_hash(&statement_changed)
        );
    }

    #[test]
    fn research_target_refuted_requires_claim_gate() {
        assert!(matches!(
            validate_fixture("refuted-without-claim-gate.json"),
            Err(ResearchTargetValidationErrorKind::ClaimGateRequired {
                state: ResearchTargetState::Refuted
            })
        ));
        assert!(matches!(
            validate_fixture("refuted-without-checked-counterexample-link.json"),
            Err(ResearchTargetValidationErrorKind::RefutedRequiresCheckedCounterexampleLink)
        ));
    }
}

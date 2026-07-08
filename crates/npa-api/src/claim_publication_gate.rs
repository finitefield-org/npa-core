use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::research_target::{ResearchTargetClaimClass, ResearchTargetState};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const CLAIM_PUBLICATION_GATE_API_VERSION: &str = "npa.claim-publication-gate.v1";
pub const CLAIM_PUBLICATION_GATE_HASH_DOMAIN: &str = "npa.claim-publication-gate.identity.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "record_key",
    "target_key",
    "formal_statement_hash",
    "reviewed_formal_statement_hash",
    "claim_class",
    "proposed_target_state",
    "gate_decision",
    "review_procedure_hash",
    "assumption_list_hash",
    "assumption_disclosure_hash",
    "assumptions",
    "axiom_report_hash",
    "certificate_references",
    "source_free_reproduction_command_hashes",
    "independent_checker_hash",
    "clean_reproduction_hash",
    "human_review_hash",
    "barrier_review_hash",
    "barrier_relationship",
    "supporting_evidence_kind",
    "formal_proof_evidence_hash",
    "counterexample_or_refutation_hash",
    "special_case_scope_hash",
    "unresolved_blocker_hashes",
    "informal_explanation_hash",
    "informal_explanation_is_formal_proof",
    "target_state_transition_authorized",
    "pua_m17_bundle_handoff_eligible",
    "pua_m17_bundle_handoff_hash",
    "rejection_reasons",
    "wall_clock_time",
    "display_text",
];
const ASSUMPTION_FIELDS: &[&str] = &["assumption_key", "assumption_hash", "disclosure_hash"];
const CERTIFICATE_REFERENCE_FIELDS: &[&str] = &[
    "certificate_key",
    "certificate_hash",
    "current_certificate_hash",
    "source_free_reproduction_hash",
    "checker_profile_hash",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimPublicationGateRecord {
    pub api_version: String,
    pub record_key: String,
    pub target_key: String,
    pub formal_statement_hash: Hash,
    pub reviewed_formal_statement_hash: Hash,
    pub claim_class: ResearchTargetClaimClass,
    pub proposed_target_state: ResearchTargetState,
    pub gate_decision: ClaimPublicationGateDecision,
    pub review_procedure_hash: Hash,
    pub assumption_list_hash: Option<Hash>,
    pub assumption_disclosure_hash: Option<Hash>,
    pub assumptions: Vec<ClaimPublicationGateAssumption>,
    pub axiom_report_hash: Option<Hash>,
    pub certificate_references: Vec<ClaimPublicationGateCertificateReference>,
    pub source_free_reproduction_command_hashes: Vec<Hash>,
    pub independent_checker_hash: Option<Hash>,
    pub clean_reproduction_hash: Option<Hash>,
    pub human_review_hash: Option<Hash>,
    pub barrier_review_hash: Option<Hash>,
    pub barrier_relationship: ClaimPublicationBarrierRelationship,
    pub supporting_evidence_kind: ClaimPublicationSupportingEvidenceKind,
    pub formal_proof_evidence_hash: Option<Hash>,
    pub counterexample_or_refutation_hash: Option<Hash>,
    pub special_case_scope_hash: Option<Hash>,
    pub unresolved_blocker_hashes: Vec<Hash>,
    pub informal_explanation_hash: Option<Hash>,
    pub informal_explanation_is_formal_proof: bool,
    pub target_state_transition_authorized: bool,
    pub pua_m17_bundle_handoff_eligible: bool,
    pub pua_m17_bundle_handoff_hash: Option<Hash>,
    pub rejection_reasons: Vec<ClaimPublicationGateRejectionReason>,
    pub wall_clock_time: Option<String>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimPublicationGateAssumption {
    pub assumption_key: String,
    pub assumption_hash: Hash,
    pub disclosure_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimPublicationGateCertificateReference {
    pub certificate_key: String,
    pub certificate_hash: Hash,
    pub current_certificate_hash: Hash,
    pub source_free_reproduction_hash: Hash,
    pub checker_profile_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClaimPublicationGateDecision {
    Approved,
    Rejected,
}

impl ClaimPublicationGateDecision {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Approved => "approved",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "approved" => Some(Self::Approved),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClaimPublicationBarrierRelationship {
    ReviewedNoBarrier,
    ReviewedBarrierNotApplicable,
    ReviewedBarrierRelated,
    ReviewedBarrierBlocker,
}

impl ClaimPublicationBarrierRelationship {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ReviewedNoBarrier => "reviewed_no_barrier",
            Self::ReviewedBarrierNotApplicable => "reviewed_barrier_not_applicable",
            Self::ReviewedBarrierRelated => "reviewed_barrier_related",
            Self::ReviewedBarrierBlocker => "reviewed_barrier_blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "reviewed_no_barrier" => Some(Self::ReviewedNoBarrier),
            "reviewed_barrier_not_applicable" => Some(Self::ReviewedBarrierNotApplicable),
            "reviewed_barrier_related" => Some(Self::ReviewedBarrierRelated),
            "reviewed_barrier_blocker" => Some(Self::ReviewedBarrierBlocker),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClaimPublicationSupportingEvidenceKind {
    VerifiedCertificate,
    CheckedRefutation,
    ConditionalTheorem,
    SpecialCaseTheorem,
    ExperimentOnly,
    NotebookOnly,
    BarrierOnly,
}

impl ClaimPublicationSupportingEvidenceKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::VerifiedCertificate => "verified_certificate",
            Self::CheckedRefutation => "checked_refutation",
            Self::ConditionalTheorem => "conditional_theorem",
            Self::SpecialCaseTheorem => "special_case_theorem",
            Self::ExperimentOnly => "experiment_only",
            Self::NotebookOnly => "notebook_only",
            Self::BarrierOnly => "barrier_only",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "verified_certificate" => Some(Self::VerifiedCertificate),
            "checked_refutation" => Some(Self::CheckedRefutation),
            "conditional_theorem" => Some(Self::ConditionalTheorem),
            "special_case_theorem" => Some(Self::SpecialCaseTheorem),
            "experiment_only" => Some(Self::ExperimentOnly),
            "notebook_only" => Some(Self::NotebookOnly),
            "barrier_only" => Some(Self::BarrierOnly),
            _ => None,
        }
    }

    pub const fn is_non_proof_sidecar(self) -> bool {
        matches!(
            self,
            Self::ExperimentOnly | Self::NotebookOnly | Self::BarrierOnly
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClaimPublicationGateRejectionReason {
    MissingAssumption,
    MissingIndependentChecker,
    ExperimentOnlyClaim,
    StaleCertificate,
    UnresolvedBlocker,
    MissingBarrierReview,
    MissingAxiomReport,
    MissingCertificate,
    MissingSourceFreeReproduction,
    MissingCleanReproduction,
    MissingHumanReview,
    InformalExplanationUsedAsProof,
    ClaimClassStateMismatch,
    MissingPuaM17Handoff,
}

impl ClaimPublicationGateRejectionReason {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::MissingAssumption => "missing_assumption",
            Self::MissingIndependentChecker => "missing_independent_checker",
            Self::ExperimentOnlyClaim => "experiment_only_claim",
            Self::StaleCertificate => "stale_certificate",
            Self::UnresolvedBlocker => "unresolved_blocker",
            Self::MissingBarrierReview => "missing_barrier_review",
            Self::MissingAxiomReport => "missing_axiom_report",
            Self::MissingCertificate => "missing_certificate",
            Self::MissingSourceFreeReproduction => "missing_source_free_reproduction",
            Self::MissingCleanReproduction => "missing_clean_reproduction",
            Self::MissingHumanReview => "missing_human_review",
            Self::InformalExplanationUsedAsProof => "informal_explanation_used_as_proof",
            Self::ClaimClassStateMismatch => "claim_class_state_mismatch",
            Self::MissingPuaM17Handoff => "missing_pua_m17_handoff",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "missing_assumption" => Some(Self::MissingAssumption),
            "missing_independent_checker" => Some(Self::MissingIndependentChecker),
            "experiment_only_claim" => Some(Self::ExperimentOnlyClaim),
            "stale_certificate" => Some(Self::StaleCertificate),
            "unresolved_blocker" => Some(Self::UnresolvedBlocker),
            "missing_barrier_review" => Some(Self::MissingBarrierReview),
            "missing_axiom_report" => Some(Self::MissingAxiomReport),
            "missing_certificate" => Some(Self::MissingCertificate),
            "missing_source_free_reproduction" => Some(Self::MissingSourceFreeReproduction),
            "missing_clean_reproduction" => Some(Self::MissingCleanReproduction),
            "missing_human_review" => Some(Self::MissingHumanReview),
            "informal_explanation_used_as_proof" => Some(Self::InformalExplanationUsedAsProof),
            "claim_class_state_mismatch" => Some(Self::ClaimClassStateMismatch),
            "missing_pua_m17_handoff" => Some(Self::MissingPuaM17Handoff),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimPublicationGateSchemaError {
    path: String,
    kind: ClaimPublicationGateSchemaErrorKind,
}

impl ClaimPublicationGateSchemaError {
    fn new(path: impl Into<String>, kind: ClaimPublicationGateSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &ClaimPublicationGateSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ClaimPublicationGateSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "claim-publication gate schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for ClaimPublicationGateSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimPublicationGateSchemaErrorKind {
    JsonParse { offset: usize },
    ExpectedObject { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidApiVersion { value: String },
    InvalidHash { value: String },
    InvalidClaimClass { value: String },
    InvalidTargetState { value: String },
    InvalidGateDecision { value: String },
    InvalidBarrierRelationship { value: String },
    InvalidSupportingEvidenceKind { value: String },
    InvalidRejectionReason { value: String },
}

impl fmt::Display for ClaimPublicationGateSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "invalid JSON at byte offset {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidClaimClass { value } => write!(f, "invalid claim class `{value}`"),
            Self::InvalidTargetState { value } => {
                write!(f, "invalid target state `{value}`")
            }
            Self::InvalidGateDecision { value } => write!(f, "invalid gate decision `{value}`"),
            Self::InvalidBarrierRelationship { value } => {
                write!(f, "invalid barrier relationship `{value}`")
            }
            Self::InvalidSupportingEvidenceKind { value } => {
                write!(f, "invalid supporting evidence kind `{value}`")
            }
            Self::InvalidRejectionReason { value } => {
                write!(f, "invalid rejection reason `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimPublicationGateValidationError {
    kind: ClaimPublicationGateValidationErrorKind,
}

impl ClaimPublicationGateValidationError {
    fn new(kind: ClaimPublicationGateValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &ClaimPublicationGateValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ClaimPublicationGateValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "claim-publication gate validation error: {}", self.kind)
    }
}

impl std::error::Error for ClaimPublicationGateValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimPublicationGateValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    ExactFormalStatementMismatch {
        formal_statement_hash: String,
        reviewed_formal_statement_hash: String,
    },
    ClaimClassTargetStateMismatch {
        claim_class: ResearchTargetClaimClass,
        proposed_target_state: ResearchTargetState,
    },
    DuplicateAssumption {
        assumption_key: String,
    },
    DuplicateCertificate {
        certificate_key: String,
    },
    DuplicateSourceFreeReproductionCommand {
        command_hash: String,
    },
    DuplicateUnresolvedBlocker {
        blocker_hash: String,
    },
    DuplicateRejectionReason {
        reason: ClaimPublicationGateRejectionReason,
    },
    StaleCertificate {
        certificate_key: String,
        certificate_hash: String,
        current_certificate_hash: String,
    },
    MissingAssumptionListHash,
    ConditionalClaimRequiresAssumptionList,
    SpecialCaseClaimRequiresScope,
    MissingAssumptionDisclosure,
    MissingAxiomReport,
    MissingCertificateHash,
    MissingSourceFreeReproduction,
    MissingIndependentChecker,
    MissingCleanReproduction,
    MissingHumanReview,
    MissingBarrierReview,
    MissingFormalProofEvidence,
    RefutationRequiresCounterexampleOrRefutation,
    ExperimentOnlyClaimCannotPassGate,
    NotebookOnlyClaimCannotPassGate,
    BarrierOnlyClaimCannotPassGate,
    SupportingEvidenceClaimClassMismatch {
        claim_class: ResearchTargetClaimClass,
        supporting_evidence_kind: ClaimPublicationSupportingEvidenceKind,
    },
    UnresolvedBlocker {
        blocker_hash: String,
    },
    InformalExplanationCannotBeFormalProof,
    ApprovedGateRequiresTargetTransitionAuthorization,
    ProgressClaimCannotAuthorizeTerminalTransition,
    RejectedGateCannotAuthorizeTargetTransition,
    ApprovedGateRequiresPuaM17Handoff,
    HandoffEligibilityRequiresHash,
    ApprovedGateCannotCarryRejectionReasons,
    RejectionRequiresReason,
}

impl fmt::Display for ClaimPublicationGateValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::ExactFormalStatementMismatch {
                formal_statement_hash,
                reviewed_formal_statement_hash,
            } => write!(
                f,
                "formal statement `{formal_statement_hash}` does not match reviewed statement `{reviewed_formal_statement_hash}`"
            ),
            Self::ClaimClassTargetStateMismatch {
                claim_class,
                proposed_target_state,
            } => write!(
                f,
                "claim class `{}` cannot propose target state `{}`",
                claim_class.wire(),
                proposed_target_state.wire()
            ),
            Self::DuplicateAssumption { assumption_key } => {
                write!(f, "duplicate assumption `{assumption_key}`")
            }
            Self::DuplicateCertificate { certificate_key } => {
                write!(f, "duplicate certificate `{certificate_key}`")
            }
            Self::DuplicateSourceFreeReproductionCommand { command_hash } => {
                write!(f, "duplicate source-free reproduction command `{command_hash}`")
            }
            Self::DuplicateUnresolvedBlocker { blocker_hash } => {
                write!(f, "duplicate unresolved blocker `{blocker_hash}`")
            }
            Self::DuplicateRejectionReason { reason } => {
                write!(f, "duplicate rejection reason `{}`", reason.wire())
            }
            Self::StaleCertificate {
                certificate_key,
                certificate_hash,
                current_certificate_hash,
            } => write!(
                f,
                "certificate `{certificate_key}` recorded hash `{certificate_hash}` does not match current hash `{current_certificate_hash}`"
            ),
            Self::MissingAssumptionListHash => write!(f, "missing full assumption-list hash"),
            Self::ConditionalClaimRequiresAssumptionList => {
                write!(f, "conditional and special-case claims require assumptions")
            }
            Self::SpecialCaseClaimRequiresScope => write!(f, "special-case claim requires scope"),
            Self::MissingAssumptionDisclosure => {
                write!(f, "missing assumption disclosure hash")
            }
            Self::MissingAxiomReport => write!(f, "missing axiom report hash"),
            Self::MissingCertificateHash => write!(f, "missing certificate hash"),
            Self::MissingSourceFreeReproduction => {
                write!(f, "missing source-free reproduction command hash")
            }
            Self::MissingIndependentChecker => write!(f, "missing independent checker hash"),
            Self::MissingCleanReproduction => write!(f, "missing clean reproduction hash"),
            Self::MissingHumanReview => write!(f, "missing human mathematical review hash"),
            Self::MissingBarrierReview => write!(f, "missing barrier review hash"),
            Self::MissingFormalProofEvidence => write!(f, "missing formal proof evidence hash"),
            Self::RefutationRequiresCounterexampleOrRefutation => {
                write!(f, "refutation requires checked counterexample or refutation hash")
            }
            Self::ExperimentOnlyClaimCannotPassGate => {
                write!(f, "experiment-only claim cannot pass the claim-publication gate")
            }
            Self::NotebookOnlyClaimCannotPassGate => {
                write!(f, "notebook-only claim cannot pass the claim-publication gate")
            }
            Self::BarrierOnlyClaimCannotPassGate => {
                write!(f, "barrier-only claim cannot pass the claim-publication gate")
            }
            Self::SupportingEvidenceClaimClassMismatch {
                claim_class,
                supporting_evidence_kind,
            } => write!(
                f,
                "claim class `{}` cannot use supporting evidence kind `{}`",
                claim_class.wire(),
                supporting_evidence_kind.wire()
            ),
            Self::UnresolvedBlocker { blocker_hash } => {
                write!(f, "unresolved blocker `{blocker_hash}`")
            }
            Self::InformalExplanationCannotBeFormalProof => {
                write!(f, "informal explanation cannot be formal proof evidence")
            }
            Self::ApprovedGateRequiresTargetTransitionAuthorization => write!(
                f,
                "approved terminal claim requires target-state transition authorization"
            ),
            Self::ProgressClaimCannotAuthorizeTerminalTransition => {
                write!(f, "conditional or special-case progress cannot authorize a terminal transition")
            }
            Self::RejectedGateCannotAuthorizeTargetTransition => {
                write!(f, "rejected gate cannot authorize a target-state transition")
            }
            Self::ApprovedGateRequiresPuaM17Handoff => {
                write!(f, "approved gate requires PUA-M17 handoff eligibility")
            }
            Self::HandoffEligibilityRequiresHash => {
                write!(f, "PUA-M17 handoff eligibility requires handoff hash")
            }
            Self::ApprovedGateCannotCarryRejectionReasons => {
                write!(f, "approved gate cannot carry rejection reasons")
            }
            Self::RejectionRequiresReason => write!(f, "rejected gate requires rejection reason"),
        }
    }
}

pub fn parse_claim_publication_gate_record(
    source: &str,
) -> Result<ClaimPublicationGateRecord, ClaimPublicationGateSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != CLAIM_PUBLICATION_GATE_API_VERSION {
        return Err(ClaimPublicationGateSchemaError::new(
            "$.api_version",
            ClaimPublicationGateSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ClaimPublicationGateRecord {
        api_version,
        record_key: required_string(&root, "record_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        formal_statement_hash: required_hash(&root, "formal_statement_hash", "$")?,
        reviewed_formal_statement_hash: required_hash(
            &root,
            "reviewed_formal_statement_hash",
            "$",
        )?,
        claim_class: parse_claim_class_value(
            required_value(&root, "claim_class", "$")?,
            "$.claim_class",
        )?,
        proposed_target_state: parse_target_state_value(
            required_value(&root, "proposed_target_state", "$")?,
            "$.proposed_target_state",
        )?,
        gate_decision: parse_gate_decision_value(
            required_value(&root, "gate_decision", "$")?,
            "$.gate_decision",
        )?,
        review_procedure_hash: required_hash(&root, "review_procedure_hash", "$")?,
        assumption_list_hash: optional_hash(&root, "assumption_list_hash", "$")?,
        assumption_disclosure_hash: optional_hash(&root, "assumption_disclosure_hash", "$")?,
        assumptions: parse_assumptions(required_value(&root, "assumptions", "$")?)?,
        axiom_report_hash: optional_hash(&root, "axiom_report_hash", "$")?,
        certificate_references: parse_certificate_references(required_value(
            &root,
            "certificate_references",
            "$",
        )?)?,
        source_free_reproduction_command_hashes: parse_hash_array(
            required_value(&root, "source_free_reproduction_command_hashes", "$")?,
            "$.source_free_reproduction_command_hashes",
        )?,
        independent_checker_hash: optional_hash(&root, "independent_checker_hash", "$")?,
        clean_reproduction_hash: optional_hash(&root, "clean_reproduction_hash", "$")?,
        human_review_hash: optional_hash(&root, "human_review_hash", "$")?,
        barrier_review_hash: optional_hash(&root, "barrier_review_hash", "$")?,
        barrier_relationship: parse_barrier_relationship_value(
            required_value(&root, "barrier_relationship", "$")?,
            "$.barrier_relationship",
        )?,
        supporting_evidence_kind: parse_supporting_evidence_kind_value(
            required_value(&root, "supporting_evidence_kind", "$")?,
            "$.supporting_evidence_kind",
        )?,
        formal_proof_evidence_hash: optional_hash(&root, "formal_proof_evidence_hash", "$")?,
        counterexample_or_refutation_hash: optional_hash(
            &root,
            "counterexample_or_refutation_hash",
            "$",
        )?,
        special_case_scope_hash: optional_hash(&root, "special_case_scope_hash", "$")?,
        unresolved_blocker_hashes: parse_hash_array(
            required_value(&root, "unresolved_blocker_hashes", "$")?,
            "$.unresolved_blocker_hashes",
        )?,
        informal_explanation_hash: optional_hash(&root, "informal_explanation_hash", "$")?,
        informal_explanation_is_formal_proof: required_bool(
            &root,
            "informal_explanation_is_formal_proof",
            "$",
        )?,
        target_state_transition_authorized: required_bool(
            &root,
            "target_state_transition_authorized",
            "$",
        )?,
        pua_m17_bundle_handoff_eligible: required_bool(
            &root,
            "pua_m17_bundle_handoff_eligible",
            "$",
        )?,
        pua_m17_bundle_handoff_hash: optional_hash(&root, "pua_m17_bundle_handoff_hash", "$")?,
        rejection_reasons: parse_rejection_reasons(required_value(
            &root,
            "rejection_reasons",
            "$",
        )?)?,
        wall_clock_time: optional_string(&root, "wall_clock_time", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_claim_publication_gate_record(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    require_non_empty(&record.record_key, "record_key")?;
    require_non_empty(&record.target_key, "target_key")?;
    if record.formal_statement_hash != record.reviewed_formal_statement_hash {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ExactFormalStatementMismatch {
                formal_statement_hash: format_hash_string(&record.formal_statement_hash),
                reviewed_formal_statement_hash: format_hash_string(
                    &record.reviewed_formal_statement_hash,
                ),
            },
        ));
    }
    validate_claim_class_state(record)?;
    validate_assumptions(record)?;
    validate_certificates(record)?;
    validate_hash_list(
        "source_free",
        &record.source_free_reproduction_command_hashes,
    )?;
    validate_hash_list("unresolved_blocker", &record.unresolved_blocker_hashes)?;
    validate_rejection_reasons(&record.rejection_reasons)?;
    validate_informal_explanation_boundary(record)?;

    match record.gate_decision {
        ClaimPublicationGateDecision::Approved => validate_approved_gate(record),
        ClaimPublicationGateDecision::Rejected => validate_rejected_gate(record),
    }
}

pub fn claim_publication_gate_canonical_identity_bytes(
    record: &ClaimPublicationGateRecord,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, CLAIM_PUBLICATION_GATE_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &record.target_key);
    encode_string_to(&mut out, "formal_statement_hash");
    encode_hash_to(&mut out, &record.formal_statement_hash);
    encode_string_to(&mut out, "reviewed_formal_statement_hash");
    encode_hash_to(&mut out, &record.reviewed_formal_statement_hash);
    encode_string_to(&mut out, "claim_class");
    encode_string_to(&mut out, record.claim_class.wire());
    encode_string_to(&mut out, "proposed_target_state");
    encode_string_to(&mut out, record.proposed_target_state.wire());
    encode_string_to(&mut out, "gate_decision");
    encode_string_to(&mut out, record.gate_decision.wire());
    encode_string_to(&mut out, "review_procedure_hash");
    encode_hash_to(&mut out, &record.review_procedure_hash);
    encode_option_hash_to(
        &mut out,
        "assumption_list_hash",
        record.assumption_list_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "assumption_disclosure_hash",
        record.assumption_disclosure_hash.as_ref(),
    );
    encode_assumptions_to(&mut out, &record.assumptions);
    encode_option_hash_to(
        &mut out,
        "axiom_report_hash",
        record.axiom_report_hash.as_ref(),
    );
    encode_certificates_to(&mut out, &record.certificate_references);
    encode_hash_list_to(
        &mut out,
        "source_free_reproduction_command_hashes",
        &record.source_free_reproduction_command_hashes,
    );
    encode_option_hash_to(
        &mut out,
        "independent_checker_hash",
        record.independent_checker_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "clean_reproduction_hash",
        record.clean_reproduction_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "human_review_hash",
        record.human_review_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "barrier_review_hash",
        record.barrier_review_hash.as_ref(),
    );
    encode_string_to(&mut out, "barrier_relationship");
    encode_string_to(&mut out, record.barrier_relationship.wire());
    encode_string_to(&mut out, "supporting_evidence_kind");
    encode_string_to(&mut out, record.supporting_evidence_kind.wire());
    encode_option_hash_to(
        &mut out,
        "formal_proof_evidence_hash",
        record.formal_proof_evidence_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "counterexample_or_refutation_hash",
        record.counterexample_or_refutation_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "special_case_scope_hash",
        record.special_case_scope_hash.as_ref(),
    );
    encode_hash_list_to(
        &mut out,
        "unresolved_blocker_hashes",
        &record.unresolved_blocker_hashes,
    );
    encode_option_hash_to(
        &mut out,
        "informal_explanation_hash",
        record.informal_explanation_hash.as_ref(),
    );
    encode_string_to(&mut out, "informal_explanation_is_formal_proof");
    out.push(u8::from(record.informal_explanation_is_formal_proof));
    encode_string_to(&mut out, "target_state_transition_authorized");
    out.push(u8::from(record.target_state_transition_authorized));
    encode_string_to(&mut out, "pua_m17_bundle_handoff_eligible");
    out.push(u8::from(record.pua_m17_bundle_handoff_eligible));
    encode_option_hash_to(
        &mut out,
        "pua_m17_bundle_handoff_hash",
        record.pua_m17_bundle_handoff_hash.as_ref(),
    );
    encode_rejection_reasons_to(&mut out, &record.rejection_reasons);
    out
}

pub fn claim_publication_gate_hash(record: &ClaimPublicationGateRecord) -> Hash {
    let digest = Sha256::digest(claim_publication_gate_canonical_identity_bytes(record));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn claim_publication_gate_hash_string(record: &ClaimPublicationGateRecord) -> String {
    format_hash_string(&claim_publication_gate_hash(record))
}

fn validate_claim_class_state(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    let expected = match record.claim_class {
        ResearchTargetClaimClass::Resolution => ResearchTargetState::Resolved,
        ResearchTargetClaimClass::Refutation => ResearchTargetState::Refuted,
        ResearchTargetClaimClass::ConditionalProgress => ResearchTargetState::ConditionalProgress,
        ResearchTargetClaimClass::SpecialCaseProgress => ResearchTargetState::SpecialCaseProgress,
    };
    if record.proposed_target_state != expected {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ClaimClassTargetStateMismatch {
                claim_class: record.claim_class,
                proposed_target_state: record.proposed_target_state,
            },
        ));
    }
    Ok(())
}

fn validate_assumptions(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    let mut seen = BTreeSet::new();
    for assumption in &record.assumptions {
        require_non_empty(&assumption.assumption_key, "assumptions.assumption_key")?;
        if !seen.insert(assumption.assumption_key.as_str()) {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::DuplicateAssumption {
                    assumption_key: assumption.assumption_key.clone(),
                },
            ));
        }
    }

    if record.gate_decision == ClaimPublicationGateDecision::Approved {
        if record.assumption_list_hash.is_none() {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::MissingAssumptionListHash,
            ));
        }
        let assumptions_required = matches!(
            record.claim_class,
            ResearchTargetClaimClass::ConditionalProgress
                | ResearchTargetClaimClass::SpecialCaseProgress
        );
        if assumptions_required && record.assumptions.is_empty() {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::ConditionalClaimRequiresAssumptionList,
            ));
        }
        if (!record.assumptions.is_empty() || assumptions_required)
            && record.assumption_disclosure_hash.is_none()
        {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::MissingAssumptionDisclosure,
            ));
        }
        if record.claim_class == ResearchTargetClaimClass::SpecialCaseProgress
            && record.special_case_scope_hash.is_none()
        {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::SpecialCaseClaimRequiresScope,
            ));
        }
    }
    Ok(())
}

fn validate_certificates(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    let mut seen = BTreeSet::new();
    for certificate in &record.certificate_references {
        require_non_empty(
            &certificate.certificate_key,
            "certificate_references.certificate_key",
        )?;
        if !seen.insert(certificate.certificate_key.as_str()) {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::DuplicateCertificate {
                    certificate_key: certificate.certificate_key.clone(),
                },
            ));
        }
        if certificate.certificate_hash != certificate.current_certificate_hash {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::StaleCertificate {
                    certificate_key: certificate.certificate_key.clone(),
                    certificate_hash: format_hash_string(&certificate.certificate_hash),
                    current_certificate_hash: format_hash_string(
                        &certificate.current_certificate_hash,
                    ),
                },
            ));
        }
    }
    Ok(())
}

fn validate_hash_list(
    label: &'static str,
    hashes: &[Hash],
) -> Result<(), ClaimPublicationGateValidationError> {
    let mut seen = BTreeSet::new();
    for hash in hashes {
        if !seen.insert(*hash) {
            let hash = format_hash_string(hash);
            return match label {
                "source_free" => Err(ClaimPublicationGateValidationError::new(
                    ClaimPublicationGateValidationErrorKind::DuplicateSourceFreeReproductionCommand {
                        command_hash: hash,
                    },
                )),
                "unresolved_blocker" => Err(ClaimPublicationGateValidationError::new(
                    ClaimPublicationGateValidationErrorKind::DuplicateUnresolvedBlocker {
                        blocker_hash: hash,
                    },
                )),
                _ => Ok(()),
            };
        }
    }
    Ok(())
}

fn validate_rejection_reasons(
    reasons: &[ClaimPublicationGateRejectionReason],
) -> Result<(), ClaimPublicationGateValidationError> {
    let mut seen = BTreeSet::new();
    for reason in reasons {
        if !seen.insert(*reason) {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::DuplicateRejectionReason {
                    reason: *reason,
                },
            ));
        }
    }
    Ok(())
}

fn validate_informal_explanation_boundary(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    if record.informal_explanation_is_formal_proof {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::InformalExplanationCannotBeFormalProof,
        ));
    }
    if let (Some(informal), Some(proof)) = (
        record.informal_explanation_hash,
        record.formal_proof_evidence_hash,
    ) {
        if informal == proof {
            return Err(ClaimPublicationGateValidationError::new(
                ClaimPublicationGateValidationErrorKind::InformalExplanationCannotBeFormalProof,
            ));
        }
    }
    Ok(())
}

fn validate_approved_gate(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    if record.axiom_report_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingAxiomReport,
        ));
    }
    if record.certificate_references.is_empty() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingCertificateHash,
        ));
    }
    if record.source_free_reproduction_command_hashes.is_empty() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingSourceFreeReproduction,
        ));
    }
    if record.independent_checker_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingIndependentChecker,
        ));
    }
    if record.clean_reproduction_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingCleanReproduction,
        ));
    }
    if record.human_review_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingHumanReview,
        ));
    }
    if record.barrier_review_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingBarrierReview,
        ));
    }
    if record.formal_proof_evidence_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::MissingFormalProofEvidence,
        ));
    }
    if record.claim_class == ResearchTargetClaimClass::Refutation
        && record.counterexample_or_refutation_hash.is_none()
    {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::RefutationRequiresCounterexampleOrRefutation,
        ));
    }
    if let Some(blocker) = record.unresolved_blocker_hashes.first() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::UnresolvedBlocker {
                blocker_hash: format_hash_string(blocker),
            },
        ));
    }
    if record.supporting_evidence_kind.is_non_proof_sidecar() {
        return Err(ClaimPublicationGateValidationError::new(
            match record.supporting_evidence_kind {
                ClaimPublicationSupportingEvidenceKind::ExperimentOnly => {
                    ClaimPublicationGateValidationErrorKind::ExperimentOnlyClaimCannotPassGate
                }
                ClaimPublicationSupportingEvidenceKind::NotebookOnly => {
                    ClaimPublicationGateValidationErrorKind::NotebookOnlyClaimCannotPassGate
                }
                ClaimPublicationSupportingEvidenceKind::BarrierOnly => {
                    ClaimPublicationGateValidationErrorKind::BarrierOnlyClaimCannotPassGate
                }
                _ => unreachable!("non-proof sidecar check already matched"),
            },
        ));
    }
    let expected_evidence_kind = match record.claim_class {
        ResearchTargetClaimClass::Resolution => {
            ClaimPublicationSupportingEvidenceKind::VerifiedCertificate
        }
        ResearchTargetClaimClass::Refutation => {
            ClaimPublicationSupportingEvidenceKind::CheckedRefutation
        }
        ResearchTargetClaimClass::ConditionalProgress => {
            ClaimPublicationSupportingEvidenceKind::ConditionalTheorem
        }
        ResearchTargetClaimClass::SpecialCaseProgress => {
            ClaimPublicationSupportingEvidenceKind::SpecialCaseTheorem
        }
    };
    if record.supporting_evidence_kind != expected_evidence_kind {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::SupportingEvidenceClaimClassMismatch {
                claim_class: record.claim_class,
                supporting_evidence_kind: record.supporting_evidence_kind,
            },
        ));
    }
    let terminal_claim = record.proposed_target_state.is_claim_terminal();
    if terminal_claim && !record.target_state_transition_authorized {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ApprovedGateRequiresTargetTransitionAuthorization,
        ));
    }
    if !terminal_claim && record.target_state_transition_authorized {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ProgressClaimCannotAuthorizeTerminalTransition,
        ));
    }
    if !record.pua_m17_bundle_handoff_eligible {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ApprovedGateRequiresPuaM17Handoff,
        ));
    }
    if record.pua_m17_bundle_handoff_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::HandoffEligibilityRequiresHash,
        ));
    }
    if !record.rejection_reasons.is_empty() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::ApprovedGateCannotCarryRejectionReasons,
        ));
    }
    Ok(())
}

fn validate_rejected_gate(
    record: &ClaimPublicationGateRecord,
) -> Result<(), ClaimPublicationGateValidationError> {
    if record.target_state_transition_authorized {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::RejectedGateCannotAuthorizeTargetTransition,
        ));
    }
    if record.rejection_reasons.is_empty() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::RejectionRequiresReason,
        ));
    }
    if record.pua_m17_bundle_handoff_eligible && record.pua_m17_bundle_handoff_hash.is_none() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::HandoffEligibilityRequiresHash,
        ));
    }
    Ok(())
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ClaimPublicationGateSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ClaimPublicationGateSchemaError::new(
            "$",
            ClaimPublicationGateSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ClaimPublicationGateSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ClaimPublicationGateSchemaError::new(
                format!("{path}.{}", member.key()),
                ClaimPublicationGateSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ClaimPublicationGateSchemaError::new(
                format!("{path}.{}", member.key()),
                ClaimPublicationGateSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ClaimPublicationGateSchemaError> {
    value.array_elements().ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ClaimPublicationGateSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            format!("{path}.{field}"),
            ClaimPublicationGateSchemaErrorKind::MissingField { field },
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
) -> Result<String, ClaimPublicationGateSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ClaimPublicationGateSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<String, ClaimPublicationGateSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ClaimPublicationGateSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ClaimPublicationGateSchemaError> {
    value.bool_value().ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ClaimPublicationGateSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ClaimPublicationGateSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_assumptions(
    value: &JsonValue<'_>,
) -> Result<Vec<ClaimPublicationGateAssumption>, ClaimPublicationGateSchemaError> {
    array_elements(value, "$.assumptions")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_assumption(value, &format!("$.assumptions[{index}]")))
        .collect()
}

fn parse_assumption(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationGateAssumption, ClaimPublicationGateSchemaError> {
    let members = object_map(value, path, ASSUMPTION_FIELDS)?;
    Ok(ClaimPublicationGateAssumption {
        assumption_key: required_string(&members, "assumption_key", path)?,
        assumption_hash: required_hash(&members, "assumption_hash", path)?,
        disclosure_hash: required_hash(&members, "disclosure_hash", path)?,
    })
}

fn parse_certificate_references(
    value: &JsonValue<'_>,
) -> Result<Vec<ClaimPublicationGateCertificateReference>, ClaimPublicationGateSchemaError> {
    array_elements(value, "$.certificate_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_certificate_reference(value, &format!("$.certificate_references[{index}]"))
        })
        .collect()
}

fn parse_certificate_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationGateCertificateReference, ClaimPublicationGateSchemaError> {
    let members = object_map(value, path, CERTIFICATE_REFERENCE_FIELDS)?;
    Ok(ClaimPublicationGateCertificateReference {
        certificate_key: required_string(&members, "certificate_key", path)?,
        certificate_hash: required_hash(&members, "certificate_hash", path)?,
        current_certificate_hash: required_hash(&members, "current_certificate_hash", path)?,
        source_free_reproduction_hash: required_hash(
            &members,
            "source_free_reproduction_hash",
            path,
        )?,
        checker_profile_hash: required_hash(&members, "checker_profile_hash", path)?,
    })
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, ClaimPublicationGateSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_rejection_reasons(
    value: &JsonValue<'_>,
) -> Result<Vec<ClaimPublicationGateRejectionReason>, ClaimPublicationGateSchemaError> {
    array_elements(value, "$.rejection_reasons")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_rejection_reason_value(value, &format!("$.rejection_reasons[{index}]"))
        })
        .collect()
}

fn parse_claim_class_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetClaimClass, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetClaimClass::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidClaimClass { value: wire },
        )
    })
}

fn parse_target_state_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchTargetState, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ResearchTargetState::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidTargetState { value: wire },
        )
    })
}

fn parse_gate_decision_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationGateDecision, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ClaimPublicationGateDecision::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidGateDecision { value: wire },
        )
    })
}

fn parse_barrier_relationship_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationBarrierRelationship, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ClaimPublicationBarrierRelationship::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidBarrierRelationship { value: wire },
        )
    })
}

fn parse_supporting_evidence_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationSupportingEvidenceKind, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ClaimPublicationSupportingEvidenceKind::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidSupportingEvidenceKind { value: wire },
        )
    })
}

fn parse_rejection_reason_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ClaimPublicationGateRejectionReason, ClaimPublicationGateSchemaError> {
    let wire = string_value(value, path)?;
    ClaimPublicationGateRejectionReason::parse(&wire).ok_or_else(|| {
        ClaimPublicationGateSchemaError::new(
            path,
            ClaimPublicationGateSchemaErrorKind::InvalidRejectionReason { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ClaimPublicationGateValidationError> {
    if value.trim().is_empty() {
        return Err(ClaimPublicationGateValidationError::new(
            ClaimPublicationGateValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_assumptions_to(out: &mut Vec<u8>, assumptions: &[ClaimPublicationGateAssumption]) {
    encode_string_to(out, "assumptions");
    let mut assumptions = assumptions.to_vec();
    assumptions.sort_by(|left, right| left.assumption_key.cmp(&right.assumption_key));
    encode_len_to(out, assumptions.len());
    for assumption in &assumptions {
        encode_string_to(out, &assumption.assumption_key);
        encode_hash_to(out, &assumption.assumption_hash);
        encode_hash_to(out, &assumption.disclosure_hash);
    }
}

fn encode_certificates_to(
    out: &mut Vec<u8>,
    certificates: &[ClaimPublicationGateCertificateReference],
) {
    encode_string_to(out, "certificate_references");
    let mut certificates = certificates.to_vec();
    certificates.sort_by(|left, right| left.certificate_key.cmp(&right.certificate_key));
    encode_len_to(out, certificates.len());
    for certificate in &certificates {
        encode_string_to(out, &certificate.certificate_key);
        encode_hash_to(out, &certificate.certificate_hash);
        encode_hash_to(out, &certificate.current_certificate_hash);
        encode_hash_to(out, &certificate.source_free_reproduction_hash);
        encode_hash_to(out, &certificate.checker_profile_hash);
    }
}

fn encode_hash_list_to(out: &mut Vec<u8>, label: &str, hashes: &[Hash]) {
    encode_string_to(out, label);
    let mut hashes = hashes.to_vec();
    hashes.sort();
    encode_len_to(out, hashes.len());
    for hash in &hashes {
        encode_hash_to(out, hash);
    }
}

fn encode_rejection_reasons_to(out: &mut Vec<u8>, reasons: &[ClaimPublicationGateRejectionReason]) {
    encode_string_to(out, "rejection_reasons");
    let mut reasons = reasons.to_vec();
    reasons.sort();
    encode_len_to(out, reasons.len());
    for reason in &reasons {
        encode_string_to(out, reason.wire());
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_len_to(out, value.len());
    out.extend_from_slice(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_option_hash_to(out: &mut Vec<u8>, label: &str, value: Option<&Hash>) {
    encode_string_to(out, label);
    match value {
        Some(hash) => {
            out.push(1);
            encode_hash_to(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    out.extend_from_slice(&(len as u64).to_be_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    fn fixture_path(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("npa-api is under crates")
            .parent()
            .expect("crates is under repo root")
            .join("testdata/proof-using-agents/fixtures/pua-m16-claim-publication-gate")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name))
            .expect("claim-publication gate fixture should exist")
    }

    fn parse_fixture(name: &str) -> ClaimPublicationGateRecord {
        parse_claim_publication_gate_record(&fixture(name))
            .expect("claim-publication gate fixture should parse")
    }

    fn validate_fixture(name: &str) -> Result<(), ClaimPublicationGateValidationErrorKind> {
        let record = parse_fixture(name);
        validate_claim_publication_gate_record(&record).map_err(|error| error.kind().clone())
    }

    #[test]
    fn claim_publication_gate_requires_independent_checker() {
        let approved = parse_fixture("valid-resolution.json");
        validate_claim_publication_gate_record(&approved).expect("resolution gate validates");
        assert_eq!(
            approved.proposed_target_state,
            ResearchTargetState::Resolved
        );
        assert!(approved.target_state_transition_authorized);

        let mut display_changed = approved.clone();
        display_changed.wall_clock_time = Some("2099-12-31T23:59:59Z".to_owned());
        display_changed.display_text = Some("display text changed".to_owned());
        display_changed.record_key = "claim-gate.pnp.resolution.copy".to_owned();
        assert_eq!(
            claim_publication_gate_hash(&approved),
            claim_publication_gate_hash(&display_changed)
        );

        let mut evidence_changed = approved.clone();
        evidence_changed.independent_checker_hash = Some(
            parse_hash_string(
                "sha256:9999999999999999999999999999999999999999999999999999999999999999",
            )
            .expect("test hash parses"),
        );
        assert_ne!(
            claim_publication_gate_hash(&approved),
            claim_publication_gate_hash(&evidence_changed)
        );

        assert!(matches!(
            validate_fixture("missing-independent-checker.json"),
            Err(ClaimPublicationGateValidationErrorKind::MissingIndependentChecker)
        ));
        assert!(matches!(
            validate_fixture("missing-clean-reproduction.json"),
            Err(ClaimPublicationGateValidationErrorKind::MissingCleanReproduction)
        ));
        assert!(matches!(
            validate_fixture("informal-explanation-as-proof.json"),
            Err(ClaimPublicationGateValidationErrorKind::InformalExplanationCannotBeFormalProof)
        ));

        let mut ambiguous_approval = approved.clone();
        ambiguous_approval
            .rejection_reasons
            .push(ClaimPublicationGateRejectionReason::MissingIndependentChecker);
        assert!(matches!(
            validate_claim_publication_gate_record(&ambiguous_approval)
                .map_err(|error| error.kind().clone()),
            Err(ClaimPublicationGateValidationErrorKind::ApprovedGateCannotCarryRejectionReasons)
        ));
    }

    #[test]
    fn claim_publication_gate_rejects_experiment_only() {
        let refutation = parse_fixture("valid-refutation.json");
        validate_claim_publication_gate_record(&refutation).expect("refutation gate validates");
        assert_eq!(
            refutation.proposed_target_state,
            ResearchTargetState::Refuted
        );
        assert!(refutation.counterexample_or_refutation_hash.is_some());

        assert!(matches!(
            validate_fixture("experiment-only-claim.json"),
            Err(ClaimPublicationGateValidationErrorKind::ExperimentOnlyClaimCannotPassGate)
        ));
        let mut mismatched_evidence = refutation.clone();
        mismatched_evidence.supporting_evidence_kind =
            ClaimPublicationSupportingEvidenceKind::VerifiedCertificate;
        assert!(matches!(
            validate_claim_publication_gate_record(&mismatched_evidence)
                .map_err(|error| error.kind().clone()),
            Err(
                ClaimPublicationGateValidationErrorKind::SupportingEvidenceClaimClassMismatch { .. }
            )
        ));
        assert!(matches!(
            validate_fixture("stale-certificate.json"),
            Err(ClaimPublicationGateValidationErrorKind::StaleCertificate { .. })
        ));
        assert!(matches!(
            validate_fixture("unresolved-blocker.json"),
            Err(ClaimPublicationGateValidationErrorKind::UnresolvedBlocker { .. })
        ));
        assert!(matches!(
            validate_fixture("missing-barrier-review.json"),
            Err(ClaimPublicationGateValidationErrorKind::MissingBarrierReview)
        ));
    }

    #[test]
    fn claim_publication_gate_requires_assumption_list() {
        let conditional = parse_fixture("valid-conditional-progress.json");
        validate_claim_publication_gate_record(&conditional).expect("conditional gate validates");
        assert_eq!(
            conditional.proposed_target_state,
            ResearchTargetState::ConditionalProgress
        );
        assert!(!conditional.target_state_transition_authorized);
        assert!(!conditional.assumptions.is_empty());

        let special_case = parse_fixture("valid-special-case-progress.json");
        validate_claim_publication_gate_record(&special_case).expect("special-case gate validates");
        assert_eq!(
            special_case.proposed_target_state,
            ResearchTargetState::SpecialCaseProgress
        );
        assert!(special_case.special_case_scope_hash.is_some());

        assert!(matches!(
            validate_fixture("missing-assumption.json"),
            Err(ClaimPublicationGateValidationErrorKind::ConditionalClaimRequiresAssumptionList)
        ));
        assert!(matches!(
            validate_fixture("missing-assumption-disclosure.json"),
            Err(ClaimPublicationGateValidationErrorKind::MissingAssumptionDisclosure)
        ));
        assert!(matches!(
            validate_fixture("claim-class-state-mismatch.json"),
            Err(ClaimPublicationGateValidationErrorKind::ClaimClassTargetStateMismatch { .. })
        ));
    }
}

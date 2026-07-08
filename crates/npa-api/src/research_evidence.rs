use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const RESEARCH_EVIDENCE_API_VERSION: &str = "npa.research-evidence.v1";
pub const RESEARCH_EVIDENCE_HASH_DOMAIN: &str = "npa.research-evidence.identity.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "evidence_key",
    "target_key",
    "formal_statement_hash",
    "evidence_level",
    "evidence_kind",
    "claim_scope",
    "verified_theorem_artifact_hash",
    "certificate_hash",
    "axiom_report_hash",
    "checker_profile_hash",
    "assumptions",
    "bound_hash",
    "experiment_result_hash",
    "counterexample_or_refutation_hash",
    "independent_checker_hash",
    "human_review_hash",
    "barrier_review_hash",
    "reproduction_hash",
    "model_output_hash",
    "notebook_entry_hash",
    "barrier_audit_hash",
    "display_text",
];
const ASSUMPTION_FIELDS: &[&str] = &["assumption_hash", "disclosure_hash"];

const E0_CLAIMS: &[ResearchEvidenceClaimScope] = &[ResearchEvidenceClaimScope::NoProofClaim];
const E1_CLAIMS: &[ResearchEvidenceClaimScope] = &[ResearchEvidenceClaimScope::BoundedObservation];
const E2_CLAIMS: &[ResearchEvidenceClaimScope] = &[
    ResearchEvidenceClaimScope::FiniteCaseTheorem,
    ResearchEvidenceClaimScope::SpecialCaseTheorem,
];
const E3_CLAIMS: &[ResearchEvidenceClaimScope] = &[ResearchEvidenceClaimScope::ConditionalTheorem];
const E4_CLAIMS: &[ResearchEvidenceClaimScope] = &[
    ResearchEvidenceClaimScope::GeneralProof,
    ResearchEvidenceClaimScope::GeneralRefutation,
];
const E5_CLAIMS: &[ResearchEvidenceClaimScope] = &[
    ResearchEvidenceClaimScope::TerminalResolution,
    ResearchEvidenceClaimScope::TerminalRefutation,
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchEvidence {
    pub api_version: String,
    pub evidence_key: String,
    pub target_key: String,
    pub formal_statement_hash: Hash,
    pub evidence_level: ResearchEvidenceLevel,
    pub evidence_kind: ResearchEvidenceKind,
    pub claim_scope: ResearchEvidenceClaimScope,
    pub verified_theorem_artifact_hash: Option<Hash>,
    pub certificate_hash: Option<Hash>,
    pub axiom_report_hash: Option<Hash>,
    pub checker_profile_hash: Option<Hash>,
    pub assumptions: Vec<ResearchEvidenceAssumption>,
    pub bound_hash: Option<Hash>,
    pub experiment_result_hash: Option<Hash>,
    pub counterexample_or_refutation_hash: Option<Hash>,
    pub independent_checker_hash: Option<Hash>,
    pub human_review_hash: Option<Hash>,
    pub barrier_review_hash: Option<Hash>,
    pub reproduction_hash: Option<Hash>,
    pub model_output_hash: Option<Hash>,
    pub notebook_entry_hash: Option<Hash>,
    pub barrier_audit_hash: Option<Hash>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchEvidenceAssumption {
    pub assumption_hash: Hash,
    pub disclosure_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchEvidenceLevel {
    E0,
    E1,
    E2,
    E3,
    E4,
    E5,
}

impl ResearchEvidenceLevel {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::E0 => "E0",
            Self::E1 => "E1",
            Self::E2 => "E2",
            Self::E3 => "E3",
            Self::E4 => "E4",
            Self::E5 => "E5",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "E0" => Some(Self::E0),
            "E1" => Some(Self::E1),
            "E2" => Some(Self::E2),
            "E3" => Some(Self::E3),
            "E4" => Some(Self::E4),
            "E5" => Some(Self::E5),
            _ => None,
        }
    }

    pub const fn permitted_claim_text(self) -> &'static str {
        match self {
            Self::E0 => "no proof claim",
            Self::E1 => "only within stated bounds",
            Self::E2 => "formally proved finite or special case theorem",
            Self::E3 => "proved under explicit assumptions",
            Self::E4 => "verified general theorem or checked refutation candidate",
            Self::E5 => "independently verified resolution or refutation",
        }
    }

    pub const fn permitted_claim_scopes(self) -> &'static [ResearchEvidenceClaimScope] {
        match self {
            Self::E0 => E0_CLAIMS,
            Self::E1 => E1_CLAIMS,
            Self::E2 => E2_CLAIMS,
            Self::E3 => E3_CLAIMS,
            Self::E4 => E4_CLAIMS,
            Self::E5 => E5_CLAIMS,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchEvidenceKind {
    Proof,
    ConditionalProof,
    FiniteCase,
    SpecialCase,
    Counterexample,
    Refutation,
    Experiment,
    Heuristic,
    BarrierResult,
    OpenBlocker,
}

impl ResearchEvidenceKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Proof => "proof",
            Self::ConditionalProof => "conditional_proof",
            Self::FiniteCase => "finite_case",
            Self::SpecialCase => "special_case",
            Self::Counterexample => "counterexample",
            Self::Refutation => "refutation",
            Self::Experiment => "experiment",
            Self::Heuristic => "heuristic",
            Self::BarrierResult => "barrier_result",
            Self::OpenBlocker => "open_blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "proof" => Some(Self::Proof),
            "conditional_proof" => Some(Self::ConditionalProof),
            "finite_case" => Some(Self::FiniteCase),
            "special_case" => Some(Self::SpecialCase),
            "counterexample" => Some(Self::Counterexample),
            "refutation" => Some(Self::Refutation),
            "experiment" => Some(Self::Experiment),
            "heuristic" => Some(Self::Heuristic),
            "barrier_result" => Some(Self::BarrierResult),
            "open_blocker" => Some(Self::OpenBlocker),
            _ => None,
        }
    }

    pub const fn is_non_proof_sidecar(self) -> bool {
        matches!(
            self,
            Self::Experiment | Self::Heuristic | Self::BarrierResult | Self::OpenBlocker
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchEvidenceClaimScope {
    NoProofClaim,
    BoundedObservation,
    FiniteCaseTheorem,
    SpecialCaseTheorem,
    ConditionalTheorem,
    GeneralProof,
    GeneralRefutation,
    TerminalResolution,
    TerminalRefutation,
}

impl ResearchEvidenceClaimScope {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::NoProofClaim => "no_proof_claim",
            Self::BoundedObservation => "bounded_observation",
            Self::FiniteCaseTheorem => "finite_case_theorem",
            Self::SpecialCaseTheorem => "special_case_theorem",
            Self::ConditionalTheorem => "conditional_theorem",
            Self::GeneralProof => "general_proof",
            Self::GeneralRefutation => "general_refutation",
            Self::TerminalResolution => "terminal_resolution",
            Self::TerminalRefutation => "terminal_refutation",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "no_proof_claim" => Some(Self::NoProofClaim),
            "bounded_observation" => Some(Self::BoundedObservation),
            "finite_case_theorem" => Some(Self::FiniteCaseTheorem),
            "special_case_theorem" => Some(Self::SpecialCaseTheorem),
            "conditional_theorem" => Some(Self::ConditionalTheorem),
            "general_proof" => Some(Self::GeneralProof),
            "general_refutation" => Some(Self::GeneralRefutation),
            "terminal_resolution" => Some(Self::TerminalResolution),
            "terminal_refutation" => Some(Self::TerminalRefutation),
            _ => None,
        }
    }

    pub const fn claims_proof(self) -> bool {
        !matches!(self, Self::NoProofClaim | Self::BoundedObservation)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchEvidenceRequiredArtifact {
    VerifiedTheoremArtifact,
    CertificateHash,
    AxiomReportHash,
    CheckerProfileHash,
    Assumptions,
    BoundHash,
    ExperimentResultHash,
    CounterexampleOrRefutationHash,
    IndependentCheckerHash,
    HumanReviewHash,
    BarrierReviewHash,
    ReproductionHash,
    BarrierAuditHash,
}

impl ResearchEvidenceRequiredArtifact {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::VerifiedTheoremArtifact => "verified_theorem_artifact_hash",
            Self::CertificateHash => "certificate_hash",
            Self::AxiomReportHash => "axiom_report_hash",
            Self::CheckerProfileHash => "checker_profile_hash",
            Self::Assumptions => "assumptions",
            Self::BoundHash => "bound_hash",
            Self::ExperimentResultHash => "experiment_result_hash",
            Self::CounterexampleOrRefutationHash => "counterexample_or_refutation_hash",
            Self::IndependentCheckerHash => "independent_checker_hash",
            Self::HumanReviewHash => "human_review_hash",
            Self::BarrierReviewHash => "barrier_review_hash",
            Self::ReproductionHash => "reproduction_hash",
            Self::BarrierAuditHash => "barrier_audit_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchEvidenceSchemaError {
    path: String,
    kind: ResearchEvidenceSchemaErrorKind,
}

impl ResearchEvidenceSchemaError {
    fn new(path: impl Into<String>, kind: ResearchEvidenceSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ResearchEvidenceSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchEvidenceSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ResearchEvidenceSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchEvidenceSchemaErrorKind {
    JsonParse { offset: usize },
    ExpectedObject { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidApiVersion { value: String },
    InvalidHash { value: String },
    InvalidEvidenceLevel { value: String },
    InvalidEvidenceKind { value: String },
    InvalidClaimScope { value: String },
}

impl fmt::Display for ResearchEvidenceSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "json parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidEvidenceLevel { value } => {
                write!(f, "invalid evidence level `{value}`")
            }
            Self::InvalidEvidenceKind { value } => {
                write!(f, "invalid evidence kind `{value}`")
            }
            Self::InvalidClaimScope { value } => write!(f, "invalid claim scope `{value}`"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchEvidenceValidationError {
    kind: ResearchEvidenceValidationErrorKind,
}

impl ResearchEvidenceValidationError {
    fn new(kind: ResearchEvidenceValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ResearchEvidenceValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchEvidenceValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::error::Error for ResearchEvidenceValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchEvidenceValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    NonProofEvidenceCannotClaimProof {
        kind: ResearchEvidenceKind,
        claim_scope: ResearchEvidenceClaimScope,
    },
    ClaimScopeNotPermittedForLevel {
        level: ResearchEvidenceLevel,
        claim_scope: ResearchEvidenceClaimScope,
    },
    EvidenceKindNotPermittedForLevel {
        level: ResearchEvidenceLevel,
        kind: ResearchEvidenceKind,
    },
    ClaimScopeKindMismatch {
        kind: ResearchEvidenceKind,
        claim_scope: ResearchEvidenceClaimScope,
    },
    DuplicateAssumption {
        assumption_hash: String,
    },
    MissingRequiredArtifact {
        artifact: ResearchEvidenceRequiredArtifact,
        level: ResearchEvidenceLevel,
        kind: ResearchEvidenceKind,
    },
}

impl fmt::Display for ResearchEvidenceValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::NonProofEvidenceCannotClaimProof { kind, claim_scope } => write!(
                f,
                "non-proof evidence kind `{}` cannot claim `{}`",
                kind.wire(),
                claim_scope.wire()
            ),
            Self::ClaimScopeNotPermittedForLevel { level, claim_scope } => write!(
                f,
                "claim scope `{}` is not permitted for evidence level `{}`",
                claim_scope.wire(),
                level.wire()
            ),
            Self::EvidenceKindNotPermittedForLevel { level, kind } => write!(
                f,
                "evidence kind `{}` is not permitted for evidence level `{}`",
                kind.wire(),
                level.wire()
            ),
            Self::ClaimScopeKindMismatch { kind, claim_scope } => write!(
                f,
                "evidence kind `{}` cannot use claim scope `{}`",
                kind.wire(),
                claim_scope.wire()
            ),
            Self::DuplicateAssumption { assumption_hash } => {
                write!(f, "duplicate assumption `{assumption_hash}`")
            }
            Self::MissingRequiredArtifact {
                artifact,
                level,
                kind,
            } => write!(
                f,
                "evidence level `{}` kind `{}` requires `{}`",
                level.wire(),
                kind.wire(),
                artifact.wire()
            ),
        }
    }
}

pub fn parse_research_evidence(
    source: &str,
) -> Result<ResearchEvidence, ResearchEvidenceSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;

    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != RESEARCH_EVIDENCE_API_VERSION {
        return Err(ResearchEvidenceSchemaError::new(
            "$.api_version",
            ResearchEvidenceSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ResearchEvidence {
        api_version,
        evidence_key: required_string(&root, "evidence_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        formal_statement_hash: required_hash(&root, "formal_statement_hash", "$")?,
        evidence_level: parse_evidence_level_value(
            required_value(&root, "evidence_level", "$")?,
            "$.evidence_level",
        )?,
        evidence_kind: parse_evidence_kind_value(
            required_value(&root, "evidence_kind", "$")?,
            "$.evidence_kind",
        )?,
        claim_scope: parse_claim_scope_value(
            required_value(&root, "claim_scope", "$")?,
            "$.claim_scope",
        )?,
        verified_theorem_artifact_hash: optional_hash(
            &root,
            "verified_theorem_artifact_hash",
            "$",
        )?,
        certificate_hash: optional_hash(&root, "certificate_hash", "$")?,
        axiom_report_hash: optional_hash(&root, "axiom_report_hash", "$")?,
        checker_profile_hash: optional_hash(&root, "checker_profile_hash", "$")?,
        assumptions: parse_assumptions(required_value(&root, "assumptions", "$")?)?,
        bound_hash: optional_hash(&root, "bound_hash", "$")?,
        experiment_result_hash: optional_hash(&root, "experiment_result_hash", "$")?,
        counterexample_or_refutation_hash: optional_hash(
            &root,
            "counterexample_or_refutation_hash",
            "$",
        )?,
        independent_checker_hash: optional_hash(&root, "independent_checker_hash", "$")?,
        human_review_hash: optional_hash(&root, "human_review_hash", "$")?,
        barrier_review_hash: optional_hash(&root, "barrier_review_hash", "$")?,
        reproduction_hash: optional_hash(&root, "reproduction_hash", "$")?,
        model_output_hash: optional_hash(&root, "model_output_hash", "$")?,
        notebook_entry_hash: optional_hash(&root, "notebook_entry_hash", "$")?,
        barrier_audit_hash: optional_hash(&root, "barrier_audit_hash", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_research_evidence(
    evidence: &ResearchEvidence,
) -> Result<(), ResearchEvidenceValidationError> {
    require_non_empty(&evidence.evidence_key, "evidence_key")?;
    require_non_empty(&evidence.target_key, "target_key")?;

    if evidence.evidence_kind.is_non_proof_sidecar() && evidence.claim_scope.claims_proof() {
        return Err(ResearchEvidenceValidationError::new(
            ResearchEvidenceValidationErrorKind::NonProofEvidenceCannotClaimProof {
                kind: evidence.evidence_kind,
                claim_scope: evidence.claim_scope,
            },
        ));
    }

    if !evidence
        .evidence_level
        .permitted_claim_scopes()
        .contains(&evidence.claim_scope)
    {
        return Err(ResearchEvidenceValidationError::new(
            ResearchEvidenceValidationErrorKind::ClaimScopeNotPermittedForLevel {
                level: evidence.evidence_level,
                claim_scope: evidence.claim_scope,
            },
        ));
    }

    if !research_evidence_level_permits_kind(evidence.evidence_level, evidence.evidence_kind) {
        return Err(ResearchEvidenceValidationError::new(
            ResearchEvidenceValidationErrorKind::EvidenceKindNotPermittedForLevel {
                level: evidence.evidence_level,
                kind: evidence.evidence_kind,
            },
        ));
    }

    if !research_evidence_kind_permits_claim_scope(evidence.evidence_kind, evidence.claim_scope) {
        return Err(ResearchEvidenceValidationError::new(
            ResearchEvidenceValidationErrorKind::ClaimScopeKindMismatch {
                kind: evidence.evidence_kind,
                claim_scope: evidence.claim_scope,
            },
        ));
    }

    let mut assumption_hashes = BTreeSet::new();
    for assumption in &evidence.assumptions {
        if !assumption_hashes.insert(assumption.assumption_hash) {
            return Err(ResearchEvidenceValidationError::new(
                ResearchEvidenceValidationErrorKind::DuplicateAssumption {
                    assumption_hash: format_hash_string(&assumption.assumption_hash),
                },
            ));
        }
    }

    for artifact in
        research_evidence_required_artifacts(evidence.evidence_level, evidence.evidence_kind)
    {
        if !evidence_has_required_artifact(evidence, artifact) {
            return Err(ResearchEvidenceValidationError::new(
                ResearchEvidenceValidationErrorKind::MissingRequiredArtifact {
                    artifact,
                    level: evidence.evidence_level,
                    kind: evidence.evidence_kind,
                },
            ));
        }
    }

    Ok(())
}

pub const fn research_evidence_level_permitted_claim_text(
    level: ResearchEvidenceLevel,
) -> &'static str {
    level.permitted_claim_text()
}

pub fn research_evidence_required_artifacts(
    level: ResearchEvidenceLevel,
    kind: ResearchEvidenceKind,
) -> Vec<ResearchEvidenceRequiredArtifact> {
    match level {
        ResearchEvidenceLevel::E0 => match kind {
            ResearchEvidenceKind::BarrierResult => {
                vec![ResearchEvidenceRequiredArtifact::BarrierAuditHash]
            }
            _ => Vec::new(),
        },
        ResearchEvidenceLevel::E1 => match kind {
            ResearchEvidenceKind::Experiment => vec![
                ResearchEvidenceRequiredArtifact::BoundHash,
                ResearchEvidenceRequiredArtifact::ExperimentResultHash,
            ],
            ResearchEvidenceKind::Counterexample => vec![
                ResearchEvidenceRequiredArtifact::BoundHash,
                ResearchEvidenceRequiredArtifact::CounterexampleOrRefutationHash,
            ],
            _ => Vec::new(),
        },
        ResearchEvidenceLevel::E2 => vec![
            ResearchEvidenceRequiredArtifact::VerifiedTheoremArtifact,
            ResearchEvidenceRequiredArtifact::CertificateHash,
            ResearchEvidenceRequiredArtifact::AxiomReportHash,
            ResearchEvidenceRequiredArtifact::CheckerProfileHash,
            ResearchEvidenceRequiredArtifact::BoundHash,
        ],
        ResearchEvidenceLevel::E3 => vec![
            ResearchEvidenceRequiredArtifact::VerifiedTheoremArtifact,
            ResearchEvidenceRequiredArtifact::CertificateHash,
            ResearchEvidenceRequiredArtifact::AxiomReportHash,
            ResearchEvidenceRequiredArtifact::CheckerProfileHash,
            ResearchEvidenceRequiredArtifact::Assumptions,
        ],
        ResearchEvidenceLevel::E4 => {
            let mut artifacts = vec![
                ResearchEvidenceRequiredArtifact::VerifiedTheoremArtifact,
                ResearchEvidenceRequiredArtifact::CertificateHash,
                ResearchEvidenceRequiredArtifact::AxiomReportHash,
                ResearchEvidenceRequiredArtifact::CheckerProfileHash,
            ];
            if kind == ResearchEvidenceKind::Refutation {
                artifacts.push(ResearchEvidenceRequiredArtifact::CounterexampleOrRefutationHash);
            }
            artifacts
        }
        ResearchEvidenceLevel::E5 => {
            let mut artifacts = vec![
                ResearchEvidenceRequiredArtifact::VerifiedTheoremArtifact,
                ResearchEvidenceRequiredArtifact::CertificateHash,
                ResearchEvidenceRequiredArtifact::AxiomReportHash,
                ResearchEvidenceRequiredArtifact::CheckerProfileHash,
                ResearchEvidenceRequiredArtifact::IndependentCheckerHash,
                ResearchEvidenceRequiredArtifact::HumanReviewHash,
                ResearchEvidenceRequiredArtifact::BarrierReviewHash,
                ResearchEvidenceRequiredArtifact::ReproductionHash,
            ];
            if kind == ResearchEvidenceKind::Refutation {
                artifacts.push(ResearchEvidenceRequiredArtifact::CounterexampleOrRefutationHash);
            }
            artifacts
        }
    }
}

pub fn research_evidence_level_permits_kind(
    level: ResearchEvidenceLevel,
    kind: ResearchEvidenceKind,
) -> bool {
    match level {
        ResearchEvidenceLevel::E0 => matches!(
            kind,
            ResearchEvidenceKind::Heuristic
                | ResearchEvidenceKind::BarrierResult
                | ResearchEvidenceKind::OpenBlocker
        ),
        ResearchEvidenceLevel::E1 => {
            matches!(
                kind,
                ResearchEvidenceKind::Experiment | ResearchEvidenceKind::Counterexample
            )
        }
        ResearchEvidenceLevel::E2 => {
            matches!(
                kind,
                ResearchEvidenceKind::FiniteCase | ResearchEvidenceKind::SpecialCase
            )
        }
        ResearchEvidenceLevel::E3 => kind == ResearchEvidenceKind::ConditionalProof,
        ResearchEvidenceLevel::E4 | ResearchEvidenceLevel::E5 => {
            matches!(
                kind,
                ResearchEvidenceKind::Proof | ResearchEvidenceKind::Refutation
            )
        }
    }
}

pub fn research_evidence_kind_permits_claim_scope(
    kind: ResearchEvidenceKind,
    claim_scope: ResearchEvidenceClaimScope,
) -> bool {
    match kind {
        ResearchEvidenceKind::Proof => matches!(
            claim_scope,
            ResearchEvidenceClaimScope::GeneralProof
                | ResearchEvidenceClaimScope::TerminalResolution
        ),
        ResearchEvidenceKind::ConditionalProof => {
            claim_scope == ResearchEvidenceClaimScope::ConditionalTheorem
        }
        ResearchEvidenceKind::FiniteCase => {
            claim_scope == ResearchEvidenceClaimScope::FiniteCaseTheorem
        }
        ResearchEvidenceKind::SpecialCase => {
            claim_scope == ResearchEvidenceClaimScope::SpecialCaseTheorem
        }
        ResearchEvidenceKind::Counterexample | ResearchEvidenceKind::Experiment => {
            claim_scope == ResearchEvidenceClaimScope::BoundedObservation
        }
        ResearchEvidenceKind::Refutation => matches!(
            claim_scope,
            ResearchEvidenceClaimScope::GeneralRefutation
                | ResearchEvidenceClaimScope::TerminalRefutation
        ),
        ResearchEvidenceKind::Heuristic
        | ResearchEvidenceKind::BarrierResult
        | ResearchEvidenceKind::OpenBlocker => {
            claim_scope == ResearchEvidenceClaimScope::NoProofClaim
        }
    }
}

pub fn research_evidence_canonical_identity_bytes(evidence: &ResearchEvidence) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, RESEARCH_EVIDENCE_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &evidence.api_version);
    encode_string_to(&mut out, "evidence_key");
    encode_string_to(&mut out, &evidence.evidence_key);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &evidence.target_key);
    encode_string_to(&mut out, "formal_statement_hash");
    encode_hash_to(&mut out, &evidence.formal_statement_hash);
    encode_string_to(&mut out, "evidence_level");
    encode_string_to(&mut out, evidence.evidence_level.wire());
    encode_string_to(&mut out, "evidence_kind");
    encode_string_to(&mut out, evidence.evidence_kind.wire());
    encode_string_to(&mut out, "claim_scope");
    encode_string_to(&mut out, evidence.claim_scope.wire());
    encode_option_hash_to(
        &mut out,
        "verified_theorem_artifact_hash",
        evidence.verified_theorem_artifact_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "certificate_hash",
        evidence.certificate_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "axiom_report_hash",
        evidence.axiom_report_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "checker_profile_hash",
        evidence.checker_profile_hash.as_ref(),
    );
    encode_string_to(&mut out, "assumptions");
    let mut assumptions = evidence.assumptions.clone();
    assumptions.sort_by_key(|assumption| (assumption.assumption_hash, assumption.disclosure_hash));
    encode_len_to(&mut out, assumptions.len());
    for assumption in &assumptions {
        encode_assumption_to(&mut out, assumption);
    }
    encode_option_hash_to(&mut out, "bound_hash", evidence.bound_hash.as_ref());
    encode_option_hash_to(
        &mut out,
        "experiment_result_hash",
        evidence.experiment_result_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "counterexample_or_refutation_hash",
        evidence.counterexample_or_refutation_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "independent_checker_hash",
        evidence.independent_checker_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "human_review_hash",
        evidence.human_review_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "barrier_review_hash",
        evidence.barrier_review_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "reproduction_hash",
        evidence.reproduction_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "model_output_hash",
        evidence.model_output_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "notebook_entry_hash",
        evidence.notebook_entry_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "barrier_audit_hash",
        evidence.barrier_audit_hash.as_ref(),
    );
    out
}

pub fn research_evidence_hash(evidence: &ResearchEvidence) -> Hash {
    let digest = Sha256::digest(research_evidence_canonical_identity_bytes(evidence));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn research_evidence_hash_string(evidence: &ResearchEvidence) -> String {
    format_hash_string(&research_evidence_hash(evidence))
}

fn evidence_has_required_artifact(
    evidence: &ResearchEvidence,
    artifact: ResearchEvidenceRequiredArtifact,
) -> bool {
    match artifact {
        ResearchEvidenceRequiredArtifact::VerifiedTheoremArtifact => {
            evidence.verified_theorem_artifact_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::CertificateHash => evidence.certificate_hash.is_some(),
        ResearchEvidenceRequiredArtifact::AxiomReportHash => evidence.axiom_report_hash.is_some(),
        ResearchEvidenceRequiredArtifact::CheckerProfileHash => {
            evidence.checker_profile_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::Assumptions => !evidence.assumptions.is_empty(),
        ResearchEvidenceRequiredArtifact::BoundHash => evidence.bound_hash.is_some(),
        ResearchEvidenceRequiredArtifact::ExperimentResultHash => {
            evidence.experiment_result_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::CounterexampleOrRefutationHash => {
            evidence.counterexample_or_refutation_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::IndependentCheckerHash => {
            evidence.independent_checker_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::HumanReviewHash => evidence.human_review_hash.is_some(),
        ResearchEvidenceRequiredArtifact::BarrierReviewHash => {
            evidence.barrier_review_hash.is_some()
        }
        ResearchEvidenceRequiredArtifact::ReproductionHash => evidence.reproduction_hash.is_some(),
        ResearchEvidenceRequiredArtifact::BarrierAuditHash => evidence.barrier_audit_hash.is_some(),
    }
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ResearchEvidenceValidationError> {
    if value.trim().is_empty() {
        return Err(ResearchEvidenceValidationError::new(
            ResearchEvidenceValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn parse_assumptions(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchEvidenceAssumption>, ResearchEvidenceSchemaError> {
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
) -> Result<ResearchEvidenceAssumption, ResearchEvidenceSchemaError> {
    let members = object_map(value, path, ASSUMPTION_FIELDS)?;
    Ok(ResearchEvidenceAssumption {
        assumption_hash: required_hash(&members, "assumption_hash", path)?,
        disclosure_hash: required_hash(&members, "disclosure_hash", path)?,
    })
}

fn parse_evidence_level_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchEvidenceLevel, ResearchEvidenceSchemaError> {
    let wire = string_value(value, path)?;
    ResearchEvidenceLevel::parse(&wire).ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::InvalidEvidenceLevel { value: wire },
        )
    })
}

fn parse_evidence_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchEvidenceKind, ResearchEvidenceSchemaError> {
    let wire = string_value(value, path)?;
    ResearchEvidenceKind::parse(&wire).ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::InvalidEvidenceKind { value: wire },
        )
    })
}

fn parse_claim_scope_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchEvidenceClaimScope, ResearchEvidenceSchemaError> {
    let wire = string_value(value, path)?;
    ResearchEvidenceClaimScope::parse(&wire).ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::InvalidClaimScope { value: wire },
        )
    })
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ResearchEvidenceSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ResearchEvidenceSchemaError::new(
            "$",
            ResearchEvidenceSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ResearchEvidenceSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ResearchEvidenceSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchEvidenceSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ResearchEvidenceSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchEvidenceSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ResearchEvidenceSchemaError> {
    value.array_elements().ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ResearchEvidenceSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            format!("{path}.{field}"),
            ResearchEvidenceSchemaErrorKind::MissingField { field },
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
) -> Result<String, ResearchEvidenceSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ResearchEvidenceSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ResearchEvidenceSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ResearchEvidenceSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ResearchEvidenceSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ResearchEvidenceSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ResearchEvidenceSchemaError::new(
            path,
            ResearchEvidenceSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn encode_assumption_to(out: &mut Vec<u8>, assumption: &ResearchEvidenceAssumption) {
    encode_string_to(out, "assumption_hash");
    encode_hash_to(out, &assumption.assumption_hash);
    encode_string_to(out, "disclosure_hash");
    encode_hash_to(out, &assumption.disclosure_hash);
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
            .join("testdata/proof-using-agents/fixtures/pua-m16-research-evidence")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("research evidence fixture should exist")
    }

    fn parse_fixture(name: &str) -> ResearchEvidence {
        parse_research_evidence(&fixture(name)).expect("fixture should parse")
    }

    fn validate_fixture(name: &str) -> Result<(), ResearchEvidenceValidationErrorKind> {
        validate_research_evidence(&parse_fixture(name)).map_err(|error| error.kind().clone())
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    #[test]
    fn research_evidence_taxonomy() {
        assert_eq!(
            research_evidence_level_permitted_claim_text(ResearchEvidenceLevel::E0),
            "no proof claim"
        );
        assert_eq!(
            ResearchEvidenceLevel::E5.permitted_claim_scopes(),
            E5_CLAIMS
        );
        assert!(research_evidence_level_permits_kind(
            ResearchEvidenceLevel::E2,
            ResearchEvidenceKind::FiniteCase
        ));
        assert!(!research_evidence_level_permits_kind(
            ResearchEvidenceLevel::E2,
            ResearchEvidenceKind::Experiment
        ));
        assert!(research_evidence_kind_permits_claim_scope(
            ResearchEvidenceKind::Refutation,
            ResearchEvidenceClaimScope::TerminalRefutation
        ));

        validate_fixture("heuristic-e0-evidence.json")
            .expect("E0 heuristic should validate only as non-proof evidence");
        validate_fixture("barrier-result-e0-evidence.json")
            .expect("E0 barrier result should validate only as non-proof evidence");
        validate_fixture("open-blocker-e0-evidence.json")
            .expect("E0 open blocker should validate only as non-proof evidence");
        validate_fixture("bounded-experiment-e1-evidence.json")
            .expect("E1 bounded experiment should validate as non-proof evidence");
        validate_fixture("bounded-counterexample-e1-evidence.json")
            .expect("E1 counterexample should validate as bounded evidence");
        validate_fixture("finite-case-e2-evidence.json")
            .expect("E2 finite case should reference a checked theorem artifact");
        validate_fixture("special-case-e2-evidence.json")
            .expect("E2 special case should reference a checked theorem artifact");
        validate_fixture("conditional-proof-e3-evidence.json")
            .expect("E3 conditional proof should include assumptions");
        validate_fixture("refutation-e4-evidence.json")
            .expect("E4 refutation should reference checked refutation evidence");
        validate_fixture("resolution-e5-evidence.json")
            .expect("E5 resolution should include independent review artifacts");

        let conditional = parse_fixture("conditional-proof-e3-evidence.json");
        let mut assumption_changed = conditional.clone();
        assumption_changed.assumptions[0].assumption_hash = hash(0x91);
        assert_ne!(
            research_evidence_hash(&conditional),
            research_evidence_hash(&assumption_changed)
        );

        let mut axiom_changed = conditional.clone();
        axiom_changed.axiom_report_hash = Some(hash(0x92));
        assert_ne!(
            research_evidence_hash(&conditional),
            research_evidence_hash(&axiom_changed)
        );

        let mut certificate_changed = conditional.clone();
        certificate_changed.certificate_hash = Some(hash(0x93));
        assert_ne!(
            research_evidence_hash(&conditional),
            research_evidence_hash(&certificate_changed)
        );

        let mut checker_changed = conditional.clone();
        checker_changed.checker_profile_hash = Some(hash(0x94));
        assert_ne!(
            research_evidence_hash(&conditional),
            research_evidence_hash(&checker_changed)
        );

        let finite = parse_fixture("finite-case-e2-evidence.json");
        let mut bound_changed = finite.clone();
        bound_changed.bound_hash = Some(hash(0x95));
        assert_ne!(
            research_evidence_hash(&finite),
            research_evidence_hash(&bound_changed)
        );

        let experiment = parse_fixture("bounded-experiment-e1-evidence.json");
        let mut experiment_changed = experiment.clone();
        experiment_changed.experiment_result_hash = Some(hash(0x96));
        assert_ne!(
            research_evidence_hash(&experiment),
            research_evidence_hash(&experiment_changed)
        );

        let mut display_changed = conditional.clone();
        display_changed.display_text = Some("display-only text".to_owned());
        assert_eq!(
            research_evidence_hash(&conditional),
            research_evidence_hash(&display_changed)
        );
    }

    #[test]
    fn research_evidence_rejects_experiment_as_proof() {
        for fixture_name in [
            "experiment-as-proof.json",
            "heuristic-as-proof.json",
            "bounded-search-as-proof.json",
            "model-output-as-proof.json",
            "barrier-result-as-proof.json",
            "notebook-note-as-proof.json",
        ] {
            assert!(
                matches!(
                    validate_fixture(fixture_name),
                    Err(
                        ResearchEvidenceValidationErrorKind::NonProofEvidenceCannotClaimProof { .. }
                    )
                ),
                "{fixture_name} should reject non-proof proof claims"
            );
        }
    }

    #[test]
    fn conditional_evidence_requires_assumptions() {
        assert!(matches!(
            validate_fixture("conditional-without-assumptions.json"),
            Err(
                ResearchEvidenceValidationErrorKind::MissingRequiredArtifact {
                    artifact: ResearchEvidenceRequiredArtifact::Assumptions,
                    level: ResearchEvidenceLevel::E3,
                    kind: ResearchEvidenceKind::ConditionalProof,
                }
            )
        ));
    }
}

use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const RESEARCH_NOTEBOOK_ENTRY_API_VERSION: &str = "npa.research-notebook-entry.v1";
pub const RESEARCH_NOTEBOOK_ENTRY_HASH_DOMAIN: &str = "npa.research-notebook-entry.identity.v1";
pub const DEAD_END_LEDGER_RECORD_API_VERSION: &str = "npa.dead-end-ledger-record.v1";
pub const DEAD_END_LEDGER_RECORD_HASH_DOMAIN: &str = "npa.dead-end-ledger-record.identity.v1";

const NOTEBOOK_ROOT_FIELDS: &[&str] = &[
    "api_version",
    "entry_key",
    "target_key",
    "event_index",
    "entry_kind",
    "route_hash",
    "attempt_hash",
    "dependency_hashes",
    "certificate_references",
    "barrier_classification",
    "counterexample_hash",
    "missing_assumption_hash",
    "needed_theorem_statement_hash",
    "bottleneck_hash",
    "representation_problem_hash",
    "payload_hash",
    "redaction_status",
    "reviewer_outcome",
    "wall_clock_time",
    "claims_proof",
    "creates_evidence_record",
    "creates_verified_artifact",
    "releases_proof_dependency",
    "claim_gate_success",
    "display_text",
];
const DEAD_END_ROOT_FIELDS: &[&str] = &[
    "api_version",
    "record_key",
    "target_key",
    "formal_statement_hash",
    "route_hash",
    "blocker_kind",
    "supporting_notebook_entry_hash",
    "dependency_hashes",
    "redaction_status",
    "review_status",
    "suppression_policy",
    "searchable_terms_hash",
    "blocks_valid_proof_task_with_new_evidence",
    "creates_proof_evidence",
    "creates_verified_artifact",
    "releases_proof_dependency",
    "claim_gate_success",
    "display_text",
];
const DEPENDENCY_FIELDS: &[&str] = &["dependency_key", "recorded_hash", "current_hash"];
const CERTIFICATE_REFERENCE_FIELDS: &[&str] = &[
    "certificate_hash",
    "source_free_reproduction_hash",
    "checker_profile_hash",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchNotebookEntry {
    pub api_version: String,
    pub entry_key: String,
    pub target_key: String,
    pub event_index: u64,
    pub entry_kind: ResearchNotebookEntryKind,
    pub route_hash: Option<Hash>,
    pub attempt_hash: Option<Hash>,
    pub dependency_hashes: Vec<ResearchNotebookDependencyReference>,
    pub certificate_references: Vec<ResearchNotebookCertificateReference>,
    pub barrier_classification: Option<ResearchNotebookBarrierClassification>,
    pub counterexample_hash: Option<Hash>,
    pub missing_assumption_hash: Option<Hash>,
    pub needed_theorem_statement_hash: Option<Hash>,
    pub bottleneck_hash: Option<Hash>,
    pub representation_problem_hash: Option<Hash>,
    pub payload_hash: Hash,
    pub redaction_status: ResearchNotebookRedactionStatus,
    pub reviewer_outcome: ResearchNotebookReviewerOutcome,
    pub wall_clock_time: Option<String>,
    pub claims_proof: bool,
    pub creates_evidence_record: bool,
    pub creates_verified_artifact: bool,
    pub releases_proof_dependency: bool,
    pub claim_gate_success: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchNotebookDependencyReference {
    pub dependency_key: String,
    pub recorded_hash: Hash,
    pub current_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchNotebookCertificateReference {
    pub certificate_hash: Hash,
    pub source_free_reproduction_hash: Hash,
    pub checker_profile_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeadEndLedgerRecord {
    pub api_version: String,
    pub record_key: String,
    pub target_key: String,
    pub formal_statement_hash: Hash,
    pub route_hash: Hash,
    pub blocker_kind: DeadEndBlockerKind,
    pub supporting_notebook_entry_hash: Hash,
    pub dependency_hashes: Vec<ResearchNotebookDependencyReference>,
    pub redaction_status: ResearchNotebookRedactionStatus,
    pub review_status: DeadEndReviewStatus,
    pub suppression_policy: DeadEndSuppressionPolicy,
    pub searchable_terms_hash: Hash,
    pub blocks_valid_proof_task_with_new_evidence: bool,
    pub creates_proof_evidence: bool,
    pub creates_verified_artifact: bool,
    pub releases_proof_dependency: bool,
    pub claim_gate_success: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchNotebookEntryKind {
    Attempt,
    FailedProofSkeleton,
    RepairAttempt,
    DependencyHashRecord,
    CertificateReference,
    BarrierClassification,
    MinimalCounterexample,
    MissingAssumption,
    NeededTheorem,
    ComputationalBottleneck,
    RepresentationProblem,
    WeeklyReviewOutcome,
}

impl ResearchNotebookEntryKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Attempt => "attempt",
            Self::FailedProofSkeleton => "failed_proof_skeleton",
            Self::RepairAttempt => "repair_attempt",
            Self::DependencyHashRecord => "dependency_hash_record",
            Self::CertificateReference => "certificate_reference",
            Self::BarrierClassification => "barrier_classification",
            Self::MinimalCounterexample => "minimal_counterexample",
            Self::MissingAssumption => "missing_assumption",
            Self::NeededTheorem => "needed_theorem",
            Self::ComputationalBottleneck => "computational_bottleneck",
            Self::RepresentationProblem => "representation_problem",
            Self::WeeklyReviewOutcome => "weekly_review_outcome",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "attempt" => Some(Self::Attempt),
            "failed_proof_skeleton" => Some(Self::FailedProofSkeleton),
            "repair_attempt" => Some(Self::RepairAttempt),
            "dependency_hash_record" => Some(Self::DependencyHashRecord),
            "certificate_reference" => Some(Self::CertificateReference),
            "barrier_classification" => Some(Self::BarrierClassification),
            "minimal_counterexample" => Some(Self::MinimalCounterexample),
            "missing_assumption" => Some(Self::MissingAssumption),
            "needed_theorem" => Some(Self::NeededTheorem),
            "computational_bottleneck" => Some(Self::ComputationalBottleneck),
            "representation_problem" => Some(Self::RepresentationProblem),
            "weekly_review_outcome" => Some(Self::WeeklyReviewOutcome),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchNotebookBarrierClassification {
    NotDetected,
    Possible,
    Likely,
    Confirmed,
    NotApplicable,
}

impl ResearchNotebookBarrierClassification {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::NotDetected => "not_detected",
            Self::Possible => "possible",
            Self::Likely => "likely",
            Self::Confirmed => "confirmed",
            Self::NotApplicable => "not_applicable",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "not_detected" => Some(Self::NotDetected),
            "possible" => Some(Self::Possible),
            "likely" => Some(Self::Likely),
            "confirmed" => Some(Self::Confirmed),
            "not_applicable" => Some(Self::NotApplicable),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchNotebookRedactionStatus {
    ReviewedRedacted,
    ReviewedNoSensitiveContent,
    Missing,
}

impl ResearchNotebookRedactionStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ReviewedRedacted => "reviewed_redacted",
            Self::ReviewedNoSensitiveContent => "reviewed_no_sensitive_content",
            Self::Missing => "missing",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "reviewed_redacted" => Some(Self::ReviewedRedacted),
            "reviewed_no_sensitive_content" => Some(Self::ReviewedNoSensitiveContent),
            "missing" => Some(Self::Missing),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchNotebookReviewerOutcome {
    NeedsReview,
    Reviewed,
    Rejected,
}

impl ResearchNotebookReviewerOutcome {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::NeedsReview => "needs_review",
            Self::Reviewed => "reviewed",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "needs_review" => Some(Self::NeedsReview),
            "reviewed" => Some(Self::Reviewed),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeadEndBlockerKind {
    MissingAssumption,
    NeededTheorem,
    ComputationalBottleneck,
    RepresentationProblem,
    BarrierBlocker,
    CheckedCounterexample,
    StaleDependency,
    FailedProofSkeleton,
}

impl DeadEndBlockerKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::MissingAssumption => "missing_assumption",
            Self::NeededTheorem => "needed_theorem",
            Self::ComputationalBottleneck => "computational_bottleneck",
            Self::RepresentationProblem => "representation_problem",
            Self::BarrierBlocker => "barrier_blocker",
            Self::CheckedCounterexample => "checked_counterexample",
            Self::StaleDependency => "stale_dependency",
            Self::FailedProofSkeleton => "failed_proof_skeleton",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "missing_assumption" => Some(Self::MissingAssumption),
            "needed_theorem" => Some(Self::NeededTheorem),
            "computational_bottleneck" => Some(Self::ComputationalBottleneck),
            "representation_problem" => Some(Self::RepresentationProblem),
            "barrier_blocker" => Some(Self::BarrierBlocker),
            "checked_counterexample" => Some(Self::CheckedCounterexample),
            "stale_dependency" => Some(Self::StaleDependency),
            "failed_proof_skeleton" => Some(Self::FailedProofSkeleton),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeadEndReviewStatus {
    Pending,
    BlockerReviewed,
    Rejected,
}

impl DeadEndReviewStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::BlockerReviewed => "blocker_reviewed",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "pending" => Some(Self::Pending),
            "blocker_reviewed" => Some(Self::BlockerReviewed),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeadEndSuppressionPolicy {
    None,
    SuppressExactRepeatedRoute,
}

impl DeadEndSuppressionPolicy {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::SuppressExactRepeatedRoute => "suppress_exact_repeated_route",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "none" => Some(Self::None),
            "suppress_exact_repeated_route" => Some(Self::SuppressExactRepeatedRoute),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchNotebookSchemaError {
    path: String,
    kind: ResearchNotebookSchemaErrorKind,
}

impl ResearchNotebookSchemaError {
    fn new(path: impl Into<String>, kind: ResearchNotebookSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &ResearchNotebookSchemaErrorKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchNotebookSchemaErrorKind {
    JsonParse { offset: usize },
    InvalidApiVersion { value: String },
    ExpectedObject { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    ExpectedInteger { actual: JsonValueKind },
    InvalidInteger { value: String },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidHash { value: String },
    InvalidEntryKind { value: String },
    InvalidBarrierClassification { value: String },
    InvalidRedactionStatus { value: String },
    InvalidReviewerOutcome { value: String },
    InvalidBlockerKind { value: String },
    InvalidDeadEndReviewStatus { value: String },
    InvalidSuppressionPolicy { value: String },
}

impl fmt::Display for ResearchNotebookSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "research notebook schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for ResearchNotebookSchemaError {}

impl fmt::Display for ResearchNotebookSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "invalid JSON at byte offset {offset}"),
            Self::InvalidApiVersion { value } => {
                write!(f, "invalid research notebook api_version `{value}`")
            }
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedInteger { actual } => write!(f, "expected integer, found {actual:?}"),
            Self::InvalidInteger { value } => write!(f, "invalid integer `{value}`"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidEntryKind { value } => write!(f, "invalid notebook entry kind `{value}`"),
            Self::InvalidBarrierClassification { value } => {
                write!(f, "invalid barrier classification `{value}`")
            }
            Self::InvalidRedactionStatus { value } => {
                write!(f, "invalid redaction status `{value}`")
            }
            Self::InvalidReviewerOutcome { value } => {
                write!(f, "invalid reviewer outcome `{value}`")
            }
            Self::InvalidBlockerKind { value } => write!(f, "invalid blocker kind `{value}`"),
            Self::InvalidDeadEndReviewStatus { value } => {
                write!(f, "invalid dead-end review status `{value}`")
            }
            Self::InvalidSuppressionPolicy { value } => {
                write!(f, "invalid suppression policy `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchNotebookValidationError {
    kind: ResearchNotebookValidationErrorKind,
}

impl ResearchNotebookValidationError {
    fn new(kind: ResearchNotebookValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &ResearchNotebookValidationErrorKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchNotebookValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    MissingRedactionReview,
    NotebookCannotClaimProof,
    NotebookCannotCreateEvidenceRecord,
    NotebookCannotCreateVerifiedArtifact,
    NotebookCannotReleaseProofDependency,
    NotebookCannotSatisfyClaimGate,
    DuplicateDependencyReference {
        dependency_key: String,
    },
    StaleDependencyHash {
        dependency_key: String,
        recorded_hash: String,
        current_hash: String,
    },
    CertificateReferenceRequiresSourceFreeReproduction,
    EntryKindRequiresCertificateReference,
    EntryKindRequiresBarrierClassification,
    EntryKindRequiresCounterexampleHash,
    EntryKindRequiresMissingAssumptionHash,
    EntryKindRequiresNeededTheoremHash,
    EntryKindRequiresBottleneckHash,
    EntryKindRequiresRepresentationProblemHash,
    DeadEndCannotSuppressWithoutBlockerReview,
    DeadEndCannotBlockValidProofTask,
    DeadEndCannotCreateProofEvidence,
    DeadEndCannotCreateVerifiedArtifact,
    DeadEndCannotReleaseProofDependency,
    DeadEndCannotSatisfyClaimGate,
}

impl fmt::Display for ResearchNotebookValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "research notebook validation error: {}", self.kind)
    }
}

impl std::error::Error for ResearchNotebookValidationError {}

impl fmt::Display for ResearchNotebookValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::MissingRedactionReview => write!(f, "redaction review is missing"),
            Self::NotebookCannotClaimProof => write!(f, "notebook entry cannot claim proof"),
            Self::NotebookCannotCreateEvidenceRecord => {
                write!(f, "notebook entry cannot create evidence records")
            }
            Self::NotebookCannotCreateVerifiedArtifact => {
                write!(f, "notebook entry cannot create verified artifacts")
            }
            Self::NotebookCannotReleaseProofDependency => {
                write!(f, "notebook entry cannot release proof dependencies")
            }
            Self::NotebookCannotSatisfyClaimGate => {
                write!(f, "notebook entry cannot satisfy a claim gate")
            }
            Self::DuplicateDependencyReference { dependency_key } => {
                write!(f, "duplicate dependency reference `{dependency_key}`")
            }
            Self::StaleDependencyHash {
                dependency_key,
                recorded_hash,
                current_hash,
            } => write!(
                f,
                "dependency `{dependency_key}` recorded hash `{recorded_hash}` does not match current hash `{current_hash}`"
            ),
            Self::CertificateReferenceRequiresSourceFreeReproduction => write!(
                f,
                "certificate references require source-free reproduction and checker-profile hashes"
            ),
            Self::EntryKindRequiresCertificateReference => {
                write!(f, "certificate_reference entry requires certificate reference")
            }
            Self::EntryKindRequiresBarrierClassification => {
                write!(f, "barrier_classification entry requires barrier classification")
            }
            Self::EntryKindRequiresCounterexampleHash => {
                write!(f, "minimal_counterexample entry requires counterexample hash")
            }
            Self::EntryKindRequiresMissingAssumptionHash => {
                write!(f, "missing_assumption entry requires missing assumption hash")
            }
            Self::EntryKindRequiresNeededTheoremHash => {
                write!(f, "needed_theorem entry requires theorem statement hash")
            }
            Self::EntryKindRequiresBottleneckHash => {
                write!(f, "computational_bottleneck entry requires bottleneck hash")
            }
            Self::EntryKindRequiresRepresentationProblemHash => {
                write!(f, "representation_problem entry requires representation problem hash")
            }
            Self::DeadEndCannotSuppressWithoutBlockerReview => write!(
                f,
                "dead-end suppression requires recorded blocker review"
            ),
            Self::DeadEndCannotBlockValidProofTask => {
                write!(f, "dead-end record cannot block a valid proof task")
            }
            Self::DeadEndCannotCreateProofEvidence => {
                write!(f, "dead-end record cannot create proof evidence")
            }
            Self::DeadEndCannotCreateVerifiedArtifact => {
                write!(f, "dead-end record cannot create verified artifacts")
            }
            Self::DeadEndCannotReleaseProofDependency => {
                write!(f, "dead-end record cannot release proof dependencies")
            }
            Self::DeadEndCannotSatisfyClaimGate => {
                write!(f, "dead-end record cannot satisfy a claim gate")
            }
        }
    }
}

pub fn parse_research_notebook_entry(
    source: &str,
) -> Result<ResearchNotebookEntry, ResearchNotebookSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", NOTEBOOK_ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != RESEARCH_NOTEBOOK_ENTRY_API_VERSION {
        return Err(ResearchNotebookSchemaError::new(
            "$.api_version",
            ResearchNotebookSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ResearchNotebookEntry {
        api_version,
        entry_key: required_string(&root, "entry_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        event_index: required_u64(&root, "event_index", "$")?,
        entry_kind: parse_entry_kind_value(
            required_value(&root, "entry_kind", "$")?,
            "$.entry_kind",
        )?,
        route_hash: optional_hash(&root, "route_hash", "$")?,
        attempt_hash: optional_hash(&root, "attempt_hash", "$")?,
        dependency_hashes: parse_dependencies(required_value(&root, "dependency_hashes", "$")?)?,
        certificate_references: parse_certificate_references(required_value(
            &root,
            "certificate_references",
            "$",
        )?)?,
        barrier_classification: optional_barrier_classification(
            &root,
            "barrier_classification",
            "$",
        )?,
        counterexample_hash: optional_hash(&root, "counterexample_hash", "$")?,
        missing_assumption_hash: optional_hash(&root, "missing_assumption_hash", "$")?,
        needed_theorem_statement_hash: optional_hash(&root, "needed_theorem_statement_hash", "$")?,
        bottleneck_hash: optional_hash(&root, "bottleneck_hash", "$")?,
        representation_problem_hash: optional_hash(&root, "representation_problem_hash", "$")?,
        payload_hash: required_hash(&root, "payload_hash", "$")?,
        redaction_status: parse_redaction_status_value(
            required_value(&root, "redaction_status", "$")?,
            "$.redaction_status",
        )?,
        reviewer_outcome: parse_reviewer_outcome_value(
            required_value(&root, "reviewer_outcome", "$")?,
            "$.reviewer_outcome",
        )?,
        wall_clock_time: optional_string(&root, "wall_clock_time", "$")?,
        claims_proof: required_bool(&root, "claims_proof", "$")?,
        creates_evidence_record: required_bool(&root, "creates_evidence_record", "$")?,
        creates_verified_artifact: required_bool(&root, "creates_verified_artifact", "$")?,
        releases_proof_dependency: required_bool(&root, "releases_proof_dependency", "$")?,
        claim_gate_success: required_bool(&root, "claim_gate_success", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn parse_dead_end_ledger_record(
    source: &str,
) -> Result<DeadEndLedgerRecord, ResearchNotebookSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", DEAD_END_ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != DEAD_END_LEDGER_RECORD_API_VERSION {
        return Err(ResearchNotebookSchemaError::new(
            "$.api_version",
            ResearchNotebookSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(DeadEndLedgerRecord {
        api_version,
        record_key: required_string(&root, "record_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        formal_statement_hash: required_hash(&root, "formal_statement_hash", "$")?,
        route_hash: required_hash(&root, "route_hash", "$")?,
        blocker_kind: parse_blocker_kind_value(
            required_value(&root, "blocker_kind", "$")?,
            "$.blocker_kind",
        )?,
        supporting_notebook_entry_hash: required_hash(
            &root,
            "supporting_notebook_entry_hash",
            "$",
        )?,
        dependency_hashes: parse_dependencies(required_value(&root, "dependency_hashes", "$")?)?,
        redaction_status: parse_redaction_status_value(
            required_value(&root, "redaction_status", "$")?,
            "$.redaction_status",
        )?,
        review_status: parse_dead_end_review_status_value(
            required_value(&root, "review_status", "$")?,
            "$.review_status",
        )?,
        suppression_policy: parse_suppression_policy_value(
            required_value(&root, "suppression_policy", "$")?,
            "$.suppression_policy",
        )?,
        searchable_terms_hash: required_hash(&root, "searchable_terms_hash", "$")?,
        blocks_valid_proof_task_with_new_evidence: required_bool(
            &root,
            "blocks_valid_proof_task_with_new_evidence",
            "$",
        )?,
        creates_proof_evidence: required_bool(&root, "creates_proof_evidence", "$")?,
        creates_verified_artifact: required_bool(&root, "creates_verified_artifact", "$")?,
        releases_proof_dependency: required_bool(&root, "releases_proof_dependency", "$")?,
        claim_gate_success: required_bool(&root, "claim_gate_success", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_research_notebook_entry(
    entry: &ResearchNotebookEntry,
) -> Result<(), ResearchNotebookValidationError> {
    require_non_empty(&entry.entry_key, "entry_key")?;
    require_non_empty(&entry.target_key, "target_key")?;
    validate_redaction(entry.redaction_status)?;
    validate_notebook_output_boundary(entry)?;
    validate_dependency_hashes(&entry.dependency_hashes)?;
    validate_entry_kind_requirements(entry)?;
    Ok(())
}

pub fn validate_dead_end_ledger_record(
    record: &DeadEndLedgerRecord,
) -> Result<(), ResearchNotebookValidationError> {
    require_non_empty(&record.record_key, "record_key")?;
    require_non_empty(&record.target_key, "target_key")?;
    validate_redaction(record.redaction_status)?;
    validate_dependency_hashes(&record.dependency_hashes)?;
    if record.suppression_policy == DeadEndSuppressionPolicy::SuppressExactRepeatedRoute
        && record.review_status != DeadEndReviewStatus::BlockerReviewed
    {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotSuppressWithoutBlockerReview,
        ));
    }
    if record.blocks_valid_proof_task_with_new_evidence {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotBlockValidProofTask,
        ));
    }
    if record.creates_proof_evidence {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotCreateProofEvidence,
        ));
    }
    if record.creates_verified_artifact {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotCreateVerifiedArtifact,
        ));
    }
    if record.releases_proof_dependency {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotReleaseProofDependency,
        ));
    }
    if record.claim_gate_success {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::DeadEndCannotSatisfyClaimGate,
        ));
    }
    Ok(())
}

pub fn research_notebook_entry_canonical_identity_bytes(entry: &ResearchNotebookEntry) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, RESEARCH_NOTEBOOK_ENTRY_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &entry.api_version);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &entry.target_key);
    encode_string_to(&mut out, "event_index");
    out.extend_from_slice(&entry.event_index.to_be_bytes());
    encode_string_to(&mut out, "entry_kind");
    encode_string_to(&mut out, entry.entry_kind.wire());
    encode_option_hash_to(&mut out, "route_hash", entry.route_hash.as_ref());
    encode_option_hash_to(&mut out, "attempt_hash", entry.attempt_hash.as_ref());
    encode_dependencies_to(&mut out, &entry.dependency_hashes);
    encode_certificate_references_to(&mut out, &entry.certificate_references);
    encode_string_to(&mut out, "barrier_classification");
    match entry.barrier_classification {
        Some(classification) => {
            out.push(1);
            encode_string_to(&mut out, classification.wire());
        }
        None => out.push(0),
    }
    encode_option_hash_to(
        &mut out,
        "counterexample_hash",
        entry.counterexample_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "missing_assumption_hash",
        entry.missing_assumption_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "needed_theorem_statement_hash",
        entry.needed_theorem_statement_hash.as_ref(),
    );
    encode_option_hash_to(&mut out, "bottleneck_hash", entry.bottleneck_hash.as_ref());
    encode_option_hash_to(
        &mut out,
        "representation_problem_hash",
        entry.representation_problem_hash.as_ref(),
    );
    encode_string_to(&mut out, "payload_hash");
    encode_hash_to(&mut out, &entry.payload_hash);
    encode_string_to(&mut out, "redaction_status");
    encode_string_to(&mut out, entry.redaction_status.wire());
    encode_string_to(&mut out, "reviewer_outcome");
    encode_string_to(&mut out, entry.reviewer_outcome.wire());
    out
}

pub fn research_notebook_entry_hash(entry: &ResearchNotebookEntry) -> Hash {
    let digest = Sha256::digest(research_notebook_entry_canonical_identity_bytes(entry));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn research_notebook_entry_hash_string(entry: &ResearchNotebookEntry) -> String {
    format_hash_string(&research_notebook_entry_hash(entry))
}

pub fn dead_end_ledger_record_canonical_identity_bytes(record: &DeadEndLedgerRecord) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, DEAD_END_LEDGER_RECORD_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &record.target_key);
    encode_string_to(&mut out, "formal_statement_hash");
    encode_hash_to(&mut out, &record.formal_statement_hash);
    encode_string_to(&mut out, "route_hash");
    encode_hash_to(&mut out, &record.route_hash);
    encode_string_to(&mut out, "blocker_kind");
    encode_string_to(&mut out, record.blocker_kind.wire());
    encode_string_to(&mut out, "supporting_notebook_entry_hash");
    encode_hash_to(&mut out, &record.supporting_notebook_entry_hash);
    encode_dependencies_to(&mut out, &record.dependency_hashes);
    encode_string_to(&mut out, "redaction_status");
    encode_string_to(&mut out, record.redaction_status.wire());
    encode_string_to(&mut out, "review_status");
    encode_string_to(&mut out, record.review_status.wire());
    encode_string_to(&mut out, "suppression_policy");
    encode_string_to(&mut out, record.suppression_policy.wire());
    encode_string_to(&mut out, "searchable_terms_hash");
    encode_hash_to(&mut out, &record.searchable_terms_hash);
    out
}

pub fn dead_end_ledger_record_hash(record: &DeadEndLedgerRecord) -> Hash {
    let digest = Sha256::digest(dead_end_ledger_record_canonical_identity_bytes(record));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn dead_end_ledger_record_hash_string(record: &DeadEndLedgerRecord) -> String {
    format_hash_string(&dead_end_ledger_record_hash(record))
}

fn validate_redaction(
    redaction_status: ResearchNotebookRedactionStatus,
) -> Result<(), ResearchNotebookValidationError> {
    if redaction_status == ResearchNotebookRedactionStatus::Missing {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::MissingRedactionReview,
        ));
    }
    Ok(())
}

fn validate_notebook_output_boundary(
    entry: &ResearchNotebookEntry,
) -> Result<(), ResearchNotebookValidationError> {
    if entry.claims_proof {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::NotebookCannotClaimProof,
        ));
    }
    if entry.creates_evidence_record {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::NotebookCannotCreateEvidenceRecord,
        ));
    }
    if entry.creates_verified_artifact {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::NotebookCannotCreateVerifiedArtifact,
        ));
    }
    if entry.releases_proof_dependency {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::NotebookCannotReleaseProofDependency,
        ));
    }
    if entry.claim_gate_success {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::NotebookCannotSatisfyClaimGate,
        ));
    }
    Ok(())
}

fn validate_dependency_hashes(
    dependencies: &[ResearchNotebookDependencyReference],
) -> Result<(), ResearchNotebookValidationError> {
    let mut seen = BTreeSet::new();
    for dependency in dependencies {
        require_non_empty(
            &dependency.dependency_key,
            "dependency_hashes.dependency_key",
        )?;
        if !seen.insert(dependency.dependency_key.as_str()) {
            return Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::DuplicateDependencyReference {
                    dependency_key: dependency.dependency_key.clone(),
                },
            ));
        }
        if dependency.recorded_hash != dependency.current_hash {
            return Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::StaleDependencyHash {
                    dependency_key: dependency.dependency_key.clone(),
                    recorded_hash: format_hash_string(&dependency.recorded_hash),
                    current_hash: format_hash_string(&dependency.current_hash),
                },
            ));
        }
    }
    Ok(())
}

fn validate_entry_kind_requirements(
    entry: &ResearchNotebookEntry,
) -> Result<(), ResearchNotebookValidationError> {
    match entry.entry_kind {
        ResearchNotebookEntryKind::CertificateReference
            if entry.certificate_references.is_empty() =>
        {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresCertificateReference,
            ))
        }
        ResearchNotebookEntryKind::BarrierClassification
            if entry.barrier_classification.is_none() =>
        {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresBarrierClassification,
            ))
        }
        ResearchNotebookEntryKind::MinimalCounterexample if entry.counterexample_hash.is_none() => {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresCounterexampleHash,
            ))
        }
        ResearchNotebookEntryKind::MissingAssumption if entry.missing_assumption_hash.is_none() => {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresMissingAssumptionHash,
            ))
        }
        ResearchNotebookEntryKind::NeededTheorem
            if entry.needed_theorem_statement_hash.is_none() =>
        {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresNeededTheoremHash,
            ))
        }
        ResearchNotebookEntryKind::ComputationalBottleneck if entry.bottleneck_hash.is_none() => {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresBottleneckHash,
            ))
        }
        ResearchNotebookEntryKind::RepresentationProblem
            if entry.representation_problem_hash.is_none() =>
        {
            Err(ResearchNotebookValidationError::new(
                ResearchNotebookValidationErrorKind::EntryKindRequiresRepresentationProblemHash,
            ))
        }
        _ => Ok(()),
    }
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ResearchNotebookSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ResearchNotebookSchemaError::new(
            "$",
            ResearchNotebookSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ResearchNotebookSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ResearchNotebookSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchNotebookSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ResearchNotebookSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchNotebookSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ResearchNotebookSchemaError> {
    value.array_elements().ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ResearchNotebookSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            format!("{path}.{field}"),
            ResearchNotebookSchemaErrorKind::MissingField { field },
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
) -> Result<String, ResearchNotebookSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ResearchNotebookSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ResearchNotebookSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ResearchNotebookSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ResearchNotebookSchemaError> {
    value.bool_value().ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_u64(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<u64, ResearchNotebookSchemaError> {
    let value = required_value(members, field, path)?;
    let raw = value.number_raw().ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            format!("{path}.{field}"),
            ResearchNotebookSchemaErrorKind::ExpectedInteger {
                actual: value.kind(),
            },
        )
    })?;
    if raw.starts_with('-') || raw.contains('.') || raw.contains('e') || raw.contains('E') {
        return Err(ResearchNotebookSchemaError::new(
            format!("{path}.{field}"),
            ResearchNotebookSchemaErrorKind::InvalidInteger {
                value: raw.to_owned(),
            },
        ));
    }
    raw.parse::<u64>().map_err(|_| {
        ResearchNotebookSchemaError::new(
            format!("{path}.{field}"),
            ResearchNotebookSchemaErrorKind::InvalidInteger {
                value: raw.to_owned(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ResearchNotebookSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ResearchNotebookSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_dependencies(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchNotebookDependencyReference>, ResearchNotebookSchemaError> {
    array_elements(value, "$.dependency_hashes")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_dependency(value, &format!("$.dependency_hashes[{index}]")))
        .collect()
}

fn parse_dependency(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchNotebookDependencyReference, ResearchNotebookSchemaError> {
    let members = object_map(value, path, DEPENDENCY_FIELDS)?;
    Ok(ResearchNotebookDependencyReference {
        dependency_key: required_string(&members, "dependency_key", path)?,
        recorded_hash: required_hash(&members, "recorded_hash", path)?,
        current_hash: required_hash(&members, "current_hash", path)?,
    })
}

fn parse_certificate_references(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchNotebookCertificateReference>, ResearchNotebookSchemaError> {
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
) -> Result<ResearchNotebookCertificateReference, ResearchNotebookSchemaError> {
    let members = object_map(value, path, CERTIFICATE_REFERENCE_FIELDS)?;
    Ok(ResearchNotebookCertificateReference {
        certificate_hash: required_hash(&members, "certificate_hash", path)?,
        source_free_reproduction_hash: required_hash(
            &members,
            "source_free_reproduction_hash",
            path,
        )?,
        checker_profile_hash: required_hash(&members, "checker_profile_hash", path)?,
    })
}

fn parse_entry_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchNotebookEntryKind, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    ResearchNotebookEntryKind::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidEntryKind { value: wire },
        )
    })
}

fn optional_barrier_classification(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<ResearchNotebookBarrierClassification>, ResearchNotebookSchemaError> {
    optional_value(members, field)
        .map(|value| parse_barrier_classification_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn parse_barrier_classification_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchNotebookBarrierClassification, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    ResearchNotebookBarrierClassification::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidBarrierClassification { value: wire },
        )
    })
}

fn parse_redaction_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchNotebookRedactionStatus, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    ResearchNotebookRedactionStatus::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidRedactionStatus { value: wire },
        )
    })
}

fn parse_reviewer_outcome_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchNotebookReviewerOutcome, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    ResearchNotebookReviewerOutcome::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidReviewerOutcome { value: wire },
        )
    })
}

fn parse_blocker_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<DeadEndBlockerKind, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    DeadEndBlockerKind::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidBlockerKind { value: wire },
        )
    })
}

fn parse_dead_end_review_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<DeadEndReviewStatus, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    DeadEndReviewStatus::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidDeadEndReviewStatus { value: wire },
        )
    })
}

fn parse_suppression_policy_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<DeadEndSuppressionPolicy, ResearchNotebookSchemaError> {
    let wire = string_value(value, path)?;
    DeadEndSuppressionPolicy::parse(&wire).ok_or_else(|| {
        ResearchNotebookSchemaError::new(
            path,
            ResearchNotebookSchemaErrorKind::InvalidSuppressionPolicy { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ResearchNotebookValidationError> {
    if value.trim().is_empty() {
        return Err(ResearchNotebookValidationError::new(
            ResearchNotebookValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_dependencies_to(out: &mut Vec<u8>, dependencies: &[ResearchNotebookDependencyReference]) {
    encode_string_to(out, "dependency_hashes");
    let mut dependencies = dependencies.to_vec();
    dependencies.sort_by(|left, right| left.dependency_key.cmp(&right.dependency_key));
    encode_len_to(out, dependencies.len());
    for dependency in &dependencies {
        encode_string_to(out, &dependency.dependency_key);
        encode_hash_to(out, &dependency.recorded_hash);
        encode_hash_to(out, &dependency.current_hash);
    }
}

fn encode_certificate_references_to(
    out: &mut Vec<u8>,
    certificates: &[ResearchNotebookCertificateReference],
) {
    encode_string_to(out, "certificate_references");
    let mut certificates = certificates.to_vec();
    certificates.sort_by_key(|certificate| {
        (
            certificate.certificate_hash,
            certificate.source_free_reproduction_hash,
            certificate.checker_profile_hash,
        )
    });
    encode_len_to(out, certificates.len());
    for certificate in &certificates {
        encode_hash_to(out, &certificate.certificate_hash);
        encode_hash_to(out, &certificate.source_free_reproduction_hash);
        encode_hash_to(out, &certificate.checker_profile_hash);
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

use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const COMPLEXITY_OBLIGATION_RECORD_API_VERSION: &str = "npa.complexity-obligation-record.v1";
pub const COMPLEXITY_OBLIGATION_RECORD_HASH_DOMAIN: &str =
    "npa.complexity-obligation-record.identity.v1";

const PROOF_CORPUS_PREFIX: &str = "Proofs.Ai.";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "obligation_key",
    "subject_hash",
    "route_package_hash",
    "theorem_card_hash",
    "machine_model_hash",
    "obligation_kind",
    "statement_artifact_hash",
    "status",
    "checked_theorem_references",
    "source_free_verification_hashes",
    "encoding_audit_hashes",
    "depends_on_obligation_hashes",
    "proof_task_key",
    "blockers",
    "rejection_reason_hash",
    "uses_explicit_fuel",
    "uses_termination_evidence",
    "runtime_separated_from_correctness",
    "output_size_separated_from_correctness",
    "allows_host_timing_evidence",
    "allows_solver_counter_evidence",
    "allows_simulation_log_evidence",
    "hidden_unbounded_recursion",
    "machine_encoding_valid",
    "creates_theorem_declarations",
    "creates_verified_artifacts",
    "releases_dependencies",
    "creates_proof_acceptance",
    "wall_clock_time",
    "display_text",
];
const THEOREM_REFERENCE_FIELDS: &[&str] = &[
    "theorem_declaration",
    "statement_hash",
    "certificate_hash",
    "source_free_verification_hash",
];
const BLOCKER_FIELDS: &[&str] = &[
    "blocker_key",
    "blocker_hash",
    "reason",
    "prerequisite_task_key",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationRecord {
    pub api_version: String,
    pub obligation_key: String,
    pub subject_hash: Hash,
    pub route_package_hash: Option<Hash>,
    pub theorem_card_hash: Option<Hash>,
    pub machine_model_hash: Hash,
    pub obligation_kind: ComplexityObligationKind,
    pub statement_artifact_hash: Hash,
    pub status: ComplexityObligationStatus,
    pub checked_theorem_references: Vec<ComplexityObligationTheoremReference>,
    pub source_free_verification_hashes: Vec<Hash>,
    pub encoding_audit_hashes: Vec<Hash>,
    pub depends_on_obligation_hashes: Vec<Hash>,
    pub proof_task_key: Option<String>,
    pub blockers: Vec<ComplexityObligationBlocker>,
    pub rejection_reason_hash: Option<Hash>,
    pub uses_explicit_fuel: bool,
    pub uses_termination_evidence: bool,
    pub runtime_separated_from_correctness: bool,
    pub output_size_separated_from_correctness: bool,
    pub allows_host_timing_evidence: bool,
    pub allows_solver_counter_evidence: bool,
    pub allows_simulation_log_evidence: bool,
    pub hidden_unbounded_recursion: bool,
    pub machine_encoding_valid: bool,
    pub creates_theorem_declarations: bool,
    pub creates_verified_artifacts: bool,
    pub releases_dependencies: bool,
    pub creates_proof_acceptance: bool,
    pub wall_clock_time: Option<String>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationTheoremReference {
    pub theorem_declaration: String,
    pub statement_hash: Hash,
    pub certificate_hash: Hash,
    pub source_free_verification_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationBlocker {
    pub blocker_key: String,
    pub blocker_hash: Hash,
    pub reason: String,
    pub prerequisite_task_key: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ComplexityObligationKind {
    FunctionalCorrectness,
    WellFormedness,
    Termination,
    FuelSufficiency,
    RuntimeRecurrence,
    RuntimePolynomial,
    OutputSizeRecurrence,
    OutputSizePolynomial,
    CodecCorrectness,
    Uniformity,
}

impl ComplexityObligationKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FunctionalCorrectness => "functional_correctness",
            Self::WellFormedness => "well_formedness",
            Self::Termination => "termination",
            Self::FuelSufficiency => "fuel_sufficiency",
            Self::RuntimeRecurrence => "runtime_recurrence",
            Self::RuntimePolynomial => "runtime_polynomial",
            Self::OutputSizeRecurrence => "output_size_recurrence",
            Self::OutputSizePolynomial => "output_size_polynomial",
            Self::CodecCorrectness => "codec_correctness",
            Self::Uniformity => "uniformity",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "functional_correctness" => Some(Self::FunctionalCorrectness),
            "well_formedness" => Some(Self::WellFormedness),
            "termination" => Some(Self::Termination),
            "fuel_sufficiency" => Some(Self::FuelSufficiency),
            "runtime_recurrence" => Some(Self::RuntimeRecurrence),
            "runtime_polynomial" => Some(Self::RuntimePolynomial),
            "output_size_recurrence" => Some(Self::OutputSizeRecurrence),
            "output_size_polynomial" => Some(Self::OutputSizePolynomial),
            "codec_correctness" => Some(Self::CodecCorrectness),
            "uniformity" => Some(Self::Uniformity),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ComplexityObligationStatus {
    Open,
    TaskCreated,
    Verified,
    Rejected,
}

impl ComplexityObligationStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::TaskCreated => "task_created",
            Self::Verified => "verified",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "open" => Some(Self::Open),
            "task_created" => Some(Self::TaskCreated),
            "verified" => Some(Self::Verified),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationSchemaError {
    path: String,
    kind: ComplexityObligationSchemaErrorKind,
}

impl ComplexityObligationSchemaError {
    fn new(path: impl Into<String>, kind: ComplexityObligationSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &ComplexityObligationSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ComplexityObligationSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "complexity obligation schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for ComplexityObligationSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComplexityObligationSchemaErrorKind {
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
    InvalidObligationKind { value: String },
    InvalidStatus { value: String },
}

impl fmt::Display for ComplexityObligationSchemaErrorKind {
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
            Self::InvalidObligationKind { value } => {
                write!(f, "invalid complexity obligation kind `{value}`")
            }
            Self::InvalidStatus { value } => {
                write!(f, "invalid complexity obligation status `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationValidationError {
    kind: ComplexityObligationValidationErrorKind,
}

impl ComplexityObligationValidationError {
    fn new(kind: ComplexityObligationValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &ComplexityObligationValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ComplexityObligationValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "complexity obligation validation error: {}", self.kind)
    }
}

impl std::error::Error for ComplexityObligationValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComplexityObligationValidationErrorKind {
    EmptyRequiredField { field: &'static str },
    SidecarBoundaryViolation { field: &'static str },
    OperationalEvidenceBoundaryViolation { field: &'static str },
    HiddenUnboundedRecursion,
    InvalidMachineEncoding,
    MissingFuelOrTerminationEvidence,
    RuntimeObligationNotSeparated,
    OutputSizeObligationNotSeparated,
    MissingEvidence { field: &'static str },
    DuplicateEvidenceHash { field: &'static str, hash: String },
    MissingCheckedTheoremReference,
    DuplicateCheckedTheoremReference { theorem_declaration: String },
    CheckedTheoremOutsideProofCorpus { theorem_declaration: String },
    VerifiedObligationCannotHaveBlockers,
    VerifiedObligationCannotHaveRejection,
    OpenObligationRequiresBlockerOrTask,
    TaskCreatedRequiresProofTask,
    RejectedObligationRequiresReason,
    DuplicateBlocker { blocker_key: String },
}

impl fmt::Display for ComplexityObligationValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::SidecarBoundaryViolation { field } => {
                write!(
                    f,
                    "complexity obligation violates sidecar boundary via `{field}`"
                )
            }
            Self::OperationalEvidenceBoundaryViolation { field } => write!(
                f,
                "operational evidence field `{field}` cannot satisfy a complexity obligation"
            ),
            Self::HiddenUnboundedRecursion => {
                write!(
                    f,
                    "hidden unbounded recursion is not an accepted machine obligation"
                )
            }
            Self::InvalidMachineEncoding => write!(f, "machine encoding is not valid"),
            Self::MissingFuelOrTerminationEvidence => write!(
                f,
                "machine execution obligations require explicit fuel or termination evidence"
            ),
            Self::RuntimeObligationNotSeparated => write!(
                f,
                "runtime obligations must be separate from semantic correctness"
            ),
            Self::OutputSizeObligationNotSeparated => write!(
                f,
                "output-size obligations must be separate from semantic correctness"
            ),
            Self::MissingEvidence { field } => write!(f, "missing evidence `{field}`"),
            Self::DuplicateEvidenceHash { field, hash } => {
                write!(f, "duplicate hash `{hash}` in `{field}`")
            }
            Self::MissingCheckedTheoremReference => write!(
                f,
                "verified complexity obligation requires checked theorem references"
            ),
            Self::DuplicateCheckedTheoremReference {
                theorem_declaration,
            } => write!(
                f,
                "duplicate checked theorem reference `{theorem_declaration}`"
            ),
            Self::CheckedTheoremOutsideProofCorpus {
                theorem_declaration,
            } => write!(
                f,
                "checked theorem `{theorem_declaration}` is outside the proof corpus namespace"
            ),
            Self::VerifiedObligationCannotHaveBlockers => {
                write!(f, "verified complexity obligation cannot carry blockers")
            }
            Self::VerifiedObligationCannotHaveRejection => {
                write!(
                    f,
                    "verified complexity obligation cannot carry rejection reason"
                )
            }
            Self::OpenObligationRequiresBlockerOrTask => {
                write!(f, "open complexity obligation requires a blocker or task")
            }
            Self::TaskCreatedRequiresProofTask => {
                write!(
                    f,
                    "task-created complexity obligation requires a proof task key"
                )
            }
            Self::RejectedObligationRequiresReason => {
                write!(
                    f,
                    "rejected complexity obligation requires a rejection reason"
                )
            }
            Self::DuplicateBlocker { blocker_key } => {
                write!(f, "duplicate blocker `{blocker_key}`")
            }
        }
    }
}

pub fn parse_complexity_obligation_record(
    source: &str,
) -> Result<ComplexityObligationRecord, ComplexityObligationSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != COMPLEXITY_OBLIGATION_RECORD_API_VERSION {
        return Err(ComplexityObligationSchemaError::new(
            "$.api_version",
            ComplexityObligationSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ComplexityObligationRecord {
        api_version,
        obligation_key: required_string(&root, "obligation_key", "$")?,
        subject_hash: required_hash(&root, "subject_hash", "$")?,
        route_package_hash: optional_hash(&root, "route_package_hash", "$")?,
        theorem_card_hash: optional_hash(&root, "theorem_card_hash", "$")?,
        machine_model_hash: required_hash(&root, "machine_model_hash", "$")?,
        obligation_kind: parse_obligation_kind_value(
            required_value(&root, "obligation_kind", "$")?,
            "$.obligation_kind",
        )?,
        statement_artifact_hash: required_hash(&root, "statement_artifact_hash", "$")?,
        status: parse_status_value(required_value(&root, "status", "$")?, "$.status")?,
        checked_theorem_references: parse_theorem_references(required_value(
            &root,
            "checked_theorem_references",
            "$",
        )?)?,
        source_free_verification_hashes: parse_hash_array(
            required_value(&root, "source_free_verification_hashes", "$")?,
            "$.source_free_verification_hashes",
        )?,
        encoding_audit_hashes: parse_hash_array(
            required_value(&root, "encoding_audit_hashes", "$")?,
            "$.encoding_audit_hashes",
        )?,
        depends_on_obligation_hashes: parse_hash_array(
            required_value(&root, "depends_on_obligation_hashes", "$")?,
            "$.depends_on_obligation_hashes",
        )?,
        proof_task_key: optional_string(&root, "proof_task_key", "$")?,
        blockers: parse_blockers(required_value(&root, "blockers", "$")?)?,
        rejection_reason_hash: optional_hash(&root, "rejection_reason_hash", "$")?,
        uses_explicit_fuel: required_bool(&root, "uses_explicit_fuel", "$")?,
        uses_termination_evidence: required_bool(&root, "uses_termination_evidence", "$")?,
        runtime_separated_from_correctness: required_bool(
            &root,
            "runtime_separated_from_correctness",
            "$",
        )?,
        output_size_separated_from_correctness: required_bool(
            &root,
            "output_size_separated_from_correctness",
            "$",
        )?,
        allows_host_timing_evidence: required_bool(&root, "allows_host_timing_evidence", "$")?,
        allows_solver_counter_evidence: required_bool(
            &root,
            "allows_solver_counter_evidence",
            "$",
        )?,
        allows_simulation_log_evidence: required_bool(
            &root,
            "allows_simulation_log_evidence",
            "$",
        )?,
        hidden_unbounded_recursion: required_bool(&root, "hidden_unbounded_recursion", "$")?,
        machine_encoding_valid: required_bool(&root, "machine_encoding_valid", "$")?,
        creates_theorem_declarations: required_bool(&root, "creates_theorem_declarations", "$")?,
        creates_verified_artifacts: required_bool(&root, "creates_verified_artifacts", "$")?,
        releases_dependencies: required_bool(&root, "releases_dependencies", "$")?,
        creates_proof_acceptance: required_bool(&root, "creates_proof_acceptance", "$")?,
        wall_clock_time: optional_string(&root, "wall_clock_time", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_complexity_obligation_record(
    record: &ComplexityObligationRecord,
) -> Result<(), ComplexityObligationValidationError> {
    require_non_empty(&record.obligation_key, "obligation_key")?;
    validate_sidecar_boundary(record)?;
    validate_operational_boundary(record)?;
    if record.hidden_unbounded_recursion {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::HiddenUnboundedRecursion,
        ));
    }
    if !record.machine_encoding_valid {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::InvalidMachineEncoding,
        ));
    }
    if !record.uses_explicit_fuel && !record.uses_termination_evidence {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::MissingFuelOrTerminationEvidence,
        ));
    }
    if is_runtime_kind(record.obligation_kind) && !record.runtime_separated_from_correctness {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::RuntimeObligationNotSeparated,
        ));
    }
    if is_output_size_kind(record.obligation_kind) && !record.output_size_separated_from_correctness
    {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::OutputSizeObligationNotSeparated,
        ));
    }
    validate_theorem_references(&record.checked_theorem_references)?;
    validate_hash_evidence(
        &record.source_free_verification_hashes,
        "source_free_verification_hashes",
        record.status == ComplexityObligationStatus::Verified,
    )?;
    validate_hash_evidence(
        &record.encoding_audit_hashes,
        "encoding_audit_hashes",
        record.obligation_kind == ComplexityObligationKind::CodecCorrectness
            && record.status == ComplexityObligationStatus::Verified,
    )?;
    validate_hash_evidence(
        &record.depends_on_obligation_hashes,
        "depends_on_obligation_hashes",
        false,
    )?;
    validate_blockers(&record.blockers)?;
    validate_status(record)?;
    Ok(())
}

pub fn complexity_obligation_record_canonical_identity_bytes(
    record: &ComplexityObligationRecord,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, COMPLEXITY_OBLIGATION_RECORD_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "obligation_key");
    encode_string_to(&mut out, &record.obligation_key);
    encode_string_to(&mut out, "subject_hash");
    encode_hash_to(&mut out, &record.subject_hash);
    encode_option_hash_to(
        &mut out,
        "route_package_hash",
        record.route_package_hash.as_ref(),
    );
    encode_option_hash_to(
        &mut out,
        "theorem_card_hash",
        record.theorem_card_hash.as_ref(),
    );
    encode_string_to(&mut out, "machine_model_hash");
    encode_hash_to(&mut out, &record.machine_model_hash);
    encode_string_to(&mut out, "obligation_kind");
    encode_string_to(&mut out, record.obligation_kind.wire());
    encode_string_to(&mut out, "statement_artifact_hash");
    encode_hash_to(&mut out, &record.statement_artifact_hash);
    encode_string_to(&mut out, "status");
    encode_string_to(&mut out, record.status.wire());
    encode_theorem_references_to(&mut out, &record.checked_theorem_references);
    encode_hash_list_to(
        &mut out,
        "source_free_verification_hashes",
        &record.source_free_verification_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "encoding_audit_hashes",
        &record.encoding_audit_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "depends_on_obligation_hashes",
        &record.depends_on_obligation_hashes,
    );
    encode_option_string_to(&mut out, "proof_task_key", record.proof_task_key.as_deref());
    encode_blockers_to(&mut out, &record.blockers);
    encode_option_hash_to(
        &mut out,
        "rejection_reason_hash",
        record.rejection_reason_hash.as_ref(),
    );
    encode_bool_field_to(&mut out, "uses_explicit_fuel", record.uses_explicit_fuel);
    encode_bool_field_to(
        &mut out,
        "uses_termination_evidence",
        record.uses_termination_evidence,
    );
    encode_bool_field_to(
        &mut out,
        "runtime_separated_from_correctness",
        record.runtime_separated_from_correctness,
    );
    encode_bool_field_to(
        &mut out,
        "output_size_separated_from_correctness",
        record.output_size_separated_from_correctness,
    );
    encode_bool_field_to(
        &mut out,
        "allows_host_timing_evidence",
        record.allows_host_timing_evidence,
    );
    encode_bool_field_to(
        &mut out,
        "allows_solver_counter_evidence",
        record.allows_solver_counter_evidence,
    );
    encode_bool_field_to(
        &mut out,
        "allows_simulation_log_evidence",
        record.allows_simulation_log_evidence,
    );
    encode_bool_field_to(
        &mut out,
        "hidden_unbounded_recursion",
        record.hidden_unbounded_recursion,
    );
    encode_bool_field_to(
        &mut out,
        "machine_encoding_valid",
        record.machine_encoding_valid,
    );
    encode_bool_field_to(
        &mut out,
        "creates_theorem_declarations",
        record.creates_theorem_declarations,
    );
    encode_bool_field_to(
        &mut out,
        "creates_verified_artifacts",
        record.creates_verified_artifacts,
    );
    encode_bool_field_to(
        &mut out,
        "releases_dependencies",
        record.releases_dependencies,
    );
    encode_bool_field_to(
        &mut out,
        "creates_proof_acceptance",
        record.creates_proof_acceptance,
    );
    out
}

pub fn complexity_obligation_record_hash(record: &ComplexityObligationRecord) -> Hash {
    let digest = Sha256::digest(complexity_obligation_record_canonical_identity_bytes(
        record,
    ));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn complexity_obligation_record_hash_string(record: &ComplexityObligationRecord) -> String {
    format_hash_string(&complexity_obligation_record_hash(record))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ComplexityObligationAuditRequirement {
    FunctionalCorrectness,
    TerminationOrFuelSufficiency,
    RuntimeRecurrence,
    RuntimePolynomial,
    OutputSizeRecurrence,
    OutputSizePolynomial,
    CodecCorrectness,
    Uniformity,
}

impl ComplexityObligationAuditRequirement {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FunctionalCorrectness => "functional_correctness",
            Self::TerminationOrFuelSufficiency => "termination_or_fuel_sufficiency",
            Self::RuntimeRecurrence => "runtime_recurrence",
            Self::RuntimePolynomial => "runtime_polynomial",
            Self::OutputSizeRecurrence => "output_size_recurrence",
            Self::OutputSizePolynomial => "output_size_polynomial",
            Self::CodecCorrectness => "codec_correctness",
            Self::Uniformity => "uniformity",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexityObligationAuditReport {
    pub missing_requirements: Vec<ComplexityObligationAuditRequirement>,
    pub verified_obligation_hashes: Vec<Hash>,
    pub open_obligation_hashes: Vec<Hash>,
    pub task_created_obligation_hashes: Vec<Hash>,
    pub rejected_obligation_hashes: Vec<Hash>,
    pub non_verified_obligation_hashes: Vec<Hash>,
    pub blocks_route_readiness: bool,
}

const COMPLEXITY_OBLIGATION_AUDIT_REQUIREMENTS: &[ComplexityObligationAuditRequirement] = &[
    ComplexityObligationAuditRequirement::FunctionalCorrectness,
    ComplexityObligationAuditRequirement::TerminationOrFuelSufficiency,
    ComplexityObligationAuditRequirement::RuntimeRecurrence,
    ComplexityObligationAuditRequirement::RuntimePolynomial,
    ComplexityObligationAuditRequirement::OutputSizeRecurrence,
    ComplexityObligationAuditRequirement::OutputSizePolynomial,
    ComplexityObligationAuditRequirement::CodecCorrectness,
    ComplexityObligationAuditRequirement::Uniformity,
];

pub fn audit_complexity_obligations(
    records: &[ComplexityObligationRecord],
) -> ComplexityObligationAuditReport {
    let mut satisfied = BTreeSet::new();
    let mut verified_obligation_hashes = BTreeSet::new();
    let mut open_obligation_hashes = BTreeSet::new();
    let mut task_created_obligation_hashes = BTreeSet::new();
    let mut rejected_obligation_hashes = BTreeSet::new();
    let mut non_verified_obligation_hashes = BTreeSet::new();

    for record in records {
        let hash = complexity_obligation_record_hash(record);
        match record.status {
            ComplexityObligationStatus::Verified => {
                verified_obligation_hashes.insert(hash);
                for requirement in audit_requirements_satisfied_by(record.obligation_kind) {
                    satisfied.insert(*requirement);
                }
            }
            ComplexityObligationStatus::Open => {
                open_obligation_hashes.insert(hash);
                non_verified_obligation_hashes.insert(hash);
            }
            ComplexityObligationStatus::TaskCreated => {
                task_created_obligation_hashes.insert(hash);
                non_verified_obligation_hashes.insert(hash);
            }
            ComplexityObligationStatus::Rejected => {
                rejected_obligation_hashes.insert(hash);
                non_verified_obligation_hashes.insert(hash);
            }
        }
    }

    let missing_requirements = COMPLEXITY_OBLIGATION_AUDIT_REQUIREMENTS
        .iter()
        .copied()
        .filter(|requirement| !satisfied.contains(requirement))
        .collect::<Vec<_>>();
    let non_verified_obligation_hashes = non_verified_obligation_hashes
        .into_iter()
        .collect::<Vec<_>>();
    let blocks_route_readiness =
        !missing_requirements.is_empty() || !non_verified_obligation_hashes.is_empty();

    ComplexityObligationAuditReport {
        missing_requirements,
        verified_obligation_hashes: verified_obligation_hashes.into_iter().collect(),
        open_obligation_hashes: open_obligation_hashes.into_iter().collect(),
        task_created_obligation_hashes: task_created_obligation_hashes.into_iter().collect(),
        rejected_obligation_hashes: rejected_obligation_hashes.into_iter().collect(),
        non_verified_obligation_hashes,
        blocks_route_readiness,
    }
}

fn audit_requirements_satisfied_by(
    kind: ComplexityObligationKind,
) -> &'static [ComplexityObligationAuditRequirement] {
    match kind {
        ComplexityObligationKind::FunctionalCorrectness => {
            &[ComplexityObligationAuditRequirement::FunctionalCorrectness]
        }
        ComplexityObligationKind::Termination | ComplexityObligationKind::FuelSufficiency => {
            &[ComplexityObligationAuditRequirement::TerminationOrFuelSufficiency]
        }
        ComplexityObligationKind::RuntimeRecurrence => {
            &[ComplexityObligationAuditRequirement::RuntimeRecurrence]
        }
        ComplexityObligationKind::RuntimePolynomial => {
            &[ComplexityObligationAuditRequirement::RuntimePolynomial]
        }
        ComplexityObligationKind::OutputSizeRecurrence => {
            &[ComplexityObligationAuditRequirement::OutputSizeRecurrence]
        }
        ComplexityObligationKind::OutputSizePolynomial => {
            &[ComplexityObligationAuditRequirement::OutputSizePolynomial]
        }
        ComplexityObligationKind::CodecCorrectness => {
            &[ComplexityObligationAuditRequirement::CodecCorrectness]
        }
        ComplexityObligationKind::Uniformity => &[ComplexityObligationAuditRequirement::Uniformity],
        ComplexityObligationKind::WellFormedness => &[],
    }
}

fn validate_sidecar_boundary(
    record: &ComplexityObligationRecord,
) -> Result<(), ComplexityObligationValidationError> {
    let flags = [
        (
            "creates_theorem_declarations",
            record.creates_theorem_declarations,
        ),
        (
            "creates_verified_artifacts",
            record.creates_verified_artifacts,
        ),
        ("releases_dependencies", record.releases_dependencies),
        ("creates_proof_acceptance", record.creates_proof_acceptance),
    ];
    for (field, value) in flags {
        if value {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::SidecarBoundaryViolation { field },
            ));
        }
    }
    Ok(())
}

fn validate_operational_boundary(
    record: &ComplexityObligationRecord,
) -> Result<(), ComplexityObligationValidationError> {
    let flags = [
        (
            "allows_host_timing_evidence",
            record.allows_host_timing_evidence,
        ),
        (
            "allows_solver_counter_evidence",
            record.allows_solver_counter_evidence,
        ),
        (
            "allows_simulation_log_evidence",
            record.allows_simulation_log_evidence,
        ),
    ];
    for (field, value) in flags {
        if value {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::OperationalEvidenceBoundaryViolation {
                    field,
                },
            ));
        }
    }
    Ok(())
}

fn validate_theorem_references(
    references: &[ComplexityObligationTheoremReference],
) -> Result<(), ComplexityObligationValidationError> {
    let mut seen = BTreeSet::new();
    for reference in references {
        require_non_empty(
            &reference.theorem_declaration,
            "checked_theorem_references.theorem_declaration",
        )?;
        if !reference
            .theorem_declaration
            .starts_with(PROOF_CORPUS_PREFIX)
        {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::CheckedTheoremOutsideProofCorpus {
                    theorem_declaration: reference.theorem_declaration.clone(),
                },
            ));
        }
        if !seen.insert(reference.theorem_declaration.as_str()) {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::DuplicateCheckedTheoremReference {
                    theorem_declaration: reference.theorem_declaration.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn validate_hash_evidence(
    hashes: &[Hash],
    field: &'static str,
    required: bool,
) -> Result<(), ComplexityObligationValidationError> {
    if required && hashes.is_empty() {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::MissingEvidence { field },
        ));
    }
    let mut seen = BTreeSet::new();
    for hash in hashes {
        if !seen.insert(*hash) {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::DuplicateEvidenceHash {
                    field,
                    hash: format_hash_string(hash),
                },
            ));
        }
    }
    Ok(())
}

fn validate_blockers(
    blockers: &[ComplexityObligationBlocker],
) -> Result<(), ComplexityObligationValidationError> {
    let mut seen = BTreeSet::new();
    for blocker in blockers {
        require_non_empty(&blocker.blocker_key, "blockers.blocker_key")?;
        require_non_empty(&blocker.reason, "blockers.reason")?;
        if !seen.insert(blocker.blocker_key.as_str()) {
            return Err(ComplexityObligationValidationError::new(
                ComplexityObligationValidationErrorKind::DuplicateBlocker {
                    blocker_key: blocker.blocker_key.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn validate_status(
    record: &ComplexityObligationRecord,
) -> Result<(), ComplexityObligationValidationError> {
    match record.status {
        ComplexityObligationStatus::Verified => {
            if record.checked_theorem_references.is_empty() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::MissingCheckedTheoremReference,
                ));
            }
            if !record.blockers.is_empty() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::VerifiedObligationCannotHaveBlockers,
                ));
            }
            if record.rejection_reason_hash.is_some() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::VerifiedObligationCannotHaveRejection,
                ));
            }
        }
        ComplexityObligationStatus::Open => {
            if record.blockers.is_empty() && record.proof_task_key.is_none() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::OpenObligationRequiresBlockerOrTask,
                ));
            }
        }
        ComplexityObligationStatus::TaskCreated => {
            if record.proof_task_key.is_none() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::TaskCreatedRequiresProofTask,
                ));
            }
        }
        ComplexityObligationStatus::Rejected => {
            if record.rejection_reason_hash.is_none() {
                return Err(ComplexityObligationValidationError::new(
                    ComplexityObligationValidationErrorKind::RejectedObligationRequiresReason,
                ));
            }
        }
    }
    Ok(())
}

fn is_runtime_kind(kind: ComplexityObligationKind) -> bool {
    matches!(
        kind,
        ComplexityObligationKind::RuntimeRecurrence | ComplexityObligationKind::RuntimePolynomial
    )
}

fn is_output_size_kind(kind: ComplexityObligationKind) -> bool {
    matches!(
        kind,
        ComplexityObligationKind::OutputSizeRecurrence
            | ComplexityObligationKind::OutputSizePolynomial
    )
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ComplexityObligationSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ComplexityObligationSchemaError::new(
            "$",
            ComplexityObligationSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ComplexityObligationSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ComplexityObligationSchemaError::new(
                format!("{path}.{}", member.key()),
                ComplexityObligationSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ComplexityObligationSchemaError::new(
                format!("{path}.{}", member.key()),
                ComplexityObligationSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ComplexityObligationSchemaError> {
    value.array_elements().ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ComplexityObligationSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            format!("{path}.{field}"),
            ComplexityObligationSchemaErrorKind::MissingField { field },
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
) -> Result<String, ComplexityObligationSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ComplexityObligationSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<String, ComplexityObligationSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ComplexityObligationSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ComplexityObligationSchemaError> {
    value.bool_value().ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ComplexityObligationSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ComplexityObligationSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ComplexityObligationSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_theorem_references(
    value: &JsonValue<'_>,
) -> Result<Vec<ComplexityObligationTheoremReference>, ComplexityObligationSchemaError> {
    array_elements(value, "$.checked_theorem_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_theorem_reference(value, &format!("$.checked_theorem_references[{index}]"))
        })
        .collect()
}

fn parse_theorem_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ComplexityObligationTheoremReference, ComplexityObligationSchemaError> {
    let members = object_map(value, path, THEOREM_REFERENCE_FIELDS)?;
    Ok(ComplexityObligationTheoremReference {
        theorem_declaration: required_string(&members, "theorem_declaration", path)?,
        statement_hash: required_hash(&members, "statement_hash", path)?,
        certificate_hash: required_hash(&members, "certificate_hash", path)?,
        source_free_verification_hash: required_hash(
            &members,
            "source_free_verification_hash",
            path,
        )?,
    })
}

fn parse_blockers(
    value: &JsonValue<'_>,
) -> Result<Vec<ComplexityObligationBlocker>, ComplexityObligationSchemaError> {
    array_elements(value, "$.blockers")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_blocker(value, &format!("$.blockers[{index}]")))
        .collect()
}

fn parse_blocker(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ComplexityObligationBlocker, ComplexityObligationSchemaError> {
    let members = object_map(value, path, BLOCKER_FIELDS)?;
    Ok(ComplexityObligationBlocker {
        blocker_key: required_string(&members, "blocker_key", path)?,
        blocker_hash: required_hash(&members, "blocker_hash", path)?,
        reason: required_string(&members, "reason", path)?,
        prerequisite_task_key: optional_string(&members, "prerequisite_task_key", path)?,
    })
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, ComplexityObligationSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_obligation_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ComplexityObligationKind, ComplexityObligationSchemaError> {
    let wire = string_value(value, path)?;
    ComplexityObligationKind::parse(&wire).ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::InvalidObligationKind { value: wire },
        )
    })
}

fn parse_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ComplexityObligationStatus, ComplexityObligationSchemaError> {
    let wire = string_value(value, path)?;
    ComplexityObligationStatus::parse(&wire).ok_or_else(|| {
        ComplexityObligationSchemaError::new(
            path,
            ComplexityObligationSchemaErrorKind::InvalidStatus { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ComplexityObligationValidationError> {
    if value.trim().is_empty() {
        return Err(ComplexityObligationValidationError::new(
            ComplexityObligationValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_theorem_references_to(
    out: &mut Vec<u8>,
    references: &[ComplexityObligationTheoremReference],
) {
    encode_string_to(out, "checked_theorem_references");
    let mut references = references.to_vec();
    references.sort_by(|left, right| left.theorem_declaration.cmp(&right.theorem_declaration));
    encode_len_to(out, references.len());
    for reference in &references {
        encode_string_to(out, &reference.theorem_declaration);
        encode_hash_to(out, &reference.statement_hash);
        encode_hash_to(out, &reference.certificate_hash);
        encode_hash_to(out, &reference.source_free_verification_hash);
    }
}

fn encode_blockers_to(out: &mut Vec<u8>, blockers: &[ComplexityObligationBlocker]) {
    encode_string_to(out, "blockers");
    let mut blockers = blockers.to_vec();
    blockers.sort_by(|left, right| left.blocker_key.cmp(&right.blocker_key));
    encode_len_to(out, blockers.len());
    for blocker in &blockers {
        encode_string_to(out, &blocker.blocker_key);
        encode_hash_to(out, &blocker.blocker_hash);
        encode_string_to(out, &blocker.reason);
        encode_option_string_to(
            out,
            "prerequisite_task_key",
            blocker.prerequisite_task_key.as_deref(),
        );
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

fn encode_bool_field_to(out: &mut Vec<u8>, label: &str, value: bool) {
    encode_string_to(out, label);
    out.push(u8::from(value));
}

fn encode_option_string_to(out: &mut Vec<u8>, label: &str, value: Option<&str>) {
    encode_string_to(out, label);
    match value {
        Some(value) => {
            out.push(1);
            encode_string_to(out, value);
        }
        None => out.push(0),
    }
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

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_len_to(out, value.len());
    out.extend_from_slice(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    out.extend_from_slice(&(len as u64).to_be_bytes());
}

use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const BARRIER_AUDIT_API_VERSION: &str = "npa.barrier-audit.v1";
pub const BARRIER_AUDIT_HASH_DOMAIN: &str = "npa.barrier-audit.identity.v1";

const REPORT_KIND: &str = "audit_report";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "report_kind",
    "proof_or_plan_hash",
    "dependency_hashes",
    "findings",
    "complexity_obligation_hashes",
    "review_required_for_confirmed_findings",
    "blocks_route_readiness",
    "creates_theorem_declarations",
    "creates_certificate_evidence",
    "creates_verified_artifacts",
    "releases_dependencies",
    "creates_proof_acceptance",
    "automatically_refutes_route",
    "rejects_valid_checked_theorem_without_review",
    "audit_hash",
    "display_text",
];
const FINDING_FIELDS: &[&str] = &["category", "assessment", "evidence"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarrierAuditRecord {
    pub api_version: String,
    pub report_kind: String,
    pub proof_or_plan_hash: Hash,
    pub dependency_hashes: Vec<Hash>,
    pub findings: Vec<BarrierAuditFinding>,
    pub complexity_obligation_hashes: Vec<Hash>,
    pub review_required_for_confirmed_findings: bool,
    pub blocks_route_readiness: bool,
    pub creates_theorem_declarations: bool,
    pub creates_certificate_evidence: bool,
    pub creates_verified_artifacts: bool,
    pub releases_dependencies: bool,
    pub creates_proof_acceptance: bool,
    pub automatically_refutes_route: bool,
    pub rejects_valid_checked_theorem_without_review: bool,
    pub audit_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarrierAuditFinding {
    pub category: BarrierAuditCategory,
    pub assessment: BarrierAuditAssessment,
    pub evidence: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BarrierAuditCategory {
    Relativization,
    NaturalProofs,
    Algebrization,
    BlackBox,
    Nonuniformity,
    CountingOnly,
    CryptographicAssumption,
    ClassicalAssumption,
}

impl BarrierAuditCategory {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Relativization => "relativization",
            Self::NaturalProofs => "natural_proofs",
            Self::Algebrization => "algebrization",
            Self::BlackBox => "black_box",
            Self::Nonuniformity => "nonuniformity",
            Self::CountingOnly => "counting_only",
            Self::CryptographicAssumption => "cryptographic_assumption",
            Self::ClassicalAssumption => "classical_assumption",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "relativization" => Some(Self::Relativization),
            "natural_proofs" => Some(Self::NaturalProofs),
            "algebrization" => Some(Self::Algebrization),
            "black_box" => Some(Self::BlackBox),
            "nonuniformity" => Some(Self::Nonuniformity),
            "counting_only" => Some(Self::CountingOnly),
            "cryptographic_assumption" => Some(Self::CryptographicAssumption),
            "classical_assumption" => Some(Self::ClassicalAssumption),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BarrierAuditAssessment {
    NotDetected,
    Possible,
    Likely,
    Confirmed,
    NotApplicable,
}

impl BarrierAuditAssessment {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarrierAuditSchemaError {
    path: String,
    kind: BarrierAuditSchemaErrorKind,
}

impl BarrierAuditSchemaError {
    fn new(path: impl Into<String>, kind: BarrierAuditSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &BarrierAuditSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for BarrierAuditSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "barrier audit schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for BarrierAuditSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BarrierAuditSchemaErrorKind {
    JsonParse { offset: usize },
    ExpectedObject { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidApiVersion { value: String },
    InvalidReportKind { value: String },
    InvalidHash { value: String },
    InvalidCategory { value: String },
    InvalidAssessment { value: String },
}

impl fmt::Display for BarrierAuditSchemaErrorKind {
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
            Self::InvalidReportKind { value } => write!(f, "invalid report kind `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidCategory { value } => write!(f, "invalid barrier category `{value}`"),
            Self::InvalidAssessment { value } => write!(f, "invalid barrier assessment `{value}`"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarrierAuditValidationError {
    kind: BarrierAuditValidationErrorKind,
}

impl BarrierAuditValidationError {
    fn new(kind: BarrierAuditValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &BarrierAuditValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for BarrierAuditValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "barrier audit validation error: {}", self.kind)
    }
}

impl std::error::Error for BarrierAuditValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BarrierAuditValidationErrorKind {
    EmptyDependencyHashes,
    EmptyFindings,
    EmptyEvidence {
        category: BarrierAuditCategory,
    },
    EmptyEvidenceEntry {
        category: BarrierAuditCategory,
    },
    DuplicateDependencyHash {
        hash: String,
    },
    DuplicateComplexityObligationHash {
        hash: String,
    },
    DuplicateFindingCategory {
        category: String,
    },
    DuplicateEvidence {
        category: BarrierAuditCategory,
        evidence: String,
    },
    SidecarBoundaryViolation {
        field: &'static str,
    },
    ConfirmedFindingRequiresReview {
        category: BarrierAuditCategory,
    },
    FindingRequiresReadinessBlock {
        category: BarrierAuditCategory,
    },
    MissingComplexityObligationsRequireReadinessBlock,
}

impl fmt::Display for BarrierAuditValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyDependencyHashes => write!(f, "audit report requires dependency hashes"),
            Self::EmptyFindings => write!(f, "audit report requires findings"),
            Self::EmptyEvidence { category } => {
                write!(f, "finding `{}` requires evidence", category.wire())
            }
            Self::EmptyEvidenceEntry { category } => {
                write!(f, "finding `{}` has empty evidence entry", category.wire())
            }
            Self::DuplicateDependencyHash { hash } => {
                write!(f, "duplicate dependency hash `{hash}`")
            }
            Self::DuplicateComplexityObligationHash { hash } => {
                write!(f, "duplicate complexity obligation hash `{hash}`")
            }
            Self::DuplicateFindingCategory { category } => {
                write!(f, "duplicate finding category `{category}`")
            }
            Self::DuplicateEvidence { category, evidence } => write!(
                f,
                "duplicate evidence `{evidence}` for finding `{}`",
                category.wire()
            ),
            Self::SidecarBoundaryViolation { field } => {
                write!(f, "audit report violates sidecar boundary via `{field}`")
            }
            Self::ConfirmedFindingRequiresReview { category } => write!(
                f,
                "confirmed finding `{}` requires explicit review",
                category.wire()
            ),
            Self::FindingRequiresReadinessBlock { category } => write!(
                f,
                "finding `{}` requires route-readiness blocking until review",
                category.wire()
            ),
            Self::MissingComplexityObligationsRequireReadinessBlock => write!(
                f,
                "missing complexity obligations require route-readiness blocking"
            ),
        }
    }
}

pub fn parse_barrier_audit_record(
    source: &str,
) -> Result<BarrierAuditRecord, BarrierAuditSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != BARRIER_AUDIT_API_VERSION {
        return Err(BarrierAuditSchemaError::new(
            "$.api_version",
            BarrierAuditSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }
    let report_kind = required_string(&root, "report_kind", "$")?;
    if report_kind != REPORT_KIND {
        return Err(BarrierAuditSchemaError::new(
            "$.report_kind",
            BarrierAuditSchemaErrorKind::InvalidReportKind { value: report_kind },
        ));
    }

    Ok(BarrierAuditRecord {
        api_version,
        report_kind,
        proof_or_plan_hash: required_hash(&root, "proof_or_plan_hash", "$")?,
        dependency_hashes: parse_hash_array(
            required_value(&root, "dependency_hashes", "$")?,
            "$.dependency_hashes",
        )?,
        findings: parse_findings(required_value(&root, "findings", "$")?)?,
        complexity_obligation_hashes: optional_hash_array(
            &root,
            "complexity_obligation_hashes",
            "$.complexity_obligation_hashes",
        )?,
        review_required_for_confirmed_findings: required_bool(
            &root,
            "review_required_for_confirmed_findings",
            "$",
        )?,
        blocks_route_readiness: required_bool(&root, "blocks_route_readiness", "$")?,
        creates_theorem_declarations: required_bool(&root, "creates_theorem_declarations", "$")?,
        creates_certificate_evidence: required_bool(&root, "creates_certificate_evidence", "$")?,
        creates_verified_artifacts: required_bool(&root, "creates_verified_artifacts", "$")?,
        releases_dependencies: required_bool(&root, "releases_dependencies", "$")?,
        creates_proof_acceptance: required_bool(&root, "creates_proof_acceptance", "$")?,
        automatically_refutes_route: required_bool(&root, "automatically_refutes_route", "$")?,
        rejects_valid_checked_theorem_without_review: required_bool(
            &root,
            "rejects_valid_checked_theorem_without_review",
            "$",
        )?,
        audit_hash: required_hash(&root, "audit_hash", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_barrier_audit_record(
    record: &BarrierAuditRecord,
) -> Result<(), BarrierAuditValidationError> {
    validate_sidecar_boundary(record)?;
    validate_hash_list(&record.dependency_hashes, HashListKind::Dependency)?;
    validate_hash_list(
        &record.complexity_obligation_hashes,
        HashListKind::ComplexityObligation,
    )?;
    validate_findings_semantics(record)?;
    Ok(())
}

pub fn barrier_audit_canonical_identity_bytes(record: &BarrierAuditRecord) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, BARRIER_AUDIT_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "report_kind");
    encode_string_to(&mut out, &record.report_kind);
    encode_string_to(&mut out, "proof_or_plan_hash");
    encode_hash_to(&mut out, &record.proof_or_plan_hash);
    encode_hash_list_to(&mut out, "dependency_hashes", &record.dependency_hashes);
    encode_findings_to(&mut out, &record.findings);
    encode_hash_list_to(
        &mut out,
        "complexity_obligation_hashes",
        &record.complexity_obligation_hashes,
    );
    encode_bool_field_to(
        &mut out,
        "review_required_for_confirmed_findings",
        record.review_required_for_confirmed_findings,
    );
    encode_bool_field_to(
        &mut out,
        "blocks_route_readiness",
        record.blocks_route_readiness,
    );
    encode_bool_field_to(
        &mut out,
        "creates_theorem_declarations",
        record.creates_theorem_declarations,
    );
    encode_bool_field_to(
        &mut out,
        "creates_certificate_evidence",
        record.creates_certificate_evidence,
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
    encode_bool_field_to(
        &mut out,
        "automatically_refutes_route",
        record.automatically_refutes_route,
    );
    encode_bool_field_to(
        &mut out,
        "rejects_valid_checked_theorem_without_review",
        record.rejects_valid_checked_theorem_without_review,
    );
    out
}

pub fn barrier_audit_hash(record: &BarrierAuditRecord) -> Hash {
    let digest = Sha256::digest(barrier_audit_canonical_identity_bytes(record));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn barrier_audit_hash_string(record: &BarrierAuditRecord) -> String {
    format_hash_string(&barrier_audit_hash(record))
}

fn validate_sidecar_boundary(
    record: &BarrierAuditRecord,
) -> Result<(), BarrierAuditValidationError> {
    let flags = [
        (
            "creates_theorem_declarations",
            record.creates_theorem_declarations,
        ),
        (
            "creates_certificate_evidence",
            record.creates_certificate_evidence,
        ),
        (
            "creates_verified_artifacts",
            record.creates_verified_artifacts,
        ),
        ("releases_dependencies", record.releases_dependencies),
        ("creates_proof_acceptance", record.creates_proof_acceptance),
        (
            "automatically_refutes_route",
            record.automatically_refutes_route,
        ),
        (
            "rejects_valid_checked_theorem_without_review",
            record.rejects_valid_checked_theorem_without_review,
        ),
    ];
    for (field, value) in flags {
        if value {
            return Err(BarrierAuditValidationError::new(
                BarrierAuditValidationErrorKind::SidecarBoundaryViolation { field },
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum HashListKind {
    Dependency,
    ComplexityObligation,
}

fn validate_hash_list(
    hashes: &[Hash],
    kind: HashListKind,
) -> Result<(), BarrierAuditValidationError> {
    if hashes.is_empty() && matches!(kind, HashListKind::Dependency) {
        return Err(BarrierAuditValidationError::new(
            BarrierAuditValidationErrorKind::EmptyDependencyHashes,
        ));
    }
    let mut seen = BTreeSet::new();
    for hash in hashes {
        if !seen.insert(*hash) {
            let hash = format_hash_string(hash);
            return Err(BarrierAuditValidationError::new(match kind {
                HashListKind::Dependency => {
                    BarrierAuditValidationErrorKind::DuplicateDependencyHash { hash }
                }
                HashListKind::ComplexityObligation => {
                    BarrierAuditValidationErrorKind::DuplicateComplexityObligationHash { hash }
                }
            }));
        }
    }
    Ok(())
}

fn validate_findings_semantics(
    record: &BarrierAuditRecord,
) -> Result<(), BarrierAuditValidationError> {
    if record.findings.is_empty() {
        return Err(BarrierAuditValidationError::new(
            BarrierAuditValidationErrorKind::EmptyFindings,
        ));
    }

    let mut seen_categories = BTreeSet::new();
    let mut requires_readiness_block = false;
    for finding in &record.findings {
        if !seen_categories.insert(finding.category) {
            return Err(BarrierAuditValidationError::new(
                BarrierAuditValidationErrorKind::DuplicateFindingCategory {
                    category: finding.category.wire().to_owned(),
                },
            ));
        }
        if finding.evidence.is_empty() {
            return Err(BarrierAuditValidationError::new(
                BarrierAuditValidationErrorKind::EmptyEvidence {
                    category: finding.category,
                },
            ));
        }
        let mut seen_evidence = BTreeSet::new();
        for evidence in &finding.evidence {
            if evidence.trim().is_empty() {
                return Err(BarrierAuditValidationError::new(
                    BarrierAuditValidationErrorKind::EmptyEvidenceEntry {
                        category: finding.category,
                    },
                ));
            }
            if !seen_evidence.insert(evidence.as_str()) {
                return Err(BarrierAuditValidationError::new(
                    BarrierAuditValidationErrorKind::DuplicateEvidence {
                        category: finding.category,
                        evidence: evidence.clone(),
                    },
                ));
            }
        }
        if finding.assessment == BarrierAuditAssessment::Confirmed
            && !record.review_required_for_confirmed_findings
        {
            return Err(BarrierAuditValidationError::new(
                BarrierAuditValidationErrorKind::ConfirmedFindingRequiresReview {
                    category: finding.category,
                },
            ));
        }
        if matches!(
            finding.assessment,
            BarrierAuditAssessment::Likely | BarrierAuditAssessment::Confirmed
        ) {
            requires_readiness_block = true;
        }
    }

    if requires_readiness_block && !record.blocks_route_readiness {
        let category = record
            .findings
            .iter()
            .find(|finding| {
                matches!(
                    finding.assessment,
                    BarrierAuditAssessment::Likely | BarrierAuditAssessment::Confirmed
                )
            })
            .expect("requires_readiness_block came from a finding")
            .category;
        return Err(BarrierAuditValidationError::new(
            BarrierAuditValidationErrorKind::FindingRequiresReadinessBlock { category },
        ));
    }

    if !record.complexity_obligation_hashes.is_empty() && !record.blocks_route_readiness {
        return Err(BarrierAuditValidationError::new(
            BarrierAuditValidationErrorKind::MissingComplexityObligationsRequireReadinessBlock,
        ));
    }

    Ok(())
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, BarrierAuditSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        BarrierAuditSchemaError::new(
            "$",
            BarrierAuditSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, BarrierAuditSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(BarrierAuditSchemaError::new(
            path,
            BarrierAuditSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(BarrierAuditSchemaError::new(
                format!("{path}.{}", member.key()),
                BarrierAuditSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(BarrierAuditSchemaError::new(
                format!("{path}.{}", member.key()),
                BarrierAuditSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], BarrierAuditSchemaError> {
    value.array_elements().ok_or_else(|| {
        BarrierAuditSchemaError::new(
            path,
            BarrierAuditSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, BarrierAuditSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        BarrierAuditSchemaError::new(
            format!("{path}.{field}"),
            BarrierAuditSchemaErrorKind::MissingField { field },
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
) -> Result<String, BarrierAuditSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, BarrierAuditSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, BarrierAuditSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        BarrierAuditSchemaError::new(
            path,
            BarrierAuditSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, BarrierAuditSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, BarrierAuditSchemaError> {
    value.bool_value().ok_or_else(|| {
        BarrierAuditSchemaError::new(
            path,
            BarrierAuditSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, BarrierAuditSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, BarrierAuditSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        BarrierAuditSchemaError::new(
            path,
            BarrierAuditSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, BarrierAuditSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn optional_hash_array(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Vec<Hash>, BarrierAuditSchemaError> {
    optional_value(members, field)
        .map(|value| parse_hash_array(value, path))
        .unwrap_or_else(|| Ok(Vec::new()))
}

fn parse_findings(
    value: &JsonValue<'_>,
) -> Result<Vec<BarrierAuditFinding>, BarrierAuditSchemaError> {
    array_elements(value, "$.findings")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_finding(value, &format!("$.findings[{index}]")))
        .collect()
}

fn parse_finding(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<BarrierAuditFinding, BarrierAuditSchemaError> {
    let members = object_map(value, path, FINDING_FIELDS)?;
    Ok(BarrierAuditFinding {
        category: parse_category_value(required_value(&members, "category", path)?, path)?,
        assessment: parse_assessment_value(required_value(&members, "assessment", path)?, path)?,
        evidence: parse_string_array(
            required_value(&members, "evidence", path)?,
            &format!("{path}.evidence"),
        )?,
    })
}

fn parse_string_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<String>, BarrierAuditSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| string_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_category_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<BarrierAuditCategory, BarrierAuditSchemaError> {
    let wire = string_value(value, &format!("{path}.category"))?;
    BarrierAuditCategory::parse(&wire).ok_or_else(|| {
        BarrierAuditSchemaError::new(
            format!("{path}.category"),
            BarrierAuditSchemaErrorKind::InvalidCategory { value: wire },
        )
    })
}

fn parse_assessment_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<BarrierAuditAssessment, BarrierAuditSchemaError> {
    let wire = string_value(value, &format!("{path}.assessment"))?;
    BarrierAuditAssessment::parse(&wire).ok_or_else(|| {
        BarrierAuditSchemaError::new(
            format!("{path}.assessment"),
            BarrierAuditSchemaErrorKind::InvalidAssessment { value: wire },
        )
    })
}

fn encode_findings_to(out: &mut Vec<u8>, findings: &[BarrierAuditFinding]) {
    encode_string_to(out, "findings");
    let mut findings = findings.to_vec();
    findings.sort_by_key(|finding| finding.category);
    encode_len_to(out, findings.len());
    for finding in &findings {
        encode_string_to(out, finding.category.wire());
        encode_string_to(out, finding.assessment.wire());
        let mut evidence = finding.evidence.clone();
        evidence.sort();
        encode_len_to(out, evidence.len());
        for item in &evidence {
            encode_string_to(out, item);
        }
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
            .join("testdata/proof-using-agents/fixtures/pua-m16-barrier-audit")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("barrier audit fixture should exist")
    }

    fn parse_fixture(name: &str) -> BarrierAuditRecord {
        parse_barrier_audit_record(&fixture(name)).expect("barrier audit fixture should parse")
    }

    fn validate_fixture(name: &str) -> Result<(), BarrierAuditValidationErrorKind> {
        validate_barrier_audit_record(&parse_fixture(name)).map_err(|error| error.kind().clone())
    }

    #[test]
    fn barrier_auditor_negative_strategies() {
        for (fixture_name, category) in [
            (
                "negative-relativization.json",
                BarrierAuditCategory::Relativization,
            ),
            (
                "negative-natural-proofs.json",
                BarrierAuditCategory::NaturalProofs,
            ),
            (
                "negative-algebrization.json",
                BarrierAuditCategory::Algebrization,
            ),
            ("negative-black-box.json", BarrierAuditCategory::BlackBox),
            (
                "negative-nonuniformity.json",
                BarrierAuditCategory::Nonuniformity,
            ),
            (
                "negative-counting-only.json",
                BarrierAuditCategory::CountingOnly,
            ),
            (
                "negative-cryptographic-assumption.json",
                BarrierAuditCategory::CryptographicAssumption,
            ),
            (
                "negative-classical-assumption.json",
                BarrierAuditCategory::ClassicalAssumption,
            ),
        ] {
            let report = parse_fixture(fixture_name);
            validate_barrier_audit_record(&report)
                .unwrap_or_else(|error| panic!("{fixture_name} should validate: {error}"));
            assert_eq!(report.report_kind, REPORT_KIND);
            assert_eq!(report.findings.len(), 1);
            assert_eq!(report.findings[0].category, category);
            assert_eq!(
                report.findings[0].assessment,
                BarrierAuditAssessment::Confirmed
            );
            assert!(report.review_required_for_confirmed_findings);
            assert!(report.blocks_route_readiness);
            assert!(!report.creates_certificate_evidence);
            assert!(!report.creates_proof_acceptance);
            assert!(!report.automatically_refutes_route);
            assert!(!report.rejects_valid_checked_theorem_without_review);
        }

        let missing_obligation_report = parse_fixture("missing-complexity-obligations.json");
        validate_barrier_audit_record(&missing_obligation_report)
            .expect("missing complexity obligation audit should validate");
        assert!(!missing_obligation_report
            .complexity_obligation_hashes
            .is_empty());
        assert!(missing_obligation_report.blocks_route_readiness);
    }

    #[test]
    fn barrier_audit_is_not_proof_evidence() {
        let report = parse_fixture("valid-route-review.json");
        validate_barrier_audit_record(&report).expect("valid route review should validate");
        let mut display_changed = report.clone();
        display_changed.display_text =
            Some("display text can change without changing audit identity".to_owned());
        assert_eq!(
            barrier_audit_hash(&report),
            barrier_audit_hash(&display_changed)
        );

        assert!(matches!(
            validate_fixture("invalid-audit-report-as-proof.json"),
            Err(BarrierAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "creates_proof_acceptance"
            })
        ));
        assert!(matches!(
            validate_fixture("invalid-audit-report-as-certificate.json"),
            Err(BarrierAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "creates_certificate_evidence"
            })
        ));
        assert!(matches!(
            validate_fixture("invalid-audit-report-auto-refutes.json"),
            Err(BarrierAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "automatically_refutes_route"
            })
        ));
        assert!(matches!(
            validate_fixture("invalid-audit-report-rejects-theorem.json"),
            Err(BarrierAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "rejects_valid_checked_theorem_without_review"
            })
        ));

        let mut unreviewed = parse_fixture("negative-relativization.json");
        unreviewed.review_required_for_confirmed_findings = false;
        assert!(matches!(
            validate_barrier_audit_record(&unreviewed).map_err(|error| error.kind().clone()),
            Err(
                BarrierAuditValidationErrorKind::ConfirmedFindingRequiresReview {
                    category: BarrierAuditCategory::Relativization
                }
            )
        ));

        let mut nonblocking_missing = parse_fixture("missing-complexity-obligations.json");
        nonblocking_missing.blocks_route_readiness = false;
        assert!(matches!(
            validate_barrier_audit_record(&nonblocking_missing)
                .map_err(|error| error.kind().clone()),
            Err(BarrierAuditValidationErrorKind::MissingComplexityObligationsRequireReadinessBlock)
        ));
    }
}

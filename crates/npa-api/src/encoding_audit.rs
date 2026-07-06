use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const ENCODING_AUDIT_RECORD_API_VERSION: &str = "npa.encoding-audit-record.v1";
pub const ENCODING_AUDIT_RECORD_HASH_DOMAIN: &str = "npa.encoding-audit-record.identity.v1";

const COMPLEXITY_ENCODING_NAMESPACE: &str = "Proofs.Ai.Complexity.Encoding.";
const COMPLEXITY_NAMESPACE_PREFIX: &str = "Proofs.Ai.Complexity.";
const REQUIRED_FOUNDATION_MODULES: &[&str] = &[
    "Proofs.Ai.BitString",
    "Proofs.Ai.Codec",
    "Proofs.Ai.NatPolynomial",
    "Proofs.Ai.PolyBound",
    "Proofs.Ai.Cost",
    "Proofs.Ai.Foundation.Poly",
    "Proofs.Ai.Foundation.Cost",
];

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "audit_key",
    "subject_hash",
    "route_package_hash",
    "theorem_card_hash",
    "foundation_references",
    "bridge_theorem_references",
    "codec_identity_hash",
    "representation_class",
    "representation_choice_hash",
    "self_delimiting_policy",
    "malformed_input_behavior",
    "input_size_theorem_hashes",
    "output_size_theorem_hashes",
    "translation_theorem_hashes",
    "source_free_verification_hashes",
    "complexity_obligation_hashes",
    "blockers",
    "audit_decision",
    "rejection_reason_hash",
    "creates_theorem_declarations",
    "creates_verified_artifacts",
    "releases_dependencies",
    "creates_proof_acceptance",
    "wall_clock_time",
    "display_text",
];
const FOUNDATION_REFERENCE_FIELDS: &[&str] = &[
    "module_name",
    "certificate_hash",
    "export_hash",
    "source_free_verification_hash",
    "reused_not_redeclared",
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
pub struct EncodingAuditRecord {
    pub api_version: String,
    pub audit_key: String,
    pub subject_hash: Hash,
    pub route_package_hash: Option<Hash>,
    pub theorem_card_hash: Option<Hash>,
    pub foundation_references: Vec<EncodingAuditFoundationReference>,
    pub bridge_theorem_references: Vec<EncodingAuditTheoremReference>,
    pub codec_identity_hash: Hash,
    pub representation_class: EncodingAuditRepresentationClass,
    pub representation_choice_hash: Hash,
    pub self_delimiting_policy: EncodingAuditSelfDelimitingPolicy,
    pub malformed_input_behavior: EncodingAuditMalformedInputBehavior,
    pub input_size_theorem_hashes: Vec<Hash>,
    pub output_size_theorem_hashes: Vec<Hash>,
    pub translation_theorem_hashes: Vec<Hash>,
    pub source_free_verification_hashes: Vec<Hash>,
    pub complexity_obligation_hashes: Vec<Hash>,
    pub blockers: Vec<EncodingAuditBlocker>,
    pub audit_decision: EncodingAuditDecision,
    pub rejection_reason_hash: Option<Hash>,
    pub creates_theorem_declarations: bool,
    pub creates_verified_artifacts: bool,
    pub releases_dependencies: bool,
    pub creates_proof_acceptance: bool,
    pub wall_clock_time: Option<String>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingAuditFoundationReference {
    pub module_name: String,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub source_free_verification_hash: Hash,
    pub reused_not_redeclared: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingAuditTheoremReference {
    pub theorem_declaration: String,
    pub statement_hash: Hash,
    pub certificate_hash: Hash,
    pub source_free_verification_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingAuditBlocker {
    pub blocker_key: String,
    pub blocker_hash: Hash,
    pub reason: String,
    pub prerequisite_task_key: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EncodingAuditRepresentationClass {
    Unary,
    Binary,
    SelfDelimiting,
    Composite,
}

impl EncodingAuditRepresentationClass {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Unary => "unary",
            Self::Binary => "binary",
            Self::SelfDelimiting => "self_delimiting",
            Self::Composite => "composite",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "unary" => Some(Self::Unary),
            "binary" => Some(Self::Binary),
            "self_delimiting" => Some(Self::SelfDelimiting),
            "composite" => Some(Self::Composite),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EncodingAuditSelfDelimitingPolicy {
    NotApplicable,
    FixedWidth,
    LengthPrefix,
    PrefixFree,
    DelimiterEscaped,
}

impl EncodingAuditSelfDelimitingPolicy {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::NotApplicable => "not_applicable",
            Self::FixedWidth => "fixed_width",
            Self::LengthPrefix => "length_prefix",
            Self::PrefixFree => "prefix_free",
            Self::DelimiterEscaped => "delimiter_escaped",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "not_applicable" => Some(Self::NotApplicable),
            "fixed_width" => Some(Self::FixedWidth),
            "length_prefix" => Some(Self::LengthPrefix),
            "prefix_free" => Some(Self::PrefixFree),
            "delimiter_escaped" => Some(Self::DelimiterEscaped),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EncodingAuditMalformedInputBehavior {
    RejectWithNone,
    RejectWithError,
    NormalizeCanonical,
    OutOfScopeBlocker,
}

impl EncodingAuditMalformedInputBehavior {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::RejectWithNone => "reject_with_none",
            Self::RejectWithError => "reject_with_error",
            Self::NormalizeCanonical => "normalize_canonical",
            Self::OutOfScopeBlocker => "out_of_scope_blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "reject_with_none" => Some(Self::RejectWithNone),
            "reject_with_error" => Some(Self::RejectWithError),
            "normalize_canonical" => Some(Self::NormalizeCanonical),
            "out_of_scope_blocker" => Some(Self::OutOfScopeBlocker),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EncodingAuditDecision {
    VerifiedByReferences,
    Blocked,
    Rejected,
}

impl EncodingAuditDecision {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::VerifiedByReferences => "verified_by_references",
            Self::Blocked => "blocked",
            Self::Rejected => "rejected",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "verified_by_references" => Some(Self::VerifiedByReferences),
            "blocked" => Some(Self::Blocked),
            "rejected" => Some(Self::Rejected),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingAuditSchemaError {
    path: String,
    kind: EncodingAuditSchemaErrorKind,
}

impl EncodingAuditSchemaError {
    fn new(path: impl Into<String>, kind: EncodingAuditSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &EncodingAuditSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for EncodingAuditSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "encoding audit schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for EncodingAuditSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodingAuditSchemaErrorKind {
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
    InvalidRepresentationClass { value: String },
    InvalidSelfDelimitingPolicy { value: String },
    InvalidMalformedInputBehavior { value: String },
    InvalidAuditDecision { value: String },
}

impl fmt::Display for EncodingAuditSchemaErrorKind {
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
            Self::InvalidRepresentationClass { value } => {
                write!(f, "invalid representation class `{value}`")
            }
            Self::InvalidSelfDelimitingPolicy { value } => {
                write!(f, "invalid self-delimiting policy `{value}`")
            }
            Self::InvalidMalformedInputBehavior { value } => {
                write!(f, "invalid malformed-input behavior `{value}`")
            }
            Self::InvalidAuditDecision { value } => {
                write!(f, "invalid encoding audit decision `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingAuditValidationError {
    kind: EncodingAuditValidationErrorKind,
}

impl EncodingAuditValidationError {
    fn new(kind: EncodingAuditValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &EncodingAuditValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for EncodingAuditValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "encoding audit validation error: {}", self.kind)
    }
}

impl std::error::Error for EncodingAuditValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodingAuditValidationErrorKind {
    EmptyRequiredField { field: &'static str },
    SidecarBoundaryViolation { field: &'static str },
    MissingFoundationReference { module_name: &'static str },
    DuplicateFoundationReference { module_name: String },
    UnexpectedFoundationReference { module_name: String },
    FoundationReferenceUnderComplexityNamespace { module_name: String },
    FoundationReferenceNotReused { module_name: String },
    MissingBridgeTheoremReference,
    DuplicateBridgeTheoremReference { theorem_declaration: String },
    BridgeTheoremOutsideEncodingNamespace { theorem_declaration: String },
    MissingEvidence { field: &'static str },
    DuplicateEvidenceHash { field: &'static str, hash: String },
    DuplicateBlocker { blocker_key: String },
    SelfDelimitingPolicyRequired,
    MalformedOutOfScopeRequiresBlocker,
    VerifiedAuditCannotHaveBlockers,
    VerifiedAuditCannotHaveRejection,
    BlockedAuditRequiresBlocker,
    RejectedAuditRequiresReason,
}

impl fmt::Display for EncodingAuditValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::SidecarBoundaryViolation { field } => {
                write!(f, "encoding audit violates sidecar boundary via `{field}`")
            }
            Self::MissingFoundationReference { module_name } => {
                write!(f, "missing foundation reference `{module_name}`")
            }
            Self::DuplicateFoundationReference { module_name } => {
                write!(f, "duplicate foundation reference `{module_name}`")
            }
            Self::UnexpectedFoundationReference { module_name } => {
                write!(f, "unexpected foundation reference `{module_name}`")
            }
            Self::FoundationReferenceUnderComplexityNamespace { module_name } => write!(
                f,
                "foundation reference `{module_name}` must not be redeclared under Proofs.Ai.Complexity"
            ),
            Self::FoundationReferenceNotReused { module_name } => {
                write!(f, "foundation reference `{module_name}` is not marked reused")
            }
            Self::MissingBridgeTheoremReference => write!(
                f,
                "encoding audit requires checked Proofs.Ai.Complexity.Encoding bridge references"
            ),
            Self::DuplicateBridgeTheoremReference {
                theorem_declaration,
            } => write!(
                f,
                "duplicate encoding bridge theorem reference `{theorem_declaration}`"
            ),
            Self::BridgeTheoremOutsideEncodingNamespace {
                theorem_declaration,
            } => write!(
                f,
                "bridge theorem `{theorem_declaration}` is outside Proofs.Ai.Complexity.Encoding"
            ),
            Self::MissingEvidence { field } => write!(f, "missing evidence `{field}`"),
            Self::DuplicateEvidenceHash { field, hash } => {
                write!(f, "duplicate hash `{hash}` in `{field}`")
            }
            Self::DuplicateBlocker { blocker_key } => {
                write!(f, "duplicate blocker `{blocker_key}`")
            }
            Self::SelfDelimitingPolicyRequired => write!(
                f,
                "self-delimiting representation requires an explicit nontrivial policy"
            ),
            Self::MalformedOutOfScopeRequiresBlocker => write!(
                f,
                "out-of-scope malformed-input behavior requires blocked decision and blocker"
            ),
            Self::VerifiedAuditCannotHaveBlockers => {
                write!(f, "verified encoding audit cannot carry blockers")
            }
            Self::VerifiedAuditCannotHaveRejection => {
                write!(f, "verified encoding audit cannot carry rejection reason")
            }
            Self::BlockedAuditRequiresBlocker => {
                write!(f, "blocked encoding audit requires at least one blocker")
            }
            Self::RejectedAuditRequiresReason => {
                write!(f, "rejected encoding audit requires a rejection reason hash")
            }
        }
    }
}

pub fn parse_encoding_audit_record(
    source: &str,
) -> Result<EncodingAuditRecord, EncodingAuditSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != ENCODING_AUDIT_RECORD_API_VERSION {
        return Err(EncodingAuditSchemaError::new(
            "$.api_version",
            EncodingAuditSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(EncodingAuditRecord {
        api_version,
        audit_key: required_string(&root, "audit_key", "$")?,
        subject_hash: required_hash(&root, "subject_hash", "$")?,
        route_package_hash: optional_hash(&root, "route_package_hash", "$")?,
        theorem_card_hash: optional_hash(&root, "theorem_card_hash", "$")?,
        foundation_references: parse_foundation_references(required_value(
            &root,
            "foundation_references",
            "$",
        )?)?,
        bridge_theorem_references: parse_theorem_references(required_value(
            &root,
            "bridge_theorem_references",
            "$",
        )?)?,
        codec_identity_hash: required_hash(&root, "codec_identity_hash", "$")?,
        representation_class: parse_representation_class_value(
            required_value(&root, "representation_class", "$")?,
            "$.representation_class",
        )?,
        representation_choice_hash: required_hash(&root, "representation_choice_hash", "$")?,
        self_delimiting_policy: parse_self_delimiting_policy_value(
            required_value(&root, "self_delimiting_policy", "$")?,
            "$.self_delimiting_policy",
        )?,
        malformed_input_behavior: parse_malformed_input_behavior_value(
            required_value(&root, "malformed_input_behavior", "$")?,
            "$.malformed_input_behavior",
        )?,
        input_size_theorem_hashes: parse_hash_array(
            required_value(&root, "input_size_theorem_hashes", "$")?,
            "$.input_size_theorem_hashes",
        )?,
        output_size_theorem_hashes: parse_hash_array(
            required_value(&root, "output_size_theorem_hashes", "$")?,
            "$.output_size_theorem_hashes",
        )?,
        translation_theorem_hashes: parse_hash_array(
            required_value(&root, "translation_theorem_hashes", "$")?,
            "$.translation_theorem_hashes",
        )?,
        source_free_verification_hashes: parse_hash_array(
            required_value(&root, "source_free_verification_hashes", "$")?,
            "$.source_free_verification_hashes",
        )?,
        complexity_obligation_hashes: parse_hash_array(
            required_value(&root, "complexity_obligation_hashes", "$")?,
            "$.complexity_obligation_hashes",
        )?,
        blockers: parse_blockers(required_value(&root, "blockers", "$")?)?,
        audit_decision: parse_audit_decision_value(
            required_value(&root, "audit_decision", "$")?,
            "$.audit_decision",
        )?,
        rejection_reason_hash: optional_hash(&root, "rejection_reason_hash", "$")?,
        creates_theorem_declarations: required_bool(&root, "creates_theorem_declarations", "$")?,
        creates_verified_artifacts: required_bool(&root, "creates_verified_artifacts", "$")?,
        releases_dependencies: required_bool(&root, "releases_dependencies", "$")?,
        creates_proof_acceptance: required_bool(&root, "creates_proof_acceptance", "$")?,
        wall_clock_time: optional_string(&root, "wall_clock_time", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_encoding_audit_record(
    record: &EncodingAuditRecord,
) -> Result<(), EncodingAuditValidationError> {
    require_non_empty(&record.audit_key, "audit_key")?;
    validate_sidecar_boundary(record)?;
    validate_foundation_references(&record.foundation_references)?;
    validate_bridge_theorem_references(&record.bridge_theorem_references)?;
    require_hash_evidence(
        &record.input_size_theorem_hashes,
        "input_size_theorem_hashes",
    )?;
    require_hash_evidence(
        &record.output_size_theorem_hashes,
        "output_size_theorem_hashes",
    )?;
    require_hash_evidence(
        &record.translation_theorem_hashes,
        "translation_theorem_hashes",
    )?;
    require_hash_evidence(
        &record.source_free_verification_hashes,
        "source_free_verification_hashes",
    )?;
    require_hash_evidence(
        &record.complexity_obligation_hashes,
        "complexity_obligation_hashes",
    )?;
    validate_blockers(&record.blockers)?;
    validate_representation(record)?;
    validate_decision(record)?;
    Ok(())
}

pub fn encoding_audit_record_canonical_identity_bytes(record: &EncodingAuditRecord) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, ENCODING_AUDIT_RECORD_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "audit_key");
    encode_string_to(&mut out, &record.audit_key);
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
    encode_foundation_references_to(&mut out, &record.foundation_references);
    encode_theorem_references_to(&mut out, &record.bridge_theorem_references);
    encode_string_to(&mut out, "codec_identity_hash");
    encode_hash_to(&mut out, &record.codec_identity_hash);
    encode_string_to(&mut out, "representation_class");
    encode_string_to(&mut out, record.representation_class.wire());
    encode_string_to(&mut out, "representation_choice_hash");
    encode_hash_to(&mut out, &record.representation_choice_hash);
    encode_string_to(&mut out, "self_delimiting_policy");
    encode_string_to(&mut out, record.self_delimiting_policy.wire());
    encode_string_to(&mut out, "malformed_input_behavior");
    encode_string_to(&mut out, record.malformed_input_behavior.wire());
    encode_hash_list_to(
        &mut out,
        "input_size_theorem_hashes",
        &record.input_size_theorem_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "output_size_theorem_hashes",
        &record.output_size_theorem_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "translation_theorem_hashes",
        &record.translation_theorem_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "source_free_verification_hashes",
        &record.source_free_verification_hashes,
    );
    encode_hash_list_to(
        &mut out,
        "complexity_obligation_hashes",
        &record.complexity_obligation_hashes,
    );
    encode_blockers_to(&mut out, &record.blockers);
    encode_string_to(&mut out, "audit_decision");
    encode_string_to(&mut out, record.audit_decision.wire());
    encode_option_hash_to(
        &mut out,
        "rejection_reason_hash",
        record.rejection_reason_hash.as_ref(),
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

pub fn encoding_audit_record_hash(record: &EncodingAuditRecord) -> Hash {
    let digest = Sha256::digest(encoding_audit_record_canonical_identity_bytes(record));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn encoding_audit_record_hash_string(record: &EncodingAuditRecord) -> String {
    format_hash_string(&encoding_audit_record_hash(record))
}

fn validate_sidecar_boundary(
    record: &EncodingAuditRecord,
) -> Result<(), EncodingAuditValidationError> {
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
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::SidecarBoundaryViolation { field },
            ));
        }
    }
    Ok(())
}

fn validate_foundation_references(
    references: &[EncodingAuditFoundationReference],
) -> Result<(), EncodingAuditValidationError> {
    let mut seen = BTreeSet::new();
    for reference in references {
        require_non_empty(&reference.module_name, "foundation_references.module_name")?;
        if reference
            .module_name
            .starts_with(COMPLEXITY_NAMESPACE_PREFIX)
        {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::FoundationReferenceUnderComplexityNamespace {
                    module_name: reference.module_name.clone(),
                },
            ));
        }
        if !REQUIRED_FOUNDATION_MODULES.contains(&reference.module_name.as_str()) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::UnexpectedFoundationReference {
                    module_name: reference.module_name.clone(),
                },
            ));
        }
        if !reference.reused_not_redeclared {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::FoundationReferenceNotReused {
                    module_name: reference.module_name.clone(),
                },
            ));
        }
        if !seen.insert(reference.module_name.as_str()) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::DuplicateFoundationReference {
                    module_name: reference.module_name.clone(),
                },
            ));
        }
    }
    for module_name in REQUIRED_FOUNDATION_MODULES {
        if !seen.contains(module_name) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::MissingFoundationReference { module_name },
            ));
        }
    }
    Ok(())
}

fn validate_bridge_theorem_references(
    references: &[EncodingAuditTheoremReference],
) -> Result<(), EncodingAuditValidationError> {
    if references.is_empty() {
        return Err(EncodingAuditValidationError::new(
            EncodingAuditValidationErrorKind::MissingBridgeTheoremReference,
        ));
    }
    let mut seen = BTreeSet::new();
    for reference in references {
        require_non_empty(
            &reference.theorem_declaration,
            "bridge_theorem_references.theorem_declaration",
        )?;
        if !reference
            .theorem_declaration
            .starts_with(COMPLEXITY_ENCODING_NAMESPACE)
        {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::BridgeTheoremOutsideEncodingNamespace {
                    theorem_declaration: reference.theorem_declaration.clone(),
                },
            ));
        }
        if !seen.insert(reference.theorem_declaration.as_str()) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::DuplicateBridgeTheoremReference {
                    theorem_declaration: reference.theorem_declaration.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn require_hash_evidence(
    hashes: &[Hash],
    field: &'static str,
) -> Result<(), EncodingAuditValidationError> {
    if hashes.is_empty() {
        return Err(EncodingAuditValidationError::new(
            EncodingAuditValidationErrorKind::MissingEvidence { field },
        ));
    }
    let mut seen = BTreeSet::new();
    for hash in hashes {
        if !seen.insert(*hash) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::DuplicateEvidenceHash {
                    field,
                    hash: format_hash_string(hash),
                },
            ));
        }
    }
    Ok(())
}

fn validate_blockers(
    blockers: &[EncodingAuditBlocker],
) -> Result<(), EncodingAuditValidationError> {
    let mut seen = BTreeSet::new();
    for blocker in blockers {
        require_non_empty(&blocker.blocker_key, "blockers.blocker_key")?;
        require_non_empty(&blocker.reason, "blockers.reason")?;
        if !seen.insert(blocker.blocker_key.as_str()) {
            return Err(EncodingAuditValidationError::new(
                EncodingAuditValidationErrorKind::DuplicateBlocker {
                    blocker_key: blocker.blocker_key.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn validate_representation(
    record: &EncodingAuditRecord,
) -> Result<(), EncodingAuditValidationError> {
    if record.representation_class == EncodingAuditRepresentationClass::SelfDelimiting
        && record.self_delimiting_policy == EncodingAuditSelfDelimitingPolicy::NotApplicable
    {
        return Err(EncodingAuditValidationError::new(
            EncodingAuditValidationErrorKind::SelfDelimitingPolicyRequired,
        ));
    }
    if record.malformed_input_behavior == EncodingAuditMalformedInputBehavior::OutOfScopeBlocker
        && (record.audit_decision != EncodingAuditDecision::Blocked || record.blockers.is_empty())
    {
        return Err(EncodingAuditValidationError::new(
            EncodingAuditValidationErrorKind::MalformedOutOfScopeRequiresBlocker,
        ));
    }
    Ok(())
}

fn validate_decision(record: &EncodingAuditRecord) -> Result<(), EncodingAuditValidationError> {
    match record.audit_decision {
        EncodingAuditDecision::VerifiedByReferences => {
            if !record.blockers.is_empty() {
                return Err(EncodingAuditValidationError::new(
                    EncodingAuditValidationErrorKind::VerifiedAuditCannotHaveBlockers,
                ));
            }
            if record.rejection_reason_hash.is_some() {
                return Err(EncodingAuditValidationError::new(
                    EncodingAuditValidationErrorKind::VerifiedAuditCannotHaveRejection,
                ));
            }
        }
        EncodingAuditDecision::Blocked => {
            if record.blockers.is_empty() {
                return Err(EncodingAuditValidationError::new(
                    EncodingAuditValidationErrorKind::BlockedAuditRequiresBlocker,
                ));
            }
        }
        EncodingAuditDecision::Rejected => {
            if record.rejection_reason_hash.is_none() {
                return Err(EncodingAuditValidationError::new(
                    EncodingAuditValidationErrorKind::RejectedAuditRequiresReason,
                ));
            }
        }
    }
    Ok(())
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, EncodingAuditSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        EncodingAuditSchemaError::new(
            "$",
            EncodingAuditSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, EncodingAuditSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(EncodingAuditSchemaError::new(
                format!("{path}.{}", member.key()),
                EncodingAuditSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(EncodingAuditSchemaError::new(
                format!("{path}.{}", member.key()),
                EncodingAuditSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], EncodingAuditSchemaError> {
    value.array_elements().ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, EncodingAuditSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        EncodingAuditSchemaError::new(
            format!("{path}.{field}"),
            EncodingAuditSchemaErrorKind::MissingField { field },
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
) -> Result<String, EncodingAuditSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, EncodingAuditSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, EncodingAuditSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, EncodingAuditSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, EncodingAuditSchemaError> {
    value.bool_value().ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, EncodingAuditSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, EncodingAuditSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, EncodingAuditSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_foundation_references(
    value: &JsonValue<'_>,
) -> Result<Vec<EncodingAuditFoundationReference>, EncodingAuditSchemaError> {
    array_elements(value, "$.foundation_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_foundation_reference(value, &format!("$.foundation_references[{index}]"))
        })
        .collect()
}

fn parse_foundation_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditFoundationReference, EncodingAuditSchemaError> {
    let members = object_map(value, path, FOUNDATION_REFERENCE_FIELDS)?;
    Ok(EncodingAuditFoundationReference {
        module_name: required_string(&members, "module_name", path)?,
        certificate_hash: required_hash(&members, "certificate_hash", path)?,
        export_hash: required_hash(&members, "export_hash", path)?,
        source_free_verification_hash: required_hash(
            &members,
            "source_free_verification_hash",
            path,
        )?,
        reused_not_redeclared: required_bool(&members, "reused_not_redeclared", path)?,
    })
}

fn parse_theorem_references(
    value: &JsonValue<'_>,
) -> Result<Vec<EncodingAuditTheoremReference>, EncodingAuditSchemaError> {
    array_elements(value, "$.bridge_theorem_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_theorem_reference(value, &format!("$.bridge_theorem_references[{index}]"))
        })
        .collect()
}

fn parse_theorem_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditTheoremReference, EncodingAuditSchemaError> {
    let members = object_map(value, path, THEOREM_REFERENCE_FIELDS)?;
    Ok(EncodingAuditTheoremReference {
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
) -> Result<Vec<EncodingAuditBlocker>, EncodingAuditSchemaError> {
    array_elements(value, "$.blockers")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_blocker(value, &format!("$.blockers[{index}]")))
        .collect()
}

fn parse_blocker(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditBlocker, EncodingAuditSchemaError> {
    let members = object_map(value, path, BLOCKER_FIELDS)?;
    Ok(EncodingAuditBlocker {
        blocker_key: required_string(&members, "blocker_key", path)?,
        blocker_hash: required_hash(&members, "blocker_hash", path)?,
        reason: required_string(&members, "reason", path)?,
        prerequisite_task_key: optional_string(&members, "prerequisite_task_key", path)?,
    })
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, EncodingAuditSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_representation_class_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditRepresentationClass, EncodingAuditSchemaError> {
    let wire = string_value(value, path)?;
    EncodingAuditRepresentationClass::parse(&wire).ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::InvalidRepresentationClass { value: wire },
        )
    })
}

fn parse_self_delimiting_policy_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditSelfDelimitingPolicy, EncodingAuditSchemaError> {
    let wire = string_value(value, path)?;
    EncodingAuditSelfDelimitingPolicy::parse(&wire).ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::InvalidSelfDelimitingPolicy { value: wire },
        )
    })
}

fn parse_malformed_input_behavior_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditMalformedInputBehavior, EncodingAuditSchemaError> {
    let wire = string_value(value, path)?;
    EncodingAuditMalformedInputBehavior::parse(&wire).ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::InvalidMalformedInputBehavior { value: wire },
        )
    })
}

fn parse_audit_decision_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<EncodingAuditDecision, EncodingAuditSchemaError> {
    let wire = string_value(value, path)?;
    EncodingAuditDecision::parse(&wire).ok_or_else(|| {
        EncodingAuditSchemaError::new(
            path,
            EncodingAuditSchemaErrorKind::InvalidAuditDecision { value: wire },
        )
    })
}

fn require_non_empty(value: &str, field: &'static str) -> Result<(), EncodingAuditValidationError> {
    if value.trim().is_empty() {
        return Err(EncodingAuditValidationError::new(
            EncodingAuditValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_foundation_references_to(
    out: &mut Vec<u8>,
    references: &[EncodingAuditFoundationReference],
) {
    encode_string_to(out, "foundation_references");
    let mut references = references.to_vec();
    references.sort_by(|left, right| left.module_name.cmp(&right.module_name));
    encode_len_to(out, references.len());
    for reference in &references {
        encode_string_to(out, &reference.module_name);
        encode_hash_to(out, &reference.certificate_hash);
        encode_hash_to(out, &reference.export_hash);
        encode_hash_to(out, &reference.source_free_verification_hash);
        out.push(u8::from(reference.reused_not_redeclared));
    }
}

fn encode_theorem_references_to(out: &mut Vec<u8>, references: &[EncodingAuditTheoremReference]) {
    encode_string_to(out, "bridge_theorem_references");
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

fn encode_blockers_to(out: &mut Vec<u8>, blockers: &[EncodingAuditBlocker]) {
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
            .join("../npa/develop/proof-using-agents/fixtures/pua-m16-encoding-audit")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("encoding audit fixture should exist")
    }

    fn parse_fixture(name: &str) -> EncodingAuditRecord {
        parse_encoding_audit_record(&fixture(name)).expect("encoding audit fixture should parse")
    }

    #[test]
    fn encoding_audit_record_reuses_foundation_modules() {
        let record = parse_fixture("valid-bitstring-binary-audit.json");
        validate_encoding_audit_record(&record).expect("encoding audit validates");

        for module_name in REQUIRED_FOUNDATION_MODULES {
            assert!(record
                .foundation_references
                .iter()
                .any(|reference| reference.module_name == *module_name
                    && reference.reused_not_redeclared));
        }
        assert!(record
            .bridge_theorem_references
            .iter()
            .all(|reference| reference
                .theorem_declaration
                .starts_with(COMPLEXITY_ENCODING_NAMESPACE)));

        let mut display_changed = record.clone();
        display_changed.display_text = Some("human-only wording changed".to_owned());
        display_changed.wall_clock_time = Some("2099-12-31T23:59:59Z".to_owned());
        assert_eq!(
            encoding_audit_record_hash(&record),
            encoding_audit_record_hash(&display_changed)
        );

        let unary = parse_fixture("valid-unary-representation-audit.json");
        validate_encoding_audit_record(&unary).expect("unary encoding audit validates");
        assert_eq!(
            unary.representation_class,
            EncodingAuditRepresentationClass::Unary
        );
    }

    #[test]
    fn encoding_audit_record_rejects_proof_acceptance() {
        let record = parse_fixture("invalid-proof-acceptance.json");
        assert!(matches!(
            validate_encoding_audit_record(&record).map_err(|error| error.kind().clone()),
            Err(EncodingAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "creates_proof_acceptance"
            })
        ));

        let mut verified_artifact = parse_fixture("valid-bitstring-binary-audit.json");
        verified_artifact.creates_verified_artifacts = true;
        assert!(matches!(
            validate_encoding_audit_record(&verified_artifact)
                .map_err(|error| error.kind().clone()),
            Err(EncodingAuditValidationErrorKind::SidecarBoundaryViolation {
                field: "creates_verified_artifacts"
            })
        ));
    }

    #[test]
    fn encoding_audit_record_requires_size_and_malformed_behavior() {
        let missing_size = parse_fixture("invalid-missing-size-theorem.json");
        assert!(matches!(
            validate_encoding_audit_record(&missing_size).map_err(|error| error.kind().clone()),
            Err(EncodingAuditValidationErrorKind::MissingEvidence {
                field: "input_size_theorem_hashes"
            })
        ));

        let self_delimiting = parse_fixture("valid-self-delimiting-translation-audit.json");
        validate_encoding_audit_record(&self_delimiting)
            .expect("self-delimiting encoding audit validates");
        assert_eq!(
            self_delimiting.representation_class,
            EncodingAuditRepresentationClass::SelfDelimiting
        );
        assert_ne!(
            self_delimiting.self_delimiting_policy,
            EncodingAuditSelfDelimitingPolicy::NotApplicable
        );

        let mut malformed_without_blocker = self_delimiting;
        malformed_without_blocker.malformed_input_behavior =
            EncodingAuditMalformedInputBehavior::OutOfScopeBlocker;
        assert!(matches!(
            validate_encoding_audit_record(&malformed_without_blocker)
                .map_err(|error| error.kind().clone()),
            Err(EncodingAuditValidationErrorKind::MalformedOutOfScopeRequiresBlocker)
        ));
    }
}

use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::research_evidence::ResearchEvidenceLevel;
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const COUNTEREXAMPLE_RESULT_API_VERSION: &str = "npa.counterexample-result.v1";
pub const COUNTEREXAMPLE_SEARCH_PROFILE_HASH_DOMAIN: &str =
    "npa.counterexample-search-profile.identity.v1";
pub const COUNTEREXAMPLE_RESULT_HASH_DOMAIN: &str = "npa.counterexample-result.identity.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "result_key",
    "target_key",
    "statement_hash",
    "status",
    "search_profile",
    "search_profile_hash",
    "evidence_level",
    "candidate_proof_action",
    "proof_status_advanced",
    "witness_artifact_hash",
    "checked_domain",
    "formal_counterexample_certificate_hash",
    "formal_counterexample_handoff",
    "result_hash",
    "display_text",
];
const SEARCH_PROFILE_FIELDS: &[&str] = &[
    "domain_hash",
    "bounds_hash",
    "evaluator_identity_hash",
    "seed_policy_hash",
    "environment_hash",
    "finite_carrier",
    "parameter_range",
    "domain_supported",
    "evaluator_checked",
    "decision_procedure_verified",
    "profile_current",
];
const CHECKED_DOMAIN_FIELDS: &[&str] = &[
    "domain_hash",
    "bounds_hash",
    "evaluator_identity_hash",
    "finite_carrier",
    "parameter_range",
];
const FORMAL_HANDOFF_FIELDS: &[&str] = &[
    "module_name",
    "theorem_name",
    "source_path",
    "source_hash",
    "certificate_path",
    "certificate_hash",
    "meta_path",
    "meta_hash",
    "replay_path",
    "replay_hash",
    "source_free_verification_hash",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleResult {
    pub api_version: String,
    pub result_key: String,
    pub target_key: String,
    pub statement_hash: Hash,
    pub status: CounterexampleGateStatus,
    pub search_profile: CounterexampleSearchProfile,
    pub search_profile_hash: Hash,
    pub evidence_level: ResearchEvidenceLevel,
    pub candidate_proof_action: CounterexampleGateProofAction,
    pub proof_status_advanced: bool,
    pub witness_artifact_hash: Option<Hash>,
    pub checked_domain: Option<CounterexampleCheckedDomain>,
    pub formal_counterexample_certificate_hash: Option<Hash>,
    pub formal_counterexample_handoff: Option<CounterexampleFormalHandoff>,
    pub result_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleSearchProfile {
    pub domain_hash: Hash,
    pub bounds_hash: Hash,
    pub evaluator_identity_hash: Hash,
    pub seed_policy_hash: Hash,
    pub environment_hash: Hash,
    pub finite_carrier: String,
    pub parameter_range: String,
    pub domain_supported: bool,
    pub evaluator_checked: bool,
    pub decision_procedure_verified: bool,
    pub profile_current: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleCheckedDomain {
    pub domain_hash: Hash,
    pub bounds_hash: Hash,
    pub evaluator_identity_hash: Hash,
    pub finite_carrier: String,
    pub parameter_range: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleFormalHandoff {
    pub module_name: String,
    pub theorem_name: String,
    pub source_path: String,
    pub source_hash: Hash,
    pub certificate_path: String,
    pub certificate_hash: Hash,
    pub meta_path: String,
    pub meta_hash: Hash,
    pub replay_path: String,
    pub replay_hash: Hash,
    pub source_free_verification_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CounterexampleGateStatus {
    Found,
    NotFoundWithinBound,
    Unsupported,
    Inconclusive,
}

impl CounterexampleGateStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Found => "found",
            Self::NotFoundWithinBound => "not_found_within_bound",
            Self::Unsupported => "unsupported",
            Self::Inconclusive => "inconclusive",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "found" => Some(Self::Found),
            "not_found_within_bound" => Some(Self::NotFoundWithinBound),
            "unsupported" => Some(Self::Unsupported),
            "inconclusive" => Some(Self::Inconclusive),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CounterexampleGateProofAction {
    Continue,
    Defer,
    Stop,
}

impl CounterexampleGateProofAction {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Continue => "continue",
            Self::Defer => "defer",
            Self::Stop => "stop",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "continue" => Some(Self::Continue),
            "defer" => Some(Self::Defer),
            "stop" => Some(Self::Stop),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleResultSchemaError {
    path: String,
    kind: CounterexampleResultSchemaErrorKind,
}

impl CounterexampleResultSchemaError {
    fn new(path: impl Into<String>, kind: CounterexampleResultSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &CounterexampleResultSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for CounterexampleResultSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for CounterexampleResultSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CounterexampleResultSchemaErrorKind {
    JsonParse { offset: usize },
    ExpectedObject { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    MissingField { field: &'static str },
    DuplicateKey { key: String },
    UnknownField { field: String },
    InvalidApiVersion { value: String },
    InvalidStatus { value: String },
    InvalidProofAction { value: String },
    InvalidEvidenceLevel { value: String },
    InvalidHash { value: String },
}

impl fmt::Display for CounterexampleResultSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "JSON parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, got {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, got {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, got {actual:?}"),
            Self::MissingField { field } => write!(f, "missing required field `{field}`"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::InvalidApiVersion { value } => {
                write!(f, "invalid counterexample-result API version `{value}`")
            }
            Self::InvalidStatus { value } => write!(f, "invalid counterexample status `{value}`"),
            Self::InvalidProofAction { value } => {
                write!(f, "invalid proof-search action `{value}`")
            }
            Self::InvalidEvidenceLevel { value } => write!(f, "invalid evidence level `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleGateValidationError {
    kind: CounterexampleGateValidationErrorKind,
}

impl CounterexampleGateValidationError {
    fn new(kind: CounterexampleGateValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &CounterexampleGateValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for CounterexampleGateValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for CounterexampleGateValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CounterexampleGateValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    SearchProfileHashMismatch {
        declared: String,
        computed: String,
    },
    ResultHashMismatch {
        declared: String,
        computed: String,
    },
    StaleSearchProfile,
    UncheckedEvaluator {
        status: CounterexampleGateStatus,
    },
    UnsupportedDomainCannotProduceSearchResult {
        status: CounterexampleGateStatus,
    },
    UnsupportedStatusRequiresUnsupportedDomain,
    FoundRequiresWitnessArtifact,
    FoundRequiresCheckedDomain,
    CheckedDomainMismatch {
        field: &'static str,
    },
    FoundCounterexampleMustStopOrDefer,
    NonFoundCannotCarryWitness,
    NonFoundCannotCarryFormalCounterexample,
    NonFoundCannotStopProofSearch,
    GateResultCannotAdvanceProofStatus,
    NotFoundWithinBoundIsNotProof,
    FormalCounterexampleCertificateRequiresFound,
    FormalCounterexampleRequiresHandoff,
    FormalCounterexampleCertificateMismatch {
        declared: String,
        handoff: String,
    },
    HandoffWithoutCertificateHash,
    InvalidHandoffPath {
        field: &'static str,
        path: String,
        expected_suffix: &'static str,
    },
}

impl fmt::Display for CounterexampleGateValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "required field `{field}` is empty"),
            Self::SearchProfileHashMismatch { declared, computed } => write!(
                f,
                "search profile hash mismatch: declared {declared}, computed {computed}"
            ),
            Self::ResultHashMismatch { declared, computed } => write!(
                f,
                "counterexample result hash mismatch: declared {declared}, computed {computed}"
            ),
            Self::StaleSearchProfile => write!(f, "search profile is stale"),
            Self::UncheckedEvaluator { status } => {
                write!(f, "{status:?} result requires a checked evaluator or decision procedure")
            }
            Self::UnsupportedDomainCannotProduceSearchResult { status } => {
                write!(f, "{status:?} cannot be produced for an unsupported domain")
            }
            Self::UnsupportedStatusRequiresUnsupportedDomain => {
                write!(f, "unsupported status requires domain_supported=false")
            }
            Self::FoundRequiresWitnessArtifact => {
                write!(f, "found counterexample requires witness artifact hash")
            }
            Self::FoundRequiresCheckedDomain => {
                write!(f, "found counterexample requires checked domain")
            }
            Self::CheckedDomainMismatch { field } => {
                write!(f, "checked domain field `{field}` does not match search profile")
            }
            Self::FoundCounterexampleMustStopOrDefer => {
                write!(f, "found counterexample must stop or defer candidate proof search")
            }
            Self::NonFoundCannotCarryWitness => {
                write!(f, "non-found counterexample result cannot carry a witness artifact")
            }
            Self::NonFoundCannotCarryFormalCounterexample => {
                write!(f, "non-found counterexample result cannot carry a formal certificate")
            }
            Self::NonFoundCannotStopProofSearch => {
                write!(f, "non-found counterexample result cannot stop proof search")
            }
            Self::GateResultCannotAdvanceProofStatus => {
                write!(f, "counterexample gate result cannot advance proof status")
            }
            Self::NotFoundWithinBoundIsNotProof => {
                write!(f, "not_found_within_bound is bounded search evidence, not proof")
            }
            Self::FormalCounterexampleCertificateRequiresFound => {
                write!(f, "formal counterexample certificate is only allowed for found results")
            }
            Self::FormalCounterexampleRequiresHandoff => {
                write!(f, "formal counterexample certificate requires checked theorem handoff")
            }
            Self::FormalCounterexampleCertificateMismatch { declared, handoff } => write!(
                f,
                "formal certificate hash mismatch: declared {declared}, handoff {handoff}"
            ),
            Self::HandoffWithoutCertificateHash => {
                write!(f, "formal handoff requires formal_counterexample_certificate_hash")
            }
            Self::InvalidHandoffPath {
                field,
                path,
                expected_suffix,
            } => write!(
                f,
                "formal handoff path `{field}` has invalid path `{path}`, expected suffix `{expected_suffix}`"
            ),
        }
    }
}

pub fn parse_counterexample_result(
    source: &str,
) -> Result<CounterexampleResult, CounterexampleResultSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != COUNTEREXAMPLE_RESULT_API_VERSION {
        return Err(CounterexampleResultSchemaError::new(
            "$.api_version",
            CounterexampleResultSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(CounterexampleResult {
        api_version,
        result_key: required_string(&root, "result_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        statement_hash: required_hash(&root, "statement_hash", "$")?,
        status: required_status(&root, "status", "$")?,
        search_profile: parse_search_profile(required_value(&root, "search_profile", "$")?)?,
        search_profile_hash: required_hash(&root, "search_profile_hash", "$")?,
        evidence_level: required_evidence_level(&root, "evidence_level", "$")?,
        candidate_proof_action: required_proof_action(&root, "candidate_proof_action", "$")?,
        proof_status_advanced: required_bool(&root, "proof_status_advanced", "$")?,
        witness_artifact_hash: optional_hash(&root, "witness_artifact_hash", "$")?,
        checked_domain: optional_value(&root, "checked_domain")
            .map(parse_checked_domain)
            .transpose()?,
        formal_counterexample_certificate_hash: optional_hash(
            &root,
            "formal_counterexample_certificate_hash",
            "$",
        )?,
        formal_counterexample_handoff: optional_value(&root, "formal_counterexample_handoff")
            .map(parse_formal_handoff)
            .transpose()?,
        result_hash: required_hash(&root, "result_hash", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_counterexample_gate(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    require_non_empty(&result.result_key, "result_key")?;
    require_non_empty(&result.target_key, "target_key")?;
    validate_profile_shape(&result.search_profile)?;
    if let Some(domain) = &result.checked_domain {
        validate_checked_domain_shape(domain)?;
    }
    if let Some(handoff) = &result.formal_counterexample_handoff {
        validate_handoff_shape(handoff)?;
    }

    let computed_profile_hash = counterexample_search_profile_hash(&result.search_profile);
    if result.search_profile_hash != computed_profile_hash {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::SearchProfileHashMismatch {
                declared: format_hash_string(&result.search_profile_hash),
                computed: format_hash_string(&computed_profile_hash),
            },
        ));
    }

    let computed_result_hash = counterexample_result_hash(result);
    if result.result_hash != computed_result_hash {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::ResultHashMismatch {
                declared: format_hash_string(&result.result_hash),
                computed: format_hash_string(&computed_result_hash),
            },
        ));
    }

    if !result.search_profile.profile_current {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::StaleSearchProfile,
        ));
    }

    if result.proof_status_advanced {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::GateResultCannotAdvanceProofStatus,
        ));
    }

    match result.status {
        CounterexampleGateStatus::Found => validate_found_counterexample(result)?,
        CounterexampleGateStatus::NotFoundWithinBound => validate_not_found(result)?,
        CounterexampleGateStatus::Unsupported => validate_unsupported(result)?,
        CounterexampleGateStatus::Inconclusive => validate_inconclusive(result)?,
    }

    validate_formal_handoff_policy(result)?;

    Ok(())
}

pub fn counterexample_search_profile_canonical_identity_bytes(
    profile: &CounterexampleSearchProfile,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, COUNTEREXAMPLE_SEARCH_PROFILE_HASH_DOMAIN);
    encode_string_to(&mut out, "domain_hash");
    encode_hash_to(&mut out, &profile.domain_hash);
    encode_string_to(&mut out, "bounds_hash");
    encode_hash_to(&mut out, &profile.bounds_hash);
    encode_string_to(&mut out, "evaluator_identity_hash");
    encode_hash_to(&mut out, &profile.evaluator_identity_hash);
    encode_string_to(&mut out, "seed_policy_hash");
    encode_hash_to(&mut out, &profile.seed_policy_hash);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &profile.environment_hash);
    encode_string_to(&mut out, "finite_carrier");
    encode_string_to(&mut out, &profile.finite_carrier);
    encode_string_to(&mut out, "parameter_range");
    encode_string_to(&mut out, &profile.parameter_range);
    encode_string_to(&mut out, "domain_supported");
    encode_bool_to(&mut out, profile.domain_supported);
    encode_string_to(&mut out, "evaluator_checked");
    encode_bool_to(&mut out, profile.evaluator_checked);
    encode_string_to(&mut out, "decision_procedure_verified");
    encode_bool_to(&mut out, profile.decision_procedure_verified);
    encode_string_to(&mut out, "profile_current");
    encode_bool_to(&mut out, profile.profile_current);
    out
}

pub fn counterexample_search_profile_hash(profile: &CounterexampleSearchProfile) -> Hash {
    sha256(counterexample_search_profile_canonical_identity_bytes(
        profile,
    ))
}

pub fn counterexample_search_profile_hash_string(profile: &CounterexampleSearchProfile) -> String {
    format_hash_string(&counterexample_search_profile_hash(profile))
}

pub fn counterexample_result_canonical_identity_bytes(result: &CounterexampleResult) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, COUNTEREXAMPLE_RESULT_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &result.api_version);
    encode_string_to(&mut out, "result_key");
    encode_string_to(&mut out, &result.result_key);
    encode_string_to(&mut out, "target_key");
    encode_string_to(&mut out, &result.target_key);
    encode_string_to(&mut out, "statement_hash");
    encode_hash_to(&mut out, &result.statement_hash);
    encode_string_to(&mut out, "status");
    encode_string_to(&mut out, result.status.wire());
    encode_string_to(&mut out, "search_profile_hash");
    encode_hash_to(&mut out, &result.search_profile_hash);
    encode_string_to(&mut out, "evidence_level");
    encode_string_to(&mut out, result.evidence_level.wire());
    encode_string_to(&mut out, "candidate_proof_action");
    encode_string_to(&mut out, result.candidate_proof_action.wire());
    encode_string_to(&mut out, "proof_status_advanced");
    encode_bool_to(&mut out, result.proof_status_advanced);
    encode_string_to(&mut out, "witness_artifact_hash");
    encode_option_hash_to(&mut out, result.witness_artifact_hash.as_ref());
    encode_string_to(&mut out, "checked_domain");
    encode_optional_checked_domain_to(&mut out, result.checked_domain.as_ref());
    encode_string_to(&mut out, "formal_counterexample_certificate_hash");
    encode_option_hash_to(
        &mut out,
        result.formal_counterexample_certificate_hash.as_ref(),
    );
    encode_string_to(&mut out, "formal_counterexample_handoff");
    encode_optional_formal_handoff_to(&mut out, result.formal_counterexample_handoff.as_ref());
    out
}

pub fn counterexample_result_hash(result: &CounterexampleResult) -> Hash {
    sha256(counterexample_result_canonical_identity_bytes(result))
}

pub fn counterexample_result_hash_string(result: &CounterexampleResult) -> String {
    format_hash_string(&counterexample_result_hash(result))
}

fn validate_found_counterexample(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    if !result.search_profile.domain_supported {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::UnsupportedDomainCannotProduceSearchResult {
                status: result.status,
            },
        ));
    }
    if !profile_has_checked_evaluator(&result.search_profile) {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::UncheckedEvaluator {
                status: result.status,
            },
        ));
    }
    if result.witness_artifact_hash.is_none() {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::FoundRequiresWitnessArtifact,
        ));
    }
    let checked_domain = result.checked_domain.as_ref().ok_or_else(|| {
        CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::FoundRequiresCheckedDomain,
        )
    })?;
    validate_checked_domain_matches_profile(checked_domain, &result.search_profile)?;
    if !matches!(
        result.candidate_proof_action,
        CounterexampleGateProofAction::Defer | CounterexampleGateProofAction::Stop
    ) {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::FoundCounterexampleMustStopOrDefer,
        ));
    }
    if result.evidence_level > ResearchEvidenceLevel::E1 {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::GateResultCannotAdvanceProofStatus,
        ));
    }
    Ok(())
}

fn validate_not_found(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    validate_supported_non_found(result)?;
    if result.evidence_level > ResearchEvidenceLevel::E1 {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::NotFoundWithinBoundIsNotProof,
        ));
    }
    Ok(())
}

fn validate_inconclusive(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    validate_supported_non_found(result)?;
    if result.evidence_level > ResearchEvidenceLevel::E1 {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::GateResultCannotAdvanceProofStatus,
        ));
    }
    Ok(())
}

fn validate_supported_non_found(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    if !result.search_profile.domain_supported {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::UnsupportedDomainCannotProduceSearchResult {
                status: result.status,
            },
        ));
    }
    if !profile_has_checked_evaluator(&result.search_profile) {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::UncheckedEvaluator {
                status: result.status,
            },
        ));
    }
    validate_non_found_payload(result)
}

fn validate_unsupported(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    if result.search_profile.domain_supported {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::UnsupportedStatusRequiresUnsupportedDomain,
        ));
    }
    if result.evidence_level > ResearchEvidenceLevel::E1 {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::GateResultCannotAdvanceProofStatus,
        ));
    }
    validate_non_found_payload(result)
}

fn validate_non_found_payload(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    if result.witness_artifact_hash.is_some() || result.checked_domain.is_some() {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::NonFoundCannotCarryWitness,
        ));
    }
    if result.formal_counterexample_certificate_hash.is_some()
        || result.formal_counterexample_handoff.is_some()
    {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::NonFoundCannotCarryFormalCounterexample,
        ));
    }
    if result.candidate_proof_action == CounterexampleGateProofAction::Stop {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::NonFoundCannotStopProofSearch,
        ));
    }
    Ok(())
}

fn validate_formal_handoff_policy(
    result: &CounterexampleResult,
) -> Result<(), CounterexampleGateValidationError> {
    if result.formal_counterexample_certificate_hash.is_some()
        && result.status != CounterexampleGateStatus::Found
    {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::FormalCounterexampleCertificateRequiresFound,
        ));
    }

    if let Some(certificate_hash) = &result.formal_counterexample_certificate_hash {
        let handoff = result
            .formal_counterexample_handoff
            .as_ref()
            .ok_or_else(|| {
                CounterexampleGateValidationError::new(
                    CounterexampleGateValidationErrorKind::FormalCounterexampleRequiresHandoff,
                )
            })?;
        if certificate_hash != &handoff.certificate_hash {
            return Err(CounterexampleGateValidationError::new(
                CounterexampleGateValidationErrorKind::FormalCounterexampleCertificateMismatch {
                    declared: format_hash_string(certificate_hash),
                    handoff: format_hash_string(&handoff.certificate_hash),
                },
            ));
        }
    } else if result.formal_counterexample_handoff.is_some() {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::HandoffWithoutCertificateHash,
        ));
    }

    Ok(())
}

fn validate_profile_shape(
    profile: &CounterexampleSearchProfile,
) -> Result<(), CounterexampleGateValidationError> {
    require_non_empty(&profile.finite_carrier, "search_profile.finite_carrier")?;
    require_non_empty(&profile.parameter_range, "search_profile.parameter_range")
}

fn validate_checked_domain_shape(
    domain: &CounterexampleCheckedDomain,
) -> Result<(), CounterexampleGateValidationError> {
    require_non_empty(&domain.finite_carrier, "checked_domain.finite_carrier")?;
    require_non_empty(&domain.parameter_range, "checked_domain.parameter_range")
}

fn validate_handoff_shape(
    handoff: &CounterexampleFormalHandoff,
) -> Result<(), CounterexampleGateValidationError> {
    require_non_empty(
        &handoff.module_name,
        "formal_counterexample_handoff.module_name",
    )?;
    require_non_empty(
        &handoff.theorem_name,
        "formal_counterexample_handoff.theorem_name",
    )?;
    validate_handoff_path("source_path", &handoff.source_path, "/source.npa")?;
    validate_handoff_path(
        "certificate_path",
        &handoff.certificate_path,
        "/certificate.npcert",
    )?;
    validate_handoff_path("meta_path", &handoff.meta_path, "/meta.json")?;
    validate_handoff_path("replay_path", &handoff.replay_path, "/replay.json")?;
    Ok(())
}

fn validate_handoff_path(
    field: &'static str,
    path: &str,
    expected_suffix: &'static str,
) -> Result<(), CounterexampleGateValidationError> {
    let valid_package_path = path.starts_with("proofs/")
        && path.ends_with(expected_suffix)
        && path
            .split('/')
            .all(|segment| !segment.is_empty() && segment != "." && segment != "..");
    if !valid_package_path {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::InvalidHandoffPath {
                field,
                path: path.to_owned(),
                expected_suffix,
            },
        ));
    }
    Ok(())
}

fn validate_checked_domain_matches_profile(
    domain: &CounterexampleCheckedDomain,
    profile: &CounterexampleSearchProfile,
) -> Result<(), CounterexampleGateValidationError> {
    if domain.domain_hash != profile.domain_hash {
        return Err(checked_domain_mismatch("domain_hash"));
    }
    if domain.bounds_hash != profile.bounds_hash {
        return Err(checked_domain_mismatch("bounds_hash"));
    }
    if domain.evaluator_identity_hash != profile.evaluator_identity_hash {
        return Err(checked_domain_mismatch("evaluator_identity_hash"));
    }
    if domain.finite_carrier != profile.finite_carrier {
        return Err(checked_domain_mismatch("finite_carrier"));
    }
    if domain.parameter_range != profile.parameter_range {
        return Err(checked_domain_mismatch("parameter_range"));
    }
    Ok(())
}

fn checked_domain_mismatch(field: &'static str) -> CounterexampleGateValidationError {
    CounterexampleGateValidationError::new(
        CounterexampleGateValidationErrorKind::CheckedDomainMismatch { field },
    )
}

fn profile_has_checked_evaluator(profile: &CounterexampleSearchProfile) -> bool {
    profile.evaluator_checked || profile.decision_procedure_verified
}

fn parse_search_profile(
    value: &JsonValue<'_>,
) -> Result<CounterexampleSearchProfile, CounterexampleResultSchemaError> {
    let members = object_map(value, "$.search_profile", SEARCH_PROFILE_FIELDS)?;
    Ok(CounterexampleSearchProfile {
        domain_hash: required_hash(&members, "domain_hash", "$.search_profile")?,
        bounds_hash: required_hash(&members, "bounds_hash", "$.search_profile")?,
        evaluator_identity_hash: required_hash(
            &members,
            "evaluator_identity_hash",
            "$.search_profile",
        )?,
        seed_policy_hash: required_hash(&members, "seed_policy_hash", "$.search_profile")?,
        environment_hash: required_hash(&members, "environment_hash", "$.search_profile")?,
        finite_carrier: required_string(&members, "finite_carrier", "$.search_profile")?,
        parameter_range: required_string(&members, "parameter_range", "$.search_profile")?,
        domain_supported: required_bool(&members, "domain_supported", "$.search_profile")?,
        evaluator_checked: required_bool(&members, "evaluator_checked", "$.search_profile")?,
        decision_procedure_verified: required_bool(
            &members,
            "decision_procedure_verified",
            "$.search_profile",
        )?,
        profile_current: required_bool(&members, "profile_current", "$.search_profile")?,
    })
}

fn parse_checked_domain(
    value: &JsonValue<'_>,
) -> Result<CounterexampleCheckedDomain, CounterexampleResultSchemaError> {
    let members = object_map(value, "$.checked_domain", CHECKED_DOMAIN_FIELDS)?;
    Ok(CounterexampleCheckedDomain {
        domain_hash: required_hash(&members, "domain_hash", "$.checked_domain")?,
        bounds_hash: required_hash(&members, "bounds_hash", "$.checked_domain")?,
        evaluator_identity_hash: required_hash(
            &members,
            "evaluator_identity_hash",
            "$.checked_domain",
        )?,
        finite_carrier: required_string(&members, "finite_carrier", "$.checked_domain")?,
        parameter_range: required_string(&members, "parameter_range", "$.checked_domain")?,
    })
}

fn parse_formal_handoff(
    value: &JsonValue<'_>,
) -> Result<CounterexampleFormalHandoff, CounterexampleResultSchemaError> {
    let members = object_map(
        value,
        "$.formal_counterexample_handoff",
        FORMAL_HANDOFF_FIELDS,
    )?;
    Ok(CounterexampleFormalHandoff {
        module_name: required_string(&members, "module_name", "$.formal_counterexample_handoff")?,
        theorem_name: required_string(&members, "theorem_name", "$.formal_counterexample_handoff")?,
        source_path: required_string(&members, "source_path", "$.formal_counterexample_handoff")?,
        source_hash: required_hash(&members, "source_hash", "$.formal_counterexample_handoff")?,
        certificate_path: required_string(
            &members,
            "certificate_path",
            "$.formal_counterexample_handoff",
        )?,
        certificate_hash: required_hash(
            &members,
            "certificate_hash",
            "$.formal_counterexample_handoff",
        )?,
        meta_path: required_string(&members, "meta_path", "$.formal_counterexample_handoff")?,
        meta_hash: required_hash(&members, "meta_hash", "$.formal_counterexample_handoff")?,
        replay_path: required_string(&members, "replay_path", "$.formal_counterexample_handoff")?,
        replay_hash: required_hash(&members, "replay_hash", "$.formal_counterexample_handoff")?,
        source_free_verification_hash: required_hash(
            &members,
            "source_free_verification_hash",
            "$.formal_counterexample_handoff",
        )?,
    })
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, CounterexampleResultSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        CounterexampleResultSchemaError::new(
            "$",
            CounterexampleResultSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, CounterexampleResultSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(CounterexampleResultSchemaError::new(
            path,
            CounterexampleResultSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(CounterexampleResultSchemaError::new(
                format!("{path}.{}", member.key()),
                CounterexampleResultSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(CounterexampleResultSchemaError::new(
                format!("{path}.{}", member.key()),
                CounterexampleResultSchemaErrorKind::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
        map.insert(member.key(), member.value());
    }
    Ok(map)
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, CounterexampleResultSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            format!("{path}.{field}"),
            CounterexampleResultSchemaErrorKind::MissingField { field },
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
) -> Result<String, CounterexampleResultSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, CounterexampleResultSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<String, CounterexampleResultSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            path,
            CounterexampleResultSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, CounterexampleResultSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, CounterexampleResultSchemaError> {
    value.bool_value().ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            path,
            CounterexampleResultSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, CounterexampleResultSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, CounterexampleResultSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, CounterexampleResultSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        CounterexampleResultSchemaError::new(
            path,
            CounterexampleResultSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn required_status(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<CounterexampleGateStatus, CounterexampleResultSchemaError> {
    let wire = required_string(members, field, path)?;
    CounterexampleGateStatus::parse(&wire).ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            format!("{path}.{field}"),
            CounterexampleResultSchemaErrorKind::InvalidStatus { value: wire },
        )
    })
}

fn required_proof_action(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<CounterexampleGateProofAction, CounterexampleResultSchemaError> {
    let wire = required_string(members, field, path)?;
    CounterexampleGateProofAction::parse(&wire).ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            format!("{path}.{field}"),
            CounterexampleResultSchemaErrorKind::InvalidProofAction { value: wire },
        )
    })
}

fn required_evidence_level(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<ResearchEvidenceLevel, CounterexampleResultSchemaError> {
    let wire = required_string(members, field, path)?;
    ResearchEvidenceLevel::parse(&wire).ok_or_else(|| {
        CounterexampleResultSchemaError::new(
            format!("{path}.{field}"),
            CounterexampleResultSchemaErrorKind::InvalidEvidenceLevel { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), CounterexampleGateValidationError> {
    if value.is_empty() {
        return Err(CounterexampleGateValidationError::new(
            CounterexampleGateValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_optional_checked_domain_to(
    out: &mut Vec<u8>,
    domain: Option<&CounterexampleCheckedDomain>,
) {
    match domain {
        None => encode_bool_to(out, false),
        Some(domain) => {
            encode_bool_to(out, true);
            encode_string_to(out, "domain_hash");
            encode_hash_to(out, &domain.domain_hash);
            encode_string_to(out, "bounds_hash");
            encode_hash_to(out, &domain.bounds_hash);
            encode_string_to(out, "evaluator_identity_hash");
            encode_hash_to(out, &domain.evaluator_identity_hash);
            encode_string_to(out, "finite_carrier");
            encode_string_to(out, &domain.finite_carrier);
            encode_string_to(out, "parameter_range");
            encode_string_to(out, &domain.parameter_range);
        }
    }
}

fn encode_optional_formal_handoff_to(
    out: &mut Vec<u8>,
    handoff: Option<&CounterexampleFormalHandoff>,
) {
    match handoff {
        None => encode_bool_to(out, false),
        Some(handoff) => {
            encode_bool_to(out, true);
            encode_string_to(out, "module_name");
            encode_string_to(out, &handoff.module_name);
            encode_string_to(out, "theorem_name");
            encode_string_to(out, &handoff.theorem_name);
            encode_string_to(out, "source_path");
            encode_string_to(out, &handoff.source_path);
            encode_string_to(out, "source_hash");
            encode_hash_to(out, &handoff.source_hash);
            encode_string_to(out, "certificate_path");
            encode_string_to(out, &handoff.certificate_path);
            encode_string_to(out, "certificate_hash");
            encode_hash_to(out, &handoff.certificate_hash);
            encode_string_to(out, "meta_path");
            encode_string_to(out, &handoff.meta_path);
            encode_string_to(out, "meta_hash");
            encode_hash_to(out, &handoff.meta_hash);
            encode_string_to(out, "replay_path");
            encode_string_to(out, &handoff.replay_path);
            encode_string_to(out, "replay_hash");
            encode_hash_to(out, &handoff.replay_hash);
            encode_string_to(out, "source_free_verification_hash");
            encode_hash_to(out, &handoff.source_free_verification_hash);
        }
    }
}

fn encode_option_hash_to(out: &mut Vec<u8>, hash: Option<&Hash>) {
    match hash {
        None => encode_bool_to(out, false),
        Some(hash) => {
            encode_bool_to(out, true);
            encode_hash_to(out, hash);
        }
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_u64_to(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_bool_to(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn sha256(bytes: Vec<u8>) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

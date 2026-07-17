use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const EXPERIMENT_ARTIFACT_API_VERSION: &str = "npa.experiment-artifact.v1";
pub const EXPERIMENT_ARTIFACT_HASH_DOMAIN: &str = "npa.experiment-artifact.identity.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "experiment_key",
    "target_key",
    "formal_statement_hash",
    "classification",
    "relationship_to_statement",
    "supported_research_output",
    "code_hash",
    "input_generator_hash",
    "parameter_range_hash",
    "random_seed_policy",
    "random_seed_policy_hash",
    "machine_container_digest",
    "result_hash",
    "summary_hash",
    "documented_nondeterminism_hash",
    "related_research_dag_node_hash",
    "output_creates_verified_artifact",
    "output_creates_proof",
    "output_creates_general_theorem",
    "output_creates_resolution_evidence",
    "output_releases_proof_dependency",
    "output_claim_gate_success",
    "retention_excludes_secrets",
    "retention_excludes_raw_prompts",
    "retention_excludes_unrelated_source_context",
    "display_text",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExperimentArtifact {
    pub api_version: String,
    pub experiment_key: String,
    pub target_key: String,
    pub formal_statement_hash: Hash,
    pub classification: ExperimentArtifactClassification,
    pub relationship_to_statement: ExperimentRelationshipToStatement,
    pub supported_research_output: ExperimentSupportedResearchOutput,
    pub code_hash: Hash,
    pub input_generator_hash: Hash,
    pub parameter_range_hash: Hash,
    pub random_seed_policy: ExperimentRandomSeedPolicy,
    pub random_seed_policy_hash: Hash,
    pub machine_container_digest: Hash,
    pub result_hash: Hash,
    pub summary_hash: Hash,
    pub documented_nondeterminism_hash: Option<Hash>,
    pub related_research_dag_node_hash: Option<Hash>,
    pub output_creates_verified_artifact: bool,
    pub output_creates_proof: bool,
    pub output_creates_general_theorem: bool,
    pub output_creates_resolution_evidence: bool,
    pub output_releases_proof_dependency: bool,
    pub output_claim_gate_success: bool,
    pub retention_excludes_secrets: bool,
    pub retention_excludes_raw_prompts: bool,
    pub retention_excludes_unrelated_source_context: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExperimentArtifactClassification {
    ResearchOnly,
    AuthoringSidecar,
}

impl ExperimentArtifactClassification {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ResearchOnly => "research_only",
            Self::AuthoringSidecar => "authoring_sidecar",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "research_only" => Some(Self::ResearchOnly),
            "authoring_sidecar" => Some(Self::AuthoringSidecar),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExperimentRelationshipToStatement {
    TestsStatement,
    SupportsHypothesis,
    RecordsBlocker,
    RecordsRouteNote,
    Inconclusive,
}

impl ExperimentRelationshipToStatement {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::TestsStatement => "tests_statement",
            Self::SupportsHypothesis => "supports_hypothesis",
            Self::RecordsBlocker => "records_blocker",
            Self::RecordsRouteNote => "records_route_note",
            Self::Inconclusive => "inconclusive",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "tests_statement" => Some(Self::TestsStatement),
            "supports_hypothesis" => Some(Self::SupportsHypothesis),
            "records_blocker" => Some(Self::RecordsBlocker),
            "records_route_note" => Some(Self::RecordsRouteNote),
            "inconclusive" => Some(Self::Inconclusive),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExperimentSupportedResearchOutput {
    Hypothesis,
    Blocker,
    RouteNote,
}

impl ExperimentSupportedResearchOutput {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Hypothesis => "hypothesis",
            Self::Blocker => "blocker",
            Self::RouteNote => "route_note",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "hypothesis" => Some(Self::Hypothesis),
            "blocker" => Some(Self::Blocker),
            "route_note" => Some(Self::RouteNote),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExperimentRandomSeedPolicy {
    FixedSeed,
    DeterministicSchedule,
    ExhaustiveDeterministic,
    NondeterministicDocumentedFailure,
}

impl ExperimentRandomSeedPolicy {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FixedSeed => "fixed_seed",
            Self::DeterministicSchedule => "deterministic_schedule",
            Self::ExhaustiveDeterministic => "exhaustive_deterministic",
            Self::NondeterministicDocumentedFailure => "nondeterministic_documented_failure",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "fixed_seed" => Some(Self::FixedSeed),
            "deterministic_schedule" => Some(Self::DeterministicSchedule),
            "exhaustive_deterministic" => Some(Self::ExhaustiveDeterministic),
            "nondeterministic_documented_failure" => Some(Self::NondeterministicDocumentedFailure),
            _ => None,
        }
    }

    pub const fn is_nondeterministic_failure(self) -> bool {
        matches!(self, Self::NondeterministicDocumentedFailure)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExperimentArtifactSchemaError {
    path: String,
    kind: ExperimentArtifactSchemaErrorKind,
}

impl ExperimentArtifactSchemaError {
    fn new(path: impl Into<String>, kind: ExperimentArtifactSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &ExperimentArtifactSchemaErrorKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExperimentArtifactSchemaErrorKind {
    JsonParse { offset: usize },
    InvalidApiVersion { value: String },
    ExpectedObject { actual: JsonValueKind },
    ExpectedString { actual: JsonValueKind },
    ExpectedBool { actual: JsonValueKind },
    ExpectedArray { actual: JsonValueKind },
    DuplicateKey { key: String },
    UnknownField { field: String },
    MissingField { field: &'static str },
    InvalidHash { value: String },
    InvalidClassification { value: String },
    InvalidRelationship { value: String },
    InvalidSupportedResearchOutput { value: String },
    InvalidRandomSeedPolicy { value: String },
}

impl fmt::Display for ExperimentArtifactSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "experiment artifact schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for ExperimentArtifactSchemaError {}

impl fmt::Display for ExperimentArtifactSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "invalid JSON at byte offset {offset}"),
            Self::InvalidApiVersion { value } => {
                write!(f, "invalid experiment artifact api_version `{value}`")
            }
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidClassification { value } => {
                write!(f, "invalid experiment artifact classification `{value}`")
            }
            Self::InvalidRelationship { value } => {
                write!(f, "invalid experiment relationship `{value}`")
            }
            Self::InvalidSupportedResearchOutput { value } => {
                write!(f, "invalid supported research output `{value}`")
            }
            Self::InvalidRandomSeedPolicy { value } => {
                write!(f, "invalid random seed policy `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExperimentArtifactValidationError {
    kind: ExperimentArtifactValidationErrorKind,
}

impl ExperimentArtifactValidationError {
    fn new(kind: ExperimentArtifactValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &ExperimentArtifactValidationErrorKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExperimentArtifactValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    ExperimentCannotCreateVerifiedArtifact,
    ExperimentCannotCreateProof,
    ExperimentCannotCreateGeneralTheorem,
    ExperimentCannotCreateResolutionEvidence,
    ExperimentCannotReleaseProofDependency,
    ExperimentCannotSatisfyClaimGate,
    RelationshipOutputMismatch {
        relationship: ExperimentRelationshipToStatement,
        supported_output: ExperimentSupportedResearchOutput,
    },
    NondeterministicSeedPolicyRequiresDocumentation,
    DeterministicSeedPolicyCannotDeclareNondeterminism,
    RetentionMayIncludeSecrets,
    RetentionMayIncludeRawPrompts,
    RetentionMayIncludeUnrelatedSourceContext,
}

impl fmt::Display for ExperimentArtifactValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "experiment artifact validation error: {}", self.kind)
    }
}

impl std::error::Error for ExperimentArtifactValidationError {}

impl fmt::Display for ExperimentArtifactValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::ExperimentCannotCreateVerifiedArtifact => {
                write!(f, "experiment artifact cannot create a VerifiedArtifact")
            }
            Self::ExperimentCannotCreateProof => {
                write!(f, "experiment artifact cannot create a Proof")
            }
            Self::ExperimentCannotCreateGeneralTheorem => {
                write!(f, "experiment artifact cannot create a GeneralTheorem")
            }
            Self::ExperimentCannotCreateResolutionEvidence => write!(
                f,
                "experiment artifact cannot create resolution or refutation evidence"
            ),
            Self::ExperimentCannotReleaseProofDependency => {
                write!(f, "experiment artifact cannot release proof dependencies")
            }
            Self::ExperimentCannotSatisfyClaimGate => {
                write!(f, "experiment artifact cannot satisfy a claim gate")
            }
            Self::RelationshipOutputMismatch {
                relationship,
                supported_output,
            } => write!(
                f,
                "relationship `{}` cannot support research output `{}`",
                relationship.wire(),
                supported_output.wire()
            ),
            Self::NondeterministicSeedPolicyRequiresDocumentation => write!(
                f,
                "nondeterministic seed-policy failure requires documentation hash"
            ),
            Self::DeterministicSeedPolicyCannotDeclareNondeterminism => write!(
                f,
                "deterministic seed policy cannot declare nondeterminism documentation"
            ),
            Self::RetentionMayIncludeSecrets => {
                write!(f, "experiment retention may include secrets")
            }
            Self::RetentionMayIncludeRawPrompts => {
                write!(f, "experiment retention may include raw prompts")
            }
            Self::RetentionMayIncludeUnrelatedSourceContext => write!(
                f,
                "experiment retention may include unrelated source context"
            ),
        }
    }
}

pub fn parse_experiment_artifact(
    source: &str,
) -> Result<ExperimentArtifact, ExperimentArtifactSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != EXPERIMENT_ARTIFACT_API_VERSION {
        return Err(ExperimentArtifactSchemaError::new(
            "$.api_version",
            ExperimentArtifactSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ExperimentArtifact {
        api_version,
        experiment_key: required_string(&root, "experiment_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        formal_statement_hash: required_hash(&root, "formal_statement_hash", "$")?,
        classification: parse_classification_value(
            required_value(&root, "classification", "$")?,
            "$.classification",
        )?,
        relationship_to_statement: parse_relationship_value(
            required_value(&root, "relationship_to_statement", "$")?,
            "$.relationship_to_statement",
        )?,
        supported_research_output: parse_supported_research_output_value(
            required_value(&root, "supported_research_output", "$")?,
            "$.supported_research_output",
        )?,
        code_hash: required_hash(&root, "code_hash", "$")?,
        input_generator_hash: required_hash(&root, "input_generator_hash", "$")?,
        parameter_range_hash: required_hash(&root, "parameter_range_hash", "$")?,
        random_seed_policy: parse_random_seed_policy_value(
            required_value(&root, "random_seed_policy", "$")?,
            "$.random_seed_policy",
        )?,
        random_seed_policy_hash: required_hash(&root, "random_seed_policy_hash", "$")?,
        machine_container_digest: required_hash(&root, "machine_container_digest", "$")?,
        result_hash: required_hash(&root, "result_hash", "$")?,
        summary_hash: required_hash(&root, "summary_hash", "$")?,
        documented_nondeterminism_hash: optional_hash(
            &root,
            "documented_nondeterminism_hash",
            "$",
        )?,
        related_research_dag_node_hash: optional_hash(
            &root,
            "related_research_dag_node_hash",
            "$",
        )?,
        output_creates_verified_artifact: required_bool(
            &root,
            "output_creates_verified_artifact",
            "$",
        )?,
        output_creates_proof: required_bool(&root, "output_creates_proof", "$")?,
        output_creates_general_theorem: required_bool(
            &root,
            "output_creates_general_theorem",
            "$",
        )?,
        output_creates_resolution_evidence: required_bool(
            &root,
            "output_creates_resolution_evidence",
            "$",
        )?,
        output_releases_proof_dependency: required_bool(
            &root,
            "output_releases_proof_dependency",
            "$",
        )?,
        output_claim_gate_success: required_bool(&root, "output_claim_gate_success", "$")?,
        retention_excludes_secrets: required_bool(&root, "retention_excludes_secrets", "$")?,
        retention_excludes_raw_prompts: required_bool(
            &root,
            "retention_excludes_raw_prompts",
            "$",
        )?,
        retention_excludes_unrelated_source_context: required_bool(
            &root,
            "retention_excludes_unrelated_source_context",
            "$",
        )?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_experiment_artifact(
    artifact: &ExperimentArtifact,
) -> Result<(), ExperimentArtifactValidationError> {
    require_non_empty(&artifact.experiment_key, "experiment_key")?;
    require_non_empty(&artifact.target_key, "target_key")?;
    validate_output_boundary(artifact)?;
    validate_relationship_output(artifact)?;
    validate_seed_policy(artifact)?;
    validate_retention_boundary(artifact)?;
    Ok(())
}

pub fn experiment_artifact_canonical_identity_bytes(artifact: &ExperimentArtifact) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, EXPERIMENT_ARTIFACT_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &artifact.api_version);
    encode_string_to(&mut out, "formal_statement_hash");
    encode_hash_to(&mut out, &artifact.formal_statement_hash);
    encode_string_to(&mut out, "relationship_to_statement");
    encode_string_to(&mut out, artifact.relationship_to_statement.wire());
    encode_string_to(&mut out, "code_hash");
    encode_hash_to(&mut out, &artifact.code_hash);
    encode_string_to(&mut out, "input_generator_hash");
    encode_hash_to(&mut out, &artifact.input_generator_hash);
    encode_string_to(&mut out, "parameter_range_hash");
    encode_hash_to(&mut out, &artifact.parameter_range_hash);
    encode_string_to(&mut out, "random_seed_policy");
    encode_string_to(&mut out, artifact.random_seed_policy.wire());
    encode_string_to(&mut out, "random_seed_policy_hash");
    encode_hash_to(&mut out, &artifact.random_seed_policy_hash);
    encode_string_to(&mut out, "machine_container_digest");
    encode_hash_to(&mut out, &artifact.machine_container_digest);
    encode_string_to(&mut out, "result_hash");
    encode_hash_to(&mut out, &artifact.result_hash);
    encode_option_hash_to(
        &mut out,
        "documented_nondeterminism_hash",
        artifact.documented_nondeterminism_hash.as_ref(),
    );
    out
}

pub fn experiment_artifact_hash(artifact: &ExperimentArtifact) -> Hash {
    let digest = Sha256::digest(experiment_artifact_canonical_identity_bytes(artifact));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn experiment_artifact_hash_string(artifact: &ExperimentArtifact) -> String {
    format_hash_string(&experiment_artifact_hash(artifact))
}

fn validate_output_boundary(
    artifact: &ExperimentArtifact,
) -> Result<(), ExperimentArtifactValidationError> {
    if artifact.output_creates_verified_artifact {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotCreateVerifiedArtifact,
        ));
    }
    if artifact.output_creates_proof {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotCreateProof,
        ));
    }
    if artifact.output_creates_general_theorem {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotCreateGeneralTheorem,
        ));
    }
    if artifact.output_creates_resolution_evidence {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotCreateResolutionEvidence,
        ));
    }
    if artifact.output_releases_proof_dependency {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotReleaseProofDependency,
        ));
    }
    if artifact.output_claim_gate_success {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::ExperimentCannotSatisfyClaimGate,
        ));
    }
    Ok(())
}

fn validate_relationship_output(
    artifact: &ExperimentArtifact,
) -> Result<(), ExperimentArtifactValidationError> {
    let allowed = match artifact.relationship_to_statement {
        ExperimentRelationshipToStatement::SupportsHypothesis => {
            artifact.supported_research_output == ExperimentSupportedResearchOutput::Hypothesis
        }
        ExperimentRelationshipToStatement::RecordsBlocker => {
            artifact.supported_research_output == ExperimentSupportedResearchOutput::Blocker
        }
        ExperimentRelationshipToStatement::TestsStatement
        | ExperimentRelationshipToStatement::RecordsRouteNote
        | ExperimentRelationshipToStatement::Inconclusive => {
            artifact.supported_research_output == ExperimentSupportedResearchOutput::RouteNote
        }
    };
    if !allowed {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::RelationshipOutputMismatch {
                relationship: artifact.relationship_to_statement,
                supported_output: artifact.supported_research_output,
            },
        ));
    }
    Ok(())
}

fn validate_seed_policy(
    artifact: &ExperimentArtifact,
) -> Result<(), ExperimentArtifactValidationError> {
    if artifact.random_seed_policy.is_nondeterministic_failure() {
        if artifact.documented_nondeterminism_hash.is_none() {
            return Err(ExperimentArtifactValidationError::new(
                ExperimentArtifactValidationErrorKind::NondeterministicSeedPolicyRequiresDocumentation,
            ));
        }
    } else if artifact.documented_nondeterminism_hash.is_some() {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::DeterministicSeedPolicyCannotDeclareNondeterminism,
        ));
    }
    Ok(())
}

fn validate_retention_boundary(
    artifact: &ExperimentArtifact,
) -> Result<(), ExperimentArtifactValidationError> {
    if !artifact.retention_excludes_secrets {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::RetentionMayIncludeSecrets,
        ));
    }
    if !artifact.retention_excludes_raw_prompts {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::RetentionMayIncludeRawPrompts,
        ));
    }
    if !artifact.retention_excludes_unrelated_source_context {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::RetentionMayIncludeUnrelatedSourceContext,
        ));
    }
    Ok(())
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ExperimentArtifactSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ExperimentArtifactSchemaError::new(
            "$",
            ExperimentArtifactSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ExperimentArtifactSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ExperimentArtifactSchemaError::new(
                format!("{path}.{}", member.key()),
                ExperimentArtifactSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ExperimentArtifactSchemaError::new(
                format!("{path}.{}", member.key()),
                ExperimentArtifactSchemaErrorKind::UnknownField {
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
) -> Result<&'value JsonValue<'src>, ExperimentArtifactSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            format!("{path}.{field}"),
            ExperimentArtifactSchemaErrorKind::MissingField { field },
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
) -> Result<String, ExperimentArtifactSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ExperimentArtifactSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<String, ExperimentArtifactSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ExperimentArtifactSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ExperimentArtifactSchemaError> {
    value.bool_value().ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ExperimentArtifactSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ExperimentArtifactSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ExperimentArtifactSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_classification_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ExperimentArtifactClassification, ExperimentArtifactSchemaError> {
    let wire = string_value(value, path)?;
    ExperimentArtifactClassification::parse(&wire).ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::InvalidClassification { value: wire },
        )
    })
}

fn parse_relationship_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ExperimentRelationshipToStatement, ExperimentArtifactSchemaError> {
    let wire = string_value(value, path)?;
    ExperimentRelationshipToStatement::parse(&wire).ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::InvalidRelationship { value: wire },
        )
    })
}

fn parse_supported_research_output_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ExperimentSupportedResearchOutput, ExperimentArtifactSchemaError> {
    let wire = string_value(value, path)?;
    ExperimentSupportedResearchOutput::parse(&wire).ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::InvalidSupportedResearchOutput { value: wire },
        )
    })
}

fn parse_random_seed_policy_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ExperimentRandomSeedPolicy, ExperimentArtifactSchemaError> {
    let wire = string_value(value, path)?;
    ExperimentRandomSeedPolicy::parse(&wire).ok_or_else(|| {
        ExperimentArtifactSchemaError::new(
            path,
            ExperimentArtifactSchemaErrorKind::InvalidRandomSeedPolicy { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ExperimentArtifactValidationError> {
    if value.trim().is_empty() {
        return Err(ExperimentArtifactValidationError::new(
            ExperimentArtifactValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
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

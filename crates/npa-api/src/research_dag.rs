use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::research_evidence::ResearchEvidenceLevel;
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const RESEARCH_DAG_API_VERSION: &str = "npa.research-dag.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "dag_key",
    "target_key",
    "formal_statement_hash",
    "execution",
    "artifact_references",
    "nodes",
    "edges",
    "display_text",
];
const EXECUTION_FIELDS: &[&str] = &[
    "primary_plane",
    "normal_verify_dependency",
    "allowed_outputs",
    "dependency_kind",
    "verified_artifact_identity_hash",
    "dependency_release_trust_level",
];
const ARTIFACT_REFERENCE_FIELDS: &[&str] = &["artifact_hash", "artifact_kind", "current"];
const NODE_FIELDS: &[&str] = &[
    "node_key",
    "node_kind",
    "evidence_level",
    "statement_hash",
    "verified_artifact_identity_hash",
    "research_evidence_hash",
    "counterexample_or_refutation_hash",
    "experiment_artifact_hash",
    "barrier_audit_hash",
    "review_hash",
    "assumption_hashes",
    "sidecar_only",
    "proof_claim",
    "creates_verified_artifact",
    "upgrades_verified_artifact",
    "display_text",
];
const EDGE_FIELDS: &[&str] = &[
    "edge_key",
    "from_node_key",
    "to_node_key",
    "edge_kind",
    "evidence_hash",
    "checked_counterexample_hash",
    "review_hash",
    "rewrites_target_statement",
    "dependency_release_attempt",
    "display_text",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDag {
    pub api_version: String,
    pub dag_key: String,
    pub target_key: String,
    pub formal_statement_hash: Hash,
    pub execution: ResearchDagExecutionBoundary,
    pub artifact_references: Vec<ResearchDagArtifactReference>,
    pub nodes: Vec<ResearchDagNode>,
    pub edges: Vec<ResearchDagEdge>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagExecutionBoundary {
    pub primary_plane: ResearchDagExecutionPlane,
    pub normal_verify_dependency: bool,
    pub allowed_outputs: Vec<ResearchDagAllowedOutput>,
    pub dependency_kind: ResearchDagDependencyKind,
    pub verified_artifact_identity_hash: Option<Hash>,
    pub dependency_release_trust_level: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagArtifactReference {
    pub artifact_hash: Hash,
    pub artifact_kind: ResearchDagArtifactKind,
    pub current: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagNode {
    pub node_key: String,
    pub node_kind: ResearchDagNodeKind,
    pub evidence_level: ResearchEvidenceLevel,
    pub statement_hash: Option<Hash>,
    pub verified_artifact_identity_hash: Option<Hash>,
    pub research_evidence_hash: Option<Hash>,
    pub counterexample_or_refutation_hash: Option<Hash>,
    pub experiment_artifact_hash: Option<Hash>,
    pub barrier_audit_hash: Option<Hash>,
    pub review_hash: Option<Hash>,
    pub assumption_hashes: Vec<Hash>,
    pub sidecar_only: bool,
    pub proof_claim: bool,
    pub creates_verified_artifact: bool,
    pub upgrades_verified_artifact: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagEdge {
    pub edge_key: String,
    pub from_node_key: String,
    pub to_node_key: String,
    pub edge_kind: ResearchDagEdgeKind,
    pub evidence_hash: Option<Hash>,
    pub checked_counterexample_hash: Option<Hash>,
    pub review_hash: Option<Hash>,
    pub rewrites_target_statement: bool,
    pub dependency_release_attempt: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagExecutionPlane {
    ResearchOnly,
}

impl ResearchDagExecutionPlane {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ResearchOnly => "research_only",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "research_only" => Some(Self::ResearchOnly),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagAllowedOutput {
    ResearchEvidence,
    CounterexampleReport,
    BarrierAnalysis,
}

impl ResearchDagAllowedOutput {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ResearchEvidence => "research_evidence",
            Self::CounterexampleReport => "counterexample_report",
            Self::BarrierAnalysis => "barrier_analysis",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "research_evidence" => Some(Self::ResearchEvidence),
            "counterexample_report" => Some(Self::CounterexampleReport),
            "barrier_analysis" => Some(Self::BarrierAnalysis),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagDependencyKind {
    Research,
    Ordering,
    VerifiedArtifact,
}

impl ResearchDagDependencyKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Research => "research",
            Self::Ordering => "ordering",
            Self::VerifiedArtifact => "verified_artifact",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "research" => Some(Self::Research),
            "ordering" => Some(Self::Ordering),
            "verified_artifact" => Some(Self::VerifiedArtifact),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagArtifactKind {
    VerifiedArtifactIdentity,
    ResearchEvidence,
    CounterexampleReport,
    BarrierAnalysis,
    ExperimentArtifact,
    ReviewRecord,
    AssumptionRecord,
}

impl ResearchDagArtifactKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::VerifiedArtifactIdentity => "verified_artifact_identity",
            Self::ResearchEvidence => "research_evidence",
            Self::CounterexampleReport => "counterexample_report",
            Self::BarrierAnalysis => "barrier_analysis",
            Self::ExperimentArtifact => "experiment_artifact",
            Self::ReviewRecord => "review_record",
            Self::AssumptionRecord => "assumption_record",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "verified_artifact_identity" => Some(Self::VerifiedArtifactIdentity),
            "research_evidence" => Some(Self::ResearchEvidence),
            "counterexample_report" => Some(Self::CounterexampleReport),
            "barrier_analysis" => Some(Self::BarrierAnalysis),
            "experiment_artifact" => Some(Self::ExperimentArtifact),
            "review_record" => Some(Self::ReviewRecord),
            "assumption_record" => Some(Self::AssumptionRecord),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagNodeKind {
    Definition,
    KnownTheorem,
    EquivalentFormulation,
    Reduction,
    SpecialCase,
    ConditionalLemma,
    ComputationalExperiment,
    CounterexampleSearch,
    BarrierResult,
    CandidateLemma,
    OpenBlocker,
}

impl ResearchDagNodeKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::KnownTheorem => "known_theorem",
            Self::EquivalentFormulation => "equivalent_formulation",
            Self::Reduction => "reduction",
            Self::SpecialCase => "special_case",
            Self::ConditionalLemma => "conditional_lemma",
            Self::ComputationalExperiment => "computational_experiment",
            Self::CounterexampleSearch => "counterexample_search",
            Self::BarrierResult => "barrier_result",
            Self::CandidateLemma => "candidate_lemma",
            Self::OpenBlocker => "open_blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "definition" => Some(Self::Definition),
            "known_theorem" => Some(Self::KnownTheorem),
            "equivalent_formulation" => Some(Self::EquivalentFormulation),
            "reduction" => Some(Self::Reduction),
            "special_case" => Some(Self::SpecialCase),
            "conditional_lemma" => Some(Self::ConditionalLemma),
            "computational_experiment" => Some(Self::ComputationalExperiment),
            "counterexample_search" => Some(Self::CounterexampleSearch),
            "barrier_result" => Some(Self::BarrierResult),
            "candidate_lemma" => Some(Self::CandidateLemma),
            "open_blocker" => Some(Self::OpenBlocker),
            _ => None,
        }
    }

    pub const fn is_mandatory_sidecar(self) -> bool {
        matches!(
            self,
            Self::ComputationalExperiment
                | Self::CounterexampleSearch
                | Self::BarrierResult
                | Self::CandidateLemma
                | Self::OpenBlocker
                | Self::EquivalentFormulation
                | Self::Definition
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchDagEdgeKind {
    DependsOn,
    Implies,
    EquivalentTo,
    Strengthens,
    Weakens,
    Refutes,
    SupportedByExperiment,
    BlockedBy,
}

impl ResearchDagEdgeKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::DependsOn => "depends_on",
            Self::Implies => "implies",
            Self::EquivalentTo => "equivalent_to",
            Self::Strengthens => "strengthens",
            Self::Weakens => "weakens",
            Self::Refutes => "refutes",
            Self::SupportedByExperiment => "supported_by_experiment",
            Self::BlockedBy => "blocked_by",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "depends_on" => Some(Self::DependsOn),
            "implies" => Some(Self::Implies),
            "equivalent_to" => Some(Self::EquivalentTo),
            "strengthens" => Some(Self::Strengthens),
            "weakens" => Some(Self::Weakens),
            "refutes" => Some(Self::Refutes),
            "supported_by_experiment" => Some(Self::SupportedByExperiment),
            "blocked_by" => Some(Self::BlockedBy),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagSchemaError {
    path: String,
    kind: ResearchDagSchemaErrorKind,
}

impl ResearchDagSchemaError {
    fn new(path: impl Into<String>, kind: ResearchDagSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ResearchDagSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchDagSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ResearchDagSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchDagSchemaErrorKind {
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
    InvalidEvidenceLevel { value: String },
    InvalidExecutionPlane { value: String },
    InvalidAllowedOutput { value: String },
    InvalidDependencyKind { value: String },
    InvalidArtifactKind { value: String },
    InvalidNodeKind { value: String },
    InvalidEdgeKind { value: String },
}

impl fmt::Display for ResearchDagSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "json parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedBool { actual } => write!(f, "expected bool, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidEvidenceLevel { value } => write!(f, "invalid evidence level `{value}`"),
            Self::InvalidExecutionPlane { value } => {
                write!(f, "invalid execution plane `{value}`")
            }
            Self::InvalidAllowedOutput { value } => write!(f, "invalid allowed output `{value}`"),
            Self::InvalidDependencyKind { value } => {
                write!(f, "invalid dependency kind `{value}`")
            }
            Self::InvalidArtifactKind { value } => write!(f, "invalid artifact kind `{value}`"),
            Self::InvalidNodeKind { value } => write!(f, "invalid node kind `{value}`"),
            Self::InvalidEdgeKind { value } => write!(f, "invalid edge kind `{value}`"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchDagValidationError {
    kind: ResearchDagValidationErrorKind,
}

impl ResearchDagValidationError {
    fn new(kind: ResearchDagValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ResearchDagValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchDagValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::error::Error for ResearchDagValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchDagValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    DuplicateNodeKey {
        node_key: String,
    },
    DuplicateEdgeKey {
        edge_key: String,
    },
    DuplicateArtifactReference {
        artifact_hash: String,
    },
    MissingNodeReference {
        edge_key: String,
        node_key: String,
    },
    CycleDetected {
        node_key: String,
    },
    ResearchDagMustBeResearchOnly,
    ResearchDagCannotReleaseProofDependency,
    DuplicateAllowedOutput {
        output: ResearchDagAllowedOutput,
    },
    MissingAllowedOutput {
        output: ResearchDagAllowedOutput,
    },
    NodeMustRemainSidecar {
        node_key: String,
        kind: ResearchDagNodeKind,
    },
    SidecarNodeCannotClaimProof {
        node_key: String,
        kind: ResearchDagNodeKind,
    },
    NodeCannotCreateOrUpgradeVerifiedArtifact {
        node_key: String,
    },
    UnsupportedProofClaim {
        node_key: String,
    },
    MissingVerifiedArtifactReference {
        node_key: String,
    },
    MissingResearchEvidenceReference {
        node_key: String,
    },
    MissingAssumptions {
        node_key: String,
    },
    EquivalentNodeRequiresReview {
        node_key: String,
    },
    MissingCounterexampleEvidence {
        node_key: String,
    },
    MissingExperimentArtifact {
        node_key: String,
    },
    MissingBarrierAudit {
        node_key: String,
    },
    InvalidEvidenceLevelForNode {
        node_key: String,
        kind: ResearchDagNodeKind,
        level: ResearchEvidenceLevel,
    },
    MissingArtifactReference {
        field: &'static str,
        artifact_hash: String,
    },
    StaleArtifactReference {
        field: &'static str,
        artifact_hash: String,
    },
    ArtifactKindMismatch {
        field: &'static str,
        artifact_hash: String,
        expected: ResearchDagArtifactKind,
        actual: ResearchDagArtifactKind,
    },
    EvidenceLevelUpgradeRequiresVerifiedArtifact {
        edge_key: String,
        from_level: ResearchEvidenceLevel,
        to_level: ResearchEvidenceLevel,
    },
    RefutesRequiresCheckedCounterexample {
        edge_key: String,
    },
    EquivalentRequiresReview {
        edge_key: String,
    },
    EquivalentCannotRewriteTarget {
        edge_key: String,
    },
    SupportedByExperimentRequiresExperimentNode {
        edge_key: String,
    },
}

impl fmt::Display for ResearchDagValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::DuplicateNodeKey { node_key } => write!(f, "duplicate node key `{node_key}`"),
            Self::DuplicateEdgeKey { edge_key } => write!(f, "duplicate edge key `{edge_key}`"),
            Self::DuplicateArtifactReference { artifact_hash } => {
                write!(f, "duplicate artifact reference `{artifact_hash}`")
            }
            Self::MissingNodeReference {
                edge_key,
                node_key,
            } => write!(
                f,
                "edge `{edge_key}` references missing node `{node_key}`"
            ),
            Self::CycleDetected { node_key } => {
                write!(f, "research DAG contains a cycle at node `{node_key}`")
            }
            Self::ResearchDagMustBeResearchOnly => {
                write!(f, "research DAG execution plane must be research_only")
            }
            Self::ResearchDagCannotReleaseProofDependency => {
                write!(f, "research DAG cannot release proof-task dependencies")
            }
            Self::DuplicateAllowedOutput { output } => {
                write!(f, "duplicate allowed output `{}`", output.wire())
            }
            Self::MissingAllowedOutput { output } => {
                write!(f, "research DAG must allow `{}` output", output.wire())
            }
            Self::NodeMustRemainSidecar { node_key, kind } => write!(
                f,
                "node `{node_key}` kind `{}` must remain a visible sidecar",
                kind.wire()
            ),
            Self::SidecarNodeCannotClaimProof { node_key, kind } => write!(
                f,
                "sidecar node `{node_key}` kind `{}` cannot claim proof",
                kind.wire()
            ),
            Self::NodeCannotCreateOrUpgradeVerifiedArtifact { node_key } => write!(
                f,
                "research DAG node `{node_key}` cannot create or upgrade a verified artifact"
            ),
            Self::UnsupportedProofClaim { node_key } => write!(
                f,
                "research DAG node `{node_key}` cannot claim proof without checked evidence"
            ),
            Self::MissingVerifiedArtifactReference { node_key } => write!(
                f,
                "research DAG node `{node_key}` requires a verified artifact identity reference"
            ),
            Self::MissingResearchEvidenceReference { node_key } => write!(
                f,
                "research DAG node `{node_key}` requires research evidence or verified artifact reference"
            ),
            Self::MissingAssumptions { node_key } => {
                write!(f, "conditional node `{node_key}` requires assumptions")
            }
            Self::EquivalentNodeRequiresReview { node_key } => {
                write!(f, "equivalent formulation node `{node_key}` requires review")
            }
            Self::MissingCounterexampleEvidence { node_key } => write!(
                f,
                "counterexample node `{node_key}` requires checked counterexample evidence"
            ),
            Self::MissingExperimentArtifact { node_key } => {
                write!(f, "experiment node `{node_key}` requires an experiment artifact")
            }
            Self::MissingBarrierAudit { node_key } => {
                write!(f, "barrier node `{node_key}` requires a barrier audit")
            }
            Self::InvalidEvidenceLevelForNode {
                node_key,
                kind,
                level,
            } => write!(
                f,
                "node `{node_key}` kind `{}` cannot use evidence level `{}`",
                kind.wire(),
                level.wire()
            ),
            Self::MissingArtifactReference {
                field,
                artifact_hash,
            } => write!(
                f,
                "field `{field}` references unregistered artifact `{artifact_hash}`"
            ),
            Self::StaleArtifactReference {
                field,
                artifact_hash,
            } => write!(
                f,
                "field `{field}` references stale artifact `{artifact_hash}`"
            ),
            Self::ArtifactKindMismatch {
                field,
                artifact_hash,
                expected,
                actual,
            } => write!(
                f,
                "field `{field}` references artifact `{artifact_hash}` as `{}` but registry has `{}`",
                expected.wire(),
                actual.wire()
            ),
            Self::EvidenceLevelUpgradeRequiresVerifiedArtifact {
                edge_key,
                from_level,
                to_level,
            } => write!(
                f,
                "edge `{edge_key}` cannot upgrade evidence from `{}` to `{}` without a verified artifact identity",
                from_level.wire(),
                to_level.wire()
            ),
            Self::RefutesRequiresCheckedCounterexample { edge_key } => write!(
                f,
                "refutes edge `{edge_key}` requires checked counterexample evidence"
            ),
            Self::EquivalentRequiresReview { edge_key } => {
                write!(f, "equivalent edge `{edge_key}` requires review")
            }
            Self::EquivalentCannotRewriteTarget { edge_key } => write!(
                f,
                "equivalent edge `{edge_key}` cannot silently rewrite the target statement"
            ),
            Self::SupportedByExperimentRequiresExperimentNode { edge_key } => write!(
                f,
                "supported_by_experiment edge `{edge_key}` must include an experiment node"
            ),
        }
    }
}

pub fn parse_research_dag(source: &str) -> Result<ResearchDag, ResearchDagSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;

    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != RESEARCH_DAG_API_VERSION {
        return Err(ResearchDagSchemaError::new(
            "$.api_version",
            ResearchDagSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ResearchDag {
        api_version,
        dag_key: required_string(&root, "dag_key", "$")?,
        target_key: required_string(&root, "target_key", "$")?,
        formal_statement_hash: required_hash(&root, "formal_statement_hash", "$")?,
        execution: parse_execution(required_value(&root, "execution", "$")?)?,
        artifact_references: parse_artifact_references(required_value(
            &root,
            "artifact_references",
            "$",
        )?)?,
        nodes: parse_nodes(required_value(&root, "nodes", "$")?)?,
        edges: parse_edges(required_value(&root, "edges", "$")?)?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_research_dag(dag: &ResearchDag) -> Result<(), ResearchDagValidationError> {
    require_non_empty(&dag.dag_key, "dag_key")?;
    require_non_empty(&dag.target_key, "target_key")?;
    validate_execution_boundary(&dag.execution)?;

    let artifact_registry = artifact_registry(&dag.artifact_references)?;
    let node_by_key = validate_nodes(dag, &artifact_registry)?;
    validate_edges(dag, &node_by_key, &artifact_registry)?;
    validate_acyclic(dag, &node_by_key)?;

    Ok(())
}

fn validate_execution_boundary(
    execution: &ResearchDagExecutionBoundary,
) -> Result<(), ResearchDagValidationError> {
    if execution.primary_plane != ResearchDagExecutionPlane::ResearchOnly
        || execution.normal_verify_dependency
    {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::ResearchDagMustBeResearchOnly,
        ));
    }

    if execution.dependency_kind != ResearchDagDependencyKind::Research
        || execution.verified_artifact_identity_hash.is_some()
        || execution.dependency_release_trust_level.is_some()
    {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::ResearchDagCannotReleaseProofDependency,
        ));
    }

    let mut seen_outputs = BTreeSet::new();
    for output in &execution.allowed_outputs {
        if !seen_outputs.insert(*output) {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::DuplicateAllowedOutput { output: *output },
            ));
        }
    }

    for output in [
        ResearchDagAllowedOutput::ResearchEvidence,
        ResearchDagAllowedOutput::CounterexampleReport,
        ResearchDagAllowedOutput::BarrierAnalysis,
    ] {
        if !execution.allowed_outputs.contains(&output) {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::MissingAllowedOutput { output },
            ));
        }
    }

    Ok(())
}

fn artifact_registry(
    references: &[ResearchDagArtifactReference],
) -> Result<BTreeMap<Hash, &ResearchDagArtifactReference>, ResearchDagValidationError> {
    let mut registry = BTreeMap::new();
    for reference in references {
        if registry
            .insert(reference.artifact_hash, reference)
            .is_some()
        {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::DuplicateArtifactReference {
                    artifact_hash: format_hash_string(&reference.artifact_hash),
                },
            ));
        }
    }
    Ok(registry)
}

fn validate_nodes<'a>(
    dag: &'a ResearchDag,
    artifact_registry: &BTreeMap<Hash, &ResearchDagArtifactReference>,
) -> Result<BTreeMap<&'a str, &'a ResearchDagNode>, ResearchDagValidationError> {
    let mut node_by_key = BTreeMap::new();
    for node in &dag.nodes {
        require_non_empty(&node.node_key, "node_key")?;
        if node_by_key.insert(node.node_key.as_str(), node).is_some() {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::DuplicateNodeKey {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        validate_node(node, artifact_registry)?;
    }
    Ok(node_by_key)
}

fn validate_node(
    node: &ResearchDagNode,
    artifact_registry: &BTreeMap<Hash, &ResearchDagArtifactReference>,
) -> Result<(), ResearchDagValidationError> {
    if !research_dag_node_kind_permits_evidence_level(node.node_kind, node.evidence_level) {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::InvalidEvidenceLevelForNode {
                node_key: node.node_key.clone(),
                kind: node.node_kind,
                level: node.evidence_level,
            },
        ));
    }

    if !node.sidecar_only {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::NodeMustRemainSidecar {
                node_key: node.node_key.clone(),
                kind: node.node_kind,
            },
        ));
    }

    if node.creates_verified_artifact || node.upgrades_verified_artifact {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::NodeCannotCreateOrUpgradeVerifiedArtifact {
                node_key: node.node_key.clone(),
            },
        ));
    }

    if node.node_kind.is_mandatory_sidecar() && node.proof_claim {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::SidecarNodeCannotClaimProof {
                node_key: node.node_key.clone(),
                kind: node.node_kind,
            },
        ));
    }

    if node.proof_claim
        && node.verified_artifact_identity_hash.is_none()
        && node.counterexample_or_refutation_hash.is_none()
    {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::UnsupportedProofClaim {
                node_key: node.node_key.clone(),
            },
        ));
    }

    match node.node_kind {
        ResearchDagNodeKind::EquivalentFormulation if node.review_hash.is_none() => {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::EquivalentNodeRequiresReview {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        ResearchDagNodeKind::KnownTheorem if node.verified_artifact_identity_hash.is_none() => {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::MissingVerifiedArtifactReference {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        ResearchDagNodeKind::SpecialCase
            if node.verified_artifact_identity_hash.is_none()
                && node.research_evidence_hash.is_none() =>
        {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::MissingResearchEvidenceReference {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        ResearchDagNodeKind::ConditionalLemma => {
            if node.assumption_hashes.is_empty() {
                return Err(ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::MissingAssumptions {
                        node_key: node.node_key.clone(),
                    },
                ));
            }
            if node.verified_artifact_identity_hash.is_none()
                && node.research_evidence_hash.is_none()
            {
                return Err(ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::MissingResearchEvidenceReference {
                        node_key: node.node_key.clone(),
                    },
                ));
            }
        }
        ResearchDagNodeKind::ComputationalExperiment if node.experiment_artifact_hash.is_none() => {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::MissingExperimentArtifact {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        ResearchDagNodeKind::CounterexampleSearch => {
            let checked_counterexample_level = matches!(
                node.evidence_level,
                ResearchEvidenceLevel::E4 | ResearchEvidenceLevel::E5
            );
            if checked_counterexample_level && node.counterexample_or_refutation_hash.is_none() {
                return Err(ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::MissingCounterexampleEvidence {
                        node_key: node.node_key.clone(),
                    },
                ));
            }
        }
        ResearchDagNodeKind::BarrierResult if node.barrier_audit_hash.is_none() => {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::MissingBarrierAudit {
                    node_key: node.node_key.clone(),
                },
            ));
        }
        _ => {}
    }

    check_optional_artifact(
        artifact_registry,
        node.verified_artifact_identity_hash.as_ref(),
        "verified_artifact_identity_hash",
        ResearchDagArtifactKind::VerifiedArtifactIdentity,
    )?;
    check_optional_artifact(
        artifact_registry,
        node.research_evidence_hash.as_ref(),
        "research_evidence_hash",
        ResearchDagArtifactKind::ResearchEvidence,
    )?;
    check_optional_artifact(
        artifact_registry,
        node.counterexample_or_refutation_hash.as_ref(),
        "counterexample_or_refutation_hash",
        ResearchDagArtifactKind::CounterexampleReport,
    )?;
    check_optional_artifact(
        artifact_registry,
        node.experiment_artifact_hash.as_ref(),
        "experiment_artifact_hash",
        ResearchDagArtifactKind::ExperimentArtifact,
    )?;
    check_optional_artifact(
        artifact_registry,
        node.barrier_audit_hash.as_ref(),
        "barrier_audit_hash",
        ResearchDagArtifactKind::BarrierAnalysis,
    )?;
    check_optional_artifact(
        artifact_registry,
        node.review_hash.as_ref(),
        "review_hash",
        ResearchDagArtifactKind::ReviewRecord,
    )?;
    for assumption_hash in &node.assumption_hashes {
        check_artifact(
            artifact_registry,
            assumption_hash,
            "assumption_hashes",
            ResearchDagArtifactKind::AssumptionRecord,
        )?;
    }

    Ok(())
}

fn validate_edges(
    dag: &ResearchDag,
    node_by_key: &BTreeMap<&str, &ResearchDagNode>,
    artifact_registry: &BTreeMap<Hash, &ResearchDagArtifactReference>,
) -> Result<(), ResearchDagValidationError> {
    let mut edge_keys = BTreeSet::new();
    for edge in &dag.edges {
        require_non_empty(&edge.edge_key, "edge_key")?;
        if !edge_keys.insert(edge.edge_key.as_str()) {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::DuplicateEdgeKey {
                    edge_key: edge.edge_key.clone(),
                },
            ));
        }
        let from = node_by_key
            .get(edge.from_node_key.as_str())
            .ok_or_else(|| {
                ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::MissingNodeReference {
                        edge_key: edge.edge_key.clone(),
                        node_key: edge.from_node_key.clone(),
                    },
                )
            })?;
        let to = node_by_key.get(edge.to_node_key.as_str()).ok_or_else(|| {
            ResearchDagValidationError::new(ResearchDagValidationErrorKind::MissingNodeReference {
                edge_key: edge.edge_key.clone(),
                node_key: edge.to_node_key.clone(),
            })
        })?;

        if edge.dependency_release_attempt {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::ResearchDagCannotReleaseProofDependency,
            ));
        }

        validate_edge_transition(edge, from, to)?;
        check_optional_artifact(
            artifact_registry,
            edge.evidence_hash.as_ref(),
            "evidence_hash",
            ResearchDagArtifactKind::ResearchEvidence,
        )?;
        check_optional_artifact(
            artifact_registry,
            edge.checked_counterexample_hash.as_ref(),
            "checked_counterexample_hash",
            ResearchDagArtifactKind::CounterexampleReport,
        )?;
        check_optional_artifact(
            artifact_registry,
            edge.review_hash.as_ref(),
            "review_hash",
            ResearchDagArtifactKind::ReviewRecord,
        )?;
    }
    Ok(())
}

fn validate_edge_transition(
    edge: &ResearchDagEdge,
    from: &ResearchDagNode,
    to: &ResearchDagNode,
) -> Result<(), ResearchDagValidationError> {
    if matches!(
        edge.edge_kind,
        ResearchDagEdgeKind::Implies
            | ResearchDagEdgeKind::EquivalentTo
            | ResearchDagEdgeKind::Strengthens
            | ResearchDagEdgeKind::Weakens
            | ResearchDagEdgeKind::SupportedByExperiment
    ) && from.evidence_level < to.evidence_level
        && to.verified_artifact_identity_hash.is_none()
    {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::EvidenceLevelUpgradeRequiresVerifiedArtifact {
                edge_key: edge.edge_key.clone(),
                from_level: from.evidence_level,
                to_level: to.evidence_level,
            },
        ));
    }

    match edge.edge_kind {
        ResearchDagEdgeKind::Refutes if edge.checked_counterexample_hash.is_none() => {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::RefutesRequiresCheckedCounterexample {
                    edge_key: edge.edge_key.clone(),
                },
            ));
        }
        ResearchDagEdgeKind::EquivalentTo => {
            if edge.review_hash.is_none() {
                return Err(ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::EquivalentRequiresReview {
                        edge_key: edge.edge_key.clone(),
                    },
                ));
            }
            if edge.rewrites_target_statement {
                return Err(ResearchDagValidationError::new(
                    ResearchDagValidationErrorKind::EquivalentCannotRewriteTarget {
                        edge_key: edge.edge_key.clone(),
                    },
                ));
            }
        }
        ResearchDagEdgeKind::SupportedByExperiment
            if from.node_kind != ResearchDagNodeKind::ComputationalExperiment
                && to.node_kind != ResearchDagNodeKind::ComputationalExperiment =>
        {
            return Err(ResearchDagValidationError::new(
                ResearchDagValidationErrorKind::SupportedByExperimentRequiresExperimentNode {
                    edge_key: edge.edge_key.clone(),
                },
            ));
        }
        _ => {}
    }

    Ok(())
}

fn validate_acyclic(
    dag: &ResearchDag,
    node_by_key: &BTreeMap<&str, &ResearchDagNode>,
) -> Result<(), ResearchDagValidationError> {
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for edge in &dag.edges {
        if edge.edge_kind == ResearchDagEdgeKind::EquivalentTo {
            continue;
        }
        adjacency
            .entry(edge.from_node_key.as_str())
            .or_default()
            .push(edge.to_node_key.as_str());
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    for node_key in node_by_key.keys() {
        dfs_cycle(node_key, &adjacency, &mut visiting, &mut visited)?;
    }
    Ok(())
}

fn dfs_cycle<'a>(
    node_key: &'a str,
    adjacency: &BTreeMap<&'a str, Vec<&'a str>>,
    visiting: &mut BTreeSet<&'a str>,
    visited: &mut BTreeSet<&'a str>,
) -> Result<(), ResearchDagValidationError> {
    if visited.contains(node_key) {
        return Ok(());
    }
    if !visiting.insert(node_key) {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::CycleDetected {
                node_key: node_key.to_owned(),
            },
        ));
    }
    if let Some(next) = adjacency.get(node_key) {
        for next_key in next {
            dfs_cycle(next_key, adjacency, visiting, visited)?;
        }
    }
    visiting.remove(node_key);
    visited.insert(node_key);
    Ok(())
}

pub fn research_dag_node_kind_permits_evidence_level(
    kind: ResearchDagNodeKind,
    level: ResearchEvidenceLevel,
) -> bool {
    match kind {
        ResearchDagNodeKind::Definition
        | ResearchDagNodeKind::EquivalentFormulation
        | ResearchDagNodeKind::Reduction
        | ResearchDagNodeKind::CandidateLemma
        | ResearchDagNodeKind::BarrierResult
        | ResearchDagNodeKind::OpenBlocker => level == ResearchEvidenceLevel::E0,
        ResearchDagNodeKind::KnownTheorem => matches!(
            level,
            ResearchEvidenceLevel::E2
                | ResearchEvidenceLevel::E3
                | ResearchEvidenceLevel::E4
                | ResearchEvidenceLevel::E5
        ),
        ResearchDagNodeKind::SpecialCase => level == ResearchEvidenceLevel::E2,
        ResearchDagNodeKind::ConditionalLemma => level == ResearchEvidenceLevel::E3,
        ResearchDagNodeKind::ComputationalExperiment => level == ResearchEvidenceLevel::E1,
        ResearchDagNodeKind::CounterexampleSearch => matches!(
            level,
            ResearchEvidenceLevel::E1 | ResearchEvidenceLevel::E4 | ResearchEvidenceLevel::E5
        ),
    }
}

fn check_optional_artifact(
    artifact_registry: &BTreeMap<Hash, &ResearchDagArtifactReference>,
    artifact_hash: Option<&Hash>,
    field: &'static str,
    expected: ResearchDagArtifactKind,
) -> Result<(), ResearchDagValidationError> {
    if let Some(artifact_hash) = artifact_hash {
        check_artifact(artifact_registry, artifact_hash, field, expected)?;
    }
    Ok(())
}

fn check_artifact(
    artifact_registry: &BTreeMap<Hash, &ResearchDagArtifactReference>,
    artifact_hash: &Hash,
    field: &'static str,
    expected: ResearchDagArtifactKind,
) -> Result<(), ResearchDagValidationError> {
    let Some(reference) = artifact_registry.get(artifact_hash) else {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::MissingArtifactReference {
                field,
                artifact_hash: format_hash_string(artifact_hash),
            },
        ));
    };
    if !reference.current {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::StaleArtifactReference {
                field,
                artifact_hash: format_hash_string(artifact_hash),
            },
        ));
    }
    if reference.artifact_kind != expected {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::ArtifactKindMismatch {
                field,
                artifact_hash: format_hash_string(artifact_hash),
                expected,
                actual: reference.artifact_kind,
            },
        ));
    }
    Ok(())
}

fn require_non_empty(value: &str, field: &'static str) -> Result<(), ResearchDagValidationError> {
    if value.trim().is_empty() {
        return Err(ResearchDagValidationError::new(
            ResearchDagValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn parse_execution(
    value: &JsonValue<'_>,
) -> Result<ResearchDagExecutionBoundary, ResearchDagSchemaError> {
    let members = object_map(value, "$.execution", EXECUTION_FIELDS)?;
    Ok(ResearchDagExecutionBoundary {
        primary_plane: parse_execution_plane_value(
            required_value(&members, "primary_plane", "$.execution")?,
            "$.execution.primary_plane",
        )?,
        normal_verify_dependency: required_bool(
            &members,
            "normal_verify_dependency",
            "$.execution",
        )?,
        allowed_outputs: parse_allowed_outputs(required_value(
            &members,
            "allowed_outputs",
            "$.execution",
        )?)?,
        dependency_kind: parse_dependency_kind_value(
            required_value(&members, "dependency_kind", "$.execution")?,
            "$.execution.dependency_kind",
        )?,
        verified_artifact_identity_hash: optional_hash(
            &members,
            "verified_artifact_identity_hash",
            "$.execution",
        )?,
        dependency_release_trust_level: optional_string(
            &members,
            "dependency_release_trust_level",
            "$.execution",
        )?,
    })
}

fn parse_artifact_references(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchDagArtifactReference>, ResearchDagSchemaError> {
    array_elements(value, "$.artifact_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_artifact_reference(value, &format!("$.artifact_references[{index}]"))
        })
        .collect()
}

fn parse_artifact_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagArtifactReference, ResearchDagSchemaError> {
    let members = object_map(value, path, ARTIFACT_REFERENCE_FIELDS)?;
    Ok(ResearchDagArtifactReference {
        artifact_hash: required_hash(&members, "artifact_hash", path)?,
        artifact_kind: parse_artifact_kind_value(
            required_value(&members, "artifact_kind", path)?,
            &format!("{path}.artifact_kind"),
        )?,
        current: required_bool(&members, "current", path)?,
    })
}

fn parse_nodes(value: &JsonValue<'_>) -> Result<Vec<ResearchDagNode>, ResearchDagSchemaError> {
    array_elements(value, "$.nodes")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_node(value, &format!("$.nodes[{index}]")))
        .collect()
}

fn parse_node(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagNode, ResearchDagSchemaError> {
    let members = object_map(value, path, NODE_FIELDS)?;
    Ok(ResearchDagNode {
        node_key: required_string(&members, "node_key", path)?,
        node_kind: parse_node_kind_value(
            required_value(&members, "node_kind", path)?,
            &format!("{path}.node_kind"),
        )?,
        evidence_level: parse_evidence_level_value(
            required_value(&members, "evidence_level", path)?,
            &format!("{path}.evidence_level"),
        )?,
        statement_hash: optional_hash(&members, "statement_hash", path)?,
        verified_artifact_identity_hash: optional_hash(
            &members,
            "verified_artifact_identity_hash",
            path,
        )?,
        research_evidence_hash: optional_hash(&members, "research_evidence_hash", path)?,
        counterexample_or_refutation_hash: optional_hash(
            &members,
            "counterexample_or_refutation_hash",
            path,
        )?,
        experiment_artifact_hash: optional_hash(&members, "experiment_artifact_hash", path)?,
        barrier_audit_hash: optional_hash(&members, "barrier_audit_hash", path)?,
        review_hash: optional_hash(&members, "review_hash", path)?,
        assumption_hashes: parse_hash_array(
            required_value(&members, "assumption_hashes", path)?,
            &format!("{path}.assumption_hashes"),
        )?,
        sidecar_only: required_bool(&members, "sidecar_only", path)?,
        proof_claim: required_bool(&members, "proof_claim", path)?,
        creates_verified_artifact: required_bool(&members, "creates_verified_artifact", path)?,
        upgrades_verified_artifact: required_bool(&members, "upgrades_verified_artifact", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_edges(value: &JsonValue<'_>) -> Result<Vec<ResearchDagEdge>, ResearchDagSchemaError> {
    array_elements(value, "$.edges")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_edge(value, &format!("$.edges[{index}]")))
        .collect()
}

fn parse_edge(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagEdge, ResearchDagSchemaError> {
    let members = object_map(value, path, EDGE_FIELDS)?;
    Ok(ResearchDagEdge {
        edge_key: required_string(&members, "edge_key", path)?,
        from_node_key: required_string(&members, "from_node_key", path)?,
        to_node_key: required_string(&members, "to_node_key", path)?,
        edge_kind: parse_edge_kind_value(
            required_value(&members, "edge_kind", path)?,
            &format!("{path}.edge_kind"),
        )?,
        evidence_hash: optional_hash(&members, "evidence_hash", path)?,
        checked_counterexample_hash: optional_hash(&members, "checked_counterexample_hash", path)?,
        review_hash: optional_hash(&members, "review_hash", path)?,
        rewrites_target_statement: required_bool(&members, "rewrites_target_statement", path)?,
        dependency_release_attempt: required_bool(&members, "dependency_release_attempt", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_allowed_outputs(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchDagAllowedOutput>, ResearchDagSchemaError> {
    array_elements(value, "$.execution.allowed_outputs")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_allowed_output_value(value, &format!("$.execution.allowed_outputs[{index}]"))
        })
        .collect()
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, ResearchDagSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_evidence_level_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchEvidenceLevel, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchEvidenceLevel::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidEvidenceLevel { value: wire },
        )
    })
}

fn parse_execution_plane_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagExecutionPlane, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagExecutionPlane::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidExecutionPlane { value: wire },
        )
    })
}

fn parse_allowed_output_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagAllowedOutput, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagAllowedOutput::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidAllowedOutput { value: wire },
        )
    })
}

fn parse_dependency_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagDependencyKind, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagDependencyKind::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidDependencyKind { value: wire },
        )
    })
}

fn parse_artifact_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagArtifactKind, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagArtifactKind::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidArtifactKind { value: wire },
        )
    })
}

fn parse_node_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagNodeKind, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagNodeKind::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidNodeKind { value: wire },
        )
    })
}

fn parse_edge_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchDagEdgeKind, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    ResearchDagEdgeKind::parse(&wire).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidEdgeKind { value: wire },
        )
    })
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ResearchDagSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ResearchDagSchemaError::new(
            "$",
            ResearchDagSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ResearchDagSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ResearchDagSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchDagSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ResearchDagSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchDagSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ResearchDagSchemaError> {
    value.array_elements().ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ResearchDagSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ResearchDagSchemaError::new(
            format!("{path}.{field}"),
            ResearchDagSchemaErrorKind::MissingField { field },
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
) -> Result<String, ResearchDagSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ResearchDagSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ResearchDagSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ResearchDagSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ResearchDagSchemaError> {
    value.bool_value().ok_or_else(|| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ResearchDagSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, ResearchDagSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ResearchDagSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ResearchDagSchemaError::new(
            path,
            ResearchDagSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

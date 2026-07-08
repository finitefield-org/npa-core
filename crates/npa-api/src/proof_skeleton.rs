use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const PROOF_SKELETON_API_VERSION: &str = "npa.proof-skeleton.v1";
pub const PROOF_SKELETON_HASH_DOMAIN: &str = "npa.proof-skeleton.skeleton-hash.v1";
pub const PROOF_SKELETON_HOLE_HASH_DOMAIN: &str = "npa.proof-skeleton.hole-hash.v1";
pub const PROOF_SKELETON_CORE_EXPR_ENCODING: &str = "npa.core-expr.canonical-bytes.v0.1";
pub const PROOF_SKELETON_CORE_EXPR_ARTIFACT_SCHEMA: &str = "npa.core-expr-artifact.v0.1";
pub const PROOF_SKELETON_TERM_KINDS: &[&str] = &["core", "app", "lam", "let", "hole"];

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "skeleton_id",
    "target_statement_identity",
    "environment_hash",
    "policy_hash",
    "root",
    "holes",
];
const TARGET_IDENTITY_FIELDS: &[&str] = &[
    "statement_hash",
    "expected_type_hash",
    "root_context_hash",
    "module",
    "declaration",
];
const TERM_FIELDS: &[&str] = &[
    "kind",
    "core_expr",
    "function",
    "argument",
    "binder_type",
    "value",
    "body",
    "hole_id",
];
const TERM_CORE_FIELDS: &[&str] = &["kind", "core_expr"];
const TERM_APP_FIELDS: &[&str] = &["kind", "function", "argument"];
const TERM_LAM_FIELDS: &[&str] = &["kind", "binder_type", "body"];
const TERM_LET_FIELDS: &[&str] = &["kind", "binder_type", "value", "body"];
const TERM_HOLE_FIELDS: &[&str] = &["kind", "hole_id"];
const CORE_EXPR_SOURCE_FIELDS: &[&str] = &[
    "kind",
    "encoding",
    "core_expr_hash",
    "canonical_bytes_hex",
    "artifact_schema",
    "artifact_hash",
    "size_bytes",
];
const INLINE_CORE_EXPR_FIELDS: &[&str] =
    &["kind", "encoding", "core_expr_hash", "canonical_bytes_hex"];
const ARTIFACT_CORE_EXPR_FIELDS: &[&str] = &[
    "kind",
    "artifact_schema",
    "artifact_hash",
    "core_expr_hash",
    "size_bytes",
];
const HOLE_FIELDS: &[&str] = &[
    "hole_id",
    "local_context_identity",
    "expected_type_identity",
    "dependent_hole_ids",
    "allowed_premise_identities",
    "strategy_profile",
    "budget",
    "stale_solution_rejection",
];
const LOCAL_CONTEXT_FIELDS: &[&str] = &["context_hash", "binder_fingerprint_hash"];
const EXPECTED_TYPE_FIELDS: &[&str] = &["expected_type_hash", "expected_type"];
const PREMISE_IDENTITY_FIELDS: &[&str] = &["premise_hash", "source", "axiom_profile_hash"];
const STRATEGY_PROFILE_FIELDS: &[&str] = &["profile_id", "preferred_node_kinds"];
const BUDGET_FIELDS: &[&str] = &[
    "max_candidates",
    "max_search_nodes",
    "max_depth",
    "max_repair_steps",
];
const STALE_SOLUTION_FIELDS: &[&str] = &[
    "required_context_hash",
    "required_expected_type_hash",
    "required_environment_hash",
    "required_policy_hash",
];
const MAX_HOLES: usize = 1000;
const MAX_DEPENDENT_HOLES: usize = 1000;
const MAX_ALLOWED_PREMISES: usize = 256;
const MAX_PREFERRED_NODE_KINDS: usize = 32;
const MAX_CORE_EXPR_BYTES: usize = 65_536;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeleton {
    pub api_version: String,
    pub skeleton_id: Hash,
    pub target_statement_identity: ProofSkeletonTargetStatementIdentity,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub root: ProofSkeletonTerm,
    pub holes: Vec<ProofSkeletonHole>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonTargetStatementIdentity {
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub root_context_hash: Hash,
    pub module: Option<String>,
    pub declaration: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSkeletonTerm {
    Core {
        core_expr: ProofSkeletonCoreExpr,
    },
    App {
        function: Box<ProofSkeletonTerm>,
        argument: Box<ProofSkeletonTerm>,
    },
    Lam {
        binder_type: ProofSkeletonCoreExpr,
        body: Box<ProofSkeletonTerm>,
    },
    Let {
        binder_type: ProofSkeletonCoreExpr,
        value: Box<ProofSkeletonTerm>,
        body: Box<ProofSkeletonTerm>,
    },
    Hole {
        hole_id: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSkeletonCoreExpr {
    Inline {
        core_expr_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        artifact_hash: Hash,
        core_expr_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
}

impl ProofSkeletonCoreExpr {
    pub fn core_expr_hash(&self) -> &Hash {
        match self {
            Self::Inline { core_expr_hash, .. } | Self::Artifact { core_expr_hash, .. } => {
                core_expr_hash
            }
        }
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        match self {
            Self::Inline {
                canonical_bytes, ..
            }
            | Self::Artifact {
                canonical_bytes, ..
            } => canonical_bytes,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonResolvedCoreExprArtifact {
    pub artifact_hash: Hash,
    pub core_expr_hash: Hash,
    pub canonical_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonHole {
    pub hole_id: String,
    pub local_context_identity: ProofSkeletonLocalContextIdentity,
    pub expected_type_identity: ProofSkeletonExpectedTypeIdentity,
    pub dependent_hole_ids: Vec<String>,
    pub allowed_premise_identities: Vec<ProofSkeletonPremiseIdentity>,
    pub strategy_profile: ProofSkeletonStrategyProfile,
    pub budget: ProofSkeletonBudget,
    pub stale_solution_rejection: ProofSkeletonStaleSolutionRejection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonLocalContextIdentity {
    pub context_hash: Hash,
    pub binder_fingerprint_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonExpectedTypeIdentity {
    pub expected_type_hash: Hash,
    pub expected_type: ProofSkeletonCoreExpr,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProofSkeletonPremiseIdentity {
    pub premise_hash: Hash,
    pub source: ProofSkeletonPremiseSource,
    pub axiom_profile_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSkeletonPremiseSource {
    LocalContext,
    VerifiedImport,
    VerifiedLocalLemma,
}

impl ProofSkeletonPremiseSource {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "local_context" => Some(Self::LocalContext),
            "verified_import" => Some(Self::VerifiedImport),
            "verified_local_lemma" => Some(Self::VerifiedLocalLemma),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::LocalContext => "local_context",
            Self::VerifiedImport => "verified_import",
            Self::VerifiedLocalLemma => "verified_local_lemma",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonStrategyProfile {
    pub profile_id: ProofSkeletonStrategyProfileId,
    pub preferred_node_kinds: Vec<ProofSkeletonPreferredNodeKind>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSkeletonStrategyProfileId {
    Exact,
    Rewrite,
    Solver,
    Search,
    LocalLemma,
}

impl ProofSkeletonStrategyProfileId {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "exact" => Some(Self::Exact),
            "rewrite" => Some(Self::Rewrite),
            "solver" => Some(Self::Solver),
            "search" => Some(Self::Search),
            "local_lemma" => Some(Self::LocalLemma),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Rewrite => "rewrite",
            Self::Solver => "solver",
            Self::Search => "search",
            Self::LocalLemma => "local_lemma",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofSkeletonPreferredNodeKind {
    Introduce,
    CaseSplit,
    Induction,
    AssertLemma,
    ApplyPremise,
    RewritePhase,
    SolverPhase,
    CloseByExact,
    SearchSubgoal,
}

impl ProofSkeletonPreferredNodeKind {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "introduce" => Some(Self::Introduce),
            "case_split" => Some(Self::CaseSplit),
            "induction" => Some(Self::Induction),
            "assert_lemma" => Some(Self::AssertLemma),
            "apply_premise" => Some(Self::ApplyPremise),
            "rewrite_phase" => Some(Self::RewritePhase),
            "solver_phase" => Some(Self::SolverPhase),
            "close_by_exact" => Some(Self::CloseByExact),
            "search_subgoal" => Some(Self::SearchSubgoal),
            _ => None,
        }
    }

    const fn wire(self) -> &'static str {
        match self {
            Self::Introduce => "introduce",
            Self::CaseSplit => "case_split",
            Self::Induction => "induction",
            Self::AssertLemma => "assert_lemma",
            Self::ApplyPremise => "apply_premise",
            Self::RewritePhase => "rewrite_phase",
            Self::SolverPhase => "solver_phase",
            Self::CloseByExact => "close_by_exact",
            Self::SearchSubgoal => "search_subgoal",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonBudget {
    pub max_candidates: u64,
    pub max_search_nodes: u64,
    pub max_depth: Option<u64>,
    pub max_repair_steps: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonStaleSolutionRejection {
    pub required_context_hash: Hash,
    pub required_expected_type_hash: Hash,
    pub required_environment_hash: Hash,
    pub required_policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSkeletonSchemaError {
    path: String,
    kind: ProofSkeletonSchemaErrorKind,
}

impl ProofSkeletonSchemaError {
    fn new(path: impl Into<String>, kind: ProofSkeletonSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ProofSkeletonSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSkeletonSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ProofSkeletonSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSkeletonSchemaErrorKind {
    JsonParse {
        offset: usize,
    },
    ExpectedObject {
        actual: JsonValueKind,
    },
    ExpectedArray {
        actual: JsonValueKind,
    },
    ExpectedString {
        actual: JsonValueKind,
    },
    ExpectedInteger {
        actual: JsonValueKind,
    },
    DuplicateKey {
        key: String,
    },
    UnknownField {
        field: String,
    },
    MissingField {
        field: &'static str,
    },
    InvalidApiVersion {
        value: String,
    },
    InvalidHash {
        value: String,
    },
    InvalidIdentifier {
        value: String,
    },
    InvalidTermKind {
        value: String,
    },
    InvalidCoreExprSourceKind {
        value: String,
    },
    InvalidCoreExprEncoding {
        value: String,
    },
    InvalidCoreExprArtifactSchema {
        value: String,
    },
    InvalidHexBytes {
        value: String,
    },
    CoreExprHashMismatch {
        declared: String,
        actual: String,
    },
    UnresolvedArtifactReference {
        artifact_hash: String,
    },
    ArtifactIdentityMismatch {
        artifact_hash: String,
    },
    ExpectedTypeHashMismatch {
        hole_id: String,
        declared: String,
        actual: String,
    },
    InvalidPremiseSource {
        value: String,
    },
    InvalidStrategyProfile {
        value: String,
    },
    InvalidPreferredNodeKind {
        value: String,
    },
    InvalidInteger {
        value: String,
    },
    IntegerOutOfRange {
        value: String,
    },
    ArrayLengthOutOfRange {
        min: usize,
        max: usize,
        actual: usize,
    },
    DuplicateHoleId {
        hole_id: String,
    },
    UnknownHoleReference {
        hole_id: String,
    },
    DuplicateDependentHoleId {
        hole_id: String,
    },
    DuplicatePremiseIdentity {
        premise_hash: String,
    },
    StaleContextHashMismatch {
        hole_id: String,
    },
    StaleExpectedTypeHashMismatch {
        hole_id: String,
    },
    StaleEnvironmentHashMismatch {
        hole_id: String,
    },
    StalePolicyHashMismatch {
        hole_id: String,
    },
    StringLengthOutOfRange {
        min: usize,
        max: usize,
        actual: usize,
    },
}

impl fmt::Display for ProofSkeletonSchemaErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JsonParse { offset } => write!(f, "json parse error at byte {offset}"),
            Self::ExpectedObject { actual } => write!(f, "expected object, found {actual:?}"),
            Self::ExpectedArray { actual } => write!(f, "expected array, found {actual:?}"),
            Self::ExpectedString { actual } => write!(f, "expected string, found {actual:?}"),
            Self::ExpectedInteger { actual } => write!(f, "expected integer, found {actual:?}"),
            Self::DuplicateKey { key } => write!(f, "duplicate key `{key}`"),
            Self::UnknownField { field } => write!(f, "unknown field `{field}`"),
            Self::MissingField { field } => write!(f, "missing field `{field}`"),
            Self::InvalidApiVersion { value } => write!(f, "invalid api version `{value}`"),
            Self::InvalidHash { value } => write!(f, "invalid hash `{value}`"),
            Self::InvalidIdentifier { value } => write!(f, "invalid identifier `{value}`"),
            Self::InvalidTermKind { value } => write!(f, "invalid term kind `{value}`"),
            Self::InvalidCoreExprSourceKind { value } => {
                write!(f, "invalid core expr source kind `{value}`")
            }
            Self::InvalidCoreExprEncoding { value } => {
                write!(f, "invalid core expr encoding `{value}`")
            }
            Self::InvalidCoreExprArtifactSchema { value } => {
                write!(f, "invalid core expr artifact schema `{value}`")
            }
            Self::InvalidHexBytes { value } => write!(f, "invalid hex bytes `{value}`"),
            Self::CoreExprHashMismatch { declared, actual } => {
                write!(f, "core expr hash mismatch declared `{declared}` actual `{actual}`")
            }
            Self::UnresolvedArtifactReference { artifact_hash } => {
                write!(f, "unresolved core expr artifact `{artifact_hash}`")
            }
            Self::ArtifactIdentityMismatch { artifact_hash } => {
                write!(f, "resolved artifact identity mismatch `{artifact_hash}`")
            }
            Self::ExpectedTypeHashMismatch {
                hole_id,
                declared,
                actual,
            } => write!(
                f,
                "expected type hash mismatch for `{hole_id}` declared `{declared}` actual `{actual}`"
            ),
            Self::InvalidPremiseSource { value } => write!(f, "invalid premise source `{value}`"),
            Self::InvalidStrategyProfile { value } => {
                write!(f, "invalid strategy profile `{value}`")
            }
            Self::InvalidPreferredNodeKind { value } => {
                write!(f, "invalid preferred node kind `{value}`")
            }
            Self::InvalidInteger { value } => write!(f, "invalid integer `{value}`"),
            Self::IntegerOutOfRange { value } => write!(f, "integer out of range `{value}`"),
            Self::ArrayLengthOutOfRange { min, max, actual } => write!(
                f,
                "array length {actual} is outside allowed range {min}..={max}"
            ),
            Self::DuplicateHoleId { hole_id } => write!(f, "duplicate hole id `{hole_id}`"),
            Self::UnknownHoleReference { hole_id } => {
                write!(f, "unknown hole reference `{hole_id}`")
            }
            Self::DuplicateDependentHoleId { hole_id } => {
                write!(f, "duplicate dependent hole id `{hole_id}`")
            }
            Self::DuplicatePremiseIdentity { premise_hash } => {
                write!(f, "duplicate premise identity `{premise_hash}`")
            }
            Self::StaleContextHashMismatch { hole_id } => {
                write!(f, "stale context rejection mismatch for `{hole_id}`")
            }
            Self::StaleExpectedTypeHashMismatch { hole_id } => {
                write!(f, "stale expected type rejection mismatch for `{hole_id}`")
            }
            Self::StaleEnvironmentHashMismatch { hole_id } => {
                write!(f, "stale environment rejection mismatch for `{hole_id}`")
            }
            Self::StalePolicyHashMismatch { hole_id } => {
                write!(f, "stale policy rejection mismatch for `{hole_id}`")
            }
            Self::StringLengthOutOfRange { min, max, actual } => write!(
                f,
                "string length {actual} is outside allowed range {min}..={max}"
            ),
        }
    }
}

pub fn parse_proof_skeleton(source: &str) -> Result<ProofSkeleton, ProofSkeletonSchemaError> {
    parse_proof_skeleton_with_artifacts(source, &[])
}

pub fn parse_proof_skeleton_with_artifacts(
    source: &str,
    artifacts: &[ProofSkeletonResolvedCoreExprArtifact],
) -> Result<ProofSkeleton, ProofSkeletonSchemaError> {
    let document = JsonDocument::parse(source).map_err(|err| {
        ProofSkeletonSchemaError::new(
            "$",
            ProofSkeletonSchemaErrorKind::JsonParse { offset: err.offset },
        )
    })?;
    let artifact_map: BTreeMap<Hash, &ProofSkeletonResolvedCoreExprArtifact> = artifacts
        .iter()
        .map(|artifact| (artifact.artifact_hash, artifact))
        .collect();
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;

    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != PROOF_SKELETON_API_VERSION {
        return Err(ProofSkeletonSchemaError::new(
            "$.api_version",
            ProofSkeletonSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    let skeleton_id = required_hash(&root, "skeleton_id", "$")?;
    let target_statement_identity =
        parse_target_statement_identity(required_value(&root, "target_statement_identity", "$")?)?;
    let environment_hash = required_hash(&root, "environment_hash", "$")?;
    let policy_hash = required_hash(&root, "policy_hash", "$")?;
    let root_term = parse_term(required_value(&root, "root", "$")?, "$.root", &artifact_map)?;
    let mut holes = parse_holes(
        required_value(&root, "holes", "$")?,
        &artifact_map,
        &environment_hash,
        &policy_hash,
    )?;
    holes.sort_by(|left, right| left.hole_id.cmp(&right.hole_id));
    validate_hole_references(&root_term, &holes)?;

    Ok(ProofSkeleton {
        api_version,
        skeleton_id,
        target_statement_identity,
        environment_hash,
        policy_hash,
        root: root_term,
        holes,
    })
}

pub fn proof_skeleton_canonical_identity_bytes(skeleton: &ProofSkeleton) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKELETON_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &skeleton.api_version);
    encode_string_to(&mut out, "target_statement_identity");
    encode_target_statement_identity_to(&mut out, &skeleton.target_statement_identity);
    encode_string_to(&mut out, "environment_hash");
    encode_hash_to(&mut out, &skeleton.environment_hash);
    encode_string_to(&mut out, "policy_hash");
    encode_hash_to(&mut out, &skeleton.policy_hash);
    encode_string_to(&mut out, "root");
    encode_term_to(&mut out, &skeleton.root);
    encode_string_to(&mut out, "holes");
    let mut holes = skeleton.holes.iter().collect::<Vec<_>>();
    holes.sort_by(|left, right| left.hole_id.cmp(&right.hole_id));
    encode_len_to(&mut out, holes.len());
    for hole in holes {
        encode_hole_to(&mut out, hole);
    }
    out
}

pub fn proof_skeleton_hash(skeleton: &ProofSkeleton) -> Hash {
    let digest = Sha256::digest(proof_skeleton_canonical_identity_bytes(skeleton));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_skeleton_hash_string(skeleton: &ProofSkeleton) -> String {
    format_hash_string(&proof_skeleton_hash(skeleton))
}

pub fn proof_skeleton_hole_canonical_identity_bytes(hole: &ProofSkeletonHole) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_SKELETON_HOLE_HASH_DOMAIN);
    encode_hole_to(&mut out, hole);
    out
}

pub fn proof_skeleton_hole_hash(hole: &ProofSkeletonHole) -> Hash {
    let digest = Sha256::digest(proof_skeleton_hole_canonical_identity_bytes(hole));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn proof_skeleton_hole_hash_string(hole: &ProofSkeletonHole) -> String {
    format_hash_string(&proof_skeleton_hole_hash(hole))
}

fn parse_target_statement_identity(
    value: &JsonValue<'_>,
) -> Result<ProofSkeletonTargetStatementIdentity, ProofSkeletonSchemaError> {
    let path = "$.target_statement_identity";
    let members = object_map(value, path, TARGET_IDENTITY_FIELDS)?;
    Ok(ProofSkeletonTargetStatementIdentity {
        statement_hash: required_hash(&members, "statement_hash", path)?,
        expected_type_hash: required_hash(&members, "expected_type_hash", path)?,
        root_context_hash: required_hash(&members, "root_context_hash", path)?,
        module: optional_bounded_string(&members, "module", path, 1, 256)?,
        declaration: optional_bounded_string(&members, "declaration", path, 1, 256)?,
    })
}

fn parse_term(
    value: &JsonValue<'_>,
    path: &str,
    artifacts: &BTreeMap<Hash, &ProofSkeletonResolvedCoreExprArtifact>,
) -> Result<ProofSkeletonTerm, ProofSkeletonSchemaError> {
    let generic = object_map(value, path, TERM_FIELDS)?;
    let kind = required_string(&generic, "kind", path)?;
    match kind.as_str() {
        "core" => {
            let members = object_map(value, path, TERM_CORE_FIELDS)?;
            Ok(ProofSkeletonTerm::Core {
                core_expr: parse_core_expr_source(
                    required_value(&members, "core_expr", path)?,
                    &format!("{path}.core_expr"),
                    artifacts,
                )?,
            })
        }
        "app" => {
            let members = object_map(value, path, TERM_APP_FIELDS)?;
            Ok(ProofSkeletonTerm::App {
                function: Box::new(parse_term(
                    required_value(&members, "function", path)?,
                    &format!("{path}.function"),
                    artifacts,
                )?),
                argument: Box::new(parse_term(
                    required_value(&members, "argument", path)?,
                    &format!("{path}.argument"),
                    artifacts,
                )?),
            })
        }
        "lam" => {
            let members = object_map(value, path, TERM_LAM_FIELDS)?;
            Ok(ProofSkeletonTerm::Lam {
                binder_type: parse_core_expr_source(
                    required_value(&members, "binder_type", path)?,
                    &format!("{path}.binder_type"),
                    artifacts,
                )?,
                body: Box::new(parse_term(
                    required_value(&members, "body", path)?,
                    &format!("{path}.body"),
                    artifacts,
                )?),
            })
        }
        "let" => {
            let members = object_map(value, path, TERM_LET_FIELDS)?;
            Ok(ProofSkeletonTerm::Let {
                binder_type: parse_core_expr_source(
                    required_value(&members, "binder_type", path)?,
                    &format!("{path}.binder_type"),
                    artifacts,
                )?,
                value: Box::new(parse_term(
                    required_value(&members, "value", path)?,
                    &format!("{path}.value"),
                    artifacts,
                )?),
                body: Box::new(parse_term(
                    required_value(&members, "body", path)?,
                    &format!("{path}.body"),
                    artifacts,
                )?),
            })
        }
        "hole" => {
            let members = object_map(value, path, TERM_HOLE_FIELDS)?;
            Ok(ProofSkeletonTerm::Hole {
                hole_id: required_identifier(&members, "hole_id", path)?,
            })
        }
        _ => Err(ProofSkeletonSchemaError::new(
            format!("{path}.kind"),
            ProofSkeletonSchemaErrorKind::InvalidTermKind { value: kind },
        )),
    }
}

fn parse_core_expr_source(
    value: &JsonValue<'_>,
    path: &str,
    artifacts: &BTreeMap<Hash, &ProofSkeletonResolvedCoreExprArtifact>,
) -> Result<ProofSkeletonCoreExpr, ProofSkeletonSchemaError> {
    let generic = object_map(value, path, CORE_EXPR_SOURCE_FIELDS)?;
    let kind = required_string(&generic, "kind", path)?;
    match kind.as_str() {
        "inline_core_expr" => {
            let members = object_map(value, path, INLINE_CORE_EXPR_FIELDS)?;
            let encoding = required_string(&members, "encoding", path)?;
            if encoding != PROOF_SKELETON_CORE_EXPR_ENCODING {
                return Err(ProofSkeletonSchemaError::new(
                    format!("{path}.encoding"),
                    ProofSkeletonSchemaErrorKind::InvalidCoreExprEncoding { value: encoding },
                ));
            }
            let declared = required_hash(&members, "core_expr_hash", path)?;
            let canonical_bytes =
                required_hex_bytes(&members, "canonical_bytes_hex", path, MAX_CORE_EXPR_BYTES)?;
            let actual = sha256_hash(&canonical_bytes);
            if declared != actual {
                return Err(ProofSkeletonSchemaError::new(
                    format!("{path}.core_expr_hash"),
                    ProofSkeletonSchemaErrorKind::CoreExprHashMismatch {
                        declared: format_hash_string(&declared),
                        actual: format_hash_string(&actual),
                    },
                ));
            }
            Ok(ProofSkeletonCoreExpr::Inline {
                core_expr_hash: declared,
                canonical_bytes,
            })
        }
        "core_expr_artifact" => {
            let members = object_map(value, path, ARTIFACT_CORE_EXPR_FIELDS)?;
            let schema = required_string(&members, "artifact_schema", path)?;
            if schema != PROOF_SKELETON_CORE_EXPR_ARTIFACT_SCHEMA {
                return Err(ProofSkeletonSchemaError::new(
                    format!("{path}.artifact_schema"),
                    ProofSkeletonSchemaErrorKind::InvalidCoreExprArtifactSchema { value: schema },
                ));
            }
            let artifact_hash = required_hash(&members, "artifact_hash", path)?;
            let declared_core_expr_hash = required_hash(&members, "core_expr_hash", path)?;
            let size_bytes = required_u64_in_range(&members, "size_bytes", path, 1, 1_048_576)?;
            let Some(resolved) = artifacts.get(&artifact_hash) else {
                return Err(ProofSkeletonSchemaError::new(
                    format!("{path}.artifact_hash"),
                    ProofSkeletonSchemaErrorKind::UnresolvedArtifactReference {
                        artifact_hash: format_hash_string(&artifact_hash),
                    },
                ));
            };
            if resolved.core_expr_hash != declared_core_expr_hash
                || resolved.canonical_bytes.len() as u64 != size_bytes
                || sha256_hash(&resolved.canonical_bytes) != declared_core_expr_hash
            {
                return Err(ProofSkeletonSchemaError::new(
                    path,
                    ProofSkeletonSchemaErrorKind::ArtifactIdentityMismatch {
                        artifact_hash: format_hash_string(&artifact_hash),
                    },
                ));
            }
            Ok(ProofSkeletonCoreExpr::Artifact {
                artifact_hash,
                core_expr_hash: declared_core_expr_hash,
                canonical_bytes: resolved.canonical_bytes.clone(),
            })
        }
        _ => Err(ProofSkeletonSchemaError::new(
            format!("{path}.kind"),
            ProofSkeletonSchemaErrorKind::InvalidCoreExprSourceKind { value: kind },
        )),
    }
}

fn parse_holes(
    value: &JsonValue<'_>,
    artifacts: &BTreeMap<Hash, &ProofSkeletonResolvedCoreExprArtifact>,
    environment_hash: &Hash,
    policy_hash: &Hash,
) -> Result<Vec<ProofSkeletonHole>, ProofSkeletonSchemaError> {
    let elements = array_elements(value, "$.holes")?;
    enforce_array_len("$.holes", elements.len(), 0, MAX_HOLES)?;
    let mut holes = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let path = format!("$.holes[{index}]");
        let members = object_map(element, &path, HOLE_FIELDS)?;
        let hole_id = required_identifier(&members, "hole_id", &path)?;
        if !seen.insert(hole_id.clone()) {
            return Err(ProofSkeletonSchemaError::new(
                format!("{path}.hole_id"),
                ProofSkeletonSchemaErrorKind::DuplicateHoleId { hole_id },
            ));
        }
        let local_context_identity = parse_local_context_identity(
            required_value(&members, "local_context_identity", &path)?,
            &format!("{path}.local_context_identity"),
        )?;
        let expected_type_identity = parse_expected_type_identity(
            required_value(&members, "expected_type_identity", &path)?,
            &format!("{path}.expected_type_identity"),
            &hole_id,
            artifacts,
        )?;
        let dependent_hole_ids = parse_dependent_hole_ids(
            required_value(&members, "dependent_hole_ids", &path)?,
            &format!("{path}.dependent_hole_ids"),
        )?;
        let allowed_premise_identities = parse_allowed_premise_identities(
            required_value(&members, "allowed_premise_identities", &path)?,
            &format!("{path}.allowed_premise_identities"),
        )?;
        let strategy_profile = parse_strategy_profile(
            required_value(&members, "strategy_profile", &path)?,
            &format!("{path}.strategy_profile"),
        )?;
        let budget = parse_budget(
            required_value(&members, "budget", &path)?,
            &format!("{path}.budget"),
        )?;
        let stale_solution_rejection = parse_stale_solution_rejection(
            required_value(&members, "stale_solution_rejection", &path)?,
            &format!("{path}.stale_solution_rejection"),
        )?;
        validate_stale_solution_rejection(
            &hole_id,
            &local_context_identity,
            &expected_type_identity,
            &stale_solution_rejection,
            environment_hash,
            policy_hash,
        )?;
        holes.push(ProofSkeletonHole {
            hole_id,
            local_context_identity,
            expected_type_identity,
            dependent_hole_ids,
            allowed_premise_identities,
            strategy_profile,
            budget,
            stale_solution_rejection,
        });
    }
    Ok(holes)
}

fn parse_local_context_identity(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSkeletonLocalContextIdentity, ProofSkeletonSchemaError> {
    let members = object_map(value, path, LOCAL_CONTEXT_FIELDS)?;
    Ok(ProofSkeletonLocalContextIdentity {
        context_hash: required_hash(&members, "context_hash", path)?,
        binder_fingerprint_hash: required_hash(&members, "binder_fingerprint_hash", path)?,
    })
}

fn parse_expected_type_identity(
    value: &JsonValue<'_>,
    path: &str,
    hole_id: &str,
    artifacts: &BTreeMap<Hash, &ProofSkeletonResolvedCoreExprArtifact>,
) -> Result<ProofSkeletonExpectedTypeIdentity, ProofSkeletonSchemaError> {
    let members = object_map(value, path, EXPECTED_TYPE_FIELDS)?;
    let expected_type_hash = required_hash(&members, "expected_type_hash", path)?;
    let expected_type = parse_core_expr_source(
        required_value(&members, "expected_type", path)?,
        &format!("{path}.expected_type"),
        artifacts,
    )?;
    if *expected_type.core_expr_hash() != expected_type_hash {
        return Err(ProofSkeletonSchemaError::new(
            format!("{path}.expected_type_hash"),
            ProofSkeletonSchemaErrorKind::ExpectedTypeHashMismatch {
                hole_id: hole_id.to_owned(),
                declared: format_hash_string(&expected_type_hash),
                actual: format_hash_string(expected_type.core_expr_hash()),
            },
        ));
    }
    Ok(ProofSkeletonExpectedTypeIdentity {
        expected_type_hash,
        expected_type,
    })
}

fn parse_dependent_hole_ids(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<String>, ProofSkeletonSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), 0, MAX_DEPENDENT_HOLES)?;
    let mut ids = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let hole_id = identifier_value(element, &item_path)?;
        if !seen.insert(hole_id.clone()) {
            return Err(ProofSkeletonSchemaError::new(
                item_path,
                ProofSkeletonSchemaErrorKind::DuplicateDependentHoleId { hole_id },
            ));
        }
        ids.push(hole_id);
    }
    ids.sort();
    Ok(ids)
}

fn parse_allowed_premise_identities(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<ProofSkeletonPremiseIdentity>, ProofSkeletonSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), 0, MAX_ALLOWED_PREMISES)?;
    let mut premises = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let members = object_map(element, &item_path, PREMISE_IDENTITY_FIELDS)?;
        let source_wire = required_string(&members, "source", &item_path)?;
        let source = ProofSkeletonPremiseSource::parse(&source_wire).ok_or_else(|| {
            ProofSkeletonSchemaError::new(
                format!("{item_path}.source"),
                ProofSkeletonSchemaErrorKind::InvalidPremiseSource { value: source_wire },
            )
        })?;
        let premise = ProofSkeletonPremiseIdentity {
            premise_hash: required_hash(&members, "premise_hash", &item_path)?,
            source,
            axiom_profile_hash: required_hash(&members, "axiom_profile_hash", &item_path)?,
        };
        if !seen.insert(premise.clone()) {
            return Err(ProofSkeletonSchemaError::new(
                item_path,
                ProofSkeletonSchemaErrorKind::DuplicatePremiseIdentity {
                    premise_hash: format_hash_string(&premise.premise_hash),
                },
            ));
        }
        premises.push(premise);
    }
    premises.sort();
    Ok(premises)
}

fn parse_strategy_profile(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSkeletonStrategyProfile, ProofSkeletonSchemaError> {
    let members = object_map(value, path, STRATEGY_PROFILE_FIELDS)?;
    let profile_wire = required_string(&members, "profile_id", path)?;
    let profile_id = ProofSkeletonStrategyProfileId::parse(&profile_wire).ok_or_else(|| {
        ProofSkeletonSchemaError::new(
            format!("{path}.profile_id"),
            ProofSkeletonSchemaErrorKind::InvalidStrategyProfile {
                value: profile_wire,
            },
        )
    })?;
    let preferred_node_kinds = optional_value(&members, "preferred_node_kinds")
        .map(|value| parse_preferred_node_kinds(value, &format!("{path}.preferred_node_kinds")))
        .transpose()?
        .unwrap_or_default();
    Ok(ProofSkeletonStrategyProfile {
        profile_id,
        preferred_node_kinds,
    })
}

fn parse_preferred_node_kinds(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<ProofSkeletonPreferredNodeKind>, ProofSkeletonSchemaError> {
    let elements = array_elements(value, path)?;
    enforce_array_len(path, elements.len(), 0, MAX_PREFERRED_NODE_KINDS)?;
    let mut kinds = Vec::with_capacity(elements.len());
    let mut seen = BTreeSet::new();
    for (index, element) in elements.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let wire = string_value(element, &item_path)?;
        let kind = ProofSkeletonPreferredNodeKind::parse(&wire).ok_or_else(|| {
            ProofSkeletonSchemaError::new(
                item_path.clone(),
                ProofSkeletonSchemaErrorKind::InvalidPreferredNodeKind { value: wire },
            )
        })?;
        if seen.insert(kind) {
            kinds.push(kind);
        }
    }
    kinds.sort();
    Ok(kinds)
}

fn parse_budget(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSkeletonBudget, ProofSkeletonSchemaError> {
    let members = object_map(value, path, BUDGET_FIELDS)?;
    Ok(ProofSkeletonBudget {
        max_candidates: required_u64_in_range(&members, "max_candidates", path, 0, 1_000_000)?,
        max_search_nodes: required_u64_in_range(&members, "max_search_nodes", path, 0, 1_000_000)?,
        max_depth: optional_u64_in_range(&members, "max_depth", path, 0, 1_000_000)?,
        max_repair_steps: optional_u64_in_range(&members, "max_repair_steps", path, 0, 1_000_000)?,
    })
}

fn parse_stale_solution_rejection(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ProofSkeletonStaleSolutionRejection, ProofSkeletonSchemaError> {
    let members = object_map(value, path, STALE_SOLUTION_FIELDS)?;
    Ok(ProofSkeletonStaleSolutionRejection {
        required_context_hash: required_hash(&members, "required_context_hash", path)?,
        required_expected_type_hash: required_hash(&members, "required_expected_type_hash", path)?,
        required_environment_hash: required_hash(&members, "required_environment_hash", path)?,
        required_policy_hash: required_hash(&members, "required_policy_hash", path)?,
    })
}

fn validate_stale_solution_rejection(
    hole_id: &str,
    local_context_identity: &ProofSkeletonLocalContextIdentity,
    expected_type_identity: &ProofSkeletonExpectedTypeIdentity,
    stale: &ProofSkeletonStaleSolutionRejection,
    environment_hash: &Hash,
    policy_hash: &Hash,
) -> Result<(), ProofSkeletonSchemaError> {
    if stale.required_context_hash != local_context_identity.context_hash {
        return Err(ProofSkeletonSchemaError::new(
            "$.holes.stale_solution_rejection.required_context_hash",
            ProofSkeletonSchemaErrorKind::StaleContextHashMismatch {
                hole_id: hole_id.to_owned(),
            },
        ));
    }
    if stale.required_expected_type_hash != expected_type_identity.expected_type_hash {
        return Err(ProofSkeletonSchemaError::new(
            "$.holes.stale_solution_rejection.required_expected_type_hash",
            ProofSkeletonSchemaErrorKind::StaleExpectedTypeHashMismatch {
                hole_id: hole_id.to_owned(),
            },
        ));
    }
    if &stale.required_environment_hash != environment_hash {
        return Err(ProofSkeletonSchemaError::new(
            "$.holes.stale_solution_rejection.required_environment_hash",
            ProofSkeletonSchemaErrorKind::StaleEnvironmentHashMismatch {
                hole_id: hole_id.to_owned(),
            },
        ));
    }
    if &stale.required_policy_hash != policy_hash {
        return Err(ProofSkeletonSchemaError::new(
            "$.holes.stale_solution_rejection.required_policy_hash",
            ProofSkeletonSchemaErrorKind::StalePolicyHashMismatch {
                hole_id: hole_id.to_owned(),
            },
        ));
    }
    Ok(())
}

fn validate_hole_references(
    root: &ProofSkeletonTerm,
    holes: &[ProofSkeletonHole],
) -> Result<(), ProofSkeletonSchemaError> {
    let hole_ids: BTreeSet<&str> = holes.iter().map(|hole| hole.hole_id.as_str()).collect();
    let mut term_hole_ids = BTreeSet::new();
    collect_term_hole_ids(root, &mut term_hole_ids);
    for hole_id in term_hole_ids {
        if !hole_ids.contains(hole_id.as_str()) {
            return Err(ProofSkeletonSchemaError::new(
                "$.root.hole_id",
                ProofSkeletonSchemaErrorKind::UnknownHoleReference { hole_id },
            ));
        }
    }
    for hole in holes {
        for dependent in &hole.dependent_hole_ids {
            if !hole_ids.contains(dependent.as_str()) {
                return Err(ProofSkeletonSchemaError::new(
                    format!("$.holes.{}.dependent_hole_ids", hole.hole_id),
                    ProofSkeletonSchemaErrorKind::UnknownHoleReference {
                        hole_id: dependent.clone(),
                    },
                ));
            }
        }
    }
    Ok(())
}

fn collect_term_hole_ids(term: &ProofSkeletonTerm, ids: &mut BTreeSet<String>) {
    match term {
        ProofSkeletonTerm::Core { .. } => {}
        ProofSkeletonTerm::App { function, argument } => {
            collect_term_hole_ids(function, ids);
            collect_term_hole_ids(argument, ids);
        }
        ProofSkeletonTerm::Lam { body, .. } => collect_term_hole_ids(body, ids),
        ProofSkeletonTerm::Let { value, body, .. } => {
            collect_term_hole_ids(value, ids);
            collect_term_hole_ids(body, ids);
        }
        ProofSkeletonTerm::Hole { hole_id } => {
            ids.insert(hole_id.clone());
        }
    }
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ProofSkeletonSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ProofSkeletonSchemaError::new(
                format!("{path}.{}", member.key()),
                ProofSkeletonSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ProofSkeletonSchemaError::new(
                format!("{path}.{}", member.key()),
                ProofSkeletonSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ProofSkeletonSchemaError> {
    value.array_elements().ok_or_else(|| {
        ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn enforce_array_len(
    path: &str,
    actual: usize,
    min: usize,
    max: usize,
) -> Result<(), ProofSkeletonSchemaError> {
    if actual < min || actual > max {
        return Err(ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::ArrayLengthOutOfRange { min, max, actual },
        ));
    }
    Ok(())
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ProofSkeletonSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ProofSkeletonSchemaError::new(
            format!("{path}.{field}"),
            ProofSkeletonSchemaErrorKind::MissingField { field },
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
) -> Result<String, ProofSkeletonSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ProofSkeletonSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn optional_bounded_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: usize,
    max: usize,
) -> Result<Option<String>, ProofSkeletonSchemaError> {
    let Some(value) = optional_string(members, field, path)? else {
        return Ok(None);
    };
    let actual = value.chars().count();
    if actual < min || actual > max {
        return Err(ProofSkeletonSchemaError::new(
            format!("{path}.{field}"),
            ProofSkeletonSchemaErrorKind::StringLengthOutOfRange { min, max, actual },
        ));
    }
    Ok(Some(value))
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ProofSkeletonSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_identifier(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<String, ProofSkeletonSchemaError> {
    identifier_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn identifier_value(value: &JsonValue<'_>, path: &str) -> Result<String, ProofSkeletonSchemaError> {
    let identifier = string_value(value, path)?;
    if identifier.is_empty()
        || identifier.len() > 128
        || !identifier
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    {
        return Err(ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::InvalidIdentifier { value: identifier },
        ));
    }
    Ok(identifier)
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ProofSkeletonSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ProofSkeletonSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn required_hex_bytes(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    max_bytes: usize,
) -> Result<Vec<u8>, ProofSkeletonSchemaError> {
    let wire = required_string(members, field, path)?;
    if wire.is_empty() || wire.len() % 2 != 0 || wire.len() / 2 > max_bytes {
        return Err(ProofSkeletonSchemaError::new(
            format!("{path}.{field}"),
            ProofSkeletonSchemaErrorKind::InvalidHexBytes { value: wire },
        ));
    }
    let mut bytes = Vec::with_capacity(wire.len() / 2);
    let raw = wire.as_bytes();
    for index in (0..raw.len()).step_by(2) {
        let high = hex_nibble(raw[index]);
        let low = hex_nibble(raw[index + 1]);
        let (Some(high), Some(low)) = (high, low) else {
            return Err(ProofSkeletonSchemaError::new(
                format!("{path}.{field}"),
                ProofSkeletonSchemaErrorKind::InvalidHexBytes { value: wire },
            ));
        };
        bytes.push((high << 4) | low);
    }
    Ok(bytes)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn required_u64_in_range(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: u64,
    max: u64,
) -> Result<u64, ProofSkeletonSchemaError> {
    parse_u64_in_range(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
        min,
        max,
    )
}

fn optional_u64_in_range(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
    min: u64,
    max: u64,
) -> Result<Option<u64>, ProofSkeletonSchemaError> {
    optional_value(members, field)
        .map(|value| parse_u64_in_range(value, &format!("{path}.{field}"), min, max))
        .transpose()
}

fn parse_u64_in_range(
    value: &JsonValue<'_>,
    path: &str,
    min: u64,
    max: u64,
) -> Result<u64, ProofSkeletonSchemaError> {
    let raw = value.number_raw().map(ToOwned::to_owned).ok_or_else(|| {
        ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::ExpectedInteger {
                actual: value.kind(),
            },
        )
    })?;
    if raw.is_empty() || raw.bytes().any(|byte| !byte.is_ascii_digit()) {
        return Err(ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::InvalidInteger { value: raw },
        ));
    }
    let parsed: u64 = raw.parse().map_err(|_| {
        ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::InvalidInteger { value: raw.clone() },
        )
    })?;
    if parsed < min || parsed > max {
        return Err(ProofSkeletonSchemaError::new(
            path,
            ProofSkeletonSchemaErrorKind::IntegerOutOfRange { value: raw },
        ));
    }
    Ok(parsed)
}

fn encode_target_statement_identity_to(
    out: &mut Vec<u8>,
    identity: &ProofSkeletonTargetStatementIdentity,
) {
    encode_string_to(out, "statement_hash");
    encode_hash_to(out, &identity.statement_hash);
    encode_string_to(out, "expected_type_hash");
    encode_hash_to(out, &identity.expected_type_hash);
    encode_string_to(out, "root_context_hash");
    encode_hash_to(out, &identity.root_context_hash);
    encode_option_string_to(out, "module", identity.module.as_deref());
    encode_option_string_to(out, "declaration", identity.declaration.as_deref());
}

fn encode_term_to(out: &mut Vec<u8>, term: &ProofSkeletonTerm) {
    match term {
        ProofSkeletonTerm::Core { core_expr } => {
            encode_string_to(out, "core");
            encode_string_to(out, "core_expr");
            encode_core_expr_to(out, core_expr);
        }
        ProofSkeletonTerm::App { function, argument } => {
            encode_string_to(out, "app");
            encode_string_to(out, "function");
            encode_term_to(out, function);
            encode_string_to(out, "argument");
            encode_term_to(out, argument);
        }
        ProofSkeletonTerm::Lam { binder_type, body } => {
            encode_string_to(out, "lam");
            encode_string_to(out, "binder_type");
            encode_core_expr_to(out, binder_type);
            encode_string_to(out, "body");
            encode_term_to(out, body);
        }
        ProofSkeletonTerm::Let {
            binder_type,
            value,
            body,
        } => {
            encode_string_to(out, "let");
            encode_string_to(out, "binder_type");
            encode_core_expr_to(out, binder_type);
            encode_string_to(out, "value");
            encode_term_to(out, value);
            encode_string_to(out, "body");
            encode_term_to(out, body);
        }
        ProofSkeletonTerm::Hole { hole_id } => {
            encode_string_to(out, "hole");
            encode_string_to(out, "hole_id");
            encode_string_to(out, hole_id);
        }
    }
}

fn encode_core_expr_to(out: &mut Vec<u8>, core_expr: &ProofSkeletonCoreExpr) {
    encode_string_to(out, "core_expr_hash");
    encode_hash_to(out, core_expr.core_expr_hash());
    encode_string_to(out, "canonical_bytes");
    encode_bytes_to(out, core_expr.canonical_bytes());
}

fn encode_hole_to(out: &mut Vec<u8>, hole: &ProofSkeletonHole) {
    encode_string_to(out, "hole_id");
    encode_string_to(out, &hole.hole_id);
    encode_string_to(out, "local_context_identity");
    encode_string_to(out, "context_hash");
    encode_hash_to(out, &hole.local_context_identity.context_hash);
    encode_string_to(out, "binder_fingerprint_hash");
    encode_hash_to(out, &hole.local_context_identity.binder_fingerprint_hash);
    encode_string_to(out, "expected_type_identity");
    encode_string_to(out, "expected_type_hash");
    encode_hash_to(out, &hole.expected_type_identity.expected_type_hash);
    encode_string_to(out, "expected_type");
    encode_core_expr_to(out, &hole.expected_type_identity.expected_type);
    encode_string_to(out, "dependent_hole_ids");
    let mut dependent_hole_ids = hole.dependent_hole_ids.clone();
    dependent_hole_ids.sort();
    dependent_hole_ids.dedup();
    encode_len_to(out, dependent_hole_ids.len());
    for dependent_hole_id in &dependent_hole_ids {
        encode_string_to(out, dependent_hole_id);
    }
    encode_string_to(out, "allowed_premise_identities");
    let mut premises = hole.allowed_premise_identities.clone();
    premises.sort();
    premises.dedup();
    encode_len_to(out, premises.len());
    for premise in &premises {
        encode_string_to(out, "premise_hash");
        encode_hash_to(out, &premise.premise_hash);
        encode_string_to(out, "source");
        encode_string_to(out, premise.source.wire());
        encode_string_to(out, "axiom_profile_hash");
        encode_hash_to(out, &premise.axiom_profile_hash);
    }
    encode_string_to(out, "strategy_profile");
    encode_string_to(out, "profile_id");
    encode_string_to(out, hole.strategy_profile.profile_id.wire());
    encode_string_to(out, "preferred_node_kinds");
    let mut preferred_node_kinds = hole.strategy_profile.preferred_node_kinds.clone();
    preferred_node_kinds.sort();
    preferred_node_kinds.dedup();
    encode_len_to(out, preferred_node_kinds.len());
    for kind in &preferred_node_kinds {
        encode_string_to(out, kind.wire());
    }
    encode_string_to(out, "budget");
    encode_string_to(out, "max_candidates");
    encode_u64_to(out, hole.budget.max_candidates);
    encode_string_to(out, "max_search_nodes");
    encode_u64_to(out, hole.budget.max_search_nodes);
    encode_option_u64_to(out, "max_depth", hole.budget.max_depth);
    encode_option_u64_to(out, "max_repair_steps", hole.budget.max_repair_steps);
    encode_string_to(out, "stale_solution_rejection");
    encode_string_to(out, "required_context_hash");
    encode_hash_to(out, &hole.stale_solution_rejection.required_context_hash);
    encode_string_to(out, "required_expected_type_hash");
    encode_hash_to(
        out,
        &hole.stale_solution_rejection.required_expected_type_hash,
    );
    encode_string_to(out, "required_environment_hash");
    encode_hash_to(
        out,
        &hole.stale_solution_rejection.required_environment_hash,
    );
    encode_string_to(out, "required_policy_hash");
    encode_hash_to(out, &hole.stale_solution_rejection.required_policy_hash);
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

fn encode_bytes_to(out: &mut Vec<u8>, bytes: &[u8]) {
    out.push(b'b');
    encode_len_to(out, bytes.len());
    out.extend(bytes);
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

fn encode_option_u64_to(out: &mut Vec<u8>, field: &str, value: Option<u64>) {
    encode_string_to(out, field);
    match value {
        Some(value) => {
            out.push(1);
            encode_u64_to(out, value);
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

fn sha256_hash(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
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
            .join("testdata/proof-using-agents/fixtures/pua-m08-proof-skeleton")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("proof skeleton fixture should exist")
    }

    fn parse_fixture(name: &str) -> ProofSkeleton {
        parse_proof_skeleton(&fixture(name)).expect("fixture should parse")
    }

    fn expect_error(name: &str) -> ProofSkeletonSchemaErrorKind {
        parse_proof_skeleton(&fixture(name))
            .expect_err("fixture should be rejected")
            .kind()
            .clone()
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn resolved_byte_zero_artifact() -> ProofSkeletonResolvedCoreExprArtifact {
        ProofSkeletonResolvedCoreExprArtifact {
            artifact_hash: parse_hash_string(
                "sha256:5555555555555555555555555555555555555555555555555555555555555555",
            )
            .unwrap(),
            core_expr_hash: parse_hash_string(
                "sha256:6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
            )
            .unwrap(),
            canonical_bytes: vec![0],
        }
    }

    #[test]
    fn proof_skeleton_schema_accepts_complete_and_one_hole_fixtures() {
        let complete = parse_fixture("complete-skeleton.json");
        assert!(complete.holes.is_empty());
        assert!(matches!(complete.root, ProofSkeletonTerm::Let { .. }));

        let one_hole = parse_fixture("one-typed-hole.json");
        assert_eq!(one_hole.holes.len(), 1);
        assert!(matches!(
            one_hole.root,
            ProofSkeletonTerm::Hole { ref hole_id } if hole_id == "h1"
        ));
        assert_eq!(
            one_hole.holes[0].expected_type_identity.expected_type_hash,
            *one_hole.holes[0]
                .expected_type_identity
                .expected_type
                .core_expr_hash()
        );
    }

    #[test]
    fn proof_skeleton_schema_rejects_negative_fixtures() {
        assert!(matches!(
            expect_error("duplicate-hole-ids.json"),
            ProofSkeletonSchemaErrorKind::DuplicateHoleId { .. }
        ));
        assert!(matches!(
            expect_error("unresolved-artifact-reference.json"),
            ProofSkeletonSchemaErrorKind::UnresolvedArtifactReference { .. }
        ));
        assert!(matches!(
            expect_error("context-hash-mismatch.json"),
            ProofSkeletonSchemaErrorKind::StaleContextHashMismatch { .. }
        ));
        assert!(matches!(
            expect_error("expected-type-hash-mismatch.json"),
            ProofSkeletonSchemaErrorKind::ExpectedTypeHashMismatch { .. }
        ));
        assert!(matches!(
            expect_error("unknown-term-kind.json"),
            ProofSkeletonSchemaErrorKind::InvalidTermKind { .. }
        ));
    }

    #[test]
    fn proof_skeleton_schema_rejects_unknown_hole_reference() {
        let err = parse_proof_skeleton(
            r#"{
              "api_version":"npa.proof-skeleton.v1",
              "skeleton_id":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
              "target_statement_identity":{
                "statement_hash":"sha256:1111111111111111111111111111111111111111111111111111111111111111",
                "expected_type_hash":"sha256:4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
                "root_context_hash":"sha256:2222222222222222222222222222222222222222222222222222222222222222"
              },
              "environment_hash":"sha256:3333333333333333333333333333333333333333333333333333333333333333",
              "policy_hash":"sha256:4444444444444444444444444444444444444444444444444444444444444444",
              "root":{"kind":"hole","hole_id":"missing"},
              "holes":[]
            }"#,
        )
        .expect_err("unknown root hole should reject");
        assert!(matches!(
            err.kind(),
            ProofSkeletonSchemaErrorKind::UnknownHoleReference { .. }
        ));
    }

    #[test]
    fn proof_skeleton_schema_can_resolve_content_addressed_core_expr_artifact() {
        let source = fixture("unresolved-artifact-reference.json");
        let artifact = resolved_byte_zero_artifact();
        let skeleton = parse_proof_skeleton_with_artifacts(&source, &[artifact])
            .expect("resolved artifact should parse");
        assert!(matches!(
            skeleton.root,
            ProofSkeletonTerm::Core {
                core_expr: ProofSkeletonCoreExpr::Artifact { .. }
            }
        ));
    }

    #[test]
    fn proof_skeleton_hash_round_trip_excludes_id_and_resolves_artifact_semantics() {
        let complete = parse_fixture("complete-skeleton.json");
        let mut changed_id = complete.clone();
        changed_id.skeleton_id = hash(0x9a);
        assert_eq!(
            proof_skeleton_hash(&complete),
            proof_skeleton_hash(&changed_id)
        );
        assert!(proof_skeleton_hash_string(&complete).starts_with("sha256:"));

        let artifact_source = fixture("unresolved-artifact-reference.json");
        let artifact =
            parse_proof_skeleton_with_artifacts(&artifact_source, &[resolved_byte_zero_artifact()])
                .expect("resolved artifact should parse");
        let inline_source = artifact_source.replace(
            r#"{
      "kind": "core_expr_artifact",
      "artifact_schema": "npa.core-expr-artifact.v0.1",
      "artifact_hash": "sha256:5555555555555555555555555555555555555555555555555555555555555555",
      "core_expr_hash": "sha256:6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
      "size_bytes": 1
    }"#,
            r#"{
      "kind": "inline_core_expr",
      "encoding": "npa.core-expr.canonical-bytes.v0.1",
      "core_expr_hash": "sha256:6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
      "canonical_bytes_hex": "00"
    }"#,
        );
        let inline = parse_proof_skeleton(&inline_source).expect("inline core expr should parse");
        assert_eq!(proof_skeleton_hash(&artifact), proof_skeleton_hash(&inline));

        let mut changed_policy = inline.clone();
        changed_policy.policy_hash = hash(0x9b);
        assert_ne!(
            proof_skeleton_hash(&inline),
            proof_skeleton_hash(&changed_policy)
        );
    }

    #[test]
    fn proof_skeleton_hash_hole_identity_tracks_typed_context() {
        let skeleton = parse_fixture("one-typed-hole.json");
        let hole = &skeleton.holes[0];
        assert!(proof_skeleton_hole_hash_string(hole).starts_with("sha256:"));

        let mut changed = hole.clone();
        changed.local_context_identity.context_hash = hash(0x81);
        assert_ne!(
            proof_skeleton_hole_hash(hole),
            proof_skeleton_hole_hash(&changed)
        );

        let mut reordered = hole.clone();
        reordered.dependent_hole_ids = vec!["h3".to_owned(), "h2".to_owned()];
        let mut same_set = hole.clone();
        same_set.dependent_hole_ids = vec!["h2".to_owned(), "h3".to_owned()];
        assert_eq!(
            proof_skeleton_hole_hash(&reordered),
            proof_skeleton_hole_hash(&same_set)
        );
    }

    #[test]
    fn proof_skeleton_strict_decode_rejects_structured_schema_failures() {
        assert!(matches!(
            expect_error("duplicate-hole-ids.json"),
            ProofSkeletonSchemaErrorKind::DuplicateHoleId { .. }
        ));
        assert!(matches!(
            expect_error("unknown-term-kind.json"),
            ProofSkeletonSchemaErrorKind::InvalidTermKind { .. }
        ));
        assert!(matches!(
            expect_error("context-hash-mismatch.json"),
            ProofSkeletonSchemaErrorKind::StaleContextHashMismatch { .. }
        ));
        assert!(matches!(
            expect_error("expected-type-hash-mismatch.json"),
            ProofSkeletonSchemaErrorKind::ExpectedTypeHashMismatch { .. }
        ));

        let err = parse_proof_skeleton(
            r#"{
              "api_version":"npa.proof-skeleton.v1",
              "skeleton_id":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
              "target_statement_identity":{
                "statement_hash":"sha256:1111111111111111111111111111111111111111111111111111111111111111",
                "expected_type_hash":"sha256:4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
                "root_context_hash":"sha256:2222222222222222222222222222222222222222222222222222222222222222"
              },
              "environment_hash":"sha256:3333333333333333333333333333333333333333333333333333333333333333",
              "policy_hash":"sha256:4444444444444444444444444444444444444444444444444444444444444444",
              "root":{"kind":"hole","hole_id":"missing"},
              "holes":[]
            }"#,
        )
        .expect_err("unknown root hole should reject");
        assert!(matches!(
            err.kind(),
            ProofSkeletonSchemaErrorKind::UnknownHoleReference { .. }
        ));
    }

    #[test]
    fn proof_skeleton_schema_rejects_target_identity_string_bounds() {
        let source = fixture("complete-skeleton.json")
            .replace(r#""module": "Proofs.Ai.Example""#, r#""module": """#);
        let err = parse_proof_skeleton(&source).expect_err("empty module should reject");
        assert!(matches!(
            err.kind(),
            ProofSkeletonSchemaErrorKind::StringLengthOutOfRange { .. }
        ));
    }

    #[test]
    fn proof_skeleton_schema_contract_file_mentions_hole_boundary() {
        let schema = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("crate has workspace parent")
                .parent()
                .expect("workspace has repo root")
                .join("testdata/proof-using-agents/schemas/proof_skeleton.schema.json"),
        )
        .expect("schema should exist");
        for term_kind in PROOF_SKELETON_TERM_KINDS {
            assert!(schema.contains(term_kind));
        }
        assert!(schema.contains("hash-only core-expression references are insufficient"));
        assert!(schema.contains("proof_skeleton_hash"));
        assert!(schema.contains("certificate identity"));
        assert!(schema.contains("stale_solution_rejection"));
        assert!(schema.contains("dependent_hole_ids"));
    }
}

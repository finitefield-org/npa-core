use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const ROUTE_PACKAGE_API_VERSION: &str = "npa.route-package.v1";
pub const ROUTE_PACKAGE_HASH_DOMAIN: &str = "npa.route-package.identity.v1";

const COMPLEXITY_NAMESPACE_PREFIX: &str = "Proofs.Ai.Complexity.";
const TOP_LEVEL_P_EQUALS_NP_DECLARATION: &str = "Proofs.Ai.Complexity.PEqualsNP";
const TOP_LEVEL_P_NOT_EQUALS_NP_DECLARATION: &str = "Proofs.Ai.Complexity.PNotEqualsNP";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "route_key",
    "route_title",
    "final_question_targets",
    "module_namespaces",
    "dependency_layers",
    "theorem_cards",
    "blockers",
    "known_result_hashes",
    "barrier_audit_hashes",
    "assumption_hashes",
    "dependency_dag_hash",
    "claim_gate_dependency_hash",
    "verification_commands",
    "creates_unresolved_theorem_declarations",
    "creates_l1_scaffolds",
    "creates_axioms",
    "creates_verified_artifacts",
    "releases_dependencies",
    "creates_top_level_open_problem_claim",
    "wall_clock_time",
    "display_text",
];
const FINAL_TARGET_FIELDS: &[&str] = &[
    "target_key",
    "target_record_hash",
    "reviewed_formalization_candidate_hash",
    "no_theorem_declaration",
    "proof_corpus_theorem_declaration",
];
const LAYER_FIELDS: &[&str] = &[
    "layer_key",
    "layer_title",
    "namespace",
    "depends_on",
    "obligation_kinds",
];
const THEOREM_CARD_FIELDS: &[&str] = &[
    "card_key",
    "layer_key",
    "statement_hash",
    "status",
    "theorem_declaration",
    "certificate_hash",
    "source_free_verification_hash",
    "assumption_hashes",
    "special_case_scope_hash",
    "blocker_hash",
    "requires_complexity_obligations",
    "complexity_obligations",
    "verification_command_hashes",
    "creates_top_level_claim",
    "display_text",
];
const COMPLEXITY_OBLIGATION_FIELDS: &[&str] = &[
    "kind",
    "obligation_hash",
    "status",
    "statement_artifact_hash",
];
const BLOCKER_FIELDS: &[&str] = &[
    "blocker_key",
    "layer_key",
    "blocker_hash",
    "reason",
    "prerequisite_task_key",
];
const VERIFICATION_COMMAND_FIELDS: &[&str] =
    &["command_key", "command_hash", "command", "source_free"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageRecord {
    pub api_version: String,
    pub route_key: String,
    pub route_title: String,
    pub final_question_targets: Vec<RoutePackageFinalQuestionTarget>,
    pub module_namespaces: Vec<String>,
    pub dependency_layers: Vec<RoutePackageLayer>,
    pub theorem_cards: Vec<RoutePackageTheoremCard>,
    pub blockers: Vec<RoutePackageBlocker>,
    pub known_result_hashes: Vec<Hash>,
    pub barrier_audit_hashes: Vec<Hash>,
    pub assumption_hashes: Vec<Hash>,
    pub dependency_dag_hash: Hash,
    pub claim_gate_dependency_hash: Option<Hash>,
    pub verification_commands: Vec<RoutePackageVerificationCommand>,
    pub creates_unresolved_theorem_declarations: bool,
    pub creates_l1_scaffolds: bool,
    pub creates_axioms: bool,
    pub creates_verified_artifacts: bool,
    pub releases_dependencies: bool,
    pub creates_top_level_open_problem_claim: bool,
    pub wall_clock_time: Option<String>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageFinalQuestionTarget {
    pub target_key: String,
    pub target_record_hash: Hash,
    pub reviewed_formalization_candidate_hash: Hash,
    pub no_theorem_declaration: bool,
    pub proof_corpus_theorem_declaration: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageLayer {
    pub layer_key: String,
    pub layer_title: String,
    pub namespace: String,
    pub depends_on: Vec<String>,
    pub obligation_kinds: Vec<RoutePackageComplexityObligationKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageTheoremCard {
    pub card_key: String,
    pub layer_key: String,
    pub statement_hash: Hash,
    pub status: RoutePackageTheoremStatus,
    pub theorem_declaration: Option<String>,
    pub certificate_hash: Option<Hash>,
    pub source_free_verification_hash: Option<Hash>,
    pub assumption_hashes: Vec<Hash>,
    pub special_case_scope_hash: Option<Hash>,
    pub blocker_hash: Option<Hash>,
    pub requires_complexity_obligations: bool,
    pub complexity_obligations: Vec<RoutePackageComplexityObligationRef>,
    pub verification_command_hashes: Vec<Hash>,
    pub creates_top_level_claim: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageComplexityObligationRef {
    pub kind: RoutePackageComplexityObligationKind,
    pub obligation_hash: Hash,
    pub status: RoutePackageComplexityObligationStatus,
    pub statement_artifact_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageBlocker {
    pub blocker_key: String,
    pub layer_key: String,
    pub blocker_hash: Hash,
    pub reason: String,
    pub prerequisite_task_key: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageVerificationCommand {
    pub command_key: String,
    pub command_hash: Hash,
    pub command: String,
    pub source_free: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RoutePackageTheoremStatus {
    L2Derived,
    Conditional,
    FiniteOrSpecialCase,
    Blocker,
}

impl RoutePackageTheoremStatus {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::L2Derived => "l2_derived",
            Self::Conditional => "conditional",
            Self::FiniteOrSpecialCase => "finite_or_special_case",
            Self::Blocker => "blocker",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "l2_derived" => Some(Self::L2Derived),
            "conditional" => Some(Self::Conditional),
            "finite_or_special_case" => Some(Self::FiniteOrSpecialCase),
            "blocker" => Some(Self::Blocker),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RoutePackageComplexityObligationKind {
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

impl RoutePackageComplexityObligationKind {
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
pub enum RoutePackageComplexityObligationStatus {
    Open,
    TaskCreated,
    Verified,
    Rejected,
}

impl RoutePackageComplexityObligationStatus {
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
pub struct RoutePackageSchemaError {
    path: String,
    kind: RoutePackageSchemaErrorKind,
}

impl RoutePackageSchemaError {
    fn new(path: impl Into<String>, kind: RoutePackageSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn kind(&self) -> &RoutePackageSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for RoutePackageSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "route-package schema error at {}: {}",
            self.path, self.kind
        )
    }
}

impl std::error::Error for RoutePackageSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoutePackageSchemaErrorKind {
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
    InvalidTheoremStatus { value: String },
    InvalidComplexityObligationKind { value: String },
    InvalidComplexityObligationStatus { value: String },
}

impl fmt::Display for RoutePackageSchemaErrorKind {
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
            Self::InvalidTheoremStatus { value } => {
                write!(f, "invalid theorem-card status `{value}`")
            }
            Self::InvalidComplexityObligationKind { value } => {
                write!(f, "invalid complexity obligation kind `{value}`")
            }
            Self::InvalidComplexityObligationStatus { value } => {
                write!(f, "invalid complexity obligation status `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutePackageValidationError {
    kind: RoutePackageValidationErrorKind,
}

impl RoutePackageValidationError {
    fn new(kind: RoutePackageValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &RoutePackageValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for RoutePackageValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "route-package validation error: {}", self.kind)
    }
}

impl std::error::Error for RoutePackageValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoutePackageValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    MissingFinalQuestionTarget {
        target_key: &'static str,
    },
    DuplicateFinalQuestionTarget {
        target_key: String,
    },
    FinalQuestionTargetCreatesTheorem {
        target_key: String,
    },
    InvalidComplexityNamespace {
        namespace: String,
    },
    MissingDependencyLayer {
        layer_key: &'static str,
    },
    DuplicateDependencyLayer {
        layer_key: String,
    },
    UnknownLayerDependency {
        layer_key: String,
        dependency: String,
    },
    DuplicateTheoremCard {
        card_key: String,
    },
    UnknownTheoremCardLayer {
        card_key: String,
        layer_key: String,
    },
    TheoremCardCreatesTopLevelClaim {
        card_key: String,
    },
    MissingTheoremDeclaration {
        card_key: String,
    },
    TheoremDeclarationOutsideComplexityNamespace {
        card_key: String,
        theorem_declaration: String,
    },
    TopLevelFinalQuestionTheoremDeclaration {
        card_key: String,
        theorem_declaration: String,
    },
    MissingCertificateHash {
        card_key: String,
    },
    MissingSourceFreeVerification {
        card_key: String,
    },
    ConditionalRequiresAssumptions {
        card_key: String,
    },
    L2DerivedCannotHaveAssumptions {
        card_key: String,
    },
    FiniteOrSpecialCaseRequiresScope {
        card_key: String,
    },
    BlockerRequiresBlockerHash {
        card_key: String,
    },
    UnknownBlockerReference {
        card_key: String,
        blocker_hash: String,
    },
    BlockerCannotEmitTheoremDeclaration {
        card_key: String,
    },
    DuplicateComplexityObligation {
        card_key: String,
        kind: RoutePackageComplexityObligationKind,
    },
    MissingRequiredComplexityObligation {
        card_key: String,
        kind: RoutePackageComplexityObligationKind,
    },
    RequiredComplexityObligationUnverified {
        card_key: String,
        kind: RoutePackageComplexityObligationKind,
    },
    MissingVerificationCommands,
    DuplicateVerificationCommand {
        command_key: String,
    },
    DuplicateVerificationCommandHash {
        command_hash: String,
    },
    MissingSourceFreeVerificationCommand,
    UnknownVerificationCommandHash {
        card_key: String,
        command_hash: String,
    },
    DuplicateBlocker {
        blocker_key: String,
    },
    UnknownBlockerLayer {
        blocker_key: String,
        layer_key: String,
    },
    SidecarBoundaryViolation {
        field: &'static str,
    },
    MissingRouteContext {
        field: &'static str,
    },
}

impl fmt::Display for RoutePackageValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::MissingFinalQuestionTarget { target_key } => {
                write!(f, "missing final-question target `{target_key}`")
            }
            Self::DuplicateFinalQuestionTarget { target_key } => {
                write!(f, "duplicate final-question target `{target_key}`")
            }
            Self::FinalQuestionTargetCreatesTheorem { target_key } => write!(
                f,
                "final-question target `{target_key}` must remain metadata-only"
            ),
            Self::InvalidComplexityNamespace { namespace } => {
                write!(f, "invalid complexity namespace `{namespace}`")
            }
            Self::MissingDependencyLayer { layer_key } => {
                write!(f, "missing dependency layer `{layer_key}`")
            }
            Self::DuplicateDependencyLayer { layer_key } => {
                write!(f, "duplicate dependency layer `{layer_key}`")
            }
            Self::UnknownLayerDependency {
                layer_key,
                dependency,
            } => write!(
                f,
                "layer `{layer_key}` references unknown or later dependency `{dependency}`"
            ),
            Self::DuplicateTheoremCard { card_key } => {
                write!(f, "duplicate theorem card `{card_key}`")
            }
            Self::UnknownTheoremCardLayer {
                card_key,
                layer_key,
            } => write!(
                f,
                "theorem card `{card_key}` references unknown layer `{layer_key}`"
            ),
            Self::TheoremCardCreatesTopLevelClaim { card_key } => write!(
                f,
                "theorem card `{card_key}` attempts to create a top-level open-problem claim"
            ),
            Self::MissingTheoremDeclaration { card_key } => {
                write!(f, "theorem card `{card_key}` is missing a theorem declaration")
            }
            Self::TheoremDeclarationOutsideComplexityNamespace {
                card_key,
                theorem_declaration,
            } => write!(
                f,
                "theorem card `{card_key}` declaration `{theorem_declaration}` is outside Proofs.Ai.Complexity"
            ),
            Self::TopLevelFinalQuestionTheoremDeclaration {
                card_key,
                theorem_declaration,
            } => write!(
                f,
                "theorem card `{card_key}` declares unresolved final question `{theorem_declaration}`"
            ),
            Self::MissingCertificateHash { card_key } => {
                write!(f, "theorem card `{card_key}` is missing certificate hash")
            }
            Self::MissingSourceFreeVerification { card_key } => write!(
                f,
                "theorem card `{card_key}` is missing source-free verification hash"
            ),
            Self::ConditionalRequiresAssumptions { card_key } => write!(
                f,
                "conditional theorem card `{card_key}` requires explicit assumptions"
            ),
            Self::L2DerivedCannotHaveAssumptions { card_key } => write!(
                f,
                "l2_derived theorem card `{card_key}` cannot carry assumptions"
            ),
            Self::FiniteOrSpecialCaseRequiresScope { card_key } => write!(
                f,
                "finite or special-case theorem card `{card_key}` requires scope hash"
            ),
            Self::BlockerRequiresBlockerHash { card_key } => {
                write!(f, "blocker theorem card `{card_key}` requires blocker hash")
            }
            Self::UnknownBlockerReference { card_key, blocker_hash } => write!(
                f,
                "theorem card `{card_key}` references unknown blocker `{blocker_hash}`"
            ),
            Self::BlockerCannotEmitTheoremDeclaration { card_key } => write!(
                f,
                "blocker theorem card `{card_key}` cannot emit theorem artifacts"
            ),
            Self::DuplicateComplexityObligation { card_key, kind } => write!(
                f,
                "theorem card `{card_key}` duplicates complexity obligation `{}`",
                kind.wire()
            ),
            Self::MissingRequiredComplexityObligation { card_key, kind } => write!(
                f,
                "theorem card `{card_key}` is missing required complexity obligation `{}`",
                kind.wire()
            ),
            Self::RequiredComplexityObligationUnverified { card_key, kind } => write!(
                f,
                "theorem card `{card_key}` has unverified required complexity obligation `{}`",
                kind.wire()
            ),
            Self::MissingVerificationCommands => write!(f, "missing verification commands"),
            Self::DuplicateVerificationCommand { command_key } => {
                write!(f, "duplicate verification command `{command_key}`")
            }
            Self::DuplicateVerificationCommandHash { command_hash } => {
                write!(f, "duplicate verification command hash `{command_hash}`")
            }
            Self::MissingSourceFreeVerificationCommand => {
                write!(f, "missing source-free verification command")
            }
            Self::UnknownVerificationCommandHash {
                card_key,
                command_hash,
            } => write!(
                f,
                "theorem card `{card_key}` references unknown verification command `{command_hash}`"
            ),
            Self::DuplicateBlocker { blocker_key } => {
                write!(f, "duplicate blocker `{blocker_key}`")
            }
            Self::UnknownBlockerLayer {
                blocker_key,
                layer_key,
            } => write!(f, "blocker `{blocker_key}` references unknown layer `{layer_key}`"),
            Self::SidecarBoundaryViolation { field } => {
                write!(f, "route package violates sidecar boundary via `{field}`")
            }
            Self::MissingRouteContext { field } => {
                write!(f, "route package is missing route context `{field}`")
            }
        }
    }
}

pub fn parse_route_package_record(
    source: &str,
) -> Result<RoutePackageRecord, RoutePackageSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != ROUTE_PACKAGE_API_VERSION {
        return Err(RoutePackageSchemaError::new(
            "$.api_version",
            RoutePackageSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(RoutePackageRecord {
        api_version,
        route_key: required_string(&root, "route_key", "$")?,
        route_title: required_string(&root, "route_title", "$")?,
        final_question_targets: parse_final_question_targets(required_value(
            &root,
            "final_question_targets",
            "$",
        )?)?,
        module_namespaces: parse_string_array(
            required_value(&root, "module_namespaces", "$")?,
            "$.module_namespaces",
        )?,
        dependency_layers: parse_dependency_layers(required_value(
            &root,
            "dependency_layers",
            "$",
        )?)?,
        theorem_cards: parse_theorem_cards(required_value(&root, "theorem_cards", "$")?)?,
        blockers: parse_blockers(required_value(&root, "blockers", "$")?)?,
        known_result_hashes: parse_hash_array(
            required_value(&root, "known_result_hashes", "$")?,
            "$.known_result_hashes",
        )?,
        barrier_audit_hashes: parse_hash_array(
            required_value(&root, "barrier_audit_hashes", "$")?,
            "$.barrier_audit_hashes",
        )?,
        assumption_hashes: parse_hash_array(
            required_value(&root, "assumption_hashes", "$")?,
            "$.assumption_hashes",
        )?,
        dependency_dag_hash: required_hash(&root, "dependency_dag_hash", "$")?,
        claim_gate_dependency_hash: optional_hash(&root, "claim_gate_dependency_hash", "$")?,
        verification_commands: parse_verification_commands(required_value(
            &root,
            "verification_commands",
            "$",
        )?)?,
        creates_unresolved_theorem_declarations: required_bool(
            &root,
            "creates_unresolved_theorem_declarations",
            "$",
        )?,
        creates_l1_scaffolds: required_bool(&root, "creates_l1_scaffolds", "$")?,
        creates_axioms: required_bool(&root, "creates_axioms", "$")?,
        creates_verified_artifacts: required_bool(&root, "creates_verified_artifacts", "$")?,
        releases_dependencies: required_bool(&root, "releases_dependencies", "$")?,
        creates_top_level_open_problem_claim: required_bool(
            &root,
            "creates_top_level_open_problem_claim",
            "$",
        )?,
        wall_clock_time: optional_string(&root, "wall_clock_time", "$")?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_route_package_record(
    record: &RoutePackageRecord,
) -> Result<(), RoutePackageValidationError> {
    require_non_empty(&record.route_key, "route_key")?;
    require_non_empty(&record.route_title, "route_title")?;
    validate_sidecar_boundary(record)?;
    validate_route_context(record)?;
    validate_final_question_targets(record)?;
    validate_module_namespaces(&record.module_namespaces)?;
    let layer_keys = validate_dependency_layers(&record.dependency_layers)?;
    let blocker_hashes = validate_blockers(&record.blockers, &layer_keys)?;
    let command_hashes = validate_verification_commands(&record.verification_commands)?;
    validate_theorem_cards(record, &layer_keys, &blocker_hashes, &command_hashes)?;
    Ok(())
}

pub fn route_package_canonical_identity_bytes(record: &RoutePackageRecord) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_to(&mut out, ROUTE_PACKAGE_HASH_DOMAIN);
    encode_string_to(&mut out, "api_version");
    encode_string_to(&mut out, &record.api_version);
    encode_string_to(&mut out, "route_key");
    encode_string_to(&mut out, &record.route_key);
    encode_string_to(&mut out, "route_title");
    encode_string_to(&mut out, &record.route_title);
    encode_final_question_targets_to(&mut out, &record.final_question_targets);
    encode_string_list_to(&mut out, "module_namespaces", &record.module_namespaces);
    encode_dependency_layers_to(&mut out, &record.dependency_layers);
    encode_theorem_cards_to(&mut out, &record.theorem_cards);
    encode_blockers_to(&mut out, &record.blockers);
    encode_hash_list_to(&mut out, "known_result_hashes", &record.known_result_hashes);
    encode_hash_list_to(
        &mut out,
        "barrier_audit_hashes",
        &record.barrier_audit_hashes,
    );
    encode_hash_list_to(&mut out, "assumption_hashes", &record.assumption_hashes);
    encode_string_to(&mut out, "dependency_dag_hash");
    encode_hash_to(&mut out, &record.dependency_dag_hash);
    encode_option_hash_to(
        &mut out,
        "claim_gate_dependency_hash",
        record.claim_gate_dependency_hash.as_ref(),
    );
    encode_verification_commands_to(&mut out, &record.verification_commands);
    encode_bool_field_to(
        &mut out,
        "creates_unresolved_theorem_declarations",
        record.creates_unresolved_theorem_declarations,
    );
    encode_bool_field_to(
        &mut out,
        "creates_l1_scaffolds",
        record.creates_l1_scaffolds,
    );
    encode_bool_field_to(&mut out, "creates_axioms", record.creates_axioms);
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
        "creates_top_level_open_problem_claim",
        record.creates_top_level_open_problem_claim,
    );
    out
}

pub fn route_package_hash(record: &RoutePackageRecord) -> Hash {
    let digest = Sha256::digest(route_package_canonical_identity_bytes(record));
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub fn route_package_hash_string(record: &RoutePackageRecord) -> String {
    format_hash_string(&route_package_hash(record))
}

fn validate_sidecar_boundary(
    record: &RoutePackageRecord,
) -> Result<(), RoutePackageValidationError> {
    let flags = [
        (
            "creates_unresolved_theorem_declarations",
            record.creates_unresolved_theorem_declarations,
        ),
        ("creates_l1_scaffolds", record.creates_l1_scaffolds),
        ("creates_axioms", record.creates_axioms),
        (
            "creates_verified_artifacts",
            record.creates_verified_artifacts,
        ),
        ("releases_dependencies", record.releases_dependencies),
        (
            "creates_top_level_open_problem_claim",
            record.creates_top_level_open_problem_claim,
        ),
    ];
    for (field, value) in flags {
        if value {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::SidecarBoundaryViolation { field },
            ));
        }
    }
    Ok(())
}

fn validate_route_context(record: &RoutePackageRecord) -> Result<(), RoutePackageValidationError> {
    if record.known_result_hashes.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingRouteContext {
                field: "known_result_hashes",
            },
        ));
    }
    if record.barrier_audit_hashes.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingRouteContext {
                field: "barrier_audit_hashes",
            },
        ));
    }
    if record.assumption_hashes.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingRouteContext {
                field: "assumption_hashes",
            },
        ));
    }
    Ok(())
}

fn validate_final_question_targets(
    record: &RoutePackageRecord,
) -> Result<(), RoutePackageValidationError> {
    let mut missing = BTreeSet::from(["PEqualsNP", "PNotEqualsNP"]);
    let mut seen = BTreeSet::new();
    for target in &record.final_question_targets {
        require_non_empty(&target.target_key, "final_question_targets.target_key")?;
        if !seen.insert(target.target_key.as_str()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateFinalQuestionTarget {
                    target_key: target.target_key.clone(),
                },
            ));
        }
        missing.remove(target.target_key.as_str());
        if !target.no_theorem_declaration || target.proof_corpus_theorem_declaration.is_some() {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::FinalQuestionTargetCreatesTheorem {
                    target_key: target.target_key.clone(),
                },
            ));
        }
    }
    if missing.contains("PEqualsNP") {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingFinalQuestionTarget {
                target_key: "PEqualsNP",
            },
        ));
    }
    if missing.contains("PNotEqualsNP") {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingFinalQuestionTarget {
                target_key: "PNotEqualsNP",
            },
        ));
    }
    Ok(())
}

fn validate_module_namespaces(namespaces: &[String]) -> Result<(), RoutePackageValidationError> {
    if namespaces.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingRouteContext {
                field: "module_namespaces",
            },
        ));
    }
    let mut seen = BTreeSet::new();
    for namespace in namespaces {
        require_non_empty(namespace, "module_namespaces")?;
        if !namespace.starts_with(COMPLEXITY_NAMESPACE_PREFIX) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::InvalidComplexityNamespace {
                    namespace: namespace.clone(),
                },
            ));
        }
        if !seen.insert(namespace.as_str()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::InvalidComplexityNamespace {
                    namespace: namespace.clone(),
                },
            ));
        }
    }
    Ok(())
}

fn validate_dependency_layers(
    layers: &[RoutePackageLayer],
) -> Result<BTreeSet<String>, RoutePackageValidationError> {
    let mut seen = BTreeSet::new();
    for layer in layers {
        require_non_empty(&layer.layer_key, "dependency_layers.layer_key")?;
        require_non_empty(&layer.layer_title, "dependency_layers.layer_title")?;
        require_non_empty(&layer.namespace, "dependency_layers.namespace")?;
        if !layer.namespace.starts_with(COMPLEXITY_NAMESPACE_PREFIX) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::InvalidComplexityNamespace {
                    namespace: layer.namespace.clone(),
                },
            ));
        }
        for dependency in &layer.depends_on {
            if !seen.contains(dependency) {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::UnknownLayerDependency {
                        layer_key: layer.layer_key.clone(),
                        dependency: dependency.clone(),
                    },
                ));
            }
        }
        if !seen.insert(layer.layer_key.clone()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateDependencyLayer {
                    layer_key: layer.layer_key.clone(),
                },
            ));
        }
    }
    for expected in ["A", "B", "C", "D", "E", "F", "G", "H", "I"] {
        if !seen.contains(expected) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::MissingDependencyLayer {
                    layer_key: expected,
                },
            ));
        }
    }
    Ok(seen)
}

fn validate_blockers(
    blockers: &[RoutePackageBlocker],
    layer_keys: &BTreeSet<String>,
) -> Result<BTreeSet<Hash>, RoutePackageValidationError> {
    let mut blocker_keys = BTreeSet::new();
    let mut blocker_hashes = BTreeSet::new();
    for blocker in blockers {
        require_non_empty(&blocker.blocker_key, "blockers.blocker_key")?;
        require_non_empty(&blocker.reason, "blockers.reason")?;
        if !layer_keys.contains(&blocker.layer_key) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::UnknownBlockerLayer {
                    blocker_key: blocker.blocker_key.clone(),
                    layer_key: blocker.layer_key.clone(),
                },
            ));
        }
        if !blocker_keys.insert(blocker.blocker_key.as_str()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateBlocker {
                    blocker_key: blocker.blocker_key.clone(),
                },
            ));
        }
        blocker_hashes.insert(blocker.blocker_hash);
    }
    Ok(blocker_hashes)
}

fn validate_verification_commands(
    commands: &[RoutePackageVerificationCommand],
) -> Result<BTreeSet<Hash>, RoutePackageValidationError> {
    if commands.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingVerificationCommands,
        ));
    }
    let mut keys = BTreeSet::new();
    let mut hashes = BTreeSet::new();
    let mut has_source_free = false;
    for command in commands {
        require_non_empty(&command.command_key, "verification_commands.command_key")?;
        require_non_empty(&command.command, "verification_commands.command")?;
        has_source_free |= command.source_free;
        if !keys.insert(command.command_key.as_str()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateVerificationCommand {
                    command_key: command.command_key.clone(),
                },
            ));
        }
        if !hashes.insert(command.command_hash) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateVerificationCommandHash {
                    command_hash: format_hash_string(&command.command_hash),
                },
            ));
        }
    }
    if !has_source_free {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingSourceFreeVerificationCommand,
        ));
    }
    Ok(hashes)
}

fn validate_theorem_cards(
    record: &RoutePackageRecord,
    layer_keys: &BTreeSet<String>,
    blocker_hashes: &BTreeSet<Hash>,
    command_hashes: &BTreeSet<Hash>,
) -> Result<(), RoutePackageValidationError> {
    if record.theorem_cards.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingRouteContext {
                field: "theorem_cards",
            },
        ));
    }
    let mut seen = BTreeSet::new();
    for card in &record.theorem_cards {
        require_non_empty(&card.card_key, "theorem_cards.card_key")?;
        if !seen.insert(card.card_key.as_str()) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateTheoremCard {
                    card_key: card.card_key.clone(),
                },
            ));
        }
        if !layer_keys.contains(&card.layer_key) {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::UnknownTheoremCardLayer {
                    card_key: card.card_key.clone(),
                    layer_key: card.layer_key.clone(),
                },
            ));
        }
        if card.creates_top_level_claim {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::TheoremCardCreatesTopLevelClaim {
                    card_key: card.card_key.clone(),
                },
            ));
        }
        validate_theorem_status(card, blocker_hashes)?;
        validate_theorem_card_obligations(card)?;
        for command_hash in &card.verification_command_hashes {
            if !command_hashes.contains(command_hash) {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::UnknownVerificationCommandHash {
                        card_key: card.card_key.clone(),
                        command_hash: format_hash_string(command_hash),
                    },
                ));
            }
        }
    }
    Ok(())
}

fn validate_theorem_status(
    card: &RoutePackageTheoremCard,
    blocker_hashes: &BTreeSet<Hash>,
) -> Result<(), RoutePackageValidationError> {
    match card.status {
        RoutePackageTheoremStatus::L2Derived => {
            validate_checked_card_artifacts(card)?;
            if !card.assumption_hashes.is_empty() {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::L2DerivedCannotHaveAssumptions {
                        card_key: card.card_key.clone(),
                    },
                ));
            }
        }
        RoutePackageTheoremStatus::Conditional => {
            validate_checked_card_artifacts(card)?;
            if card.assumption_hashes.is_empty() {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::ConditionalRequiresAssumptions {
                        card_key: card.card_key.clone(),
                    },
                ));
            }
        }
        RoutePackageTheoremStatus::FiniteOrSpecialCase => {
            validate_checked_card_artifacts(card)?;
            if card.special_case_scope_hash.is_none() {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::FiniteOrSpecialCaseRequiresScope {
                        card_key: card.card_key.clone(),
                    },
                ));
            }
        }
        RoutePackageTheoremStatus::Blocker => {
            let Some(blocker_hash) = card.blocker_hash else {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::BlockerRequiresBlockerHash {
                        card_key: card.card_key.clone(),
                    },
                ));
            };
            if !blocker_hashes.contains(&blocker_hash) {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::UnknownBlockerReference {
                        card_key: card.card_key.clone(),
                        blocker_hash: format_hash_string(&blocker_hash),
                    },
                ));
            }
            if card.theorem_declaration.is_some()
                || card.certificate_hash.is_some()
                || card.source_free_verification_hash.is_some()
            {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::BlockerCannotEmitTheoremDeclaration {
                        card_key: card.card_key.clone(),
                    },
                ));
            }
        }
    }
    Ok(())
}

fn validate_checked_card_artifacts(
    card: &RoutePackageTheoremCard,
) -> Result<(), RoutePackageValidationError> {
    let Some(declaration) = card.theorem_declaration.as_deref() else {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingTheoremDeclaration {
                card_key: card.card_key.clone(),
            },
        ));
    };
    if !declaration.starts_with(COMPLEXITY_NAMESPACE_PREFIX) {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::TheoremDeclarationOutsideComplexityNamespace {
                card_key: card.card_key.clone(),
                theorem_declaration: declaration.to_owned(),
            },
        ));
    }
    if declaration == TOP_LEVEL_P_EQUALS_NP_DECLARATION
        || declaration == TOP_LEVEL_P_NOT_EQUALS_NP_DECLARATION
    {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::TopLevelFinalQuestionTheoremDeclaration {
                card_key: card.card_key.clone(),
                theorem_declaration: declaration.to_owned(),
            },
        ));
    }
    if card.certificate_hash.is_none() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingCertificateHash {
                card_key: card.card_key.clone(),
            },
        ));
    }
    if card.source_free_verification_hash.is_none() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingSourceFreeVerification {
                card_key: card.card_key.clone(),
            },
        ));
    }
    if card.verification_command_hashes.is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::MissingSourceFreeVerification {
                card_key: card.card_key.clone(),
            },
        ));
    }
    Ok(())
}

fn validate_theorem_card_obligations(
    card: &RoutePackageTheoremCard,
) -> Result<(), RoutePackageValidationError> {
    let mut by_kind = BTreeMap::new();
    for obligation in &card.complexity_obligations {
        if by_kind.insert(obligation.kind, obligation.status).is_some() {
            return Err(RoutePackageValidationError::new(
                RoutePackageValidationErrorKind::DuplicateComplexityObligation {
                    card_key: card.card_key.clone(),
                    kind: obligation.kind,
                },
            ));
        }
    }
    if card.requires_complexity_obligations {
        for kind in [
            RoutePackageComplexityObligationKind::RuntimePolynomial,
            RoutePackageComplexityObligationKind::OutputSizePolynomial,
            RoutePackageComplexityObligationKind::CodecCorrectness,
            RoutePackageComplexityObligationKind::Uniformity,
        ] {
            let Some(status) = by_kind.get(&kind) else {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::MissingRequiredComplexityObligation {
                        card_key: card.card_key.clone(),
                        kind,
                    },
                ));
            };
            if card.status != RoutePackageTheoremStatus::Blocker
                && *status != RoutePackageComplexityObligationStatus::Verified
            {
                return Err(RoutePackageValidationError::new(
                    RoutePackageValidationErrorKind::RequiredComplexityObligationUnverified {
                        card_key: card.card_key.clone(),
                        kind,
                    },
                ));
            }
        }
    }
    Ok(())
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, RoutePackageSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        RoutePackageSchemaError::new(
            "$",
            RoutePackageSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, RoutePackageSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(RoutePackageSchemaError::new(
                format!("{path}.{}", member.key()),
                RoutePackageSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(RoutePackageSchemaError::new(
                format!("{path}.{}", member.key()),
                RoutePackageSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], RoutePackageSchemaError> {
    value.array_elements().ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, RoutePackageSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        RoutePackageSchemaError::new(
            format!("{path}.{field}"),
            RoutePackageSchemaErrorKind::MissingField { field },
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
) -> Result<String, RoutePackageSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, RoutePackageSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, RoutePackageSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, RoutePackageSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, RoutePackageSchemaError> {
    value.bool_value().ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, RoutePackageSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<Hash>, RoutePackageSchemaError> {
    optional_value(members, field)
        .map(|value| hash_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, RoutePackageSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_final_question_targets(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageFinalQuestionTarget>, RoutePackageSchemaError> {
    array_elements(value, "$.final_question_targets")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_final_question_target(value, &format!("$.final_question_targets[{index}]"))
        })
        .collect()
}

fn parse_final_question_target(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageFinalQuestionTarget, RoutePackageSchemaError> {
    let members = object_map(value, path, FINAL_TARGET_FIELDS)?;
    Ok(RoutePackageFinalQuestionTarget {
        target_key: required_string(&members, "target_key", path)?,
        target_record_hash: required_hash(&members, "target_record_hash", path)?,
        reviewed_formalization_candidate_hash: required_hash(
            &members,
            "reviewed_formalization_candidate_hash",
            path,
        )?,
        no_theorem_declaration: required_bool(&members, "no_theorem_declaration", path)?,
        proof_corpus_theorem_declaration: optional_string(
            &members,
            "proof_corpus_theorem_declaration",
            path,
        )?,
    })
}

fn parse_dependency_layers(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageLayer>, RoutePackageSchemaError> {
    array_elements(value, "$.dependency_layers")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_dependency_layer(value, &format!("$.dependency_layers[{index}]"))
        })
        .collect()
}

fn parse_dependency_layer(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageLayer, RoutePackageSchemaError> {
    let members = object_map(value, path, LAYER_FIELDS)?;
    Ok(RoutePackageLayer {
        layer_key: required_string(&members, "layer_key", path)?,
        layer_title: required_string(&members, "layer_title", path)?,
        namespace: required_string(&members, "namespace", path)?,
        depends_on: parse_string_array(
            required_value(&members, "depends_on", path)?,
            &format!("{path}.depends_on"),
        )?,
        obligation_kinds: parse_complexity_obligation_kind_array(
            required_value(&members, "obligation_kinds", path)?,
            &format!("{path}.obligation_kinds"),
        )?,
    })
}

fn parse_theorem_cards(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageTheoremCard>, RoutePackageSchemaError> {
    array_elements(value, "$.theorem_cards")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_theorem_card(value, &format!("$.theorem_cards[{index}]")))
        .collect()
}

fn parse_theorem_card(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageTheoremCard, RoutePackageSchemaError> {
    let members = object_map(value, path, THEOREM_CARD_FIELDS)?;
    Ok(RoutePackageTheoremCard {
        card_key: required_string(&members, "card_key", path)?,
        layer_key: required_string(&members, "layer_key", path)?,
        statement_hash: required_hash(&members, "statement_hash", path)?,
        status: parse_theorem_status_value(
            required_value(&members, "status", path)?,
            &format!("{path}.status"),
        )?,
        theorem_declaration: optional_string(&members, "theorem_declaration", path)?,
        certificate_hash: optional_hash(&members, "certificate_hash", path)?,
        source_free_verification_hash: optional_hash(
            &members,
            "source_free_verification_hash",
            path,
        )?,
        assumption_hashes: parse_hash_array(
            required_value(&members, "assumption_hashes", path)?,
            &format!("{path}.assumption_hashes"),
        )?,
        special_case_scope_hash: optional_hash(&members, "special_case_scope_hash", path)?,
        blocker_hash: optional_hash(&members, "blocker_hash", path)?,
        requires_complexity_obligations: required_bool(
            &members,
            "requires_complexity_obligations",
            path,
        )?,
        complexity_obligations: parse_complexity_obligations(required_value(
            &members,
            "complexity_obligations",
            path,
        )?)?,
        verification_command_hashes: parse_hash_array(
            required_value(&members, "verification_command_hashes", path)?,
            &format!("{path}.verification_command_hashes"),
        )?,
        creates_top_level_claim: required_bool(&members, "creates_top_level_claim", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_complexity_obligations(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageComplexityObligationRef>, RoutePackageSchemaError> {
    array_elements(value, "$.theorem_cards[].complexity_obligations")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_complexity_obligation(
                value,
                &format!("$.theorem_cards[].complexity_obligations[{index}]"),
            )
        })
        .collect()
}

fn parse_complexity_obligation(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageComplexityObligationRef, RoutePackageSchemaError> {
    let members = object_map(value, path, COMPLEXITY_OBLIGATION_FIELDS)?;
    Ok(RoutePackageComplexityObligationRef {
        kind: parse_complexity_obligation_kind_value(
            required_value(&members, "kind", path)?,
            &format!("{path}.kind"),
        )?,
        obligation_hash: required_hash(&members, "obligation_hash", path)?,
        status: parse_complexity_obligation_status_value(
            required_value(&members, "status", path)?,
            &format!("{path}.status"),
        )?,
        statement_artifact_hash: required_hash(&members, "statement_artifact_hash", path)?,
    })
}

fn parse_blockers(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageBlocker>, RoutePackageSchemaError> {
    array_elements(value, "$.blockers")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_blocker(value, &format!("$.blockers[{index}]")))
        .collect()
}

fn parse_blocker(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageBlocker, RoutePackageSchemaError> {
    let members = object_map(value, path, BLOCKER_FIELDS)?;
    Ok(RoutePackageBlocker {
        blocker_key: required_string(&members, "blocker_key", path)?,
        layer_key: required_string(&members, "layer_key", path)?,
        blocker_hash: required_hash(&members, "blocker_hash", path)?,
        reason: required_string(&members, "reason", path)?,
        prerequisite_task_key: optional_string(&members, "prerequisite_task_key", path)?,
    })
}

fn parse_verification_commands(
    value: &JsonValue<'_>,
) -> Result<Vec<RoutePackageVerificationCommand>, RoutePackageSchemaError> {
    array_elements(value, "$.verification_commands")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_verification_command(value, &format!("$.verification_commands[{index}]"))
        })
        .collect()
}

fn parse_verification_command(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageVerificationCommand, RoutePackageSchemaError> {
    let members = object_map(value, path, VERIFICATION_COMMAND_FIELDS)?;
    Ok(RoutePackageVerificationCommand {
        command_key: required_string(&members, "command_key", path)?,
        command_hash: required_hash(&members, "command_hash", path)?,
        command: required_string(&members, "command", path)?,
        source_free: required_bool(&members, "source_free", path)?,
    })
}

fn parse_string_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<String>, RoutePackageSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| string_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_hash_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<Hash>, RoutePackageSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| hash_value(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_complexity_obligation_kind_array(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Vec<RoutePackageComplexityObligationKind>, RoutePackageSchemaError> {
    array_elements(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_complexity_obligation_kind_value(value, &format!("{path}[{index}]"))
        })
        .collect()
}

fn parse_theorem_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageTheoremStatus, RoutePackageSchemaError> {
    let wire = string_value(value, path)?;
    RoutePackageTheoremStatus::parse(&wire).ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::InvalidTheoremStatus { value: wire },
        )
    })
}

fn parse_complexity_obligation_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageComplexityObligationKind, RoutePackageSchemaError> {
    let wire = string_value(value, path)?;
    RoutePackageComplexityObligationKind::parse(&wire).ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::InvalidComplexityObligationKind { value: wire },
        )
    })
}

fn parse_complexity_obligation_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<RoutePackageComplexityObligationStatus, RoutePackageSchemaError> {
    let wire = string_value(value, path)?;
    RoutePackageComplexityObligationStatus::parse(&wire).ok_or_else(|| {
        RoutePackageSchemaError::new(
            path,
            RoutePackageSchemaErrorKind::InvalidComplexityObligationStatus { value: wire },
        )
    })
}

fn require_non_empty(value: &str, field: &'static str) -> Result<(), RoutePackageValidationError> {
    if value.trim().is_empty() {
        return Err(RoutePackageValidationError::new(
            RoutePackageValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
}

fn encode_final_question_targets_to(
    out: &mut Vec<u8>,
    targets: &[RoutePackageFinalQuestionTarget],
) {
    encode_string_to(out, "final_question_targets");
    let mut targets = targets.to_vec();
    targets.sort_by(|left, right| left.target_key.cmp(&right.target_key));
    encode_len_to(out, targets.len());
    for target in &targets {
        encode_string_to(out, &target.target_key);
        encode_hash_to(out, &target.target_record_hash);
        encode_hash_to(out, &target.reviewed_formalization_candidate_hash);
        out.push(u8::from(target.no_theorem_declaration));
        encode_option_string_to(
            out,
            "proof_corpus_theorem_declaration",
            target.proof_corpus_theorem_declaration.as_deref(),
        );
    }
}

fn encode_dependency_layers_to(out: &mut Vec<u8>, layers: &[RoutePackageLayer]) {
    encode_string_to(out, "dependency_layers");
    let mut layers = layers.to_vec();
    layers.sort_by(|left, right| left.layer_key.cmp(&right.layer_key));
    encode_len_to(out, layers.len());
    for layer in &layers {
        encode_string_to(out, &layer.layer_key);
        encode_string_to(out, &layer.layer_title);
        encode_string_to(out, &layer.namespace);
        encode_string_list_to(out, "depends_on", &layer.depends_on);
        encode_obligation_kind_list_to(out, "obligation_kinds", &layer.obligation_kinds);
    }
}

fn encode_theorem_cards_to(out: &mut Vec<u8>, cards: &[RoutePackageTheoremCard]) {
    encode_string_to(out, "theorem_cards");
    let mut cards = cards.to_vec();
    cards.sort_by(|left, right| left.card_key.cmp(&right.card_key));
    encode_len_to(out, cards.len());
    for card in &cards {
        encode_string_to(out, &card.card_key);
        encode_string_to(out, &card.layer_key);
        encode_hash_to(out, &card.statement_hash);
        encode_string_to(out, card.status.wire());
        encode_option_string_to(
            out,
            "theorem_declaration",
            card.theorem_declaration.as_deref(),
        );
        encode_option_hash_to(out, "certificate_hash", card.certificate_hash.as_ref());
        encode_option_hash_to(
            out,
            "source_free_verification_hash",
            card.source_free_verification_hash.as_ref(),
        );
        encode_hash_list_to(out, "assumption_hashes", &card.assumption_hashes);
        encode_option_hash_to(
            out,
            "special_case_scope_hash",
            card.special_case_scope_hash.as_ref(),
        );
        encode_option_hash_to(out, "blocker_hash", card.blocker_hash.as_ref());
        encode_bool_field_to(
            out,
            "requires_complexity_obligations",
            card.requires_complexity_obligations,
        );
        encode_complexity_obligations_to(out, &card.complexity_obligations);
        encode_hash_list_to(
            out,
            "verification_command_hashes",
            &card.verification_command_hashes,
        );
        encode_bool_field_to(out, "creates_top_level_claim", card.creates_top_level_claim);
    }
}

fn encode_complexity_obligations_to(
    out: &mut Vec<u8>,
    obligations: &[RoutePackageComplexityObligationRef],
) {
    encode_string_to(out, "complexity_obligations");
    let mut obligations = obligations.to_vec();
    obligations.sort_by_key(|obligation| obligation.kind);
    encode_len_to(out, obligations.len());
    for obligation in &obligations {
        encode_string_to(out, obligation.kind.wire());
        encode_hash_to(out, &obligation.obligation_hash);
        encode_string_to(out, obligation.status.wire());
        encode_hash_to(out, &obligation.statement_artifact_hash);
    }
}

fn encode_blockers_to(out: &mut Vec<u8>, blockers: &[RoutePackageBlocker]) {
    encode_string_to(out, "blockers");
    let mut blockers = blockers.to_vec();
    blockers.sort_by(|left, right| left.blocker_key.cmp(&right.blocker_key));
    encode_len_to(out, blockers.len());
    for blocker in &blockers {
        encode_string_to(out, &blocker.blocker_key);
        encode_string_to(out, &blocker.layer_key);
        encode_hash_to(out, &blocker.blocker_hash);
        encode_string_to(out, &blocker.reason);
        encode_option_string_to(
            out,
            "prerequisite_task_key",
            blocker.prerequisite_task_key.as_deref(),
        );
    }
}

fn encode_verification_commands_to(
    out: &mut Vec<u8>,
    commands: &[RoutePackageVerificationCommand],
) {
    encode_string_to(out, "verification_commands");
    let mut commands = commands.to_vec();
    commands.sort_by(|left, right| left.command_key.cmp(&right.command_key));
    encode_len_to(out, commands.len());
    for command in &commands {
        encode_string_to(out, &command.command_key);
        encode_hash_to(out, &command.command_hash);
        encode_string_to(out, &command.command);
        out.push(u8::from(command.source_free));
    }
}

fn encode_string_list_to(out: &mut Vec<u8>, label: &str, values: &[String]) {
    encode_string_to(out, label);
    let mut values = values.to_vec();
    values.sort();
    encode_len_to(out, values.len());
    for value in &values {
        encode_string_to(out, value);
    }
}

fn encode_obligation_kind_list_to(
    out: &mut Vec<u8>,
    label: &str,
    values: &[RoutePackageComplexityObligationKind],
) {
    encode_string_to(out, label);
    let mut values = values.to_vec();
    values.sort();
    encode_len_to(out, values.len());
    for value in &values {
        encode_string_to(out, value.wire());
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
            .join("testdata/proof-using-agents/fixtures/pua-m16-route-package")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("route-package fixture should exist")
    }

    fn parse_fixture(name: &str) -> RoutePackageRecord {
        parse_route_package_record(&fixture(name)).expect("route-package fixture should parse")
    }

    #[test]
    fn route_package_record_keeps_final_questions_metadata_only() {
        let package = parse_fixture("valid-p-vs-np-route-package.json");
        validate_route_package_record(&package).expect("route package validates");
        assert!(package
            .final_question_targets
            .iter()
            .any(|target| target.target_key == "PEqualsNP" && target.no_theorem_declaration));
        assert!(package
            .final_question_targets
            .iter()
            .any(|target| target.target_key == "PNotEqualsNP" && target.no_theorem_declaration));
        assert!(package
            .module_namespaces
            .iter()
            .any(|namespace| namespace.starts_with("Proofs.Ai.Complexity")));

        let mut display_changed = package.clone();
        display_changed.display_text = Some("display-only wording changed".to_owned());
        display_changed.wall_clock_time = Some("2099-12-31T23:59:59Z".to_owned());
        assert_eq!(
            route_package_hash(&package),
            route_package_hash(&display_changed)
        );
    }

    #[test]
    fn route_package_record_rejects_unresolved_top_level_theorem() {
        let package = parse_fixture("valid-p-vs-np-route-package.json");

        let mut target_theorem = package.clone();
        let target = target_theorem
            .final_question_targets
            .iter_mut()
            .find(|target| target.target_key == "PEqualsNP")
            .expect("valid fixture has PEqualsNP");
        target.no_theorem_declaration = false;
        target.proof_corpus_theorem_declaration = Some("Proofs.Ai.Complexity.PEqualsNP".to_owned());
        assert!(matches!(
            validate_route_package_record(&target_theorem).map_err(|error| error.kind().clone()),
            Err(RoutePackageValidationErrorKind::FinalQuestionTargetCreatesTheorem { .. })
        ));

        let mut card_claim = package.clone();
        card_claim.theorem_cards[0].creates_top_level_claim = true;
        assert!(matches!(
            validate_route_package_record(&card_claim).map_err(|error| error.kind().clone()),
            Err(RoutePackageValidationErrorKind::TheoremCardCreatesTopLevelClaim { .. })
        ));

        let mut blocker_with_theorem = package.clone();
        let blocker_card = blocker_with_theorem
            .theorem_cards
            .iter_mut()
            .find(|card| card.status == RoutePackageTheoremStatus::Blocker)
            .expect("valid fixture has blocker card");
        blocker_card.theorem_declaration =
            Some("Proofs.Ai.Complexity.AC0.switching_lemma_placeholder".to_owned());
        assert!(matches!(
            validate_route_package_record(&blocker_with_theorem)
                .map_err(|error| error.kind().clone()),
            Err(RoutePackageValidationErrorKind::BlockerCannotEmitTheoremDeclaration { .. })
        ));

        let mut l2_with_assumption = package.clone();
        l2_with_assumption.theorem_cards[0].assumption_hashes.push(
            parse_hash_string(
                "sha256:5353535353535353535353535353535353535353535353535353535353535353",
            )
            .expect("synthetic assumption hash is valid"),
        );
        assert!(matches!(
            validate_route_package_record(&l2_with_assumption)
                .map_err(|error| error.kind().clone()),
            Err(RoutePackageValidationErrorKind::L2DerivedCannotHaveAssumptions { .. })
        ));
    }

    #[test]
    fn route_package_record_requires_complexity_obligations() {
        let package = parse_fixture("valid-p-vs-np-route-package.json");
        let karp_card = package
            .theorem_cards
            .iter()
            .find(|card| card.card_key == "layer-c.karp-reduction-witness")
            .expect("valid fixture has Karp card");
        assert!(karp_card.requires_complexity_obligations);
        for required_kind in [
            RoutePackageComplexityObligationKind::RuntimePolynomial,
            RoutePackageComplexityObligationKind::OutputSizePolynomial,
            RoutePackageComplexityObligationKind::CodecCorrectness,
            RoutePackageComplexityObligationKind::Uniformity,
        ] {
            assert!(karp_card
                .complexity_obligations
                .iter()
                .any(|obligation| obligation.kind == required_kind));

            let mut missing_required = package.clone();
            let karp_card = missing_required
                .theorem_cards
                .iter_mut()
                .find(|card| card.card_key == "layer-c.karp-reduction-witness")
                .expect("valid fixture has Karp card");
            karp_card
                .complexity_obligations
                .retain(|obligation| obligation.kind != required_kind);
            let err = validate_route_package_record(&missing_required)
                .expect_err("missing required Karp obligation should fail validation");
            assert!(
                matches!(
                    err.kind(),
                    RoutePackageValidationErrorKind::MissingRequiredComplexityObligation {
                        kind,
                        ..
                    } if *kind == required_kind
                ),
                "unexpected validation error: {err:?}"
            );
        }
        let l1_scaffold_status =
            fixture("valid-p-vs-np-route-package.json").replacen("l2_derived", "l1_scaffold", 1);
        assert!(matches!(
            parse_route_package_record(&l1_scaffold_status),
            Err(RoutePackageSchemaError { .. })
        ));

        let mut missing_target = package.clone();
        missing_target
            .final_question_targets
            .retain(|target| target.target_key != "PNotEqualsNP");
        assert!(matches!(
            validate_route_package_record(&missing_target).map_err(|error| error.kind().clone()),
            Err(
                RoutePackageValidationErrorKind::MissingFinalQuestionTarget {
                    target_key: "PNotEqualsNP"
                }
            )
        ));
    }
}

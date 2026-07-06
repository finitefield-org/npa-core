use crate::json::{JsonDocument, JsonValue, JsonValueKind};
use crate::types::{format_hash_string, parse_hash_string};
use npa_cert::Hash;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const RESEARCH_VARIANT_API_VERSION: &str = "npa.research-variant.v1";

const ROOT_FIELDS: &[&str] = &[
    "api_version",
    "variant_key",
    "parent_target_key",
    "parent_statement_hash",
    "variant_statement_hash",
    "variant_scope",
    "transformation_kind",
    "relationship_review",
    "assumption_deltas",
    "bound_deltas",
    "output_task_references",
    "output_replaces_parent_target",
    "output_creates_theorem_declaration",
    "output_creates_evidence_record",
    "display_text",
];
const RELATIONSHIP_REVIEW_FIELDS: &[&str] = &[
    "review_hash",
    "reviewer_status",
    "relationship_to_parent",
    "relationship_inferred",
    "parent_statement_hash",
    "variant_statement_hash",
    "display_text",
];
const ASSUMPTION_DELTA_FIELDS: &[&str] = &[
    "delta_kind",
    "assumption_hash",
    "disclosure_hash",
    "display_text",
];
const BOUND_DELTA_FIELDS: &[&str] = &["bound_kind", "bound_hash", "display_text"];
const OUTPUT_TASK_REFERENCE_FIELDS: &[&str] = &[
    "task_key",
    "task_kind",
    "task_hash",
    "parent_statement_hash",
    "variant_statement_hash",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariant {
    pub api_version: String,
    pub variant_key: String,
    pub parent_target_key: String,
    pub parent_statement_hash: Hash,
    pub variant_statement_hash: Hash,
    pub variant_scope: ResearchVariantScope,
    pub transformation_kind: ResearchVariantTransformationKind,
    pub relationship_review: ResearchVariantRelationshipReview,
    pub assumption_deltas: Vec<ResearchVariantAssumptionDelta>,
    pub bound_deltas: Vec<ResearchVariantBoundDelta>,
    pub output_task_references: Vec<ResearchVariantOutputTaskReference>,
    pub output_replaces_parent_target: bool,
    pub output_creates_theorem_declaration: bool,
    pub output_creates_evidence_record: bool,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantRelationshipReview {
    pub review_hash: Hash,
    pub reviewer_status: ResearchVariantReviewerStatus,
    pub relationship_to_parent: ResearchVariantRelationshipToParent,
    pub relationship_inferred: bool,
    pub parent_statement_hash: Hash,
    pub variant_statement_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantAssumptionDelta {
    pub delta_kind: ResearchVariantAssumptionDeltaKind,
    pub assumption_hash: Hash,
    pub disclosure_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantBoundDelta {
    pub bound_kind: ResearchVariantBoundKind,
    pub bound_hash: Hash,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantOutputTaskReference {
    pub task_key: String,
    pub task_kind: ResearchVariantOutputTaskKind,
    pub task_hash: Hash,
    pub parent_statement_hash: Hash,
    pub variant_statement_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantScope {
    General,
    Conditional,
    SpecialCase,
}

impl ResearchVariantScope {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::General => "general",
            Self::Conditional => "conditional",
            Self::SpecialCase => "special_case",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "general" => Some(Self::General),
            "conditional" => Some(Self::Conditional),
            "special_case" => Some(Self::SpecialCase),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantTransformationKind {
    AddAssumption,
    WeakenConclusion,
    RestrictFiniteDomain,
    FixDimension,
    TestSmallParameters,
    AddSymmetry,
    AddMonotonicity,
    ApproximateForm,
    AsymptoticForm,
    AverageCaseForm,
    RandomizedForm,
    UniformNonuniformSwitch,
}

impl ResearchVariantTransformationKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::AddAssumption => "add_assumption",
            Self::WeakenConclusion => "weaken_conclusion",
            Self::RestrictFiniteDomain => "restrict_finite_domain",
            Self::FixDimension => "fix_dimension",
            Self::TestSmallParameters => "test_small_parameters",
            Self::AddSymmetry => "add_symmetry",
            Self::AddMonotonicity => "add_monotonicity",
            Self::ApproximateForm => "approximate_form",
            Self::AsymptoticForm => "asymptotic_form",
            Self::AverageCaseForm => "average_case_form",
            Self::RandomizedForm => "randomized_form",
            Self::UniformNonuniformSwitch => "uniform_nonuniform_switch",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "add_assumption" => Some(Self::AddAssumption),
            "weaken_conclusion" => Some(Self::WeakenConclusion),
            "restrict_finite_domain" => Some(Self::RestrictFiniteDomain),
            "fix_dimension" => Some(Self::FixDimension),
            "test_small_parameters" => Some(Self::TestSmallParameters),
            "add_symmetry" => Some(Self::AddSymmetry),
            "add_monotonicity" => Some(Self::AddMonotonicity),
            "approximate_form" => Some(Self::ApproximateForm),
            "asymptotic_form" => Some(Self::AsymptoticForm),
            "average_case_form" => Some(Self::AverageCaseForm),
            "randomized_form" => Some(Self::RandomizedForm),
            "uniform_nonuniform_switch" => Some(Self::UniformNonuniformSwitch),
            _ => None,
        }
    }

    pub const fn requires_assumption_delta(self) -> bool {
        matches!(
            self,
            Self::AddAssumption | Self::AverageCaseForm | Self::RandomizedForm
        )
    }

    pub const fn requires_bound_delta(self) -> bool {
        self.required_bound_kind().is_some()
    }

    pub const fn required_bound_kind(self) -> Option<ResearchVariantBoundKind> {
        match self {
            Self::RestrictFiniteDomain => Some(ResearchVariantBoundKind::FiniteDomain),
            Self::FixDimension => Some(ResearchVariantBoundKind::FixedDimension),
            Self::TestSmallParameters => Some(ResearchVariantBoundKind::SmallParameter),
            Self::ApproximateForm => Some(ResearchVariantBoundKind::ApproximationError),
            Self::AsymptoticForm => Some(ResearchVariantBoundKind::AsymptoticRange),
            Self::AverageCaseForm => Some(ResearchVariantBoundKind::AverageCaseDistribution),
            Self::RandomizedForm => Some(ResearchVariantBoundKind::RandomSeedPolicy),
            Self::UniformNonuniformSwitch => Some(ResearchVariantBoundKind::UniformityModel),
            Self::AddAssumption
            | Self::WeakenConclusion
            | Self::AddSymmetry
            | Self::AddMonotonicity => None,
        }
    }

    pub const fn disallows_strengthening_claim(self) -> bool {
        matches!(
            self,
            Self::AddAssumption
                | Self::WeakenConclusion
                | Self::RestrictFiniteDomain
                | Self::FixDimension
                | Self::TestSmallParameters
                | Self::AverageCaseForm
                | Self::RandomizedForm
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantReviewerStatus {
    NeedsReview,
    Reviewed,
    Rejected,
}

impl ResearchVariantReviewerStatus {
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
pub enum ResearchVariantRelationshipToParent {
    StrengthensParent,
    WeakensParent,
    ImpliesParent,
    IsImpliedByParent,
    EquivalentToParent,
    IncomparableWithParent,
}

impl ResearchVariantRelationshipToParent {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::StrengthensParent => "strengthens_parent",
            Self::WeakensParent => "weakens_parent",
            Self::ImpliesParent => "implies_parent",
            Self::IsImpliedByParent => "is_implied_by_parent",
            Self::EquivalentToParent => "equivalent_to_parent",
            Self::IncomparableWithParent => "incomparable_with_parent",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "strengthens_parent" => Some(Self::StrengthensParent),
            "weakens_parent" => Some(Self::WeakensParent),
            "implies_parent" => Some(Self::ImpliesParent),
            "is_implied_by_parent" => Some(Self::IsImpliedByParent),
            "equivalent_to_parent" => Some(Self::EquivalentToParent),
            "incomparable_with_parent" => Some(Self::IncomparableWithParent),
            _ => None,
        }
    }

    pub const fn is_strengthening_claim(self) -> bool {
        matches!(self, Self::StrengthensParent | Self::ImpliesParent)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantAssumptionDeltaKind {
    Added,
    Retained,
    Dropped,
}

impl ResearchVariantAssumptionDeltaKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::Added => "added",
            Self::Retained => "retained",
            Self::Dropped => "dropped",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "added" => Some(Self::Added),
            "retained" => Some(Self::Retained),
            "dropped" => Some(Self::Dropped),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantBoundKind {
    FiniteDomain,
    FixedDimension,
    SmallParameter,
    ApproximationError,
    AsymptoticRange,
    AverageCaseDistribution,
    RandomSeedPolicy,
    UniformityModel,
}

impl ResearchVariantBoundKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::FiniteDomain => "finite_domain",
            Self::FixedDimension => "fixed_dimension",
            Self::SmallParameter => "small_parameter",
            Self::ApproximationError => "approximation_error",
            Self::AsymptoticRange => "asymptotic_range",
            Self::AverageCaseDistribution => "average_case_distribution",
            Self::RandomSeedPolicy => "random_seed_policy",
            Self::UniformityModel => "uniformity_model",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "finite_domain" => Some(Self::FiniteDomain),
            "fixed_dimension" => Some(Self::FixedDimension),
            "small_parameter" => Some(Self::SmallParameter),
            "approximation_error" => Some(Self::ApproximationError),
            "asymptotic_range" => Some(Self::AsymptoticRange),
            "average_case_distribution" => Some(Self::AverageCaseDistribution),
            "random_seed_policy" => Some(Self::RandomSeedPolicy),
            "uniformity_model" => Some(Self::UniformityModel),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResearchVariantOutputTaskKind {
    ResearchTask,
    ProofTask,
}

impl ResearchVariantOutputTaskKind {
    pub const fn wire(self) -> &'static str {
        match self {
            Self::ResearchTask => "research_task",
            Self::ProofTask => "proof_task",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "research_task" => Some(Self::ResearchTask),
            "proof_task" => Some(Self::ProofTask),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantSchemaError {
    path: String,
    kind: ResearchVariantSchemaErrorKind,
}

impl ResearchVariantSchemaError {
    fn new(path: impl Into<String>, kind: ResearchVariantSchemaErrorKind) -> Self {
        Self {
            path: path.into(),
            kind,
        }
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub const fn kind(&self) -> &ResearchVariantSchemaErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchVariantSchemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.path)
    }
}

impl std::error::Error for ResearchVariantSchemaError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchVariantSchemaErrorKind {
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
    InvalidVariantScope { value: String },
    InvalidTransformationKind { value: String },
    InvalidReviewerStatus { value: String },
    InvalidRelationship { value: String },
    InvalidAssumptionDeltaKind { value: String },
    InvalidBoundKind { value: String },
    InvalidOutputTaskKind { value: String },
}

impl fmt::Display for ResearchVariantSchemaErrorKind {
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
            Self::InvalidVariantScope { value } => write!(f, "invalid variant scope `{value}`"),
            Self::InvalidTransformationKind { value } => {
                write!(f, "invalid transformation kind `{value}`")
            }
            Self::InvalidReviewerStatus { value } => {
                write!(f, "invalid reviewer status `{value}`")
            }
            Self::InvalidRelationship { value } => {
                write!(f, "invalid parent-relative relationship `{value}`")
            }
            Self::InvalidAssumptionDeltaKind { value } => {
                write!(f, "invalid assumption delta kind `{value}`")
            }
            Self::InvalidBoundKind { value } => write!(f, "invalid bound kind `{value}`"),
            Self::InvalidOutputTaskKind { value } => {
                write!(f, "invalid output task kind `{value}`")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResearchVariantValidationError {
    kind: ResearchVariantValidationErrorKind,
}

impl ResearchVariantValidationError {
    fn new(kind: ResearchVariantValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ResearchVariantValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ResearchVariantValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::error::Error for ResearchVariantValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResearchVariantValidationErrorKind {
    EmptyRequiredField {
        field: &'static str,
    },
    RelationshipRequiresReviewedStatus,
    RelationshipCannotBeInferred,
    RelationshipParentStatementHashMismatch {
        declared: String,
        review: String,
    },
    RelationshipVariantStatementHashMismatch {
        declared: String,
        review: String,
    },
    ParentReplacementRequiresReviewedEquivalence,
    VariantCannotCreateTheoremDeclaration,
    VariantCannotCreateEvidenceRecord,
    VariantMustCreateResearchOrProofTask,
    DuplicateOutputTask {
        task_key: String,
    },
    OutputTaskParentStatementHashMismatch {
        task_key: String,
    },
    OutputTaskVariantStatementHashMismatch {
        task_key: String,
    },
    DroppedAssumption {
        assumption_hash: String,
    },
    TransformationRequiresAssumptionDelta {
        transformation: ResearchVariantTransformationKind,
    },
    TransformationRequiresAddedAssumption {
        transformation: ResearchVariantTransformationKind,
    },
    TransformationRequiresBoundDelta {
        transformation: ResearchVariantTransformationKind,
    },
    TransformationRequiresBoundKind {
        transformation: ResearchVariantTransformationKind,
        expected: ResearchVariantBoundKind,
    },
    ConditionalVariantRequiresAssumption,
    SpecialCaseVariantRequiresBound,
    UnsoundStrengthening {
        transformation: ResearchVariantTransformationKind,
        relationship: ResearchVariantRelationshipToParent,
    },
}

impl fmt::Display for ResearchVariantValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRequiredField { field } => write!(f, "empty required field `{field}`"),
            Self::RelationshipRequiresReviewedStatus => {
                write!(f, "variant relationship must be explicitly reviewed")
            }
            Self::RelationshipCannotBeInferred => {
                write!(f, "variant relationship cannot be inferred")
            }
            Self::RelationshipParentStatementHashMismatch { declared, review } => write!(
                f,
                "parent statement hash mismatch: declared {declared}, review {review}"
            ),
            Self::RelationshipVariantStatementHashMismatch { declared, review } => write!(
                f,
                "variant statement hash mismatch: declared {declared}, review {review}"
            ),
            Self::ParentReplacementRequiresReviewedEquivalence => write!(
                f,
                "variant cannot replace parent unless reviewed as equivalent_to_parent"
            ),
            Self::VariantCannotCreateTheoremDeclaration => {
                write!(f, "variant generation cannot create theorem declarations")
            }
            Self::VariantCannotCreateEvidenceRecord => {
                write!(f, "variant generation cannot create evidence records")
            }
            Self::VariantMustCreateResearchOrProofTask => {
                write!(
                    f,
                    "variant generation must create research or proof task references"
                )
            }
            Self::DuplicateOutputTask { task_key } => {
                write!(f, "duplicate variant output task `{task_key}`")
            }
            Self::OutputTaskParentStatementHashMismatch { task_key } => write!(
                f,
                "output task `{task_key}` does not bind the parent statement hash"
            ),
            Self::OutputTaskVariantStatementHashMismatch { task_key } => write!(
                f,
                "output task `{task_key}` does not bind the variant statement hash"
            ),
            Self::DroppedAssumption { assumption_hash } => {
                write!(
                    f,
                    "variant cannot silently drop assumption `{assumption_hash}`"
                )
            }
            Self::TransformationRequiresAssumptionDelta { transformation } => write!(
                f,
                "transformation `{}` requires an explicit assumption delta",
                transformation.wire()
            ),
            Self::TransformationRequiresAddedAssumption { transformation } => write!(
                f,
                "transformation `{}` requires an added assumption delta",
                transformation.wire()
            ),
            Self::TransformationRequiresBoundDelta { transformation } => write!(
                f,
                "transformation `{}` requires an explicit bound delta",
                transformation.wire()
            ),
            Self::TransformationRequiresBoundKind {
                transformation,
                expected,
            } => write!(
                f,
                "transformation `{}` requires bound kind `{}`",
                transformation.wire(),
                expected.wire()
            ),
            Self::ConditionalVariantRequiresAssumption => {
                write!(f, "conditional variant requires explicit assumptions")
            }
            Self::SpecialCaseVariantRequiresBound => {
                write!(f, "special-case variant requires explicit bounds")
            }
            Self::UnsoundStrengthening {
                transformation,
                relationship,
            } => write!(
                f,
                "transformation `{}` cannot claim `{}`",
                transformation.wire(),
                relationship.wire()
            ),
        }
    }
}

pub fn parse_research_variant(source: &str) -> Result<ResearchVariant, ResearchVariantSchemaError> {
    let document = parse_json_document(source)?;
    let root = object_map(document.root(), "$", ROOT_FIELDS)?;
    let api_version = required_string(&root, "api_version", "$")?;
    if api_version != RESEARCH_VARIANT_API_VERSION {
        return Err(ResearchVariantSchemaError::new(
            "$.api_version",
            ResearchVariantSchemaErrorKind::InvalidApiVersion { value: api_version },
        ));
    }

    Ok(ResearchVariant {
        api_version,
        variant_key: required_string(&root, "variant_key", "$")?,
        parent_target_key: required_string(&root, "parent_target_key", "$")?,
        parent_statement_hash: required_hash(&root, "parent_statement_hash", "$")?,
        variant_statement_hash: required_hash(&root, "variant_statement_hash", "$")?,
        variant_scope: parse_variant_scope_value(
            required_value(&root, "variant_scope", "$")?,
            "$.variant_scope",
        )?,
        transformation_kind: parse_transformation_kind_value(
            required_value(&root, "transformation_kind", "$")?,
            "$.transformation_kind",
        )?,
        relationship_review: parse_relationship_review(required_value(
            &root,
            "relationship_review",
            "$",
        )?)?,
        assumption_deltas: parse_assumption_deltas(required_value(
            &root,
            "assumption_deltas",
            "$",
        )?)?,
        bound_deltas: parse_bound_deltas(required_value(&root, "bound_deltas", "$")?)?,
        output_task_references: parse_output_task_references(required_value(
            &root,
            "output_task_references",
            "$",
        )?)?,
        output_replaces_parent_target: required_bool(&root, "output_replaces_parent_target", "$")?,
        output_creates_theorem_declaration: required_bool(
            &root,
            "output_creates_theorem_declaration",
            "$",
        )?,
        output_creates_evidence_record: required_bool(
            &root,
            "output_creates_evidence_record",
            "$",
        )?,
        display_text: optional_string(&root, "display_text", "$")?,
    })
}

pub fn validate_research_variant(
    variant: &ResearchVariant,
) -> Result<(), ResearchVariantValidationError> {
    require_non_empty(&variant.variant_key, "variant_key")?;
    require_non_empty(&variant.parent_target_key, "parent_target_key")?;
    validate_relationship_review(variant)?;
    validate_output_boundary(variant)?;
    validate_assumption_deltas(variant)?;
    validate_bound_deltas(variant)?;
    validate_transformation_relationship(variant)?;
    Ok(())
}

fn validate_relationship_review(
    variant: &ResearchVariant,
) -> Result<(), ResearchVariantValidationError> {
    if variant.relationship_review.reviewer_status != ResearchVariantReviewerStatus::Reviewed {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::RelationshipRequiresReviewedStatus,
        ));
    }
    if variant.relationship_review.relationship_inferred {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::RelationshipCannotBeInferred,
        ));
    }
    if variant.relationship_review.parent_statement_hash != variant.parent_statement_hash {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::RelationshipParentStatementHashMismatch {
                declared: format_hash_string(&variant.parent_statement_hash),
                review: format_hash_string(&variant.relationship_review.parent_statement_hash),
            },
        ));
    }
    if variant.relationship_review.variant_statement_hash != variant.variant_statement_hash {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::RelationshipVariantStatementHashMismatch {
                declared: format_hash_string(&variant.variant_statement_hash),
                review: format_hash_string(&variant.relationship_review.variant_statement_hash),
            },
        ));
    }
    if variant.output_replaces_parent_target
        && variant.relationship_review.relationship_to_parent
            != ResearchVariantRelationshipToParent::EquivalentToParent
    {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::ParentReplacementRequiresReviewedEquivalence,
        ));
    }
    Ok(())
}

fn validate_output_boundary(
    variant: &ResearchVariant,
) -> Result<(), ResearchVariantValidationError> {
    if variant.output_creates_theorem_declaration {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::VariantCannotCreateTheoremDeclaration,
        ));
    }
    if variant.output_creates_evidence_record {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::VariantCannotCreateEvidenceRecord,
        ));
    }
    if variant.output_task_references.is_empty() {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::VariantMustCreateResearchOrProofTask,
        ));
    }

    let mut seen_tasks = BTreeSet::new();
    for task in &variant.output_task_references {
        require_non_empty(&task.task_key, "output_task_references.task_key")?;
        if !seen_tasks.insert(task.task_key.as_str()) {
            return Err(ResearchVariantValidationError::new(
                ResearchVariantValidationErrorKind::DuplicateOutputTask {
                    task_key: task.task_key.clone(),
                },
            ));
        }
        if task.parent_statement_hash != variant.parent_statement_hash {
            return Err(ResearchVariantValidationError::new(
                ResearchVariantValidationErrorKind::OutputTaskParentStatementHashMismatch {
                    task_key: task.task_key.clone(),
                },
            ));
        }
        if task.variant_statement_hash != variant.variant_statement_hash {
            return Err(ResearchVariantValidationError::new(
                ResearchVariantValidationErrorKind::OutputTaskVariantStatementHashMismatch {
                    task_key: task.task_key.clone(),
                },
            ));
        }
    }

    Ok(())
}

fn validate_assumption_deltas(
    variant: &ResearchVariant,
) -> Result<(), ResearchVariantValidationError> {
    for assumption in &variant.assumption_deltas {
        if assumption.delta_kind == ResearchVariantAssumptionDeltaKind::Dropped {
            return Err(ResearchVariantValidationError::new(
                ResearchVariantValidationErrorKind::DroppedAssumption {
                    assumption_hash: format_hash_string(&assumption.assumption_hash),
                },
            ));
        }
    }

    if (variant.transformation_kind.requires_assumption_delta()
        || variant.variant_scope == ResearchVariantScope::Conditional)
        && variant.assumption_deltas.is_empty()
    {
        let kind = if variant.transformation_kind.requires_assumption_delta() {
            ResearchVariantValidationErrorKind::TransformationRequiresAssumptionDelta {
                transformation: variant.transformation_kind,
            }
        } else {
            ResearchVariantValidationErrorKind::ConditionalVariantRequiresAssumption
        };
        return Err(ResearchVariantValidationError::new(kind));
    }

    if variant.transformation_kind == ResearchVariantTransformationKind::AddAssumption
        && !variant
            .assumption_deltas
            .iter()
            .any(|delta| delta.delta_kind == ResearchVariantAssumptionDeltaKind::Added)
    {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::TransformationRequiresAddedAssumption {
                transformation: variant.transformation_kind,
            },
        ));
    }

    Ok(())
}

fn validate_bound_deltas(variant: &ResearchVariant) -> Result<(), ResearchVariantValidationError> {
    if variant.transformation_kind.requires_bound_delta() && variant.bound_deltas.is_empty() {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::TransformationRequiresBoundDelta {
                transformation: variant.transformation_kind,
            },
        ));
    }
    if let Some(expected) = variant.transformation_kind.required_bound_kind() {
        if !variant
            .bound_deltas
            .iter()
            .any(|delta| delta.bound_kind == expected)
        {
            return Err(ResearchVariantValidationError::new(
                ResearchVariantValidationErrorKind::TransformationRequiresBoundKind {
                    transformation: variant.transformation_kind,
                    expected,
                },
            ));
        }
    }
    if variant.variant_scope == ResearchVariantScope::SpecialCase && variant.bound_deltas.is_empty()
    {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::SpecialCaseVariantRequiresBound,
        ));
    }
    Ok(())
}

fn validate_transformation_relationship(
    variant: &ResearchVariant,
) -> Result<(), ResearchVariantValidationError> {
    let relationship = variant.relationship_review.relationship_to_parent;
    if variant.transformation_kind.disallows_strengthening_claim()
        && relationship.is_strengthening_claim()
    {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::UnsoundStrengthening {
                transformation: variant.transformation_kind,
                relationship,
            },
        ));
    }
    Ok(())
}

fn parse_relationship_review(
    value: &JsonValue<'_>,
) -> Result<ResearchVariantRelationshipReview, ResearchVariantSchemaError> {
    let members = object_map(value, "$.relationship_review", RELATIONSHIP_REVIEW_FIELDS)?;
    Ok(ResearchVariantRelationshipReview {
        review_hash: required_hash(&members, "review_hash", "$.relationship_review")?,
        reviewer_status: parse_reviewer_status_value(
            required_value(&members, "reviewer_status", "$.relationship_review")?,
            "$.relationship_review.reviewer_status",
        )?,
        relationship_to_parent: parse_relationship_value(
            required_value(&members, "relationship_to_parent", "$.relationship_review")?,
            "$.relationship_review.relationship_to_parent",
        )?,
        relationship_inferred: required_bool(
            &members,
            "relationship_inferred",
            "$.relationship_review",
        )?,
        parent_statement_hash: required_hash(
            &members,
            "parent_statement_hash",
            "$.relationship_review",
        )?,
        variant_statement_hash: required_hash(
            &members,
            "variant_statement_hash",
            "$.relationship_review",
        )?,
        display_text: optional_string(&members, "display_text", "$.relationship_review")?,
    })
}

fn parse_assumption_deltas(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchVariantAssumptionDelta>, ResearchVariantSchemaError> {
    array_elements(value, "$.assumption_deltas")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_assumption_delta(value, &format!("$.assumption_deltas[{index}]"))
        })
        .collect()
}

fn parse_assumption_delta(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantAssumptionDelta, ResearchVariantSchemaError> {
    let members = object_map(value, path, ASSUMPTION_DELTA_FIELDS)?;
    Ok(ResearchVariantAssumptionDelta {
        delta_kind: parse_assumption_delta_kind_value(
            required_value(&members, "delta_kind", path)?,
            &format!("{path}.delta_kind"),
        )?,
        assumption_hash: required_hash(&members, "assumption_hash", path)?,
        disclosure_hash: required_hash(&members, "disclosure_hash", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_bound_deltas(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchVariantBoundDelta>, ResearchVariantSchemaError> {
    array_elements(value, "$.bound_deltas")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_bound_delta(value, &format!("$.bound_deltas[{index}]")))
        .collect()
}

fn parse_bound_delta(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantBoundDelta, ResearchVariantSchemaError> {
    let members = object_map(value, path, BOUND_DELTA_FIELDS)?;
    Ok(ResearchVariantBoundDelta {
        bound_kind: parse_bound_kind_value(
            required_value(&members, "bound_kind", path)?,
            &format!("{path}.bound_kind"),
        )?,
        bound_hash: required_hash(&members, "bound_hash", path)?,
        display_text: optional_string(&members, "display_text", path)?,
    })
}

fn parse_output_task_references(
    value: &JsonValue<'_>,
) -> Result<Vec<ResearchVariantOutputTaskReference>, ResearchVariantSchemaError> {
    array_elements(value, "$.output_task_references")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            parse_output_task_reference(value, &format!("$.output_task_references[{index}]"))
        })
        .collect()
}

fn parse_output_task_reference(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantOutputTaskReference, ResearchVariantSchemaError> {
    let members = object_map(value, path, OUTPUT_TASK_REFERENCE_FIELDS)?;
    Ok(ResearchVariantOutputTaskReference {
        task_key: required_string(&members, "task_key", path)?,
        task_kind: parse_output_task_kind_value(
            required_value(&members, "task_kind", path)?,
            &format!("{path}.task_kind"),
        )?,
        task_hash: required_hash(&members, "task_hash", path)?,
        parent_statement_hash: required_hash(&members, "parent_statement_hash", path)?,
        variant_statement_hash: required_hash(&members, "variant_statement_hash", path)?,
    })
}

fn parse_json_document(source: &str) -> Result<JsonDocument<'_>, ResearchVariantSchemaError> {
    JsonDocument::parse(source).map_err(|error| {
        ResearchVariantSchemaError::new(
            "$",
            ResearchVariantSchemaErrorKind::JsonParse {
                offset: error.offset,
            },
        )
    })
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
    allowed_fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'src>>, ResearchVariantSchemaError> {
    let Some(members) = value.object_members() else {
        return Err(ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    let mut map = BTreeMap::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(ResearchVariantSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchVariantSchemaErrorKind::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
        if !allowed_fields
            .iter()
            .any(|allowed| *allowed == member.key())
        {
            return Err(ResearchVariantSchemaError::new(
                format!("{path}.{}", member.key()),
                ResearchVariantSchemaErrorKind::UnknownField {
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
) -> Result<&'value [JsonValue<'src>], ResearchVariantSchemaError> {
    value.array_elements().ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::ExpectedArray {
                actual: value.kind(),
            },
        )
    })
}

fn required_value<'value, 'src>(
    members: &BTreeMap<&'value str, &'value JsonValue<'src>>,
    field: &'static str,
    path: &str,
) -> Result<&'value JsonValue<'src>, ResearchVariantSchemaError> {
    members.get(field).copied().ok_or_else(|| {
        ResearchVariantSchemaError::new(
            format!("{path}.{field}"),
            ResearchVariantSchemaErrorKind::MissingField { field },
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
) -> Result<String, ResearchVariantSchemaError> {
    string_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn optional_string(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Option<String>, ResearchVariantSchemaError> {
    optional_value(members, field)
        .map(|value| string_value(value, &format!("{path}.{field}")))
        .transpose()
}

fn string_value(value: &JsonValue<'_>, path: &str) -> Result<String, ResearchVariantSchemaError> {
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::ExpectedString {
                actual: value.kind(),
            },
        )
    })
}

fn required_bool(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<bool, ResearchVariantSchemaError> {
    bool_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn bool_value(value: &JsonValue<'_>, path: &str) -> Result<bool, ResearchVariantSchemaError> {
    value.bool_value().ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::ExpectedBool {
                actual: value.kind(),
            },
        )
    })
}

fn required_hash(
    members: &BTreeMap<&str, &JsonValue<'_>>,
    field: &'static str,
    path: &str,
) -> Result<Hash, ResearchVariantSchemaError> {
    hash_value(
        required_value(members, field, path)?,
        &format!("{path}.{field}"),
    )
}

fn hash_value(value: &JsonValue<'_>, path: &str) -> Result<Hash, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    parse_hash_string(&wire).map_err(|_| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidHash { value: wire },
        )
    })
}

fn parse_variant_scope_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantScope, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantScope::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidVariantScope { value: wire },
        )
    })
}

fn parse_transformation_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantTransformationKind, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantTransformationKind::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidTransformationKind { value: wire },
        )
    })
}

fn parse_reviewer_status_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantReviewerStatus, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantReviewerStatus::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidReviewerStatus { value: wire },
        )
    })
}

fn parse_relationship_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantRelationshipToParent, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantRelationshipToParent::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidRelationship { value: wire },
        )
    })
}

fn parse_assumption_delta_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantAssumptionDeltaKind, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantAssumptionDeltaKind::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidAssumptionDeltaKind { value: wire },
        )
    })
}

fn parse_bound_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantBoundKind, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantBoundKind::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidBoundKind { value: wire },
        )
    })
}

fn parse_output_task_kind_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ResearchVariantOutputTaskKind, ResearchVariantSchemaError> {
    let wire = string_value(value, path)?;
    ResearchVariantOutputTaskKind::parse(&wire).ok_or_else(|| {
        ResearchVariantSchemaError::new(
            path,
            ResearchVariantSchemaErrorKind::InvalidOutputTaskKind { value: wire },
        )
    })
}

fn require_non_empty(
    value: &str,
    field: &'static str,
) -> Result<(), ResearchVariantValidationError> {
    if value.trim().is_empty() {
        return Err(ResearchVariantValidationError::new(
            ResearchVariantValidationErrorKind::EmptyRequiredField { field },
        ));
    }
    Ok(())
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
            .join("../npa/develop/proof-using-agents/fixtures/pua-m16-research-variant")
            .join(name)
    }

    fn fixture(name: &str) -> String {
        std::fs::read_to_string(fixture_path(name)).expect("research variant fixture should exist")
    }

    fn parse_fixture(name: &str) -> ResearchVariant {
        parse_research_variant(&fixture(name)).expect("research variant fixture should parse")
    }

    fn validate_fixture(name: &str) -> Result<(), ResearchVariantValidationErrorKind> {
        let variant = parse_fixture(name);
        validate_research_variant(&variant).map_err(|error| error.kind().clone())
    }

    #[test]
    fn research_variant_relationships() {
        let add_assumption = parse_fixture("valid-add-assumption.json");
        validate_research_variant(&add_assumption).expect("add-assumption variant should pass");
        assert_eq!(
            add_assumption.relationship_review.relationship_to_parent,
            ResearchVariantRelationshipToParent::WeakensParent
        );
        assert!(!add_assumption.relationship_review.relationship_inferred);
        assert_eq!(
            add_assumption.relationship_review.parent_statement_hash,
            add_assumption.parent_statement_hash
        );
        assert_eq!(
            add_assumption.relationship_review.variant_statement_hash,
            add_assumption.variant_statement_hash
        );

        let small_parameter = parse_fixture("valid-small-parameter-proof-task.json");
        validate_research_variant(&small_parameter).expect("small-parameter variant should pass");
        assert_eq!(
            small_parameter.relationship_review.relationship_to_parent,
            ResearchVariantRelationshipToParent::IsImpliedByParent
        );
        assert_eq!(
            small_parameter.output_task_references[0].task_kind,
            ResearchVariantOutputTaskKind::ProofTask
        );

        assert!(matches!(
            parse_research_variant(&fixture("missing-relationship.json"))
                .map_err(|error| error.kind().clone()),
            Err(ResearchVariantSchemaErrorKind::MissingField {
                field: "relationship_review"
            })
        ));
        assert_eq!(
            validate_fixture("unsound-strengthening.json"),
            Err(ResearchVariantValidationErrorKind::UnsoundStrengthening {
                transformation: ResearchVariantTransformationKind::WeakenConclusion,
                relationship: ResearchVariantRelationshipToParent::StrengthensParent,
            })
        );
        assert_eq!(
            validate_fixture("inferred-relationship.json"),
            Err(ResearchVariantValidationErrorKind::RelationshipCannotBeInferred)
        );
        assert_eq!(
            validate_fixture("statement-hash-mismatch.json"),
            Err(
                ResearchVariantValidationErrorKind::RelationshipVariantStatementHashMismatch {
                    declared:
                        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                            .to_owned(),
                    review:
                        "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
                            .to_owned(),
                }
            )
        );
        assert_eq!(
            validate_fixture("theorem-declaration-output.json"),
            Err(ResearchVariantValidationErrorKind::VariantCannotCreateTheoremDeclaration)
        );
        assert_eq!(
            validate_fixture("evidence-record-output.json"),
            Err(ResearchVariantValidationErrorKind::VariantCannotCreateEvidenceRecord)
        );
    }

    #[test]
    fn research_variant_rejects_unreviewed_equivalence() {
        assert_eq!(
            validate_fixture("unreviewed-equivalence-replacement.json"),
            Err(ResearchVariantValidationErrorKind::RelationshipRequiresReviewedStatus)
        );

        assert_eq!(
            validate_fixture("non-equivalent-parent-replacement.json"),
            Err(ResearchVariantValidationErrorKind::ParentReplacementRequiresReviewedEquivalence)
        );
    }

    #[test]
    fn research_variant_preserves_assumption_record() {
        let valid = parse_fixture("valid-add-assumption.json");
        validate_research_variant(&valid).expect("valid assumption variant should pass");
        assert_eq!(valid.variant_scope, ResearchVariantScope::Conditional);
        assert!(valid.assumption_deltas.iter().any(|delta| {
            delta.delta_kind == ResearchVariantAssumptionDeltaKind::Added
                && delta.disclosure_hash != [0u8; 32]
        }));

        assert_eq!(
            validate_fixture("dropped-assumption.json"),
            Err(ResearchVariantValidationErrorKind::DroppedAssumption {
                assumption_hash:
                    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                        .to_owned(),
            })
        );
        assert_eq!(
            validate_fixture("conditional-missing-assumption.json"),
            Err(
                ResearchVariantValidationErrorKind::TransformationRequiresAssumptionDelta {
                    transformation: ResearchVariantTransformationKind::AddAssumption,
                }
            )
        );
        assert_eq!(
            validate_fixture("add-assumption-without-added-assumption.json"),
            Err(
                ResearchVariantValidationErrorKind::TransformationRequiresAddedAssumption {
                    transformation: ResearchVariantTransformationKind::AddAssumption,
                }
            )
        );
        assert_eq!(
            validate_fixture("special-case-missing-bound.json"),
            Err(
                ResearchVariantValidationErrorKind::TransformationRequiresBoundDelta {
                    transformation: ResearchVariantTransformationKind::TestSmallParameters,
                }
            )
        );
        assert_eq!(
            validate_fixture("small-parameter-wrong-bound.json"),
            Err(
                ResearchVariantValidationErrorKind::TransformationRequiresBoundKind {
                    transformation: ResearchVariantTransformationKind::TestSmallParameters,
                    expected: ResearchVariantBoundKind::SmallParameter,
                }
            )
        );
    }
}

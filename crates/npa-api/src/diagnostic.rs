use std::collections::BTreeSet;

use npa_cert::{Hash, Name};
use npa_tactic::{
    goal_id_canonical_bytes, DiagnosticBudget, DiagnosticBudgetCounterReport,
    DiagnosticBudgetReport, DiagnosticProfile, DiagnosticRequestPath, GoalId, RewriteDiagnostic,
    RewriteDiagnosticSite, UnificationConflictSubsetKind, UnificationDiagnosticPhase,
    UniverseConstraintDiagnostic, UniverseDiagnostic, UniverseInstantiationCandidate,
};
use sha2::{Digest, Sha256};

use crate::current::{encode_machine_axiom_ref_wire, MachineAxiomRefWire};
use crate::json::{JsonDocument, JsonParseError, JsonValue, JsonValueKind};
use crate::types::{
    format_goal_id_wire, format_hash_string, parse_goal_id_wire, parse_hash_string, ExprPath,
    ExprPathStep, MachineWireGrammarErrorKind,
};
use crate::validation::{
    parse_strict_u64_token, validate_json_object, FieldSpec, JsonFieldType, JsonPath,
    MachineApiRequestError, ObjectSchema, StrictUnsignedIntegerError,
};
use crate::{
    MachineApiDiagnosticPhase, MachineApiDiagnosticProjection, MachineApiErrorKind,
    MachineApiTacticKind, MachineApiUpstreamDiagnostic,
};

const API_DIAGNOSTIC_TAG: &str = "npa.machine-api.api-diagnostic.v1";
pub const MACHINE_DIAGNOSTIC_TREE_SCHEMA: &str = "npa.machine-diagnostic-tree.v1";
const MACHINE_DIAGNOSTIC_TREE_HASH_TAG: &str = "npa.machine-diagnostic-tree.v1";
const MACHINE_DIAGNOSTIC_TREE_MAX_DEPTH: usize = 4;
const MACHINE_DIAGNOSTIC_TREE_MAX_CHILDREN: usize = 16;
const MACHINE_DIAGNOSTIC_TREE_MAX_PATH_STEPS: usize = 64;
const MACHINE_DIAGNOSTIC_TREE_MAX_RELATED_CONSTRAINTS: usize = 32;

const DIAGNOSTIC_TREE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("schema", JsonFieldType::String),
    FieldSpec::required("diagnostic_hash", JsonFieldType::String),
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("phase", JsonFieldType::String),
    FieldSpec::required("profile", JsonFieldType::String),
    FieldSpec::required("goal_id", JsonFieldType::String).allow_null(),
    FieldSpec::required("candidate_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("deterministic_budget_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("state_fingerprint", JsonFieldType::String).allow_null(),
    FieldSpec::required("expression_path", JsonFieldType::Array),
    FieldSpec::required("expected_summary", JsonFieldType::Object).allow_null(),
    FieldSpec::required("actual_summary", JsonFieldType::Object).allow_null(),
    FieldSpec::required("related_constraints", JsonFieldType::Array),
    FieldSpec::required("parent_diagnostic_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("budget_report", JsonFieldType::Object).allow_null(),
    FieldSpec::required("children", JsonFieldType::Array),
    FieldSpec::required("source_message", JsonFieldType::String).allow_null(),
    FieldSpec::required("pretty_payload", JsonFieldType::Object).allow_null(),
];

const TERM_SUMMARY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("head_symbol", JsonFieldType::String).allow_null(),
    FieldSpec::required("structural_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required(
        "node_count",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    )
    .allow_null(),
    FieldSpec::required("attributes", JsonFieldType::Object),
];

const RELATED_CONSTRAINT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("constraint_id", JsonFieldType::String),
    FieldSpec::required("kind", JsonFieldType::String),
    FieldSpec::required("phase", JsonFieldType::String),
    FieldSpec::required("lhs_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("rhs_hash", JsonFieldType::String).allow_null(),
    FieldSpec::required("path", JsonFieldType::Array),
    FieldSpec::required("expected_summary", JsonFieldType::Object).allow_null(),
    FieldSpec::required("actual_summary", JsonFieldType::Object).allow_null(),
    FieldSpec::required("child_constraint_ids", JsonFieldType::Array),
    FieldSpec::required("subset_kind", JsonFieldType::String),
    FieldSpec::required("attributes", JsonFieldType::Object),
];

const BUDGET_REPORT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("truncated", JsonFieldType::Boolean),
    FieldSpec::required("graph_nodes", JsonFieldType::Object),
    FieldSpec::required("expression_paths", JsonFieldType::Object),
    FieldSpec::required("rewrite_site_scans", JsonFieldType::Object),
    FieldSpec::required("pretty_term_bytes", JsonFieldType::Object),
    FieldSpec::required("repair_proposals", JsonFieldType::Object),
    FieldSpec::required("diagnostic_steps", JsonFieldType::Object),
];

const BUDGET_COUNTER_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("used", JsonFieldType::UnsignedInteger { max: u64::MAX }),
    FieldSpec::required("limit", JsonFieldType::UnsignedInteger { max: u64::MAX }),
    FieldSpec::required("truncated", JsonFieldType::Boolean),
];

const PRETTY_PAYLOAD_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("message", JsonFieldType::String).allow_null(),
    FieldSpec::required("pretty_terms", JsonFieldType::Array),
    FieldSpec::required("repair_proposals", JsonFieldType::Array),
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDiagnosticTree {
    pub kind: MachineApiErrorKind,
    pub phase: crate::MachineApiDiagnosticPhase,
    pub profile: DiagnosticProfile,
    pub goal_id: Option<GoalId>,
    pub candidate_hash: Option<Hash>,
    pub deterministic_budget_hash: Option<Hash>,
    pub state_fingerprint: Option<Hash>,
    pub expression_path: Vec<String>,
    pub expected_summary: Option<MachineDiagnosticTermSummary>,
    pub actual_summary: Option<MachineDiagnosticTermSummary>,
    pub related_constraints: Vec<MachineDiagnosticConstraintSummary>,
    pub parent_diagnostic_hash: Option<Hash>,
    pub budget_report: Option<DiagnosticBudgetReport>,
    pub children: Vec<MachineDiagnosticTree>,
    pub source_message: Option<String>,
    pub pretty_payload: Option<MachineDiagnosticPrettyPayload>,
}

impl MachineDiagnosticTree {
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, MachineDiagnosticTreeCanonicalizationError> {
        machine_diagnostic_tree_canonical_bytes(self)
    }

    pub fn diagnostic_hash(&self) -> Result<Hash, MachineDiagnosticTreeCanonicalizationError> {
        machine_diagnostic_tree_hash(self)
    }

    pub fn canonical_json(&self) -> Result<String, MachineDiagnosticTreeCanonicalizationError> {
        machine_diagnostic_tree_canonical_json(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDiagnosticTermSummary {
    pub head_symbol: Option<String>,
    pub structural_hash: Option<Hash>,
    pub node_count: Option<u64>,
    pub attributes: Vec<MachineDiagnosticAttribute>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachineDiagnosticAttribute {
    pub key: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDiagnosticConstraintSummary {
    pub constraint_id: String,
    pub kind: String,
    pub phase: crate::MachineApiDiagnosticPhase,
    pub lhs_hash: Option<Hash>,
    pub rhs_hash: Option<Hash>,
    pub path: Vec<String>,
    pub expected_summary: Option<MachineDiagnosticTermSummary>,
    pub actual_summary: Option<MachineDiagnosticTermSummary>,
    pub child_constraint_ids: Vec<String>,
    pub subset_kind: MachineDiagnosticConflictSubsetKind,
    pub attributes: Vec<MachineDiagnosticAttribute>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MachineDiagnosticConflictSubsetKind {
    Minimal,
    Reduced,
    Truncated,
}

impl MachineDiagnosticConflictSubsetKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Minimal => "minimal",
            Self::Reduced => "reduced",
            Self::Truncated => "truncated",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDiagnosticPrettyPayload {
    pub message: Option<String>,
    pub pretty_terms: Vec<String>,
    pub repair_proposals: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDiagnosticTreeCanonicalizationError {
    LengthExceeded { field: &'static str, len: usize },
    DepthExceeded { max_depth: usize },
    TooManyChildren { len: usize, max: usize },
    TooManyExpressionPathSteps { len: usize, max: usize },
    TooManyRelatedConstraints { len: usize, max: usize },
    DuplicateChildDiagnosticHash { hash: Hash },
    DuplicateRelatedConstraint,
    DuplicateAttribute { key: String },
    NonCanonicalAttributeOrder,
    InvalidExpressionPath { step: String },
    OffProfileHasRichPayload,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDiagnosticTreeParseError {
    Json(JsonParseError),
    Shape(Box<MachineApiRequestError>),
    UnsupportedSchema {
        actual: String,
    },
    UnsupportedEnum {
        field: &'static str,
        value: String,
    },
    InvalidHash {
        field: &'static str,
        error: MachineWireGrammarErrorKind,
    },
    InvalidGoalId {
        field: &'static str,
        error: MachineWireGrammarErrorKind,
    },
    InvalidUnsignedInteger {
        field: &'static str,
        raw: String,
        error: StrictUnsignedIntegerError,
    },
    BudgetCounterMismatch {
        field: &'static str,
    },
    BudgetReportMismatch,
    DiagnosticHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    Canonical(MachineDiagnosticTreeCanonicalizationError),
}

pub fn machine_diagnostic_tree_canonical_bytes(
    tree: &MachineDiagnosticTree,
) -> Result<Vec<u8>, MachineDiagnosticTreeCanonicalizationError> {
    let mut out = Vec::new();
    encode_tree_to(&mut out, tree, 0)?;
    Ok(out)
}

pub fn machine_diagnostic_tree_hash(
    tree: &MachineDiagnosticTree,
) -> Result<Hash, MachineDiagnosticTreeCanonicalizationError> {
    let canonical = machine_diagnostic_tree_canonical_bytes(tree)?;
    let digest = Sha256::digest(&canonical);
    let mut hash = [0; 32];
    hash.copy_from_slice(&digest);
    Ok(hash)
}

pub fn machine_diagnostic_tree_canonical_json(
    tree: &MachineDiagnosticTree,
) -> Result<String, MachineDiagnosticTreeCanonicalizationError> {
    let diagnostic_hash = machine_diagnostic_tree_hash(tree)?;
    let mut out = String::new();
    write_tree_json(&mut out, tree, diagnostic_hash)?;
    Ok(out)
}

pub fn parse_machine_diagnostic_tree_json(
    source: &str,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeParseError> {
    let doc = JsonDocument::parse(source).map_err(MachineDiagnosticTreeParseError::Json)?;
    parse_diagnostic_tree_value(doc.root(), 0)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineDiagnosticTreeAdapterContext {
    pub profile: DiagnosticProfile,
    pub candidate_hash: Option<Hash>,
    pub deterministic_budget_hash: Option<Hash>,
    pub state_fingerprint: Option<Hash>,
    pub diagnostic_budget: DiagnosticBudget,
}

impl MachineDiagnosticTreeAdapterContext {
    pub fn off() -> Self {
        Self {
            profile: DiagnosticProfile::Off,
            candidate_hash: None,
            deterministic_budget_hash: None,
            state_fingerprint: None,
            diagnostic_budget: DiagnosticBudget::default(),
        }
    }

    pub fn basic() -> Self {
        Self {
            profile: DiagnosticProfile::Basic,
            candidate_hash: None,
            deterministic_budget_hash: None,
            state_fingerprint: None,
            diagnostic_budget: DiagnosticBudget::default(),
        }
    }

    pub fn full() -> Self {
        Self {
            profile: DiagnosticProfile::Full,
            candidate_hash: None,
            deterministic_budget_hash: None,
            state_fingerprint: None,
            diagnostic_budget: DiagnosticBudget::default(),
        }
    }
}

impl Default for MachineDiagnosticTreeAdapterContext {
    fn default() -> Self {
        Self::off()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDiagnosticTreeAdapterError {
    ApiDiagnostic(MachineApiDiagnosticCanonicalizationError),
    Tree(MachineDiagnosticTreeCanonicalizationError),
}

impl From<MachineApiDiagnosticCanonicalizationError> for MachineDiagnosticTreeAdapterError {
    fn from(error: MachineApiDiagnosticCanonicalizationError) -> Self {
        Self::ApiDiagnostic(error)
    }
}

impl From<MachineDiagnosticTreeCanonicalizationError> for MachineDiagnosticTreeAdapterError {
    fn from(error: MachineDiagnosticTreeCanonicalizationError) -> Self {
        Self::Tree(error)
    }
}

pub fn machine_api_projection_diagnostic_tree(
    diagnostic: &MachineApiDiagnosticProjection,
    context: MachineDiagnosticTreeAdapterContext,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeAdapterError> {
    diagnostic.diagnostic_hash()?;
    let (related_constraints, budget_report, pretty_payload) =
        projection_full_sidecar_payload(diagnostic, context);

    let tree = MachineDiagnosticTree {
        kind: diagnostic.kind,
        phase: diagnostic.phase,
        profile: context.profile,
        goal_id: diagnostic.goal_id,
        candidate_hash: context.candidate_hash,
        deterministic_budget_hash: context.deterministic_budget_hash,
        state_fingerprint: context.state_fingerprint,
        expression_path: Vec::new(),
        expected_summary: projection_term_summary(
            diagnostic,
            diagnostic.expected_hash,
            ProjectionTermSide::Expected,
            context.profile,
        ),
        actual_summary: projection_term_summary(
            diagnostic,
            diagnostic.actual_hash,
            ProjectionTermSide::Actual,
            context.profile,
        ),
        related_constraints,
        parent_diagnostic_hash: None,
        budget_report,
        children: Vec::new(),
        source_message: Some(diagnostic.source_message.clone()),
        pretty_payload,
    };
    tree.diagnostic_hash()?;
    Ok(tree)
}

pub fn machine_tactic_diagnostic_tree(
    diagnostic: npa_tactic::MachineTacticDiagnostic,
    phase: MachineApiDiagnosticPhase,
    context: MachineDiagnosticTreeAdapterContext,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeAdapterError> {
    let projection = crate::adapter::project_machine_tactic_diagnostic(diagnostic, phase);
    machine_api_projection_diagnostic_tree(&projection, context)
}

pub fn machine_frontend_diagnostic_tree(
    diagnostic: npa_frontend::MachineDiagnostic,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<GoalId>,
    tactic_kind: Option<MachineApiTacticKind>,
    context: MachineDiagnosticTreeAdapterContext,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeAdapterError> {
    let projection =
        crate::adapter::project_frontend_diagnostic(diagnostic, phase, goal_id, tactic_kind);
    machine_api_projection_diagnostic_tree(&projection, context)
}

pub fn human_diagnostic_tree(
    diagnostic: &npa_frontend::HumanDiagnostic,
    context: MachineDiagnosticTreeAdapterContext,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeAdapterError> {
    let phase = diagnostic
        .payload
        .as_ref()
        .and_then(|payload| payload.phase)
        .unwrap_or(npa_frontend::HumanDiagnosticPhase::Elaborator);
    let tree = MachineDiagnosticTree {
        kind: map_human_diagnostic_kind(&diagnostic.kind),
        phase: map_human_diagnostic_phase(phase),
        profile: context.profile,
        goal_id: None,
        candidate_hash: context.candidate_hash,
        deterministic_budget_hash: context.deterministic_budget_hash,
        state_fingerprint: context.state_fingerprint,
        expression_path: Vec::new(),
        expected_summary: None,
        actual_summary: None,
        related_constraints: Vec::new(),
        parent_diagnostic_hash: None,
        budget_report: None,
        children: Vec::new(),
        source_message: Some(diagnostic.message.clone()),
        pretty_payload: None,
    };
    tree.diagnostic_hash()?;
    Ok(tree)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProjectionTermSide {
    Expected,
    Actual,
}

fn projection_term_summary(
    diagnostic: &MachineApiDiagnosticProjection,
    structural_hash: Option<Hash>,
    side: ProjectionTermSide,
    profile: DiagnosticProfile,
) -> Option<MachineDiagnosticTermSummary> {
    if profile == DiagnosticProfile::Off {
        return None;
    }

    structural_hash.map(|hash| MachineDiagnosticTermSummary {
        head_symbol: projection_head_symbol(diagnostic, side),
        structural_hash: Some(hash),
        node_count: None,
        attributes: projection_term_attributes(diagnostic, side),
    })
}

fn projection_head_symbol(
    diagnostic: &MachineApiDiagnosticProjection,
    _side: ProjectionTermSide,
) -> Option<String> {
    match &diagnostic.upstream {
        MachineApiUpstreamDiagnostic::Frontend(frontend) => frontend
            .payload
            .as_ref()
            .and_then(|payload| payload.head_symbol.clone()),
        MachineApiUpstreamDiagnostic::MachineTactic(_) => None,
    }
}

fn projection_term_attributes(
    diagnostic: &MachineApiDiagnosticProjection,
    side: ProjectionTermSide,
) -> Vec<MachineDiagnosticAttribute> {
    let MachineApiUpstreamDiagnostic::Frontend(frontend) = &diagnostic.upstream else {
        return Vec::new();
    };
    let Some(payload) = frontend.payload.as_ref() else {
        return Vec::new();
    };
    let universe_args = match side {
        ProjectionTermSide::Expected => payload.expected_universe_args,
        ProjectionTermSide::Actual => payload.actual_universe_args,
    };
    universe_args
        .map(|count| {
            vec![MachineDiagnosticAttribute {
                key: "universe_args".to_owned(),
                value: count.to_string(),
            }]
        })
        .unwrap_or_default()
}

fn projection_full_sidecar_payload(
    diagnostic: &MachineApiDiagnosticProjection,
    context: MachineDiagnosticTreeAdapterContext,
) -> (
    Vec<MachineDiagnosticConstraintSummary>,
    Option<DiagnosticBudgetReport>,
    Option<MachineDiagnosticPrettyPayload>,
) {
    let universe_payload = projection_universe_diagnostic_payload(diagnostic, context);
    if universe_payload.1.is_some() || universe_payload.2.is_some() {
        return universe_payload;
    }

    let rewrite_payload = projection_rewrite_diagnostic_payload(diagnostic, context);
    if rewrite_payload.1.is_some() || rewrite_payload.2.is_some() {
        return rewrite_payload;
    }

    let (constraints, budget_report) = projection_unification_conflict_payload(diagnostic, context);
    (constraints, budget_report, None)
}

fn projection_universe_diagnostic_payload(
    diagnostic: &MachineApiDiagnosticProjection,
    context: MachineDiagnosticTreeAdapterContext,
) -> (
    Vec<MachineDiagnosticConstraintSummary>,
    Option<DiagnosticBudgetReport>,
    Option<MachineDiagnosticPrettyPayload>,
) {
    if context.profile != DiagnosticProfile::Full {
        return (Vec::new(), None, None);
    }

    let MachineApiUpstreamDiagnostic::MachineTactic(tactic_diagnostic) = &diagnostic.upstream
    else {
        return (Vec::new(), None, None);
    };
    let Some(universe) = npa_tactic::universe_diagnostic_for_profile(
        tactic_diagnostic,
        DiagnosticProfile::Full,
        DiagnosticRequestPath::ExplicitFailureRequest,
        context.diagnostic_budget,
    ) else {
        return (Vec::new(), None, None);
    };

    let subset_kind = map_unification_subset_kind(universe.subset_kind);
    let constraints = universe
        .constraints
        .iter()
        .map(|constraint| MachineDiagnosticConstraintSummary {
            constraint_id: constraint.id.wire(),
            kind: constraint.kind.as_str().to_owned(),
            phase: diagnostic.phase,
            lhs_hash: None,
            rhs_hash: None,
            path: api_safe_universe_path(&constraint.path),
            expected_summary: None,
            actual_summary: None,
            child_constraint_ids: constraint
                .dependency_ids
                .iter()
                .map(|dependency_id| dependency_id.wire())
                .collect(),
            subset_kind,
            attributes: universe_constraint_attributes(&universe, constraint),
        })
        .collect();
    let repair_proposals = universe_repair_proposal_strings(&universe);
    let pretty_payload = if repair_proposals.is_empty() {
        None
    } else {
        Some(MachineDiagnosticPrettyPayload {
            message: None,
            pretty_terms: Vec::new(),
            repair_proposals,
        })
    };
    (constraints, Some(universe.budget_report), pretty_payload)
}

fn projection_unification_conflict_payload(
    diagnostic: &MachineApiDiagnosticProjection,
    context: MachineDiagnosticTreeAdapterContext,
) -> (
    Vec<MachineDiagnosticConstraintSummary>,
    Option<DiagnosticBudgetReport>,
) {
    if context.profile != DiagnosticProfile::Full {
        return (Vec::new(), None);
    }

    let MachineApiUpstreamDiagnostic::MachineTactic(tactic_diagnostic) = &diagnostic.upstream
    else {
        return (Vec::new(), None);
    };
    let Some(conflict_set) = npa_tactic::unification_conflict_set_for_profile(
        tactic_diagnostic,
        DiagnosticProfile::Full,
        DiagnosticRequestPath::ExplicitFailureRequest,
        context.diagnostic_budget,
    ) else {
        return (Vec::new(), None);
    };
    let subset_kind = map_unification_subset_kind(conflict_set.subset_kind);
    let constraints = conflict_set
        .constraints
        .into_iter()
        .map(|constraint| MachineDiagnosticConstraintSummary {
            constraint_id: constraint.id.wire(),
            kind: constraint.kind.as_str().to_owned(),
            phase: map_unification_constraint_phase(constraint.phase),
            lhs_hash: constraint.expected_hash,
            rhs_hash: constraint.actual_hash,
            path: constraint.path,
            expected_summary: hash_term_summary(constraint.expected_hash),
            actual_summary: hash_term_summary(constraint.actual_hash),
            child_constraint_ids: constraint
                .child_ids
                .into_iter()
                .map(|child_id| child_id.wire())
                .collect(),
            subset_kind,
            attributes: Vec::new(),
        })
        .collect();
    (constraints, Some(conflict_set.budget_report))
}

fn projection_rewrite_diagnostic_payload(
    diagnostic: &MachineApiDiagnosticProjection,
    context: MachineDiagnosticTreeAdapterContext,
) -> (
    Vec<MachineDiagnosticConstraintSummary>,
    Option<DiagnosticBudgetReport>,
    Option<MachineDiagnosticPrettyPayload>,
) {
    if context.profile != DiagnosticProfile::Full {
        return (Vec::new(), None, None);
    }

    let MachineApiUpstreamDiagnostic::MachineTactic(tactic_diagnostic) = &diagnostic.upstream
    else {
        return (Vec::new(), None, None);
    };
    let Some(rewrite) = npa_tactic::rewrite_diagnostic_for_profile(
        tactic_diagnostic,
        DiagnosticProfile::Full,
        DiagnosticRequestPath::ExplicitFailureRequest,
        context.diagnostic_budget,
    ) else {
        return (Vec::new(), None, None);
    };
    let repair_proposals = rewrite_repair_proposal_strings(&rewrite);
    let subset_kind = map_unification_subset_kind(rewrite.subset_kind);
    let constraints = rewrite
        .sites
        .iter()
        .map(|site| MachineDiagnosticConstraintSummary {
            constraint_id: site.id.wire(),
            kind: site.kind.as_str().to_owned(),
            phase: MachineApiDiagnosticPhase::TacticExecution,
            lhs_hash: site.expected_hash,
            rhs_hash: site.actual_hash,
            path: site.path.clone(),
            expected_summary: hash_term_summary(site.expected_hash),
            actual_summary: hash_term_summary(site.actual_hash),
            child_constraint_ids: Vec::new(),
            subset_kind,
            attributes: rewrite_constraint_attributes(&rewrite, site),
        })
        .collect();
    let pretty_payload = if repair_proposals.is_empty() {
        None
    } else {
        Some(MachineDiagnosticPrettyPayload {
            message: None,
            pretty_terms: Vec::new(),
            repair_proposals,
        })
    };
    (constraints, Some(rewrite.budget_report), pretty_payload)
}

fn universe_constraint_attributes(
    universe: &UniverseDiagnostic,
    constraint: &UniverseConstraintDiagnostic,
) -> Vec<MachineDiagnosticAttribute> {
    let mut attributes = vec![
        MachineDiagnosticAttribute {
            key: "complete_graph".to_owned(),
            value: universe.complete_graph.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "core_kind".to_owned(),
            value: universe.core_kind.as_str().to_owned(),
        },
        MachineDiagnosticAttribute {
            key: "lhs_level".to_owned(),
            value: npa_tactic::universe_level_diagnostic_wire(&constraint.lhs),
        },
        MachineDiagnosticAttribute {
            key: "relation".to_owned(),
            value: universe_constraint_relation_wire(constraint.relation).to_owned(),
        },
        MachineDiagnosticAttribute {
            key: "rhs_level".to_owned(),
            value: npa_tactic::universe_level_diagnostic_wire(&constraint.rhs),
        },
    ];
    if !constraint.universe_params.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "universe_params".to_owned(),
            value: constraint.universe_params.join(","),
        });
    }
    if !constraint.path.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "universe_source_path".to_owned(),
            value: constraint.path.join("/"),
        });
    }
    if !constraint.universe_metas.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "universe_metas".to_owned(),
            value: constraint.universe_metas.join(","),
        });
    }
    if !universe.unresolved_metas.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "unresolved_metas".to_owned(),
            value: universe.unresolved_metas.join(","),
        });
    }
    if !universe.candidate_instantiations.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "candidate_instantiations".to_owned(),
            value: universe_candidate_instantiation_wire(&universe.candidate_instantiations),
        });
    }
    if !universe.repair_operators.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "repair_operators".to_owned(),
            value: universe
                .repair_operators
                .iter()
                .map(|operator| operator.as_str())
                .collect::<Vec<_>>()
                .join(","),
        });
    }
    attributes.sort();
    attributes
}

fn api_safe_universe_path(path: &[String]) -> Vec<String> {
    path.iter()
        .filter_map(|step| {
            if let Some(index) = step
                .strip_prefix("UniverseArg(")
                .and_then(|raw| raw.strip_suffix(')'))
            {
                Some(format!("AppArgument({index})"))
            } else if step.starts_with("UniverseConstraint(") {
                None
            } else {
                Some(step.clone())
            }
        })
        .collect()
}

fn universe_repair_proposal_strings(universe: &UniverseDiagnostic) -> Vec<String> {
    let mut proposals = universe
        .repair_operators
        .iter()
        .map(|operator| operator.as_str())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if !universe.candidate_instantiations.is_empty() {
        proposals.push("instantiate_universe".to_owned());
    }
    proposals.sort();
    proposals.dedup();
    proposals
}

fn universe_candidate_instantiation_wire(candidates: &[UniverseInstantiationCandidate]) -> String {
    candidates
        .iter()
        .map(|candidate| {
            let status = if candidate.valid { "valid" } else { "invalid" };
            let rejection = candidate
                .rejection_kind
                .map(|kind| kind.as_str())
                .unwrap_or("none");
            format!(
                "{}={}:{}:{}",
                candidate.param,
                npa_tactic::universe_level_diagnostic_wire(&candidate.level),
                status,
                rejection
            )
        })
        .collect::<Vec<_>>()
        .join(";")
}

fn universe_constraint_relation_wire(
    relation: npa_kernel::UniverseConstraintRelation,
) -> &'static str {
    match relation {
        npa_kernel::UniverseConstraintRelation::Le => "le",
        npa_kernel::UniverseConstraintRelation::Eq => "eq",
    }
}

fn rewrite_constraint_attributes(
    rewrite: &RewriteDiagnostic,
    site: &RewriteDiagnosticSite,
) -> Vec<MachineDiagnosticAttribute> {
    let mut attributes = vec![
        MachineDiagnosticAttribute {
            key: "backward_matches_goal".to_owned(),
            value: rewrite.backward_matches_goal.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "backward_matches_hypothesis".to_owned(),
            value: rewrite.backward_matches_hypothesis.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "backward_valid".to_owned(),
            value: rewrite.backward_valid.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "complete_scan".to_owned(),
            value: rewrite.complete_scan.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "congruence_depth".to_owned(),
            value: site.congruence_depth.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "direction".to_owned(),
            value: site.direction.as_str().to_owned(),
        },
        MachineDiagnosticAttribute {
            key: "forward_matches_goal".to_owned(),
            value: rewrite.forward_matches_goal.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "forward_matches_hypothesis".to_owned(),
            value: rewrite.forward_matches_hypothesis.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "forward_valid".to_owned(),
            value: rewrite.forward_valid.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "matched_side".to_owned(),
            value: site.matched_side.as_str().to_owned(),
        },
        MachineDiagnosticAttribute {
            key: "rejected_by_budget_or_progress".to_owned(),
            value: rewrite.rejected_by_budget_or_progress.to_string(),
        },
        MachineDiagnosticAttribute {
            key: "replacement_side".to_owned(),
            value: site.replacement_side.as_str().to_owned(),
        },
        MachineDiagnosticAttribute {
            key: "target_kind".to_owned(),
            value: site.target_kind.as_str().to_owned(),
        },
    ];
    if let Some(local_name) = &site.local_name {
        attributes.push(MachineDiagnosticAttribute {
            key: "local_name".to_owned(),
            value: local_name.clone(),
        });
    }
    if let Some(reason) = rewrite.no_progress_reason {
        attributes.push(MachineDiagnosticAttribute {
            key: "no_progress_reason".to_owned(),
            value: reason.as_str().to_owned(),
        });
    }
    if let Some(index) = site.occurrence_index {
        attributes.push(MachineDiagnosticAttribute {
            key: "occurrence_index".to_owned(),
            value: index.to_string(),
        });
    }
    if !site.repair_operators.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "repair_operators".to_owned(),
            value: site
                .repair_operators
                .iter()
                .map(|operator| operator.as_str())
                .collect::<Vec<_>>()
                .join(","),
        });
    }
    if !site.required_unfoldings.is_empty() {
        attributes.push(MachineDiagnosticAttribute {
            key: "required_unfoldings".to_owned(),
            value: site.required_unfoldings.join(","),
        });
    }
    attributes.sort();
    attributes
}

fn rewrite_repair_proposal_strings(rewrite: &RewriteDiagnostic) -> Vec<String> {
    let mut proposals = rewrite
        .sites
        .iter()
        .flat_map(|site| {
            site.repair_operators
                .iter()
                .map(|operator| operator.as_str())
        })
        .map(str::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    proposals.sort();
    proposals
}

fn hash_term_summary(hash: Option<Hash>) -> Option<MachineDiagnosticTermSummary> {
    hash.map(|hash| MachineDiagnosticTermSummary {
        head_symbol: None,
        structural_hash: Some(hash),
        node_count: None,
        attributes: Vec::new(),
    })
}

fn map_unification_constraint_phase(
    phase: UnificationDiagnosticPhase,
) -> MachineApiDiagnosticPhase {
    match phase {
        UnificationDiagnosticPhase::MachineTermElaboration => {
            MachineApiDiagnosticPhase::MachineTermCheck
        }
        UnificationDiagnosticPhase::TacticApply
        | UnificationDiagnosticPhase::TacticExact
        | UnificationDiagnosticPhase::TacticRefineLike
        | UnificationDiagnosticPhase::TacticChange => MachineApiDiagnosticPhase::TacticExecution,
        UnificationDiagnosticPhase::KernelCheck => MachineApiDiagnosticPhase::KernelCheck,
    }
}

fn map_unification_subset_kind(
    kind: UnificationConflictSubsetKind,
) -> MachineDiagnosticConflictSubsetKind {
    match kind {
        UnificationConflictSubsetKind::Minimal => MachineDiagnosticConflictSubsetKind::Minimal,
        UnificationConflictSubsetKind::Reduced => MachineDiagnosticConflictSubsetKind::Reduced,
        UnificationConflictSubsetKind::Truncated => MachineDiagnosticConflictSubsetKind::Truncated,
    }
}

fn map_human_diagnostic_phase(
    phase: npa_frontend::HumanDiagnosticPhase,
) -> MachineApiDiagnosticPhase {
    use npa_frontend::HumanDiagnosticPhase as Human;

    match phase {
        Human::Parser => MachineApiDiagnosticPhase::MachineTermParse,
        Human::Resolver | Human::Elaborator => MachineApiDiagnosticPhase::MachineTermCheck,
        Human::TacticParse | Human::TacticValidation => {
            MachineApiDiagnosticPhase::CandidateValidation
        }
        Human::TacticExecution | Human::TacticUnresolvedGoal => {
            MachineApiDiagnosticPhase::TacticExecution
        }
        Human::KernelHandoff => MachineApiDiagnosticPhase::KernelCheck,
        Human::CertificateHandoff => MachineApiDiagnosticPhase::CertificateVerify,
    }
}

fn map_human_diagnostic_kind(kind: &npa_frontend::HumanDiagnosticKind) -> MachineApiErrorKind {
    use npa_frontend::HumanDiagnosticKind as Human;
    use MachineApiErrorKind as Api;

    match kind {
        Human::ParseError => Api::MachineTermParseError,
        Human::UnknownIdentifier
        | Human::AmbiguousName
        | Human::AmbiguousConstructor
        | Human::UnknownNamespace
        | Human::NamespaceMismatch => Api::UnknownName,
        Human::UnsupportedTactic => Api::UnsupportedTactic,
        Human::TypeclassBudgetExceeded => Api::BudgetExceeded,
        Human::ExpectedFunctionType => Api::ExpectedPiType,
        Human::NoGoalsButTacticRemaining | Human::UnresolvedGoal => Api::InvalidMachineProofState,
        Human::KernelRejected => Api::VerifyFailed,
        Human::TypeMismatch
        | Human::NotImplemented
        | Human::ImportAfterItem
        | Human::UnsupportedSyntax
        | Human::ImportResolutionError
        | Human::MissingVerifiedImport
        | Human::DuplicateDeclaration
        | Human::ForwardReference
        | Human::NotationConflict
        | Human::AmbiguousNotation
        | Human::TooManyNotationCandidates
        | Human::TypeclassNoSolution
        | Human::TypeclassAmbiguous
        | Human::UnsupportedEquationGuard
        | Human::UnsupportedViewPattern
        | Human::EquationCompilerDisabled
        | Human::NonExhaustivePatterns
        | Human::RedundantEquation
        | Human::ImpossibleBranchNotProvable
        | Human::RecursiveCallNotDecreasing
        | Human::MutualCycleWithoutDecrease
        | Human::TerminationMeasureNotNat
        | Human::MeasureDecreaseProofMissing
        | Human::UnsolvedImplicit
        | Human::UnsolvedMeta
        | Human::UnsolvedUniverseMeta
        | Human::UnsolvedHole
        | Human::NamedHoleContextMismatch
        | Human::OccursCheckFailed
        | Human::ExpectedSort
        | Human::MachineElaborationError => Api::MachineTermElaborationError,
    }
}

fn encode_tree_to(
    out: &mut Vec<u8>,
    tree: &MachineDiagnosticTree,
    depth: usize,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    validate_tree_shape(tree, depth)?;
    tree_encode_string(out, "tag", MACHINE_DIAGNOSTIC_TREE_HASH_TAG)?;
    tree_encode_string(out, "kind", tree.kind.as_str())?;
    tree_encode_string(out, "phase", tree.phase.as_str())?;
    tree_encode_string(out, "profile", tree.profile.as_str())?;
    tree_encode_option_goal_id(out, tree.goal_id);
    tree_encode_option_hash(out, tree.candidate_hash.as_ref());
    tree_encode_option_hash(out, tree.deterministic_budget_hash.as_ref());
    tree_encode_option_hash(out, tree.state_fingerprint.as_ref());
    tree_encode_string_list(out, "expression_path", &tree.expression_path)?;
    tree_encode_option_summary(out, tree.expected_summary.as_ref())?;
    tree_encode_option_summary(out, tree.actual_summary.as_ref())?;
    tree_encode_constraints(out, &tree.related_constraints)?;
    tree_encode_option_hash(out, tree.parent_diagnostic_hash.as_ref());
    tree_encode_option_budget_report(out, tree.budget_report.as_ref());
    let children = sorted_child_refs(&tree.children)?;
    tree_encode_u32(out, tree_checked_u32_len("children", children.len())?);
    for (_child_hash, child) in children {
        encode_tree_to(out, child, depth + 1)?;
    }
    out.push(0x00);
    Ok(())
}

fn validate_tree_shape(
    tree: &MachineDiagnosticTree,
    depth: usize,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    if depth > MACHINE_DIAGNOSTIC_TREE_MAX_DEPTH {
        return Err(MachineDiagnosticTreeCanonicalizationError::DepthExceeded {
            max_depth: MACHINE_DIAGNOSTIC_TREE_MAX_DEPTH,
        });
    }
    if tree.children.len() > MACHINE_DIAGNOSTIC_TREE_MAX_CHILDREN {
        return Err(
            MachineDiagnosticTreeCanonicalizationError::TooManyChildren {
                len: tree.children.len(),
                max: MACHINE_DIAGNOSTIC_TREE_MAX_CHILDREN,
            },
        );
    }
    if tree.expression_path.len() > MACHINE_DIAGNOSTIC_TREE_MAX_PATH_STEPS {
        return Err(
            MachineDiagnosticTreeCanonicalizationError::TooManyExpressionPathSteps {
                len: tree.expression_path.len(),
                max: MACHINE_DIAGNOSTIC_TREE_MAX_PATH_STEPS,
            },
        );
    }
    validate_diagnostic_expr_path("expression_path", &tree.expression_path)?;
    if tree.related_constraints.len() > MACHINE_DIAGNOSTIC_TREE_MAX_RELATED_CONSTRAINTS {
        return Err(
            MachineDiagnosticTreeCanonicalizationError::TooManyRelatedConstraints {
                len: tree.related_constraints.len(),
                max: MACHINE_DIAGNOSTIC_TREE_MAX_RELATED_CONSTRAINTS,
            },
        );
    }
    for constraint in &tree.related_constraints {
        validate_diagnostic_expr_path("related_constraints.path", &constraint.path)?;
        validate_attributes(&constraint.attributes)?;
        if let Some(summary) = &constraint.expected_summary {
            validate_attributes(&summary.attributes)?;
        }
        if let Some(summary) = &constraint.actual_summary {
            validate_attributes(&summary.attributes)?;
        }
    }
    if tree.profile == DiagnosticProfile::Off
        && (!tree.expression_path.is_empty()
            || tree.expected_summary.is_some()
            || tree.actual_summary.is_some()
            || !tree.related_constraints.is_empty()
            || tree.budget_report.is_some()
            || !tree.children.is_empty()
            || tree.pretty_payload.is_some())
    {
        return Err(MachineDiagnosticTreeCanonicalizationError::OffProfileHasRichPayload);
    }
    if let Some(summary) = &tree.expected_summary {
        validate_attributes(&summary.attributes)?;
    }
    if let Some(summary) = &tree.actual_summary {
        validate_attributes(&summary.attributes)?;
    }
    let _ = sorted_constraint_refs(&tree.related_constraints)?;
    let _ = sorted_child_refs(&tree.children)?;
    Ok(())
}

fn validate_diagnostic_expr_path(
    field: &'static str,
    path: &[String],
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    ExprPath::parse_wire_segments(path).map_err(|_| {
        MachineDiagnosticTreeCanonicalizationError::InvalidExpressionPath {
            step: format!("{field}:{}", invalid_expr_path_step(path)),
        }
    })?;
    Ok(())
}

fn invalid_expr_path_step(path: &[String]) -> String {
    path.iter()
        .find(|step| ExprPathStep::parse(step).is_err())
        .cloned()
        .unwrap_or_else(|| "<too-many-steps>".to_owned())
}

fn sorted_constraint_refs(
    constraints: &[MachineDiagnosticConstraintSummary],
) -> Result<Vec<ConstraintRefSortEntry<'_>>, MachineDiagnosticTreeCanonicalizationError> {
    let mut keyed = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        let mut encoded = Vec::new();
        tree_encode_constraint(&mut encoded, constraint)?;
        keyed.push((encoded, constraint_sort_key(constraint), constraint));
    }
    keyed.sort_by(
        |(left_encoded, left_key, _), (right_encoded, right_key, _)| {
            left_key
                .cmp(right_key)
                .then_with(|| left_encoded.cmp(right_encoded))
        },
    );
    for window in keyed.windows(2) {
        if window[0].0 == window[1].0 {
            return Err(MachineDiagnosticTreeCanonicalizationError::DuplicateRelatedConstraint);
        }
    }
    Ok(keyed)
}

fn sort_constraints_owned(
    constraints: Vec<MachineDiagnosticConstraintSummary>,
) -> Result<Vec<MachineDiagnosticConstraintSummary>, MachineDiagnosticTreeCanonicalizationError> {
    let mut keyed = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        let mut encoded = Vec::new();
        tree_encode_constraint(&mut encoded, &constraint)?;
        keyed.push((encoded, constraint_sort_key(&constraint), constraint));
    }
    keyed.sort_by(
        |(left_encoded, left_key, _), (right_encoded, right_key, _)| {
            left_key
                .cmp(right_key)
                .then_with(|| left_encoded.cmp(right_encoded))
        },
    );
    for window in keyed.windows(2) {
        if window[0].0 == window[1].0 {
            return Err(MachineDiagnosticTreeCanonicalizationError::DuplicateRelatedConstraint);
        }
    }
    Ok(keyed
        .into_iter()
        .map(|(_encoded, _key, constraint)| constraint)
        .collect())
}

type ConstraintRefSortEntry<'a> = (
    Vec<u8>,
    ConstraintSortKey,
    &'a MachineDiagnosticConstraintSummary,
);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ConstraintSortKey {
    constraint_id: String,
    path: Vec<String>,
    kind: String,
}

fn constraint_sort_key(constraint: &MachineDiagnosticConstraintSummary) -> ConstraintSortKey {
    ConstraintSortKey {
        constraint_id: constraint.constraint_id.clone(),
        path: constraint.path.clone(),
        kind: constraint.kind.clone(),
    }
}

fn sorted_child_refs(
    children: &[MachineDiagnosticTree],
) -> Result<Vec<(Hash, &MachineDiagnosticTree)>, MachineDiagnosticTreeCanonicalizationError> {
    let mut keyed = Vec::with_capacity(children.len());
    for child in children {
        keyed.push((machine_diagnostic_tree_hash(child)?, child));
    }
    keyed.sort_by_key(|(hash, _)| *hash);
    for window in keyed.windows(2) {
        if window[0].0 == window[1].0 {
            return Err(
                MachineDiagnosticTreeCanonicalizationError::DuplicateChildDiagnosticHash {
                    hash: window[0].0,
                },
            );
        }
    }
    Ok(keyed)
}

fn sort_children_owned(
    children: Vec<MachineDiagnosticTree>,
) -> Result<Vec<MachineDiagnosticTree>, MachineDiagnosticTreeCanonicalizationError> {
    let mut keyed = Vec::with_capacity(children.len());
    for child in children {
        keyed.push((machine_diagnostic_tree_hash(&child)?, child));
    }
    keyed.sort_by_key(|(hash, _)| *hash);
    for window in keyed.windows(2) {
        if window[0].0 == window[1].0 {
            return Err(
                MachineDiagnosticTreeCanonicalizationError::DuplicateChildDiagnosticHash {
                    hash: window[0].0,
                },
            );
        }
    }
    Ok(keyed.into_iter().map(|(_hash, child)| child).collect())
}

fn validate_attributes(
    attributes: &[MachineDiagnosticAttribute],
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    let mut previous = None;
    let mut seen = BTreeSet::new();
    for attribute in attributes {
        if !seen.insert(attribute.key.clone()) {
            return Err(
                MachineDiagnosticTreeCanonicalizationError::DuplicateAttribute {
                    key: attribute.key.clone(),
                },
            );
        }
        if previous.is_some_and(|previous: &String| previous > &attribute.key) {
            return Err(MachineDiagnosticTreeCanonicalizationError::NonCanonicalAttributeOrder);
        }
        previous = Some(&attribute.key);
    }
    Ok(())
}

fn tree_encode_option_summary(
    out: &mut Vec<u8>,
    value: Option<&MachineDiagnosticTermSummary>,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    match value {
        Some(summary) => {
            out.push(0x01);
            tree_encode_option_string(out, "head_symbol", summary.head_symbol.as_deref())?;
            tree_encode_option_hash(out, summary.structural_hash.as_ref());
            tree_encode_option_u64(out, summary.node_count);
            tree_encode_u32(
                out,
                tree_checked_u32_len("summary.attributes", summary.attributes.len())?,
            );
            for attribute in &summary.attributes {
                tree_encode_string(out, "summary.attribute.key", &attribute.key)?;
                tree_encode_string(out, "summary.attribute.value", &attribute.value)?;
            }
            Ok(())
        }
        None => {
            out.push(0x00);
            Ok(())
        }
    }
}

fn tree_encode_constraints(
    out: &mut Vec<u8>,
    constraints: &[MachineDiagnosticConstraintSummary],
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    let constraints = sorted_constraint_refs(constraints)?;
    tree_encode_u32(
        out,
        tree_checked_u32_len("related_constraints", constraints.len())?,
    );
    for (_encoded, _key, constraint) in constraints {
        tree_encode_constraint(out, constraint)?;
    }
    Ok(())
}

fn tree_encode_constraint(
    out: &mut Vec<u8>,
    constraint: &MachineDiagnosticConstraintSummary,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    validate_diagnostic_expr_path("related_constraints.path", &constraint.path)?;
    tree_encode_string(
        out,
        "related_constraints.constraint_id",
        &constraint.constraint_id,
    )?;
    tree_encode_string(out, "related_constraints.kind", &constraint.kind)?;
    tree_encode_string(out, "related_constraints.phase", constraint.phase.as_str())?;
    tree_encode_option_hash(out, constraint.lhs_hash.as_ref());
    tree_encode_option_hash(out, constraint.rhs_hash.as_ref());
    tree_encode_string_list(out, "related_constraints.path", &constraint.path)?;
    tree_encode_option_summary(out, constraint.expected_summary.as_ref())?;
    tree_encode_option_summary(out, constraint.actual_summary.as_ref())?;
    tree_encode_string_list(
        out,
        "related_constraints.child_constraint_ids",
        &constraint.child_constraint_ids,
    )?;
    tree_encode_string(
        out,
        "related_constraints.subset_kind",
        constraint.subset_kind.as_str(),
    )?;
    tree_encode_u32(
        out,
        tree_checked_u32_len(
            "related_constraints.attributes",
            constraint.attributes.len(),
        )?,
    );
    for attribute in &constraint.attributes {
        tree_encode_string(out, "related_constraints.attribute.key", &attribute.key)?;
        tree_encode_string(out, "related_constraints.attribute.value", &attribute.value)?;
    }
    Ok(())
}

fn tree_encode_option_budget_report(out: &mut Vec<u8>, report: Option<&DiagnosticBudgetReport>) {
    match report {
        Some(report) => {
            out.push(0x01);
            tree_encode_budget_counter(out, report.graph_nodes);
            tree_encode_budget_counter(out, report.expression_paths);
            tree_encode_budget_counter(out, report.rewrite_site_scans);
            tree_encode_budget_counter(out, report.pretty_term_bytes);
            tree_encode_budget_counter(out, report.repair_proposals);
            tree_encode_budget_counter(out, report.diagnostic_steps);
        }
        None => out.push(0x00),
    }
}

fn tree_encode_budget_counter(out: &mut Vec<u8>, counter: DiagnosticBudgetCounterReport) {
    tree_encode_u64(out, counter.used);
    tree_encode_u64(out, counter.limit);
    out.push(u8::from(counter.truncated));
}

fn tree_encode_string_list(
    out: &mut Vec<u8>,
    field: &'static str,
    values: &[String],
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    tree_encode_u32(out, tree_checked_u32_len(field, values.len())?);
    for value in values {
        tree_encode_string(out, field, value)?;
    }
    Ok(())
}

fn tree_encode_option_goal_id(out: &mut Vec<u8>, value: Option<GoalId>) {
    match value {
        Some(goal_id) => {
            out.push(0x01);
            out.extend(goal_id_canonical_bytes(goal_id));
        }
        None => out.push(0x00),
    }
}

fn tree_encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
}

fn tree_encode_option_string(
    out: &mut Vec<u8>,
    field: &'static str,
    value: Option<&str>,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    match value {
        Some(value) => {
            out.push(0x01);
            tree_encode_string(out, field, value)
        }
        None => {
            out.push(0x00);
            Ok(())
        }
    }
}

fn tree_encode_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            out.push(0x01);
            tree_encode_u64(out, value);
        }
        None => out.push(0x00),
    }
}

fn tree_encode_string(
    out: &mut Vec<u8>,
    field: &'static str,
    value: &str,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    tree_encode_u32(out, tree_checked_u32_len(field, value.len())?);
    out.extend(value.as_bytes());
    Ok(())
}

fn tree_checked_u32_len(
    field: &'static str,
    len: usize,
) -> Result<u32, MachineDiagnosticTreeCanonicalizationError> {
    u32::try_from(len)
        .map_err(|_| MachineDiagnosticTreeCanonicalizationError::LengthExceeded { field, len })
}

fn tree_encode_u32(out: &mut Vec<u8>, value: u32) {
    tree_encode_u64(out, u64::from(value));
}

fn tree_encode_u64(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn parse_diagnostic_tree_value(
    value: &JsonValue<'_>,
    depth: usize,
) -> Result<MachineDiagnosticTree, MachineDiagnosticTreeParseError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            DIAGNOSTIC_TREE_FIELDS,
        ),
        &JsonPath::root(),
    )
    .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;

    let schema = required_string(object.field("schema").expect("schema validated"), "schema")?;
    if schema != MACHINE_DIAGNOSTIC_TREE_SCHEMA {
        return Err(MachineDiagnosticTreeParseError::UnsupportedSchema {
            actual: schema.to_owned(),
        });
    }
    let declared_hash = required_hash(
        object
            .field("diagnostic_hash")
            .expect("diagnostic_hash validated"),
        "diagnostic_hash",
    )?;
    let tree = MachineDiagnosticTree {
        kind: parse_error_kind(required_string(
            object.field("kind").expect("kind validated"),
            "kind",
        )?)?,
        phase: parse_diagnostic_phase(required_string(
            object.field("phase").expect("phase validated"),
            "phase",
        )?)?,
        profile: parse_diagnostic_profile(required_string(
            object.field("profile").expect("profile validated"),
            "profile",
        )?)?,
        goal_id: optional_goal_id(
            object.field("goal_id").expect("goal_id validated"),
            "goal_id",
        )?,
        candidate_hash: optional_hash(
            object
                .field("candidate_hash")
                .expect("candidate_hash validated"),
            "candidate_hash",
        )?,
        deterministic_budget_hash: optional_hash(
            object
                .field("deterministic_budget_hash")
                .expect("deterministic_budget_hash validated"),
            "deterministic_budget_hash",
        )?,
        state_fingerprint: optional_hash(
            object
                .field("state_fingerprint")
                .expect("state_fingerprint validated"),
            "state_fingerprint",
        )?,
        expression_path: string_array(
            object
                .field("expression_path")
                .expect("expression_path validated"),
            "expression_path",
        )?,
        expected_summary: optional_summary(
            object
                .field("expected_summary")
                .expect("expected_summary validated"),
        )?,
        actual_summary: optional_summary(
            object
                .field("actual_summary")
                .expect("actual_summary validated"),
        )?,
        related_constraints: related_constraints(
            object
                .field("related_constraints")
                .expect("related_constraints validated"),
        )?,
        parent_diagnostic_hash: optional_hash(
            object
                .field("parent_diagnostic_hash")
                .expect("parent_diagnostic_hash validated"),
            "parent_diagnostic_hash",
        )?,
        budget_report: optional_budget_report(
            object
                .field("budget_report")
                .expect("budget_report validated"),
        )?,
        children: diagnostic_children(
            object.field("children").expect("children validated"),
            depth,
        )?,
        source_message: optional_string(
            object
                .field("source_message")
                .expect("source_message validated"),
            "source_message",
        )?,
        pretty_payload: optional_pretty_payload(
            object
                .field("pretty_payload")
                .expect("pretty_payload validated"),
        )?,
    };
    let actual_hash =
        machine_diagnostic_tree_hash(&tree).map_err(MachineDiagnosticTreeParseError::Canonical)?;
    if declared_hash != actual_hash {
        return Err(MachineDiagnosticTreeParseError::DiagnosticHashMismatch {
            expected: declared_hash,
            actual: actual_hash,
        });
    }
    Ok(tree)
}

fn required_string<'a>(
    value: &'a JsonValue<'_>,
    field: &'static str,
) -> Result<&'a str, MachineDiagnosticTreeParseError> {
    value
        .string_value()
        .ok_or_else(|| MachineDiagnosticTreeParseError::UnsupportedEnum {
            field,
            value: value.raw_slice().to_owned(),
        })
}

fn optional_string(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Option<String>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    Ok(Some(required_string(value, field)?.to_owned()))
}

fn required_hash(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Hash, MachineDiagnosticTreeParseError> {
    let raw = required_string(value, field)?;
    parse_hash_string(raw).map_err(|error| MachineDiagnosticTreeParseError::InvalidHash {
        field,
        error: error.kind,
    })
}

fn optional_hash(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Option<Hash>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    required_hash(value, field).map(Some)
}

fn optional_goal_id(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Option<GoalId>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let raw = required_string(value, field)?;
    parse_goal_id_wire(raw).map(Some).map_err(|error| {
        MachineDiagnosticTreeParseError::InvalidGoalId {
            field,
            error: error.kind,
        }
    })
}

fn parse_error_kind(value: &str) -> Result<MachineApiErrorKind, MachineDiagnosticTreeParseError> {
    let kind = match value {
        "unknown_session" => MachineApiErrorKind::UnknownSession,
        "unknown_snapshot" => MachineApiErrorKind::UnknownSnapshot,
        "state_fingerprint_mismatch" => MachineApiErrorKind::StateFingerprintMismatch,
        "session_root_hash_mismatch" => MachineApiErrorKind::SessionRootHashMismatch,
        "invalid_verified_import" => MachineApiErrorKind::InvalidVerifiedImport,
        "invalid_checked_current_decl" => MachineApiErrorKind::InvalidCheckedCurrentDecl,
        "invalid_machine_api_options" => MachineApiErrorKind::InvalidMachineApiOptions,
        "invalid_machine_proof_state" => MachineApiErrorKind::InvalidMachineProofState,
        "invalid_session_request" => MachineApiErrorKind::InvalidSessionRequest,
        "invalid_snapshot_request" => MachineApiErrorKind::InvalidSnapshotRequest,
        "invalid_tactic_run_request" => MachineApiErrorKind::InvalidTacticRunRequest,
        "invalid_theorem_index" => MachineApiErrorKind::InvalidTheoremIndex,
        "invalid_theorem_query" => MachineApiErrorKind::InvalidTheoremQuery,
        "theorem_index_fingerprint_mismatch" => {
            MachineApiErrorKind::TheoremIndexFingerprintMismatch
        }
        "invalid_prompt_payload_request" => MachineApiErrorKind::InvalidPromptPayloadRequest,
        "invalid_batch_policy" => MachineApiErrorKind::InvalidBatchPolicy,
        "invalid_scheduler_limits" => MachineApiErrorKind::InvalidSchedulerLimits,
        "invalid_replay_plan" => MachineApiErrorKind::InvalidReplayPlan,
        "invalid_verify_request" => MachineApiErrorKind::InvalidVerifyRequest,
        "replay_hash_mismatch" => MachineApiErrorKind::ReplayHashMismatch,
        "disallowed_axiom" => MachineApiErrorKind::DisallowedAxiom,
        "goal_not_open" => MachineApiErrorKind::GoalNotOpen,
        "invalid_candidate" => MachineApiErrorKind::InvalidCandidate,
        "invalid_budget" => MachineApiErrorKind::InvalidBudget,
        "unsupported_tactic" => MachineApiErrorKind::UnsupportedTactic,
        "machine_term_parse_error" => MachineApiErrorKind::MachineTermParseError,
        "machine_term_elaboration_error" => MachineApiErrorKind::MachineTermElaborationError,
        "unknown_name" => MachineApiErrorKind::UnknownName,
        "implicit_argument_required" => MachineApiErrorKind::ImplicitArgumentRequired,
        "type_mismatch" => MachineApiErrorKind::TypeMismatch,
        "expected_pi_type" => MachineApiErrorKind::ExpectedPiType,
        "rewrite_rule_invalid" => MachineApiErrorKind::RewriteRuleInvalid,
        "simp_no_progress" => MachineApiErrorKind::SimpNoProgress,
        "induction_target_not_nat" => MachineApiErrorKind::InductionTargetNotNat,
        "budget_exceeded" => MachineApiErrorKind::BudgetExceeded,
        "too_many_goals" => MachineApiErrorKind::TooManyGoals,
        "too_large_term" => MachineApiErrorKind::TooLargeTerm,
        "verify_failed" => MachineApiErrorKind::VerifyFailed,
        _ => {
            return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
                field: "kind",
                value: value.to_owned(),
            })
        }
    };
    Ok(kind)
}

fn parse_diagnostic_phase(
    value: &str,
) -> Result<crate::MachineApiDiagnosticPhase, MachineDiagnosticTreeParseError> {
    let phase = match value {
        "request_validation" => crate::MachineApiDiagnosticPhase::RequestValidation,
        "session_lookup" => crate::MachineApiDiagnosticPhase::SessionLookup,
        "session_create" => crate::MachineApiDiagnosticPhase::SessionCreate,
        "snapshot_lookup" => crate::MachineApiDiagnosticPhase::SnapshotLookup,
        "candidate_validation" => crate::MachineApiDiagnosticPhase::CandidateValidation,
        "machine_term_parse" => crate::MachineApiDiagnosticPhase::MachineTermParse,
        "machine_term_check" => crate::MachineApiDiagnosticPhase::MachineTermCheck,
        "tactic_execution" => crate::MachineApiDiagnosticPhase::TacticExecution,
        "theorem_search" => crate::MachineApiDiagnosticPhase::TheoremSearch,
        "prompt_payload" => crate::MachineApiDiagnosticPhase::PromptPayload,
        "replay_validation" => crate::MachineApiDiagnosticPhase::ReplayValidation,
        "replay_execution" => crate::MachineApiDiagnosticPhase::ReplayExecution,
        "kernel_check" => crate::MachineApiDiagnosticPhase::KernelCheck,
        "certificate_generation" => crate::MachineApiDiagnosticPhase::CertificateGeneration,
        "certificate_verify" => crate::MachineApiDiagnosticPhase::CertificateVerify,
        _ => {
            return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
                field: "phase",
                value: value.to_owned(),
            })
        }
    };
    Ok(phase)
}

fn parse_diagnostic_profile(
    value: &str,
) -> Result<DiagnosticProfile, MachineDiagnosticTreeParseError> {
    let profile = match value {
        "off" => DiagnosticProfile::Off,
        "basic" => DiagnosticProfile::Basic,
        "full" => DiagnosticProfile::Full,
        _ => {
            return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
                field: "profile",
                value: value.to_owned(),
            })
        }
    };
    Ok(profile)
}

fn parse_conflict_subset_kind(
    value: &str,
) -> Result<MachineDiagnosticConflictSubsetKind, MachineDiagnosticTreeParseError> {
    let kind = match value {
        "minimal" => MachineDiagnosticConflictSubsetKind::Minimal,
        "reduced" => MachineDiagnosticConflictSubsetKind::Reduced,
        "truncated" => MachineDiagnosticConflictSubsetKind::Truncated,
        _ => {
            return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
                field: "subset_kind",
                value: value.to_owned(),
            })
        }
    };
    Ok(kind)
}

fn string_array(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Vec<String>, MachineDiagnosticTreeParseError> {
    let Some(elements) = value.array_elements() else {
        return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
            field,
            value: value.raw_slice().to_owned(),
        });
    };
    elements
        .iter()
        .map(|element| required_string(element, field).map(str::to_owned))
        .collect()
}

fn optional_summary(
    value: &JsonValue<'_>,
) -> Result<Option<MachineDiagnosticTermSummary>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            TERM_SUMMARY_FIELDS,
        ),
        &JsonPath::root(),
    )
    .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;
    Ok(Some(MachineDiagnosticTermSummary {
        head_symbol: optional_string(
            object.field("head_symbol").expect("head_symbol validated"),
            "head_symbol",
        )?,
        structural_hash: optional_hash(
            object
                .field("structural_hash")
                .expect("structural_hash validated"),
            "structural_hash",
        )?,
        node_count: optional_u64(
            object.field("node_count").expect("node_count validated"),
            "node_count",
        )?,
        attributes: attributes_object(object.field("attributes").expect("attributes validated"))?,
    }))
}

fn attributes_object(
    value: &JsonValue<'_>,
) -> Result<Vec<MachineDiagnosticAttribute>, MachineDiagnosticTreeParseError> {
    let members = object_members_no_duplicates(value)?;
    let mut attributes = Vec::new();
    for member in members {
        let value = required_string(member.value(), "attributes")?;
        attributes.push(MachineDiagnosticAttribute {
            key: member.key().to_owned(),
            value: value.to_owned(),
        });
    }
    attributes.sort();
    Ok(attributes)
}

fn object_members_no_duplicates<'a, 'src>(
    value: &'a JsonValue<'src>,
) -> Result<&'a [crate::JsonMember<'src>], MachineDiagnosticTreeParseError> {
    let Some(members) = value.object_members() else {
        return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
            field: "attributes",
            value: value.raw_slice().to_owned(),
        });
    };
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineDiagnosticTreeParseError::Canonical(
                MachineDiagnosticTreeCanonicalizationError::DuplicateAttribute {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    Ok(members)
}

fn optional_u64(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<Option<u64>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    required_u64(value, field).map(Some)
}

fn required_u64(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<u64, MachineDiagnosticTreeParseError> {
    let Some(raw) = value.number_raw() else {
        return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
            field,
            value: value.raw_slice().to_owned(),
        });
    };
    parse_strict_u64_token(raw, u64::MAX).map_err(|error| {
        MachineDiagnosticTreeParseError::InvalidUnsignedInteger {
            field,
            raw: raw.to_owned(),
            error,
        }
    })
}

fn related_constraints(
    value: &JsonValue<'_>,
) -> Result<Vec<MachineDiagnosticConstraintSummary>, MachineDiagnosticTreeParseError> {
    let Some(elements) = value.array_elements() else {
        return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
            field: "related_constraints",
            value: value.raw_slice().to_owned(),
        });
    };
    let mut constraints = Vec::new();
    for element in elements {
        let object = validate_json_object(
            element,
            ObjectSchema::new(
                MachineApiErrorKind::InvalidPromptPayloadRequest,
                RELATED_CONSTRAINT_FIELDS,
            ),
            &JsonPath::root(),
        )
        .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;
        constraints.push(MachineDiagnosticConstraintSummary {
            constraint_id: required_string(
                object
                    .field("constraint_id")
                    .expect("constraint_id validated"),
                "constraint_id",
            )?
            .to_owned(),
            kind: required_string(object.field("kind").expect("kind validated"), "kind")?
                .to_owned(),
            phase: parse_diagnostic_phase(required_string(
                object.field("phase").expect("phase validated"),
                "phase",
            )?)?,
            lhs_hash: optional_hash(
                object.field("lhs_hash").expect("lhs_hash validated"),
                "lhs_hash",
            )?,
            rhs_hash: optional_hash(
                object.field("rhs_hash").expect("rhs_hash validated"),
                "rhs_hash",
            )?,
            path: string_array(object.field("path").expect("path validated"), "path")?,
            expected_summary: optional_summary(
                object
                    .field("expected_summary")
                    .expect("expected_summary validated"),
            )?,
            actual_summary: optional_summary(
                object
                    .field("actual_summary")
                    .expect("actual_summary validated"),
            )?,
            child_constraint_ids: string_array(
                object
                    .field("child_constraint_ids")
                    .expect("child_constraint_ids validated"),
                "child_constraint_ids",
            )?,
            subset_kind: parse_conflict_subset_kind(required_string(
                object.field("subset_kind").expect("subset_kind validated"),
                "subset_kind",
            )?)?,
            attributes: attributes_object(
                object.field("attributes").expect("attributes validated"),
            )?,
        });
    }
    sort_constraints_owned(constraints).map_err(MachineDiagnosticTreeParseError::Canonical)
}

fn optional_budget_report(
    value: &JsonValue<'_>,
) -> Result<Option<DiagnosticBudgetReport>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            BUDGET_REPORT_FIELDS,
        ),
        &JsonPath::root(),
    )
    .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;
    let report = DiagnosticBudgetReport {
        graph_nodes: budget_counter(
            object.field("graph_nodes").expect("graph_nodes validated"),
            "graph_nodes",
        )?,
        expression_paths: budget_counter(
            object
                .field("expression_paths")
                .expect("expression_paths validated"),
            "expression_paths",
        )?,
        rewrite_site_scans: budget_counter(
            object
                .field("rewrite_site_scans")
                .expect("rewrite_site_scans validated"),
            "rewrite_site_scans",
        )?,
        pretty_term_bytes: budget_counter(
            object
                .field("pretty_term_bytes")
                .expect("pretty_term_bytes validated"),
            "pretty_term_bytes",
        )?,
        repair_proposals: budget_counter(
            object
                .field("repair_proposals")
                .expect("repair_proposals validated"),
            "repair_proposals",
        )?,
        diagnostic_steps: budget_counter(
            object
                .field("diagnostic_steps")
                .expect("diagnostic_steps validated"),
            "diagnostic_steps",
        )?,
    };
    let truncated = object
        .field("truncated")
        .expect("truncated validated")
        .bool_value()
        .expect("truncated is boolean");
    if report.truncated() != truncated {
        return Err(MachineDiagnosticTreeParseError::BudgetReportMismatch);
    }
    Ok(Some(report))
}

fn budget_counter(
    value: &JsonValue<'_>,
    field: &'static str,
) -> Result<DiagnosticBudgetCounterReport, MachineDiagnosticTreeParseError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            BUDGET_COUNTER_FIELDS,
        ),
        &JsonPath::root(),
    )
    .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;
    let used = required_u64(object.field("used").expect("used validated"), "used")?;
    let limit = required_u64(object.field("limit").expect("limit validated"), "limit")?;
    let truncated = object
        .field("truncated")
        .expect("truncated validated")
        .bool_value()
        .expect("truncated is boolean");
    let counter = DiagnosticBudgetCounterReport::new(used, limit);
    if counter.truncated != truncated {
        return Err(MachineDiagnosticTreeParseError::BudgetCounterMismatch { field });
    }
    Ok(counter)
}

fn diagnostic_children(
    value: &JsonValue<'_>,
    depth: usize,
) -> Result<Vec<MachineDiagnosticTree>, MachineDiagnosticTreeParseError> {
    let Some(elements) = value.array_elements() else {
        return Err(MachineDiagnosticTreeParseError::UnsupportedEnum {
            field: "children",
            value: value.raw_slice().to_owned(),
        });
    };
    let children = elements
        .iter()
        .map(|element| parse_diagnostic_tree_value(element, depth + 1))
        .collect::<Result<Vec<_>, _>>()?;
    sort_children_owned(children).map_err(MachineDiagnosticTreeParseError::Canonical)
}

fn optional_pretty_payload(
    value: &JsonValue<'_>,
) -> Result<Option<MachineDiagnosticPrettyPayload>, MachineDiagnosticTreeParseError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidPromptPayloadRequest,
            PRETTY_PAYLOAD_FIELDS,
        ),
        &JsonPath::root(),
    )
    .map_err(|error| MachineDiagnosticTreeParseError::Shape(Box::new(error)))?;
    Ok(Some(MachineDiagnosticPrettyPayload {
        message: optional_string(
            object.field("message").expect("message validated"),
            "message",
        )?,
        pretty_terms: string_array(
            object
                .field("pretty_terms")
                .expect("pretty_terms validated"),
            "pretty_terms",
        )?,
        repair_proposals: string_array(
            object
                .field("repair_proposals")
                .expect("repair_proposals validated"),
            "repair_proposals",
        )?,
    }))
}

fn write_tree_json(
    out: &mut String,
    tree: &MachineDiagnosticTree,
    diagnostic_hash: Hash,
) -> Result<(), MachineDiagnosticTreeCanonicalizationError> {
    out.push('{');
    json_field(
        out,
        "schema",
        &json_string(MACHINE_DIAGNOSTIC_TREE_SCHEMA),
        true,
    );
    json_field(out, "diagnostic_hash", &json_hash(&diagnostic_hash), false);
    json_field(out, "kind", &json_string(tree.kind.as_str()), false);
    json_field(out, "phase", &json_string(tree.phase.as_str()), false);
    json_field(out, "profile", &json_string(tree.profile.as_str()), false);
    json_field(out, "goal_id", &json_goal_id_option(tree.goal_id), false);
    json_field(
        out,
        "candidate_hash",
        &json_hash_option(tree.candidate_hash.as_ref()),
        false,
    );
    json_field(
        out,
        "deterministic_budget_hash",
        &json_hash_option(tree.deterministic_budget_hash.as_ref()),
        false,
    );
    json_field(
        out,
        "state_fingerprint",
        &json_hash_option(tree.state_fingerprint.as_ref()),
        false,
    );
    json_field(
        out,
        "expression_path",
        &json_string_array(&tree.expression_path),
        false,
    );
    json_field(
        out,
        "expected_summary",
        &json_summary_option(tree.expected_summary.as_ref()),
        false,
    );
    json_field(
        out,
        "actual_summary",
        &json_summary_option(tree.actual_summary.as_ref()),
        false,
    );
    json_field(
        out,
        "related_constraints",
        &json_constraints(&tree.related_constraints)?,
        false,
    );
    json_field(
        out,
        "parent_diagnostic_hash",
        &json_hash_option(tree.parent_diagnostic_hash.as_ref()),
        false,
    );
    json_field(
        out,
        "budget_report",
        &json_budget_report_option(tree.budget_report.as_ref()),
        false,
    );
    json_field(out, "children", &json_children(&tree.children)?, false);
    json_field(
        out,
        "source_message",
        &json_string_option(tree.source_message.as_deref()),
        false,
    );
    json_field(
        out,
        "pretty_payload",
        &json_pretty_payload_option(tree.pretty_payload.as_ref()),
        false,
    );
    out.push('}');
    Ok(())
}

fn json_field(out: &mut String, key: &str, value: &str, first: bool) {
    if !first {
        out.push(',');
    }
    out.push_str(&json_string(key));
    out.push(':');
    out.push_str(value);
}

fn json_summary_option(value: Option<&MachineDiagnosticTermSummary>) -> String {
    let Some(value) = value else {
        return "null".to_owned();
    };
    format!(
        "{{\"head_symbol\":{},\"structural_hash\":{},\"node_count\":{},\"attributes\":{}}}",
        json_string_option(value.head_symbol.as_deref()),
        json_hash_option(value.structural_hash.as_ref()),
        value
            .node_count
            .map(|value| value.to_string())
            .unwrap_or_else(|| "null".to_owned()),
        json_attributes(&value.attributes)
    )
}

fn json_attributes(attributes: &[MachineDiagnosticAttribute]) -> String {
    let mut out = String::new();
    out.push('{');
    for (index, attribute) in attributes.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(&attribute.key));
        out.push(':');
        out.push_str(&json_string(&attribute.value));
    }
    out.push('}');
    out
}

fn json_constraints(
    constraints: &[MachineDiagnosticConstraintSummary],
) -> Result<String, MachineDiagnosticTreeCanonicalizationError> {
    let mut out = String::new();
    out.push('[');
    for (index, (_encoded, _key, constraint)) in
        sorted_constraint_refs(constraints)?.into_iter().enumerate()
    {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            "{{\"constraint_id\":{},\"kind\":{},\"phase\":{},\"lhs_hash\":{},\"rhs_hash\":{},\"path\":{},\"expected_summary\":{},\"actual_summary\":{},\"child_constraint_ids\":{},\"subset_kind\":{},\"attributes\":{}}}",
            json_string(&constraint.constraint_id),
            json_string(&constraint.kind),
            json_string(constraint.phase.as_str()),
            json_hash_option(constraint.lhs_hash.as_ref()),
            json_hash_option(constraint.rhs_hash.as_ref()),
            json_string_array(&constraint.path),
            json_summary_option(constraint.expected_summary.as_ref()),
            json_summary_option(constraint.actual_summary.as_ref()),
            json_string_array(&constraint.child_constraint_ids),
            json_string(constraint.subset_kind.as_str()),
            json_attributes(&constraint.attributes),
        ));
    }
    out.push(']');
    Ok(out)
}

fn json_budget_report_option(report: Option<&DiagnosticBudgetReport>) -> String {
    let Some(report) = report else {
        return "null".to_owned();
    };
    format!(
        "{{\"truncated\":{},\"graph_nodes\":{},\"expression_paths\":{},\"rewrite_site_scans\":{},\"pretty_term_bytes\":{},\"repair_proposals\":{},\"diagnostic_steps\":{}}}",
        report.truncated(),
        json_budget_counter(report.graph_nodes),
        json_budget_counter(report.expression_paths),
        json_budget_counter(report.rewrite_site_scans),
        json_budget_counter(report.pretty_term_bytes),
        json_budget_counter(report.repair_proposals),
        json_budget_counter(report.diagnostic_steps)
    )
}

fn json_budget_counter(counter: DiagnosticBudgetCounterReport) -> String {
    format!(
        "{{\"used\":{},\"limit\":{},\"truncated\":{}}}",
        counter.used, counter.limit, counter.truncated
    )
}

fn json_children(
    children: &[MachineDiagnosticTree],
) -> Result<String, MachineDiagnosticTreeCanonicalizationError> {
    let mut out = String::new();
    out.push('[');
    for (index, (child_hash, child)) in sorted_child_refs(children)?.into_iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write_tree_json(&mut out, child, child_hash)?;
    }
    out.push(']');
    Ok(out)
}

fn json_pretty_payload_option(value: Option<&MachineDiagnosticPrettyPayload>) -> String {
    let Some(value) = value else {
        return "null".to_owned();
    };
    format!(
        "{{\"message\":{},\"pretty_terms\":{},\"repair_proposals\":{}}}",
        json_string_option(value.message.as_deref()),
        json_string_array(&value.pretty_terms),
        json_string_array(&value.repair_proposals)
    )
}

fn json_goal_id_option(value: Option<GoalId>) -> String {
    match value {
        Some(value) => json_string(&format_goal_id_wire(value)),
        None => "null".to_owned(),
    }
}

fn json_hash(hash: &Hash) -> String {
    json_string(&format_hash_string(hash))
}

fn json_hash_option(hash: Option<&Hash>) -> String {
    match hash {
        Some(hash) => json_hash(hash),
        None => "null".to_owned(),
    }
}

fn json_string_option(value: Option<&str>) -> String {
    match value {
        Some(value) => json_string(value),
        None => "null".to_owned(),
    }
}

fn json_string_array(values: &[String]) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(value));
    }
    out.push(']');
    out
}

fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            ch if ch <= '\u{1f}' => {
                out.push_str(&format!("\\u{:04x}", ch as u32));
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineApiDiagnosticCanonicalizationError {
    RetryableDiagnosticUnsupported,
    LengthExceeded { field: &'static str, len: usize },
    NonCanonicalName { field: &'static str },
    MissingPrimaryAxiomRef,
    UnexpectedPrimaryAxiomRef,
    DisallowedAxiomPrimaryNameMismatch,
    IncompleteTypeMismatchHashes,
    UnexpectedExpectedActualHash { kind: MachineApiErrorKind },
    MissingGoalId { kind: MachineApiErrorKind },
    UnexpectedGoalId { kind: MachineApiErrorKind },
    MissingTacticKind { kind: MachineApiErrorKind },
    UnexpectedTacticKind { kind: MachineApiErrorKind },
    UnexpectedPrimaryName { kind: MachineApiErrorKind },
}

impl MachineApiDiagnosticProjection {
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, MachineApiDiagnosticCanonicalizationError> {
        machine_api_diagnostic_canonical_bytes(self)
    }

    pub fn diagnostic_hash(&self) -> Result<Hash, MachineApiDiagnosticCanonicalizationError> {
        machine_api_diagnostic_hash(self)
    }
}

pub fn machine_api_diagnostic_canonical_bytes(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<Vec<u8>, MachineApiDiagnosticCanonicalizationError> {
    validate_diagnostic(diagnostic)?;

    let mut out = Vec::new();
    encode_string(&mut out, "tag", API_DIAGNOSTIC_TAG)?;
    encode_string(&mut out, "kind", diagnostic.kind.as_str())?;
    encode_some_string(&mut out, "phase", diagnostic.phase.as_str())?;
    encode_option_goal_id(&mut out, diagnostic.goal_id);
    encode_option_tactic_kind(&mut out, diagnostic.tactic_kind)?;
    encode_option_name(&mut out, "primary_name", diagnostic.primary_name.as_ref())?;
    encode_option_axiom_ref(&mut out, diagnostic.primary_axiom_ref.as_ref());
    encode_option_hash(&mut out, diagnostic.expected_hash.as_ref());
    encode_option_hash(&mut out, diagnostic.actual_hash.as_ref());
    out.push(0x00);
    Ok(out)
}

pub fn machine_api_diagnostic_hash(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<Hash, MachineApiDiagnosticCanonicalizationError> {
    let canonical = machine_api_diagnostic_canonical_bytes(diagnostic)?;
    let digest = Sha256::digest(&canonical);
    let mut hash = [0; 32];
    hash.copy_from_slice(&digest);
    Ok(hash)
}

fn validate_diagnostic(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.retryable {
        return Err(MachineApiDiagnosticCanonicalizationError::RetryableDiagnosticUnsupported);
    }

    if let Some(name) = &diagnostic.primary_name {
        validate_name("primary_name", name)?;
    }

    match diagnostic.kind {
        MachineApiErrorKind::DisallowedAxiom => {
            let axiom_ref = diagnostic
                .primary_axiom_ref
                .as_ref()
                .ok_or(MachineApiDiagnosticCanonicalizationError::MissingPrimaryAxiomRef)?;
            validate_axiom_ref(axiom_ref)?;
            if diagnostic.primary_name.as_ref() != Some(axiom_ref_name(axiom_ref)) {
                return Err(
                    MachineApiDiagnosticCanonicalizationError::DisallowedAxiomPrimaryNameMismatch,
                );
            }
        }
        _ if diagnostic.primary_axiom_ref.is_some() => {
            return Err(MachineApiDiagnosticCanonicalizationError::UnexpectedPrimaryAxiomRef);
        }
        _ => {}
    }

    match (
        diagnostic.kind,
        diagnostic.expected_hash.is_some(),
        diagnostic.actual_hash.is_some(),
    ) {
        (MachineApiErrorKind::TypeMismatch, true, true) => Ok(()),
        (MachineApiErrorKind::TypeMismatch, _, _) => {
            Err(MachineApiDiagnosticCanonicalizationError::IncompleteTypeMismatchHashes)
        }
        (_, false, false) => Ok(()),
        (kind, _, _) => {
            Err(MachineApiDiagnosticCanonicalizationError::UnexpectedExpectedActualHash { kind })
        }
    }?;

    validate_primary_name_population(diagnostic)?;
    validate_goal_tactic_population(diagnostic)
}

fn validate_axiom_ref(
    axiom_ref: &MachineAxiomRefWire,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    match axiom_ref {
        MachineAxiomRefWire::Imported { module, name, .. } => {
            validate_name("primary_axiom_ref.module", module)?;
            validate_name("primary_axiom_ref.name", name)
        }
        MachineAxiomRefWire::CurrentModule { module, name, .. } => {
            validate_name("primary_axiom_ref.module", module)?;
            validate_name("primary_axiom_ref.name", name)
        }
        MachineAxiomRefWire::Builtin { name, .. } => validate_name("primary_axiom_ref.name", name),
    }
}

fn axiom_ref_name(axiom_ref: &MachineAxiomRefWire) -> &Name {
    match axiom_ref {
        MachineAxiomRefWire::Imported { name, .. }
        | MachineAxiomRefWire::CurrentModule { name, .. }
        | MachineAxiomRefWire::Builtin { name, .. } => name,
    }
}

fn validate_primary_name_population(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.primary_name.is_none() || diagnostic.kind == MachineApiErrorKind::DisallowedAxiom
    {
        return Ok(());
    }

    if primary_name_forbidden(diagnostic.kind) {
        return Err(
            MachineApiDiagnosticCanonicalizationError::UnexpectedPrimaryName {
                kind: diagnostic.kind,
            },
        );
    }

    Ok(())
}

fn primary_name_forbidden(kind: MachineApiErrorKind) -> bool {
    matches!(
        kind,
        MachineApiErrorKind::UnknownSession
            | MachineApiErrorKind::UnknownSnapshot
            | MachineApiErrorKind::StateFingerprintMismatch
            | MachineApiErrorKind::SessionRootHashMismatch
            | MachineApiErrorKind::InvalidSnapshotRequest
            | MachineApiErrorKind::InvalidTacticRunRequest
            | MachineApiErrorKind::InvalidTheoremQuery
            | MachineApiErrorKind::TheoremIndexFingerprintMismatch
            | MachineApiErrorKind::InvalidPromptPayloadRequest
            | MachineApiErrorKind::InvalidBatchPolicy
            | MachineApiErrorKind::InvalidSchedulerLimits
            | MachineApiErrorKind::InvalidReplayPlan
            | MachineApiErrorKind::InvalidVerifyRequest
            | MachineApiErrorKind::InvalidBudget
            | MachineApiErrorKind::GoalNotOpen
            | MachineApiErrorKind::ReplayHashMismatch
            | MachineApiErrorKind::MachineTermParseError
            | MachineApiErrorKind::TypeMismatch
            | MachineApiErrorKind::ExpectedPiType
            | MachineApiErrorKind::UnsupportedTactic
            | MachineApiErrorKind::RewriteRuleInvalid
            | MachineApiErrorKind::SimpNoProgress
            | MachineApiErrorKind::InductionTargetNotNat
            | MachineApiErrorKind::BudgetExceeded
            | MachineApiErrorKind::TooManyGoals
            | MachineApiErrorKind::TooLargeTerm
            | MachineApiErrorKind::VerifyFailed
    )
}

fn validate_goal_tactic_population(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.tactic_kind.is_some() && diagnostic.goal_id.is_none() {
        return Err(MachineApiDiagnosticCanonicalizationError::MissingGoalId {
            kind: diagnostic.kind,
        });
    }

    match diagnostic.kind {
        MachineApiErrorKind::DisallowedAxiom => ensure_no_goal_tactic(diagnostic),
        MachineApiErrorKind::GoalNotOpen => {
            ensure_goal_id(diagnostic)?;
            ensure_no_tactic_kind(diagnostic)
        }
        MachineApiErrorKind::ReplayHashMismatch => ensure_goal_id(diagnostic),
        MachineApiErrorKind::UnsupportedTactic
        | MachineApiErrorKind::RewriteRuleInvalid
        | MachineApiErrorKind::SimpNoProgress
        | MachineApiErrorKind::InductionTargetNotNat
        | MachineApiErrorKind::BudgetExceeded
        | MachineApiErrorKind::TooManyGoals
        | MachineApiErrorKind::TooLargeTerm => {
            ensure_goal_id(diagnostic)?;
            ensure_tactic_kind(diagnostic)
        }
        MachineApiErrorKind::MachineTermParseError
        | MachineApiErrorKind::MachineTermElaborationError
        | MachineApiErrorKind::UnknownName
        | MachineApiErrorKind::ImplicitArgumentRequired
        | MachineApiErrorKind::TypeMismatch
        | MachineApiErrorKind::ExpectedPiType => {
            if diagnostic.goal_id.is_some() {
                ensure_tactic_kind(diagnostic)
            } else {
                Ok(())
            }
        }
        MachineApiErrorKind::InvalidMachineProofState | MachineApiErrorKind::InvalidCandidate => {
            Ok(())
        }
        MachineApiErrorKind::UnknownSession
        | MachineApiErrorKind::UnknownSnapshot
        | MachineApiErrorKind::StateFingerprintMismatch
        | MachineApiErrorKind::SessionRootHashMismatch
        | MachineApiErrorKind::InvalidVerifiedImport
        | MachineApiErrorKind::InvalidCheckedCurrentDecl
        | MachineApiErrorKind::InvalidMachineApiOptions
        | MachineApiErrorKind::InvalidSessionRequest
        | MachineApiErrorKind::InvalidSnapshotRequest
        | MachineApiErrorKind::InvalidTacticRunRequest
        | MachineApiErrorKind::InvalidTheoremIndex
        | MachineApiErrorKind::InvalidTheoremQuery
        | MachineApiErrorKind::TheoremIndexFingerprintMismatch
        | MachineApiErrorKind::InvalidPromptPayloadRequest
        | MachineApiErrorKind::InvalidBatchPolicy
        | MachineApiErrorKind::InvalidSchedulerLimits
        | MachineApiErrorKind::InvalidReplayPlan
        | MachineApiErrorKind::InvalidVerifyRequest
        | MachineApiErrorKind::InvalidBudget
        | MachineApiErrorKind::VerifyFailed => ensure_no_goal_tactic(diagnostic),
    }
}

fn ensure_no_goal_tactic(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    ensure_no_goal_id(diagnostic)?;
    ensure_no_tactic_kind(diagnostic)
}

fn ensure_goal_id(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.goal_id.is_some() {
        Ok(())
    } else {
        Err(MachineApiDiagnosticCanonicalizationError::MissingGoalId {
            kind: diagnostic.kind,
        })
    }
}

fn ensure_no_goal_id(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.goal_id.is_none() {
        Ok(())
    } else {
        Err(
            MachineApiDiagnosticCanonicalizationError::UnexpectedGoalId {
                kind: diagnostic.kind,
            },
        )
    }
}

fn ensure_tactic_kind(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.tactic_kind.is_some() {
        Ok(())
    } else {
        Err(
            MachineApiDiagnosticCanonicalizationError::MissingTacticKind {
                kind: diagnostic.kind,
            },
        )
    }
}

fn ensure_no_tactic_kind(
    diagnostic: &MachineApiDiagnosticProjection,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if diagnostic.tactic_kind.is_none() {
        Ok(())
    } else {
        Err(
            MachineApiDiagnosticCanonicalizationError::UnexpectedTacticKind {
                kind: diagnostic.kind,
            },
        )
    }
}

fn validate_name(
    field: &'static str,
    name: &Name,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    if !name.is_canonical() {
        return Err(MachineApiDiagnosticCanonicalizationError::NonCanonicalName { field });
    }
    checked_u32_len(field, name.0.len())?;
    for component in &name.0 {
        checked_u32_len(field, component.len())?;
    }
    Ok(())
}

fn encode_some_string(
    out: &mut Vec<u8>,
    field: &'static str,
    value: &str,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    out.push(0x01);
    encode_string(out, field, value)
}

fn encode_option_goal_id(out: &mut Vec<u8>, value: Option<npa_tactic::GoalId>) {
    match value {
        Some(goal_id) => {
            out.push(0x01);
            out.extend(goal_id_canonical_bytes(goal_id));
        }
        None => out.push(0x00),
    }
}

fn encode_option_tactic_kind(
    out: &mut Vec<u8>,
    value: Option<crate::MachineApiTacticKind>,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    match value {
        Some(kind) => encode_some_string(out, "tactic_kind", kind.as_str()),
        None => {
            out.push(0x00);
            Ok(())
        }
    }
}

fn encode_option_name(
    out: &mut Vec<u8>,
    field: &'static str,
    value: Option<&Name>,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    match value {
        Some(name) => {
            out.push(0x01);
            encode_name(out, field, name)
        }
        None => {
            out.push(0x00);
            Ok(())
        }
    }
}

fn encode_option_axiom_ref(out: &mut Vec<u8>, value: Option<&MachineAxiomRefWire>) {
    match value {
        Some(axiom_ref) => {
            out.push(0x01);
            out.extend(encode_machine_axiom_ref_wire(axiom_ref));
        }
        None => out.push(0x00),
    }
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
}

fn encode_name(
    out: &mut Vec<u8>,
    field: &'static str,
    name: &Name,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    validate_name(field, name)?;
    encode_u32(out, checked_u32_len(field, name.0.len())?);
    for component in &name.0 {
        encode_string(out, field, component)?;
    }
    Ok(())
}

fn encode_string(
    out: &mut Vec<u8>,
    field: &'static str,
    value: &str,
) -> Result<(), MachineApiDiagnosticCanonicalizationError> {
    encode_u32(out, checked_u32_len(field, value.len())?);
    out.extend(value.as_bytes());
    Ok(())
}

fn checked_u32_len(
    field: &'static str,
    len: usize,
) -> Result<u32, MachineApiDiagnosticCanonicalizationError> {
    u32::try_from(len)
        .map_err(|_| MachineApiDiagnosticCanonicalizationError::LengthExceeded { field, len })
}

fn encode_u32(out: &mut Vec<u8>, mut value: u32) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        DiagnosticBudget, DiagnosticBudgetCounterReport, DiagnosticBudgetReport,
        DiagnosticBudgetUsage, DiagnosticExecutionPlane, DiagnosticProfile, DiagnosticRequestPath,
        MachineApiDiagnosticPhase, MachineApiErrorWire, MachineApiRequestErrorReason,
        MachineApiTacticKind, MachineApiUpstreamDiagnostic,
    };
    use npa_kernel::{Level, UniverseConstraintRelation};
    use npa_tactic::{
        GoalId, MachineTacticDiagnostic, MachineTacticDiagnosticKind, RewriteDiagnostic,
        RewriteDiagnosticId, RewriteDiagnosticKind, RewriteDiagnosticSite,
        RewriteDiagnosticTargetKind, RewriteDirection, RewriteNoProgressReason,
        RewriteRepairOperator, RewriteSite, TacticFuelKind, UnificationConflictSubsetKind,
        UnificationDiagnosticKind, UniverseConstraintDiagnostic, UniverseDiagnostic,
        UniverseDiagnosticCoreKind, UniverseDiagnosticId, UniverseDiagnosticKind,
        UniverseInstantiationCandidate, UniverseRepairOperator,
    };

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn projection(kind: MachineApiErrorKind) -> MachineApiDiagnosticProjection {
        MachineApiDiagnosticProjection {
            kind,
            phase: MachineApiDiagnosticPhase::MachineTermCheck,
            retryable: false,
            goal_id: Some(GoalId(7)),
            tactic_kind: Some(MachineApiTacticKind::Exact),
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
            source_message: "display only".to_owned(),
            upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::MachineTermElaborationError,
                "display only",
            )),
        }
    }

    fn diagnostic_tree_off_fixture(message: &str) -> MachineDiagnosticTree {
        MachineDiagnosticTree {
            kind: MachineApiErrorKind::GoalNotOpen,
            phase: MachineApiDiagnosticPhase::SnapshotLookup,
            profile: DiagnosticProfile::Off,
            goal_id: Some(GoalId(7)),
            candidate_hash: Some(hash(1)),
            deterministic_budget_hash: Some(hash(2)),
            state_fingerprint: Some(hash(3)),
            expression_path: Vec::new(),
            expected_summary: None,
            actual_summary: None,
            related_constraints: Vec::new(),
            parent_diagnostic_hash: None,
            budget_report: None,
            children: Vec::new(),
            source_message: Some(message.to_owned()),
            pretty_payload: None,
        }
    }

    fn diagnostic_summary(head: &str, hash_byte: u8) -> MachineDiagnosticTermSummary {
        MachineDiagnosticTermSummary {
            head_symbol: Some(head.to_owned()),
            structural_hash: Some(hash(hash_byte)),
            node_count: Some(3),
            attributes: vec![
                MachineDiagnosticAttribute {
                    key: "binder_arity".to_owned(),
                    value: "1".to_owned(),
                },
                MachineDiagnosticAttribute {
                    key: "head_kind".to_owned(),
                    value: "constant".to_owned(),
                },
            ],
        }
    }

    fn diagnostic_tree_basic_fixture(message: &str) -> MachineDiagnosticTree {
        MachineDiagnosticTree {
            kind: MachineApiErrorKind::TypeMismatch,
            phase: MachineApiDiagnosticPhase::MachineTermCheck,
            profile: DiagnosticProfile::Basic,
            goal_id: Some(GoalId(7)),
            candidate_hash: Some(hash(1)),
            deterministic_budget_hash: Some(hash(2)),
            state_fingerprint: Some(hash(3)),
            expression_path: vec!["AppFunction".to_owned(), "AppArgument(1)".to_owned()],
            expected_summary: Some(diagnostic_summary("Nat.succ", 4)),
            actual_summary: Some(diagnostic_summary("Bool.true", 5)),
            related_constraints: vec![MachineDiagnosticConstraintSummary {
                constraint_id: "c0".to_owned(),
                kind: "rigid_head_mismatch".to_owned(),
                phase: MachineApiDiagnosticPhase::MachineTermCheck,
                lhs_hash: Some(hash(4)),
                rhs_hash: Some(hash(5)),
                path: vec!["AppArgument(1)".to_owned()],
                expected_summary: Some(diagnostic_summary("Nat.succ", 4)),
                actual_summary: Some(diagnostic_summary("Bool.true", 5)),
                child_constraint_ids: Vec::new(),
                subset_kind: MachineDiagnosticConflictSubsetKind::Minimal,
                attributes: Vec::new(),
            }],
            parent_diagnostic_hash: None,
            budget_report: None,
            children: Vec::new(),
            source_message: Some(message.to_owned()),
            pretty_payload: None,
        }
    }

    fn diagnostic_tree_full_fixture(message: &str) -> MachineDiagnosticTree {
        MachineDiagnosticTree {
            kind: MachineApiErrorKind::RewriteRuleInvalid,
            phase: MachineApiDiagnosticPhase::TacticExecution,
            profile: DiagnosticProfile::Full,
            goal_id: Some(GoalId(9)),
            candidate_hash: Some(hash(9)),
            deterministic_budget_hash: Some(hash(10)),
            state_fingerprint: Some(hash(11)),
            expression_path: vec!["RewriteOccurrence(0)".to_owned()],
            expected_summary: Some(diagnostic_summary("Eq", 12)),
            actual_summary: None,
            related_constraints: vec![MachineDiagnosticConstraintSummary {
                constraint_id: "c0".to_owned(),
                kind: "rewrite_site_blocked".to_owned(),
                phase: MachineApiDiagnosticPhase::TacticExecution,
                lhs_hash: Some(hash(12)),
                rhs_hash: None,
                path: vec!["RewriteOccurrence(0)".to_owned()],
                expected_summary: Some(diagnostic_summary("Eq", 12)),
                actual_summary: None,
                child_constraint_ids: Vec::new(),
                subset_kind: MachineDiagnosticConflictSubsetKind::Reduced,
                attributes: Vec::new(),
            }],
            parent_diagnostic_hash: Some(hash(13)),
            budget_report: Some(DiagnosticBudgetReport {
                graph_nodes: DiagnosticBudgetCounterReport::new(5, 4),
                expression_paths: DiagnosticBudgetCounterReport::new(2, 2),
                rewrite_site_scans: DiagnosticBudgetCounterReport::new(3, 1),
                pretty_term_bytes: DiagnosticBudgetCounterReport::new(17, 16),
                repair_proposals: DiagnosticBudgetCounterReport::new(1, 1),
                diagnostic_steps: DiagnosticBudgetCounterReport::new(9, 8),
            }),
            children: Vec::new(),
            source_message: Some(message.to_owned()),
            pretty_payload: Some(MachineDiagnosticPrettyPayload {
                message: Some("full pretty payload".to_owned()),
                pretty_terms: vec!["target pretty term".to_owned()],
                repair_proposals: vec!["reverse rewrite".to_owned()],
            }),
        }
    }

    fn manual_string(value: &str) -> Vec<u8> {
        let mut out = Vec::new();
        manual_u32(&mut out, value.len() as u32);
        out.extend(value.as_bytes());
        out
    }

    fn manual_name(components: &[&str]) -> Vec<u8> {
        let mut out = Vec::new();
        manual_u32(&mut out, components.len() as u32);
        for component in components {
            out.extend(manual_string(component));
        }
        out
    }

    fn manual_u32(out: &mut Vec<u8>, mut value: u32) {
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if value == 0 {
                break;
            }
        }
    }

    #[test]
    fn canonical_bytes_use_fixed_field_order_and_wire_names() {
        let mut diagnostic = projection(MachineApiErrorKind::UnknownName);
        diagnostic.tactic_kind = Some(MachineApiTacticKind::Rw);
        diagnostic.primary_name = Some(Name::from_dotted("Nat.zero"));

        let mut expected = Vec::new();
        expected.extend(manual_string(API_DIAGNOSTIC_TAG));
        expected.extend(manual_string("unknown_name"));
        expected.push(0x01);
        expected.extend(manual_string("machine_term_check"));
        expected.push(0x01);
        expected.extend(goal_id_canonical_bytes(GoalId(7)));
        expected.push(0x01);
        expected.extend(manual_string("rw"));
        expected.push(0x01);
        expected.extend(manual_name(&["Nat", "zero"]));
        expected.push(0x00);
        expected.push(0x00);
        expected.push(0x00);
        expected.push(0x00);

        assert_eq!(diagnostic.canonical_bytes().unwrap(), expected);
    }

    #[test]
    fn diagnostic_hash_uses_canonical_bytes_only() {
        let mut diagnostic = projection(MachineApiErrorKind::TypeMismatch);
        diagnostic.expected_hash = Some([1; 32]);
        diagnostic.actual_hash = Some([2; 32]);

        let hash = diagnostic.diagnostic_hash().unwrap();
        let canonical = diagnostic.canonical_bytes().unwrap();
        let manual = Sha256::digest(&canonical);
        assert_eq!(hash.as_slice(), manual.as_slice());

        let mut display_changed = diagnostic.clone();
        display_changed.source_message = "different display text".to_owned();
        display_changed.upstream =
            MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
                MachineTacticDiagnosticKind::TypeMismatch,
                "different source diagnostic message",
            ));
        assert_eq!(display_changed.diagnostic_hash().unwrap(), hash);

        let mut structured_changed = diagnostic;
        structured_changed.actual_hash = Some([3; 32]);
        assert_ne!(structured_changed.diagnostic_hash().unwrap(), hash);
    }

    #[test]
    fn disallowed_axiom_requires_matching_primary_axiom_ref() {
        let axiom_ref = MachineAxiomRefWire::Builtin {
            name: Name::from_dotted("Classical.choice"),
            decl_interface_hash: [4; 32],
        };
        let mut diagnostic = projection(MachineApiErrorKind::DisallowedAxiom);
        diagnostic.phase = MachineApiDiagnosticPhase::CertificateVerify;
        diagnostic.goal_id = None;
        diagnostic.tactic_kind = None;
        diagnostic.primary_name = Some(Name::from_dotted("Classical.choice"));
        diagnostic.primary_axiom_ref = Some(axiom_ref.clone());

        let hash = diagnostic.diagnostic_hash().unwrap();
        let mut changed = diagnostic;
        changed.primary_axiom_ref = Some(MachineAxiomRefWire::Builtin {
            name: Name::from_dotted("Classical.choice"),
            decl_interface_hash: [5; 32],
        });
        assert_ne!(changed.diagnostic_hash().unwrap(), hash);

        let mut missing = changed;
        missing.primary_axiom_ref = None;
        assert_eq!(
            missing.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::MissingPrimaryAxiomRef
        );
    }

    #[test]
    fn scheduler_retryable_stop_is_not_a_deterministic_diagnostic() {
        let mut diagnostic = projection(MachineApiErrorKind::BudgetExceeded);
        diagnostic.retryable = true;

        assert_eq!(
            diagnostic.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::RetryableDiagnosticUnsupported
        );
    }

    #[test]
    fn lazy_diagnostic_profile_api_success_path_never_generates_full() {
        let plan = crate::plan_lazy_diagnostic_profile(
            DiagnosticProfile::Full,
            DiagnosticRequestPath::SuccessPath,
        );

        assert_eq!(plan.effective_profile, DiagnosticProfile::Off);
        assert_eq!(plan.execution_plane, DiagnosticExecutionPlane::Tactic);
        assert_eq!(plan.full_diagnostics_generated_on_success, 0);
        assert!(plan
            .effective_profile
            .capabilities()
            .compact_error_record_fields_enabled());
        assert!(!plan.full_payloads_enabled());
    }

    #[test]
    fn lazy_diagnostic_profile_api_basic_failure_avoids_full_graph_budget() {
        let plan = crate::plan_lazy_diagnostic_profile(
            DiagnosticProfile::Basic,
            DiagnosticRequestPath::FailedCandidateDiagnosticHash,
        );
        let capabilities = plan.effective_profile.capabilities();

        assert_eq!(plan.effective_profile, DiagnosticProfile::Basic);
        assert_eq!(plan.execution_plane, DiagnosticExecutionPlane::Tactic);
        assert!(capabilities.compact_error_record_fields_enabled());
        assert!(capabilities.expected_actual_heads);
        assert!(capabilities.compact_expression_paths);
        assert!(capabilities.bounded_local_context);
        assert!(capabilities.related_constraint_summary);
        assert!(!capabilities.has_full_payloads());
        assert!(plan
            .full_budget_report(
                DiagnosticBudget::default(),
                DiagnosticBudgetUsage::default()
            )
            .is_none());
    }

    #[test]
    fn lazy_diagnostic_profile_api_full_failure_reports_budget_truncation() {
        let plan = crate::plan_lazy_diagnostic_profile(
            DiagnosticProfile::Full,
            DiagnosticRequestPath::PreviousFailureCacheHit,
        );
        let report = plan
            .full_budget_report(
                DiagnosticBudget {
                    max_graph_nodes: 1,
                    max_expression_paths: 2,
                    max_rewrite_site_scans: 3,
                    max_pretty_term_bytes: 4,
                    max_repair_proposals: 5,
                    max_diagnostic_steps: 6,
                },
                DiagnosticBudgetUsage {
                    graph_nodes: 2,
                    expression_paths: 2,
                    rewrite_site_scans: 3,
                    pretty_term_bytes: 4,
                    repair_proposals: 7,
                    diagnostic_steps: 6,
                },
            )
            .expect("full diagnostics use an explicit diagnostic budget");

        assert_eq!(
            plan.execution_plane,
            DiagnosticExecutionPlane::AuthoringSidecar
        );
        assert!(report.truncated());
        assert!(report.graph_nodes.truncated);
        assert!(!report.expression_paths.truncated);
        assert!(!report.rewrite_site_scans.truncated);
        assert!(!report.pretty_term_bytes.truncated);
        assert!(report.repair_proposals.truncated);
        assert!(!report.diagnostic_steps.truncated);
    }

    #[test]
    fn diagnostic_tree_off_json_snapshot_round_trips() {
        let tree = diagnostic_tree_off_fixture("goal display text");
        let diagnostic_hash = tree.diagnostic_hash().unwrap();
        let expected = format!(
            "{{\"schema\":\"npa.machine-diagnostic-tree.v1\",\"diagnostic_hash\":{},\"kind\":\"goal_not_open\",\"phase\":\"snapshot_lookup\",\"profile\":\"off\",\"goal_id\":\"g7\",\"candidate_hash\":{},\"deterministic_budget_hash\":{},\"state_fingerprint\":{},\"expression_path\":[],\"expected_summary\":null,\"actual_summary\":null,\"related_constraints\":[],\"parent_diagnostic_hash\":null,\"budget_report\":null,\"children\":[],\"source_message\":\"goal display text\",\"pretty_payload\":null}}",
            json_hash(&diagnostic_hash),
            json_hash(&hash(1)),
            json_hash(&hash(2)),
            json_hash(&hash(3)),
        );

        let json = tree.canonical_json().unwrap();
        assert_eq!(json, expected);
        let parsed = parse_machine_diagnostic_tree_json(&json).unwrap();
        assert_eq!(parsed, tree);
        assert_eq!(parsed.canonical_json().unwrap(), json);
    }

    #[test]
    fn diagnostic_tree_basic_json_snapshot_round_trips() {
        let tree = diagnostic_tree_basic_fixture("type mismatch display text");
        let diagnostic_hash = tree.diagnostic_hash().unwrap();
        let expected = format!(
            "{{\"schema\":\"npa.machine-diagnostic-tree.v1\",\"diagnostic_hash\":{},\"kind\":\"type_mismatch\",\"phase\":\"machine_term_check\",\"profile\":\"basic\",\"goal_id\":\"g7\",\"candidate_hash\":{},\"deterministic_budget_hash\":{},\"state_fingerprint\":{},\"expression_path\":[\"AppFunction\",\"AppArgument(1)\"],\"expected_summary\":{{\"head_symbol\":\"Nat.succ\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"actual_summary\":{{\"head_symbol\":\"Bool.true\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"related_constraints\":[{{\"constraint_id\":\"c0\",\"kind\":\"rigid_head_mismatch\",\"phase\":\"machine_term_check\",\"lhs_hash\":{},\"rhs_hash\":{},\"path\":[\"AppArgument(1)\"],\"expected_summary\":{{\"head_symbol\":\"Nat.succ\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"actual_summary\":{{\"head_symbol\":\"Bool.true\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"child_constraint_ids\":[],\"subset_kind\":\"minimal\",\"attributes\":{{}}}}],\"parent_diagnostic_hash\":null,\"budget_report\":null,\"children\":[],\"source_message\":\"type mismatch display text\",\"pretty_payload\":null}}",
            json_hash(&diagnostic_hash),
            json_hash(&hash(1)),
            json_hash(&hash(2)),
            json_hash(&hash(3)),
            json_hash(&hash(4)),
            json_hash(&hash(5)),
            json_hash(&hash(4)),
            json_hash(&hash(5)),
            json_hash(&hash(4)),
            json_hash(&hash(5)),
        );

        let json = tree.canonical_json().unwrap();
        assert_eq!(json, expected);
        let parsed = parse_machine_diagnostic_tree_json(&json).unwrap();
        assert_eq!(parsed, tree);
        assert_eq!(parsed.canonical_json().unwrap(), json);
    }

    #[test]
    fn diagnostic_tree_full_json_snapshot_round_trips() {
        let tree = diagnostic_tree_full_fixture("rewrite display text");
        let diagnostic_hash = tree.diagnostic_hash().unwrap();
        let expected = format!(
            "{{\"schema\":\"npa.machine-diagnostic-tree.v1\",\"diagnostic_hash\":{},\"kind\":\"rewrite_rule_invalid\",\"phase\":\"tactic_execution\",\"profile\":\"full\",\"goal_id\":\"g9\",\"candidate_hash\":{},\"deterministic_budget_hash\":{},\"state_fingerprint\":{},\"expression_path\":[\"RewriteOccurrence(0)\"],\"expected_summary\":{{\"head_symbol\":\"Eq\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"actual_summary\":null,\"related_constraints\":[{{\"constraint_id\":\"c0\",\"kind\":\"rewrite_site_blocked\",\"phase\":\"tactic_execution\",\"lhs_hash\":{},\"rhs_hash\":null,\"path\":[\"RewriteOccurrence(0)\"],\"expected_summary\":{{\"head_symbol\":\"Eq\",\"structural_hash\":{},\"node_count\":3,\"attributes\":{{\"binder_arity\":\"1\",\"head_kind\":\"constant\"}}}},\"actual_summary\":null,\"child_constraint_ids\":[],\"subset_kind\":\"reduced\",\"attributes\":{{}}}}],\"parent_diagnostic_hash\":{},\"budget_report\":{{\"truncated\":true,\"graph_nodes\":{{\"used\":5,\"limit\":4,\"truncated\":true}},\"expression_paths\":{{\"used\":2,\"limit\":2,\"truncated\":false}},\"rewrite_site_scans\":{{\"used\":3,\"limit\":1,\"truncated\":true}},\"pretty_term_bytes\":{{\"used\":17,\"limit\":16,\"truncated\":true}},\"repair_proposals\":{{\"used\":1,\"limit\":1,\"truncated\":false}},\"diagnostic_steps\":{{\"used\":9,\"limit\":8,\"truncated\":true}}}},\"children\":[],\"source_message\":\"rewrite display text\",\"pretty_payload\":{{\"message\":\"full pretty payload\",\"pretty_terms\":[\"target pretty term\"],\"repair_proposals\":[\"reverse rewrite\"]}}}}",
            json_hash(&diagnostic_hash),
            json_hash(&hash(9)),
            json_hash(&hash(10)),
            json_hash(&hash(11)),
            json_hash(&hash(12)),
            json_hash(&hash(12)),
            json_hash(&hash(12)),
            json_hash(&hash(13)),
        );

        let json = tree.canonical_json().unwrap();
        assert_eq!(json, expected);
        let parsed = parse_machine_diagnostic_tree_json(&json).unwrap();
        assert_eq!(parsed, tree);
        assert_eq!(parsed.canonical_json().unwrap(), json);
    }

    #[test]
    fn diagnostic_tree_hash_ignores_display_payload_but_tracks_structure() {
        let tree = diagnostic_tree_full_fixture("first display text");
        let original_hash = tree.diagnostic_hash().unwrap();

        let mut display_changed = tree.clone();
        display_changed.source_message = Some("second display text".to_owned());
        display_changed.pretty_payload = Some(MachineDiagnosticPrettyPayload {
            message: Some("different pretty payload".to_owned()),
            pretty_terms: vec!["different pretty term".to_owned()],
            repair_proposals: vec!["different proposal text".to_owned()],
        });
        assert_eq!(display_changed.diagnostic_hash().unwrap(), original_hash);

        let mut structural_changed = tree;
        structural_changed.expression_path = vec!["RewriteOccurrence(1)".to_owned()];
        assert_ne!(structural_changed.diagnostic_hash().unwrap(), original_hash);
    }

    #[test]
    fn diagnostic_tree_rejects_invalid_expression_paths() {
        let mut tree = diagnostic_tree_basic_fixture("invalid primary path");
        tree.expression_path = vec!["AppArgument(01)".to_owned()];
        assert!(matches!(
            tree.diagnostic_hash().unwrap_err(),
            MachineDiagnosticTreeCanonicalizationError::InvalidExpressionPath { step }
                if step == "expression_path:AppArgument(01)"
        ));

        let mut tree = diagnostic_tree_basic_fixture("invalid constraint path");
        tree.related_constraints[0].path = vec!["RewriteOccurrence(-1)".to_owned()];
        assert!(matches!(
            tree.diagnostic_hash().unwrap_err(),
            MachineDiagnosticTreeCanonicalizationError::InvalidExpressionPath { step }
                if step == "related_constraints.path:RewriteOccurrence(-1)"
        ));
    }

    #[test]
    fn diagnostic_tree_related_constraints_are_canonicalized_by_bytes() {
        let mut tree = diagnostic_tree_basic_fixture("constraint order display text");
        let first = tree.related_constraints[0].clone();
        let second = MachineDiagnosticConstraintSummary {
            constraint_id: "c1".to_owned(),
            kind: "local_context_dependency".to_owned(),
            phase: MachineApiDiagnosticPhase::MachineTermCheck,
            lhs_hash: Some(hash(6)),
            rhs_hash: Some(hash(7)),
            path: vec!["AppFunction".to_owned()],
            expected_summary: None,
            actual_summary: None,
            child_constraint_ids: vec!["c0".to_owned()],
            subset_kind: MachineDiagnosticConflictSubsetKind::Reduced,
            attributes: Vec::new(),
        };
        tree.related_constraints = vec![first.clone(), second.clone()];

        let mut reversed = tree.clone();
        reversed.related_constraints = vec![second, first.clone()];

        assert_eq!(
            tree.diagnostic_hash().unwrap(),
            reversed.diagnostic_hash().unwrap()
        );
        assert_eq!(
            tree.canonical_json().unwrap(),
            reversed.canonical_json().unwrap()
        );
        let parsed = parse_machine_diagnostic_tree_json(&reversed.canonical_json().unwrap())
            .expect("canonical constraint order parses");
        assert_eq!(
            parsed.canonical_json().unwrap(),
            reversed.canonical_json().unwrap()
        );

        let mut duplicate_constraints = tree;
        duplicate_constraints.related_constraints = vec![first.clone(), first];
        assert!(matches!(
            duplicate_constraints.diagnostic_hash().unwrap_err(),
            MachineDiagnosticTreeCanonicalizationError::DuplicateRelatedConstraint
        ));
    }

    #[test]
    fn diagnostic_tree_children_are_canonicalized_by_hash() {
        let child_a = diagnostic_tree_basic_fixture("child a display text");
        let child_b = diagnostic_tree_full_fixture("child b display text");
        let mut parent = diagnostic_tree_basic_fixture("parent display text");
        parent.children = vec![child_a.clone(), child_b.clone()];

        let mut reversed = parent.clone();
        reversed.children = vec![child_b, child_a.clone()];

        assert_eq!(
            parent.diagnostic_hash().unwrap(),
            reversed.diagnostic_hash().unwrap()
        );
        let canonical_json = reversed.canonical_json().unwrap();
        let parsed = parse_machine_diagnostic_tree_json(&canonical_json).unwrap();
        let child_hashes = parsed
            .children
            .iter()
            .map(|child| child.diagnostic_hash().unwrap())
            .collect::<Vec<_>>();
        assert!(child_hashes.windows(2).all(|window| window[0] < window[1]));
        assert_eq!(parsed.canonical_json().unwrap(), canonical_json);

        let mut duplicate_children = parent;
        duplicate_children.children = vec![child_a.clone(), child_a];
        assert!(matches!(
            duplicate_children.diagnostic_hash().unwrap_err(),
            MachineDiagnosticTreeCanonicalizationError::DuplicateChildDiagnosticHash { .. }
        ));
    }

    #[test]
    fn diagnostic_tree_parse_rejects_hash_mismatch_and_duplicate_fields() {
        let tree = diagnostic_tree_off_fixture("goal display text");
        let json = tree.canonical_json().unwrap();
        let wrong_hash_json = json.replacen(
            &format_hash_string(&tree.diagnostic_hash().unwrap()),
            &format_hash_string(&hash(99)),
            1,
        );
        assert!(matches!(
            parse_machine_diagnostic_tree_json(&wrong_hash_json).unwrap_err(),
            MachineDiagnosticTreeParseError::DiagnosticHashMismatch { .. }
        ));

        let duplicate = r#"{"schema":"npa.machine-diagnostic-tree.v1","schema":"npa.machine-diagnostic-tree.v1"}"#;
        let err = parse_machine_diagnostic_tree_json(duplicate).unwrap_err();
        let MachineDiagnosticTreeParseError::Shape(error) = err else {
            panic!("expected duplicate-key shape error");
        };
        assert!(matches!(
            error.reason,
            MachineApiRequestErrorReason::DuplicateKey { .. }
        ));
    }

    #[test]
    fn diagnostic_tree_rejects_trusted_evidence_claim_payloads() {
        let tree = diagnostic_tree_off_fixture("goal display text");
        let json = tree.canonical_json().unwrap();
        let with_claim = json.replace(
            "\"source_message\"",
            "\"trusted_evidence_claim\":true,\"source_message\"",
        );
        let err = parse_machine_diagnostic_tree_json(&with_claim).unwrap_err();
        let MachineDiagnosticTreeParseError::Shape(error) = err else {
            panic!("expected unknown-field shape error");
        };
        assert!(matches!(
            &error.reason,
            MachineApiRequestErrorReason::UnknownField { field }
                if field == "trusted_evidence_claim"
        ));

        let schema = include_str!(
            "../../../testdata/proof-using-agents/schemas/diagnostic_tree.schema.json"
        );
        assert!(schema.contains("trusted_evidence_claim"));
        assert!(schema.contains("proof_acceptance_state"));
        assert!(schema.contains("verified_artifact"));
    }

    #[test]
    fn diagnostic_adapter_off_projection_preserves_compact_wire_and_hashes() {
        let mut diagnostic = projection(MachineApiErrorKind::StateFingerprintMismatch);
        diagnostic.phase = MachineApiDiagnosticPhase::SnapshotLookup;
        diagnostic.goal_id = None;
        diagnostic.tactic_kind = None;
        let compact = MachineApiErrorWire::from_projection(&diagnostic).unwrap();

        let context = MachineDiagnosticTreeAdapterContext {
            profile: DiagnosticProfile::Off,
            candidate_hash: Some(hash(10)),
            deterministic_budget_hash: Some(hash(11)),
            state_fingerprint: Some(hash(12)),
            diagnostic_budget: DiagnosticBudget::default(),
        };
        let tree = machine_api_projection_diagnostic_tree(&diagnostic, context).unwrap();

        assert_eq!(compact.kind, MachineApiErrorKind::StateFingerprintMismatch);
        assert_eq!(
            compact.diagnostic_hash,
            diagnostic.diagnostic_hash().unwrap()
        );
        assert_eq!(tree.profile, DiagnosticProfile::Off);
        assert_eq!(tree.candidate_hash, Some(hash(10)));
        assert_eq!(tree.deterministic_budget_hash, Some(hash(11)));
        assert_eq!(tree.state_fingerprint, Some(hash(12)));
        assert!(tree.expected_summary.is_none());
        assert!(tree.actual_summary.is_none());

        let mut display_changed = diagnostic;
        display_changed.source_message = "different display text".to_owned();
        let display_changed_tree =
            machine_api_projection_diagnostic_tree(&display_changed, context).unwrap();
        assert_eq!(
            tree.diagnostic_hash().unwrap(),
            display_changed_tree.diagnostic_hash().unwrap()
        );

        let mut invalid_budget = projection(MachineApiErrorKind::InvalidBudget);
        invalid_budget.phase = MachineApiDiagnosticPhase::RequestValidation;
        invalid_budget.goal_id = None;
        invalid_budget.tactic_kind = None;
        let budget_tree = machine_api_projection_diagnostic_tree(&invalid_budget, context).unwrap();
        assert_eq!(budget_tree.kind, MachineApiErrorKind::InvalidBudget);
        assert_eq!(budget_tree.profile, DiagnosticProfile::Off);
    }

    #[test]
    fn diagnostic_adapter_basic_type_mismatch_projects_term_hashes() {
        let mut diagnostic = projection(MachineApiErrorKind::TypeMismatch);
        diagnostic.expected_hash = Some(hash(4));
        diagnostic.actual_hash = Some(hash(5));

        let tree = machine_api_projection_diagnostic_tree(
            &diagnostic,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Basic,
                candidate_hash: Some(hash(10)),
                deterministic_budget_hash: Some(hash(11)),
                state_fingerprint: Some(hash(12)),
                diagnostic_budget: DiagnosticBudget::default(),
            },
        )
        .unwrap();

        let compact = MachineApiErrorWire::from_projection(&diagnostic).unwrap();
        assert_eq!(compact.expected_hash, Some(hash(4)));
        assert_eq!(compact.actual_hash, Some(hash(5)));
        assert_eq!(tree.kind, MachineApiErrorKind::TypeMismatch);
        assert_eq!(
            tree.expected_summary.as_ref().unwrap().structural_hash,
            Some(hash(4))
        );
        assert_eq!(
            tree.actual_summary.as_ref().unwrap().structural_hash,
            Some(hash(5))
        );
        assert_eq!(tree.candidate_hash, Some(hash(10)));
        assert_eq!(tree.deterministic_budget_hash, Some(hash(11)));

        let original_hash = tree.diagnostic_hash().unwrap();
        let mut structured_changed = diagnostic;
        structured_changed.actual_hash = Some(hash(6));
        let changed_tree = machine_api_projection_diagnostic_tree(
            &structured_changed,
            MachineDiagnosticTreeAdapterContext::basic(),
        )
        .unwrap();
        assert_ne!(changed_tree.diagnostic_hash().unwrap(), original_hash);
    }

    #[test]
    fn diagnostic_adapter_frontend_basic_type_mismatch_projects_head_symbols() {
        let diagnostic = npa_frontend::MachineDiagnostic::error(
            npa_frontend::MachineDiagnosticKind::TypeMismatch,
            npa_frontend::Span::new(npa_frontend::FileId(1), 0, 4),
            "frontend display text",
        )
        .with_payload(npa_frontend::MachineDiagnosticPayload {
            head_symbol: Some("Nat.succ".to_owned()),
            expected_hash: Some(hash(4)),
            actual_hash: Some(hash(5)),
            expected_universe_args: Some(1),
            actual_universe_args: Some(2),
            ..npa_frontend::MachineDiagnosticPayload::default()
        });

        let tree = machine_frontend_diagnostic_tree(
            diagnostic,
            MachineApiDiagnosticPhase::MachineTermCheck,
            Some(GoalId(7)),
            Some(MachineApiTacticKind::Exact),
            MachineDiagnosticTreeAdapterContext::basic(),
        )
        .unwrap();

        let expected = tree.expected_summary.as_ref().unwrap();
        let actual = tree.actual_summary.as_ref().unwrap();
        assert_eq!(expected.head_symbol.as_deref(), Some("Nat.succ"));
        assert_eq!(actual.head_symbol.as_deref(), Some("Nat.succ"));
        assert_eq!(
            expected.attributes,
            vec![MachineDiagnosticAttribute {
                key: "universe_args".to_owned(),
                value: "1".to_owned(),
            }]
        );
        assert_eq!(
            actual.attributes,
            vec![MachineDiagnosticAttribute {
                key: "universe_args".to_owned(),
                value: "2".to_owned(),
            }]
        );
    }

    #[test]
    fn diagnostic_adapter_machine_tactic_kind_inventory_projects_to_tree() {
        use MachineTacticDiagnosticKind as Kind;

        let kinds = vec![
            Kind::InvalidTacticOption,
            Kind::InvalidBatchPolicy,
            Kind::UnsupportedTacticOption,
            Kind::InvalidMachineTactic,
            Kind::InvalidMachineTermSource,
            Kind::MachineTermElaborationError,
            Kind::UnknownName,
            Kind::ImplicitArgumentRequired,
            Kind::UnsupportedMachineTactic,
            Kind::TacticFuelExhausted {
                kind: TacticFuelKind::TacticStep,
            },
            Kind::TacticFuelExhausted {
                kind: TacticFuelKind::ExprNode,
            },
            Kind::InvalidMachineProofState,
            Kind::InvalidMachineProofSpec,
            Kind::InvalidVerifiedImport,
            Kind::AmbiguousKernelEnvDecl,
            Kind::InvalidCurrentDeclOrder,
            Kind::UncheckedCurrentDecl,
            Kind::CurrentDeclSignatureMismatch,
            Kind::UnknownGoal,
            Kind::GoalAlreadyAssigned,
            Kind::UnknownMeta,
            Kind::GoalLimitExceeded,
            Kind::MetaLimitExceeded,
            Kind::InvalidMetaDependency,
            Kind::InvalidMetaContext,
            Kind::ProofExprScopeError,
            Kind::ProofExprTypeMismatch,
            Kind::UnknownTacticHead,
            Kind::AmbiguousTacticHead,
            Kind::UnknownLocalName,
            Kind::AmbiguousLocalName,
            Kind::InvalidLocalHead,
            Kind::ExpectedFunctionType,
            Kind::ExpectedPiTarget,
            Kind::UniverseArgumentMismatch,
            Kind::MissingExplicitArgument,
            Kind::AmbiguousApplyArgument,
            Kind::TooManyApplyArguments,
            Kind::TooFewApplyArguments,
            Kind::SubgoalDataArgument,
            Kind::ExpectedEqTarget,
            Kind::UnknownSimpRule,
            Kind::AmbiguousSimpRule,
            Kind::InvalidSimpRule,
            Kind::SimpNoProgress,
            Kind::SimpStepLimitExceeded,
            Kind::AmbiguousRewriteRule,
            Kind::TacticPrimitiveUnavailable,
            Kind::InvalidEqFamily,
            Kind::InvalidNatFamily,
            Kind::InvalidInductionTarget,
            Kind::TypeMismatch,
            Kind::KernelRejected,
            Kind::UnresolvedGoal,
        ];

        for kind in kinds {
            let mut diagnostic = MachineTacticDiagnostic::new(kind.clone(), "inventory display");
            diagnostic.goal_id = Some(GoalId(7));
            diagnostic.tactic_kind = Some("exact".to_owned());
            if matches!(
                kind,
                Kind::ProofExprTypeMismatch | Kind::UniverseArgumentMismatch | Kind::TypeMismatch
            ) {
                diagnostic.expected_hash = Some(Box::new(hash(4)));
                diagnostic.actual_hash = Some(Box::new(hash(5)));
            }

            let api_kind = crate::map_machine_tactic_diagnostic_kind(&diagnostic);
            match api_kind {
                MachineApiErrorKind::InvalidSessionRequest
                | MachineApiErrorKind::InvalidVerifiedImport
                | MachineApiErrorKind::InvalidCheckedCurrentDecl
                | MachineApiErrorKind::InvalidMachineApiOptions
                | MachineApiErrorKind::InvalidBatchPolicy => {
                    diagnostic.goal_id = None;
                    diagnostic.tactic_kind = None;
                }
                MachineApiErrorKind::GoalNotOpen => {
                    diagnostic.tactic_kind = None;
                }
                _ => {}
            }

            let tree = machine_tactic_diagnostic_tree(
                diagnostic,
                MachineApiDiagnosticPhase::TacticExecution,
                MachineDiagnosticTreeAdapterContext::basic(),
            )
            .unwrap_or_else(|error| {
                panic!(
                    "expected {:?} to project to a diagnostic tree: {error:?}",
                    kind
                )
            });
            assert_eq!(tree.kind, api_kind);

            match kind {
                Kind::UnsupportedMachineTactic => {
                    assert_eq!(tree.kind, MachineApiErrorKind::UnsupportedTactic);
                }
                Kind::SimpNoProgress => {
                    assert_eq!(tree.kind, MachineApiErrorKind::SimpNoProgress);
                }
                Kind::UnknownGoal | Kind::GoalAlreadyAssigned => {
                    assert_eq!(tree.kind, MachineApiErrorKind::GoalNotOpen);
                }
                Kind::KernelRejected => {
                    assert_eq!(tree.kind, MachineApiErrorKind::InvalidMachineProofState);
                }
                Kind::TypeMismatch
                | Kind::UniverseArgumentMismatch
                | Kind::ProofExprTypeMismatch => {
                    assert!(tree.expected_summary.is_some());
                    assert!(tree.actual_summary.is_some());
                }
                _ => {}
            }
        }
    }

    #[test]
    fn diagnostic_adapter_human_tree_ignores_rendered_message_for_identity() {
        let span = npa_frontend::Span::new(npa_frontend::FileId(1), 2, 9);
        let mut first = npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::UnknownIdentifier,
            span,
            "unknown `foo`",
        );
        first.payload.as_mut().unwrap().phase = Some(npa_frontend::HumanDiagnosticPhase::Resolver);
        let mut second = npa_frontend::HumanDiagnostic::error(
            npa_frontend::HumanDiagnosticKind::UnknownIdentifier,
            span,
            "unknown `bar`",
        );
        second.payload.as_mut().unwrap().phase = Some(npa_frontend::HumanDiagnosticPhase::Resolver);

        let first_tree =
            human_diagnostic_tree(&first, MachineDiagnosticTreeAdapterContext::basic()).unwrap();
        let second_tree =
            human_diagnostic_tree(&second, MachineDiagnosticTreeAdapterContext::basic()).unwrap();

        assert_eq!(first_tree.kind, MachineApiErrorKind::UnknownName);
        assert_eq!(
            first_tree.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_ne!(first_tree.source_message, second_tree.source_message);
        assert_eq!(
            first_tree.diagnostic_hash().unwrap(),
            second_tree.diagnostic_hash().unwrap()
        );
        assert!(first_tree.expected_summary.is_none());
        assert!(first_tree.actual_summary.is_none());
    }

    #[test]
    fn diagnostic_adapter_retryable_scheduler_projection_is_not_tree_diagnostic() {
        let mut diagnostic = projection(MachineApiErrorKind::BudgetExceeded);
        diagnostic.retryable = true;

        assert_eq!(
            machine_api_projection_diagnostic_tree(
                &diagnostic,
                MachineDiagnosticTreeAdapterContext::basic()
            )
            .unwrap_err(),
            MachineDiagnosticTreeAdapterError::ApiDiagnostic(
                MachineApiDiagnosticCanonicalizationError::RetryableDiagnosticUnsupported
            )
        );
    }

    fn unification_diagnostic_api_budget(nodes: u64, steps: u64) -> DiagnosticBudget {
        DiagnosticBudget {
            max_graph_nodes: nodes,
            max_expression_paths: 8,
            max_rewrite_site_scans: 0,
            max_pretty_term_bytes: 0,
            max_repair_proposals: 0,
            max_diagnostic_steps: steps,
        }
    }

    fn unification_diagnostic_tactic_error() -> MachineTacticDiagnostic {
        let mut diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::TypeMismatch,
            "apply argument type mismatch",
        )
        .with_unification_conflict_kind(UnificationDiagnosticKind::RigidRigidMismatch);
        diagnostic.expected_hash = Some(Box::new(hash(4)));
        diagnostic.actual_hash = Some(Box::new(hash(5)));
        diagnostic.goal_id = Some(GoalId(7));
        diagnostic.tactic_kind = Some("apply".to_owned());
        diagnostic
    }

    #[test]
    fn unification_diagnostic_api_full_tree_projects_conflict_subset() {
        let tree = machine_tactic_diagnostic_tree(
            unification_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: Some(hash(10)),
                deterministic_budget_hash: Some(hash(11)),
                state_fingerprint: Some(hash(12)),
                diagnostic_budget: unification_diagnostic_api_budget(4, 4),
            },
        )
        .unwrap();

        assert_eq!(tree.profile, DiagnosticProfile::Full);
        assert_eq!(tree.related_constraints.len(), 1);
        let constraint = &tree.related_constraints[0];
        assert_eq!(constraint.constraint_id, "u0");
        assert_eq!(constraint.kind, "rigid_rigid_mismatch");
        assert_eq!(constraint.phase, MachineApiDiagnosticPhase::TacticExecution);
        assert_eq!(constraint.lhs_hash, Some(hash(4)));
        assert_eq!(constraint.rhs_hash, Some(hash(5)));
        assert_eq!(constraint.path, vec!["AppArgument(0)".to_owned()]);
        assert_eq!(
            constraint
                .expected_summary
                .as_ref()
                .unwrap()
                .structural_hash,
            Some(hash(4))
        );
        assert_eq!(
            constraint.actual_summary.as_ref().unwrap().structural_hash,
            Some(hash(5))
        );
        assert!(constraint.child_constraint_ids.is_empty());
        assert_eq!(
            constraint.subset_kind,
            MachineDiagnosticConflictSubsetKind::Minimal
        );
        let report = tree
            .budget_report
            .expect("full conflict subset reports budget");
        assert!(!report.truncated());
        assert_eq!(tree.candidate_hash, Some(hash(10)));
        assert_eq!(tree.deterministic_budget_hash, Some(hash(11)));
    }

    #[test]
    fn unification_diagnostic_api_budget_truncation_is_visible() {
        let tree = machine_tactic_diagnostic_tree(
            unification_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: unification_diagnostic_api_budget(0, 4),
            },
        )
        .unwrap();

        assert!(tree.related_constraints.is_empty());
        let report = tree
            .budget_report
            .expect("truncated conflict subset reports budget");
        assert!(report.truncated());
        assert!(report.graph_nodes.truncated);
        assert!(!report.diagnostic_steps.truncated);
    }

    fn universe_repair_diagnostic_api_budget(
        nodes: u64,
        paths: u64,
        repairs: u64,
        steps: u64,
    ) -> DiagnosticBudget {
        DiagnosticBudget {
            max_graph_nodes: nodes,
            max_expression_paths: paths,
            max_rewrite_site_scans: 0,
            max_pretty_term_bytes: 0,
            max_repair_proposals: repairs,
            max_diagnostic_steps: steps,
        }
    }

    fn universe_repair_diagnostic_tactic_error() -> MachineTacticDiagnostic {
        let rhs = Level::succ(Level::param("v"));
        let payload = UniverseDiagnostic {
            subset_kind: UnificationConflictSubsetKind::Reduced,
            core_kind: UniverseDiagnosticCoreKind::Reduced,
            constraints: vec![UniverseConstraintDiagnostic {
                id: UniverseDiagnosticId(0),
                kind: UniverseDiagnosticKind::UniverseMismatch,
                relation: UniverseConstraintRelation::Eq,
                lhs: Level::param("u"),
                rhs: rhs.clone(),
                path: vec!["AppFunction".to_owned(), "UniverseArg(0)".to_owned()],
                universe_params: vec!["v".to_owned(), "u".to_owned()],
                universe_metas: Vec::new(),
                dependency_ids: Vec::new(),
            }],
            unresolved_metas: Vec::new(),
            candidate_instantiations: vec![UniverseInstantiationCandidate {
                param: "u".to_owned(),
                level: rhs,
                source_path: vec!["AppFunction".to_owned(), "UniverseArg(0)".to_owned()],
                valid: true,
                rejection_kind: None,
            }],
            repair_operators: vec![UniverseRepairOperator::InstantiateUniverse],
            complete_graph: true,
            budget_report: DiagnosticBudget::default().report(Default::default()),
        };
        let mut diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::UniverseArgumentMismatch,
            "display only",
        )
        .with_universe_diagnostic(payload);
        diagnostic.goal_id = Some(GoalId(7));
        diagnostic.tactic_kind = Some("apply".to_owned());
        diagnostic
    }

    #[test]
    fn universe_repair_diagnostic_api_full_tree_projects_universe_graph() {
        let tree = machine_tactic_diagnostic_tree(
            universe_repair_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: Some(hash(10)),
                deterministic_budget_hash: Some(hash(11)),
                state_fingerprint: Some(hash(12)),
                diagnostic_budget: universe_repair_diagnostic_api_budget(4, 4, 4, 8),
            },
        )
        .unwrap();

        assert_eq!(tree.profile, DiagnosticProfile::Full);
        assert_eq!(tree.related_constraints.len(), 1);
        let constraint = &tree.related_constraints[0];
        assert_eq!(constraint.constraint_id, "v0");
        assert_eq!(constraint.kind, "universe_mismatch");
        assert_eq!(constraint.phase, MachineApiDiagnosticPhase::TacticExecution);
        assert_eq!(
            constraint.path,
            vec!["AppFunction".to_owned(), "AppArgument(0)".to_owned()]
        );
        assert!(constraint.lhs_hash.is_none());
        assert!(constraint.rhs_hash.is_none());
        assert_eq!(attr_value(&constraint.attributes, "relation"), Some("eq"));
        assert_eq!(
            attr_value(&constraint.attributes, "lhs_level"),
            Some("param(u)")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "rhs_level"),
            Some("succ(param(v))")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "universe_params"),
            Some("u,v")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "universe_source_path"),
            Some("AppFunction/UniverseArg(0)")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "candidate_instantiations"),
            Some("u=succ(param(v)):valid:none")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "core_kind"),
            Some("reduced_core")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "complete_graph"),
            Some("true")
        );
        assert_eq!(
            tree.pretty_payload
                .as_ref()
                .expect("universe repair proposal should be projected")
                .repair_proposals,
            vec!["instantiate_universe".to_owned()]
        );
        assert!(!tree.budget_report.unwrap().truncated());
    }

    #[test]
    fn universe_repair_diagnostic_api_kernel_constraint_path_is_attribute_only() {
        let payload = UniverseDiagnostic {
            subset_kind: UnificationConflictSubsetKind::Minimal,
            core_kind: UniverseDiagnosticCoreKind::Unsat,
            constraints: vec![UniverseConstraintDiagnostic {
                id: UniverseDiagnosticId(0),
                kind: UniverseDiagnosticKind::UnsatisfiableConstraint,
                relation: UniverseConstraintRelation::Le,
                lhs: Level::succ(Level::param("u")),
                rhs: Level::param("u"),
                path: vec!["UniverseConstraint(0)".to_owned()],
                universe_params: vec!["u".to_owned()],
                universe_metas: Vec::new(),
                dependency_ids: Vec::new(),
            }],
            unresolved_metas: Vec::new(),
            candidate_instantiations: Vec::new(),
            repair_operators: vec![UniverseRepairOperator::InstantiateUniverse],
            complete_graph: true,
            budget_report: DiagnosticBudget::default().report(Default::default()),
        };
        let diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::KernelRejected,
            "display only",
        )
        .with_universe_diagnostic(payload);

        let tree = machine_tactic_diagnostic_tree(
            diagnostic,
            MachineApiDiagnosticPhase::KernelCheck,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: universe_repair_diagnostic_api_budget(4, 4, 4, 8),
            },
        )
        .unwrap();

        let constraint = &tree.related_constraints[0];
        assert!(constraint.path.is_empty());
        assert_eq!(constraint.phase, MachineApiDiagnosticPhase::KernelCheck);
        assert_eq!(attr_value(&constraint.attributes, "relation"), Some("le"));
        assert_eq!(
            attr_value(&constraint.attributes, "core_kind"),
            Some("unsat_core")
        );
        assert_eq!(
            attr_value(&constraint.attributes, "universe_source_path"),
            Some("UniverseConstraint(0)")
        );
    }

    #[test]
    fn universe_repair_diagnostic_api_budget_truncation_is_visible() {
        let tree = machine_tactic_diagnostic_tree(
            universe_repair_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: universe_repair_diagnostic_api_budget(0, 4, 0, 8),
            },
        )
        .unwrap();

        assert!(tree.related_constraints.is_empty());
        assert!(tree.pretty_payload.is_none());
        let report = tree
            .budget_report
            .expect("truncated universe diagnostics report budget");
        assert!(report.truncated());
        assert!(report.graph_nodes.truncated);
        assert!(report.repair_proposals.truncated);
    }

    #[test]
    fn universe_repair_diagnostic_api_basic_profile_does_not_collect_graph() {
        let tree = machine_tactic_diagnostic_tree(
            universe_repair_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Basic,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: universe_repair_diagnostic_api_budget(4, 4, 4, 8),
            },
        )
        .unwrap();

        assert!(tree.related_constraints.is_empty());
        assert!(tree.budget_report.is_none());
        assert!(tree.pretty_payload.is_none());
    }

    fn rewrite_diagnostic_api_budget(
        nodes: u64,
        paths: u64,
        scans: u64,
        repairs: u64,
        steps: u64,
    ) -> DiagnosticBudget {
        DiagnosticBudget {
            max_graph_nodes: nodes,
            max_expression_paths: paths,
            max_rewrite_site_scans: scans,
            max_pretty_term_bytes: 0,
            max_repair_proposals: repairs,
            max_diagnostic_steps: steps,
        }
    }

    fn rewrite_diagnostic_tactic_error() -> MachineTacticDiagnostic {
        let goal_site = RewriteDiagnosticSite {
            id: RewriteDiagnosticId(1),
            kind: RewriteDiagnosticKind::NoMatch,
            target_kind: RewriteDiagnosticTargetKind::Goal,
            local_name: None,
            path: vec!["RewriteOccurrence(1)".to_owned()],
            direction: RewriteDirection::Backward,
            matched_side: RewriteSite::EqTargetRight,
            replacement_side: RewriteSite::EqTargetLeft,
            occurrence_index: Some(1),
            required_unfoldings: vec!["Nat.add".to_owned()],
            congruence_depth: 2,
            expected_hash: Some(hash(6)),
            actual_hash: Some(hash(7)),
            repair_operators: vec![
                RewriteRepairOperator::ReverseRewrite,
                RewriteRepairOperator::SelectRewriteOccurrence,
                RewriteRepairOperator::Unfold,
            ],
        };
        let local_site = RewriteDiagnosticSite {
            id: RewriteDiagnosticId(0),
            kind: RewriteDiagnosticKind::NoProgress,
            target_kind: RewriteDiagnosticTargetKind::LocalType,
            local_name: Some("h".to_owned()),
            path: vec!["RewriteOccurrence(0)".to_owned()],
            direction: RewriteDirection::Forward,
            matched_side: RewriteSite::EqTargetLeft,
            replacement_side: RewriteSite::EqTargetRight,
            occurrence_index: Some(0),
            required_unfoldings: Vec::new(),
            congruence_depth: 0,
            expected_hash: Some(hash(4)),
            actual_hash: Some(hash(5)),
            repair_operators: vec![RewriteRepairOperator::ReduceSimpSet],
        };
        let local_value_site = RewriteDiagnosticSite {
            id: RewriteDiagnosticId(2),
            kind: RewriteDiagnosticKind::NoMatch,
            target_kind: RewriteDiagnosticTargetKind::LocalValue,
            local_name: Some("x".to_owned()),
            path: vec!["RewriteOccurrence(2)".to_owned()],
            direction: RewriteDirection::Forward,
            matched_side: RewriteSite::EqTargetLeft,
            replacement_side: RewriteSite::EqTargetRight,
            occurrence_index: Some(2),
            required_unfoldings: Vec::new(),
            congruence_depth: 1,
            expected_hash: Some(hash(8)),
            actual_hash: Some(hash(9)),
            repair_operators: Vec::new(),
        };
        let rewrite = RewriteDiagnostic {
            subset_kind: UnificationConflictSubsetKind::Reduced,
            sites: vec![goal_site, local_site, local_value_site],
            forward_valid: true,
            backward_valid: true,
            forward_matches_goal: false,
            backward_matches_goal: true,
            forward_matches_hypothesis: true,
            backward_matches_hypothesis: false,
            rejected_by_budget_or_progress: false,
            complete_scan: true,
            no_progress_reason: Some(RewriteNoProgressReason::NoRuleMatched),
            budget_report: DiagnosticBudget::default().report(Default::default()),
        };
        let mut diagnostic =
            MachineTacticDiagnostic::new(MachineTacticDiagnosticKind::AmbiguousRewriteRule, "rw");
        diagnostic.goal_id = Some(GoalId(7));
        diagnostic.tactic_kind = Some("rw".to_owned());
        diagnostic.with_rewrite_diagnostic(rewrite)
    }

    fn attr_value<'a>(attrs: &'a [MachineDiagnosticAttribute], key: &str) -> Option<&'a str> {
        attrs
            .iter()
            .find(|attribute| attribute.key == key)
            .map(|attribute| attribute.value.as_str())
    }

    #[test]
    fn rewrite_diagnostic_api_full_tree_projects_structured_sites() {
        let tree = machine_tactic_diagnostic_tree(
            rewrite_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: Some(hash(10)),
                deterministic_budget_hash: Some(hash(11)),
                state_fingerprint: Some(hash(12)),
                diagnostic_budget: rewrite_diagnostic_api_budget(4, 4, 4, 8, 4),
            },
        )
        .unwrap();

        assert_eq!(tree.related_constraints.len(), 3);
        let local = &tree.related_constraints[0];
        assert_eq!(local.constraint_id, "r0");
        assert_eq!(local.kind, "rewrite_no_progress");
        assert_eq!(local.phase, MachineApiDiagnosticPhase::TacticExecution);
        assert_eq!(local.path, vec!["RewriteOccurrence(0)".to_owned()]);
        assert_eq!(local.lhs_hash, Some(hash(4)));
        assert_eq!(local.rhs_hash, Some(hash(5)));
        assert_eq!(
            attr_value(&local.attributes, "target_kind"),
            Some("local_type")
        );
        assert_eq!(attr_value(&local.attributes, "local_name"), Some("h"));
        assert_eq!(
            attr_value(&local.attributes, "repair_operators"),
            Some("reduce_simp_set")
        );
        assert_eq!(
            attr_value(&local.attributes, "forward_matches_hypothesis"),
            Some("true")
        );
        assert_eq!(attr_value(&local.attributes, "complete_scan"), Some("true"));

        let goal = &tree.related_constraints[1];
        assert_eq!(goal.constraint_id, "r1");
        assert_eq!(goal.kind, "rewrite_no_match");
        assert_eq!(attr_value(&goal.attributes, "direction"), Some("backward"));
        assert_eq!(
            attr_value(&goal.attributes, "matched_side"),
            Some("eq_target_right")
        );
        assert_eq!(
            attr_value(&goal.attributes, "replacement_side"),
            Some("eq_target_left")
        );
        assert_eq!(attr_value(&goal.attributes, "occurrence_index"), Some("1"));
        assert_eq!(attr_value(&goal.attributes, "congruence_depth"), Some("2"));
        assert_eq!(
            attr_value(&goal.attributes, "required_unfoldings"),
            Some("Nat.add")
        );
        assert_eq!(
            attr_value(&goal.attributes, "repair_operators"),
            Some("reverse_rewrite,select_rewrite_occurrence,unfold")
        );
        let local_value = &tree.related_constraints[2];
        assert_eq!(local_value.constraint_id, "r2");
        assert_eq!(local_value.kind, "rewrite_no_match");
        assert_eq!(
            attr_value(&local_value.attributes, "target_kind"),
            Some("local_value")
        );
        assert_eq!(attr_value(&local_value.attributes, "local_name"), Some("x"));
        assert_eq!(
            attr_value(&local_value.attributes, "congruence_depth"),
            Some("1")
        );
        assert_eq!(
            tree.pretty_payload
                .as_ref()
                .expect("rewrite repair operators are projected")
                .repair_proposals,
            vec![
                "reduce_simp_set".to_owned(),
                "reverse_rewrite".to_owned(),
                "select_rewrite_occurrence".to_owned(),
                "unfold".to_owned(),
            ]
        );
        assert!(!tree.budget_report.unwrap().truncated());
    }

    #[test]
    fn rewrite_diagnostic_api_budget_truncation_is_visible() {
        let tree = machine_tactic_diagnostic_tree(
            rewrite_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Full,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: rewrite_diagnostic_api_budget(4, 4, 0, 8, 4),
            },
        )
        .unwrap();

        assert!(tree.related_constraints.is_empty());
        assert!(tree.pretty_payload.is_none());
        let report = tree
            .budget_report
            .expect("truncated rewrite diagnostics report budget");
        assert!(report.truncated());
        assert!(report.rewrite_site_scans.truncated);
    }

    #[test]
    fn rewrite_diagnostic_api_basic_profile_does_not_scan_sites() {
        let tree = machine_tactic_diagnostic_tree(
            rewrite_diagnostic_tactic_error(),
            MachineApiDiagnosticPhase::TacticExecution,
            MachineDiagnosticTreeAdapterContext {
                profile: DiagnosticProfile::Basic,
                candidate_hash: None,
                deterministic_budget_hash: None,
                state_fingerprint: None,
                diagnostic_budget: rewrite_diagnostic_api_budget(4, 4, 4, 8, 4),
            },
        )
        .unwrap();

        assert!(tree.related_constraints.is_empty());
        assert!(tree.budget_report.is_none());
        assert!(tree.pretty_payload.is_none());
    }

    #[test]
    fn type_mismatch_requires_both_hashes() {
        let mut diagnostic = projection(MachineApiErrorKind::TypeMismatch);
        diagnostic.expected_hash = Some([1; 32]);

        assert_eq!(
            diagnostic.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::IncompleteTypeMismatchHashes
        );
    }

    #[test]
    fn rejects_primary_name_for_kinds_with_none_override() {
        for kind in [
            MachineApiErrorKind::GoalNotOpen,
            MachineApiErrorKind::ReplayHashMismatch,
            MachineApiErrorKind::BudgetExceeded,
        ] {
            let mut diagnostic = projection(kind);
            diagnostic.primary_name = Some(Name::from_dotted("Nat.zero"));

            assert_eq!(
                diagnostic.diagnostic_hash().unwrap_err(),
                MachineApiDiagnosticCanonicalizationError::UnexpectedPrimaryName { kind }
            );
        }
    }

    #[test]
    fn rejects_goal_tactic_population_mismatch() {
        let mut budget_exceeded = projection(MachineApiErrorKind::BudgetExceeded);
        budget_exceeded.goal_id = None;
        budget_exceeded.tactic_kind = None;
        assert_eq!(
            budget_exceeded.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::MissingGoalId {
                kind: MachineApiErrorKind::BudgetExceeded
            }
        );

        let mut goal_not_open = projection(MachineApiErrorKind::GoalNotOpen);
        assert_eq!(
            goal_not_open.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::UnexpectedTacticKind {
                kind: MachineApiErrorKind::GoalNotOpen
            }
        );

        goal_not_open.tactic_kind = None;
        assert!(goal_not_open.diagnostic_hash().is_ok());

        let mut request_error = projection(MachineApiErrorKind::InvalidBatchPolicy);
        request_error.tactic_kind = None;
        assert_eq!(
            request_error.diagnostic_hash().unwrap_err(),
            MachineApiDiagnosticCanonicalizationError::UnexpectedGoalId {
                kind: MachineApiErrorKind::InvalidBatchPolicy
            }
        );
    }
}

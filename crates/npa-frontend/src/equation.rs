use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
};

use sha2::{Digest, Sha256};

use npa_kernel::{Decl, Expr, Level, Reducibility};

use crate::{
    HumanDiagnostic, HumanDiagnosticKind, HumanDiagnosticPayload, HumanDiagnosticPhase,
    HumanGeneratedDeclarationKind, HumanGlobalRef, HumanResolvedEquationItem,
    HumanResolvedEquationRow, HumanResolvedMeasureDecreaseProof, HumanResolvedPattern,
    HumanResolvedTerminationAnnotation, ResolvedHumanModule, Span,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationBudgetUsage {
    pub pattern_matrix_cells: u64,
    pub expanded_branches: u64,
    pub decision_tree_nodes: u64,
    pub decision_tree_branch_depth: u64,
    pub generated_helpers: u64,
    pub generated_core_nodes: u64,
    pub helper_body_nodes: u64,
    pub eq_rec_transports: u64,
    pub generated_certificate_bytes: u64,
}

impl HumanEquationBudgetUsage {
    pub const fn zero() -> Self {
        Self {
            pattern_matrix_cells: 0,
            expanded_branches: 0,
            decision_tree_nodes: 0,
            decision_tree_branch_depth: 0,
            generated_helpers: 0,
            generated_core_nodes: 0,
            helper_body_nodes: 0,
            eq_rec_transports: 0,
            generated_certificate_bytes: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanEquationBudget {
    pub max_pattern_matrix_cells: u64,
    pub max_expanded_branches: u64,
    pub max_decision_tree_nodes: u64,
    pub max_decision_tree_branch_depth: u64,
    pub max_generated_helpers: u64,
    pub max_generated_core_nodes: u64,
    pub max_helper_body_nodes: u64,
    pub max_generated_eq_rec_transports: u64,
    pub max_generated_certificate_bytes: u64,
    pub helper_split_node_threshold: u64,
}

impl HumanEquationBudget {
    pub const fn new(max_pattern_matrix_cells: u64, max_expanded_branches: u64) -> Self {
        Self {
            max_pattern_matrix_cells,
            max_expanded_branches,
            max_decision_tree_nodes: 16_384,
            max_decision_tree_branch_depth: 512,
            max_generated_helpers: 1_024,
            max_generated_core_nodes: 65_536,
            max_helper_body_nodes: 16_384,
            max_generated_eq_rec_transports: 512,
            max_generated_certificate_bytes: 1_048_576,
            helper_split_node_threshold: 256,
        }
    }

    pub const fn permissive() -> Self {
        Self {
            max_pattern_matrix_cells: u64::MAX,
            max_expanded_branches: u64::MAX,
            max_decision_tree_nodes: u64::MAX,
            max_decision_tree_branch_depth: u64::MAX,
            max_generated_helpers: u64::MAX,
            max_generated_core_nodes: u64::MAX,
            max_helper_body_nodes: u64::MAX,
            max_generated_eq_rec_transports: u64::MAX,
            max_generated_certificate_bytes: u64::MAX,
            helper_split_node_threshold: u64::MAX,
        }
    }

    pub const fn with_decision_tree_limits(
        mut self,
        max_decision_tree_nodes: u64,
        max_decision_tree_branch_depth: u64,
    ) -> Self {
        self.max_decision_tree_nodes = max_decision_tree_nodes;
        self.max_decision_tree_branch_depth = max_decision_tree_branch_depth;
        self
    }

    pub const fn with_helper_split_node_threshold(
        mut self,
        helper_split_node_threshold: u64,
    ) -> Self {
        self.helper_split_node_threshold = helper_split_node_threshold;
        self
    }

    pub const fn with_max_generated_helpers(mut self, max_generated_helpers: u64) -> Self {
        self.max_generated_helpers = max_generated_helpers;
        self
    }

    pub const fn with_max_generated_core_nodes(mut self, max_generated_core_nodes: u64) -> Self {
        self.max_generated_core_nodes = max_generated_core_nodes;
        self
    }

    pub const fn with_max_helper_body_nodes(mut self, max_helper_body_nodes: u64) -> Self {
        self.max_helper_body_nodes = max_helper_body_nodes;
        self
    }

    pub const fn with_max_generated_eq_rec_transports(
        mut self,
        max_generated_eq_rec_transports: u64,
    ) -> Self {
        self.max_generated_eq_rec_transports = max_generated_eq_rec_transports;
        self
    }

    pub const fn with_max_generated_certificate_bytes(
        mut self,
        max_generated_certificate_bytes: u64,
    ) -> Self {
        self.max_generated_certificate_bytes = max_generated_certificate_bytes;
        self
    }

    fn exceeded_fields(self, usage: HumanEquationBudgetUsage) -> Vec<HumanEquationBudgetField> {
        let mut exceeded = Vec::new();
        if usage.pattern_matrix_cells > self.max_pattern_matrix_cells {
            exceeded.push(HumanEquationBudgetField::PatternMatrixCells);
        }
        if usage.expanded_branches > self.max_expanded_branches {
            exceeded.push(HumanEquationBudgetField::ExpandedBranches);
        }
        if usage.decision_tree_nodes > self.max_decision_tree_nodes {
            exceeded.push(HumanEquationBudgetField::DecisionTreeNodes);
        }
        if usage.decision_tree_branch_depth > self.max_decision_tree_branch_depth {
            exceeded.push(HumanEquationBudgetField::DecisionTreeBranchDepth);
        }
        if usage.generated_helpers > self.max_generated_helpers {
            exceeded.push(HumanEquationBudgetField::GeneratedHelpers);
        }
        if usage.generated_core_nodes > self.max_generated_core_nodes {
            exceeded.push(HumanEquationBudgetField::GeneratedCoreNodes);
        }
        if usage.helper_body_nodes > self.max_helper_body_nodes {
            exceeded.push(HumanEquationBudgetField::HelperBodyNodes);
        }
        if usage.eq_rec_transports > self.max_generated_eq_rec_transports {
            exceeded.push(HumanEquationBudgetField::EqRecTransports);
        }
        if usage.generated_certificate_bytes > self.max_generated_certificate_bytes {
            exceeded.push(HumanEquationBudgetField::GeneratedCertificateBytes);
        }
        exceeded
    }
}

impl Default for HumanEquationBudget {
    fn default() -> Self {
        Self::new(16_384, 4_096)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationBudgetField {
    PatternMatrixCells,
    ExpandedBranches,
    DecisionTreeNodes,
    DecisionTreeBranchDepth,
    GeneratedHelpers,
    GeneratedCoreNodes,
    HelperBodyNodes,
    EqRecTransports,
    GeneratedCertificateBytes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationBudgetError {
    pub budget: HumanEquationBudget,
    pub requested_usage: HumanEquationBudgetUsage,
    pub exceeded: Vec<HumanEquationBudgetField>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanEquationMatrixError {
    GeneratedTermBudgetExceeded(Box<HumanEquationBudgetError>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanEquationDecisionTreeError {
    GeneratedTermBudgetExceeded(Box<HumanEquationBudgetError>),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationConstructorOrder {
    pub positions: BTreeMap<String, u64>,
}

impl HumanEquationConstructorOrder {
    pub fn position_for(&self, constructor: &HumanGlobalRef) -> Option<u64> {
        self.positions
            .get(&constructor_metadata_key_for_ref(constructor))
            .copied()
    }
}

pub fn human_equation_constructor_order_from_resolved_module(
    resolved: &ResolvedHumanModule,
) -> HumanEquationConstructorOrder {
    let mut order = HumanEquationConstructorOrder::default();
    let mut next_position = 0;

    for imported in &resolved.state.source_interfaces.imports {
        for generated in &imported.source_interface.generated_declarations {
            if generated.kind != HumanGeneratedDeclarationKind::Constructor {
                continue;
            }
            insert_constructor_position(
                &mut order,
                &mut next_position,
                format!(
                    "imported:{}:{}",
                    imported.module.as_dotted(),
                    generated.name.as_dotted()
                ),
            );
        }
    }

    for generated in &resolved
        .state
        .source_interfaces
        .current
        .generated_declarations
    {
        if generated.kind != HumanGeneratedDeclarationKind::Constructor {
            continue;
        }
        insert_constructor_position(
            &mut order,
            &mut next_position,
            format!("local-generated:{}", generated.name.as_dotted()),
        );
    }

    order
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationConstructorFamilyTable {
    pub families: Vec<HumanEquationConstructorFamily>,
    pub constructor_to_family: BTreeMap<String, usize>,
}

impl HumanEquationConstructorFamilyTable {
    pub fn family_for_constructor_key(
        &self,
        constructor_key: &str,
    ) -> Option<&HumanEquationConstructorFamily> {
        self.constructor_to_family
            .get(constructor_key)
            .and_then(|index| self.families.get(*index))
    }

    fn family_for_constructor_set(
        &self,
        set: &HumanEquationPatternMatrixConstructorSet,
    ) -> Option<&HumanEquationConstructorFamily> {
        let mut family_index = None;
        for constructor in &set.constructors {
            let index = *self
                .constructor_to_family
                .get(&constructor.constructor_key)?;
            if family_index
                .replace(index)
                .is_some_and(|existing| existing != index)
            {
                return None;
            }
        }
        family_index.and_then(|index| self.families.get(index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationConstructorFamily {
    pub family_key: String,
    pub parent_name: String,
    pub constructors: Vec<HumanEquationPatternMatrixConstructor>,
}

pub fn human_equation_constructor_family_table_from_resolved_module(
    resolved: &ResolvedHumanModule,
) -> HumanEquationConstructorFamilyTable {
    let constructor_order = human_equation_constructor_order_from_resolved_module(resolved);
    let reference_by_metadata_key = human_equation_constructor_reference_map(resolved);
    let mut families = BTreeMap::<String, HumanEquationConstructorFamily>::new();

    for imported in &resolved.state.source_interfaces.imports {
        for generated in &imported.source_interface.generated_declarations {
            if generated.kind != HumanGeneratedDeclarationKind::Constructor {
                continue;
            }
            let metadata_key = format!(
                "imported:{}:{}",
                imported.module.as_dotted(),
                generated.name.as_dotted()
            );
            let Some(constructor) = reference_by_metadata_key.get(&metadata_key) else {
                continue;
            };
            let family_key = format!(
                "imported:{}:{}",
                imported.module.as_dotted(),
                generated.parent.as_dotted()
            );
            push_constructor_family_member(
                &mut families,
                family_key,
                generated.parent.as_dotted(),
                constructor,
                &constructor_order,
            );
        }
    }

    for generated in &resolved
        .state
        .source_interfaces
        .current
        .generated_declarations
    {
        if generated.kind != HumanGeneratedDeclarationKind::Constructor {
            continue;
        }
        let metadata_key = format!("local-generated:{}", generated.name.as_dotted());
        let Some(constructor) = reference_by_metadata_key.get(&metadata_key) else {
            continue;
        };
        let family_key = format!("local-generated:{}", generated.parent.as_dotted());
        push_constructor_family_member(
            &mut families,
            family_key,
            generated.parent.as_dotted(),
            constructor,
            &constructor_order,
        );
    }

    let mut families = families.into_values().collect::<Vec<_>>();
    for family in &mut families {
        family.constructors.sort_by(|lhs, rhs| {
            lhs.constructor_order_key
                .cmp(&rhs.constructor_order_key)
                .then_with(|| lhs.constructor_key.cmp(&rhs.constructor_key))
        });
    }
    families.sort_by(|lhs, rhs| {
        lhs.family_key
            .cmp(&rhs.family_key)
            .then_with(|| lhs.parent_name.cmp(&rhs.parent_name))
    });

    let mut constructor_to_family = BTreeMap::new();
    for (family_index, family) in families.iter().enumerate() {
        for constructor in &family.constructors {
            constructor_to_family.insert(constructor.constructor_key.clone(), family_index);
        }
    }

    HumanEquationConstructorFamilyTable {
        families,
        constructor_to_family,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrix {
    pub columns: Vec<HumanEquationPatternMatrixColumn>,
    pub rows: Vec<HumanEquationPatternMatrixRow>,
    pub constructors_by_column: Vec<HumanEquationPatternMatrixConstructorSet>,
    pub identity_input: String,
    pub identity_hash: npa_cert::Hash,
    pub budget_usage: HumanEquationBudgetUsage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrixColumn {
    pub index: usize,
    pub path: HumanEquationPatternMatrixColumnPath,
    pub identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HumanEquationPatternMatrixColumnPath {
    pub root: usize,
    pub segments: Vec<HumanEquationPatternMatrixPathSegment>,
}

impl HumanEquationPatternMatrixColumnPath {
    pub fn root(root: usize) -> Self {
        Self {
            root,
            segments: Vec::new(),
        }
    }

    fn child_with_order(
        &self,
        constructor_key: String,
        constructor_order_key: String,
        argument_index: usize,
    ) -> Self {
        let mut segments = self.segments.clone();
        segments.push(HumanEquationPatternMatrixPathSegment {
            constructor_order_key,
            constructor_key,
            argument_index,
        });
        Self {
            root: self.root,
            segments,
        }
    }

    fn identity(&self) -> String {
        let mut identity = format!("root:{}", self.root);
        for segment in &self.segments {
            let _ = write!(
                identity,
                "/ctor:{}/arg:{}",
                segment.constructor_key, segment.argument_index
            );
        }
        identity
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HumanEquationPatternMatrixPathSegment {
    pub constructor_order_key: String,
    pub constructor_key: String,
    pub argument_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrixConstructorSet {
    pub column_index: usize,
    pub column_path: HumanEquationPatternMatrixColumnPath,
    pub constructors: Vec<HumanEquationPatternMatrixConstructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrixConstructor {
    pub constructor: HumanGlobalRef,
    pub constructor_key: String,
    pub constructor_order_key: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrixRow {
    pub index: usize,
    pub provenance: HumanEquationPatternMatrixRowProvenance,
    pub cells: Vec<HumanEquationPatternMatrixCell>,
    pub value_identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationPatternMatrixRowProvenance {
    pub source_row_index: usize,
    pub source_span: Span,
    pub kind: HumanEquationPatternMatrixRowKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationPatternMatrixRowKind {
    Pattern,
    ExplicitDefaultExpansion,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanEquationPatternMatrixCell {
    Constructor {
        constructor: HumanGlobalRef,
        constructor_key: String,
        arity: usize,
    },
    Variable {
        slot: usize,
    },
    Default,
    Unavailable {
        blocked_by_constructor_key: String,
    },
}

impl HumanEquationPatternMatrixCell {
    fn identity(&self) -> String {
        match self {
            Self::Constructor {
                constructor_key,
                arity,
                ..
            } => format!("ctor:{constructor_key}/arity:{arity}"),
            Self::Variable { slot } => format!("var:{slot}"),
            Self::Default => "default".to_owned(),
            Self::Unavailable {
                blocked_by_constructor_key,
            } => format!("unavailable:{blocked_by_constructor_key}"),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationCoverageOptions {
    pub impossible_rows: Vec<HumanEquationImpossibleBranchFact>,
    pub proved_impossible_rows: Vec<HumanEquationImpossibleBranchFact>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationImpossibleBranchFact {
    pub row_index: usize,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoverageResult {
    pub exhaustive: bool,
    pub accepted: bool,
    pub row_statuses: Vec<HumanEquationCoverageRowStatus>,
    pub missing_constructor_sets: Vec<HumanEquationMissingConstructorSet>,
    pub diagnostics: Vec<HumanEquationCoverageDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoverageBlockResult {
    pub accepted: bool,
    pub results: Vec<HumanEquationCoverageResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursionResult {
    pub accepted: bool,
    pub graph: HumanEquationRecursionGraph,
    pub diagnostics: Vec<HumanEquationRecursionDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursionBlockResult {
    pub accepted: bool,
    pub graph: HumanEquationRecursionGraph,
    pub diagnostics: Vec<HumanEquationRecursionDiagnostic>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationRecursionGraph {
    pub definitions: Vec<HumanEquationRecursionDefinition>,
    pub calls: Vec<HumanEquationRecursiveCall>,
    pub measure_obligations: Vec<HumanEquationMeasureDecreaseObligation>,
    pub measure_lowering_plans: Vec<HumanEquationMeasureLoweringPlan>,
    pub nondecreasing_cycles: Vec<HumanEquationMutualCycle>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursionDefinition {
    pub name: String,
    pub target_identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursiveCall {
    pub caller: String,
    pub callee: String,
    pub row_index: usize,
    pub primary_span: Span,
    pub call_identity: String,
    pub argument_mapping: Vec<String>,
    pub decrease_evidence: Option<HumanEquationStructuralDecreaseEvidence>,
    pub measure_decrease: Option<HumanEquationMeasureDecreaseObligation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationStructuralDecreaseEvidence {
    pub decreasing_parameter: usize,
    pub constructor_field_path: HumanEquationConstructorFieldPath,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationConstructorFieldPath {
    pub root_parameter: usize,
    pub segments: Vec<HumanEquationConstructorFieldSegment>,
    pub identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationConstructorFieldSegment {
    pub constructor_key: String,
    pub argument_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationMeasureDecreaseObligation {
    pub identity: String,
    pub caller: String,
    pub callee: String,
    pub row_index: usize,
    pub call_identity: String,
    pub measure_identity: String,
    pub caller_measure_identity: String,
    pub callee_measure_identity: String,
    pub relation_identity: String,
    pub proof: Option<HumanResolvedMeasureDecreaseProof>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationMeasureLoweringPlan {
    pub strategy: HumanEquationMeasureLoweringStrategy,
    pub definition_name: String,
    pub measure_identity: String,
    pub obligation_identities: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationMeasureLoweringStrategy {
    FuelStyleEncoding,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationMutualCycle {
    pub definitions: Vec<String>,
    pub target_identities: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursionDiagnostic {
    pub kind: HumanEquationRecursionDiagnosticKind,
    pub identity: String,
    pub primary_span: Span,
    pub caller: Option<String>,
    pub callee: Option<String>,
    pub row_index: Option<usize>,
    pub call_identity: Option<String>,
    pub cycle: Vec<String>,
}

impl HumanEquationRecursionDiagnostic {
    pub fn human_kind(&self) -> HumanDiagnosticKind {
        match self.kind {
            HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing => {
                HumanDiagnosticKind::RecursiveCallNotDecreasing
            }
            HumanEquationRecursionDiagnosticKind::MutualCycleWithoutDecrease => {
                HumanDiagnosticKind::MutualCycleWithoutDecrease
            }
            HumanEquationRecursionDiagnosticKind::TerminationMeasureNotNat => {
                HumanDiagnosticKind::TerminationMeasureNotNat
            }
            HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing => {
                HumanDiagnosticKind::MeasureDecreaseProofMissing
            }
        }
    }

    pub fn to_human_diagnostic(&self) -> HumanDiagnostic {
        let detail = match self.kind {
            HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing => format!(
                "recursive call from {} to {} is not structurally decreasing",
                self.caller.as_deref().unwrap_or("<unknown>"),
                self.callee.as_deref().unwrap_or("<unknown>")
            ),
            HumanEquationRecursionDiagnosticKind::MutualCycleWithoutDecrease => format!(
                "mutual recursion cycle has no structurally decreasing edge: {}",
                self.cycle.join(" -> ")
            ),
            HumanEquationRecursionDiagnosticKind::TerminationMeasureNotNat => {
                "termination measure is not Nat-valued".to_owned()
            }
            HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing => format!(
                "recursive call from {} to {} is missing checked Nat strict-decrease proof",
                self.caller.as_deref().unwrap_or("<unknown>"),
                self.callee.as_deref().unwrap_or("<unknown>")
            ),
        };

        HumanDiagnostic::error(self.human_kind(), self.primary_span, detail)
            .with_phase(HumanDiagnosticPhase::Elaborator)
            .with_payload(HumanDiagnosticPayload {
                candidates: self.cycle.clone(),
                ..HumanDiagnosticPayload::default()
            })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HumanEquationRecursionDiagnosticKind {
    RecursiveCallNotDecreasing,
    MutualCycleWithoutDecrease,
    TerminationMeasureNotNat,
    MeasureDecreaseProofMissing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionTreeResult {
    pub tree: HumanEquationDecisionTree,
    pub helper_plan: HumanEquationHelperSplitPlan,
    pub sidecar_metrics: HumanEquationDecisionTreeMetrics,
    pub budget_usage: HumanEquationBudgetUsage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionTree {
    pub root: HumanEquationDecisionTreeNode,
    pub identity_input: String,
    pub identity_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanEquationDecisionTreeNode {
    Leaf(HumanEquationDecisionLeaf),
    Switch(HumanEquationDecisionSwitch),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionLeaf {
    pub row_index: usize,
    pub source_row_index: usize,
    pub value_identity: String,
    pub branch_context: HumanEquationDecisionBranchContext,
    pub recursive_calls: Vec<HumanEquationRecursiveCall>,
    pub identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionSwitch {
    pub column_index: usize,
    pub column_identity: String,
    pub branches: Vec<HumanEquationDecisionBranch>,
    pub default_branch: Option<Box<HumanEquationDecisionTreeNode>>,
    pub identity: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionBranch {
    pub constructor: HumanEquationPatternMatrixConstructor,
    pub child: Box<HumanEquationDecisionTreeNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionBranchContext {
    pub row_index: usize,
    pub source_row_index: usize,
    pub cells: Vec<HumanEquationDecisionBranchCell>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationDecisionBranchCell {
    pub column_index: usize,
    pub column_identity: String,
    pub cell_identity: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationHelperSplitPlan {
    pub helpers: Vec<HumanEquationHelperCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationHelperCandidate {
    pub name: String,
    pub role: String,
    pub ordinal: u64,
    pub semantic_identity: String,
    pub target_node_identity: String,
    pub row_indexes: Vec<usize>,
    pub node_count: u64,
    pub branch_depth: u64,
    pub dependencies: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationDecisionTreeMetrics {
    pub source_equations: u64,
    pub pattern_matrix_cells: u64,
    pub expanded_branches: u64,
    pub decision_tree_nodes: u64,
    pub generated_helpers: u64,
    pub maximum_branch_depth: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationLoweringResult {
    pub bundle: HumanEquationCoreArtifactBundle,
    pub equation_theorems: HumanEquationTheoremPlan,
    pub sidecar_metrics: HumanEquationLoweringMetrics,
    pub budget_usage: HumanEquationBudgetUsage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoreArtifactBundle {
    pub declarations: Vec<Decl>,
    pub artifacts: Vec<HumanEquationCoreArtifact>,
    pub identity_input: String,
    pub identity_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoreArtifact {
    pub name: String,
    pub kind: HumanEquationCoreArtifactKind,
    pub opaque: bool,
    pub node_count: u64,
    pub core_hash: npa_cert::Hash,
    pub identity_input: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationCoreArtifactKind {
    HelperDefinition,
    PublicDefinition,
    EquationTheorem,
}

impl HumanEquationCoreArtifactKind {
    const fn as_str(self) -> &'static str {
        match self {
            Self::HelperDefinition => "helper_definition",
            Self::PublicDefinition => "public_definition",
            Self::EquationTheorem => "equation_theorem",
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationLoweringMetrics {
    pub source_equations: u64,
    pub pattern_matrix_cells: u64,
    pub expanded_branches: u64,
    pub decision_tree_nodes: u64,
    pub generated_helpers: u64,
    pub generated_equation_theorems: u64,
    pub generated_core_nodes: u64,
    pub helper_body_nodes: u64,
    pub eq_rec_transports: u64,
    pub generated_certificate_bytes: u64,
    pub maximum_branch_depth: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanEquationLoweringError {
    GeneratedTermBudgetExceeded(Box<HumanEquationBudgetError>),
    EquationTheoremBudgetExceeded(Box<HumanEquationTheoremBudgetError>),
    EquationTheoremGenerationFailed {
        theorem_name: Option<String>,
        reason: String,
    },
    MissingRecursor {
        constructor_key: String,
    },
    MissingRowValue {
        row_index: usize,
        source_row_index: usize,
    },
    MissingDecisionBranch {
        column_identity: String,
        constructor_key: String,
    },
    MissingHelperContext {
        helper_name: String,
        target_node_identity: String,
    },
    UnsupportedRecursorProfile {
        recursor_name: String,
        reason: String,
    },
    DependentMotiveSynthesisFailed {
        recursor_name: String,
        reason: String,
    },
    AmbiguousConstructor {
        constructor_key: String,
        recursor_names: Vec<String>,
    },
    UnsupportedEqRecTransport {
        eq_rec_name: String,
        reason: String,
    },
    UnsupportedNestedOrMutualLowering {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationTheoremRequest {
    pub enabled: bool,
    pub include_helper_split_theorems: bool,
    pub budget: HumanEquationTheoremBudget,
}

impl HumanEquationTheoremRequest {
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            include_helper_split_theorems: false,
            budget: HumanEquationTheoremBudget::default(),
        }
    }

    pub fn computation_theorems() -> Self {
        Self {
            enabled: true,
            include_helper_split_theorems: false,
            budget: HumanEquationTheoremBudget::default(),
        }
    }

    pub const fn with_helper_split_theorems(mut self, include: bool) -> Self {
        self.include_helper_split_theorems = include;
        self
    }

    pub const fn with_budget(mut self, budget: HumanEquationTheoremBudget) -> Self {
        self.budget = budget;
        self
    }
}

impl Default for HumanEquationTheoremRequest {
    fn default() -> Self {
        Self::disabled()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanEquationTheoremBudget {
    pub max_generated_declarations: u64,
    pub max_generated_core_nodes: u64,
    pub max_generated_certificate_bytes: u64,
    pub max_helper_theorem_dependencies: u64,
}

impl HumanEquationTheoremBudget {
    pub const fn new(
        max_generated_declarations: u64,
        max_generated_core_nodes: u64,
        max_generated_certificate_bytes: u64,
        max_helper_theorem_dependencies: u64,
    ) -> Self {
        Self {
            max_generated_declarations,
            max_generated_core_nodes,
            max_generated_certificate_bytes,
            max_helper_theorem_dependencies,
        }
    }

    pub const fn permissive() -> Self {
        Self::new(u64::MAX, u64::MAX, u64::MAX, u64::MAX)
    }

    fn exceeded_fields(
        self,
        usage: HumanEquationTheoremBudgetUsage,
    ) -> Vec<HumanEquationTheoremBudgetField> {
        let mut exceeded = Vec::new();
        if usage.generated_declarations > self.max_generated_declarations {
            exceeded.push(HumanEquationTheoremBudgetField::GeneratedDeclarations);
        }
        if usage.generated_core_nodes > self.max_generated_core_nodes {
            exceeded.push(HumanEquationTheoremBudgetField::GeneratedCoreNodes);
        }
        if usage.generated_certificate_bytes > self.max_generated_certificate_bytes {
            exceeded.push(HumanEquationTheoremBudgetField::GeneratedCertificateBytes);
        }
        if usage.helper_theorem_dependencies > self.max_helper_theorem_dependencies {
            exceeded.push(HumanEquationTheoremBudgetField::HelperTheoremDependencies);
        }
        exceeded
    }
}

impl Default for HumanEquationTheoremBudget {
    fn default() -> Self {
        Self::new(256, 65_536, 1_048_576, 1_024)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationTheoremBudgetUsage {
    pub generated_declarations: u64,
    pub generated_core_nodes: u64,
    pub generated_certificate_bytes: u64,
    pub helper_theorem_dependencies: u64,
}

impl HumanEquationTheoremBudgetUsage {
    fn add_declaration(
        &mut self,
        node_count: u64,
        certificate_bytes: u64,
        helper_dependencies: u64,
    ) {
        self.generated_declarations = self.generated_declarations.saturating_add(1);
        self.generated_core_nodes = self.generated_core_nodes.saturating_add(node_count);
        self.generated_certificate_bytes = self
            .generated_certificate_bytes
            .saturating_add(certificate_bytes);
        self.helper_theorem_dependencies = self
            .helper_theorem_dependencies
            .saturating_add(helper_dependencies);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationTheoremBudgetField {
    GeneratedDeclarations,
    GeneratedCoreNodes,
    GeneratedCertificateBytes,
    HelperTheoremDependencies,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationTheoremBudgetError {
    pub budget: HumanEquationTheoremBudget,
    pub requested_usage: HumanEquationTheoremBudgetUsage,
    pub exceeded: Vec<HumanEquationTheoremBudgetField>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanEquationTheoremPlan {
    pub requested: bool,
    pub theorem_specs: Vec<HumanEquationTheoremSpec>,
    pub budget_usage: HumanEquationTheoremBudgetUsage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationTheoremSpec {
    pub name: String,
    pub source: HumanEquationTheoremSource,
    pub row_index: Option<usize>,
    pub source_row_index: Option<usize>,
    pub helper_name: Option<String>,
    pub relation_identity: String,
    pub proof_strategy: HumanEquationTheoremProofStrategy,
    pub dependency_names: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationTheoremSource {
    RowComputation,
    HelperSplit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationTheoremProofStrategy {
    EqReflAfterReduction,
    HelperSelfRefl,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationLoweringProfile {
    pub public_name: String,
    pub universe_params: Vec<String>,
    pub public_binders: Vec<HumanEquationLoweringBinder>,
    pub result_type: Expr,
    pub result_universe: Level,
    pub recursors: Vec<HumanEquationRecursorLoweringProfile>,
    pub row_values: BTreeMap<usize, Expr>,
    pub row_transports: BTreeMap<usize, Vec<HumanEquationEqRecTransport>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationLoweringBinder {
    pub name: String,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationRecursorLoweringProfile {
    pub recursor_name: String,
    pub universe_args: Vec<Level>,
    pub parameters: Vec<Expr>,
    pub index_binders: Vec<HumanEquationLoweringBinder>,
    pub major_index_args: Vec<Expr>,
    pub major_type: Expr,
    pub motive_body: Option<Expr>,
    pub constructors: Vec<HumanEquationConstructorLoweringProfile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationConstructorLoweringProfile {
    pub constructor_key: String,
    pub minor_binders: Vec<HumanEquationLoweringBinder>,
    pub result_index_args: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationEqRecTransport {
    pub eq_rec_name: String,
    pub value_level: Level,
    pub motive_level: Level,
    pub source_type: Expr,
    pub source: Expr,
    pub motive: Expr,
    pub target: Expr,
    pub proof: Expr,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoverageRowStatus {
    pub row_index: usize,
    pub kind: HumanEquationCoverageRowStatusKind,
    pub covered_by_rows: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanEquationCoverageRowStatusKind {
    Reachable,
    Duplicate,
    Unreachable,
    WildcardShadowed,
    Impossible,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationMissingConstructorSet {
    pub column_index: usize,
    pub column_identity: String,
    pub family_key: String,
    pub missing_constructors: Vec<HumanEquationPatternMatrixConstructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanEquationCoverageDiagnostic {
    pub kind: HumanEquationCoverageDiagnosticKind,
    pub identity: String,
    pub primary_span: Span,
    pub row_ids: Vec<usize>,
    pub covered_by_rows: Vec<usize>,
    pub column_index: Option<usize>,
    pub column_identity: Option<String>,
    pub missing_constructors: Vec<HumanEquationPatternMatrixConstructor>,
    pub reason: Option<String>,
}

impl HumanEquationCoverageDiagnostic {
    pub fn human_kind(&self) -> HumanDiagnosticKind {
        match self.kind {
            HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns => {
                HumanDiagnosticKind::NonExhaustivePatterns
            }
            HumanEquationCoverageDiagnosticKind::DuplicateBranch
            | HumanEquationCoverageDiagnosticKind::UnreachableBranch
            | HumanEquationCoverageDiagnosticKind::WildcardShadowing => {
                HumanDiagnosticKind::RedundantEquation
            }
            HumanEquationCoverageDiagnosticKind::ImpossibleBranch => {
                HumanDiagnosticKind::ImpossibleBranchNotProvable
            }
        }
    }

    pub fn to_human_diagnostic(&self) -> HumanDiagnostic {
        let detail = match self.kind {
            HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns => {
                "non-exhaustive equation patterns".to_owned()
            }
            HumanEquationCoverageDiagnosticKind::DuplicateBranch => {
                format!("duplicate equation branch row(s) {:?}", self.row_ids)
            }
            HumanEquationCoverageDiagnosticKind::UnreachableBranch => {
                format!("unreachable equation branch row(s) {:?}", self.row_ids)
            }
            HumanEquationCoverageDiagnosticKind::WildcardShadowing => {
                format!(
                    "equation branch row(s) {:?} are shadowed by an earlier default case",
                    self.row_ids
                )
            }
            HumanEquationCoverageDiagnosticKind::ImpossibleBranch => self
                .reason
                .clone()
                .unwrap_or_else(|| format!("impossible equation branch row(s) {:?}", self.row_ids)),
        };

        HumanDiagnostic::error(self.human_kind(), self.primary_span, detail)
            .with_phase(HumanDiagnosticPhase::Elaborator)
            .with_payload(HumanDiagnosticPayload {
                candidates: self
                    .missing_constructors
                    .iter()
                    .map(|constructor| constructor.constructor_key.clone())
                    .collect(),
                ..HumanDiagnosticPayload::default()
            })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HumanEquationCoverageDiagnosticKind {
    NonExhaustivePatterns,
    DuplicateBranch,
    UnreachableBranch,
    WildcardShadowing,
    ImpossibleBranch,
}

pub fn check_human_equation_coverage(
    matrix: &HumanEquationPatternMatrix,
    constructors: &HumanEquationConstructorFamilyTable,
) -> HumanEquationCoverageResult {
    check_human_equation_coverage_with_options(
        matrix,
        constructors,
        &HumanEquationCoverageOptions::default(),
    )
}

pub fn check_human_equation_coverage_with_options(
    matrix: &HumanEquationPatternMatrix,
    constructors: &HumanEquationConstructorFamilyTable,
    options: &HumanEquationCoverageOptions,
) -> HumanEquationCoverageResult {
    let mut row_statuses = matrix
        .rows
        .iter()
        .map(|row| HumanEquationCoverageRowStatus {
            row_index: row.index,
            kind: HumanEquationCoverageRowStatusKind::Reachable,
            covered_by_rows: Vec::new(),
        })
        .collect::<Vec<_>>();
    let mut diagnostics = Vec::new();

    let impossible_facts = options
        .impossible_rows
        .iter()
        .map(|fact| (fact.row_index, (fact, false)))
        .chain(
            options
                .proved_impossible_rows
                .iter()
                .map(|fact| (fact.row_index, (fact, true))),
        )
        .collect::<BTreeMap<_, _>>();
    for (row_index, (fact, proved)) in &impossible_facts {
        let Some(row) = matrix.rows.get(*row_index) else {
            continue;
        };
        row_statuses[*row_index].kind = HumanEquationCoverageRowStatusKind::Impossible;
        if !proved {
            diagnostics.push(coverage_diagnostic(
                HumanEquationCoverageDiagnosticKind::ImpossibleBranch,
                vec![*row_index],
                Vec::new(),
                None,
                Vec::new(),
                Some(fact.reason.clone()),
                row.provenance.source_span,
            ));
        }
    }

    let mut active_previous = Vec::<usize>::new();
    let mut seen_signatures = BTreeMap::<String, usize>::new();
    for row in &matrix.rows {
        if row_statuses[row.index].kind == HumanEquationCoverageRowStatusKind::Impossible {
            continue;
        }

        let signature = row_signature(row);
        if let Some(previous) = seen_signatures.get(&signature).copied() {
            mark_redundant_row(
                matrix,
                &mut row_statuses,
                &mut diagnostics,
                row.index,
                vec![previous],
                HumanEquationCoverageRowStatusKind::Duplicate,
                HumanEquationCoverageDiagnosticKind::DuplicateBranch,
            );
            continue;
        }

        if let Some(previous) = active_previous
            .iter()
            .copied()
            .find(|previous| row_covers(&matrix.rows[*previous], row))
        {
            let previous_kind = matrix.rows[previous].provenance.kind;
            let (row_kind, diagnostic_kind) =
                if previous_kind == HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion {
                    (
                        HumanEquationCoverageRowStatusKind::WildcardShadowed,
                        HumanEquationCoverageDiagnosticKind::WildcardShadowing,
                    )
                } else {
                    (
                        HumanEquationCoverageRowStatusKind::Unreachable,
                        HumanEquationCoverageDiagnosticKind::UnreachableBranch,
                    )
                };
            mark_redundant_row(
                matrix,
                &mut row_statuses,
                &mut diagnostics,
                row.index,
                vec![previous],
                row_kind,
                diagnostic_kind,
            );
            continue;
        }

        if row.provenance.kind == HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion
            && default_row_is_exhausted_by_previous(matrix, constructors, &active_previous)
        {
            mark_redundant_row(
                matrix,
                &mut row_statuses,
                &mut diagnostics,
                row.index,
                active_previous.clone(),
                HumanEquationCoverageRowStatusKind::Unreachable,
                HumanEquationCoverageDiagnosticKind::UnreachableBranch,
            );
            continue;
        }

        seen_signatures.insert(signature, row.index);
        active_previous.push(row.index);
    }

    let active_rows = row_statuses
        .iter()
        .filter(|status| status.kind == HumanEquationCoverageRowStatusKind::Reachable)
        .map(|status| status.row_index)
        .collect::<Vec<_>>();
    let mut missing_constructor_sets = missing_constructor_sets(matrix, constructors, &active_rows);
    missing_constructor_sets.sort_by_key(missing_constructor_set_sort_key);
    if let Some(smallest_missing) = missing_constructor_sets.first() {
        diagnostics.push(coverage_diagnostic(
            HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns,
            Vec::new(),
            Vec::new(),
            Some((
                smallest_missing.column_index,
                smallest_missing.column_identity.clone(),
            )),
            smallest_missing.missing_constructors.clone(),
            None,
            matrix
                .rows
                .first()
                .map(|row| row.provenance.source_span)
                .unwrap_or_else(|| Span::empty(crate::FileId(0))),
        ));
    }

    diagnostics.sort_by_key(coverage_diagnostic_sort_key);
    let exhaustive = missing_constructor_sets.is_empty();
    let accepted = exhaustive && diagnostics.is_empty();
    HumanEquationCoverageResult {
        exhaustive,
        accepted,
        row_statuses,
        missing_constructor_sets,
        diagnostics,
    }
}

pub fn check_human_equation_coverage_block(
    matrices: &[HumanEquationPatternMatrix],
    constructors: &HumanEquationConstructorFamilyTable,
) -> HumanEquationCoverageBlockResult {
    check_human_equation_coverage_block_with_options(matrices, constructors, &[])
}

pub fn check_human_equation_coverage_block_with_options(
    matrices: &[HumanEquationPatternMatrix],
    constructors: &HumanEquationConstructorFamilyTable,
    options: &[HumanEquationCoverageOptions],
) -> HumanEquationCoverageBlockResult {
    let results = matrices
        .iter()
        .enumerate()
        .map(|(index, matrix)| {
            if let Some(options) = options.get(index) {
                check_human_equation_coverage_with_options(matrix, constructors, options)
            } else {
                check_human_equation_coverage(matrix, constructors)
            }
        })
        .collect::<Vec<_>>();
    let accepted = results.iter().all(|result| result.accepted);
    HumanEquationCoverageBlockResult { accepted, results }
}

pub fn check_human_equation_structural_recursion(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
) -> HumanEquationRecursionResult {
    check_human_equation_recursion(equation, matrix)
}

pub fn check_human_equation_recursion(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
) -> HumanEquationRecursionResult {
    let block = check_human_equation_structural_recursion_block(
        std::slice::from_ref(equation),
        std::slice::from_ref(matrix),
    );
    HumanEquationRecursionResult {
        accepted: block.accepted,
        graph: block.graph,
        diagnostics: block.diagnostics,
    }
}

pub fn check_human_equation_structural_recursion_block(
    equations: &[HumanResolvedEquationItem],
    matrices: &[HumanEquationPatternMatrix],
) -> HumanEquationRecursionBlockResult {
    check_human_equation_recursion_block(equations, matrices)
}

pub fn check_human_equation_recursion_block(
    equations: &[HumanResolvedEquationItem],
    matrices: &[HumanEquationPatternMatrix],
) -> HumanEquationRecursionBlockResult {
    assert_eq!(
        equations.len(),
        matrices.len(),
        "structural recursion block requires one pattern matrix per equation"
    );

    let mut definitions = equations
        .iter()
        .map(|equation| HumanEquationRecursionDefinition {
            name: equation.source_name.as_dotted(),
            target_identity: recursion_global_identity(&equation.target),
        })
        .collect::<Vec<_>>();
    definitions.sort_by(|lhs, rhs| {
        lhs.target_identity
            .cmp(&rhs.target_identity)
            .then_with(|| lhs.name.cmp(&rhs.name))
    });

    let target_names = definitions
        .iter()
        .map(|definition| (definition.target_identity.clone(), definition.name.clone()))
        .collect::<BTreeMap<_, _>>();
    let target_spans = equations
        .iter()
        .map(|equation| {
            (
                recursion_global_identity(&equation.target),
                equation.source_name.span,
            )
        })
        .collect::<BTreeMap<_, _>>();

    let mut calls = Vec::new();
    for (equation, matrix) in equations.iter().zip(matrices) {
        calls.extend(recursive_calls_for_equation(
            equation,
            matrix,
            &target_names,
        ));
    }
    calls.sort_by_key(recursive_call_sort_key);

    let equation_measure_statuses = equations
        .iter()
        .map(|equation| {
            (
                equation.source_name.as_dotted(),
                equation
                    .termination
                    .as_ref()
                    .map(|termination| measure_type_is_nat(&termination.measure_type_identity)),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let mut diagnostics = equations
        .iter()
        .filter_map(|equation| {
            let termination = equation.termination.as_ref()?;
            (!measure_type_is_nat(&termination.measure_type_identity))
                .then(|| termination_measure_not_nat_diagnostic(equation, termination.span))
        })
        .collect::<Vec<_>>();

    diagnostics.extend(
        calls
            .iter()
            .filter(|call| call.measure_decrease.is_none() && call.decrease_evidence.is_none())
            .map(recursive_call_not_decreasing_diagnostic),
    );
    diagnostics.extend(
        calls
            .iter()
            .filter(|call| {
                matches!(
                    equation_measure_statuses.get(&call.caller),
                    Some(Some(true))
                ) && call
                    .measure_decrease
                    .as_ref()
                    .is_some_and(|obligation| obligation.proof.is_none())
            })
            .map(measure_decrease_proof_missing_diagnostic),
    );

    let measure_obligations = calls
        .iter()
        .filter_map(|call| call.measure_decrease.clone())
        .collect::<Vec<_>>();

    let nondecreasing_cycles = nondecreasing_mutual_cycles(&definitions, &calls, &target_spans);
    diagnostics.extend(
        nondecreasing_cycles
            .iter()
            .map(|cycle| mutual_cycle_without_decrease_diagnostic(cycle, &target_spans)),
    );
    diagnostics.sort_by_key(recursion_diagnostic_sort_key);

    let accepted = diagnostics.is_empty();
    let measure_lowering_plans = if accepted {
        measure_lowering_plans(equations, &calls)
    } else {
        Vec::new()
    };
    HumanEquationRecursionBlockResult {
        accepted,
        graph: HumanEquationRecursionGraph {
            definitions,
            calls,
            measure_obligations,
            measure_lowering_plans,
            nondecreasing_cycles,
        },
        diagnostics,
    }
}

pub fn construct_human_equation_decision_tree(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    coverage: &HumanEquationCoverageResult,
    recursion: &HumanEquationRecursionResult,
    budget: HumanEquationBudget,
) -> Result<HumanEquationDecisionTreeResult, HumanEquationDecisionTreeError> {
    assert!(
        coverage.accepted,
        "decision tree construction requires accepted coverage"
    );
    assert!(
        recursion.accepted,
        "decision tree construction requires accepted recursion evidence"
    );

    let reachable_rows = coverage
        .row_statuses
        .iter()
        .filter(|status| status.kind == HumanEquationCoverageRowStatusKind::Reachable)
        .map(|status| status.row_index)
        .collect::<Vec<_>>();
    let constructor_sets = matrix
        .constructors_by_column
        .iter()
        .map(|set| (set.column_index, set))
        .collect::<BTreeMap<_, _>>();
    let recursion_by_row = recursion.graph.calls.iter().cloned().fold(
        BTreeMap::<usize, Vec<HumanEquationRecursiveCall>>::new(),
        |mut calls, call| {
            calls.entry(call.row_index).or_default().push(call);
            calls
        },
    );
    let remaining_columns = matrix
        .columns
        .iter()
        .map(|column| column.index)
        .collect::<Vec<_>>();

    let root = build_decision_tree_node(
        matrix,
        &constructor_sets,
        &recursion_by_row,
        &reachable_rows,
        &remaining_columns,
    );
    let identity_input = decision_tree_identity_input(&root);
    let identity_hash = sha256(identity_input.as_bytes());
    let tree = HumanEquationDecisionTree {
        root,
        identity_input,
        identity_hash,
    };
    let helper_plan = plan_decision_tree_helpers(equation, &tree, budget);
    let stats = decision_tree_node_stats(&tree.root);
    let sidecar_metrics = HumanEquationDecisionTreeMetrics {
        source_equations: equation.rows.len() as u64,
        pattern_matrix_cells: matrix.budget_usage.pattern_matrix_cells,
        expanded_branches: matrix.budget_usage.expanded_branches,
        decision_tree_nodes: stats.node_count,
        generated_helpers: helper_plan.helpers.len() as u64,
        maximum_branch_depth: stats.branch_depth,
    };
    let budget_usage = HumanEquationBudgetUsage {
        pattern_matrix_cells: sidecar_metrics.pattern_matrix_cells,
        expanded_branches: sidecar_metrics.expanded_branches,
        decision_tree_nodes: sidecar_metrics.decision_tree_nodes,
        decision_tree_branch_depth: sidecar_metrics.maximum_branch_depth,
        generated_helpers: sidecar_metrics.generated_helpers,
        generated_core_nodes: 0,
        helper_body_nodes: 0,
        eq_rec_transports: 0,
        generated_certificate_bytes: 0,
    };

    let exceeded = budget.exceeded_fields(budget_usage);
    if !exceeded.is_empty() {
        return Err(HumanEquationDecisionTreeError::GeneratedTermBudgetExceeded(
            Box::new(HumanEquationBudgetError {
                budget,
                requested_usage: budget_usage,
                exceeded,
            }),
        ));
    }

    Ok(HumanEquationDecisionTreeResult {
        tree,
        helper_plan,
        sidecar_metrics,
        budget_usage,
    })
}

pub fn lower_human_equation_decision_tree_to_core(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    decision: &HumanEquationDecisionTreeResult,
    profile: HumanEquationLoweringProfile,
    budget: HumanEquationBudget,
) -> Result<HumanEquationLoweringResult, HumanEquationLoweringError> {
    lower_human_equation_decision_tree_to_core_with_theorems(
        equation,
        matrix,
        decision,
        profile,
        budget,
        HumanEquationTheoremRequest::disabled(),
    )
}

pub fn lower_human_equation_decision_tree_to_core_with_theorems(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    decision: &HumanEquationDecisionTreeResult,
    profile: HumanEquationLoweringProfile,
    budget: HumanEquationBudget,
    theorem_request: HumanEquationTheoremRequest,
) -> Result<HumanEquationLoweringResult, HumanEquationLoweringError> {
    let decision_stats = decision_tree_node_stats(&decision.tree.root);
    let mut budget_usage = HumanEquationBudgetUsage {
        pattern_matrix_cells: matrix.budget_usage.pattern_matrix_cells,
        expanded_branches: matrix.budget_usage.expanded_branches,
        decision_tree_nodes: decision_stats.node_count,
        decision_tree_branch_depth: decision_stats.branch_depth,
        generated_helpers: decision.helper_plan.helpers.len() as u64,
        generated_core_nodes: 0,
        helper_body_nodes: 0,
        eq_rec_transports: 0,
        generated_certificate_bytes: 0,
    };
    let exceeded = budget.exceeded_fields(budget_usage);
    if !exceeded.is_empty() {
        return Err(HumanEquationLoweringError::GeneratedTermBudgetExceeded(
            Box::new(HumanEquationBudgetError {
                budget,
                requested_usage: budget_usage,
                exceeded,
            }),
        ));
    }

    let mut lowerer = HumanEquationCoreLowerer::new(matrix, decision, profile);
    let mut public_context =
        HumanEquationLoweringContext::new(lowerer.profile.public_binders.clone());
    let public_body = lowerer.lower_node(
        &decision.tree.root,
        &mut public_context,
        HelperReferenceMode::Use,
    )?;
    let public_body = lowerer.share_repeated_result_terms(public_body)?;
    let public_ty = close_pi(
        &lowerer.profile.public_binders,
        lowerer.profile.result_type.clone(),
    );
    let public_value = close_lam(&lowerer.profile.public_binders, public_body);

    let mut lowered_decls = lowerer.lower_helper_declarations()?;
    lowered_decls.push((
        Decl::Def {
            name: lowerer.profile.public_name.clone(),
            universe_params: lowerer.profile.universe_params.clone(),
            ty: public_ty,
            value: public_value,
            reducibility: Reducibility::Reducible,
        },
        HumanEquationCoreArtifactKind::PublicDefinition,
    ));

    let mut declarations = Vec::with_capacity(lowered_decls.len());
    let mut artifacts = Vec::with_capacity(lowered_decls.len());
    for (decl, kind) in lowered_decls {
        artifacts.push(lowered_core_artifact(&decl, kind));
        declarations.push(decl);
    }

    budget_usage.eq_rec_transports = lowerer.eq_rec_transports;
    budget_usage.generated_core_nodes = artifacts
        .iter()
        .map(|artifact| artifact.node_count)
        .sum::<u64>();
    budget_usage.helper_body_nodes = helper_body_node_count(&declarations, &artifacts);
    budget_usage.generated_certificate_bytes = declarations
        .iter()
        .map(core_declaration_certificate_bytes)
        .fold(0_u64, u64::saturating_add);
    let exceeded = budget.exceeded_fields(budget_usage);
    if !exceeded.is_empty() {
        return Err(HumanEquationLoweringError::GeneratedTermBudgetExceeded(
            Box::new(HumanEquationBudgetError {
                budget,
                requested_usage: budget_usage,
                exceeded,
            }),
        ));
    }

    let equation_theorems = if theorem_request.enabled {
        let generated_theorems = generate_human_equation_theorems(
            equation,
            matrix,
            decision,
            &lowerer.profile,
            &declarations,
            &artifacts,
            theorem_request,
        )?;
        declarations.extend(generated_theorems.declarations);
        artifacts.extend(generated_theorems.artifacts);
        generated_theorems.plan
    } else {
        HumanEquationTheoremPlan::default()
    };

    let generated_core_nodes = artifacts
        .iter()
        .map(|artifact| artifact.node_count)
        .sum::<u64>();
    let sidecar_metrics = HumanEquationLoweringMetrics {
        source_equations: equation.rows.len() as u64,
        pattern_matrix_cells: matrix.budget_usage.pattern_matrix_cells,
        expanded_branches: matrix.budget_usage.expanded_branches,
        decision_tree_nodes: decision_stats.node_count,
        generated_helpers: decision.helper_plan.helpers.len() as u64,
        generated_equation_theorems: equation_theorems.theorem_specs.len() as u64,
        generated_core_nodes,
        helper_body_nodes: budget_usage.helper_body_nodes,
        eq_rec_transports: lowerer.eq_rec_transports,
        generated_certificate_bytes: declarations
            .iter()
            .map(core_declaration_certificate_bytes)
            .fold(0_u64, u64::saturating_add),
        maximum_branch_depth: decision_stats.branch_depth,
    };

    let identity_input = lowering_bundle_identity_input(&artifacts);
    let identity_hash = sha256(identity_input.as_bytes());
    Ok(HumanEquationLoweringResult {
        bundle: HumanEquationCoreArtifactBundle {
            declarations,
            artifacts,
            identity_input,
            identity_hash,
        },
        equation_theorems,
        sidecar_metrics,
        budget_usage,
    })
}

struct HumanEquationGeneratedTheorems {
    declarations: Vec<Decl>,
    artifacts: Vec<HumanEquationCoreArtifact>,
    plan: HumanEquationTheoremPlan,
}

fn generate_human_equation_theorems(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    decision: &HumanEquationDecisionTreeResult,
    profile: &HumanEquationLoweringProfile,
    lowered_declarations: &[Decl],
    lowered_artifacts: &[HumanEquationCoreArtifact],
    request: HumanEquationTheoremRequest,
) -> Result<HumanEquationGeneratedTheorems, HumanEquationLoweringError> {
    let mut declarations = Vec::new();
    let mut artifacts = Vec::new();
    let mut specs = Vec::new();
    let mut usage = HumanEquationTheoremBudgetUsage::default();

    for row in &matrix.rows {
        let (decl, spec) =
            row_equation_theorem_declaration(equation, matrix, decision, profile, row)?;
        let artifact = lowered_core_artifact(&decl, HumanEquationCoreArtifactKind::EquationTheorem);
        usage.add_declaration(
            artifact.node_count,
            theorem_declaration_certificate_bytes(&decl),
            0,
        );
        declarations.push(decl);
        artifacts.push(artifact);
        specs.push(spec);
    }

    if request.include_helper_split_theorems {
        let helper_decls = lowered_declarations
            .iter()
            .filter_map(|decl| match decl {
                Decl::Def {
                    name,
                    universe_params,
                    ty,
                    ..
                } => lowered_artifacts
                    .iter()
                    .find(|artifact| {
                        artifact.kind == HumanEquationCoreArtifactKind::HelperDefinition
                            && artifact.name == *name
                    })
                    .map(|artifact| (name, universe_params, ty, artifact)),
                _ => None,
            })
            .collect::<Vec<_>>();
        for (helper_name, universe_params, ty, helper_artifact) in helper_decls {
            let (decl, spec) = helper_equation_theorem_declaration(
                equation,
                profile,
                helper_name,
                universe_params,
                ty,
                helper_artifact,
            );
            let artifact =
                lowered_core_artifact(&decl, HumanEquationCoreArtifactKind::EquationTheorem);
            usage.add_declaration(
                artifact.node_count,
                theorem_declaration_certificate_bytes(&decl),
                1,
            );
            declarations.push(decl);
            artifacts.push(artifact);
            specs.push(spec);
        }
    }

    let exceeded = request.budget.exceeded_fields(usage);
    if !exceeded.is_empty() {
        return Err(HumanEquationLoweringError::EquationTheoremBudgetExceeded(
            Box::new(HumanEquationTheoremBudgetError {
                budget: request.budget,
                requested_usage: usage,
                exceeded,
            }),
        ));
    }

    Ok(HumanEquationGeneratedTheorems {
        declarations,
        artifacts,
        plan: HumanEquationTheoremPlan {
            requested: true,
            theorem_specs: specs,
            budget_usage: usage,
        },
    })
}

fn theorem_declaration_certificate_bytes(decl: &Decl) -> u64 {
    match decl {
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        } => {
            let universe_param_bytes = universe_params
                .iter()
                .map(|param| param.len() as u64)
                .fold(0_u64, u64::saturating_add);
            (name.len() as u64)
                .saturating_add(universe_param_bytes)
                .saturating_add(npa_cert::core_expr_canonical_bytes(ty).len() as u64)
                .saturating_add(npa_cert::core_expr_canonical_bytes(proof).len() as u64)
        }
        _ => 0,
    }
}

fn row_equation_theorem_declaration(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    decision: &HumanEquationDecisionTreeResult,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
) -> Result<(Decl, HumanEquationTheoremSpec), HumanEquationLoweringError> {
    if row
        .cells
        .iter()
        .any(|cell| matches!(cell, HumanEquationPatternMatrixCell::Default))
    {
        return Err(HumanEquationLoweringError::EquationTheoremGenerationFailed {
            theorem_name: None,
            reason: format!(
                "row {} uses a default equation branch; constructor-specific computation theorem generation is required",
                row.index
            ),
        });
    }

    let mut bindings = HumanEquationTheoremPatternBindings::default();
    for root in 0..profile.public_binders.len() {
        let root_path = HumanEquationPatternMatrixColumnPath::root(root);
        let root_ty = profile
            .public_binders
            .get(root)
            .map(|binder| binder.ty.clone())
            .ok_or_else(
                || HumanEquationLoweringError::EquationTheoremGenerationFailed {
                    theorem_name: None,
                    reason: format!("missing public binder type for root argument {root}"),
                },
            )?;
        collect_equation_theorem_pattern_binders(
            matrix,
            profile,
            row,
            &root_path,
            root_ty,
            &mut bindings,
        )?;
    }

    let mut args = Vec::new();
    for root in 0..profile.public_binders.len() {
        let root_path = HumanEquationPatternMatrixColumnPath::root(root);
        args.push(build_equation_theorem_pattern_term(
            matrix, profile, row, &root_path, &bindings,
        )?);
    }

    let source_context_map =
        theorem_source_context_map_for_row(matrix, decision, profile, row, &bindings)?;
    let rhs_source = profile
        .row_values
        .get(&row.index)
        .or_else(|| profile.row_values.get(&row.provenance.source_row_index))
        .cloned()
        .ok_or(HumanEquationLoweringError::MissingRowValue {
            row_index: row.index,
            source_row_index: row.provenance.source_row_index,
        })?;
    let result_ty = remap_profile_public_context_expr_for_theorem(
        profile,
        matrix,
        row,
        &bindings,
        &profile.result_type,
    )?;
    let rhs = remap_expr_from_source_context_for_theorem(
        &rhs_source,
        &source_context_map.bvar_terms,
        None,
    )?;
    let lhs = Expr::apps(
        Expr::konst(
            profile.public_name.clone(),
            profile
                .universe_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect::<Vec<_>>(),
        ),
        args,
    );
    let theorem_ty = close_pi(
        &bindings.binders,
        npa_kernel::eq(
            profile.result_universe.clone(),
            result_ty.clone(),
            lhs.clone(),
            rhs.clone(),
        ),
    );
    let theorem_proof = close_lam(
        &bindings.binders,
        npa_kernel::eq_refl(profile.result_universe.clone(), result_ty, lhs.clone()),
    );
    let role = row_equation_theorem_role(matrix, row);
    let relation_identity =
        row_equation_theorem_relation_identity(equation, matrix, row, &lhs, &rhs);
    let name = equation_theorem_name(
        &profile.public_name,
        "row",
        &role,
        row.index as u64,
        &relation_identity,
    );
    let spec = HumanEquationTheoremSpec {
        name: name.clone(),
        source: HumanEquationTheoremSource::RowComputation,
        row_index: Some(row.index),
        source_row_index: Some(row.provenance.source_row_index),
        helper_name: None,
        relation_identity,
        proof_strategy: HumanEquationTheoremProofStrategy::EqReflAfterReduction,
        dependency_names: vec![profile.public_name.clone()],
    };
    Ok((
        Decl::Theorem {
            name,
            universe_params: profile.universe_params.clone(),
            ty: theorem_ty,
            proof: theorem_proof,
        },
        spec,
    ))
}

struct HumanEquationTheoremSourceContextMap {
    bvar_terms: BTreeMap<u32, Expr>,
}

struct HumanEquationTheoremSourceContextBuilder {
    context_len: usize,
    terms_by_ordinal: BTreeMap<usize, Expr>,
}

fn theorem_source_context_map_for_row(
    matrix: &HumanEquationPatternMatrix,
    decision: &HumanEquationDecisionTreeResult,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    bindings: &HumanEquationTheoremPatternBindings,
) -> Result<HumanEquationTheoremSourceContextMap, HumanEquationLoweringError> {
    let mut builder = HumanEquationTheoremSourceContextBuilder {
        context_len: profile.public_binders.len(),
        terms_by_ordinal: BTreeMap::new(),
    };
    for root in 0..profile.public_binders.len() {
        let root_path = HumanEquationPatternMatrixColumnPath::root(root);
        builder.terms_by_ordinal.insert(
            root,
            build_equation_theorem_pattern_term(matrix, profile, row, &root_path, bindings)?,
        );
    }

    let found = collect_theorem_source_context_for_row(
        &decision.tree.root,
        matrix,
        profile,
        row,
        bindings,
        &mut builder,
    )?;
    if !found {
        return Err(
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!(
                    "row {} is not present in the checked equation decision tree",
                    row.index
                ),
            },
        );
    }

    let mut bvar_terms = BTreeMap::new();
    for (ordinal, term) in builder.terms_by_ordinal {
        let index = builder
            .context_len
            .checked_sub(ordinal + 1)
            .ok_or_else(
                || HumanEquationLoweringError::EquationTheoremGenerationFailed {
                    theorem_name: None,
                    reason: format!(
                        "invalid source context ordinal {ordinal} for row {}",
                        row.index
                    ),
                },
            )?;
        bvar_terms.insert(index as u32, term);
    }
    Ok(HumanEquationTheoremSourceContextMap { bvar_terms })
}

fn collect_theorem_source_context_for_row(
    node: &HumanEquationDecisionTreeNode,
    matrix: &HumanEquationPatternMatrix,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    bindings: &HumanEquationTheoremPatternBindings,
    builder: &mut HumanEquationTheoremSourceContextBuilder,
) -> Result<bool, HumanEquationLoweringError> {
    match node {
        HumanEquationDecisionTreeNode::Leaf(leaf) => Ok(leaf.row_index == row.index),
        HumanEquationDecisionTreeNode::Switch(switch) => {
            for branch in &switch.branches {
                if !decision_node_contains_row(&branch.child, row.index) {
                    continue;
                }
                add_theorem_branch_context(
                    switch, branch, matrix, profile, row, bindings, builder,
                )?;
                return collect_theorem_source_context_for_row(
                    &branch.child,
                    matrix,
                    profile,
                    row,
                    bindings,
                    builder,
                );
            }
            if let Some(default_branch) = &switch.default_branch {
                if decision_node_contains_row(default_branch, row.index) {
                    return Err(HumanEquationLoweringError::EquationTheoremGenerationFailed {
                        theorem_name: None,
                        reason: format!(
                            "row {} reaches a default decision branch; constructor-specific computation theorem generation is required",
                            row.index
                        ),
                    });
                }
            }
            Ok(false)
        }
    }
}

fn add_theorem_branch_context(
    switch: &HumanEquationDecisionSwitch,
    branch: &HumanEquationDecisionBranch,
    matrix: &HumanEquationPatternMatrix,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    bindings: &HumanEquationTheoremPatternBindings,
    builder: &mut HumanEquationTheoremSourceContextBuilder,
) -> Result<(), HumanEquationLoweringError> {
    let column = matrix.columns.get(switch.column_index).ok_or_else(|| {
        HumanEquationLoweringError::EquationTheoremGenerationFailed {
            theorem_name: None,
            reason: format!(
                "decision switch references missing theorem column {}",
                switch.column_index
            ),
        }
    })?;
    let constructor_arity =
        theorem_row_constructor_arity(matrix, row, &column.path, &branch.constructor)?;
    let constructor = theorem_constructor_profile(
        profile,
        &branch.constructor.constructor_key,
        constructor_arity,
    )?;
    let minor_start = builder.context_len;
    for argument_index in 0..constructor_arity {
        let term = theorem_constructor_field_term(
            matrix,
            profile,
            row,
            &column.path,
            &branch.constructor.constructor_key,
            argument_index,
            bindings,
        )?;
        builder
            .terms_by_ordinal
            .insert(minor_start + argument_index, term);
    }

    for minor_index in constructor_arity..constructor.minor_binders.len() {
        if profile.public_binders.len() != 1 {
            continue;
        }
        let Some(recursive_argument) =
            theorem_recursive_argument_index(constructor, constructor_arity, minor_index)
        else {
            continue;
        };
        let recursive_arg = theorem_constructor_field_term(
            matrix,
            profile,
            row,
            &column.path,
            &branch.constructor.constructor_key,
            recursive_argument,
            bindings,
        )?;
        builder.terms_by_ordinal.insert(
            minor_start + minor_index,
            theorem_recursive_call_term(profile, matrix, row, column, recursive_arg, bindings)?,
        );
    }

    builder.context_len = builder
        .context_len
        .saturating_add(constructor.minor_binders.len());
    Ok(())
}

fn theorem_row_constructor_arity(
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
    path: &HumanEquationPatternMatrixColumnPath,
    constructor: &HumanEquationPatternMatrixConstructor,
) -> Result<usize, HumanEquationLoweringError> {
    let Some(HumanEquationPatternMatrixCell::Constructor {
        constructor_key,
        arity,
        ..
    }) = row_cell_for_path(matrix, row, path)
    else {
        return Err(
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!(
                    "row {} does not select constructor {} at decision column {}",
                    row.index,
                    constructor.constructor_key,
                    path.identity()
                ),
            },
        );
    };
    if constructor_key != &constructor.constructor_key {
        return Err(
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!(
                    "row {} constructor {} does not match decision constructor {} at column {}",
                    row.index,
                    constructor_key,
                    constructor.constructor_key,
                    path.identity()
                ),
            },
        );
    }
    Ok(*arity)
}

fn theorem_constructor_field_term(
    matrix: &HumanEquationPatternMatrix,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    path: &HumanEquationPatternMatrixColumnPath,
    constructor_key: &str,
    argument_index: usize,
    bindings: &HumanEquationTheoremPatternBindings,
) -> Result<Expr, HumanEquationLoweringError> {
    if let Some(child_path) = theorem_child_path(matrix, path, constructor_key, argument_index) {
        build_equation_theorem_pattern_term(matrix, profile, row, &child_path, bindings)
    } else {
        bindings.bvar_for(&theorem_missing_child_key(
            path,
            constructor_key,
            argument_index,
        ))
    }
}

fn theorem_recursive_argument_index(
    constructor: &HumanEquationConstructorLoweringProfile,
    arity: usize,
    minor_index: usize,
) -> Option<usize> {
    let binder_name = constructor.minor_binders.get(minor_index)?.name.as_str();
    let stem = binder_name.strip_suffix("_ih")?;
    constructor
        .minor_binders
        .iter()
        .take(arity)
        .position(|binder| binder.name == stem)
        .or_else(|| arity.checked_sub(1))
}

fn theorem_recursive_call_term(
    profile: &HumanEquationLoweringProfile,
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
    recursive_column: &HumanEquationPatternMatrixColumn,
    recursive_arg: Expr,
    bindings: &HumanEquationTheoremPatternBindings,
) -> Result<Expr, HumanEquationLoweringError> {
    if profile.public_binders.len() != 1 {
        return Err(HumanEquationLoweringError::EquationTheoremGenerationFailed {
            theorem_name: None,
            reason: "recursive equation theorem RHS remapping currently supports one public recursive argument".to_owned(),
        });
    }
    let mut args = Vec::new();
    for root in 0..profile.public_binders.len() {
        if root == recursive_column.path.root {
            args.push(recursive_arg.clone());
        } else {
            let root_path = HumanEquationPatternMatrixColumnPath::root(root);
            args.push(build_equation_theorem_pattern_term(
                matrix, profile, row, &root_path, bindings,
            )?);
        }
    }
    Ok(Expr::apps(
        Expr::konst(
            profile.public_name.clone(),
            profile
                .universe_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect::<Vec<_>>(),
        ),
        args,
    ))
}

fn decision_node_contains_row(node: &HumanEquationDecisionTreeNode, row_index: usize) -> bool {
    match node {
        HumanEquationDecisionTreeNode::Leaf(leaf) => leaf.row_index == row_index,
        HumanEquationDecisionTreeNode::Switch(switch) => {
            switch
                .branches
                .iter()
                .any(|branch| decision_node_contains_row(&branch.child, row_index))
                || switch
                    .default_branch
                    .as_deref()
                    .is_some_and(|child| decision_node_contains_row(child, row_index))
        }
    }
}

fn remap_profile_public_context_expr_for_theorem(
    profile: &HumanEquationLoweringProfile,
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
    bindings: &HumanEquationTheoremPatternBindings,
    expr: &Expr,
) -> Result<Expr, HumanEquationLoweringError> {
    let public_context_len = profile.public_binders.len();
    let mut bvar_terms = BTreeMap::new();
    for root in 0..public_context_len {
        let root_path = HumanEquationPatternMatrixColumnPath::root(root);
        let index = public_context_len.checked_sub(root + 1).ok_or_else(|| {
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!("invalid public binder ordinal {root}"),
            }
        })?;
        bvar_terms.insert(
            index as u32,
            build_equation_theorem_pattern_term(matrix, profile, row, &root_path, bindings)?,
        );
    }
    remap_expr_from_source_context_for_theorem(expr, &bvar_terms, None)
}

fn remap_expr_from_source_context_for_theorem(
    expr: &Expr,
    bvar_terms: &BTreeMap<u32, Expr>,
    theorem_name: Option<&str>,
) -> Result<Expr, HumanEquationLoweringError> {
    remap_expr_from_source_context_at_depth(expr, bvar_terms, 0, theorem_name)
}

fn remap_expr_from_source_context_at_depth(
    expr: &Expr,
    bvar_terms: &BTreeMap<u32, Expr>,
    depth: u32,
    theorem_name: Option<&str>,
) -> Result<Expr, HumanEquationLoweringError> {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => Ok(expr.clone()),
        Expr::BVar(index) if *index < depth => Ok(expr.clone()),
        Expr::BVar(index) => {
            let source_index = index - depth;
            let Some(term) = bvar_terms.get(&source_index) else {
                return Err(
                    HumanEquationLoweringError::EquationTheoremGenerationFailed {
                        theorem_name: theorem_name.map(str::to_owned),
                        reason: format!(
                        "cannot remap source bound variable {source_index} into theorem context"
                    ),
                    },
                );
            };
            npa_kernel::subst::shift(term, depth as i32, 0).map_err(|err| {
                HumanEquationLoweringError::EquationTheoremGenerationFailed {
                    theorem_name: theorem_name.map(str::to_owned),
                    reason: format!("failed to shift theorem replacement term: {err:?}"),
                }
            })
        }
        Expr::App(fun, arg) => Ok(Expr::app(
            remap_expr_from_source_context_at_depth(fun, bvar_terms, depth, theorem_name)?,
            remap_expr_from_source_context_at_depth(arg, bvar_terms, depth, theorem_name)?,
        )),
        Expr::Lam { binder, ty, body } => Ok(Expr::lam(
            binder.clone(),
            remap_expr_from_source_context_at_depth(ty, bvar_terms, depth, theorem_name)?,
            remap_expr_from_source_context_at_depth(body, bvar_terms, depth + 1, theorem_name)?,
        )),
        Expr::Pi { binder, ty, body } => Ok(Expr::pi(
            binder.clone(),
            remap_expr_from_source_context_at_depth(ty, bvar_terms, depth, theorem_name)?,
            remap_expr_from_source_context_at_depth(body, bvar_terms, depth + 1, theorem_name)?,
        )),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => Ok(Expr::let_in(
            binder.clone(),
            remap_expr_from_source_context_at_depth(ty, bvar_terms, depth, theorem_name)?,
            remap_expr_from_source_context_at_depth(value, bvar_terms, depth, theorem_name)?,
            remap_expr_from_source_context_at_depth(body, bvar_terms, depth + 1, theorem_name)?,
        )),
    }
}

fn helper_equation_theorem_declaration(
    equation: &HumanResolvedEquationItem,
    profile: &HumanEquationLoweringProfile,
    helper_name: &str,
    universe_params: &[String],
    helper_ty: &Expr,
    helper_artifact: &HumanEquationCoreArtifact,
) -> (Decl, HumanEquationTheoremSpec) {
    let helper_ref = Expr::konst(
        helper_name.to_owned(),
        universe_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let theorem_ty = npa_kernel::eq(
        profile.result_universe.clone(),
        helper_ty.clone(),
        helper_ref.clone(),
        helper_ref.clone(),
    );
    let theorem_proof = npa_kernel::eq_refl(
        profile.result_universe.clone(),
        helper_ty.clone(),
        helper_ref,
    );
    let relation_identity = format!(
        "helper:{}:{}:{}",
        equation.source_name.as_dotted(),
        helper_name,
        hash_hex(&helper_artifact.core_hash)
    );
    let name = equation_theorem_name(
        &profile.public_name,
        "helper",
        helper_name,
        0,
        &relation_identity,
    );
    let spec = HumanEquationTheoremSpec {
        name: name.clone(),
        source: HumanEquationTheoremSource::HelperSplit,
        row_index: None,
        source_row_index: None,
        helper_name: Some(helper_name.to_owned()),
        relation_identity,
        proof_strategy: HumanEquationTheoremProofStrategy::HelperSelfRefl,
        dependency_names: vec![helper_name.to_owned()],
    };
    (
        Decl::Theorem {
            name,
            universe_params: universe_params.to_vec(),
            ty: theorem_ty,
            proof: theorem_proof,
        },
        spec,
    )
}

#[derive(Clone, Debug, Default)]
struct HumanEquationTheoremPatternBindings {
    binders: Vec<HumanEquationLoweringBinder>,
    ordinals_by_key: BTreeMap<String, usize>,
}

impl HumanEquationTheoremPatternBindings {
    fn ensure(&mut self, key: String, name: String, ty: Expr) {
        if self.ordinals_by_key.contains_key(&key) {
            return;
        }
        let ordinal = self.binders.len();
        self.binders.push(HumanEquationLoweringBinder { name, ty });
        self.ordinals_by_key.insert(key, ordinal);
    }

    fn bvar_for(&self, key: &str) -> Result<Expr, HumanEquationLoweringError> {
        let Some(ordinal) = self.ordinals_by_key.get(key).copied() else {
            return Err(
                HumanEquationLoweringError::EquationTheoremGenerationFailed {
                    theorem_name: None,
                    reason: format!("missing equation theorem binder for {key}"),
                },
            );
        };
        let index = self.binders.len().checked_sub(ordinal + 1).ok_or_else(|| {
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!("invalid equation theorem binder ordinal for {key}"),
            }
        })?;
        Ok(Expr::bvar(index as u32))
    }
}

fn collect_equation_theorem_pattern_binders(
    matrix: &HumanEquationPatternMatrix,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    path: &HumanEquationPatternMatrixColumnPath,
    expected_ty: Expr,
    bindings: &mut HumanEquationTheoremPatternBindings,
) -> Result<(), HumanEquationLoweringError> {
    match row_cell_for_path(matrix, row, path) {
        Some(HumanEquationPatternMatrixCell::Constructor {
            constructor_key,
            arity,
            ..
        }) => {
            let constructor = theorem_constructor_profile(profile, constructor_key, *arity)?;
            for argument_index in 0..*arity {
                let ty = constructor.minor_binders[argument_index].ty.clone();
                if let Some(child_path) =
                    theorem_child_path(matrix, path, constructor_key, argument_index)
                {
                    collect_equation_theorem_pattern_binders(
                        matrix,
                        profile,
                        row,
                        &child_path,
                        ty,
                        bindings,
                    )?;
                } else {
                    let key = theorem_missing_child_key(path, constructor_key, argument_index);
                    bindings.ensure(key, format!("arg{argument_index}"), ty);
                }
            }
        }
        Some(HumanEquationPatternMatrixCell::Variable { slot }) => {
            bindings.ensure(theorem_variable_key(*slot), format!("x{slot}"), expected_ty);
        }
        Some(HumanEquationPatternMatrixCell::Default) | None => {
            bindings.ensure(
                theorem_path_key(path),
                format!("arg{}", path.root),
                expected_ty,
            );
        }
        Some(HumanEquationPatternMatrixCell::Unavailable { .. }) => {}
    }
    Ok(())
}

fn build_equation_theorem_pattern_term(
    matrix: &HumanEquationPatternMatrix,
    profile: &HumanEquationLoweringProfile,
    row: &HumanEquationPatternMatrixRow,
    path: &HumanEquationPatternMatrixColumnPath,
    bindings: &HumanEquationTheoremPatternBindings,
) -> Result<Expr, HumanEquationLoweringError> {
    let term = match row_cell_for_path(matrix, row, path) {
        Some(HumanEquationPatternMatrixCell::Constructor {
            constructor,
            constructor_key,
            arity,
        }) => {
            theorem_constructor_profile(profile, constructor_key, *arity)?;
            let mut args = Vec::new();
            for argument_index in 0..*arity {
                if let Some(child_path) =
                    theorem_child_path(matrix, path, constructor_key, argument_index)
                {
                    args.push(build_equation_theorem_pattern_term(
                        matrix,
                        profile,
                        row,
                        &child_path,
                        bindings,
                    )?);
                } else {
                    args.push(bindings.bvar_for(&theorem_missing_child_key(
                        path,
                        constructor_key,
                        argument_index,
                    ))?);
                }
            }
            Ok(Expr::apps(
                Expr::konst(core_name_for_equation_global_ref(constructor), Vec::new()),
                args,
            ))
        }
        Some(HumanEquationPatternMatrixCell::Variable { slot }) => {
            bindings.bvar_for(&theorem_variable_key(*slot))
        }
        Some(HumanEquationPatternMatrixCell::Default) | None => {
            bindings.bvar_for(&theorem_path_key(path))
        }
        Some(HumanEquationPatternMatrixCell::Unavailable {
            blocked_by_constructor_key,
        }) => Err(
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!(
                    "cannot generate theorem term for unavailable branch blocked by {blocked_by_constructor_key}"
                ),
            },
        ),
    }?;
    Ok(term)
}

fn row_cell_for_path<'a>(
    matrix: &'a HumanEquationPatternMatrix,
    row: &'a HumanEquationPatternMatrixRow,
    path: &HumanEquationPatternMatrixColumnPath,
) -> Option<&'a HumanEquationPatternMatrixCell> {
    matrix
        .columns
        .iter()
        .find(|column| &column.path == path)
        .and_then(|column| row.cells.get(column.index))
}

fn theorem_constructor_profile<'a>(
    profile: &'a HumanEquationLoweringProfile,
    constructor_key: &str,
    arity: usize,
) -> Result<&'a HumanEquationConstructorLoweringProfile, HumanEquationLoweringError> {
    let constructor = profile
        .recursors
        .iter()
        .flat_map(|recursor| recursor.constructors.iter())
        .find(|constructor| constructor.constructor_key == constructor_key)
        .ok_or_else(
            || HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!("missing theorem constructor profile for {constructor_key}"),
            },
        )?;
    if constructor.minor_binders.len() < arity {
        return Err(
            HumanEquationLoweringError::EquationTheoremGenerationFailed {
                theorem_name: None,
                reason: format!(
                    "constructor profile for {constructor_key} has fewer binders than arity {arity}"
                ),
            },
        );
    }
    Ok(constructor)
}

fn theorem_child_path(
    matrix: &HumanEquationPatternMatrix,
    parent: &HumanEquationPatternMatrixColumnPath,
    constructor_key: &str,
    argument_index: usize,
) -> Option<HumanEquationPatternMatrixColumnPath> {
    matrix
        .columns
        .iter()
        .map(|column| &column.path)
        .find(|path| {
            path.root == parent.root
                && path.segments.len() == parent.segments.len() + 1
                && path.segments.starts_with(&parent.segments)
                && path.segments.last().is_some_and(|segment| {
                    segment.constructor_key == constructor_key
                        && segment.argument_index == argument_index
                })
        })
        .cloned()
}

fn theorem_variable_key(slot: usize) -> String {
    format!("slot:{slot}")
}

fn theorem_path_key(path: &HumanEquationPatternMatrixColumnPath) -> String {
    format!("path:{}", path.identity())
}

fn theorem_missing_child_key(
    path: &HumanEquationPatternMatrixColumnPath,
    constructor_key: &str,
    argument_index: usize,
) -> String {
    format!(
        "missing:{}:{}:{argument_index}",
        path.identity(),
        constructor_key
    )
}

fn row_equation_theorem_role(
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
) -> String {
    row.cells
        .iter()
        .find_map(|cell| match cell {
            HumanEquationPatternMatrixCell::Constructor { constructor, .. } => {
                Some(sanitize_theorem_name_component(
                    core_name_for_equation_global_ref(constructor)
                        .rsplit('.')
                        .next()
                        .unwrap_or("constructor"),
                ))
            }
            HumanEquationPatternMatrixCell::Default => Some("default".to_owned()),
            HumanEquationPatternMatrixCell::Variable { .. }
            | HumanEquationPatternMatrixCell::Unavailable { .. } => None,
        })
        .unwrap_or_else(|| {
            matrix
                .columns
                .first()
                .map(|column| sanitize_theorem_name_component(&column.identity))
                .unwrap_or_else(|| "row".to_owned())
        })
}

fn row_equation_theorem_relation_identity(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
    lhs: &Expr,
    rhs: &Expr,
) -> String {
    let mut input = String::from("npa.frontend.equation.theorem.row-relation.v1\n");
    let _ = writeln!(input, "equation:{}", equation.semantic_identity.value);
    let _ = writeln!(input, "matrix:{}", hash_hex(&matrix.identity_hash));
    let _ = writeln!(input, "row:{}", row.index);
    let _ = writeln!(input, "source-row:{}", row.provenance.source_row_index);
    let _ = writeln!(input, "value:{}", row.value_identity);
    let _ = writeln!(input, "lhs:{}", hash_hex(&npa_cert::core_expr_hash(lhs)));
    let _ = writeln!(input, "rhs:{}", hash_hex(&npa_cert::core_expr_hash(rhs)));
    format!("row-relation:{}", hash_hex(&sha256(input.as_bytes())))
}

fn equation_theorem_name(
    public_name: &str,
    source: &str,
    role: &str,
    ordinal: u64,
    relation_identity: &str,
) -> String {
    format!(
        "{}.eqn.{}.{}.n{:04}.h{}",
        public_name,
        sanitize_theorem_name_component(source),
        sanitize_theorem_name_component(role),
        ordinal,
        short_hash(relation_identity)
    )
}

fn sanitize_theorem_name_component(input: &str) -> String {
    let mut component = input
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect::<String>();
    if component.is_empty() {
        component.push('x');
    }
    if component
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_digit())
    {
        component.insert(0, 'x');
    }
    component
}

fn short_hash(input: &str) -> String {
    hash_hex(&sha256(input.as_bytes()))[..12].to_owned()
}

fn core_name_for_equation_global_ref(reference: &HumanGlobalRef) -> String {
    match reference {
        HumanGlobalRef::Imported { name, .. }
        | HumanGlobalRef::Builtin { name, .. }
        | HumanGlobalRef::Local { name, .. }
        | HumanGlobalRef::LocalGenerated { name, .. } => name.as_dotted(),
    }
}

pub fn normalize_human_equation_pattern_matrix(
    equation: &HumanResolvedEquationItem,
    budget: HumanEquationBudget,
) -> Result<HumanEquationPatternMatrix, HumanEquationMatrixError> {
    normalize_human_equation_pattern_matrix_with_constructor_order(
        equation,
        &HumanEquationConstructorOrder::default(),
        budget,
    )
}

pub fn normalize_human_equation_pattern_matrix_with_constructor_order(
    equation: &HumanResolvedEquationItem,
    constructor_order: &HumanEquationConstructorOrder,
    budget: HumanEquationBudget,
) -> Result<HumanEquationPatternMatrix, HumanEquationMatrixError> {
    let mut paths = BTreeSet::new();
    let mut constructors_by_path =
        BTreeMap::<HumanEquationPatternMatrixColumnPath, BTreeMap<String, HumanGlobalRef>>::new();

    for row in &equation.rows {
        let HumanResolvedEquationRow::Patterns { patterns, .. } = row else {
            continue;
        };
        for (root, pattern) in patterns.iter().enumerate() {
            collect_pattern_columns(
                HumanEquationPatternMatrixColumnPath::root(root),
                pattern,
                constructor_order,
                &mut paths,
                &mut constructors_by_path,
            );
        }
    }

    let columns = paths
        .into_iter()
        .enumerate()
        .map(|(index, path)| {
            let identity = path.identity();
            HumanEquationPatternMatrixColumn {
                index,
                path,
                identity,
            }
        })
        .collect::<Vec<_>>();
    let column_indexes = columns
        .iter()
        .map(|column| (column.path.clone(), column.index))
        .collect::<BTreeMap<_, _>>();
    let constructors_by_column =
        constructor_sets_by_column(&constructors_by_path, &column_indexes, constructor_order);

    let rows = equation
        .rows
        .iter()
        .enumerate()
        .map(|(index, row)| normalize_row(index, row, &columns))
        .collect::<Vec<_>>();
    let budget_usage =
        equation_pattern_matrix_budget_usage(&rows, &constructors_by_column, columns.len());

    let exceeded = budget.exceeded_fields(budget_usage);
    if !exceeded.is_empty() {
        return Err(HumanEquationMatrixError::GeneratedTermBudgetExceeded(
            Box::new(HumanEquationBudgetError {
                budget,
                requested_usage: budget_usage,
                exceeded,
            }),
        ));
    }

    let identity_input = matrix_identity_input(&columns, &rows, &constructors_by_column);
    let identity_hash = sha256(identity_input.as_bytes());

    Ok(HumanEquationPatternMatrix {
        columns,
        rows,
        constructors_by_column,
        identity_input,
        identity_hash,
        budget_usage,
    })
}

#[derive(Clone, Debug, Default)]
struct RecursionBranchContext {
    visible_subterms: BTreeMap<String, HumanEquationConstructorFieldPath>,
}

fn recursive_calls_for_equation(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
    target_names: &BTreeMap<String, String>,
) -> Vec<HumanEquationRecursiveCall> {
    let caller_identity = recursion_global_identity(&equation.target);
    let caller = target_names
        .get(&caller_identity)
        .cloned()
        .unwrap_or_else(|| equation.source_name.as_dotted());
    let branch_contexts = recursion_branch_contexts(equation, matrix);
    let mut calls = Vec::new();

    for row in &matrix.rows {
        let Some(source_row) = equation.rows.get(row.provenance.source_row_index) else {
            continue;
        };
        let value_identity = match source_row {
            HumanResolvedEquationRow::Patterns { value_identity, .. }
            | HumanResolvedEquationRow::Default { value_identity, .. } => value_identity,
        };
        let value_expr = parse_recursion_expr(value_identity);
        let mut extracted = Vec::new();
        collect_recursive_call_occurrences(&value_expr, target_names, &mut extracted);
        let context = branch_contexts.get(&row.index).cloned().unwrap_or_default();

        for occurrence in extracted {
            let decrease_evidence =
                structural_decrease_evidence(&occurrence.argument_mapping, &context);
            let callee = target_names
                .get(&occurrence.callee_identity)
                .cloned()
                .unwrap_or_else(|| occurrence.callee_identity.clone());
            let measure_decrease = equation.termination.as_ref().map(|termination| {
                measure_decrease_obligation(
                    equation,
                    termination,
                    &occurrence,
                    &caller,
                    &callee,
                    row.index,
                )
            });
            calls.push(HumanEquationRecursiveCall {
                caller: caller.clone(),
                callee,
                row_index: row.index,
                primary_span: row.provenance.source_span,
                call_identity: occurrence.call_identity,
                argument_mapping: occurrence.argument_mapping,
                decrease_evidence,
                measure_decrease,
            });
        }
    }

    calls
}

fn recursion_branch_contexts(
    equation: &HumanResolvedEquationItem,
    matrix: &HumanEquationPatternMatrix,
) -> BTreeMap<usize, RecursionBranchContext> {
    let mut contexts = BTreeMap::new();
    for row in &matrix.rows {
        let Some(HumanResolvedEquationRow::Patterns { patterns, .. }) =
            equation.rows.get(row.provenance.source_row_index)
        else {
            contexts.insert(row.index, RecursionBranchContext::default());
            continue;
        };
        contexts.insert(row.index, recursion_branch_context(patterns));
    }
    contexts
}

fn recursion_branch_context(patterns: &[HumanResolvedPattern]) -> RecursionBranchContext {
    let mut visible = Vec::new();
    for (root, pattern) in patterns.iter().enumerate() {
        collect_visible_structural_subterms(
            pattern,
            HumanEquationConstructorFieldPath {
                root_parameter: root,
                segments: Vec::new(),
                identity: format!("root:{root}"),
            },
            &mut visible,
        );
    }

    let Some(max_slot) = visible.iter().map(|(slot, _)| *slot).max() else {
        return RecursionBranchContext::default();
    };
    let visible_subterms = visible
        .into_iter()
        .map(|(slot, path)| (format!("local:{}", max_slot - slot), path))
        .collect::<BTreeMap<_, _>>();
    RecursionBranchContext { visible_subterms }
}

fn collect_visible_structural_subterms(
    pattern: &HumanResolvedPattern,
    path: HumanEquationConstructorFieldPath,
    visible: &mut Vec<(usize, HumanEquationConstructorFieldPath)>,
) {
    match pattern {
        HumanResolvedPattern::Variable { slot } => {
            if !path.segments.is_empty() {
                visible.push((*slot, path));
            }
        }
        HumanResolvedPattern::Constructor { constructor, args } => {
            let constructor_key = human_equation_global_ref_sort_key(constructor);
            for (argument_index, arg) in args.iter().enumerate() {
                let mut child_segments = path.segments.clone();
                child_segments.push(HumanEquationConstructorFieldSegment {
                    constructor_key: constructor_key.clone(),
                    argument_index,
                });
                let child = HumanEquationConstructorFieldPath {
                    root_parameter: path.root_parameter,
                    identity: constructor_field_path_identity(path.root_parameter, &child_segments),
                    segments: child_segments,
                };
                collect_visible_structural_subterms(arg, child, visible);
            }
        }
    }
}

fn constructor_field_path_identity(
    root_parameter: usize,
    segments: &[HumanEquationConstructorFieldSegment],
) -> String {
    let mut identity = format!("root:{root_parameter}");
    for segment in segments {
        let _ = write!(
            identity,
            "/ctor:{}/arg:{}",
            segment.constructor_key, segment.argument_index
        );
    }
    identity
}

fn structural_decrease_evidence(
    argument_mapping: &[String],
    context: &RecursionBranchContext,
) -> Option<HumanEquationStructuralDecreaseEvidence> {
    argument_mapping
        .iter()
        .enumerate()
        .find_map(|(parameter, argument)| {
            context.visible_subterms.get(argument).cloned().map(|path| {
                HumanEquationStructuralDecreaseEvidence {
                    decreasing_parameter: parameter,
                    constructor_field_path: path,
                }
            })
        })
}

fn measure_decrease_obligation(
    equation: &HumanResolvedEquationItem,
    termination: &HumanResolvedTerminationAnnotation,
    occurrence: &RecursiveCallOccurrence,
    caller: &str,
    callee: &str,
    row_index: usize,
) -> HumanEquationMeasureDecreaseObligation {
    let caller_measure_identity = termination.measure_identity.clone();
    let callee_measure_identity = callee_measure_identity(
        &termination.measure_identity,
        equation.parameter_type_identities.len(),
        &occurrence.argument_mapping,
    );
    let relation_identity = format!("Nat.lt({callee_measure_identity},{caller_measure_identity})");
    let identity = measure_decrease_obligation_identity(MeasureDecreaseObligationIdentityInput {
        measure_identity: &termination.measure_identity,
        caller_measure_identity: &caller_measure_identity,
        callee_measure_identity: &callee_measure_identity,
        relation_identity: &relation_identity,
        caller,
        callee,
        row_index,
        call_identity: &occurrence.call_identity,
    });
    let proof = termination
        .checked_decrease_proofs
        .get(&identity)
        .or_else(|| {
            termination
                .checked_decrease_proofs
                .get(&occurrence.call_identity)
        })
        .cloned();
    HumanEquationMeasureDecreaseObligation {
        identity,
        caller: caller.to_owned(),
        callee: callee.to_owned(),
        row_index,
        call_identity: occurrence.call_identity.clone(),
        measure_identity: termination.measure_identity.clone(),
        caller_measure_identity,
        callee_measure_identity,
        relation_identity,
        proof,
    }
}

fn callee_measure_identity(
    measure_identity: &str,
    parameter_count: usize,
    argument_mapping: &[String],
) -> String {
    if let Some(local_index) = parse_local_identity(measure_identity) {
        if let Some(parameter) = parameter_count.checked_sub(local_index + 1) {
            if let Some(argument) = argument_mapping.get(parameter) {
                return argument.clone();
            }
        }
    }
    format!(
        "measure-subst({measure_identity};args:{})",
        argument_mapping.join(",")
    )
}

fn parse_local_identity(identity: &str) -> Option<usize> {
    identity.strip_prefix("local:")?.parse().ok()
}

struct MeasureDecreaseObligationIdentityInput<'a> {
    measure_identity: &'a str,
    caller_measure_identity: &'a str,
    callee_measure_identity: &'a str,
    relation_identity: &'a str,
    caller: &'a str,
    callee: &'a str,
    row_index: usize,
    call_identity: &'a str,
}

fn measure_decrease_obligation_identity(
    input: MeasureDecreaseObligationIdentityInput<'_>,
) -> String {
    let mut payload = String::from("npa.frontend.equation.measure-decrease-obligation.v0\n");
    let _ = writeln!(payload, "caller:{}", input.caller);
    let _ = writeln!(payload, "callee:{}", input.callee);
    let _ = writeln!(payload, "row:{}", input.row_index);
    let _ = writeln!(payload, "measure:{}", input.measure_identity);
    let _ = writeln!(payload, "caller-measure:{}", input.caller_measure_identity);
    let _ = writeln!(payload, "callee-measure:{}", input.callee_measure_identity);
    let _ = writeln!(payload, "relation:{}", input.relation_identity);
    let _ = writeln!(payload, "call:{}", input.call_identity);
    format!(
        "measure-obligation:{}",
        hash_hex(&sha256(payload.as_bytes()))
    )
}

fn measure_type_is_nat(identity: &str) -> bool {
    identity == "Nat"
        || identity.ends_with(":Nat")
        || identity.contains(":Nat:")
        || identity.ends_with(".Nat")
        || identity.contains(".Nat:")
}

fn measure_lowering_plans(
    equations: &[HumanResolvedEquationItem],
    calls: &[HumanEquationRecursiveCall],
) -> Vec<HumanEquationMeasureLoweringPlan> {
    let mut plans = equations
        .iter()
        .filter_map(|equation| {
            let termination = equation.termination.as_ref()?;
            if !measure_type_is_nat(&termination.measure_type_identity) {
                return None;
            }
            let definition_name = equation.source_name.as_dotted();
            let obligation_identities = calls
                .iter()
                .filter(|call| call.caller == definition_name)
                .filter_map(|call| call.measure_decrease.as_ref())
                .map(|obligation| obligation.identity.clone())
                .collect::<Vec<_>>();
            Some(HumanEquationMeasureLoweringPlan {
                strategy: HumanEquationMeasureLoweringStrategy::FuelStyleEncoding,
                definition_name,
                measure_identity: termination.measure_identity.clone(),
                obligation_identities,
            })
        })
        .collect::<Vec<_>>();
    plans.sort_by(|lhs, rhs| {
        lhs.definition_name
            .cmp(&rhs.definition_name)
            .then_with(|| lhs.measure_identity.cmp(&rhs.measure_identity))
            .then_with(|| lhs.obligation_identities.cmp(&rhs.obligation_identities))
    });
    plans
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RecursiveCallOccurrence {
    callee_identity: String,
    call_identity: String,
    argument_mapping: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RecursionExpr {
    Global {
        identity: String,
    },
    Local {
        identity: String,
    },
    App {
        identity: String,
        func: Box<RecursionExpr>,
        arg: Box<RecursionExpr>,
    },
    Other {
        identity: String,
        children: Vec<RecursionExpr>,
    },
}

impl RecursionExpr {
    fn identity(&self) -> &str {
        match self {
            Self::Global { identity }
            | Self::Local { identity }
            | Self::App { identity, .. }
            | Self::Other { identity, .. } => identity,
        }
    }
}

fn collect_recursive_call_occurrences(
    expr: &RecursionExpr,
    target_names: &BTreeMap<String, String>,
    calls: &mut Vec<RecursiveCallOccurrence>,
) {
    match expr {
        RecursionExpr::App { func, arg, .. } => {
            let (head, args) = flatten_recursion_application(expr);
            if let RecursionExpr::Global { identity } = head {
                if target_names.contains_key(identity) {
                    calls.push(RecursiveCallOccurrence {
                        callee_identity: identity.clone(),
                        call_identity: expr.identity().to_owned(),
                        argument_mapping: args
                            .iter()
                            .map(|arg| arg.identity().to_owned())
                            .collect(),
                    });
                    for arg in args {
                        collect_recursive_call_occurrences(arg, target_names, calls);
                    }
                    return;
                }
            }
            collect_recursive_call_occurrences(func, target_names, calls);
            collect_recursive_call_occurrences(arg, target_names, calls);
        }
        RecursionExpr::Global { identity } => {
            if target_names.contains_key(identity) {
                calls.push(RecursiveCallOccurrence {
                    callee_identity: identity.clone(),
                    call_identity: identity.clone(),
                    argument_mapping: Vec::new(),
                });
            }
        }
        RecursionExpr::Local { .. } => {}
        RecursionExpr::Other { children, .. } => {
            for child in children {
                collect_recursive_call_occurrences(child, target_names, calls);
            }
        }
    }
}

fn flatten_recursion_application(expr: &RecursionExpr) -> (&RecursionExpr, Vec<&RecursionExpr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let RecursionExpr::App { func, arg, .. } = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}

fn parse_recursion_expr(input: &str) -> RecursionExpr {
    if input.starts_with("global:") {
        return RecursionExpr::Global {
            identity: input.to_owned(),
        };
    }
    if input.starts_with("local:") {
        return RecursionExpr::Local {
            identity: input.to_owned(),
        };
    }
    if let Some(children) = parse_parenthesized_children(input, "app(") {
        if children.len() == 2 {
            return RecursionExpr::App {
                identity: input.to_owned(),
                func: Box::new(parse_recursion_expr(&children[0])),
                arg: Box::new(parse_recursion_expr(&children[1])),
            };
        }
    }
    if let Some(children) = parse_parenthesized_children(input, "annot(") {
        return RecursionExpr::Other {
            identity: input.to_owned(),
            children: children
                .into_iter()
                .map(|child| parse_recursion_expr(&child))
                .collect(),
        };
    }
    if let Some(children) = parse_parenthesized_children(input, "arrow(") {
        return RecursionExpr::Other {
            identity: input.to_owned(),
            children: children
                .into_iter()
                .map(|child| parse_recursion_expr(&child))
                .collect(),
        };
    }
    if let Some(children) = parse_notation_children(input) {
        return RecursionExpr::Other {
            identity: input.to_owned(),
            children: children
                .into_iter()
                .map(|child| parse_recursion_expr(&child))
                .collect(),
        };
    }
    if let Some(children) = parse_let_children(input) {
        return RecursionExpr::Other {
            identity: input.to_owned(),
            children,
        };
    }
    if let Some(children) =
        parse_binder_children(input, "lam(").or_else(|| parse_binder_children(input, "pi("))
    {
        return RecursionExpr::Other {
            identity: input.to_owned(),
            children,
        };
    }
    RecursionExpr::Other {
        identity: input.to_owned(),
        children: Vec::new(),
    }
}

fn parse_parenthesized_children(input: &str, prefix: &str) -> Option<Vec<String>> {
    if !input.starts_with(prefix) || !input.ends_with(')') {
        return None;
    }
    let open = prefix.len() - 1;
    let close = matching_paren_index(input, open)?;
    if close != input.len() - 1 {
        return None;
    }
    Some(split_top_level_commas(&input[prefix.len()..close]))
}

fn parse_notation_children(input: &str) -> Option<Vec<String>> {
    if !input.starts_with("notation(") || !input.ends_with(')') {
        return None;
    }
    let head_close = matching_paren_index(input, "notation".len())?;
    let args_open = head_close + 1;
    if input.as_bytes().get(args_open).copied() != Some(b'(') {
        return None;
    }
    let args_close = matching_paren_index(input, args_open)?;
    if args_close != input.len() - 1 {
        return None;
    }
    Some(split_top_level_commas(&input[args_open + 1..args_close]))
}

fn parse_let_children(input: &str) -> Option<Vec<RecursionExpr>> {
    if !input.starts_with("let(") {
        return None;
    }
    let close = matching_paren_index(input, 3)?;
    let body = input.get(close + 1..)?.strip_prefix(':')?;
    let parts = split_top_level_commas(&input[4..close]);
    let mut children = Vec::new();
    if let Some(value) = parts.get(2) {
        children.push(parse_recursion_expr(value));
    }
    children.push(parse_recursion_expr(body));
    Some(children)
}

fn parse_binder_children(input: &str, prefix: &str) -> Option<Vec<RecursionExpr>> {
    if !input.starts_with(prefix) {
        return None;
    }
    let close = matching_paren_index(input, prefix.len() - 1)?;
    let body = input.get(close + 1..)?.strip_prefix("->")?;
    let mut children = split_top_level_commas(&input[prefix.len()..close])
        .into_iter()
        .filter_map(|binder| {
            let ty = binder.split_once(':')?.1;
            (ty != "_").then(|| parse_recursion_expr(ty))
        })
        .collect::<Vec<_>>();
    children.push(parse_recursion_expr(body));
    Some(children)
}

fn matching_paren_index(input: &str, open_index: usize) -> Option<usize> {
    let bytes = input.as_bytes();
    if bytes.get(open_index).copied() != Some(b'(') {
        return None;
    }
    let mut depth = 0_u32;
    for (index, byte) in bytes.iter().enumerate().skip(open_index) {
        match byte {
            b'(' => depth = depth.saturating_add(1),
            b')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

fn split_top_level_commas(input: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut depth = 0_i32;
    for (index, byte) in input.bytes().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b',' if depth == 0 => {
                parts.push(input[start..index].to_owned());
                start = index + 1;
            }
            _ => {}
        }
    }
    if start <= input.len() {
        parts.push(input[start..].to_owned());
    }
    parts
}

fn nondecreasing_mutual_cycles(
    definitions: &[HumanEquationRecursionDefinition],
    calls: &[HumanEquationRecursiveCall],
    target_spans: &BTreeMap<String, Span>,
) -> Vec<HumanEquationMutualCycle> {
    let target_by_name = definitions
        .iter()
        .map(|definition| (definition.name.clone(), definition.target_identity.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut adjacency = BTreeMap::<String, BTreeSet<String>>::new();
    for definition in definitions {
        adjacency
            .entry(definition.target_identity.clone())
            .or_default();
    }
    for call in calls {
        if call_has_checked_decrease(call) {
            continue;
        }
        let (Some(caller), Some(callee)) = (
            target_by_name.get(&call.caller),
            target_by_name.get(&call.callee),
        ) else {
            continue;
        };
        adjacency
            .entry(caller.clone())
            .or_default()
            .insert(callee.clone());
    }

    let mut cycles = BTreeMap::<Vec<String>, HumanEquationMutualCycle>::new();
    for definition in definitions {
        let component = definitions
            .iter()
            .filter(|other| {
                path_exists(
                    &definition.target_identity,
                    &other.target_identity,
                    &adjacency,
                ) && path_exists(
                    &other.target_identity,
                    &definition.target_identity,
                    &adjacency,
                )
            })
            .map(|definition| definition.target_identity.clone())
            .collect::<Vec<_>>();
        if component.len() <= 1 {
            continue;
        }
        let names = component
            .iter()
            .filter_map(|target| {
                definitions
                    .iter()
                    .find(|definition| &definition.target_identity == target)
                    .map(|definition| definition.name.clone())
            })
            .collect::<Vec<_>>();
        let mut target_identities = component;
        target_identities.sort();
        cycles.entry(target_identities.clone()).or_insert_with(|| {
            let mut definitions = names;
            definitions.sort();
            HumanEquationMutualCycle {
                definitions,
                target_identities,
            }
        });
    }

    let mut cycles = cycles.into_values().collect::<Vec<_>>();
    cycles.sort_by_key(|cycle| {
        (
            cycle.target_identities.clone(),
            cycle
                .target_identities
                .iter()
                .filter_map(|target| target_spans.get(target).map(|span| span.start.0))
                .min()
                .unwrap_or(0),
        )
    });
    cycles
}

fn call_has_checked_decrease(call: &HumanEquationRecursiveCall) -> bool {
    call.decrease_evidence.is_some()
        || call
            .measure_decrease
            .as_ref()
            .is_some_and(|obligation| obligation.proof.is_some())
}

fn path_exists(start: &str, target: &str, adjacency: &BTreeMap<String, BTreeSet<String>>) -> bool {
    if start == target {
        return true;
    }
    let mut stack = vec![start.to_owned()];
    let mut seen = BTreeSet::new();
    while let Some(node) = stack.pop() {
        if node == target {
            return true;
        }
        if !seen.insert(node.clone()) {
            continue;
        }
        if let Some(next) = adjacency.get(&node) {
            for child in next.iter().rev() {
                stack.push(child.clone());
            }
        }
    }
    false
}

fn recursive_call_not_decreasing_diagnostic(
    call: &HumanEquationRecursiveCall,
) -> HumanEquationRecursionDiagnostic {
    recursion_diagnostic(
        HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing,
        Some(call.caller.clone()),
        Some(call.callee.clone()),
        Some(call.row_index),
        Some(call.call_identity.clone()),
        Vec::new(),
        call.primary_span,
    )
}

fn mutual_cycle_without_decrease_diagnostic(
    cycle: &HumanEquationMutualCycle,
    target_spans: &BTreeMap<String, Span>,
) -> HumanEquationRecursionDiagnostic {
    let primary_span = cycle
        .target_identities
        .iter()
        .filter_map(|target| target_spans.get(target).copied())
        .min_by_key(|span| (span.file_id.0, span.start.0, span.end.0))
        .unwrap_or_else(|| Span::empty(crate::FileId(0)));
    recursion_diagnostic(
        HumanEquationRecursionDiagnosticKind::MutualCycleWithoutDecrease,
        None,
        None,
        None,
        None,
        cycle.definitions.clone(),
        primary_span,
    )
}

fn termination_measure_not_nat_diagnostic(
    equation: &HumanResolvedEquationItem,
    primary_span: Span,
) -> HumanEquationRecursionDiagnostic {
    recursion_diagnostic(
        HumanEquationRecursionDiagnosticKind::TerminationMeasureNotNat,
        Some(equation.source_name.as_dotted()),
        None,
        None,
        None,
        Vec::new(),
        primary_span,
    )
}

fn measure_decrease_proof_missing_diagnostic(
    call: &HumanEquationRecursiveCall,
) -> HumanEquationRecursionDiagnostic {
    recursion_diagnostic(
        HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing,
        Some(call.caller.clone()),
        Some(call.callee.clone()),
        Some(call.row_index),
        Some(call.call_identity.clone()),
        Vec::new(),
        call.primary_span,
    )
}

fn recursion_diagnostic(
    kind: HumanEquationRecursionDiagnosticKind,
    caller: Option<String>,
    callee: Option<String>,
    row_index: Option<usize>,
    call_identity: Option<String>,
    cycle: Vec<String>,
    primary_span: Span,
) -> HumanEquationRecursionDiagnostic {
    let identity = format!(
        "{kind:?}|caller:{}|callee:{}|row:{row_index:?}|call:{}|cycle:{}",
        caller.as_deref().unwrap_or(""),
        callee.as_deref().unwrap_or(""),
        call_identity.as_deref().unwrap_or(""),
        cycle.join(",")
    );
    HumanEquationRecursionDiagnostic {
        kind,
        identity,
        primary_span,
        caller,
        callee,
        row_index,
        call_identity,
        cycle,
    }
}

fn recursive_call_sort_key(
    call: &HumanEquationRecursiveCall,
) -> (String, String, usize, String, Vec<String>) {
    (
        call.caller.clone(),
        call.callee.clone(),
        call.row_index,
        call.call_identity.clone(),
        call.argument_mapping.clone(),
    )
}

fn recursion_diagnostic_sort_key(
    diagnostic: &HumanEquationRecursionDiagnostic,
) -> (
    HumanEquationRecursionDiagnosticKind,
    Option<String>,
    Option<String>,
    Option<usize>,
    String,
) {
    (
        diagnostic.kind,
        diagnostic.caller.clone(),
        diagnostic.callee.clone(),
        diagnostic.row_index,
        diagnostic.identity.clone(),
    )
}

fn recursion_global_identity(reference: &HumanGlobalRef) -> String {
    format!("global:{}", recursion_global_ref_sort_key(reference))
}

fn recursion_global_ref_sort_key(reference: &HumanGlobalRef) -> String {
    match reference {
        HumanGlobalRef::Imported {
            module,
            name,
            decl_interface_hash,
        } => format!(
            "imported:{}:{}:{}",
            module.as_dotted(),
            name.as_dotted(),
            hash_hex(decl_interface_hash)
        ),
        HumanGlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => format!(
            "builtin:{}:{}",
            name.as_dotted(),
            hash_hex(decl_interface_hash)
        ),
        HumanGlobalRef::Local { index, name } => {
            format!("local:{index:08}:{}", name.as_dotted())
        }
        HumanGlobalRef::LocalGenerated { index, name } => {
            format!("local-generated:{index:08}:{}", name.as_dotted())
        }
    }
}

fn build_decision_tree_node(
    matrix: &HumanEquationPatternMatrix,
    constructor_sets: &BTreeMap<usize, &HumanEquationPatternMatrixConstructorSet>,
    recursion_by_row: &BTreeMap<usize, Vec<HumanEquationRecursiveCall>>,
    row_indexes: &[usize],
    remaining_columns: &[usize],
) -> HumanEquationDecisionTreeNode {
    let Some(split_column) = choose_decision_split_column(matrix, row_indexes, remaining_columns)
    else {
        return decision_leaf(matrix, recursion_by_row, row_indexes);
    };
    let Some(constructor_set) = constructor_sets.get(&split_column).copied() else {
        return decision_leaf(matrix, recursion_by_row, row_indexes);
    };
    let next_columns = remaining_columns
        .iter()
        .copied()
        .filter(|column| *column != split_column)
        .collect::<Vec<_>>();

    let mut branches = Vec::new();
    for constructor in &constructor_set.constructors {
        let branch_rows = row_indexes
            .iter()
            .copied()
            .filter(|row_index| {
                matrix.rows[*row_index]
                    .cells
                    .get(split_column)
                    .is_some_and(|cell| {
                        decision_cell_matches_constructor(cell, &constructor.constructor_key)
                    })
            })
            .collect::<Vec<_>>();
        if branch_rows.is_empty() {
            continue;
        }
        let child = build_decision_tree_node(
            matrix,
            constructor_sets,
            recursion_by_row,
            &branch_rows,
            &next_columns,
        );
        branches.push(HumanEquationDecisionBranch {
            constructor: constructor.clone(),
            child: Box::new(child),
        });
    }

    let default_rows = row_indexes
        .iter()
        .copied()
        .filter(|row_index| {
            matrix.rows[*row_index]
                .cells
                .get(split_column)
                .is_some_and(decision_cell_matches_default)
        })
        .collect::<Vec<_>>();
    let default_branch = if default_rows.is_empty() {
        None
    } else {
        Some(Box::new(build_decision_tree_node(
            matrix,
            constructor_sets,
            recursion_by_row,
            &default_rows,
            &next_columns,
        )))
    };

    let identity = decision_switch_identity(
        split_column,
        &matrix.columns[split_column].identity,
        &branches,
        default_branch.as_deref(),
    );
    HumanEquationDecisionTreeNode::Switch(HumanEquationDecisionSwitch {
        column_index: split_column,
        column_identity: matrix.columns[split_column].identity.clone(),
        branches,
        default_branch,
        identity,
    })
}

fn choose_decision_split_column(
    matrix: &HumanEquationPatternMatrix,
    row_indexes: &[usize],
    remaining_columns: &[usize],
) -> Option<usize> {
    remaining_columns.iter().copied().find(|column| {
        row_indexes.iter().any(|row_index| {
            matches!(
                matrix.rows[*row_index].cells.get(*column),
                Some(HumanEquationPatternMatrixCell::Constructor { .. })
            )
        })
    })
}

fn decision_cell_matches_constructor(
    cell: &HumanEquationPatternMatrixCell,
    constructor_key: &str,
) -> bool {
    match cell {
        HumanEquationPatternMatrixCell::Constructor {
            constructor_key: actual,
            ..
        } => actual == constructor_key,
        HumanEquationPatternMatrixCell::Variable { .. }
        | HumanEquationPatternMatrixCell::Default => true,
        HumanEquationPatternMatrixCell::Unavailable { .. } => false,
    }
}

fn decision_cell_matches_default(cell: &HumanEquationPatternMatrixCell) -> bool {
    matches!(
        cell,
        HumanEquationPatternMatrixCell::Variable { .. } | HumanEquationPatternMatrixCell::Default
    )
}

fn decision_leaf(
    matrix: &HumanEquationPatternMatrix,
    recursion_by_row: &BTreeMap<usize, Vec<HumanEquationRecursiveCall>>,
    row_indexes: &[usize],
) -> HumanEquationDecisionTreeNode {
    let row_index = row_indexes
        .first()
        .copied()
        .expect("accepted decision tree leaves require at least one reachable row");
    let row = &matrix.rows[row_index];
    let mut recursive_calls = recursion_by_row
        .get(&row_index)
        .cloned()
        .unwrap_or_default();
    recursive_calls.sort_by_key(recursive_call_sort_key);
    let branch_context = decision_branch_context(matrix, row);
    let identity = decision_leaf_identity(row, &branch_context, &recursive_calls);
    HumanEquationDecisionTreeNode::Leaf(HumanEquationDecisionLeaf {
        row_index,
        source_row_index: row.provenance.source_row_index,
        value_identity: row.value_identity.clone(),
        branch_context,
        recursive_calls,
        identity,
    })
}

fn decision_branch_context(
    matrix: &HumanEquationPatternMatrix,
    row: &HumanEquationPatternMatrixRow,
) -> HumanEquationDecisionBranchContext {
    let cells = row
        .cells
        .iter()
        .enumerate()
        .map(|(column_index, cell)| HumanEquationDecisionBranchCell {
            column_index,
            column_identity: matrix.columns[column_index].identity.clone(),
            cell_identity: cell.identity(),
        })
        .collect();
    HumanEquationDecisionBranchContext {
        row_index: row.index,
        source_row_index: row.provenance.source_row_index,
        cells,
    }
}

fn decision_leaf_identity(
    row: &HumanEquationPatternMatrixRow,
    branch_context: &HumanEquationDecisionBranchContext,
    recursive_calls: &[HumanEquationRecursiveCall],
) -> String {
    let mut input = String::from("npa.frontend.equation.decision-leaf.v0\n");
    let _ = writeln!(input, "value:{}", row.value_identity);
    for cell in &branch_context.cells {
        let _ = writeln!(
            input,
            "cell:{}:{}:{}",
            cell.column_index, cell.column_identity, cell.cell_identity
        );
    }
    for call in recursive_calls {
        let _ = writeln!(input, "call:{}", decision_recursive_call_identity(call));
    }
    format!("leaf:{}", hash_hex(&sha256(input.as_bytes())))
}

fn decision_recursive_call_identity(call: &HumanEquationRecursiveCall) -> String {
    let evidence = call
        .decrease_evidence
        .as_ref()
        .map(|evidence| {
            format!(
                "decrease:{}:{}",
                evidence.decreasing_parameter, evidence.constructor_field_path.identity
            )
        })
        .unwrap_or_else(|| "decrease:none".to_owned());
    let measure = call
        .measure_decrease
        .as_ref()
        .map(|obligation| {
            let proof = obligation
                .proof
                .as_ref()
                .map(|proof| proof.proof_identity.as_str())
                .unwrap_or("<missing>");
            format!(
                "measure:{}:{}:{}",
                obligation.identity, obligation.relation_identity, proof
            )
        })
        .unwrap_or_else(|| "measure:none".to_owned());
    format!(
        "caller:{}|callee:{}|call:{}|args:{}|{}|{}",
        call.caller,
        call.callee,
        call.call_identity,
        call.argument_mapping.join(","),
        evidence,
        measure
    )
}

fn decision_switch_identity(
    column_index: usize,
    column_identity: &str,
    branches: &[HumanEquationDecisionBranch],
    default_branch: Option<&HumanEquationDecisionTreeNode>,
) -> String {
    let mut input = String::from("npa.frontend.equation.decision-switch.v0\n");
    let _ = writeln!(input, "column:{column_index}:{column_identity}");
    for branch in branches {
        let _ = writeln!(
            input,
            "branch:{}:{}",
            branch.constructor.constructor_key,
            decision_tree_node_identity(&branch.child)
        );
    }
    if let Some(default_branch) = default_branch {
        let _ = writeln!(
            input,
            "default:{}",
            decision_tree_node_identity(default_branch)
        );
    } else {
        let _ = writeln!(input, "default:<none>");
    }
    format!("switch:{}", hash_hex(&sha256(input.as_bytes())))
}

fn decision_tree_identity_input(root: &HumanEquationDecisionTreeNode) -> String {
    let mut input = String::from("npa.frontend.equation.decision-tree.v0\n");
    let _ = writeln!(input, "root:{}", decision_tree_node_identity(root));
    input
}

fn decision_tree_node_identity(node: &HumanEquationDecisionTreeNode) -> &str {
    match node {
        HumanEquationDecisionTreeNode::Leaf(leaf) => &leaf.identity,
        HumanEquationDecisionTreeNode::Switch(switch) => &switch.identity,
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct DecisionTreeNodeStats {
    node_count: u64,
    branch_depth: u64,
}

fn decision_tree_node_stats(node: &HumanEquationDecisionTreeNode) -> DecisionTreeNodeStats {
    match node {
        HumanEquationDecisionTreeNode::Leaf(_) => DecisionTreeNodeStats {
            node_count: 1,
            branch_depth: 0,
        },
        HumanEquationDecisionTreeNode::Switch(switch) => {
            let mut stats = DecisionTreeNodeStats {
                node_count: 1,
                branch_depth: 0,
            };
            for branch in &switch.branches {
                let child = decision_tree_node_stats(&branch.child);
                stats.node_count = stats.node_count.saturating_add(child.node_count);
                stats.branch_depth = stats.branch_depth.max(child.branch_depth.saturating_add(1));
            }
            if let Some(default_branch) = &switch.default_branch {
                let child = decision_tree_node_stats(default_branch);
                stats.node_count = stats.node_count.saturating_add(child.node_count);
                stats.branch_depth = stats.branch_depth.max(child.branch_depth.saturating_add(1));
            }
            stats
        }
    }
}

fn plan_decision_tree_helpers(
    equation: &HumanResolvedEquationItem,
    tree: &HumanEquationDecisionTree,
    budget: HumanEquationBudget,
) -> HumanEquationHelperSplitPlan {
    let mut helpers = Vec::new();
    collect_helper_split_candidates(
        equation,
        &tree.root,
        true,
        budget.helper_split_node_threshold,
        &mut helpers,
    );
    helpers.sort_by(|lhs, rhs| {
        lhs.semantic_identity
            .cmp(&rhs.semantic_identity)
            .then_with(|| lhs.target_node_identity.cmp(&rhs.target_node_identity))
    });
    for (ordinal, helper) in helpers.iter_mut().enumerate() {
        helper.ordinal = ordinal as u64;
        helper.name = decision_helper_name(
            &equation.source_name.as_dotted(),
            &helper.role,
            &helper.semantic_identity,
            helper.ordinal,
        );
    }
    HumanEquationHelperSplitPlan { helpers }
}

fn collect_helper_split_candidates(
    equation: &HumanResolvedEquationItem,
    node: &HumanEquationDecisionTreeNode,
    is_root: bool,
    helper_split_node_threshold: u64,
    helpers: &mut Vec<HumanEquationHelperCandidate>,
) {
    let stats = decision_tree_node_stats(node);
    if !is_root && stats.node_count > helper_split_node_threshold {
        let row_indexes = decision_tree_node_row_indexes(node);
        let dependencies = Vec::new();
        let semantic_identity =
            decision_helper_semantic_identity(equation, node, stats, &dependencies);
        helpers.push(HumanEquationHelperCandidate {
            name: String::new(),
            role: "match".to_owned(),
            ordinal: 0,
            semantic_identity,
            target_node_identity: decision_tree_node_identity(node).to_owned(),
            row_indexes,
            node_count: stats.node_count,
            branch_depth: stats.branch_depth,
            dependencies,
        });
        return;
    }

    if let HumanEquationDecisionTreeNode::Switch(switch) = node {
        for branch in &switch.branches {
            collect_helper_split_candidates(
                equation,
                &branch.child,
                false,
                helper_split_node_threshold,
                helpers,
            );
        }
        if let Some(default_branch) = &switch.default_branch {
            collect_helper_split_candidates(
                equation,
                default_branch,
                false,
                helper_split_node_threshold,
                helpers,
            );
        }
    }
}

fn decision_helper_semantic_identity(
    equation: &HumanResolvedEquationItem,
    node: &HumanEquationDecisionTreeNode,
    stats: DecisionTreeNodeStats,
    dependencies: &[String],
) -> String {
    let mut input = String::from("npa.frontend.equation.helper.v0\n");
    let _ = writeln!(input, "definition:{}", equation.source_name.as_dotted());
    let _ = writeln!(input, "role:match");
    let _ = writeln!(input, "node:{}", decision_tree_node_identity(node));
    let _ = writeln!(input, "node-count:{}", stats.node_count);
    let _ = writeln!(input, "branch-depth:{}", stats.branch_depth);
    for dependency in dependencies {
        let _ = writeln!(input, "dependency:{dependency}");
    }
    input
}

fn decision_helper_name(
    declaration_name: &str,
    role: &str,
    semantic_identity: &str,
    ordinal: u64,
) -> String {
    let hash = hash_hex(&sha256(semantic_identity.as_bytes()));
    let short_hash = &hash[..12];
    format!("{declaration_name}.__eqc_{role}_{short_hash}_{ordinal:04}")
}

fn decision_tree_node_row_indexes(node: &HumanEquationDecisionTreeNode) -> Vec<usize> {
    let mut rows = Vec::new();
    collect_decision_tree_node_row_indexes(node, &mut rows);
    rows.sort_unstable();
    rows.dedup();
    rows
}

fn collect_decision_tree_node_row_indexes(
    node: &HumanEquationDecisionTreeNode,
    rows: &mut Vec<usize>,
) {
    match node {
        HumanEquationDecisionTreeNode::Leaf(leaf) => rows.push(leaf.row_index),
        HumanEquationDecisionTreeNode::Switch(switch) => {
            for branch in &switch.branches {
                collect_decision_tree_node_row_indexes(&branch.child, rows);
            }
            if let Some(default_branch) = &switch.default_branch {
                collect_decision_tree_node_row_indexes(default_branch, rows);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HelperReferenceMode {
    Inline,
    Use,
}

#[derive(Clone, Debug)]
struct HumanEquationLoweringContext {
    binders: Vec<HumanEquationLoweringBinder>,
}

impl HumanEquationLoweringContext {
    fn new(binders: Vec<HumanEquationLoweringBinder>) -> Self {
        Self { binders }
    }

    fn extend(&self, binders: &[HumanEquationLoweringBinder]) -> Self {
        let mut next = self.binders.clone();
        next.extend_from_slice(binders);
        Self { binders: next }
    }

    fn public_binder_ref(&self, root: usize) -> Result<Expr, HumanEquationLoweringError> {
        if root >= self.binders.len() {
            return Err(HumanEquationLoweringError::UnsupportedRecursorProfile {
                recursor_name: "<decision-column>".to_owned(),
                reason: format!(
                    "decision column root {root} is outside lowering context of {} binders",
                    self.binders.len()
                ),
            });
        }
        Ok(Expr::bvar((self.binders.len() - 1 - root) as u32))
    }

    fn argument_refs(&self) -> Vec<Expr> {
        let len = self.binders.len();
        (0..len)
            .map(|index| Expr::bvar((len - 1 - index) as u32))
            .collect()
    }
}

struct HumanEquationCoreLowerer<'a> {
    matrix: &'a HumanEquationPatternMatrix,
    decision: &'a HumanEquationDecisionTreeResult,
    profile: HumanEquationLoweringProfile,
    helpers_by_target: BTreeMap<String, HumanEquationHelperCandidate>,
    helper_contexts: BTreeMap<String, Vec<HumanEquationLoweringBinder>>,
    eq_rec_transports: u64,
}

impl<'a> HumanEquationCoreLowerer<'a> {
    fn new(
        matrix: &'a HumanEquationPatternMatrix,
        decision: &'a HumanEquationDecisionTreeResult,
        profile: HumanEquationLoweringProfile,
    ) -> Self {
        let helpers_by_target = decision
            .helper_plan
            .helpers
            .iter()
            .cloned()
            .map(|helper| (helper.target_node_identity.clone(), helper))
            .collect();
        Self {
            matrix,
            decision,
            profile,
            helpers_by_target,
            helper_contexts: BTreeMap::new(),
            eq_rec_transports: 0,
        }
    }

    fn lower_node(
        &mut self,
        node: &HumanEquationDecisionTreeNode,
        context: &mut HumanEquationLoweringContext,
        helper_mode: HelperReferenceMode,
    ) -> Result<Expr, HumanEquationLoweringError> {
        let node_identity = decision_tree_node_identity(node);
        if helper_mode == HelperReferenceMode::Use {
            if let Some(helper) = self.helpers_by_target.get(node_identity) {
                self.helper_contexts
                    .entry(node_identity.to_owned())
                    .or_insert_with(|| context.binders.clone());
                return Ok(Expr::apps(
                    Expr::konst(
                        helper.name.clone(),
                        helper_call_universe_args(&self.profile.universe_params),
                    ),
                    context.argument_refs(),
                ));
            }
        }

        match node {
            HumanEquationDecisionTreeNode::Leaf(leaf) => self.lower_leaf(leaf),
            HumanEquationDecisionTreeNode::Switch(switch) => {
                self.lower_switch(switch, context, helper_mode)
            }
        }
    }

    fn lower_leaf(
        &mut self,
        leaf: &HumanEquationDecisionLeaf,
    ) -> Result<Expr, HumanEquationLoweringError> {
        if let Some(call) = leaf
            .recursive_calls
            .iter()
            .find(|call| call.caller != call.callee)
        {
            return Err(
                HumanEquationLoweringError::UnsupportedNestedOrMutualLowering {
                    reason: format!(
                        "mutual recursive lowering is not supported yet: {} calls {}",
                        call.caller, call.callee
                    ),
                },
            );
        }
        let value = self
            .profile
            .row_values
            .get(&leaf.row_index)
            .or_else(|| self.profile.row_values.get(&leaf.source_row_index))
            .cloned()
            .ok_or(HumanEquationLoweringError::MissingRowValue {
                row_index: leaf.row_index,
                source_row_index: leaf.source_row_index,
            })?;
        self.apply_row_transports(leaf, value)
    }

    fn lower_switch(
        &mut self,
        switch: &HumanEquationDecisionSwitch,
        context: &mut HumanEquationLoweringContext,
        helper_mode: HelperReferenceMode,
    ) -> Result<Expr, HumanEquationLoweringError> {
        let column = self
            .matrix
            .columns
            .get(switch.column_index)
            .ok_or_else(|| HumanEquationLoweringError::UnsupportedRecursorProfile {
                recursor_name: "<decision-column>".to_owned(),
                reason: format!("decision column {} is missing", switch.column_index),
            })?;
        if !column.path.segments.is_empty() {
            return Err(
                HumanEquationLoweringError::UnsupportedNestedOrMutualLowering {
                    reason: format!(
                        "nested decision column {} requires dependent-match lowering",
                        column.identity
                    ),
                },
            );
        }
        if column.path.root >= self.profile.public_binders.len() {
            return Err(HumanEquationLoweringError::UnsupportedRecursorProfile {
                recursor_name: "<decision-column>".to_owned(),
                reason: format!(
                    "decision column root {} has no public binder",
                    column.path.root
                ),
            });
        }

        let recursor = self.recursor_for_switch(switch)?.clone();
        if recursor.universe_args.is_empty() {
            return Err(HumanEquationLoweringError::UnsupportedRecursorProfile {
                recursor_name: recursor.recursor_name,
                reason: format!(
                    "recursor profile is missing explicit universe arguments for result universe {:?}",
                    self.profile.result_universe
                ),
            });
        }
        self.validate_indexed_recursor_profile(&recursor, switch)?;
        let motive = self.synthesize_motive(&recursor)?;
        let mut recursor_args = recursor.parameters.clone();
        recursor_args.push(motive);

        for constructor in &recursor.constructors {
            let child = switch
                .branches
                .iter()
                .find(|branch| branch.constructor.constructor_key == constructor.constructor_key)
                .map(|branch| branch.child.as_ref())
                .or(switch.default_branch.as_deref())
                .ok_or_else(|| HumanEquationLoweringError::MissingDecisionBranch {
                    column_identity: switch.column_identity.clone(),
                    constructor_key: constructor.constructor_key.clone(),
                })?;
            let mut nested = context.extend(&constructor.minor_binders);
            let minor_body = self.lower_node(child, &mut nested, helper_mode)?;
            recursor_args.push(close_lam(&constructor.minor_binders, minor_body));
        }

        recursor_args.extend(recursor.major_index_args.clone());
        recursor_args.push(context.public_binder_ref(column.path.root)?);
        Ok(Expr::apps(
            Expr::konst(recursor.recursor_name, recursor.universe_args),
            recursor_args,
        ))
    }

    fn recursor_for_switch(
        &self,
        switch: &HumanEquationDecisionSwitch,
    ) -> Result<&HumanEquationRecursorLoweringProfile, HumanEquationLoweringError> {
        let branch_keys = switch
            .branches
            .iter()
            .map(|branch| branch.constructor.constructor_key.as_str())
            .collect::<Vec<_>>();
        let Some(first_key) = branch_keys.first() else {
            return Err(HumanEquationLoweringError::MissingRecursor {
                constructor_key: "<empty-switch>".to_owned(),
            });
        };
        let matches = self
            .profile
            .recursors
            .iter()
            .filter(|recursor| {
                branch_keys.iter().all(|branch_key| {
                    recursor
                        .constructors
                        .iter()
                        .any(|constructor| constructor.constructor_key == *branch_key)
                })
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => Err(HumanEquationLoweringError::MissingRecursor {
                constructor_key: (*first_key).to_owned(),
            }),
            [recursor] => Ok(*recursor),
            recursors => Err(HumanEquationLoweringError::AmbiguousConstructor {
                constructor_key: (*first_key).to_owned(),
                recursor_names: recursors
                    .iter()
                    .map(|recursor| recursor.recursor_name.clone())
                    .collect(),
            }),
        }
    }

    fn synthesize_motive(
        &self,
        recursor: &HumanEquationRecursorLoweringProfile,
    ) -> Result<Expr, HumanEquationLoweringError> {
        let mut binders = recursor.index_binders.clone();
        binders.push(HumanEquationLoweringBinder {
            name: "_".to_owned(),
            ty: recursor.major_type.clone(),
        });
        let body = if let Some(body) = &recursor.motive_body {
            body.clone()
        } else {
            npa_kernel::subst::shift(&self.profile.result_type, binders.len() as i32, 0).map_err(
                |err| HumanEquationLoweringError::DependentMotiveSynthesisFailed {
                    recursor_name: recursor.recursor_name.clone(),
                    reason: format!("failed to shift result type into motive context: {err:?}"),
                },
            )?
        };
        Ok(close_lam(&binders, body))
    }

    fn validate_indexed_recursor_profile(
        &self,
        recursor: &HumanEquationRecursorLoweringProfile,
        switch: &HumanEquationDecisionSwitch,
    ) -> Result<(), HumanEquationLoweringError> {
        if recursor.index_binders.len() != recursor.major_index_args.len() {
            return Err(HumanEquationLoweringError::DependentMotiveSynthesisFailed {
                recursor_name: recursor.recursor_name.clone(),
                reason: format!(
                    "recursor has {} index binders but {} major index arguments",
                    recursor.index_binders.len(),
                    recursor.major_index_args.len()
                ),
            });
        }
        for constructor in &recursor.constructors {
            if constructor.result_index_args.len() != recursor.index_binders.len() {
                return Err(HumanEquationLoweringError::DependentMotiveSynthesisFailed {
                    recursor_name: recursor.recursor_name.clone(),
                    reason: format!(
                        "constructor {} has {} result index arguments but the recursor motive has {} indices",
                        constructor.constructor_key,
                        constructor.result_index_args.len(),
                        recursor.index_binders.len()
                    ),
                });
            }
        }
        if !recursor.index_binders.is_empty() && switch.default_branch.is_some() {
            for branch in &switch.branches {
                if !recursor.constructors.iter().any(|constructor| {
                    constructor.constructor_key == branch.constructor.constructor_key
                }) {
                    return Err(HumanEquationLoweringError::DependentMotiveSynthesisFailed {
                        recursor_name: recursor.recursor_name.clone(),
                        reason: format!(
                            "branch constructor {} is missing from indexed recursor profile",
                            branch.constructor.constructor_key
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    fn apply_row_transports(
        &mut self,
        leaf: &HumanEquationDecisionLeaf,
        mut value: Expr,
    ) -> Result<Expr, HumanEquationLoweringError> {
        let transports = self
            .profile
            .row_transports
            .get(&leaf.row_index)
            .or_else(|| self.profile.row_transports.get(&leaf.source_row_index))
            .cloned()
            .unwrap_or_default();
        for transport in transports {
            if transport.eq_rec_name != "Eq.rec" {
                return Err(HumanEquationLoweringError::UnsupportedEqRecTransport {
                    eq_rec_name: transport.eq_rec_name,
                    reason: "equation lowering may use only the standard Eq.rec interface"
                        .to_owned(),
                });
            }
            value = Expr::apps(
                Expr::konst(
                    transport.eq_rec_name,
                    vec![transport.value_level, transport.motive_level],
                ),
                vec![
                    transport.source_type,
                    transport.source,
                    transport.motive,
                    value,
                    transport.target,
                    transport.proof,
                ],
            );
            self.eq_rec_transports = self.eq_rec_transports.saturating_add(1);
        }
        Ok(value)
    }

    fn lower_helper_declarations(
        &mut self,
    ) -> Result<Vec<(Decl, HumanEquationCoreArtifactKind)>, HumanEquationLoweringError> {
        let mut declarations = Vec::with_capacity(self.decision.helper_plan.helpers.len());
        for helper in &self.decision.helper_plan.helpers {
            let helper_context = self
                .helper_contexts
                .get(&helper.target_node_identity)
                .cloned()
                .ok_or_else(|| HumanEquationLoweringError::MissingHelperContext {
                    helper_name: helper.name.clone(),
                    target_node_identity: helper.target_node_identity.clone(),
                })?;
            let node = find_decision_tree_node_by_identity(
                &self.decision.tree.root,
                &helper.target_node_identity,
            )
            .ok_or_else(|| HumanEquationLoweringError::MissingHelperContext {
                helper_name: helper.name.clone(),
                target_node_identity: helper.target_node_identity.clone(),
            })?;
            let mut context = HumanEquationLoweringContext::new(helper_context.clone());
            let body = self.lower_node(node, &mut context, HelperReferenceMode::Inline)?;
            let body = self.share_repeated_result_terms(body)?;
            declarations.push((
                Decl::Def {
                    name: helper.name.clone(),
                    universe_params: self.profile.universe_params.clone(),
                    ty: close_pi(&helper_context, self.profile.result_type.clone()),
                    value: close_lam(&helper_context, body),
                    reducibility: Reducibility::Reducible,
                },
                HumanEquationCoreArtifactKind::HelperDefinition,
            ));
        }
        Ok(declarations)
    }

    fn share_repeated_result_terms(&self, body: Expr) -> Result<Expr, HumanEquationLoweringError> {
        share_repeated_closed_result_terms(
            body,
            &self.profile.result_type,
            &self.profile.row_values,
        )
    }
}

fn find_decision_tree_node_by_identity<'a>(
    node: &'a HumanEquationDecisionTreeNode,
    identity: &str,
) -> Option<&'a HumanEquationDecisionTreeNode> {
    if decision_tree_node_identity(node) == identity {
        return Some(node);
    }
    match node {
        HumanEquationDecisionTreeNode::Leaf(_) => None,
        HumanEquationDecisionTreeNode::Switch(switch) => {
            for branch in &switch.branches {
                if let Some(found) = find_decision_tree_node_by_identity(&branch.child, identity) {
                    return Some(found);
                }
            }
            switch
                .default_branch
                .as_deref()
                .and_then(|node| find_decision_tree_node_by_identity(node, identity))
        }
    }
}

fn helper_call_universe_args(universe_params: &[String]) -> Vec<Level> {
    universe_params.iter().cloned().map(Level::param).collect()
}

fn close_lam(binders: &[HumanEquationLoweringBinder], body: Expr) -> Expr {
    binders.iter().rev().fold(body, |body, binder| {
        Expr::lam(binder.name.clone(), binder.ty.clone(), body)
    })
}

fn close_pi(binders: &[HumanEquationLoweringBinder], body: Expr) -> Expr {
    binders.iter().rev().fold(body, |body, binder| {
        Expr::pi(binder.name.clone(), binder.ty.clone(), body)
    })
}

fn lowered_core_artifact(
    decl: &Decl,
    kind: HumanEquationCoreArtifactKind,
) -> HumanEquationCoreArtifact {
    let (name, opaque, ty, value) = match decl {
        Decl::Def {
            name,
            ty,
            value,
            reducibility,
            ..
        } => (
            name.clone(),
            *reducibility == Reducibility::Opaque,
            ty,
            value,
        ),
        Decl::Theorem {
            name, ty, proof, ..
        } => (name.clone(), true, ty, proof),
        _ => panic!("equation lowering emits only core definitions and theorem artifacts"),
    };
    let ty_hash = npa_cert::core_expr_hash(ty);
    let value_hash = npa_cert::core_expr_hash(value);
    let node_count = core_expr_node_count(ty).saturating_add(core_expr_node_count(value));
    let mut identity_input = String::from("npa.frontend.equation.lowered-core-artifact.v0\n");
    let _ = writeln!(identity_input, "name:{name}");
    let _ = writeln!(identity_input, "kind:{}", kind.as_str());
    let _ = writeln!(identity_input, "opaque:{opaque}");
    let _ = writeln!(identity_input, "type:{}", hash_hex(&ty_hash));
    let _ = writeln!(identity_input, "value:{}", hash_hex(&value_hash));
    let _ = writeln!(identity_input, "nodes:{node_count}");
    let core_hash = sha256(identity_input.as_bytes());
    HumanEquationCoreArtifact {
        name,
        kind,
        opaque,
        node_count,
        core_hash,
        identity_input,
    }
}

fn helper_body_node_count(declarations: &[Decl], artifacts: &[HumanEquationCoreArtifact]) -> u64 {
    declarations
        .iter()
        .zip(artifacts)
        .filter_map(|decl| match decl {
            (Decl::Def { value, .. }, artifact)
                if artifact.kind == HumanEquationCoreArtifactKind::HelperDefinition =>
            {
                Some(core_expr_node_count(value))
            }
            _ => None,
        })
        .max()
        .unwrap_or(0)
}

fn core_declaration_certificate_bytes(decl: &Decl) -> u64 {
    match decl {
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => declaration_certificate_bytes(
            name,
            universe_params,
            ty,
            value,
            match reducibility {
                Reducibility::Reducible => "reducible",
                Reducibility::Opaque => "opaque",
            },
        ),
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        } => declaration_certificate_bytes(name, universe_params, ty, proof, "theorem"),
        _ => 0,
    }
}

fn declaration_certificate_bytes(
    name: &str,
    universe_params: &[String],
    ty: &Expr,
    value: &Expr,
    kind: &str,
) -> u64 {
    let universe_param_bytes = universe_params
        .iter()
        .map(|param| param.len() as u64)
        .fold(0_u64, u64::saturating_add);
    (name.len() as u64)
        .saturating_add(kind.len() as u64)
        .saturating_add(universe_param_bytes)
        .saturating_add(npa_cert::core_expr_canonical_bytes(ty).len() as u64)
        .saturating_add(npa_cert::core_expr_canonical_bytes(value).len() as u64)
}

fn lowering_bundle_identity_input(artifacts: &[HumanEquationCoreArtifact]) -> String {
    let mut input = String::from("npa.frontend.equation.lowered-core-bundle.v0\n");
    for artifact in artifacts {
        let _ = writeln!(
            input,
            "artifact:{}:{}:{}",
            artifact.name,
            artifact.kind.as_str(),
            hash_hex(&artifact.core_hash)
        );
    }
    input
}

fn share_repeated_closed_result_terms(
    body: Expr,
    result_type: &Expr,
    row_values: &BTreeMap<usize, Expr>,
) -> Result<Expr, HumanEquationLoweringError> {
    let mut candidates = row_values
        .values()
        .filter(|expr| !expr_contains_bvar(expr))
        .map(|expr| {
            (
                hash_hex(&npa_cert::core_expr_hash(expr)),
                core_expr_node_count(expr),
                expr.clone(),
            )
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
    candidates.dedup_by(|lhs, rhs| lhs.0 == rhs.0);

    let result_type_nodes = core_expr_node_count(result_type);
    let mut best: Option<(u64, String, Expr)> = None;
    for (hash, candidate_nodes, candidate) in candidates {
        if candidate_nodes <= 1 {
            continue;
        }
        let occurrences = count_nonoverlapping_subterm_occurrences(&body, &candidate);
        if occurrences < 2 {
            continue;
        }
        let old_nodes = candidate_nodes.saturating_mul(occurrences);
        let shared_nodes = 1_u64
            .saturating_add(result_type_nodes)
            .saturating_add(candidate_nodes)
            .saturating_add(occurrences);
        if shared_nodes >= old_nodes {
            continue;
        }
        let saved_nodes = old_nodes.saturating_sub(shared_nodes);
        let should_replace_best = match &best {
            None => true,
            Some((best_saved, best_hash, _)) => {
                saved_nodes > *best_saved || (saved_nodes == *best_saved && hash < *best_hash)
            }
        };
        if should_replace_best {
            best = Some((saved_nodes, hash, candidate));
        }
    }

    let Some((_, hash, candidate)) = best else {
        return Ok(body);
    };
    let shifted_body = npa_kernel::subst::shift(&body, 1, 0).map_err(|err| {
        HumanEquationLoweringError::UnsupportedNestedOrMutualLowering {
            reason: format!("failed to shift generated body for let sharing: {err:?}"),
        }
    })?;
    let shared_body = replace_closed_subterm_with_bvar(shifted_body, &candidate, 0);
    Ok(Expr::let_in(
        format!("__eqc_shared_{}", &hash[..12]),
        result_type.clone(),
        candidate,
        shared_body,
    ))
}

fn expr_contains_bvar(expr: &Expr) -> bool {
    match expr {
        Expr::BVar(_) => true,
        Expr::Sort(_) | Expr::Const { .. } => false,
        Expr::App(fun, arg) => expr_contains_bvar(fun) || expr_contains_bvar(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_contains_bvar(ty) || expr_contains_bvar(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => expr_contains_bvar(ty) || expr_contains_bvar(value) || expr_contains_bvar(body),
    }
}

fn count_nonoverlapping_subterm_occurrences(expr: &Expr, candidate: &Expr) -> u64 {
    if expr == candidate {
        return 1;
    }
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => 0,
        Expr::App(fun, arg) => count_nonoverlapping_subterm_occurrences(fun, candidate)
            .saturating_add(count_nonoverlapping_subterm_occurrences(arg, candidate)),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            count_nonoverlapping_subterm_occurrences(ty, candidate)
                .saturating_add(count_nonoverlapping_subterm_occurrences(body, candidate))
        }
        Expr::Let {
            ty, value, body, ..
        } => count_nonoverlapping_subterm_occurrences(ty, candidate)
            .saturating_add(count_nonoverlapping_subterm_occurrences(value, candidate))
            .saturating_add(count_nonoverlapping_subterm_occurrences(body, candidate)),
    }
}

fn replace_closed_subterm_with_bvar(expr: Expr, candidate: &Expr, depth: u32) -> Expr {
    if &expr == candidate {
        return Expr::bvar(depth);
    }
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => expr,
        Expr::App(fun, arg) => Expr::app(
            replace_closed_subterm_with_bvar((*fun).clone(), candidate, depth),
            replace_closed_subterm_with_bvar((*arg).clone(), candidate, depth),
        ),
        Expr::Lam { binder, ty, body } => Expr::lam(
            binder,
            replace_closed_subterm_with_bvar((*ty).clone(), candidate, depth),
            replace_closed_subterm_with_bvar((*body).clone(), candidate, depth.saturating_add(1)),
        ),
        Expr::Pi { binder, ty, body } => Expr::pi(
            binder,
            replace_closed_subterm_with_bvar((*ty).clone(), candidate, depth),
            replace_closed_subterm_with_bvar((*body).clone(), candidate, depth.saturating_add(1)),
        ),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => Expr::let_in(
            binder,
            replace_closed_subterm_with_bvar((*ty).clone(), candidate, depth),
            replace_closed_subterm_with_bvar((*value).clone(), candidate, depth),
            replace_closed_subterm_with_bvar((*body).clone(), candidate, depth.saturating_add(1)),
        ),
    }
}

fn core_expr_node_count(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => 1,
        Expr::App(func, arg) => 1_u64
            .saturating_add(core_expr_node_count(func))
            .saturating_add(core_expr_node_count(arg)),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => 1_u64
            .saturating_add(core_expr_node_count(ty))
            .saturating_add(core_expr_node_count(body)),
        Expr::Let {
            ty, value, body, ..
        } => 1_u64
            .saturating_add(core_expr_node_count(ty))
            .saturating_add(core_expr_node_count(value))
            .saturating_add(core_expr_node_count(body)),
    }
}

fn mark_redundant_row(
    matrix: &HumanEquationPatternMatrix,
    row_statuses: &mut [HumanEquationCoverageRowStatus],
    diagnostics: &mut Vec<HumanEquationCoverageDiagnostic>,
    row_index: usize,
    covered_by_rows: Vec<usize>,
    row_kind: HumanEquationCoverageRowStatusKind,
    diagnostic_kind: HumanEquationCoverageDiagnosticKind,
) {
    let row = &matrix.rows[row_index];
    row_statuses[row_index].kind = row_kind;
    row_statuses[row_index].covered_by_rows = covered_by_rows.clone();
    diagnostics.push(coverage_diagnostic(
        diagnostic_kind,
        vec![row_index],
        covered_by_rows,
        None,
        Vec::new(),
        None,
        row.provenance.source_span,
    ));
}

fn coverage_diagnostic(
    kind: HumanEquationCoverageDiagnosticKind,
    mut row_ids: Vec<usize>,
    mut covered_by_rows: Vec<usize>,
    column: Option<(usize, String)>,
    missing_constructors: Vec<HumanEquationPatternMatrixConstructor>,
    reason: Option<String>,
    primary_span: Span,
) -> HumanEquationCoverageDiagnostic {
    row_ids.sort_unstable();
    row_ids.dedup();
    covered_by_rows.sort_unstable();
    covered_by_rows.dedup();
    let (column_index, column_identity) = column
        .map(|(index, identity)| (Some(index), Some(identity)))
        .unwrap_or((None, None));
    let identity = coverage_diagnostic_identity(
        kind,
        &row_ids,
        &covered_by_rows,
        column_index,
        column_identity.as_deref(),
        &missing_constructors,
        reason.as_deref(),
    );
    HumanEquationCoverageDiagnostic {
        kind,
        identity,
        primary_span,
        row_ids,
        covered_by_rows,
        column_index,
        column_identity,
        missing_constructors,
        reason,
    }
}

fn coverage_diagnostic_identity(
    kind: HumanEquationCoverageDiagnosticKind,
    row_ids: &[usize],
    covered_by_rows: &[usize],
    column_index: Option<usize>,
    column_identity: Option<&str>,
    missing_constructors: &[HumanEquationPatternMatrixConstructor],
    reason: Option<&str>,
) -> String {
    let missing = missing_constructors
        .iter()
        .map(|constructor| constructor.constructor_key.as_str())
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{kind:?}|rows:{row_ids:?}|covered_by:{covered_by_rows:?}|column:{column_index:?}:{}|missing:{missing}|reason:{}",
        column_identity.unwrap_or(""),
        reason.unwrap_or("")
    )
}

fn coverage_diagnostic_sort_key(
    diagnostic: &HumanEquationCoverageDiagnostic,
) -> (
    HumanEquationCoverageDiagnosticKind,
    Vec<usize>,
    Option<usize>,
    Vec<String>,
    String,
) {
    (
        diagnostic.kind,
        diagnostic.row_ids.clone(),
        diagnostic.column_index,
        diagnostic
            .missing_constructors
            .iter()
            .map(|constructor| constructor.constructor_key.clone())
            .collect(),
        diagnostic.identity.clone(),
    )
}

fn row_signature(row: &HumanEquationPatternMatrixRow) -> String {
    row.cells
        .iter()
        .map(HumanEquationPatternMatrixCell::identity)
        .collect::<Vec<_>>()
        .join("|")
}

fn row_covers(
    earlier: &HumanEquationPatternMatrixRow,
    later: &HumanEquationPatternMatrixRow,
) -> bool {
    earlier
        .cells
        .iter()
        .zip(&later.cells)
        .all(|(earlier, later)| cell_covers(earlier, later))
}

fn cell_covers(
    earlier: &HumanEquationPatternMatrixCell,
    later: &HumanEquationPatternMatrixCell,
) -> bool {
    match (earlier, later) {
        (HumanEquationPatternMatrixCell::Default, _)
        | (HumanEquationPatternMatrixCell::Variable { .. }, _) => true,
        (
            HumanEquationPatternMatrixCell::Constructor {
                constructor_key: lhs,
                ..
            },
            HumanEquationPatternMatrixCell::Constructor {
                constructor_key: rhs,
                ..
            },
        ) => lhs == rhs,
        (
            HumanEquationPatternMatrixCell::Unavailable {
                blocked_by_constructor_key: lhs,
            },
            HumanEquationPatternMatrixCell::Unavailable {
                blocked_by_constructor_key: rhs,
            },
        ) => lhs == rhs,
        _ => false,
    }
}

fn default_row_is_exhausted_by_previous(
    matrix: &HumanEquationPatternMatrix,
    constructors: &HumanEquationConstructorFamilyTable,
    previous_rows: &[usize],
) -> bool {
    !matrix.constructors_by_column.is_empty()
        && missing_constructor_sets(matrix, constructors, previous_rows).is_empty()
}

fn missing_constructor_sets(
    matrix: &HumanEquationPatternMatrix,
    constructors: &HumanEquationConstructorFamilyTable,
    active_rows: &[usize],
) -> Vec<HumanEquationMissingConstructorSet> {
    let split_columns = matrix
        .constructors_by_column
        .iter()
        .filter_map(|set| {
            constructors
                .family_for_constructor_set(set)
                .map(|family| (set, family))
        })
        .collect::<Vec<_>>();
    if split_columns.is_empty() {
        return Vec::new();
    }

    let column_indexes = matrix
        .columns
        .iter()
        .map(|column| (column.path.clone(), column.index))
        .collect::<BTreeMap<_, _>>();
    let mut assignments = vec![None; matrix.columns.len()];
    let mut missing =
        BTreeMap::<(usize, String, Vec<String>), HumanEquationMissingConstructorSet>::new();
    collect_missing_constructor_sets_for_split(
        matrix,
        &split_columns,
        &column_indexes,
        0,
        active_rows,
        &mut assignments,
        &mut missing,
    );
    missing.into_values().collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CoverageAssignmentCell {
    Constructor { constructor_key: String },
    Unavailable { blocked_by_constructor_key: String },
}

fn collect_missing_constructor_sets_for_split(
    matrix: &HumanEquationPatternMatrix,
    split_columns: &[(
        &HumanEquationPatternMatrixConstructorSet,
        &HumanEquationConstructorFamily,
    )],
    column_indexes: &BTreeMap<HumanEquationPatternMatrixColumnPath, usize>,
    split_index: usize,
    candidate_rows: &[usize],
    assignments: &mut [Option<CoverageAssignmentCell>],
    missing: &mut BTreeMap<(usize, String, Vec<String>), HumanEquationMissingConstructorSet>,
) {
    let Some((set, family)) = split_columns.get(split_index).copied() else {
        return;
    };
    let options = coverage_assignment_options(matrix, column_indexes, assignments, set, family);
    for option in options {
        assignments[set.column_index] = Some(option.clone());
        let next_candidates = candidate_rows
            .iter()
            .copied()
            .filter(|row_index| {
                matrix.rows[*row_index]
                    .cells
                    .get(set.column_index)
                    .is_some_and(|cell| matrix_cell_covers_assignment(cell, &option))
            })
            .collect::<Vec<_>>();

        match option {
            CoverageAssignmentCell::Constructor { constructor_key }
                if next_candidates.is_empty() =>
            {
                let mut missing_constructors =
                    missing_constructors_for_prefix_column(matrix, set, family, candidate_rows);
                if missing_constructors.is_empty() {
                    missing_constructors.extend(
                        family
                            .constructors
                            .iter()
                            .find(|constructor| constructor.constructor_key == constructor_key)
                            .cloned(),
                    );
                }
                insert_missing_constructor_set(matrix, set, family, missing_constructors, missing);
            }
            CoverageAssignmentCell::Constructor { .. }
            | CoverageAssignmentCell::Unavailable { .. }
                if !next_candidates.is_empty() =>
            {
                collect_missing_constructor_sets_for_split(
                    matrix,
                    split_columns,
                    column_indexes,
                    split_index + 1,
                    &next_candidates,
                    assignments,
                    missing,
                );
            }
            CoverageAssignmentCell::Constructor { .. } => {}
            CoverageAssignmentCell::Unavailable { .. } => {}
        }

        assignments[set.column_index] = None;
    }
}

fn coverage_assignment_options(
    matrix: &HumanEquationPatternMatrix,
    column_indexes: &BTreeMap<HumanEquationPatternMatrixColumnPath, usize>,
    assignments: &[Option<CoverageAssignmentCell>],
    set: &HumanEquationPatternMatrixConstructorSet,
    family: &HumanEquationConstructorFamily,
) -> Vec<CoverageAssignmentCell> {
    if let Some(unavailable) = inactive_assignment_cell(
        &matrix.columns[set.column_index],
        column_indexes,
        assignments,
    ) {
        return vec![unavailable];
    }

    family
        .constructors
        .iter()
        .map(|constructor| CoverageAssignmentCell::Constructor {
            constructor_key: constructor.constructor_key.clone(),
        })
        .collect()
}

fn inactive_assignment_cell(
    column: &HumanEquationPatternMatrixColumn,
    column_indexes: &BTreeMap<HumanEquationPatternMatrixColumnPath, usize>,
    assignments: &[Option<CoverageAssignmentCell>],
) -> Option<CoverageAssignmentCell> {
    let mut parent_path = HumanEquationPatternMatrixColumnPath::root(column.path.root);
    for segment in &column.path.segments {
        let parent_index = column_indexes.get(&parent_path).copied()?;
        match assignments.get(parent_index).and_then(Option::as_ref) {
            Some(CoverageAssignmentCell::Constructor { constructor_key })
                if constructor_key == &segment.constructor_key =>
            {
                parent_path.segments.push(segment.clone());
            }
            Some(CoverageAssignmentCell::Constructor { .. })
            | Some(CoverageAssignmentCell::Unavailable { .. }) => {
                return Some(CoverageAssignmentCell::Unavailable {
                    blocked_by_constructor_key: segment.constructor_key.clone(),
                });
            }
            None => return None,
        }
    }
    None
}

fn matrix_cell_covers_assignment(
    cell: &HumanEquationPatternMatrixCell,
    assignment: &CoverageAssignmentCell,
) -> bool {
    match (cell, assignment) {
        (
            HumanEquationPatternMatrixCell::Default
            | HumanEquationPatternMatrixCell::Variable { .. },
            _,
        ) => true,
        (
            HumanEquationPatternMatrixCell::Constructor {
                constructor_key: lhs,
                ..
            },
            CoverageAssignmentCell::Constructor {
                constructor_key: rhs,
            },
        ) => lhs == rhs,
        (
            HumanEquationPatternMatrixCell::Unavailable {
                blocked_by_constructor_key: lhs,
            },
            CoverageAssignmentCell::Unavailable {
                blocked_by_constructor_key: rhs,
            },
        ) => lhs == rhs,
        _ => false,
    }
}

fn missing_constructors_for_prefix_column(
    matrix: &HumanEquationPatternMatrix,
    set: &HumanEquationPatternMatrixConstructorSet,
    family: &HumanEquationConstructorFamily,
    candidate_rows: &[usize],
) -> Vec<HumanEquationPatternMatrixConstructor> {
    if candidate_rows.iter().any(|row_index| {
        matches!(
            matrix.rows[*row_index].cells.get(set.column_index),
            Some(HumanEquationPatternMatrixCell::Default)
                | Some(HumanEquationPatternMatrixCell::Variable { .. })
        )
    }) {
        return Vec::new();
    }

    let seen = candidate_rows
        .iter()
        .filter_map(
            |row_index| match matrix.rows[*row_index].cells.get(set.column_index) {
                Some(HumanEquationPatternMatrixCell::Constructor {
                    constructor_key, ..
                }) => Some(constructor_key.clone()),
                _ => None,
            },
        )
        .collect::<BTreeSet<_>>();
    family
        .constructors
        .iter()
        .filter(|constructor| !seen.contains(&constructor.constructor_key))
        .cloned()
        .collect()
}

fn insert_missing_constructor_set(
    matrix: &HumanEquationPatternMatrix,
    set: &HumanEquationPatternMatrixConstructorSet,
    family: &HumanEquationConstructorFamily,
    missing_constructors: Vec<HumanEquationPatternMatrixConstructor>,
    missing: &mut BTreeMap<(usize, String, Vec<String>), HumanEquationMissingConstructorSet>,
) {
    let constructor_keys = missing_constructors
        .iter()
        .map(|constructor| constructor.constructor_key.clone())
        .collect::<Vec<_>>();
    if constructor_keys.is_empty() {
        return;
    }
    missing
        .entry((
            set.column_index,
            family.family_key.clone(),
            constructor_keys,
        ))
        .or_insert_with(|| HumanEquationMissingConstructorSet {
            column_index: set.column_index,
            column_identity: matrix.columns[set.column_index].identity.clone(),
            family_key: family.family_key.clone(),
            missing_constructors,
        });
}

fn missing_constructor_set_sort_key(
    set: &HumanEquationMissingConstructorSet,
) -> (usize, usize, String, Vec<String>) {
    (
        set.missing_constructors.len(),
        set.column_index,
        set.column_identity.clone(),
        set.missing_constructors
            .iter()
            .map(|constructor| constructor.constructor_key.clone())
            .collect(),
    )
}

fn collect_pattern_columns(
    path: HumanEquationPatternMatrixColumnPath,
    pattern: &HumanResolvedPattern,
    constructor_order: &HumanEquationConstructorOrder,
    paths: &mut BTreeSet<HumanEquationPatternMatrixColumnPath>,
    constructors_by_path: &mut BTreeMap<
        HumanEquationPatternMatrixColumnPath,
        BTreeMap<String, HumanGlobalRef>,
    >,
) {
    paths.insert(path.clone());

    let HumanResolvedPattern::Constructor { constructor, args } = pattern else {
        return;
    };
    let constructor_key = human_equation_global_ref_sort_key(constructor);
    let constructor_order_key =
        human_equation_constructor_branch_sort_key(constructor, constructor_order);
    constructors_by_path
        .entry(path.clone())
        .or_default()
        .insert(constructor_key.clone(), constructor.clone());

    for (argument_index, arg) in args.iter().enumerate() {
        collect_pattern_columns(
            path.child_with_order(
                constructor_key.clone(),
                constructor_order_key.clone(),
                argument_index,
            ),
            arg,
            constructor_order,
            paths,
            constructors_by_path,
        );
    }
}

fn constructor_sets_by_column(
    constructors_by_path: &BTreeMap<
        HumanEquationPatternMatrixColumnPath,
        BTreeMap<String, HumanGlobalRef>,
    >,
    column_indexes: &BTreeMap<HumanEquationPatternMatrixColumnPath, usize>,
    constructor_order: &HumanEquationConstructorOrder,
) -> Vec<HumanEquationPatternMatrixConstructorSet> {
    let mut sets = Vec::new();
    for (path, constructors) in constructors_by_path {
        let Some(column_index) = column_indexes.get(path) else {
            continue;
        };
        let mut constructors = constructors
            .iter()
            .map(|(constructor_key, constructor)| {
                let constructor_order_key =
                    human_equation_constructor_branch_sort_key(constructor, constructor_order);
                HumanEquationPatternMatrixConstructor {
                    constructor: constructor.clone(),
                    constructor_key: constructor_key.clone(),
                    constructor_order_key,
                }
            })
            .collect::<Vec<_>>();
        constructors.sort_by(|lhs, rhs| {
            lhs.constructor_order_key
                .cmp(&rhs.constructor_order_key)
                .then_with(|| lhs.constructor_key.cmp(&rhs.constructor_key))
        });
        sets.push(HumanEquationPatternMatrixConstructorSet {
            column_index: *column_index,
            column_path: path.clone(),
            constructors,
        });
    }
    sets
}

fn normalize_row(
    index: usize,
    row: &HumanResolvedEquationRow,
    columns: &[HumanEquationPatternMatrixColumn],
) -> HumanEquationPatternMatrixRow {
    match row {
        HumanResolvedEquationRow::Patterns {
            patterns,
            value_identity,
            span,
        } => HumanEquationPatternMatrixRow {
            index,
            provenance: HumanEquationPatternMatrixRowProvenance {
                source_row_index: index,
                source_span: *span,
                kind: HumanEquationPatternMatrixRowKind::Pattern,
            },
            cells: columns
                .iter()
                .map(|column| pattern_cell_for_column(patterns, &column.path))
                .collect(),
            value_identity: value_identity.clone(),
        },
        HumanResolvedEquationRow::Default {
            value_identity,
            span,
        } => HumanEquationPatternMatrixRow {
            index,
            provenance: HumanEquationPatternMatrixRowProvenance {
                source_row_index: index,
                source_span: *span,
                kind: HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion,
            },
            cells: columns
                .iter()
                .map(|_| HumanEquationPatternMatrixCell::Default)
                .collect(),
            value_identity: value_identity.clone(),
        },
    }
}

fn pattern_cell_for_column(
    patterns: &[HumanResolvedPattern],
    path: &HumanEquationPatternMatrixColumnPath,
) -> HumanEquationPatternMatrixCell {
    let Some(root_pattern) = patterns.get(path.root) else {
        return HumanEquationPatternMatrixCell::Default;
    };

    match pattern_at_path(root_pattern, &path.segments) {
        PatternAtPath::Pattern(pattern) => pattern_to_cell(pattern),
        PatternAtPath::Default => HumanEquationPatternMatrixCell::Default,
        PatternAtPath::Unavailable {
            blocked_by_constructor_key,
        } => HumanEquationPatternMatrixCell::Unavailable {
            blocked_by_constructor_key,
        },
    }
}

enum PatternAtPath<'a> {
    Pattern(&'a HumanResolvedPattern),
    Default,
    Unavailable { blocked_by_constructor_key: String },
}

fn pattern_at_path<'a>(
    pattern: &'a HumanResolvedPattern,
    segments: &[HumanEquationPatternMatrixPathSegment],
) -> PatternAtPath<'a> {
    let Some((segment, remaining)) = segments.split_first() else {
        return PatternAtPath::Pattern(pattern);
    };

    let HumanResolvedPattern::Constructor { constructor, args } = pattern else {
        return PatternAtPath::Default;
    };
    let actual_key = human_equation_global_ref_sort_key(constructor);
    if actual_key != segment.constructor_key {
        return PatternAtPath::Unavailable {
            blocked_by_constructor_key: segment.constructor_key.clone(),
        };
    }

    let Some(arg) = args.get(segment.argument_index) else {
        return PatternAtPath::Default;
    };
    pattern_at_path(arg, remaining)
}

fn pattern_to_cell(pattern: &HumanResolvedPattern) -> HumanEquationPatternMatrixCell {
    match pattern {
        HumanResolvedPattern::Variable { slot } => {
            HumanEquationPatternMatrixCell::Variable { slot: *slot }
        }
        HumanResolvedPattern::Constructor { constructor, args } => {
            HumanEquationPatternMatrixCell::Constructor {
                constructor: constructor.clone(),
                constructor_key: human_equation_global_ref_sort_key(constructor),
                arity: args.len(),
            }
        }
    }
}

fn equation_pattern_matrix_budget_usage(
    rows: &[HumanEquationPatternMatrixRow],
    constructors_by_column: &[HumanEquationPatternMatrixConstructorSet],
    column_count: usize,
) -> HumanEquationBudgetUsage {
    let pattern_matrix_cells = (rows.len() as u64).saturating_mul(column_count as u64);
    let constructor_cells = rows
        .iter()
        .flat_map(|row| &row.cells)
        .filter(|cell| matches!(cell, HumanEquationPatternMatrixCell::Constructor { .. }))
        .count() as u64;
    let default_expansion_width = constructors_by_column
        .iter()
        .map(|set| set.constructors.len() as u64)
        .sum::<u64>()
        .max(1);
    let default_expansions = rows
        .iter()
        .filter(|row| {
            row.provenance.kind == HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion
        })
        .count() as u64
        * default_expansion_width;

    HumanEquationBudgetUsage {
        pattern_matrix_cells,
        expanded_branches: (rows.len() as u64)
            .saturating_add(constructor_cells)
            .saturating_add(default_expansions),
        decision_tree_nodes: 0,
        decision_tree_branch_depth: 0,
        generated_helpers: 0,
        generated_core_nodes: 0,
        helper_body_nodes: 0,
        eq_rec_transports: 0,
        generated_certificate_bytes: 0,
    }
}

fn matrix_identity_input(
    columns: &[HumanEquationPatternMatrixColumn],
    rows: &[HumanEquationPatternMatrixRow],
    constructors_by_column: &[HumanEquationPatternMatrixConstructorSet],
) -> String {
    let mut input = String::from("npa.frontend.equation.pattern-matrix.v0\n");

    for column in columns {
        let _ = writeln!(input, "column:{}:{}", column.index, column.identity);
    }
    for set in constructors_by_column {
        let constructors = set
            .constructors
            .iter()
            .map(|constructor| constructor.constructor_key.as_str())
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(input, "constructors:{}:{}", set.column_index, constructors);
    }
    for row in rows {
        let kind = match row.provenance.kind {
            HumanEquationPatternMatrixRowKind::Pattern => "pattern",
            HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion => "default",
        };
        let cells = row
            .cells
            .iter()
            .map(HumanEquationPatternMatrixCell::identity)
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(
            input,
            "row:{}:{}:{}=>{}",
            row.index, kind, cells, row.value_identity
        );
    }

    input
}

pub fn human_equation_global_ref_sort_key(reference: &HumanGlobalRef) -> String {
    match reference {
        HumanGlobalRef::Imported {
            module,
            name,
            decl_interface_hash,
        } => format!(
            "imported:{}:{}:{}",
            module.as_dotted(),
            name.as_dotted(),
            hash_hex(decl_interface_hash)
        ),
        HumanGlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => format!(
            "builtin:{}:{}",
            name.as_dotted(),
            hash_hex(decl_interface_hash)
        ),
        HumanGlobalRef::Local { name, .. } => {
            format!("local:{}", name.as_dotted())
        }
        HumanGlobalRef::LocalGenerated { name, .. } => {
            format!("local-generated:{}", name.as_dotted())
        }
    }
}

fn human_equation_constructor_branch_sort_key(
    constructor: &HumanGlobalRef,
    constructor_order: &HumanEquationConstructorOrder,
) -> String {
    match constructor_order.position_for(constructor) {
        Some(position) => format!(
            "0:metadata:{position:016}:{}",
            human_equation_global_ref_sort_key(constructor)
        ),
        None => format!(
            "1:fallback:{}",
            human_equation_global_ref_sort_key(constructor)
        ),
    }
}

fn insert_constructor_position(
    order: &mut HumanEquationConstructorOrder,
    next_position: &mut u64,
    key: String,
) {
    if order.positions.contains_key(&key) {
        return;
    }
    order.positions.insert(key, *next_position);
    *next_position = next_position.saturating_add(1);
}

fn human_equation_constructor_reference_map(
    resolved: &ResolvedHumanModule,
) -> BTreeMap<String, HumanGlobalRef> {
    resolved
        .global_scope
        .imported
        .iter()
        .chain(resolved.global_scope.current.iter())
        .filter_map(|entry| match &entry.reference {
            HumanGlobalRef::Imported { .. } | HumanGlobalRef::LocalGenerated { .. } => Some((
                constructor_metadata_key_for_ref(&entry.reference),
                entry.reference.clone(),
            )),
            HumanGlobalRef::Builtin { .. } | HumanGlobalRef::Local { .. } => None,
        })
        .collect()
}

fn push_constructor_family_member(
    families: &mut BTreeMap<String, HumanEquationConstructorFamily>,
    family_key: String,
    parent_name: String,
    constructor: &HumanGlobalRef,
    constructor_order: &HumanEquationConstructorOrder,
) {
    families
        .entry(family_key.clone())
        .or_insert_with(|| HumanEquationConstructorFamily {
            family_key,
            parent_name,
            constructors: Vec::new(),
        })
        .constructors
        .push(HumanEquationPatternMatrixConstructor {
            constructor: constructor.clone(),
            constructor_key: human_equation_global_ref_sort_key(constructor),
            constructor_order_key: human_equation_constructor_branch_sort_key(
                constructor,
                constructor_order,
            ),
        });
}

fn constructor_metadata_key_for_ref(reference: &HumanGlobalRef) -> String {
    match reference {
        HumanGlobalRef::Imported { module, name, .. } => {
            format!("imported:{}:{}", module.as_dotted(), name.as_dotted())
        }
        HumanGlobalRef::Builtin { name, .. } => format!("builtin:{}", name.as_dotted()),
        HumanGlobalRef::Local { name, .. } => format!("local:{}", name.as_dotted()),
        HumanGlobalRef::LocalGenerated { name, .. } => {
            format!("local-generated:{}", name.as_dotted())
        }
    }
}

fn hash_hex(hash: &npa_cert::Hash) -> String {
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn sha256(bytes: &[u8]) -> npa_cert::Hash {
    Sha256::digest(bytes).into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compile_human_source_to_core, parse_human_module, resolve_human_module, FileId,
        HumanCompileOptions, HumanEquationSemanticIdentity, ResolvedHumanModule,
    };
    use npa_kernel::{eq, eq_refl, nat, nat_succ, nat_zero, type0, Decl, Expr};

    fn equation_options() -> HumanCompileOptions {
        HumanCompileOptions {
            enable_equation_compiler: true,
            ..HumanCompileOptions::default()
        }
    }

    fn resolve_source(source: &str) -> ResolvedHumanModule {
        let module = parse_human_module(FileId(0), source).expect("source should parse");
        resolve_human_module(
            npa_cert::Name::from_dotted("Current.Module"),
            module,
            &[],
            &equation_options(),
        )
        .expect("source should resolve")
    }

    fn normalize(source: &str) -> HumanEquationPatternMatrix {
        let resolved = resolve_source(source);
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        normalize_human_equation_pattern_matrix_with_constructor_order(
            &resolved.resolved_equations[0],
            &constructor_order,
            HumanEquationBudget::default(),
        )
        .expect("matrix should normalize")
    }

    fn coverage(source: &str) -> HumanEquationCoverageResult {
        coverage_with_options(source, HumanEquationCoverageOptions::default())
    }

    fn coverage_with_options(
        source: &str,
        options: HumanEquationCoverageOptions,
    ) -> HumanEquationCoverageResult {
        let resolved = resolve_source(source);
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrix = normalize_human_equation_pattern_matrix_with_constructor_order(
            &resolved.resolved_equations[0],
            &constructor_order,
            HumanEquationBudget::default(),
        )
        .expect("matrix should normalize");
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        check_human_equation_coverage_with_options(&matrix, &families, &options)
    }

    fn coverage_block(source: &str) -> HumanEquationCoverageBlockResult {
        let resolved = resolve_source(source);
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrices = resolved
            .resolved_equations
            .iter()
            .map(|equation| {
                normalize_human_equation_pattern_matrix_with_constructor_order(
                    equation,
                    &constructor_order,
                    HumanEquationBudget::default(),
                )
                .expect("matrix should normalize")
            })
            .collect::<Vec<_>>();
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        check_human_equation_coverage_block(&matrices, &families)
    }

    fn recursion(source: &str) -> HumanEquationRecursionResult {
        let (resolved, matrix) = recursion_inputs(source);
        check_human_equation_recursion(&resolved.resolved_equations[0], &matrix)
    }

    fn recursion_inputs(source: &str) -> (ResolvedHumanModule, HumanEquationPatternMatrix) {
        let resolved = resolve_source(source);
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrix = normalize_human_equation_pattern_matrix_with_constructor_order(
            &resolved.resolved_equations[0],
            &constructor_order,
            HumanEquationBudget::default(),
        )
        .expect("matrix should normalize");
        (resolved, matrix)
    }

    fn decision_tree(source: &str) -> HumanEquationDecisionTreeResult {
        decision_tree_with_budget(source, HumanEquationBudget::default())
            .expect("decision tree should construct")
    }

    fn decision_tree_with_budget(
        source: &str,
        budget: HumanEquationBudget,
    ) -> Result<HumanEquationDecisionTreeResult, HumanEquationDecisionTreeError> {
        let resolved = resolve_source(source);
        let equation = &resolved.resolved_equations[0];
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrix = normalize_human_equation_pattern_matrix_with_constructor_order(
            equation,
            &constructor_order,
            HumanEquationBudget::default(),
        )
        .expect("matrix should normalize");
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        let coverage = check_human_equation_coverage(&matrix, &families);
        assert!(
            coverage.accepted,
            "coverage should accept: {:?}",
            coverage.diagnostics
        );
        let recursion = check_human_equation_structural_recursion(equation, &matrix);
        assert!(
            recursion.accepted,
            "recursion should accept: {:?}",
            recursion.diagnostics
        );
        construct_human_equation_decision_tree(equation, &matrix, &coverage, &recursion, budget)
    }

    fn decision_tree_lowering_inputs(
        source: &str,
        budget: HumanEquationBudget,
    ) -> (
        ResolvedHumanModule,
        HumanEquationPatternMatrix,
        HumanEquationDecisionTreeResult,
    ) {
        let resolved = resolve_source(source);
        let equation = &resolved.resolved_equations[0];
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrix = normalize_human_equation_pattern_matrix_with_constructor_order(
            equation,
            &constructor_order,
            HumanEquationBudget::default(),
        )
        .expect("matrix should normalize");
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        let coverage = check_human_equation_coverage(&matrix, &families);
        assert!(
            coverage.accepted,
            "coverage should accept: {:?}",
            coverage.diagnostics
        );
        let recursion = check_human_equation_structural_recursion(equation, &matrix);
        assert!(
            recursion.accepted,
            "recursion should accept: {:?}",
            recursion.diagnostics
        );
        let decision = construct_human_equation_decision_tree(
            equation, &matrix, &coverage, &recursion, budget,
        )
        .expect("decision tree should construct");
        (resolved, matrix, decision)
    }

    fn nat_pred_lowering_inputs() -> (
        ResolvedHumanModule,
        HumanEquationPatternMatrix,
        HumanEquationDecisionTreeResult,
        HumanEquationLoweringProfile,
    ) {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let zero_key = constructor_key(&matrix, "Nat.zero");
        let succ_key = constructor_key(&matrix, "Nat.succ");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, nat_zero());
        row_values.insert(1, Expr::bvar(1));
        let profile = HumanEquationLoweringProfile {
            public_name: "pred".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("n", nat())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Nat.rec",
                nat(),
                vec![
                    constructor_lowering(zero_key, Vec::new()),
                    constructor_lowering(
                        succ_key,
                        vec![lowering_binder("k", nat()), lowering_binder("k_ih", nat())],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };
        (resolved, matrix, decision, profile)
    }

    fn lowering_binder(name: &str, ty: Expr) -> HumanEquationLoweringBinder {
        HumanEquationLoweringBinder {
            name: name.to_owned(),
            ty,
        }
    }

    fn constructor_lowering(
        constructor_key: String,
        minor_binders: Vec<HumanEquationLoweringBinder>,
    ) -> HumanEquationConstructorLoweringProfile {
        HumanEquationConstructorLoweringProfile {
            constructor_key,
            minor_binders,
            result_index_args: Vec::new(),
        }
    }

    fn indexed_constructor_lowering(
        constructor_key: String,
        minor_binders: Vec<HumanEquationLoweringBinder>,
        result_index_args: Vec<Expr>,
    ) -> HumanEquationConstructorLoweringProfile {
        HumanEquationConstructorLoweringProfile {
            constructor_key,
            minor_binders,
            result_index_args,
        }
    }

    fn recursor_lowering(
        recursor_name: &str,
        major_type: Expr,
        constructors: Vec<HumanEquationConstructorLoweringProfile>,
    ) -> HumanEquationRecursorLoweringProfile {
        HumanEquationRecursorLoweringProfile {
            recursor_name: recursor_name.to_owned(),
            universe_args: vec![type0()],
            parameters: Vec::new(),
            index_binders: Vec::new(),
            major_index_args: Vec::new(),
            major_type,
            motive_body: None,
            constructors,
        }
    }

    fn indexed_recursor_lowering(
        recursor_name: &str,
        index_binders: Vec<HumanEquationLoweringBinder>,
        major_index_args: Vec<Expr>,
        major_type: Expr,
        motive_body: Expr,
        constructors: Vec<HumanEquationConstructorLoweringProfile>,
    ) -> HumanEquationRecursorLoweringProfile {
        HumanEquationRecursorLoweringProfile {
            recursor_name: recursor_name.to_owned(),
            universe_args: vec![type0()],
            parameters: Vec::new(),
            index_binders,
            major_index_args,
            major_type,
            motive_body: Some(motive_body),
            constructors,
        }
    }

    fn unit_ty() -> Expr {
        Expr::konst("Unit", vec![])
    }

    fn dvec(index: Expr) -> Expr {
        Expr::app(Expr::konst("DVec", vec![]), index)
    }

    fn vec_ty(index: Expr) -> Expr {
        Expr::app(Expr::konst("Vec", vec![]), index)
    }

    fn eq_rec_vec_transport(
        source: Expr,
        target: Expr,
        proof: Expr,
        reason: &str,
    ) -> HumanEquationEqRecTransport {
        HumanEquationEqRecTransport {
            eq_rec_name: "Eq.rec".to_owned(),
            value_level: type0(),
            motive_level: type0(),
            source_type: nat(),
            source: source.clone(),
            motive: Expr::lam(
                "b",
                nat(),
                Expr::lam(
                    "h",
                    eq(
                        type0(),
                        nat(),
                        shift_for_motive_source(source),
                        Expr::bvar(0),
                    ),
                    vec_ty(Expr::bvar(1)),
                ),
            ),
            target,
            proof,
            reason: reason.to_owned(),
        }
    }

    fn shift_for_motive_source(source: Expr) -> Expr {
        npa_kernel::subst::shift(&source, 1, 0)
            .expect("test motive source should shift under the motive index binder")
    }

    fn constructor_key(matrix: &HumanEquationPatternMatrix, name: &str) -> String {
        matrix
            .constructors_by_column
            .iter()
            .flat_map(|set| set.constructors.iter())
            .find(|constructor| constructor_name(constructor) == name)
            .unwrap_or_else(|| panic!("constructor key for {name} should exist"))
            .constructor_key
            .clone()
    }

    fn manual_dvec_lowering_inputs(
        name: &str,
        budget: HumanEquationBudget,
    ) -> (
        HumanResolvedEquationItem,
        HumanEquationPatternMatrix,
        HumanEquationDecisionTreeResult,
    ) {
        let span = Span::empty(FileId(0));
        let nil = HumanGlobalRef::LocalGenerated {
            index: 1,
            name: npa_cert::Name::from_dotted("DVec.nil"),
        };
        let cons = HumanGlobalRef::LocalGenerated {
            index: 2,
            name: npa_cert::Name::from_dotted("DVec.cons"),
        };
        let nil_constructor = HumanEquationPatternMatrixConstructor {
            constructor_key: human_equation_global_ref_sort_key(&nil),
            constructor_order_key: "0000".to_owned(),
            constructor: nil,
        };
        let cons_constructor = HumanEquationPatternMatrixConstructor {
            constructor_key: human_equation_global_ref_sort_key(&cons),
            constructor_order_key: "0001".to_owned(),
            constructor: cons,
        };
        let column = HumanEquationPatternMatrixColumn {
            index: 0,
            path: HumanEquationPatternMatrixColumnPath::root(1),
            identity: "root:1".to_owned(),
        };
        let rows = vec![
            HumanEquationPatternMatrixRow {
                index: 0,
                provenance: HumanEquationPatternMatrixRowProvenance {
                    source_row_index: 0,
                    source_span: span,
                    kind: HumanEquationPatternMatrixRowKind::Pattern,
                },
                cells: vec![HumanEquationPatternMatrixCell::Constructor {
                    constructor: nil_constructor.constructor.clone(),
                    constructor_key: nil_constructor.constructor_key.clone(),
                    arity: 0,
                }],
                value_identity: "row:0".to_owned(),
            },
            HumanEquationPatternMatrixRow {
                index: 1,
                provenance: HumanEquationPatternMatrixRowProvenance {
                    source_row_index: 1,
                    source_span: span,
                    kind: HumanEquationPatternMatrixRowKind::Pattern,
                },
                cells: vec![HumanEquationPatternMatrixCell::Constructor {
                    constructor: cons_constructor.constructor.clone(),
                    constructor_key: cons_constructor.constructor_key.clone(),
                    arity: 3,
                }],
                value_identity: "row:1".to_owned(),
            },
        ];
        let constructors_by_column = vec![HumanEquationPatternMatrixConstructorSet {
            column_index: 0,
            column_path: column.path.clone(),
            constructors: vec![nil_constructor, cons_constructor],
        }];
        let budget_usage = HumanEquationBudgetUsage {
            pattern_matrix_cells: 2,
            expanded_branches: 4,
            decision_tree_nodes: 0,
            decision_tree_branch_depth: 0,
            generated_helpers: 0,
            generated_core_nodes: 0,
            helper_body_nodes: 0,
            eq_rec_transports: 0,
            generated_certificate_bytes: 0,
        };
        let columns = vec![column];
        let identity_input = matrix_identity_input(&columns, &rows, &constructors_by_column);
        let matrix = HumanEquationPatternMatrix {
            columns,
            rows,
            constructors_by_column,
            identity_hash: sha256(identity_input.as_bytes()),
            identity_input,
            budget_usage,
        };
        let equation = HumanResolvedEquationItem {
            source_name: crate::HumanName::new(vec![name.to_owned()], span),
            target: HumanGlobalRef::Local {
                index: 0,
                name: npa_cert::Name::from_dotted(name),
            },
            parameter_type_identities: vec!["global:local:00000000:Nat".to_owned(), "_".to_owned()],
            rows: (0..2)
                .map(|index| HumanResolvedEquationRow::Default {
                    value_identity: format!("row:{index}"),
                    span,
                })
                .collect(),
            termination: None,
            semantic_identity: HumanEquationSemanticIdentity {
                value: format!("manual-dvec-{name}"),
            },
        };
        let coverage = HumanEquationCoverageResult {
            exhaustive: true,
            accepted: true,
            row_statuses: (0..2)
                .map(|row_index| HumanEquationCoverageRowStatus {
                    row_index,
                    kind: HumanEquationCoverageRowStatusKind::Reachable,
                    covered_by_rows: Vec::new(),
                })
                .collect(),
            missing_constructor_sets: Vec::new(),
            diagnostics: Vec::new(),
        };
        let recursion = HumanEquationRecursionResult {
            accepted: true,
            graph: HumanEquationRecursionGraph::default(),
            diagnostics: Vec::new(),
        };
        let decision = construct_human_equation_decision_tree(
            &equation, &matrix, &coverage, &recursion, budget,
        )
        .expect("manual DVec decision tree should construct");
        (equation, matrix, decision)
    }

    fn manual_unit_lowering_inputs(
        budget: HumanEquationBudget,
    ) -> (
        HumanResolvedEquationItem,
        HumanEquationPatternMatrix,
        HumanEquationDecisionTreeResult,
    ) {
        let span = Span::empty(FileId(0));
        let unit_mk = HumanGlobalRef::LocalGenerated {
            index: 1,
            name: npa_cert::Name::from_dotted("Unit.mk"),
        };
        let constructor = HumanEquationPatternMatrixConstructor {
            constructor_key: human_equation_global_ref_sort_key(&unit_mk),
            constructor_order_key: "0000".to_owned(),
            constructor: unit_mk,
        };
        let column = HumanEquationPatternMatrixColumn {
            index: 0,
            path: HumanEquationPatternMatrixColumnPath::root(2),
            identity: "root:2".to_owned(),
        };
        let rows = vec![HumanEquationPatternMatrixRow {
            index: 0,
            provenance: HumanEquationPatternMatrixRowProvenance {
                source_row_index: 0,
                source_span: span,
                kind: HumanEquationPatternMatrixRowKind::Pattern,
            },
            cells: vec![HumanEquationPatternMatrixCell::Constructor {
                constructor: constructor.constructor.clone(),
                constructor_key: constructor.constructor_key.clone(),
                arity: 0,
            }],
            value_identity: "row:0".to_owned(),
        }];
        let constructors_by_column = vec![HumanEquationPatternMatrixConstructorSet {
            column_index: 0,
            column_path: column.path.clone(),
            constructors: vec![constructor],
        }];
        let budget_usage = HumanEquationBudgetUsage {
            pattern_matrix_cells: 1,
            expanded_branches: 2,
            decision_tree_nodes: 0,
            decision_tree_branch_depth: 0,
            generated_helpers: 0,
            generated_core_nodes: 0,
            helper_body_nodes: 0,
            eq_rec_transports: 0,
            generated_certificate_bytes: 0,
        };
        let columns = vec![column];
        let identity_input = matrix_identity_input(&columns, &rows, &constructors_by_column);
        let matrix = HumanEquationPatternMatrix {
            columns,
            rows,
            constructors_by_column,
            identity_hash: sha256(identity_input.as_bytes()),
            identity_input,
            budget_usage,
        };
        let equation = HumanResolvedEquationItem {
            source_name: crate::HumanName::new(vec!["cast_vec_on_unit".to_owned()], span),
            target: HumanGlobalRef::Local {
                index: 0,
                name: npa_cert::Name::from_dotted("cast_vec_on_unit"),
            },
            parameter_type_identities: vec![
                "global:local:00000000:Nat".to_owned(),
                "global:local:00000001:Vec".to_owned(),
                "global:local:00000002:Unit".to_owned(),
            ],
            rows: vec![HumanResolvedEquationRow::Default {
                value_identity: "row:0".to_owned(),
                span,
            }],
            termination: None,
            semantic_identity: HumanEquationSemanticIdentity {
                value: "manual-unit-cast".to_owned(),
            },
        };
        let coverage = HumanEquationCoverageResult {
            exhaustive: true,
            accepted: true,
            row_statuses: vec![HumanEquationCoverageRowStatus {
                row_index: 0,
                kind: HumanEquationCoverageRowStatusKind::Reachable,
                covered_by_rows: Vec::new(),
            }],
            missing_constructor_sets: Vec::new(),
            diagnostics: Vec::new(),
        };
        let recursion = HumanEquationRecursionResult {
            accepted: true,
            graph: HumanEquationRecursionGraph::default(),
            diagnostics: Vec::new(),
        };
        let decision = construct_human_equation_decision_tree(
            &equation, &matrix, &coverage, &recursion, budget,
        )
        .expect("manual Unit decision tree should construct");
        (equation, matrix, decision)
    }

    fn manual_bit_xor_lowering_inputs(
        budget: HumanEquationBudget,
    ) -> (
        HumanResolvedEquationItem,
        HumanEquationPatternMatrix,
        HumanEquationDecisionTreeResult,
    ) {
        let span = Span::empty(FileId(0));
        let off = HumanGlobalRef::LocalGenerated {
            index: 1,
            name: npa_cert::Name::from_dotted("Bit.off"),
        };
        let on = HumanGlobalRef::LocalGenerated {
            index: 2,
            name: npa_cert::Name::from_dotted("Bit.on"),
        };
        let off_constructor = HumanEquationPatternMatrixConstructor {
            constructor_key: human_equation_global_ref_sort_key(&off),
            constructor_order_key: "0000".to_owned(),
            constructor: off,
        };
        let on_constructor = HumanEquationPatternMatrixConstructor {
            constructor_key: human_equation_global_ref_sort_key(&on),
            constructor_order_key: "0001".to_owned(),
            constructor: on,
        };
        let constructors = vec![off_constructor.clone(), on_constructor.clone()];
        let columns = vec![
            HumanEquationPatternMatrixColumn {
                index: 0,
                path: HumanEquationPatternMatrixColumnPath::root(0),
                identity: "root:0".to_owned(),
            },
            HumanEquationPatternMatrixColumn {
                index: 1,
                path: HumanEquationPatternMatrixColumnPath::root(1),
                identity: "root:1".to_owned(),
            },
        ];
        let constructors_by_column = vec![
            HumanEquationPatternMatrixConstructorSet {
                column_index: 0,
                column_path: columns[0].path.clone(),
                constructors: constructors.clone(),
            },
            HumanEquationPatternMatrixConstructorSet {
                column_index: 1,
                column_path: columns[1].path.clone(),
                constructors,
            },
        ];
        let mk_row = |index: usize,
                      left: &HumanEquationPatternMatrixConstructor,
                      right: &HumanEquationPatternMatrixConstructor| {
            HumanEquationPatternMatrixRow {
                index,
                provenance: HumanEquationPatternMatrixRowProvenance {
                    source_row_index: index,
                    source_span: span,
                    kind: HumanEquationPatternMatrixRowKind::Pattern,
                },
                cells: vec![
                    HumanEquationPatternMatrixCell::Constructor {
                        constructor: left.constructor.clone(),
                        constructor_key: left.constructor_key.clone(),
                        arity: 0,
                    },
                    HumanEquationPatternMatrixCell::Constructor {
                        constructor: right.constructor.clone(),
                        constructor_key: right.constructor_key.clone(),
                        arity: 0,
                    },
                ],
                value_identity: format!("row:{index}"),
            }
        };
        let rows = vec![
            mk_row(0, &off_constructor, &off_constructor),
            mk_row(1, &off_constructor, &on_constructor),
            mk_row(2, &on_constructor, &off_constructor),
            mk_row(3, &on_constructor, &on_constructor),
        ];
        let budget_usage = HumanEquationBudgetUsage {
            pattern_matrix_cells: 8,
            expanded_branches: 8,
            decision_tree_nodes: 0,
            decision_tree_branch_depth: 0,
            generated_helpers: 0,
            generated_core_nodes: 0,
            helper_body_nodes: 0,
            eq_rec_transports: 0,
            generated_certificate_bytes: 0,
        };
        let identity_input = matrix_identity_input(&columns, &rows, &constructors_by_column);
        let matrix = HumanEquationPatternMatrix {
            columns,
            rows,
            constructors_by_column,
            identity_hash: sha256(identity_input.as_bytes()),
            identity_input,
            budget_usage,
        };
        let equation = HumanResolvedEquationItem {
            source_name: crate::HumanName::new(vec!["xor".to_owned()], span),
            target: HumanGlobalRef::Local {
                index: 0,
                name: npa_cert::Name::from_dotted("xor"),
            },
            parameter_type_identities: vec![
                "global:local:00000000:Bit".to_owned(),
                "global:local:00000000:Bit".to_owned(),
            ],
            rows: (0..4)
                .map(|index| HumanResolvedEquationRow::Default {
                    value_identity: format!("row:{index}"),
                    span,
                })
                .collect(),
            termination: None,
            semantic_identity: HumanEquationSemanticIdentity {
                value: "manual-bit-xor".to_owned(),
            },
        };
        let coverage = HumanEquationCoverageResult {
            exhaustive: true,
            accepted: true,
            row_statuses: (0..4)
                .map(|row_index| HumanEquationCoverageRowStatus {
                    row_index,
                    kind: HumanEquationCoverageRowStatusKind::Reachable,
                    covered_by_rows: Vec::new(),
                })
                .collect(),
            missing_constructor_sets: Vec::new(),
            diagnostics: Vec::new(),
        };
        let recursion = HumanEquationRecursionResult {
            accepted: true,
            graph: HumanEquationRecursionGraph::default(),
            diagnostics: Vec::new(),
        };
        let decision = construct_human_equation_decision_tree(
            &equation, &matrix, &coverage, &recursion, budget,
        )
        .expect("manual xor decision tree should construct");
        (equation, matrix, decision)
    }

    fn manual_bit_xor_profile(matrix: &HumanEquationPatternMatrix) -> HumanEquationLoweringProfile {
        let off_key = constructor_key(matrix, "Bit.off");
        let on_key = constructor_key(matrix, "Bit.on");
        let bit_ty = Expr::konst("Bit", vec![]);
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::konst("Bit.off", vec![]));
        row_values.insert(1, Expr::konst("Bit.on", vec![]));
        row_values.insert(2, Expr::konst("Bit.on", vec![]));
        row_values.insert(3, Expr::konst("Bit.off", vec![]));
        HumanEquationLoweringProfile {
            public_name: "xor".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("left", bit_ty.clone()),
                lowering_binder("right", bit_ty.clone()),
            ],
            result_type: bit_ty.clone(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Bit.rec",
                bit_ty,
                vec![
                    constructor_lowering(off_key, Vec::new()),
                    constructor_lowering(on_key, Vec::new()),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        }
    }

    fn verify_lowered_bundle(prelude: &str, bundle: &HumanEquationCoreArtifactBundle) {
        let mut module = compile_human_source_to_core(
            FileId(100),
            npa_cert::Name::from_dotted("Equation.Lowering.Test"),
            prelude,
            &[],
            &HumanCompileOptions::default(),
        )
        .expect("prelude source should elaborate to core");
        module.declarations.extend(bundle.declarations.clone());
        let cert = npa_cert::build_module_cert(module, &[])
            .expect("lowered equation core module should build a certificate");
        let bytes = npa_cert::encode_module_cert(&cert).expect("lowered certificate should encode");
        npa_cert::verify_module_cert(
            &bytes,
            &mut npa_cert::VerifierSession::new(),
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("lowered equation core module should verify through the checker");
    }

    fn public_definition_value<'a>(
        bundle: &'a HumanEquationCoreArtifactBundle,
        name: &str,
    ) -> &'a Expr {
        bundle
            .declarations
            .iter()
            .find_map(|decl| match decl {
                Decl::Def {
                    name: decl_name,
                    value,
                    ..
                } if decl_name == name => Some(value),
                _ => None,
            })
            .unwrap_or_else(|| panic!("public definition {name} should exist"))
    }

    fn theorem_type<'a>(bundle: &'a HumanEquationCoreArtifactBundle, name: &str) -> &'a Expr {
        bundle
            .declarations
            .iter()
            .find_map(|decl| match decl {
                Decl::Theorem {
                    name: decl_name,
                    ty,
                    ..
                } if decl_name == name => Some(ty),
                _ => None,
            })
            .unwrap_or_else(|| panic!("theorem {name} should exist"))
    }

    fn theorem_eq_sides(ty: &Expr) -> Option<(Expr, Expr)> {
        let mut body = ty;
        while let Expr::Pi {
            body: next_body, ..
        } = body
        {
            body = next_body;
        }
        let (head, args) = npa_kernel::expr::collect_apps(body);
        match (head, args.as_slice()) {
            (Expr::Const { name, .. }, [_, lhs, rhs]) if name == "Eq" => {
                Some((lhs.clone(), rhs.clone()))
            }
            _ => None,
        }
    }

    fn expression_contains_applied_const(expr: &Expr, target: &str, min_args: usize) -> bool {
        let (head, arity) = application_head_and_arity(expr);
        if arity >= min_args && matches!(head, Expr::Const { name, .. } if name == target) {
            return true;
        }
        match expr {
            Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => false,
            Expr::App(fun, arg) => {
                expression_contains_applied_const(fun, target, min_args)
                    || expression_contains_applied_const(arg, target, min_args)
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                expression_contains_applied_const(ty, target, min_args)
                    || expression_contains_applied_const(body, target, min_args)
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                expression_contains_applied_const(ty, target, min_args)
                    || expression_contains_applied_const(value, target, min_args)
                    || expression_contains_applied_const(body, target, min_args)
            }
        }
    }

    fn expression_contains_let(expr: &Expr) -> bool {
        match expr {
            Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => false,
            Expr::App(fun, arg) => expression_contains_let(fun) || expression_contains_let(arg),
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                expression_contains_let(ty) || expression_contains_let(body)
            }
            Expr::Let { .. } => true,
        }
    }

    fn application_head_and_arity(expr: &Expr) -> (&Expr, usize) {
        let mut head = expr;
        let mut arity = 0;
        while let Expr::App(fun, _) = head {
            head = fun;
            arity += 1;
        }
        (head, arity)
    }

    fn recursion_diagnostic_kinds(
        result: &HumanEquationRecursionResult,
    ) -> Vec<HumanEquationRecursionDiagnosticKind> {
        result
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.kind)
            .collect()
    }

    fn recursion_block_for_manual_equations(
        equations: Vec<HumanResolvedEquationItem>,
    ) -> HumanEquationRecursionBlockResult {
        let matrices = equations
            .iter()
            .map(|equation| {
                normalize_human_equation_pattern_matrix(equation, HumanEquationBudget::default())
                    .expect("matrix should normalize")
            })
            .collect::<Vec<_>>();
        check_human_equation_structural_recursion_block(&equations, &matrices)
    }

    fn local_ref(index: usize, dotted: &str) -> HumanGlobalRef {
        HumanGlobalRef::Local {
            index,
            name: npa_cert::Name::from_dotted(dotted),
        }
    }

    fn nat_succ_ref() -> HumanGlobalRef {
        let resolved = resolve_source(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def probe (n : Nat) : Nat where
| Nat.succ k => k",
        );
        let HumanResolvedEquationRow::Patterns { patterns, .. } =
            &resolved.resolved_equations[0].rows[0]
        else {
            panic!("expected pattern row");
        };
        let HumanResolvedPattern::Constructor { constructor, .. } = &patterns[0] else {
            panic!("expected constructor pattern");
        };
        constructor.clone()
    }

    fn manual_nat_succ_equation(
        name: &str,
        index: usize,
        callee: &str,
        callee_index: usize,
        argument_identity: &str,
    ) -> HumanResolvedEquationItem {
        let succ = nat_succ_ref();
        let target = local_ref(index, name);
        let callee = local_ref(callee_index, callee);
        HumanResolvedEquationItem {
            source_name: crate::HumanName::new(
                name.split('.').map(str::to_owned).collect(),
                Span::empty(FileId(index as u32)),
            ),
            target: target.clone(),
            parameter_type_identities: vec!["global:local:00000000:Nat".to_owned()],
            rows: vec![HumanResolvedEquationRow::Patterns {
                patterns: vec![HumanResolvedPattern::Constructor {
                    constructor: succ,
                    args: vec![HumanResolvedPattern::Variable { slot: 1 }],
                }],
                value_identity: format!(
                    "app({},{})",
                    recursion_global_identity(&callee),
                    argument_identity
                ),
                span: Span::empty(FileId(index as u32)),
            }],
            termination: None,
            semantic_identity: crate::HumanEquationSemanticIdentity {
                value: format!(
                    "manual-recursion:{}:{}:{}",
                    recursion_global_identity(&target),
                    recursion_global_identity(&callee),
                    argument_identity
                ),
            },
        }
    }

    fn constructor_name(constructor: &HumanEquationPatternMatrixConstructor) -> String {
        match &constructor.constructor {
            HumanGlobalRef::Imported { name, .. }
            | HumanGlobalRef::Builtin { name, .. }
            | HumanGlobalRef::Local { name, .. }
            | HumanGlobalRef::LocalGenerated { name, .. } => name.as_dotted(),
        }
    }

    fn diagnostic_kinds(
        result: &HumanEquationCoverageResult,
    ) -> Vec<HumanEquationCoverageDiagnosticKind> {
        result
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.kind)
            .collect()
    }

    fn missing_names(set: &HumanEquationMissingConstructorSet) -> Vec<String> {
        set.missing_constructors
            .iter()
            .map(constructor_name)
            .collect()
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct CoverageDiagnosticSnapshot {
        kind: HumanEquationCoverageDiagnosticKind,
        human_kind: crate::HumanDiagnosticKind,
        identity: String,
        primary_span: Span,
        row_ids: Vec<usize>,
        covered_by_rows: Vec<usize>,
        column_index: Option<usize>,
        column_identity: Option<String>,
        missing_constructors: Vec<String>,
        reason: Option<String>,
        payload_candidates: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct CoverageFailureSnapshot {
        exhaustive: bool,
        accepted: bool,
        row_statuses: Vec<(usize, HumanEquationCoverageRowStatusKind, Vec<usize>)>,
        missing_constructor_sets: Vec<(usize, String, Vec<String>)>,
        diagnostics: Vec<CoverageDiagnosticSnapshot>,
    }

    fn coverage_failure_snapshot(result: &HumanEquationCoverageResult) -> CoverageFailureSnapshot {
        CoverageFailureSnapshot {
            exhaustive: result.exhaustive,
            accepted: result.accepted,
            row_statuses: result
                .row_statuses
                .iter()
                .map(|status| {
                    (
                        status.row_index,
                        status.kind,
                        status.covered_by_rows.clone(),
                    )
                })
                .collect(),
            missing_constructor_sets: result
                .missing_constructor_sets
                .iter()
                .map(|set| {
                    (
                        set.column_index,
                        set.column_identity.clone(),
                        missing_names(set),
                    )
                })
                .collect(),
            diagnostics: result
                .diagnostics
                .iter()
                .map(|diagnostic| {
                    let human = diagnostic.to_human_diagnostic();
                    let payload_candidates = human
                        .payload
                        .as_ref()
                        .map(|payload| payload.candidates.clone())
                        .unwrap_or_default();
                    CoverageDiagnosticSnapshot {
                        kind: diagnostic.kind,
                        human_kind: diagnostic.human_kind(),
                        identity: diagnostic.identity.clone(),
                        primary_span: diagnostic.primary_span,
                        row_ids: diagnostic.row_ids.clone(),
                        covered_by_rows: diagnostic.covered_by_rows.clone(),
                        column_index: diagnostic.column_index,
                        column_identity: diagnostic.column_identity.clone(),
                        missing_constructors: diagnostic
                            .missing_constructors
                            .iter()
                            .map(constructor_name)
                            .collect(),
                        reason: diagnostic.reason.clone(),
                        payload_candidates,
                    }
                })
                .collect(),
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct RecursionDiagnosticSnapshot {
        kind: HumanEquationRecursionDiagnosticKind,
        human_kind: crate::HumanDiagnosticKind,
        identity: String,
        primary_span: Span,
        caller: Option<String>,
        callee: Option<String>,
        row_index: Option<usize>,
        call_identity: Option<String>,
        cycle: Vec<String>,
        payload_candidates: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct RecursionCallSnapshot {
        caller: String,
        callee: String,
        row_index: usize,
        call_identity: String,
        argument_mapping: Vec<String>,
        has_decrease_evidence: bool,
        measure_decrease_identity: Option<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MeasureObligationSnapshot {
        identity: String,
        caller: String,
        callee: String,
        row_index: usize,
        call_identity: String,
        relation_identity: String,
        has_proof: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct RecursionFailureSnapshot {
        accepted: bool,
        calls: Vec<RecursionCallSnapshot>,
        measure_obligations: Vec<MeasureObligationSnapshot>,
        nondecreasing_cycles: Vec<Vec<String>>,
        diagnostics: Vec<RecursionDiagnosticSnapshot>,
    }

    fn recursion_failure_snapshot(
        result: &HumanEquationRecursionResult,
    ) -> RecursionFailureSnapshot {
        RecursionFailureSnapshot {
            accepted: result.accepted,
            calls: result
                .graph
                .calls
                .iter()
                .map(|call| RecursionCallSnapshot {
                    caller: call.caller.clone(),
                    callee: call.callee.clone(),
                    row_index: call.row_index,
                    call_identity: call.call_identity.clone(),
                    argument_mapping: call.argument_mapping.clone(),
                    has_decrease_evidence: call.decrease_evidence.is_some(),
                    measure_decrease_identity: call
                        .measure_decrease
                        .as_ref()
                        .map(|obligation| obligation.identity.clone()),
                })
                .collect(),
            measure_obligations: result
                .graph
                .measure_obligations
                .iter()
                .map(|obligation| MeasureObligationSnapshot {
                    identity: obligation.identity.clone(),
                    caller: obligation.caller.clone(),
                    callee: obligation.callee.clone(),
                    row_index: obligation.row_index,
                    call_identity: obligation.call_identity.clone(),
                    relation_identity: obligation.relation_identity.clone(),
                    has_proof: obligation.proof.is_some(),
                })
                .collect(),
            nondecreasing_cycles: result
                .graph
                .nondecreasing_cycles
                .iter()
                .map(|cycle| cycle.definitions.clone())
                .collect(),
            diagnostics: result
                .diagnostics
                .iter()
                .map(|diagnostic| {
                    let human = diagnostic.to_human_diagnostic();
                    let payload_candidates = human
                        .payload
                        .as_ref()
                        .map(|payload| payload.candidates.clone())
                        .unwrap_or_default();
                    RecursionDiagnosticSnapshot {
                        kind: diagnostic.kind,
                        human_kind: diagnostic.human_kind(),
                        identity: diagnostic.identity.clone(),
                        primary_span: diagnostic.primary_span,
                        caller: diagnostic.caller.clone(),
                        callee: diagnostic.callee.clone(),
                        row_index: diagnostic.row_index,
                        call_identity: diagnostic.call_identity.clone(),
                        cycle: diagnostic.cycle.clone(),
                        payload_candidates,
                    }
                })
                .collect(),
        }
    }

    fn generated_term_budget_snapshot(
        err: HumanEquationLoweringError,
    ) -> (Vec<HumanEquationBudgetField>, HumanEquationBudgetUsage) {
        let HumanEquationLoweringError::GeneratedTermBudgetExceeded(err) = err else {
            panic!("expected generated-term budget error");
        };
        (err.exceeded, err.requested_usage)
    }

    fn matrix_budget_snapshot(
        err: HumanEquationMatrixError,
    ) -> (Vec<HumanEquationBudgetField>, HumanEquationBudgetUsage) {
        let HumanEquationMatrixError::GeneratedTermBudgetExceeded(err) = err;
        (err.exceeded, err.requested_usage)
    }

    fn decision_tree_budget_snapshot(
        err: HumanEquationDecisionTreeError,
    ) -> (Vec<HumanEquationBudgetField>, HumanEquationBudgetUsage) {
        let HumanEquationDecisionTreeError::GeneratedTermBudgetExceeded(err) = err;
        (err.exceeded, err.requested_usage)
    }

    fn equation_theorem_budget_snapshot(
        err: HumanEquationLoweringError,
    ) -> (
        Vec<HumanEquationTheoremBudgetField>,
        HumanEquationTheoremBudgetUsage,
    ) {
        let HumanEquationLoweringError::EquationTheoremBudgetExceeded(err) = err else {
            panic!("expected equation-theorem budget error");
        };
        (err.exceeded, err.requested_usage)
    }

    #[test]
    fn normalized_matrix_identity_ignores_binder_display_names() {
        let left = normalize(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k",
        );
        let right = normalize(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat

def pred (m : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ value => value",
        );

        assert_eq!(left.columns, right.columns);
        assert_eq!(
            left.rows
                .iter()
                .map(|row| (&row.cells, &row.value_identity))
                .collect::<Vec<_>>(),
            right
                .rows
                .iter()
                .map(|row| (&row.cells, &row.value_identity))
                .collect::<Vec<_>>()
        );
        assert_eq!(left.identity_input, right.identity_input);
        assert_eq!(left.identity_hash, right.identity_hash);
    }

    #[test]
    fn constructor_branch_order_uses_canonical_constructor_order() {
        let matrix = normalize(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def source_reversed (n : Nat) : Nat where
| Nat.succ k => k
| Nat.zero => Nat.zero",
        );

        assert_eq!(matrix.constructors_by_column.len(), 1);
        let names = matrix.constructors_by_column[0]
            .constructors
            .iter()
            .map(constructor_name)
            .collect::<Vec<_>>();
        assert_eq!(names, vec!["Nat.zero", "Nat.succ"]);
    }

    #[test]
    fn nested_constructor_patterns_expand_to_stable_columns() {
        let matrix = normalize(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def left_leaf_value (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero",
        );

        let column_identities = matrix
            .columns
            .iter()
            .map(|column| column.identity.as_str())
            .collect::<Vec<_>>();
        assert_eq!(column_identities.len(), 4);
        assert!(column_identities[0].starts_with("root:0"));
        assert!(column_identities[1].contains("Tree.node"));
        assert!(column_identities[2].contains("Tree.leaf"));
        assert!(column_identities[3].contains("arg:1"));

        let first_row = &matrix.rows[0];
        assert!(matches!(
            first_row.cells[0],
            HumanEquationPatternMatrixCell::Constructor { .. }
        ));
        assert!(matches!(
            first_row.cells[1],
            HumanEquationPatternMatrixCell::Constructor { .. }
        ));
        assert!(matches!(
            first_row.cells[2],
            HumanEquationPatternMatrixCell::Variable { .. }
        ));
        assert!(matches!(
            first_row.cells[3],
            HumanEquationPatternMatrixCell::Variable { .. }
        ));
    }

    #[test]
    fn explicit_default_row_expands_across_known_columns() {
        let matrix = normalize(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def defaulted (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero",
        );

        let default_row = &matrix.rows[1];
        assert_eq!(
            default_row.provenance.kind,
            HumanEquationPatternMatrixRowKind::ExplicitDefaultExpansion
        );
        assert_eq!(default_row.cells.len(), matrix.columns.len());
        assert!(default_row
            .cells
            .iter()
            .all(|cell| matches!(cell, HumanEquationPatternMatrixCell::Default)));
    }

    #[test]
    fn pattern_matrix_cell_budget_overflow_is_reported_before_matrix_output() {
        let resolved = resolve_source(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def over_budget (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero",
        );
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);

        let err = normalize_human_equation_pattern_matrix_with_constructor_order(
            &resolved.resolved_equations[0],
            &constructor_order,
            HumanEquationBudget::new(3, u64::MAX),
        )
        .expect_err("normalization should fail before returning a matrix");
        let HumanEquationMatrixError::GeneratedTermBudgetExceeded(err) = err;
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::PatternMatrixCells]
        );
        assert_eq!(err.requested_usage.pattern_matrix_cells, 8);
    }

    #[test]
    fn expanded_branch_budget_overflow_counts_nested_and_default_expansion() {
        let resolved = resolve_source(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def branchy (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero",
        );
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);

        let err = normalize_human_equation_pattern_matrix_with_constructor_order(
            &resolved.resolved_equations[0],
            &constructor_order,
            HumanEquationBudget::new(u64::MAX, 4),
        )
        .expect_err("nested/default expansion should be budgeted");
        let HumanEquationMatrixError::GeneratedTermBudgetExceeded(err) = err;
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::ExpandedBranches]
        );
        assert_eq!(err.requested_usage.expanded_branches, 6);
    }

    #[test]
    fn coverage_accepts_exhaustive_nat_patterns() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k",
        );

        assert!(result.exhaustive);
        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn coverage_reports_non_exhaustive_list_patterns_with_smallest_missing_set() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def head_or_zero (xs : List) : Nat where
| List.cons x rest => x",
        );

        assert!(!result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns]
        );
        assert_eq!(result.missing_constructor_sets.len(), 1);
        assert_eq!(
            missing_names(&result.missing_constructor_sets[0]),
            vec!["List.nil"]
        );
        assert_eq!(
            result.diagnostics[0].human_kind(),
            crate::HumanDiagnosticKind::NonExhaustivePatterns
        );
    }

    #[test]
    fn coverage_reports_missing_multi_column_constructor_combinations() {
        let result = coverage(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def diagonal (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.on Bit.on => Bit.on",
        );

        assert!(!result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns]
        );
        assert_eq!(result.missing_constructor_sets.len(), 2);
        assert_eq!(
            result
                .missing_constructor_sets
                .iter()
                .map(missing_names)
                .collect::<Vec<_>>(),
            vec![vec!["Bit.on"], vec!["Bit.off"]]
        );
    }

    #[test]
    fn coverage_keeps_default_reachable_for_missing_multi_column_combinations() {
        let result = coverage(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def diagonal_default (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.on Bit.on => Bit.on
| default => Bit.off",
        );

        assert!(result.exhaustive);
        assert!(result.accepted);
        assert_eq!(
            result.row_statuses[2].kind,
            HumanEquationCoverageRowStatusKind::Reachable
        );
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn coverage_block_rejects_when_any_member_is_not_accepted() {
        let result = coverage_block(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def complete (bit : Bit) : Bit where
| Bit.off => Bit.off
| Bit.on => Bit.on
def partial (bit : Bit) : Bit where
| Bit.off => Bit.off",
        );

        assert!(!result.accepted);
        assert_eq!(result.results.len(), 2);
        assert!(result.results[0].accepted);
        assert_eq!(
            diagnostic_kinds(&result.results[1]),
            vec![HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns]
        );
    }

    #[test]
    fn coverage_checks_nested_tree_pattern_expansion() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def left_leaf_value (t : Tree) : Nat where
| Tree.leaf n => n
| Tree.node (Tree.leaf n) right => n",
        );

        assert!(!result.exhaustive);
        assert_eq!(result.missing_constructor_sets.len(), 1);
        assert!(result.missing_constructor_sets[0]
            .column_identity
            .contains("Tree.node"));
        assert_eq!(
            missing_names(&result.missing_constructor_sets[0]),
            vec!["Tree.node"]
        );
    }

    #[test]
    fn coverage_accepts_explicit_default_without_hiding_other_errors() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def defaulted (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero",
        );

        assert!(result.exhaustive);
        assert!(result.accepted);
        assert!(result.missing_constructor_sets.is_empty());
    }

    #[test]
    fn coverage_accepts_single_constructor_vector_fixture() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Vector : forall (n : Nat), Type where
| mk : forall (n : Nat), Vector n
def vector_index (xs : Vector Nat.zero) : Nat where
| Vector.mk n => n",
        );

        assert!(result.exhaustive);
        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn coverage_reports_duplicate_rows_as_redundant_equations() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def dup (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.zero => Nat.zero
| Nat.succ k => k",
        );

        assert!(result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            result.row_statuses[1].kind,
            HumanEquationCoverageRowStatusKind::Duplicate
        );
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::DuplicateBranch]
        );
        assert_eq!(
            result.diagnostics[0].human_kind(),
            crate::HumanDiagnosticKind::RedundantEquation
        );
    }

    #[test]
    fn coverage_reports_unreachable_nested_rows_after_normalization() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def unreachable_nested (t : Tree) : Nat where
| Tree.node left right => Nat.zero
| Tree.node (Tree.leaf n) right => n
| Tree.leaf n => n",
        );

        assert!(result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            result.row_statuses[1].kind,
            HumanEquationCoverageRowStatusKind::Unreachable
        );
        assert_eq!(result.row_statuses[1].covered_by_rows, vec![0]);
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::UnreachableBranch]
        );
    }

    #[test]
    fn coverage_reports_default_wildcard_shadowing() {
        let result = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def shadowed (n : Nat) : Nat where
| default => Nat.zero
| Nat.zero => Nat.zero",
        );

        assert!(result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            result.row_statuses[1].kind,
            HumanEquationCoverageRowStatusKind::WildcardShadowed
        );
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::WildcardShadowing]
        );
    }

    #[test]
    fn coverage_reports_impossible_indexed_branch_even_with_default() {
        let result = coverage_with_options(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Fin : forall (n : Nat), Type where
| zero : forall (n : Nat), Fin (Nat.succ n)
| succ : forall (n : Nat), forall (i : Fin n), Fin (Nat.succ n)
def impossible_fin (i : Fin Nat.zero) : Nat where
| Fin.zero n => Nat.zero
| default => Nat.zero",
            HumanEquationCoverageOptions {
                impossible_rows: vec![HumanEquationImpossibleBranchFact {
                    row_index: 0,
                    reason: "Fin.zero cannot inhabit Fin Nat.zero".to_owned(),
                }],
                proved_impossible_rows: Vec::new(),
            },
        );

        assert!(result.exhaustive);
        assert!(!result.accepted);
        assert_eq!(
            result.row_statuses[0].kind,
            HumanEquationCoverageRowStatusKind::Impossible
        );
        assert_eq!(
            diagnostic_kinds(&result),
            vec![HumanEquationCoverageDiagnosticKind::ImpossibleBranch]
        );
        assert_eq!(
            result.diagnostics[0].human_kind(),
            crate::HumanDiagnosticKind::ImpossibleBranchNotProvable
        );
    }

    #[test]
    fn coverage_diagnostic_identity_ignores_source_spans() {
        let left = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def partial (n : Nat) : Nat where
| Nat.zero => Nat.zero",
        );
        let right = coverage(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat

def partial (n : Nat) : Nat where
| Nat.zero => Nat.zero",
        );

        assert_eq!(
            left.diagnostics
                .iter()
                .map(|diagnostic| diagnostic.identity.as_str())
                .collect::<Vec<_>>(),
            right
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.identity.as_str())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn negative_coverage_fixtures_are_structured_and_deterministic() {
        let non_exhaustive = || {
            coverage(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def head_or_zero (xs : List) : Nat where
| List.cons x rest => x",
            )
        };
        let duplicate = || {
            coverage(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def dup (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.zero => Nat.zero
| Nat.succ k => k",
            )
        };
        let impossible = || {
            coverage_with_options(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Fin : forall (n : Nat), Type where
| zero : forall (n : Nat), Fin (Nat.succ n)
| succ : forall (n : Nat), forall (i : Fin n), Fin (Nat.succ n)
def impossible_fin (i : Fin Nat.zero) : Nat where
| Fin.zero n => Nat.zero
| default => Nat.zero",
                HumanEquationCoverageOptions {
                    impossible_rows: vec![HumanEquationImpossibleBranchFact {
                        row_index: 0,
                        reason: "Fin.zero cannot inhabit Fin Nat.zero".to_owned(),
                    }],
                    proved_impossible_rows: Vec::new(),
                },
            )
        };

        let cases = [
            (
                coverage_failure_snapshot(&non_exhaustive()),
                vec![HumanEquationCoverageDiagnosticKind::NonExhaustivePatterns],
            ),
            (
                coverage_failure_snapshot(&duplicate()),
                vec![HumanEquationCoverageDiagnosticKind::DuplicateBranch],
            ),
            (
                coverage_failure_snapshot(&impossible()),
                vec![HumanEquationCoverageDiagnosticKind::ImpossibleBranch],
            ),
        ];
        let repeated = [
            coverage_failure_snapshot(&non_exhaustive()),
            coverage_failure_snapshot(&duplicate()),
            coverage_failure_snapshot(&impossible()),
        ];

        for ((snapshot, expected_kinds), repeated_snapshot) in cases.into_iter().zip(repeated) {
            assert_eq!(snapshot, repeated_snapshot);
            assert!(!snapshot.accepted);
            assert_eq!(
                snapshot
                    .diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.kind)
                    .collect::<Vec<_>>(),
                expected_kinds
            );
        }
    }

    #[test]
    fn decision_tree_branch_order_uses_canonical_constructor_order() {
        let result = decision_tree(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def source_reversed (bit : Bit) : Bit where
| Bit.on => Bit.on
| Bit.off => Bit.off",
        );
        let canonical_source_order = decision_tree(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def source_reversed (bit : Bit) : Bit where
| Bit.off => Bit.off
| Bit.on => Bit.on",
        );

        let HumanEquationDecisionTreeNode::Switch(root) = &result.tree.root else {
            panic!("expected root switch");
        };
        let branch_names = root
            .branches
            .iter()
            .map(|branch| constructor_name(&branch.constructor))
            .collect::<Vec<_>>();
        assert_eq!(branch_names, vec!["Bit.off", "Bit.on"]);
        assert!(root.default_branch.is_none());
        assert_eq!(
            result.tree.identity_input,
            canonical_source_order.tree.identity_input
        );
        assert_eq!(
            result.tree.identity_hash,
            canonical_source_order.tree.identity_hash
        );
    }

    #[test]
    fn decision_tree_identity_and_sidecar_metrics_are_deterministic() {
        let left = decision_tree(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k",
        );
        let right = decision_tree(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat

def pred (m : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ value => value",
        );

        assert_eq!(left.tree.identity_input, right.tree.identity_input);
        assert_eq!(left.tree.identity_hash, right.tree.identity_hash);
        assert_eq!(left.sidecar_metrics, right.sidecar_metrics);
        assert_eq!(left.budget_usage, right.budget_usage);
        assert_eq!(
            left.sidecar_metrics,
            HumanEquationDecisionTreeMetrics {
                source_equations: 2,
                pattern_matrix_cells: 4,
                expanded_branches: 4,
                decision_tree_nodes: 3,
                generated_helpers: 0,
                maximum_branch_depth: 1,
            }
        );
    }

    #[test]
    fn decision_tree_recursive_call_identity_ignores_branch_source_order() {
        let reversed = decision_tree(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def length (xs : List) : Nat where
| List.cons x rest => length rest
| List.nil => Nat.zero",
        );
        let canonical = decision_tree(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def length (xs : List) : Nat where
| List.nil => Nat.zero
| List.cons x rest => length rest",
        );

        assert_eq!(reversed.tree.identity_input, canonical.tree.identity_input);
        assert_eq!(reversed.tree.identity_hash, canonical.tree.identity_hash);
        let HumanEquationDecisionTreeNode::Switch(root) = &reversed.tree.root else {
            panic!("expected root switch");
        };
        assert!(root.branches.iter().any(|branch| {
            matches!(
                branch.child.as_ref(),
                HumanEquationDecisionTreeNode::Leaf(leaf) if leaf.recursive_calls.len() == 1
            )
        }));
    }

    #[test]
    fn decision_tree_helper_split_plan_is_hash_derived_and_deterministic() {
        let budget = HumanEquationBudget::permissive().with_helper_split_node_threshold(2);
        let left = decision_tree_with_budget(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def xor (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off",
            budget,
        )
        .expect("decision tree should construct");
        let right = decision_tree_with_budget(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit

def xor (a : Bit) (b : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off",
            budget,
        )
        .expect("decision tree should construct");

        assert_eq!(left.helper_plan, right.helper_plan);
        assert_eq!(left.sidecar_metrics, right.sidecar_metrics);
        assert_eq!(
            left.sidecar_metrics,
            HumanEquationDecisionTreeMetrics {
                source_equations: 4,
                pattern_matrix_cells: 12,
                expanded_branches: 12,
                decision_tree_nodes: 7,
                generated_helpers: 2,
                maximum_branch_depth: 2,
            }
        );

        let helpers = &left.helper_plan.helpers;
        assert_eq!(helpers.len(), 2);
        assert_eq!(
            helpers
                .iter()
                .map(|helper| helper.ordinal)
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert!(helpers
            .iter()
            .all(|helper| helper.name.starts_with("xor.__eqc_match_")));
        assert!(helpers
            .iter()
            .all(|helper| helper.target_node_identity.starts_with("switch:")));
        assert!(helpers.iter().all(|helper| helper.node_count == 3));
        assert!(helpers.iter().all(|helper| helper.branch_depth == 1));
        assert!(helpers.iter().all(|helper| helper.dependencies.is_empty()));

        let mut helper_rows = helpers
            .iter()
            .map(|helper| helper.row_indexes.clone())
            .collect::<Vec<_>>();
        helper_rows.sort();
        assert_eq!(helper_rows, vec![vec![0, 1], vec![2, 3]]);
    }

    #[test]
    fn decision_tree_budget_overflow_is_structured() {
        let err = decision_tree_with_budget(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def xor (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off",
            HumanEquationBudget::permissive().with_decision_tree_limits(6, u64::MAX),
        )
        .expect_err("oversized decision tree should fail before output registration");
        let HumanEquationDecisionTreeError::GeneratedTermBudgetExceeded(err) = err;
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::DecisionTreeNodes]
        );
        assert_eq!(err.requested_usage.decision_tree_nodes, 7);
        assert_eq!(err.requested_usage.decision_tree_branch_depth, 2);
    }

    #[test]
    fn decision_tree_branch_depth_budget_overflow_is_structured() {
        let err = decision_tree_with_budget(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def xor (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off",
            HumanEquationBudget::permissive().with_decision_tree_limits(u64::MAX, 1),
        )
        .expect_err("over-deep decision tree should fail before output registration");
        let HumanEquationDecisionTreeError::GeneratedTermBudgetExceeded(err) = err;
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::DecisionTreeBranchDepth]
        );
        assert_eq!(err.requested_usage.decision_tree_branch_depth, 2);
    }

    #[test]
    fn decision_tree_generated_helper_budget_overflow_is_structured() {
        let err = decision_tree_with_budget(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit
def xor (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off",
            HumanEquationBudget::permissive()
                .with_helper_split_node_threshold(2)
                .with_max_generated_helpers(1),
        )
        .expect_err("oversized helper split plan should fail before output registration");
        let HumanEquationDecisionTreeError::GeneratedTermBudgetExceeded(err) = err;
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::GeneratedHelpers]
        );
        assert_eq!(err.requested_usage.generated_helpers, 2);
    }

    #[test]
    fn lowering_nat_pred_emits_checked_recursor_core() {
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("Nat pred should lower to a recursor application");

        assert_eq!(lowered.bundle.declarations.len(), 1);
        assert_eq!(
            lowered.bundle.artifacts[0].kind,
            HumanEquationCoreArtifactKind::PublicDefinition
        );
        assert!(!lowered.equation_theorems.requested);
        assert!(lowered.equation_theorems.theorem_specs.is_empty());
        assert_eq!(lowered.sidecar_metrics.generated_helpers, 0);
        assert_eq!(lowered.sidecar_metrics.generated_equation_theorems, 0);
        assert!(lowered.sidecar_metrics.generated_core_nodes > 0);
        verify_lowered_bundle("", &lowered.bundle);
    }

    #[test]
    fn equation_theorem_generation_is_opt_in_and_source_free_checked() {
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core_with_theorems(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
            HumanEquationTheoremRequest::computation_theorems(),
        )
        .expect("opt-in equation theorem generation should lower");

        assert!(lowered.equation_theorems.requested);
        assert_eq!(lowered.equation_theorems.theorem_specs.len(), 2);
        assert_eq!(lowered.sidecar_metrics.generated_equation_theorems, 2);
        assert_eq!(
            lowered
                .bundle
                .artifacts
                .iter()
                .filter(|artifact| artifact.kind == HumanEquationCoreArtifactKind::EquationTheorem)
                .count(),
            2
        );
        let theorem_names = lowered
            .equation_theorems
            .theorem_specs
            .iter()
            .map(|spec| spec.name.as_str())
            .collect::<Vec<_>>();
        assert!(theorem_names.iter().any(|name| name.contains(".zero.")));
        assert!(theorem_names.iter().any(|name| name.contains(".succ.")));
        assert!(lowered.bundle.declarations.iter().any(|decl| {
            matches!(decl, Decl::Theorem { name, .. } if name == theorem_names[0])
        }));
        let succ_theorem = theorem_names
            .iter()
            .find(|name| name.contains(".succ."))
            .expect("successor computation theorem should be named");
        let (lhs, rhs) = theorem_eq_sides(theorem_type(&lowered.bundle, succ_theorem))
            .expect("successor theorem should state an Eq");
        assert_ne!(lhs, rhs);
        assert_eq!(rhs, Expr::bvar(0));
        verify_lowered_bundle("", &lowered.bundle);
    }

    #[test]
    fn equation_theorem_names_are_stable_for_same_lowered_equation() {
        let (left_resolved, left_matrix, left_decision, left_profile) = nat_pred_lowering_inputs();
        let left = lower_human_equation_decision_tree_to_core_with_theorems(
            &left_resolved.resolved_equations[0],
            &left_matrix,
            &left_decision,
            left_profile,
            HumanEquationBudget::default(),
            HumanEquationTheoremRequest::computation_theorems(),
        )
        .expect("left theorem generation should lower");
        let (right_resolved, right_matrix, right_decision, right_profile) =
            nat_pred_lowering_inputs();
        let right = lower_human_equation_decision_tree_to_core_with_theorems(
            &right_resolved.resolved_equations[0],
            &right_matrix,
            &right_decision,
            right_profile,
            HumanEquationBudget::default(),
            HumanEquationTheoremRequest::computation_theorems(),
        )
        .expect("right theorem generation should lower");

        let left_names = left
            .equation_theorems
            .theorem_specs
            .iter()
            .map(|spec| spec.name.clone())
            .collect::<Vec<_>>();
        let right_names = right
            .equation_theorems
            .theorem_specs
            .iter()
            .map(|spec| spec.name.clone())
            .collect::<Vec<_>>();
        assert_eq!(left_names, right_names);
        assert_eq!(left.bundle.identity_hash, right.bundle.identity_hash);
    }

    #[test]
    fn equation_theorem_budget_overflow_rolls_back_to_checked_definition() {
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let err = lower_human_equation_decision_tree_to_core_with_theorems(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
            HumanEquationTheoremRequest::computation_theorems().with_budget(
                HumanEquationTheoremBudget::new(1, u64::MAX, u64::MAX, u64::MAX),
            ),
        )
        .expect_err("two theorem declarations should exceed a one-declaration budget");
        let HumanEquationLoweringError::EquationTheoremBudgetExceeded(err) = err else {
            panic!("expected theorem budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationTheoremBudgetField::GeneratedDeclarations]
        );

        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let err = lower_human_equation_decision_tree_to_core_with_theorems(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
            HumanEquationTheoremRequest::computation_theorems().with_budget(
                HumanEquationTheoremBudget::new(u64::MAX, u64::MAX, 1, u64::MAX),
            ),
        )
        .expect_err("generated theorem certificate bytes should be budgeted");
        let HumanEquationLoweringError::EquationTheoremBudgetExceeded(err) = err else {
            panic!("expected theorem byte budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationTheoremBudgetField::GeneratedCertificateBytes]
        );
        assert!(err.requested_usage.generated_certificate_bytes > 1);

        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("definition lowering should remain available after theorem failure");
        assert_eq!(lowered.bundle.declarations.len(), 1);
        assert!(lowered.equation_theorems.theorem_specs.is_empty());
        verify_lowered_bundle("", &lowered.bundle);
    }

    #[test]
    fn lowering_generated_core_node_budget_overflow_is_structured_and_retryable() {
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let err = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default().with_max_generated_core_nodes(1),
        )
        .expect_err("generated core-node overflow should reject before returning artifacts");
        let HumanEquationLoweringError::GeneratedTermBudgetExceeded(err) = err else {
            panic!("expected generated-term budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::GeneratedCoreNodes]
        );
        assert!(err.requested_usage.generated_core_nodes > 1);

        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("definition lowering should be retryable after a generated-term budget failure");
        assert_eq!(lowered.bundle.declarations.len(), 1);
        verify_lowered_bundle("", &lowered.bundle);
    }

    #[test]
    fn lowering_helper_body_budget_overflow_is_structured() {
        let budget = HumanEquationBudget::permissive()
            .with_helper_split_node_threshold(2)
            .with_max_helper_body_nodes(1);
        let (equation, matrix, decision) = manual_bit_xor_lowering_inputs(budget);
        let profile = manual_bit_xor_profile(&matrix);

        let err = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect_err("helper body overflow should reject before returning artifacts");
        let HumanEquationLoweringError::GeneratedTermBudgetExceeded(err) = err else {
            panic!("expected generated-term budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::HelperBodyNodes]
        );
        assert!(err.requested_usage.helper_body_nodes > 1);
    }

    #[test]
    fn lowering_generated_certificate_byte_budget_overflow_is_structured() {
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let err = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default().with_max_generated_certificate_bytes(1),
        )
        .expect_err("generated certificate-byte overflow should reject before returning artifacts");
        let HumanEquationLoweringError::GeneratedTermBudgetExceeded(err) = err else {
            panic!("expected generated-term budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::GeneratedCertificateBytes]
        );
        assert!(err.requested_usage.generated_certificate_bytes > 1);
    }

    #[test]
    fn negative_budget_fixtures_are_deterministic_and_rollback_safe() {
        let matrix_source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def over_budget (t : Tree) : Nat where
| Tree.node (Tree.leaf n) right => n
| default => Nat.zero";
        let matrix_cell_overflow = || {
            let resolved = resolve_source(matrix_source);
            let constructor_order =
                human_equation_constructor_order_from_resolved_module(&resolved);
            normalize_human_equation_pattern_matrix_with_constructor_order(
                &resolved.resolved_equations[0],
                &constructor_order,
                HumanEquationBudget::new(3, u64::MAX),
            )
            .expect_err("matrix cell overflow should fail before returning a matrix")
        };
        let expanded_branch_overflow = || {
            let resolved = resolve_source(matrix_source);
            let constructor_order =
                human_equation_constructor_order_from_resolved_module(&resolved);
            normalize_human_equation_pattern_matrix_with_constructor_order(
                &resolved.resolved_equations[0],
                &constructor_order,
                HumanEquationBudget::new(u64::MAX, 4),
            )
            .expect_err("expanded branch overflow should fail before returning a matrix")
        };
        assert_eq!(
            matrix_budget_snapshot(matrix_cell_overflow()),
            matrix_budget_snapshot(matrix_cell_overflow())
        );
        assert_eq!(
            matrix_budget_snapshot(expanded_branch_overflow()),
            matrix_budget_snapshot(expanded_branch_overflow())
        );
        assert!(normalize(matrix_source).rows.len() > 1);

        let xor_source = "\
inductive Bit : Type where
| off : Bit
| on : Bit
def xor (left : Bit) (right : Bit) : Bit where
| Bit.off Bit.off => Bit.off
| Bit.off Bit.on => Bit.on
| Bit.on Bit.off => Bit.on
| Bit.on Bit.on => Bit.off";
        let decision_depth_overflow = || {
            decision_tree_with_budget(
                xor_source,
                HumanEquationBudget::permissive().with_decision_tree_limits(u64::MAX, 1),
            )
            .expect_err("decision-tree branch depth overflow should return no decision result")
        };
        let helper_count_overflow = || {
            decision_tree_with_budget(
                xor_source,
                HumanEquationBudget::permissive()
                    .with_helper_split_node_threshold(2)
                    .with_max_generated_helpers(1),
            )
            .expect_err("helper count overflow should return no decision result")
        };
        assert_eq!(
            decision_tree_budget_snapshot(decision_depth_overflow()),
            decision_tree_budget_snapshot(decision_depth_overflow())
        );
        assert_eq!(
            decision_tree_budget_snapshot(helper_count_overflow()),
            decision_tree_budget_snapshot(helper_count_overflow())
        );
        assert_eq!(
            decision_tree(xor_source).budget_usage.decision_tree_nodes,
            7
        );

        let core_node_overflow = || {
            let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
            lower_human_equation_decision_tree_to_core(
                &resolved.resolved_equations[0],
                &matrix,
                &decision,
                profile,
                HumanEquationBudget::default().with_max_generated_core_nodes(1),
            )
            .expect_err("generated core-node overflow should return no lowered bundle")
        };
        let certificate_byte_overflow = || {
            let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
            lower_human_equation_decision_tree_to_core(
                &resolved.resolved_equations[0],
                &matrix,
                &decision,
                profile,
                HumanEquationBudget::default().with_max_generated_certificate_bytes(1),
            )
            .expect_err("generated certificate-byte overflow should return no lowered bundle")
        };
        assert_eq!(
            generated_term_budget_snapshot(core_node_overflow()),
            generated_term_budget_snapshot(core_node_overflow())
        );
        assert_eq!(
            generated_term_budget_snapshot(certificate_byte_overflow()),
            generated_term_budget_snapshot(certificate_byte_overflow())
        );
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("Nat pred should still lower after generated-term budget failures");
        assert_eq!(lowered.bundle.declarations.len(), 1);

        let helper_body_overflow = || {
            let budget = HumanEquationBudget::permissive()
                .with_helper_split_node_threshold(2)
                .with_max_helper_body_nodes(1);
            let (equation, matrix, decision) = manual_bit_xor_lowering_inputs(budget);
            let profile = manual_bit_xor_profile(&matrix);
            lower_human_equation_decision_tree_to_core(
                &equation, &matrix, &decision, profile, budget,
            )
            .expect_err("helper body overflow should return no lowered bundle")
        };
        assert_eq!(
            generated_term_budget_snapshot(helper_body_overflow()),
            generated_term_budget_snapshot(helper_body_overflow())
        );
        let helper_budget = HumanEquationBudget::permissive().with_helper_split_node_threshold(2);
        let (equation, matrix, decision) = manual_bit_xor_lowering_inputs(helper_budget);
        let lowered = lower_human_equation_decision_tree_to_core(
            &equation,
            &matrix,
            &decision,
            manual_bit_xor_profile(&matrix),
            helper_budget,
        )
        .expect("helper split lowering should still work after helper-body budget failure");
        assert_eq!(lowered.sidecar_metrics.generated_helpers, 2);

        let transport_overflow = || {
            let budget = HumanEquationBudget::default().with_max_generated_eq_rec_transports(0);
            let (equation, matrix, decision) = manual_unit_lowering_inputs(budget);
            let unit_key = constructor_key(&matrix, "Unit.mk");
            let mut row_values = BTreeMap::new();
            row_values.insert(0, Expr::bvar(1));
            let mut row_transports = BTreeMap::new();
            row_transports.insert(
                0,
                vec![eq_rec_vec_transport(
                    Expr::bvar(2),
                    Expr::bvar(2),
                    eq_refl(type0(), nat(), Expr::bvar(2)),
                    "deterministic transport budget fixture",
                )],
            );
            let profile = HumanEquationLoweringProfile {
                public_name: "cast_vec_on_unit".to_owned(),
                universe_params: Vec::new(),
                public_binders: vec![
                    lowering_binder("n", nat()),
                    lowering_binder("xs", vec_ty(Expr::bvar(0))),
                    lowering_binder("u", unit_ty()),
                ],
                result_type: vec_ty(Expr::bvar(2)),
                result_universe: type0(),
                recursors: vec![recursor_lowering(
                    "Unit.rec",
                    unit_ty(),
                    vec![constructor_lowering(unit_key, Vec::new())],
                )],
                row_values,
                row_transports,
            };
            lower_human_equation_decision_tree_to_core(
                &equation, &matrix, &decision, profile, budget,
            )
            .expect_err("Eq.rec transport overflow should return no lowered bundle")
        };
        assert_eq!(
            generated_term_budget_snapshot(transport_overflow()),
            generated_term_budget_snapshot(transport_overflow())
        );

        let theorem_budget_overflow = || {
            let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
            lower_human_equation_decision_tree_to_core_with_theorems(
                &resolved.resolved_equations[0],
                &matrix,
                &decision,
                profile,
                HumanEquationBudget::default(),
                HumanEquationTheoremRequest::computation_theorems().with_budget(
                    HumanEquationTheoremBudget::new(1, u64::MAX, u64::MAX, u64::MAX),
                ),
            )
            .expect_err("equation theorem budget overflow should roll back theorem artifacts")
        };
        assert_eq!(
            equation_theorem_budget_snapshot(theorem_budget_overflow()),
            equation_theorem_budget_snapshot(theorem_budget_overflow())
        );
        let (resolved, matrix, decision, profile) = nat_pred_lowering_inputs();
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("definition lowering should remain available after theorem budget failure");
        assert!(lowered.equation_theorems.theorem_specs.is_empty());
    }

    #[test]
    fn lowering_list_length_replaces_recursive_tail_call_with_minor_ih() {
        let source = "\
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def length (xs : List) : Nat where
| List.nil => Nat.zero
| List.cons x rest => length rest";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let nil_key = constructor_key(&matrix, "List.nil");
        let cons_key = constructor_key(&matrix, "List.cons");
        let list_ty = Expr::konst("List", vec![]);
        let mut row_values = BTreeMap::new();
        row_values.insert(0, nat_zero());
        row_values.insert(1, nat_succ(Expr::bvar(0)));
        let profile = HumanEquationLoweringProfile {
            public_name: "length".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("xs", list_ty.clone())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "List.rec",
                list_ty.clone(),
                vec![
                    constructor_lowering(nil_key, Vec::new()),
                    constructor_lowering(
                        cons_key,
                        vec![
                            lowering_binder("x", nat()),
                            lowering_binder("rest", list_ty.clone()),
                            lowering_binder("rest_ih", nat()),
                        ],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("List length should lower to a recursor application");

        assert_eq!(lowered.sidecar_metrics.decision_tree_nodes, 3);
        verify_lowered_bundle(
            "\
inductive List : Type where
| nil : List
| cons : Nat -> List -> List",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_tree_mirror_emits_two_recursive_minor_hypotheses() {
        let source = "\
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def mirror (t : Tree) : Tree where
| Tree.leaf n => Tree.leaf n
| Tree.node left right => Tree.node (mirror right) (mirror left)";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let leaf_key = constructor_key(&matrix, "Tree.leaf");
        let node_key = constructor_key(&matrix, "Tree.node");
        let tree_ty = Expr::konst("Tree", vec![]);
        let mut row_values = BTreeMap::new();
        row_values.insert(
            0,
            Expr::app(Expr::konst("Tree.leaf", vec![]), Expr::bvar(0)),
        );
        row_values.insert(
            1,
            Expr::apps(
                Expr::konst("Tree.node", vec![]),
                vec![Expr::bvar(0), Expr::bvar(2)],
            ),
        );
        let profile = HumanEquationLoweringProfile {
            public_name: "mirror".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("t", tree_ty.clone())],
            result_type: tree_ty.clone(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Tree.rec",
                tree_ty.clone(),
                vec![
                    constructor_lowering(leaf_key, vec![lowering_binder("n", nat())]),
                    constructor_lowering(
                        node_key,
                        vec![
                            lowering_binder("left", tree_ty.clone()),
                            lowering_binder("left_ih", tree_ty.clone()),
                            lowering_binder("right", tree_ty.clone()),
                            lowering_binder("right_ih", tree_ty.clone()),
                        ],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };
        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("Tree mirror should lower to a recursor application");

        assert_eq!(resolved.resolved_equations[0].rows.len(), 2);
        assert_eq!(lowered.sidecar_metrics.eq_rec_transports, 0);
        verify_lowered_bundle(
            "\
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_shares_repeated_closed_result_terms_with_let() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Bit : Type where
| off : Bit
| on : Bit
def to_two (b : Bit) : Nat where
| Bit.off => Nat.succ (Nat.succ Nat.zero)
| Bit.on => Nat.succ (Nat.succ Nat.zero)";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let off_key = constructor_key(&matrix, "Bit.off");
        let on_key = constructor_key(&matrix, "Bit.on");
        let bit_ty = Expr::konst("Bit", vec![]);
        let shared_value = nat_succ(nat_succ(nat_zero()));
        let mut row_values = BTreeMap::new();
        row_values.insert(0, shared_value.clone());
        row_values.insert(1, shared_value);
        let profile = HumanEquationLoweringProfile {
            public_name: "to_two".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("b", bit_ty.clone())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Bit.rec",
                bit_ty,
                vec![
                    constructor_lowering(off_key, Vec::new()),
                    constructor_lowering(on_key, Vec::new()),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let lowered = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect("repeated closed result terms should lower with sharing");

        assert!(expression_contains_let(public_definition_value(
            &lowered.bundle,
            "to_two",
        )));
        assert_eq!(
            lowered.sidecar_metrics.pattern_matrix_cells,
            lowered.budget_usage.pattern_matrix_cells
        );
        assert_eq!(
            lowered.sidecar_metrics.expanded_branches,
            lowered.budget_usage.expanded_branches
        );
        verify_lowered_bundle(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Bit : Type where
| off : Bit
| on : Bit",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_helper_split_emits_reducible_helper_definitions() {
        let budget = HumanEquationBudget::permissive().with_helper_split_node_threshold(2);
        let (equation, matrix, decision) = manual_bit_xor_lowering_inputs(budget);
        let off_key = constructor_key(&matrix, "Bit.off");
        let on_key = constructor_key(&matrix, "Bit.on");
        let bit_ty = Expr::konst("Bit", vec![]);
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::konst("Bit.off", vec![]));
        row_values.insert(1, Expr::konst("Bit.on", vec![]));
        row_values.insert(2, Expr::konst("Bit.on", vec![]));
        row_values.insert(3, Expr::konst("Bit.off", vec![]));
        let profile = HumanEquationLoweringProfile {
            public_name: "xor".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("left", bit_ty.clone()),
                lowering_binder("right", bit_ty.clone()),
            ],
            result_type: bit_ty.clone(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Bit.rec",
                bit_ty.clone(),
                vec![
                    constructor_lowering(off_key, Vec::new()),
                    constructor_lowering(on_key, Vec::new()),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };
        let lowered = lower_human_equation_decision_tree_to_core(
            &equation,
            &matrix,
            &decision,
            profile.clone(),
            budget,
        )
        .expect("helper split xor should lower to helper definitions");
        let repeated = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect("same helper split xor should lower deterministically");

        assert_eq!(lowered.bundle.declarations.len(), 3);
        assert_eq!(lowered.sidecar_metrics.generated_helpers, 2);
        assert_eq!(
            lowered
                .bundle
                .artifacts
                .iter()
                .filter(|artifact| artifact.kind == HumanEquationCoreArtifactKind::HelperDefinition)
                .count(),
            2
        );
        assert!(lowered
            .bundle
            .artifacts
            .iter()
            .all(|artifact| !artifact.opaque));
        let helper_signatures = lowered
            .bundle
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == HumanEquationCoreArtifactKind::HelperDefinition)
            .map(|artifact| (artifact.name.clone(), artifact.core_hash))
            .collect::<Vec<_>>();
        let repeated_helper_signatures = repeated
            .bundle
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == HumanEquationCoreArtifactKind::HelperDefinition)
            .map(|artifact| (artifact.name.clone(), artifact.core_hash))
            .collect::<Vec<_>>();
        assert_eq!(helper_signatures, repeated_helper_signatures);
        verify_lowered_bundle(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit",
            &lowered.bundle,
        );
    }

    #[test]
    fn equation_theorem_generation_names_helper_split_theorems() {
        let budget = HumanEquationBudget::permissive().with_helper_split_node_threshold(2);
        let (equation, matrix, decision) = manual_bit_xor_lowering_inputs(budget);
        let off_key = constructor_key(&matrix, "Bit.off");
        let on_key = constructor_key(&matrix, "Bit.on");
        let bit_ty = Expr::konst("Bit", vec![]);
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::konst("Bit.off", vec![]));
        row_values.insert(1, Expr::konst("Bit.on", vec![]));
        row_values.insert(2, Expr::konst("Bit.on", vec![]));
        row_values.insert(3, Expr::konst("Bit.off", vec![]));
        let profile = HumanEquationLoweringProfile {
            public_name: "xor".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("left", bit_ty.clone()),
                lowering_binder("right", bit_ty.clone()),
            ],
            result_type: bit_ty.clone(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Bit.rec",
                bit_ty.clone(),
                vec![
                    constructor_lowering(off_key, Vec::new()),
                    constructor_lowering(on_key, Vec::new()),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };
        let lowered = lower_human_equation_decision_tree_to_core_with_theorems(
            &equation,
            &matrix,
            &decision,
            profile,
            budget,
            HumanEquationTheoremRequest::computation_theorems().with_helper_split_theorems(true),
        )
        .expect("helper split theorem generation should lower");

        let helper_specs = lowered
            .equation_theorems
            .theorem_specs
            .iter()
            .filter(|spec| spec.source == HumanEquationTheoremSource::HelperSplit)
            .collect::<Vec<_>>();
        assert_eq!(helper_specs.len(), 2);
        assert!(helper_specs.iter().all(|spec| {
            spec.name.contains(".eqn.helper.")
                && spec.helper_name.is_some()
                && spec.dependency_names == vec![spec.helper_name.clone().unwrap()]
        }));
        assert_eq!(
            lowered
                .bundle
                .artifacts
                .iter()
                .filter(|artifact| artifact.kind == HumanEquationCoreArtifactKind::EquationTheorem)
                .count(),
            lowered.equation_theorems.theorem_specs.len()
        );
        verify_lowered_bundle(
            "\
inductive Bit : Type where
| off : Bit
| on : Bit",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_core_hash_ignores_binder_renaming_and_spans() {
        let left_source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k";
        let right_source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat

def pred (value : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ predecessor => predecessor";
        let (left_resolved, left_matrix, left_decision) =
            decision_tree_lowering_inputs(left_source, HumanEquationBudget::default());
        let (right_resolved, right_matrix, right_decision) =
            decision_tree_lowering_inputs(right_source, HumanEquationBudget::default());

        let mut row_values = BTreeMap::new();
        row_values.insert(0, nat_zero());
        row_values.insert(1, Expr::bvar(1));
        let left_profile = HumanEquationLoweringProfile {
            public_name: "pred".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("n", nat())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Nat.rec",
                nat(),
                vec![
                    constructor_lowering(constructor_key(&left_matrix, "Nat.zero"), Vec::new()),
                    constructor_lowering(
                        constructor_key(&left_matrix, "Nat.succ"),
                        vec![lowering_binder("k", nat()), lowering_binder("k_ih", nat())],
                    ),
                ],
            )],
            row_values: row_values.clone(),
            row_transports: BTreeMap::new(),
        };
        let right_profile = HumanEquationLoweringProfile {
            public_name: "pred".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("value", nat())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Nat.rec",
                nat(),
                vec![
                    constructor_lowering(constructor_key(&right_matrix, "Nat.zero"), Vec::new()),
                    constructor_lowering(
                        constructor_key(&right_matrix, "Nat.succ"),
                        vec![
                            lowering_binder("predecessor", nat()),
                            lowering_binder("predecessor_ih", nat()),
                        ],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let left = lower_human_equation_decision_tree_to_core(
            &left_resolved.resolved_equations[0],
            &left_matrix,
            &left_decision,
            left_profile,
            HumanEquationBudget::default(),
        )
        .expect("left pred should lower");
        let right = lower_human_equation_decision_tree_to_core(
            &right_resolved.resolved_equations[0],
            &right_matrix,
            &right_decision,
            right_profile,
            HumanEquationBudget::default(),
        )
        .expect("right pred should lower");

        assert_eq!(left.bundle.identity_hash, right.bundle.identity_hash);
        assert_eq!(
            left.bundle.artifacts[0].core_hash,
            right.bundle.artifacts[0].core_hash
        );
        assert_eq!(left.sidecar_metrics, right.sidecar_metrics);
        assert_eq!(left.budget_usage, right.budget_usage);
        assert_eq!(
            left.sidecar_metrics.pattern_matrix_cells,
            left.budget_usage.pattern_matrix_cells
        );
        assert_eq!(
            left.sidecar_metrics.expanded_branches,
            left.budget_usage.expanded_branches
        );
        assert_eq!(
            left.sidecar_metrics.generated_certificate_bytes,
            left.budget_usage.generated_certificate_bytes
        );
    }

    #[test]
    fn lowering_rejects_missing_recursor_profile() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let profile = HumanEquationLoweringProfile {
            public_name: "pred".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("n", nat())],
            result_type: nat(),
            result_universe: type0(),
            recursors: Vec::new(),
            row_values: BTreeMap::new(),
            row_transports: BTreeMap::new(),
        };

        let err = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect_err("missing recursor profile should reject lowering");
        assert!(matches!(
            err,
            HumanEquationLoweringError::MissingRecursor { .. }
        ));
    }

    #[test]
    fn dependent_coverage_eliminates_proved_impossible_indexed_branch() {
        let result = coverage_with_options(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Fin : forall (n : Nat), Type where
| zero : forall (n : Nat), Fin (Nat.succ n)
| succ : forall (n : Nat), forall (i : Fin n), Fin (Nat.succ n)
def impossible_fin (i : Fin Nat.zero) : Nat where
| Fin.zero n => Nat.zero
| default => Nat.zero",
            HumanEquationCoverageOptions {
                impossible_rows: Vec::new(),
                proved_impossible_rows: vec![HumanEquationImpossibleBranchFact {
                    row_index: 0,
                    reason: "Fin.zero constructor index Nat.succ n does not unify with Nat.zero"
                        .to_owned(),
                }],
            },
        );

        assert!(result.exhaustive);
        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
        assert_eq!(
            result.row_statuses[0].kind,
            HumanEquationCoverageRowStatusKind::Impossible
        );
    }

    #[test]
    fn lowering_dependent_indexed_head_uses_synthesized_motive() {
        let budget = HumanEquationBudget::default();
        let (equation, matrix, decision) = manual_dvec_lowering_inputs("dhead", budget);
        let nil_key = constructor_key(&matrix, "DVec.nil");
        let cons_key = constructor_key(&matrix, "DVec.cons");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, nat_zero());
        row_values.insert(1, Expr::bvar(2));
        let profile = HumanEquationLoweringProfile {
            public_name: "dhead".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", dvec(Expr::bvar(0))),
            ],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![indexed_recursor_lowering(
                "DVec.rec",
                vec![lowering_binder("idx", nat())],
                vec![Expr::bvar(1)],
                dvec(Expr::bvar(0)),
                nat(),
                vec![
                    indexed_constructor_lowering(nil_key, Vec::new(), vec![nat_zero()]),
                    indexed_constructor_lowering(
                        cons_key,
                        vec![
                            lowering_binder("k", nat()),
                            lowering_binder("x", nat()),
                            lowering_binder("rest", dvec(Expr::bvar(1))),
                            lowering_binder("rest_ih", nat()),
                        ],
                        vec![Expr::bvar(3)],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let lowered = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect("dependent indexed head should lower");

        assert_eq!(lowered.sidecar_metrics.eq_rec_transports, 0);
        verify_lowered_bundle(
            "\
inductive DVec : forall (n : Nat), Type where
| nil : DVec Nat.zero
| cons : forall (n : Nat), Nat -> DVec n -> DVec n",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_dependent_indexed_tail_uses_index_refining_motive() {
        let budget = HumanEquationBudget::default();
        let (equation, matrix, decision) = manual_dvec_lowering_inputs("dtail", budget);
        let nil_key = constructor_key(&matrix, "DVec.nil");
        let cons_key = constructor_key(&matrix, "DVec.cons");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::konst("DVec.nil", vec![]));
        row_values.insert(1, Expr::bvar(1));
        let profile = HumanEquationLoweringProfile {
            public_name: "dtail".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", dvec(Expr::bvar(0))),
            ],
            result_type: dvec(Expr::bvar(1)),
            result_universe: type0(),
            recursors: vec![indexed_recursor_lowering(
                "DVec.rec",
                vec![lowering_binder("idx", nat())],
                vec![Expr::bvar(1)],
                dvec(Expr::bvar(0)),
                dvec(Expr::bvar(1)),
                vec![
                    indexed_constructor_lowering(nil_key, Vec::new(), vec![nat_zero()]),
                    indexed_constructor_lowering(
                        cons_key,
                        vec![
                            lowering_binder("k", nat()),
                            lowering_binder("x", nat()),
                            lowering_binder("rest", dvec(Expr::bvar(1))),
                            lowering_binder("rest_ih", dvec(Expr::bvar(2))),
                        ],
                        vec![Expr::bvar(3)],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let lowered = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect("dependent indexed tail should lower");

        assert_eq!(lowered.sidecar_metrics.eq_rec_transports, 0);
        verify_lowered_bundle(
            "\
inductive DVec : forall (n : Nat), Type where
| nil : DVec Nat.zero
| cons : forall (n : Nat), Nat -> DVec n -> DVec n",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_eq_rec_transport_is_checked_and_budgeted() {
        let budget = HumanEquationBudget::default();
        let (equation, matrix, decision) = manual_unit_lowering_inputs(budget);
        let unit_key = constructor_key(&matrix, "Unit.mk");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::bvar(1));
        let mut row_transports = BTreeMap::new();
        row_transports.insert(
            0,
            vec![eq_rec_vec_transport(
                Expr::bvar(2),
                Expr::bvar(2),
                eq_refl(type0(), nat(), Expr::bvar(2)),
                "transport Vec n through a reflexive branch-local index equality",
            )],
        );
        let profile = HumanEquationLoweringProfile {
            public_name: "cast_vec_on_unit".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", vec_ty(Expr::bvar(0))),
                lowering_binder("u", unit_ty()),
            ],
            result_type: vec_ty(Expr::bvar(2)),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Unit.rec",
                unit_ty(),
                vec![constructor_lowering(unit_key, Vec::new())],
            )],
            row_values,
            row_transports,
        };

        let lowered = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect("Eq.rec transport should lower through Unit.rec");

        assert_eq!(lowered.sidecar_metrics.eq_rec_transports, 1);
        assert_eq!(lowered.budget_usage.eq_rec_transports, 1);
        assert!(expression_contains_applied_const(
            public_definition_value(&lowered.bundle, "cast_vec_on_unit"),
            "Eq.rec",
            6
        ));
        verify_lowered_bundle(
            "\
inductive Vec : forall (n : Nat), Type where
| nil : Vec Nat.zero
| cons : forall (n : Nat), Nat -> Vec n -> Vec n
inductive Unit : Type where
| mk : Unit",
            &lowered.bundle,
        );
    }

    #[test]
    fn lowering_eq_rec_transport_budget_overflow_is_structured() {
        let budget = HumanEquationBudget::default().with_max_generated_eq_rec_transports(0);
        let (equation, matrix, decision) = manual_unit_lowering_inputs(budget);
        let unit_key = constructor_key(&matrix, "Unit.mk");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::bvar(1));
        let mut row_transports = BTreeMap::new();
        row_transports.insert(
            0,
            vec![eq_rec_vec_transport(
                Expr::bvar(2),
                Expr::bvar(2),
                eq_refl(type0(), nat(), Expr::bvar(2)),
                "transport budget overflow fixture",
            )],
        );
        let profile = HumanEquationLoweringProfile {
            public_name: "cast_vec_on_unit".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", vec_ty(Expr::bvar(0))),
                lowering_binder("u", unit_ty()),
            ],
            result_type: vec_ty(Expr::bvar(2)),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Unit.rec",
                unit_ty(),
                vec![constructor_lowering(unit_key, Vec::new())],
            )],
            row_values,
            row_transports,
        };

        let err = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect_err("transport overflow should reject before returning artifacts");
        let HumanEquationLoweringError::GeneratedTermBudgetExceeded(err) = err else {
            panic!("expected generated-term budget error");
        };
        assert_eq!(
            err.exceeded,
            vec![HumanEquationBudgetField::EqRecTransports]
        );
        assert_eq!(err.requested_usage.eq_rec_transports, 1);
    }

    #[test]
    fn lowering_rejects_nonstandard_eq_rec_transport() {
        let budget = HumanEquationBudget::default();
        let (equation, matrix, decision) = manual_unit_lowering_inputs(budget);
        let unit_key = constructor_key(&matrix, "Unit.mk");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::bvar(1));
        let mut transport = eq_rec_vec_transport(
            Expr::bvar(2),
            Expr::bvar(2),
            eq_refl(type0(), nat(), Expr::bvar(2)),
            "nonstandard transport fixture",
        );
        transport.eq_rec_name = "Custom.Eq.rec".to_owned();
        let mut row_transports = BTreeMap::new();
        row_transports.insert(0, vec![transport]);
        let profile = HumanEquationLoweringProfile {
            public_name: "cast_vec_on_unit".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", vec_ty(Expr::bvar(0))),
                lowering_binder("u", unit_ty()),
            ],
            result_type: vec_ty(Expr::bvar(2)),
            result_universe: type0(),
            recursors: vec![recursor_lowering(
                "Unit.rec",
                unit_ty(),
                vec![constructor_lowering(unit_key, Vec::new())],
            )],
            row_values,
            row_transports,
        };

        let err = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect_err("custom Eq.rec transport should reject structurally");
        assert!(matches!(
            err,
            HumanEquationLoweringError::UnsupportedEqRecTransport { .. }
        ));
    }

    #[test]
    fn lowering_rejects_dependent_motive_synthesis_failure() {
        let budget = HumanEquationBudget::default();
        let (equation, matrix, decision) = manual_dvec_lowering_inputs("bad_dtail", budget);
        let nil_key = constructor_key(&matrix, "DVec.nil");
        let cons_key = constructor_key(&matrix, "DVec.cons");
        let mut row_values = BTreeMap::new();
        row_values.insert(0, Expr::konst("DVec.nil", vec![]));
        row_values.insert(1, Expr::bvar(1));
        let profile = HumanEquationLoweringProfile {
            public_name: "bad_dtail".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![
                lowering_binder("n", nat()),
                lowering_binder("xs", dvec(Expr::bvar(0))),
            ],
            result_type: dvec(Expr::bvar(1)),
            result_universe: type0(),
            recursors: vec![indexed_recursor_lowering(
                "DVec.rec",
                vec![lowering_binder("idx", nat())],
                Vec::new(),
                dvec(Expr::bvar(0)),
                dvec(Expr::bvar(1)),
                vec![
                    indexed_constructor_lowering(nil_key, Vec::new(), vec![nat_zero()]),
                    indexed_constructor_lowering(
                        cons_key,
                        vec![
                            lowering_binder("k", nat()),
                            lowering_binder("x", nat()),
                            lowering_binder("rest", dvec(Expr::bvar(1))),
                            lowering_binder("rest_ih", dvec(Expr::bvar(2))),
                        ],
                        vec![Expr::bvar(3)],
                    ),
                ],
            )],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let err = lower_human_equation_decision_tree_to_core(
            &equation, &matrix, &decision, profile, budget,
        )
        .expect_err("missing major index argument should reject motive synthesis");
        assert!(matches!(
            err,
            HumanEquationLoweringError::DependentMotiveSynthesisFailed { .. }
        ));
    }

    #[test]
    fn lowering_rejects_ambiguous_constructor_recursor_profile() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k";
        let (resolved, matrix, decision) =
            decision_tree_lowering_inputs(source, HumanEquationBudget::default());
        let zero_key = constructor_key(&matrix, "Nat.zero");
        let succ_key = constructor_key(&matrix, "Nat.succ");
        let constructors = vec![
            constructor_lowering(zero_key, Vec::new()),
            constructor_lowering(
                succ_key,
                vec![lowering_binder("k", nat()), lowering_binder("k_ih", nat())],
            ),
        ];
        let mut row_values = BTreeMap::new();
        row_values.insert(0, nat_zero());
        row_values.insert(1, Expr::bvar(1));
        let profile = HumanEquationLoweringProfile {
            public_name: "pred".to_owned(),
            universe_params: Vec::new(),
            public_binders: vec![lowering_binder("n", nat())],
            result_type: nat(),
            result_universe: type0(),
            recursors: vec![
                recursor_lowering("Nat.rec", nat(), constructors.clone()),
                recursor_lowering("OtherNat.rec", nat(), constructors),
            ],
            row_values,
            row_transports: BTreeMap::new(),
        };

        let err = lower_human_equation_decision_tree_to_core(
            &resolved.resolved_equations[0],
            &matrix,
            &decision,
            profile,
            HumanEquationBudget::default(),
        )
        .expect_err("ambiguous recursor profiles should reject lowering");
        assert!(matches!(
            err,
            HumanEquationLoweringError::AmbiguousConstructor { .. }
        ));
    }

    #[test]
    fn negative_lowering_fixtures_are_deterministic_and_artifact_free() {
        let missing_recursor = || {
            let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k";
            let (resolved, matrix, decision) =
                decision_tree_lowering_inputs(source, HumanEquationBudget::default());
            let profile = HumanEquationLoweringProfile {
                public_name: "pred".to_owned(),
                universe_params: Vec::new(),
                public_binders: vec![lowering_binder("n", nat())],
                result_type: nat(),
                result_universe: type0(),
                recursors: Vec::new(),
                row_values: BTreeMap::new(),
                row_transports: BTreeMap::new(),
            };
            lower_human_equation_decision_tree_to_core(
                &resolved.resolved_equations[0],
                &matrix,
                &decision,
                profile,
                HumanEquationBudget::default(),
            )
            .expect_err("missing recursor profile should reject before artifacts")
        };

        let motive_failure = || {
            let budget = HumanEquationBudget::default();
            let (equation, matrix, decision) = manual_dvec_lowering_inputs("bad_dtail", budget);
            let nil_key = constructor_key(&matrix, "DVec.nil");
            let cons_key = constructor_key(&matrix, "DVec.cons");
            let mut row_values = BTreeMap::new();
            row_values.insert(0, Expr::konst("DVec.nil", vec![]));
            row_values.insert(1, Expr::bvar(1));
            let profile = HumanEquationLoweringProfile {
                public_name: "bad_dtail".to_owned(),
                universe_params: Vec::new(),
                public_binders: vec![
                    lowering_binder("n", nat()),
                    lowering_binder("xs", dvec(Expr::bvar(0))),
                ],
                result_type: dvec(Expr::bvar(1)),
                result_universe: type0(),
                recursors: vec![indexed_recursor_lowering(
                    "DVec.rec",
                    vec![lowering_binder("idx", nat())],
                    Vec::new(),
                    dvec(Expr::bvar(0)),
                    dvec(Expr::bvar(1)),
                    vec![
                        indexed_constructor_lowering(nil_key, Vec::new(), vec![nat_zero()]),
                        indexed_constructor_lowering(
                            cons_key,
                            vec![
                                lowering_binder("k", nat()),
                                lowering_binder("x", nat()),
                                lowering_binder("rest", dvec(Expr::bvar(1))),
                                lowering_binder("rest_ih", dvec(Expr::bvar(2))),
                            ],
                            vec![Expr::bvar(3)],
                        ),
                    ],
                )],
                row_values,
                row_transports: BTreeMap::new(),
            };
            lower_human_equation_decision_tree_to_core(
                &equation, &matrix, &decision, profile, budget,
            )
            .expect_err("motive synthesis failure should reject before artifacts")
        };

        let nested_lowering_failure = || {
            let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def nested (t : Tree) : Nat where
| Tree.leaf n => n
| Tree.node (Tree.leaf n) right => n
| Tree.node (Tree.node left right) other => Nat.zero";
            let (resolved, matrix, decision) =
                decision_tree_lowering_inputs(source, HumanEquationBudget::default());
            let leaf_key = constructor_key(&matrix, "Tree.leaf");
            let node_key = constructor_key(&matrix, "Tree.node");
            let tree_ty = Expr::konst("Tree", vec![]);
            let mut row_values = BTreeMap::new();
            row_values.insert(0, Expr::bvar(0));
            let profile = HumanEquationLoweringProfile {
                public_name: "nested".to_owned(),
                universe_params: Vec::new(),
                public_binders: vec![lowering_binder("t", tree_ty.clone())],
                result_type: nat(),
                result_universe: type0(),
                recursors: vec![recursor_lowering(
                    "Tree.rec",
                    tree_ty,
                    vec![
                        constructor_lowering(leaf_key, vec![lowering_binder("n", nat())]),
                        constructor_lowering(
                            node_key,
                            vec![
                                lowering_binder("left", Expr::konst("Tree", vec![])),
                                lowering_binder("right", Expr::konst("Tree", vec![])),
                            ],
                        ),
                    ],
                )],
                row_values,
                row_transports: BTreeMap::new(),
            };
            lower_human_equation_decision_tree_to_core(
                &resolved.resolved_equations[0],
                &matrix,
                &decision,
                profile,
                HumanEquationBudget::default(),
            )
            .expect_err("nested decision-column lowering should reject before artifacts")
        };

        let nonstandard_transport = || {
            let budget = HumanEquationBudget::default();
            let (equation, matrix, decision) = manual_unit_lowering_inputs(budget);
            let unit_key = constructor_key(&matrix, "Unit.mk");
            let mut row_values = BTreeMap::new();
            row_values.insert(0, Expr::bvar(1));
            let mut transport = eq_rec_vec_transport(
                Expr::bvar(2),
                Expr::bvar(2),
                eq_refl(type0(), nat(), Expr::bvar(2)),
                "nonstandard transport fixture",
            );
            transport.eq_rec_name = "Custom.Eq.rec".to_owned();
            let mut row_transports = BTreeMap::new();
            row_transports.insert(0, vec![transport]);
            let profile = HumanEquationLoweringProfile {
                public_name: "cast_vec_on_unit".to_owned(),
                universe_params: Vec::new(),
                public_binders: vec![
                    lowering_binder("n", nat()),
                    lowering_binder("xs", vec_ty(Expr::bvar(0))),
                    lowering_binder("u", unit_ty()),
                ],
                result_type: vec_ty(Expr::bvar(2)),
                result_universe: type0(),
                recursors: vec![recursor_lowering(
                    "Unit.rec",
                    unit_ty(),
                    vec![constructor_lowering(unit_key, Vec::new())],
                )],
                row_values,
                row_transports,
            };
            lower_human_equation_decision_tree_to_core(
                &equation, &matrix, &decision, profile, budget,
            )
            .expect_err("nonstandard Eq.rec transport should reject before artifacts")
        };

        type LoweringErrorPredicate = fn(&HumanEquationLoweringError) -> bool;

        struct LoweringErrorCase {
            err: HumanEquationLoweringError,
            matches_expected: LoweringErrorPredicate,
        }

        let cases = vec![
            LoweringErrorCase {
                err: missing_recursor(),
                matches_expected: |err: &HumanEquationLoweringError| {
                    matches!(err, HumanEquationLoweringError::MissingRecursor { .. })
                },
            },
            LoweringErrorCase {
                err: motive_failure(),
                matches_expected: |err: &HumanEquationLoweringError| {
                    matches!(
                        err,
                        HumanEquationLoweringError::DependentMotiveSynthesisFailed { .. }
                    )
                },
            },
            LoweringErrorCase {
                err: nested_lowering_failure(),
                matches_expected: |err: &HumanEquationLoweringError| {
                    matches!(
                        err,
                        HumanEquationLoweringError::UnsupportedNestedOrMutualLowering { .. }
                    )
                },
            },
            LoweringErrorCase {
                err: nonstandard_transport(),
                matches_expected: |err: &HumanEquationLoweringError| {
                    matches!(
                        err,
                        HumanEquationLoweringError::UnsupportedEqRecTransport { .. }
                    )
                },
            },
        ];
        let repeated = [
            missing_recursor(),
            motive_failure(),
            nested_lowering_failure(),
            nonstandard_transport(),
        ];

        for (case, repeated_err) in cases.into_iter().zip(repeated) {
            assert!((case.matches_expected)(&case.err));
            assert_eq!(case.err, repeated_err);
        }
    }

    #[test]
    fn recursion_accepts_list_tail_call_with_explicit_evidence() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def length (xs : List) : Nat where
| List.nil => Nat.zero
| List.cons x rest => length rest",
        );

        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
        assert_eq!(result.graph.calls.len(), 1);
        let evidence = result.graph.calls[0]
            .decrease_evidence
            .as_ref()
            .expect("tail call should carry decrease evidence");
        assert_eq!(evidence.decreasing_parameter, 0);
        assert_eq!(evidence.constructor_field_path.root_parameter, 0);
        assert!(evidence
            .constructor_field_path
            .identity
            .contains("List.cons"));
        assert_eq!(
            evidence.constructor_field_path.segments[0].argument_index,
            1
        );
    }

    #[test]
    fn recursion_accepts_tree_child_calls_with_visible_field_paths() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive Tree : Type where
| leaf : Nat -> Tree
| node : Tree -> Tree -> Tree
def choose (a : Nat) (b : Nat) : Nat := a
def size (t : Tree) : Nat where
| Tree.leaf n => Nat.succ Nat.zero
| Tree.node left right => choose (size left) (size right)",
        );

        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
        assert_eq!(result.graph.calls.len(), 2);
        let paths = result
            .graph
            .calls
            .iter()
            .map(|call| {
                let evidence = call
                    .decrease_evidence
                    .as_ref()
                    .expect("tree child call should carry decrease evidence");
                (
                    evidence.constructor_field_path.identity.clone(),
                    evidence.constructor_field_path.segments[0].argument_index,
                )
            })
            .collect::<Vec<_>>();
        assert!(paths
            .iter()
            .any(|(identity, index)| identity.contains("Tree.node") && *index == 0));
        assert!(paths
            .iter()
            .any(|(identity, index)| identity.contains("Tree.node") && *index == 1));
    }

    #[test]
    fn recursion_measure_generates_obligation_and_accepts_checked_nat_decrease_proof() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def loop_down (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => loop_down n
termination_by n";
        let (mut resolved, matrix) = recursion_inputs(source);
        let missing = check_human_equation_recursion(&resolved.resolved_equations[0], &matrix);

        assert!(!missing.accepted);
        assert_eq!(missing.graph.measure_obligations.len(), 1);
        assert_eq!(
            recursion_diagnostic_kinds(&missing),
            vec![HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing]
        );
        let obligation = missing.graph.measure_obligations[0].clone();
        assert!(obligation.proof.is_none());
        assert_eq!(obligation.caller, "loop_down");
        assert_eq!(obligation.callee, "loop_down");
        assert_eq!(obligation.row_index, 1);
        assert_eq!(
            obligation.call_identity,
            "app(global:local:00000001:loop_down,local:1)"
        );
        assert_eq!(obligation.measure_identity, "local:0");
        assert_eq!(obligation.caller_measure_identity, "local:0");
        assert_eq!(obligation.callee_measure_identity, "local:1");
        assert!(obligation.relation_identity.starts_with("Nat.lt("));

        resolved.resolved_equations[0]
            .termination
            .as_mut()
            .expect("measure annotation should resolve")
            .checked_decrease_proofs
            .insert(
                obligation.identity,
                HumanResolvedMeasureDecreaseProof {
                    proof_identity: "checked:loop_down.measure_decrease".to_owned(),
                    span: Span::empty(FileId(7)),
                },
            );

        let accepted = check_human_equation_recursion(&resolved.resolved_equations[0], &matrix);
        assert!(accepted.accepted);
        assert!(accepted.diagnostics.is_empty());
        assert_eq!(accepted.graph.measure_obligations.len(), 1);
        assert!(accepted.graph.measure_obligations[0].proof.is_some());
        assert_eq!(accepted.graph.measure_lowering_plans.len(), 1);
        assert_eq!(
            accepted.graph.measure_lowering_plans[0].strategy,
            HumanEquationMeasureLoweringStrategy::FuelStyleEncoding
        );
        assert_eq!(
            accepted.graph.measure_lowering_plans[0].definition_name,
            "loop_down"
        );
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        let coverage = check_human_equation_coverage(&matrix, &families);
        construct_human_equation_decision_tree(
            &resolved.resolved_equations[0],
            &matrix,
            &coverage,
            &accepted,
            HumanEquationBudget::default(),
        )
        .expect("approved measure recursion should continue to decision-tree lowering plan");
    }

    #[test]
    fn recursion_measure_lowering_plans_are_owned_by_definition() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def loop_a (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => loop_a n
termination_by n
def loop_b (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => loop_b n
termination_by n";
        let mut resolved = resolve_source(source);
        let constructor_order = human_equation_constructor_order_from_resolved_module(&resolved);
        let matrices = resolved
            .resolved_equations
            .iter()
            .map(|equation| {
                normalize_human_equation_pattern_matrix_with_constructor_order(
                    equation,
                    &constructor_order,
                    HumanEquationBudget::default(),
                )
                .expect("matrix should normalize")
            })
            .collect::<Vec<_>>();

        let missing = check_human_equation_recursion_block(&resolved.resolved_equations, &matrices);
        assert!(!missing.accepted);
        assert_eq!(missing.graph.measure_obligations.len(), 2);
        for call in &missing.graph.calls {
            let obligation = call
                .measure_decrease
                .as_ref()
                .expect("Nat measure should generate an obligation");
            let equation = resolved
                .resolved_equations
                .iter_mut()
                .find(|equation| equation.source_name.as_dotted() == call.caller)
                .expect("call caller should resolve to an equation");
            equation
                .termination
                .as_mut()
                .expect("measure annotation should resolve")
                .checked_decrease_proofs
                .insert(
                    obligation.identity.clone(),
                    HumanResolvedMeasureDecreaseProof {
                        proof_identity: format!("checked:{}.measure_decrease", call.caller),
                        span: Span::empty(FileId(7)),
                    },
                );
        }

        let accepted =
            check_human_equation_recursion_block(&resolved.resolved_equations, &matrices);
        assert!(accepted.accepted);
        assert_eq!(accepted.graph.measure_lowering_plans.len(), 2);
        let plans = accepted
            .graph
            .measure_lowering_plans
            .iter()
            .map(|plan| {
                (
                    plan.definition_name.as_str(),
                    plan.obligation_identities.len(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(plans, vec![("loop_a", 1), ("loop_b", 1)]);
    }

    #[test]
    fn recursion_measure_requires_checked_decrease_proof_before_decision_tree() {
        let source = "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def loop_down (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => loop_down n
termination_by n";
        let (resolved, matrix) = recursion_inputs(source);
        let families = human_equation_constructor_family_table_from_resolved_module(&resolved);
        let coverage = check_human_equation_coverage(&matrix, &families);
        let recursion = check_human_equation_recursion(&resolved.resolved_equations[0], &matrix);

        assert!(coverage.accepted);
        assert!(!recursion.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&recursion),
            vec![HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing]
        );
    }

    #[test]
    fn negative_recursion_fixtures_are_structured_and_deterministic() {
        let same_argument = || {
            recursion(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => bad n",
            )
        };
        let hidden = || {
            recursion(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
axiom consume : (List -> Nat) -> Nat
def bad (xs : List) : Nat where
| List.nil => Nat.zero
| List.cons x rest => consume bad",
            )
        };
        let opaque_alias = || {
            recursion(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def alias (xs : List) : List := xs
def bad (xs : List) : List where
| List.nil => List.nil
| List.cons x rest => bad (alias rest)",
            )
        };
        let non_nat_measure = || {
            recursion(
                "\
inductive Bool : Type where
| false : Bool
| true : Bool
def stuck (b : Bool) : Bool where
| Bool.false => Bool.false
| Bool.true => stuck b
termination_by b",
            )
        };
        let missing_measure_proof = || {
            recursion(
                "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def loop_down (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => loop_down n
termination_by n",
            )
        };

        let cases = [
            (
                recursion_failure_snapshot(&same_argument()),
                vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing],
            ),
            (
                recursion_failure_snapshot(&hidden()),
                vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing],
            ),
            (
                recursion_failure_snapshot(&opaque_alias()),
                vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing],
            ),
            (
                recursion_failure_snapshot(&non_nat_measure()),
                vec![HumanEquationRecursionDiagnosticKind::TerminationMeasureNotNat],
            ),
            (
                recursion_failure_snapshot(&missing_measure_proof()),
                vec![HumanEquationRecursionDiagnosticKind::MeasureDecreaseProofMissing],
            ),
        ];
        let repeated = [
            recursion_failure_snapshot(&same_argument()),
            recursion_failure_snapshot(&hidden()),
            recursion_failure_snapshot(&opaque_alias()),
            recursion_failure_snapshot(&non_nat_measure()),
            recursion_failure_snapshot(&missing_measure_proof()),
        ];

        for ((snapshot, expected_kinds), repeated_snapshot) in cases.into_iter().zip(repeated) {
            assert_eq!(snapshot, repeated_snapshot);
            assert!(!snapshot.accepted);
            assert_eq!(
                snapshot
                    .diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.kind)
                    .collect::<Vec<_>>(),
                expected_kinds
            );
        }

        let mutual_cycle = || {
            recursion_block_for_manual_equations(vec![
                manual_nat_succ_equation(
                    "Current.Module.even",
                    0,
                    "Current.Module.odd",
                    1,
                    "local:1",
                ),
                manual_nat_succ_equation(
                    "Current.Module.odd",
                    1,
                    "Current.Module.even",
                    0,
                    "local:1",
                ),
            ])
        };
        let left = mutual_cycle();
        let right = mutual_cycle();
        assert_eq!(left, right);
        assert!(!left.accepted);
        assert_eq!(left.graph.nondecreasing_cycles.len(), 1);
        assert!(left.diagnostics.iter().any(|diagnostic| diagnostic.kind
            == HumanEquationRecursionDiagnosticKind::MutualCycleWithoutDecrease));
    }

    #[test]
    fn recursion_measure_rejects_non_nat_measure() {
        let result = recursion(
            "\
inductive Bool : Type where
| false : Bool
| true : Bool
def stuck (b : Bool) : Bool where
| Bool.false => Bool.false
| Bool.true => stuck b
termination_by b",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::TerminationMeasureNotNat]
        );
        assert_eq!(
            result.diagnostics[0].human_kind(),
            crate::HumanDiagnosticKind::TerminationMeasureNotNat
        );
    }

    #[test]
    fn recursion_rejects_same_argument_call() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => bad n",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0].decrease_evidence.is_none());
        assert_eq!(
            result.diagnostics[0].human_kind(),
            crate::HumanDiagnosticKind::RecursiveCallNotDecreasing
        );
    }

    #[test]
    fn recursion_rejects_constructor_growth_call() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => bad (Nat.succ k)",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0]
            .argument_mapping
            .iter()
            .any(|argument| argument.contains("Nat.succ")));
    }

    #[test]
    fn recursion_rejects_call_through_append_wrapper() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
axiom append : List -> List -> List
def bad (xs : List) (ys : List) : List where
| List.nil => ys
| List.cons x rest => bad (append rest ys) ys",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0]
            .argument_mapping
            .iter()
            .any(|argument| argument.contains("append")));
    }

    #[test]
    fn recursion_rejects_opaque_alias_call() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
def alias (xs : List) : List := xs
def bad (xs : List) : List where
| List.nil => List.nil
| List.cons x rest => bad (alias rest)",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0]
            .argument_mapping
            .iter()
            .any(|argument| argument.contains("alias")));
    }

    #[test]
    fn recursion_rejects_hidden_recursive_value() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
inductive List : Type where
| nil : List
| cons : Nat -> List -> List
axiom consume : (List -> Nat) -> Nat
def bad (xs : List) : Nat where
| List.nil => Nat.zero
| List.cons x rest => consume bad",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0].argument_mapping.is_empty());
    }

    #[test]
    fn recursion_rejects_recursive_call_hidden_in_notation_argument() {
        let result = recursion(
            "\
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
def choose (a : Nat) (b : Nat) : Nat := a
infixl:65 \" <+> \" => choose
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k <+> bad n",
        );

        assert!(!result.accepted);
        assert_eq!(
            recursion_diagnostic_kinds(&result),
            vec![HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing]
        );
        assert!(result.graph.calls[0]
            .call_identity
            .starts_with("app(global:"));
    }

    #[test]
    fn recursion_accepts_mutual_even_odd_decrease() {
        let result = recursion_block_for_manual_equations(vec![
            manual_nat_succ_equation("Current.Module.even", 0, "Current.Module.odd", 1, "local:0"),
            manual_nat_succ_equation("Current.Module.odd", 1, "Current.Module.even", 0, "local:0"),
        ]);

        assert!(result.accepted);
        assert!(result.diagnostics.is_empty());
        assert!(result.graph.nondecreasing_cycles.is_empty());
        assert_eq!(result.graph.calls.len(), 2);
        assert!(result
            .graph
            .calls
            .iter()
            .all(|call| call.decrease_evidence.is_some()));
    }

    #[test]
    fn recursion_rejects_mutual_cycle_without_decreasing_edge() {
        let result = recursion_block_for_manual_equations(vec![
            manual_nat_succ_equation("Current.Module.even", 0, "Current.Module.odd", 1, "local:1"),
            manual_nat_succ_equation("Current.Module.odd", 1, "Current.Module.even", 0, "local:1"),
        ]);

        assert!(!result.accepted);
        assert_eq!(result.graph.nondecreasing_cycles.len(), 1);
        let kinds = result
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.kind)
            .collect::<BTreeSet<_>>();
        assert!(kinds.contains(&HumanEquationRecursionDiagnosticKind::RecursiveCallNotDecreasing));
        assert!(kinds.contains(&HumanEquationRecursionDiagnosticKind::MutualCycleWithoutDecrease));
        assert_eq!(
            result.graph.nondecreasing_cycles[0].definitions,
            vec!["Current.Module.even", "Current.Module.odd"]
        );
    }
}

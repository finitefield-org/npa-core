//! Source-free metadata loading, scoring, and diagnostics for
//! `npa package refactor-plan`.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs, io,
    path::Path,
};

use npa_cert::Name;
use npa_package::{
    build_package_lock_graph, package_lock_reverse_dependencies, parse_package_lock_json,
    parse_package_theorem_index_json, PackageArtifactError, PackageArtifactOrigin,
    PackageGlobalRefView, PackageLockEntry, PackageLockEntryOrigin, PackageLockGraph,
    PackageLockManifest, PackagePath, PackageTheoremIndex, PackageTheoremIndexEntry,
    PackageTheoremIndexKind,
};

use crate::args::{PackageRefactorPlanOptions, PackageRefactorPlanScope};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::join_package_path;
use crate::package::{load_package_root, LoadedPackageRoot};
use crate::package_artifacts::{PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH};

const COMMAND: &str = "package refactor-plan";
const AXIOM_WEIGHT: f64 = 3.0;
const CERTIFICATE_SIZE_BUCKET_BYTES: u64 = 65_536;
const CERTIFICATE_SIZE_WEIGHT_CAP: u64 = 10;
const DEPENDENT_COMPLEXITY_WEIGHT: f64 = 2.0;
const DIRECT_IMPORT_WEIGHT: f64 = 2.0;
const FAMILY_CLUSTER_BONUS_CAP: f64 = 10.0;
const FAMILY_CLUSTER_BONUS_PER_CLUSTER: f64 = 2.0;
const FAMILY_CLUSTER_MIN_SIZE: usize = 3;
const HIGH_FANOUT_DIRECT_THRESHOLD: usize = 5;
const HIGH_FANOUT_TRANSITIVE_THRESHOLD: usize = 12;
const LARGE_MODULE_EXPORT_THRESHOLD: usize = 25;
const MIXED_PURPOSE_BONUS: f64 = 4.0;
const PUBLIC_EXPORT_WEIGHT: f64 = 1.0;
const THEOREM_FAMILY_AXIOM_WEIGHT: f64 = 4.0;
const THEOREM_FAMILY_PREFIX_LENGTH_CAP: usize = 12;
const THEOREM_FAMILY_THEOREM_WEIGHT: f64 = 2.0;
const THEOREM_WEIGHT: f64 = 1.0;
const VERIFICATION_CONTAINMENT_BONUS: f64 = 5.0;
const VERIFY_CHANGED_COMMAND: &str =
    "npa package verify-certs --root <root> --changed --checker reference --json";
const VERIFY_EXPORT_SUMMARY_COMMAND: &str =
    "npa package export-summary --root <root> --check --json";
const VERIFY_INDEX_COMMAND: &str = "npa package index --root <root> --check --json";

/// Stable schema label for refactor-plan diagnostics.
pub const REFACTOR_PLAN_REPORT_SCHEMA: &str = "npa.cli.package.refactor_plan.v0.1";

/// Loaded metadata and computed advisory report for `npa package refactor-plan`.
#[derive(Clone, Debug)]
pub struct LoadedRefactorPlanMetadata {
    /// Sanitized package root display string.
    pub root_display: String,
    /// Parsed and validated package-lock manifest.
    pub package_lock: PackageLockManifest,
    /// Validated package-lock graph.
    pub package_lock_graph: PackageLockGraph,
    /// Deterministic refactor-plan graph metrics.
    pub module_graph: RefactorPlanModuleGraph,
    /// Optional checked theorem index.
    pub theorem_index: Option<PackageTheoremIndex>,
    /// Aggregated theorem-index metrics when a checked theorem index is present.
    pub theorem_aggregation: Option<RefactorPlanTheoremIndexAggregation>,
    /// Computed report populated with sorted, scoped candidates.
    pub report: RefactorPlanReport,
}

/// Deterministic module graph view used by refactor-plan scoring.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefactorPlanModuleGraph {
    /// Package-lock topological module order, dependency before dependent.
    pub topological_order: Vec<Name>,
    /// Direct imports for every package-lock module.
    pub direct_imports: BTreeMap<Name, BTreeSet<Name>>,
    /// Direct reverse dependents for every package-lock module.
    pub reverse_direct: BTreeMap<Name, Vec<Name>>,
    /// Transitive reverse dependents with shortest graph distance.
    pub reverse_transitive: BTreeMap<Name, Vec<RefactorPlanReverseDependent>>,
}

/// One reverse dependent and its shortest distance from the dependency.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefactorPlanReverseDependent {
    /// Reverse dependent module.
    pub module: Name,
    /// Shortest reverse-dependency distance, where direct dependents are `1`.
    pub distance: usize,
}

/// Aggregated checked theorem-index metrics used by refactor-plan candidates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefactorPlanTheoremIndexAggregation {
    /// Per-local-module theorem metrics keyed by module.
    pub modules: BTreeMap<Name, RefactorPlanModuleTheoremAggregation>,
    /// Summary warning codes produced while aggregating the theorem index.
    pub warnings: Vec<String>,
}

/// Per-module theorem-index aggregate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefactorPlanModuleTheoremAggregation {
    /// Number of theorem exports.
    pub theorem_count: usize,
    /// Number of axiom exports.
    pub axiom_count: usize,
    /// Number of public theorem-index entries.
    pub public_export_count: usize,
    /// Theorem-family clusters in deterministic order.
    pub families: Vec<RefactorPlanTheoremFamilyAggregation>,
}

/// One theorem-family cluster derived from theorem-index names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefactorPlanTheoremFamilyAggregation {
    /// First underscore-delimited token used for the family.
    pub prefix: String,
    /// Stable family key, `<module>::<prefix>_*`.
    pub family: String,
    /// Sorted theorem or axiom declaration names in this family.
    pub theorem_names: Vec<String>,
    /// Number of theorem exports in this family.
    pub theorem_count: usize,
    /// Number of axiom exports in this family.
    pub axiom_count: usize,
    /// Shared prefix byte length.
    pub shared_prefix_length: usize,
    /// Distinct non-null statement head references by stable module/name key.
    pub statement_head_count: usize,
    /// Distinct statement constant references by stable module/name key.
    pub statement_constant_count: usize,
}

/// Internal report model for refactor-plan output.
#[derive(Clone, Debug, PartialEq)]
pub struct RefactorPlanReport {
    /// Stable report schema.
    pub schema: &'static str,
    /// Sanitized package root display string.
    pub root: String,
    /// Requested candidate scope.
    pub scope: PackageRefactorPlanScope,
    /// Whether a checked theorem index was loaded.
    pub theorem_index_status: TheoremIndexStatus,
    /// Summary warnings accumulated while loading metadata.
    pub warnings: Vec<String>,
    /// Candidate rows populated by later milestones.
    pub candidates: Vec<RefactorCandidate>,
    /// Refactor-plan output is advisory metadata, never proof evidence.
    pub proof_evidence: bool,
}

/// Checked theorem-index loading state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TheoremIndexStatus {
    /// `generated/theorem-index.json` was present and parsed canonically.
    Loaded,
    /// `generated/theorem-index.json` was absent and metrics remain nullable.
    Missing,
}

impl TheoremIndexStatus {
    /// Stable lower-case rendering.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Loaded => "loaded",
            Self::Missing => "missing",
        }
    }
}

/// Refactor candidate row.
#[derive(Clone, Debug, PartialEq)]
pub enum RefactorCandidate {
    /// Module-level refactor candidate.
    Module(ModuleRefactorCandidate),
    /// Theorem-family refactor candidate.
    TheoremFamily(TheoremFamilyRefactorCandidate),
}

/// Module-level refactor candidate.
#[derive(Clone, Debug, PartialEq)]
pub struct ModuleRefactorCandidate {
    /// Candidate module.
    pub module: Name,
    /// Raw candidate score.
    pub score: f64,
    /// Recommended refactor action.
    pub recommendation: RefactorRecommendation,
    /// Estimated refactor risk.
    pub risk: RefactorRisk,
    /// Module metrics used to explain scoring.
    pub metrics: ModuleRefactorMetrics,
    /// Stable evidence codes.
    pub evidence: Vec<String>,
    /// Suggested smallest refactor unit.
    pub suggested_unit: String,
    /// Suggested verification commands.
    pub suggested_verification: Vec<String>,
    /// Candidate rows are advisory metadata, never proof evidence.
    pub proof_evidence: bool,
}

/// Theorem-family refactor candidate.
#[derive(Clone, Debug, PartialEq)]
pub struct TheoremFamilyRefactorCandidate {
    /// Owning module.
    pub module: Name,
    /// Stable family key.
    pub family: String,
    /// Raw candidate score.
    pub score: f64,
    /// Recommended refactor action.
    pub recommendation: RefactorRecommendation,
    /// Estimated refactor risk.
    pub risk: RefactorRisk,
    /// Theorem or axiom names in the family.
    pub theorem_names: Vec<String>,
    /// Theorem-family metrics used to explain scoring.
    pub metrics: TheoremFamilyMetrics,
    /// Stable evidence codes.
    pub evidence: Vec<String>,
    /// Suggested smallest refactor unit.
    pub suggested_unit: String,
    /// Suggested verification commands.
    pub suggested_verification: Vec<String>,
    /// Candidate rows are advisory metadata, never proof evidence.
    pub proof_evidence: bool,
}

/// Module candidate metrics.
#[derive(Clone, Debug, PartialEq)]
pub struct ModuleRefactorMetrics {
    /// Local module complexity score.
    pub local_complexity: f64,
    /// Reverse-dependent weighted complexity.
    pub dependent_complexity: f64,
    /// Direct reverse dependent count.
    pub direct_dependents: usize,
    /// Transitive reverse dependent count.
    pub transitive_dependents: usize,
    /// Direct import count.
    pub direct_import_count: usize,
    /// Number of theorem exports when a theorem index is available.
    pub theorem_count: Option<usize>,
    /// Number of axiom exports when a theorem index is available.
    pub axiom_count: Option<usize>,
    /// Number of public exports when a theorem index is available.
    pub public_export_count: Option<usize>,
    /// Certificate file size from metadata only.
    pub certificate_size_bytes: Option<u64>,
    /// Integer-bucketed certificate size contribution.
    pub certificate_size_weight: f64,
    /// Number of theorem-family clusters.
    pub family_cluster_count: usize,
}

/// Theorem-family candidate metrics.
#[derive(Clone, Debug, PartialEq)]
pub struct TheoremFamilyMetrics {
    /// Number of theorem exports in the family.
    pub theorem_count: usize,
    /// Number of axiom exports in the family.
    pub axiom_count: usize,
    /// Shared prefix byte length.
    pub shared_prefix_length: usize,
    /// Distinct statement head count.
    pub statement_head_count: usize,
    /// Distinct statement constant count.
    pub statement_constant_count: usize,
    /// Owning module dependent complexity.
    pub module_dependent_complexity: f64,
}

/// Refactor action recommendation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RefactorRecommendation {
    /// Split a broad module into smaller modules.
    ModuleSplit,
    /// Extract a widely used foundation.
    ExtractFoundation,
    /// Group related theorem-family members.
    TheoremFamilyGroup,
    /// Prefer local cleanup without boundary movement.
    LocalCleanup,
    /// Reduce direct import pressure.
    DependencyHygiene,
    /// Stabilize a high-fanout boundary.
    StabilizeBoundary,
    /// No immediate action.
    NoAction,
}

impl RefactorRecommendation {
    /// Stable lower-case kebab-case rendering.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ModuleSplit => "module-split",
            Self::ExtractFoundation => "extract-foundation",
            Self::TheoremFamilyGroup => "theorem-family-group",
            Self::LocalCleanup => "local-cleanup",
            Self::DependencyHygiene => "dependency-hygiene",
            Self::StabilizeBoundary => "stabilize-boundary",
            Self::NoAction => "no-action",
        }
    }
}

/// Estimated refactor risk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RefactorRisk {
    /// Low refactor risk.
    Low,
    /// Medium refactor risk.
    Medium,
    /// High refactor risk.
    High,
}

impl RefactorRisk {
    /// Stable lower-case kebab-case rendering.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
        }
    }
}

/// Run `npa package refactor-plan` and render the advisory report as
/// diagnostics.
pub fn run_package_refactor_plan(options: PackageRefactorPlanOptions) -> CommandResult {
    let loaded = match load_refactor_plan_metadata(&options) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let LoadedRefactorPlanMetadata {
        root_display,
        report,
        ..
    } = loaded;
    let mut result = CommandResult::passed(COMMAND, root_display);
    result
        .diagnostics
        .push(refactor_plan_summary_diagnostic(&report));
    result.diagnostics.extend(
        report
            .candidates
            .iter()
            .map(refactor_plan_candidate_diagnostic),
    );
    result
}

fn refactor_plan_summary_diagnostic(report: &RefactorPlanReport) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, "refactor_plan_summary")
        .with_field("refactor_plan")
        .with_actual_value(refactor_plan_summary_actual_value(report))
}

fn refactor_plan_candidate_diagnostic(candidate: &RefactorCandidate) -> CommandDiagnostic {
    match candidate {
        RefactorCandidate::Module(candidate) => CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "refactor_plan_module_candidate",
        )
        .with_module(candidate.module.as_dotted())
        .with_field("refactor_plan")
        .with_actual_value(module_candidate_actual_value(candidate)),
        RefactorCandidate::TheoremFamily(candidate) => CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "refactor_plan_theorem_family_candidate",
        )
        .with_module(candidate.module.as_dotted())
        .with_field("refactor_plan")
        .with_actual_value(theorem_family_candidate_actual_value(candidate)),
    }
}

fn refactor_plan_summary_actual_value(report: &RefactorPlanReport) -> String {
    let module_candidate_count = report
        .candidates
        .iter()
        .filter(|candidate| matches!(candidate, RefactorCandidate::Module(_)))
        .count();
    let theorem_family_candidate_count = report.candidates.len() - module_candidate_count;
    format!(
        "schema={};scope={};theorem_index_status={};candidate_count={};module_candidate_count={};theorem_family_candidate_count={};warnings={};proof_evidence={}",
        report.schema,
        refactor_plan_scope_value(report.scope),
        report.theorem_index_status.as_str(),
        report.candidates.len(),
        module_candidate_count,
        theorem_family_candidate_count,
        csv_or_none(&report.warnings),
        bool_value(report.proof_evidence),
    )
}

fn module_candidate_actual_value(candidate: &ModuleRefactorCandidate) -> String {
    let metrics = &candidate.metrics;
    format!(
        "kind=module;module={};score={};recommendation={};risk={};local_complexity={};dependent_complexity={};direct_dependents={};transitive_dependents={};direct_import_count={};theorem_count={};axiom_count={};public_export_count={};certificate_size_bytes={};certificate_size_weight={};family_cluster_count={};evidence={};suggested_unit={};suggested_verification={};proof_evidence={}",
        diagnostic_scalar_value(&candidate.module.as_dotted()),
        f64_value(candidate.score),
        candidate.recommendation.as_str(),
        candidate.risk.as_str(),
        f64_value(metrics.local_complexity),
        f64_value(metrics.dependent_complexity),
        metrics.direct_dependents,
        metrics.transitive_dependents,
        metrics.direct_import_count,
        nullable_usize(metrics.theorem_count),
        nullable_usize(metrics.axiom_count),
        nullable_usize(metrics.public_export_count),
        nullable_u64(metrics.certificate_size_bytes),
        f64_value(metrics.certificate_size_weight),
        metrics.family_cluster_count,
        csv_or_none(&candidate.evidence),
        diagnostic_scalar_value(candidate.suggested_unit.as_str()),
        pipe_or_none(&candidate.suggested_verification),
        bool_value(candidate.proof_evidence),
    )
}

fn theorem_family_candidate_actual_value(candidate: &TheoremFamilyRefactorCandidate) -> String {
    let metrics = &candidate.metrics;
    format!(
        "kind=theorem-family;module={};family={};score={};recommendation={};risk={};theorem_count={};axiom_count={};shared_prefix_length={};statement_head_count={};statement_constant_count={};module_dependent_complexity={};evidence={};suggested_unit={};suggested_verification={};proof_evidence={}",
        diagnostic_scalar_value(&candidate.module.as_dotted()),
        diagnostic_scalar_value(candidate.family.as_str()),
        f64_value(candidate.score),
        candidate.recommendation.as_str(),
        candidate.risk.as_str(),
        metrics.theorem_count,
        metrics.axiom_count,
        metrics.shared_prefix_length,
        metrics.statement_head_count,
        metrics.statement_constant_count,
        f64_value(metrics.module_dependent_complexity),
        csv_or_none(&candidate.evidence),
        diagnostic_scalar_value(candidate.suggested_unit.as_str()),
        pipe_or_none(&candidate.suggested_verification),
        bool_value(candidate.proof_evidence),
    )
}

fn refactor_plan_scope_value(scope: PackageRefactorPlanScope) -> &'static str {
    match scope {
        PackageRefactorPlanScope::Modules => "modules",
        PackageRefactorPlanScope::Theorems => "theorems",
        PackageRefactorPlanScope::Both => "both",
    }
}

fn f64_value(value: f64) -> String {
    let value = if value == 0.0 { 0.0 } else { value };
    format!("{value:.1}")
}

fn nullable_usize(value: Option<usize>) -> String {
    value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "null".to_owned())
}

fn nullable_u64(value: Option<u64>) -> String {
    value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "null".to_owned())
}

fn csv_or_none(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_owned()
    } else {
        values
            .iter()
            .map(|value| diagnostic_scalar_value(value))
            .collect::<Vec<_>>()
            .join(",")
    }
}

fn pipe_or_none(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_owned()
    } else {
        values
            .iter()
            .map(|value| diagnostic_scalar_value(value))
            .collect::<Vec<_>>()
            .join("|")
    }
}

fn bool_value(value: bool) -> &'static str {
    if value {
        "true"
    } else {
        "false"
    }
}

fn diagnostic_scalar_value(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch == ';' || ch == '|' { '_' } else { ch })
        .collect()
}

/// Load source-free metadata for `npa package refactor-plan`.
pub fn load_refactor_plan_metadata(
    options: &PackageRefactorPlanOptions,
) -> Result<LoadedRefactorPlanMetadata, CommandResult> {
    let loaded = load_package_root(&options.common.root, COMMAND)?;
    let package_lock = read_package_lock(&loaded)?;
    let package_lock_graph = build_package_lock_graph(&package_lock).map_err(|error| {
        CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH)],
        )
    })?;
    validate_requested_module(&package_lock, options.module.as_ref(), &loaded.root_display)?;
    let module_graph =
        build_refactor_plan_module_graph_from_graph(&package_lock, &package_lock_graph).map_err(
            |diagnostic| {
                CommandResult::failed(COMMAND, loaded.root_display.clone(), vec![*diagnostic])
            },
        )?;
    let theorem_index = read_optional_theorem_index(&loaded)?;
    let theorem_index_status = if theorem_index.is_some() {
        TheoremIndexStatus::Loaded
    } else {
        TheoremIndexStatus::Missing
    };
    let theorem_aggregation = theorem_index
        .as_ref()
        .map(|index| aggregate_refactor_plan_theorem_index(&package_lock, index));
    let warnings = theorem_aggregation
        .as_ref()
        .map(|aggregation| aggregation.warnings.clone())
        .unwrap_or_default();
    let candidates = build_refactor_plan_candidates(
        &loaded.root,
        &package_lock,
        &module_graph,
        theorem_aggregation.as_ref(),
        options,
    );
    let report = RefactorPlanReport {
        schema: REFACTOR_PLAN_REPORT_SCHEMA,
        root: loaded.root_display.clone(),
        scope: options.scope,
        theorem_index_status,
        warnings,
        candidates,
        proof_evidence: false,
    };
    Ok(LoadedRefactorPlanMetadata {
        root_display: loaded.root_display,
        package_lock,
        package_lock_graph,
        module_graph,
        theorem_index,
        theorem_aggregation,
        report,
    })
}

/// Build the deterministic module graph view used by refactor-plan metrics.
pub fn build_refactor_plan_module_graph(
    lock: &PackageLockManifest,
) -> Result<RefactorPlanModuleGraph, Box<CommandDiagnostic>> {
    let graph = build_package_lock_graph(lock)
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    build_refactor_plan_module_graph_from_graph(lock, &graph)
}

fn build_refactor_plan_module_graph_from_graph(
    lock: &PackageLockManifest,
    graph: &PackageLockGraph,
) -> Result<RefactorPlanModuleGraph, Box<CommandDiagnostic>> {
    let direct_imports = direct_imports_by_module(lock);
    let mut reverse_direct = package_lock_reverse_dependencies(lock)
        .map_err(|error| Box::new(refactor_plan_lock_graph_diagnostic(error)))?;
    for module in &graph.topological_order {
        reverse_direct.entry(module.clone()).or_default();
    }
    let reverse_transitive =
        transitive_reverse_dependents(&graph.topological_order, &reverse_direct);
    Ok(RefactorPlanModuleGraph {
        topological_order: graph.topological_order.clone(),
        direct_imports,
        reverse_direct,
        reverse_transitive,
    })
}

fn direct_imports_by_module(lock: &PackageLockManifest) -> BTreeMap<Name, BTreeSet<Name>> {
    lock.entries
        .iter()
        .map(|entry| {
            (
                entry.module.clone(),
                entry
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            )
        })
        .collect()
}

fn transitive_reverse_dependents(
    topological_order: &[Name],
    reverse_direct: &BTreeMap<Name, Vec<Name>>,
) -> BTreeMap<Name, Vec<RefactorPlanReverseDependent>> {
    let mut closures = BTreeMap::new();
    for module in topological_order {
        let mut seen = BTreeSet::<Name>::new();
        let mut queue = VecDeque::<(Name, usize)>::new();
        let mut dependents = Vec::<RefactorPlanReverseDependent>::new();
        for dependent in reverse_direct.get(module).into_iter().flatten() {
            queue.push_back((dependent.clone(), 1));
        }
        while let Some((dependent, distance)) = queue.pop_front() {
            if !seen.insert(dependent.clone()) {
                continue;
            }
            dependents.push(RefactorPlanReverseDependent {
                module: dependent.clone(),
                distance,
            });
            for next in reverse_direct.get(&dependent).into_iter().flatten() {
                queue.push_back((next.clone(), distance + 1));
            }
        }
        closures.insert(module.clone(), dependents);
    }
    closures
}

/// Aggregate checked theorem-index entries for refactor-plan metrics.
pub fn aggregate_refactor_plan_theorem_index(
    lock: &PackageLockManifest,
    theorem_index: &PackageTheoremIndex,
) -> RefactorPlanTheoremIndexAggregation {
    let local_lock_modules = lock
        .entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let mut modules = local_lock_modules
        .iter()
        .map(|module| (module.clone(), ModuleTheoremAccumulator::default()))
        .collect::<BTreeMap<_, _>>();
    let mut warnings = BTreeSet::<String>::new();

    for entry in &theorem_index.entries {
        if entry.artifact.origin != PackageArtifactOrigin::Local {
            continue;
        }
        if !local_lock_modules.contains(&entry.global_ref.module) {
            warnings.insert("theorem_index_entry_unknown_module".to_owned());
            continue;
        }
        if let Some(module) = modules.get_mut(&entry.global_ref.module) {
            module.add_entry(entry);
        }
    }

    RefactorPlanTheoremIndexAggregation {
        modules: modules
            .into_iter()
            .map(|(module, accumulator)| (module.clone(), accumulator.finish(&module)))
            .collect(),
        warnings: warnings.into_iter().collect(),
    }
}

#[derive(Default)]
struct ModuleTheoremAccumulator {
    theorem_count: usize,
    axiom_count: usize,
    public_export_count: usize,
    families: BTreeMap<String, FamilyAccumulator>,
}

impl ModuleTheoremAccumulator {
    fn add_entry(&mut self, entry: &PackageTheoremIndexEntry) {
        match entry.kind {
            PackageTheoremIndexKind::Theorem => self.theorem_count += 1,
            PackageTheoremIndexKind::Axiom => self.axiom_count += 1,
        }
        self.public_export_count += 1;

        let name = entry.global_ref.name.as_dotted();
        let Some(prefix) = family_prefix(&name) else {
            return;
        };
        self.families
            .entry(prefix)
            .or_default()
            .add_entry(entry, name);
    }

    fn finish(self, module: &Name) -> RefactorPlanModuleTheoremAggregation {
        let mut families = self
            .families
            .into_iter()
            .filter_map(|(prefix, family)| family.finish(module, prefix))
            .collect::<Vec<_>>();
        families.sort_by(|left, right| {
            right
                .theorem_names
                .len()
                .cmp(&left.theorem_names.len())
                .then_with(|| left.prefix.cmp(&right.prefix))
                .then_with(|| left.theorem_names.first().cmp(&right.theorem_names.first()))
        });

        RefactorPlanModuleTheoremAggregation {
            theorem_count: self.theorem_count,
            axiom_count: self.axiom_count,
            public_export_count: self.public_export_count,
            families,
        }
    }
}

#[derive(Default)]
struct FamilyAccumulator {
    theorem_names: BTreeSet<String>,
    theorem_count: usize,
    axiom_count: usize,
    statement_heads: BTreeSet<String>,
    statement_constants: BTreeSet<String>,
}

impl FamilyAccumulator {
    fn add_entry(&mut self, entry: &PackageTheoremIndexEntry, name: String) {
        self.theorem_names.insert(name);
        match entry.kind {
            PackageTheoremIndexKind::Theorem => self.theorem_count += 1,
            PackageTheoremIndexKind::Axiom => self.axiom_count += 1,
        }
        if let Some(head) = &entry.statement.head {
            self.statement_heads.insert(statement_ref_key(head));
        }
        for constant in &entry.statement.constants {
            self.statement_constants.insert(statement_ref_key(constant));
        }
    }

    fn finish(self, module: &Name, prefix: String) -> Option<RefactorPlanTheoremFamilyAggregation> {
        if self.theorem_names.len() < FAMILY_CLUSTER_MIN_SIZE {
            return None;
        }
        let shared_prefix_length = prefix.len();
        Some(RefactorPlanTheoremFamilyAggregation {
            family: format!("{}::{prefix}_*", module.as_dotted()),
            prefix,
            theorem_names: self.theorem_names.into_iter().collect(),
            theorem_count: self.theorem_count,
            axiom_count: self.axiom_count,
            shared_prefix_length,
            statement_head_count: self.statement_heads.len(),
            statement_constant_count: self.statement_constants.len(),
        })
    }
}

fn family_prefix(name: &str) -> Option<String> {
    name.rsplit('.')
        .next()
        .into_iter()
        .flat_map(|component| component.split('_'))
        .find(|token| !token.is_empty())
        .map(ToOwned::to_owned)
}

fn statement_ref_key(reference: &PackageGlobalRefView) -> String {
    format!(
        "{}::{}",
        reference.module.as_dotted(),
        reference.name.as_dotted()
    )
}

/// Build refactor-plan candidates from package-lock and theorem-index metrics.
pub fn build_refactor_plan_candidates(
    root: &Path,
    lock: &PackageLockManifest,
    module_graph: &RefactorPlanModuleGraph,
    theorem_aggregation: Option<&RefactorPlanTheoremIndexAggregation>,
    options: &PackageRefactorPlanOptions,
) -> Vec<RefactorCandidate> {
    let mut candidates =
        build_module_candidates(root, lock, module_graph, theorem_aggregation, options);
    candidates.extend(build_theorem_family_candidates(
        root,
        lock,
        module_graph,
        theorem_aggregation,
        options,
    ));
    sort_and_limit_candidates(&mut candidates, options.top);
    candidates
}

/// Build module candidates with package-lock graph and certificate metadata metrics.
pub fn build_refactor_plan_module_candidates(
    root: &Path,
    lock: &PackageLockManifest,
    module_graph: &RefactorPlanModuleGraph,
    options: &PackageRefactorPlanOptions,
) -> Vec<RefactorCandidate> {
    let mut candidates = build_module_candidates(root, lock, module_graph, None, options);
    sort_and_limit_candidates(&mut candidates, options.top);
    candidates
}

fn build_module_candidates(
    root: &Path,
    lock: &PackageLockManifest,
    module_graph: &RefactorPlanModuleGraph,
    theorem_aggregation: Option<&RefactorPlanTheoremIndexAggregation>,
    options: &PackageRefactorPlanOptions,
) -> Vec<RefactorCandidate> {
    if !matches!(
        options.scope,
        PackageRefactorPlanScope::Modules | PackageRefactorPlanScope::Both
    ) {
        return Vec::new();
    }
    let entries = lock_entries_by_module(lock);
    let mut seeds = BTreeMap::<Name, ModuleMetricSeed>::new();
    for module in &module_graph.topological_order {
        let Some(entry) = entries.get(module).copied() else {
            continue;
        };
        let seed = if entry.origin == PackageLockEntryOrigin::Local {
            local_module_metric_seed(
                root,
                entry,
                module_graph,
                theorem_aggregation.and_then(|aggregation| aggregation.modules.get(module)),
            )
        } else {
            ModuleMetricSeed::external(module_graph, module)
        };
        seeds.insert(module.clone(), seed);
    }

    let local_complexity = seeds
        .iter()
        .map(|(module, seed)| (module.clone(), seed.local_complexity))
        .collect::<BTreeMap<_, _>>();

    module_graph
        .topological_order
        .iter()
        .filter_map(|module| {
            let entry = entries.get(module).copied()?;
            if entry.origin != PackageLockEntryOrigin::Local {
                return None;
            }
            if options
                .module
                .as_ref()
                .is_some_and(|requested| requested != module)
            {
                return None;
            }
            let seed = seeds.get(module)?;
            let dependent_complexity =
                dependent_complexity(module, module_graph, &local_complexity);
            let metrics = ModuleRefactorMetrics {
                local_complexity: seed.local_complexity,
                dependent_complexity,
                direct_dependents: module_graph.reverse_direct.get(module).map_or(0, Vec::len),
                transitive_dependents: module_graph
                    .reverse_transitive
                    .get(module)
                    .map_or(0, Vec::len),
                direct_import_count: seed.direct_import_count,
                theorem_count: seed.theorem_count,
                axiom_count: seed.axiom_count,
                public_export_count: seed.public_export_count,
                certificate_size_bytes: seed.certificate_size_bytes,
                certificate_size_weight: seed.certificate_size_weight,
                family_cluster_count: seed.family_cluster_count,
            };
            let risk = module_risk(&metrics);
            let recommendation = module_recommendation(&metrics);
            let evidence = module_evidence(
                &metrics,
                seed.certificate_metadata_available,
                theorem_aggregation.is_none(),
            );
            Some(RefactorCandidate::Module(ModuleRefactorCandidate {
                module: module.clone(),
                score: module_score(&metrics),
                recommendation,
                risk,
                metrics,
                evidence,
                suggested_unit: module_suggested_unit(module, seed.largest_family_key.as_deref()),
                suggested_verification: suggested_verification(risk),
                proof_evidence: false,
            }))
        })
        .collect()
}

fn build_theorem_family_candidates(
    root: &Path,
    lock: &PackageLockManifest,
    module_graph: &RefactorPlanModuleGraph,
    theorem_aggregation: Option<&RefactorPlanTheoremIndexAggregation>,
    options: &PackageRefactorPlanOptions,
) -> Vec<RefactorCandidate> {
    if !matches!(
        options.scope,
        PackageRefactorPlanScope::Theorems | PackageRefactorPlanScope::Both
    ) {
        return Vec::new();
    }
    let Some(theorem_aggregation) = theorem_aggregation else {
        return Vec::new();
    };

    let entries = lock_entries_by_module(lock);
    let local_complexity =
        module_local_complexity_seeds(root, lock, module_graph, theorem_aggregation);
    module_graph
        .topological_order
        .iter()
        .filter_map(|module| {
            let entry = entries.get(module).copied()?;
            if entry.origin != PackageLockEntryOrigin::Local {
                return None;
            }
            if options
                .module
                .as_ref()
                .is_some_and(|requested| requested != module)
            {
                return None;
            }
            let module_metrics = theorem_aggregation.modules.get(module)?;
            let module_dependent_complexity =
                dependent_complexity(module, module_graph, &local_complexity);
            let owner_risk = module_owner_risk(module, module_graph, module_metrics);
            Some(module_metrics.families.iter().map(move |family| {
                let metrics = TheoremFamilyMetrics {
                    theorem_count: family.theorem_count,
                    axiom_count: family.axiom_count,
                    shared_prefix_length: family.shared_prefix_length,
                    statement_head_count: family.statement_head_count,
                    statement_constant_count: family.statement_constant_count,
                    module_dependent_complexity,
                };
                let risk = theorem_family_risk(&metrics, owner_risk);
                let recommendation = theorem_family_recommendation(&metrics);
                let evidence = theorem_family_evidence(&metrics, owner_risk);
                RefactorCandidate::TheoremFamily(TheoremFamilyRefactorCandidate {
                    module: module.clone(),
                    family: family.family.clone(),
                    score: theorem_family_score(&metrics),
                    recommendation,
                    risk,
                    theorem_names: family.theorem_names.clone(),
                    metrics,
                    evidence,
                    suggested_unit: sanitize_suggested_unit(&family.family),
                    suggested_verification: suggested_verification(risk),
                    proof_evidence: false,
                })
            }))
        })
        .flatten()
        .collect()
}

fn module_local_complexity_seeds(
    root: &Path,
    lock: &PackageLockManifest,
    module_graph: &RefactorPlanModuleGraph,
    theorem_aggregation: &RefactorPlanTheoremIndexAggregation,
) -> BTreeMap<Name, f64> {
    let entries = lock_entries_by_module(lock);
    module_graph
        .topological_order
        .iter()
        .map(|module| {
            let local_complexity = entries
                .get(module)
                .copied()
                .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
                .map(|entry| {
                    local_module_metric_seed(
                        root,
                        entry,
                        module_graph,
                        theorem_aggregation.modules.get(module),
                    )
                    .local_complexity
                })
                .unwrap_or(0.0);
            (module.clone(), local_complexity)
        })
        .collect()
}

fn module_local_complexity_score(
    theorem_count: Option<usize>,
    axiom_count: Option<usize>,
    public_export_count: Option<usize>,
    direct_import_count: usize,
    certificate_size_weight: f64,
) -> f64 {
    theorem_count.unwrap_or(0) as f64 * THEOREM_WEIGHT
        + axiom_count.unwrap_or(0) as f64 * AXIOM_WEIGHT
        + public_export_count.unwrap_or(0) as f64 * PUBLIC_EXPORT_WEIGHT
        + direct_import_count as f64 * DIRECT_IMPORT_WEIGHT
        + certificate_size_weight
}

fn module_score(metrics: &ModuleRefactorMetrics) -> f64 {
    metrics.local_complexity
        + metrics.dependent_complexity * DEPENDENT_COMPLEXITY_WEIGHT
        + mixed_purpose_bonus(metrics)
        + family_cluster_bonus(metrics.family_cluster_count)
        + verification_containment_bonus(metrics)
}

fn family_cluster_bonus(family_cluster_count: usize) -> f64 {
    (family_cluster_count as f64 * FAMILY_CLUSTER_BONUS_PER_CLUSTER).min(FAMILY_CLUSTER_BONUS_CAP)
}

fn mixed_purpose_bonus(metrics: &ModuleRefactorMetrics) -> f64 {
    if metrics.family_cluster_count >= 2 && metrics.direct_import_count >= 2 {
        MIXED_PURPOSE_BONUS
    } else {
        0.0
    }
}

fn verification_containment_bonus(metrics: &ModuleRefactorMetrics) -> f64 {
    if metrics.transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
        && metrics.local_complexity <= 20.0
    {
        VERIFICATION_CONTAINMENT_BONUS
    } else {
        0.0
    }
}

fn module_recommendation(metrics: &ModuleRefactorMetrics) -> RefactorRecommendation {
    if (metrics.direct_dependents >= HIGH_FANOUT_DIRECT_THRESHOLD
        || metrics.transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD)
        && metrics.local_complexity <= 20.0
    {
        RefactorRecommendation::StabilizeBoundary
    } else if metrics.transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
        && metrics.family_cluster_count >= 1
    {
        RefactorRecommendation::ExtractFoundation
    } else if metrics.public_export_count.unwrap_or(0) >= LARGE_MODULE_EXPORT_THRESHOLD
        && metrics.family_cluster_count >= 2
    {
        RefactorRecommendation::ModuleSplit
    } else if metrics.direct_import_count >= 5 && metrics.direct_dependents <= 2 {
        RefactorRecommendation::DependencyHygiene
    } else if metrics.local_complexity >= 15.0 {
        RefactorRecommendation::LocalCleanup
    } else {
        RefactorRecommendation::NoAction
    }
}

fn module_risk(metrics: &ModuleRefactorMetrics) -> RefactorRisk {
    module_risk_from_counts(
        metrics.direct_dependents,
        metrics.transitive_dependents,
        metrics.public_export_count,
    )
}

fn module_owner_risk(
    module: &Name,
    module_graph: &RefactorPlanModuleGraph,
    theorem_metrics: &RefactorPlanModuleTheoremAggregation,
) -> RefactorRisk {
    module_risk_from_counts(
        module_graph.reverse_direct.get(module).map_or(0, Vec::len),
        module_graph
            .reverse_transitive
            .get(module)
            .map_or(0, Vec::len),
        Some(theorem_metrics.public_export_count),
    )
}

fn module_risk_from_counts(
    direct_dependents: usize,
    transitive_dependents: usize,
    public_export_count: Option<usize>,
) -> RefactorRisk {
    if transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
        || direct_dependents >= HIGH_FANOUT_DIRECT_THRESHOLD
    {
        RefactorRisk::High
    } else if transitive_dependents >= 4
        || public_export_count.unwrap_or(0) >= LARGE_MODULE_EXPORT_THRESHOLD
    {
        RefactorRisk::Medium
    } else {
        RefactorRisk::Low
    }
}

fn module_evidence(
    metrics: &ModuleRefactorMetrics,
    certificate_metadata_available: bool,
    theorem_index_missing: bool,
) -> Vec<String> {
    let mut evidence = Vec::new();
    if metrics.direct_dependents >= HIGH_FANOUT_DIRECT_THRESHOLD {
        evidence.push("high_direct_dependents".to_owned());
    }
    if metrics.transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD {
        evidence.push("high_transitive_dependents".to_owned());
    }
    if metrics.public_export_count.unwrap_or(0) >= LARGE_MODULE_EXPORT_THRESHOLD {
        evidence.push("large_public_export_count".to_owned());
    }
    if metrics.family_cluster_count >= 2 {
        evidence.push("multiple_theorem_family_clusters".to_owned());
    }
    if metrics.direct_import_count >= 5 {
        evidence.push("many_direct_imports".to_owned());
    }
    if metrics.transitive_dependents >= HIGH_FANOUT_TRANSITIVE_THRESHOLD
        && metrics.local_complexity <= 20.0
    {
        evidence.push("small_foundational_high_fanout".to_owned());
    }
    if !certificate_metadata_available {
        evidence.push("certificate_metadata_unavailable".to_owned());
    }
    if theorem_index_missing {
        evidence.push("theorem_index_missing".to_owned());
    }
    evidence
}

fn theorem_family_score(metrics: &TheoremFamilyMetrics) -> f64 {
    metrics.theorem_count as f64 * THEOREM_FAMILY_THEOREM_WEIGHT
        + metrics.axiom_count as f64 * THEOREM_FAMILY_AXIOM_WEIGHT
        + metrics
            .shared_prefix_length
            .min(THEOREM_FAMILY_PREFIX_LENGTH_CAP) as f64
        + metrics.module_dependent_complexity
}

fn theorem_family_risk(metrics: &TheoremFamilyMetrics, owner_risk: RefactorRisk) -> RefactorRisk {
    if owner_risk == RefactorRisk::High || metrics.axiom_count > 0 {
        RefactorRisk::High
    } else if metrics.theorem_count >= 8 {
        RefactorRisk::Medium
    } else {
        RefactorRisk::Low
    }
}

fn theorem_family_recommendation(metrics: &TheoremFamilyMetrics) -> RefactorRecommendation {
    if metrics.theorem_count >= 3 {
        RefactorRecommendation::TheoremFamilyGroup
    } else {
        RefactorRecommendation::LocalCleanup
    }
}

fn theorem_family_evidence(
    metrics: &TheoremFamilyMetrics,
    owner_risk: RefactorRisk,
) -> Vec<String> {
    let mut evidence = Vec::new();
    if metrics.theorem_count >= 8 {
        evidence.push("large_theorem_family".to_owned());
    }
    if metrics.axiom_count > 0 {
        evidence.push("axiom_bearing_family".to_owned());
    }
    evidence.push("shared_name_prefix".to_owned());
    if owner_risk == RefactorRisk::High {
        evidence.push("high_fanout_owner_module".to_owned());
    }
    if metrics.statement_constant_count > 0 {
        evidence.push("statement_constant_signal".to_owned());
    }
    evidence
}

fn module_suggested_unit(module: &Name, largest_family_key: Option<&str>) -> String {
    if let Some(largest_family_key) = largest_family_key {
        sanitize_suggested_unit(largest_family_key)
    } else {
        sanitize_suggested_unit(&module.as_dotted())
    }
}

fn suggested_verification(risk: RefactorRisk) -> Vec<String> {
    let mut commands = vec![VERIFY_CHANGED_COMMAND.to_owned()];
    if risk == RefactorRisk::High {
        commands.push(VERIFY_INDEX_COMMAND.to_owned());
        commands.push(VERIFY_EXPORT_SUMMARY_COMMAND.to_owned());
    }
    commands
}

fn sanitize_suggested_unit(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii() && ch != ';' && ch != '|' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn sort_and_limit_candidates(candidates: &mut Vec<RefactorCandidate>, top: usize) {
    candidates.sort_by(|left, right| {
        right
            .score()
            .total_cmp(&left.score())
            .then_with(|| {
                right
                    .dependent_complexity()
                    .total_cmp(&left.dependent_complexity())
            })
            .then_with(|| right.local_complexity().total_cmp(&left.local_complexity()))
            .then_with(|| left.kind().cmp(right.kind()))
            .then_with(|| left.module_name().cmp(&right.module_name()))
            .then_with(|| left.family_key().cmp(&right.family_key()))
    });
    candidates.truncate(top);
}

impl RefactorCandidate {
    fn score(&self) -> f64 {
        match self {
            Self::Module(candidate) => candidate.score,
            Self::TheoremFamily(candidate) => candidate.score,
        }
    }

    fn dependent_complexity(&self) -> f64 {
        match self {
            Self::Module(candidate) => candidate.metrics.dependent_complexity,
            Self::TheoremFamily(candidate) => candidate.metrics.module_dependent_complexity,
        }
    }

    fn local_complexity(&self) -> f64 {
        match self {
            Self::Module(candidate) => candidate.metrics.local_complexity,
            Self::TheoremFamily(_) => 0.0,
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            Self::Module(_) => "module",
            Self::TheoremFamily(_) => "theorem-family",
        }
    }

    fn module_name(&self) -> String {
        match self {
            Self::Module(candidate) => candidate.module.as_dotted(),
            Self::TheoremFamily(candidate) => candidate.module.as_dotted(),
        }
    }

    fn family_key(&self) -> String {
        match self {
            Self::Module(_) => String::new(),
            Self::TheoremFamily(candidate) => candidate.family.clone(),
        }
    }
}

#[derive(Clone, Debug)]
struct ModuleMetricSeed {
    direct_import_count: usize,
    theorem_count: Option<usize>,
    axiom_count: Option<usize>,
    public_export_count: Option<usize>,
    certificate_size_bytes: Option<u64>,
    certificate_size_weight: f64,
    certificate_metadata_available: bool,
    family_cluster_count: usize,
    largest_family_key: Option<String>,
    local_complexity: f64,
}

impl ModuleMetricSeed {
    fn external(module_graph: &RefactorPlanModuleGraph, module: &Name) -> Self {
        Self {
            direct_import_count: module_graph
                .direct_imports
                .get(module)
                .map_or(0, BTreeSet::len),
            theorem_count: None,
            axiom_count: None,
            public_export_count: None,
            certificate_size_bytes: None,
            certificate_size_weight: 0.0,
            certificate_metadata_available: true,
            family_cluster_count: 0,
            largest_family_key: None,
            local_complexity: 0.0,
        }
    }
}

fn local_module_metric_seed(
    root: &Path,
    entry: &PackageLockEntry,
    module_graph: &RefactorPlanModuleGraph,
    theorem_metrics: Option<&RefactorPlanModuleTheoremAggregation>,
) -> ModuleMetricSeed {
    let direct_import_count = module_graph
        .direct_imports
        .get(&entry.module)
        .map_or(0, BTreeSet::len);
    let (certificate_size_bytes, certificate_size_weight, certificate_metadata_available) =
        certificate_size_metric(root, entry);
    let theorem_count = theorem_metrics.map(|metrics| metrics.theorem_count);
    let axiom_count = theorem_metrics.map(|metrics| metrics.axiom_count);
    let public_export_count = theorem_metrics.map(|metrics| metrics.public_export_count);
    let family_cluster_count = theorem_metrics.map_or(0, |metrics| metrics.families.len());
    let largest_family_key = theorem_metrics
        .and_then(|metrics| metrics.families.first())
        .map(|family| family.family.clone());
    let local_complexity = module_local_complexity_score(
        theorem_count,
        axiom_count,
        public_export_count,
        direct_import_count,
        certificate_size_weight,
    );
    ModuleMetricSeed {
        direct_import_count,
        theorem_count,
        axiom_count,
        public_export_count,
        certificate_size_bytes,
        certificate_size_weight,
        certificate_metadata_available,
        family_cluster_count,
        largest_family_key,
        local_complexity,
    }
}

fn certificate_size_metric(root: &Path, entry: &PackageLockEntry) -> (Option<u64>, f64, bool) {
    let full_path = match join_package_path(root, &entry.certificate, "package_lock.certificate") {
        Ok(path) => path,
        Err(_) => return (None, 0.0, false),
    };
    match fs::metadata(full_path) {
        Ok(metadata) if metadata.is_file() => {
            let bytes = metadata.len();
            let bucket = (bytes / CERTIFICATE_SIZE_BUCKET_BYTES).min(CERTIFICATE_SIZE_WEIGHT_CAP);
            (Some(bytes), bucket as f64, true)
        }
        Ok(_) | Err(_) => (None, 0.0, false),
    }
}

fn dependent_complexity(
    module: &Name,
    module_graph: &RefactorPlanModuleGraph,
    local_complexity: &BTreeMap<Name, f64>,
) -> f64 {
    module_graph
        .reverse_transitive
        .get(module)
        .into_iter()
        .flatten()
        .map(|dependent| {
            local_complexity
                .get(&dependent.module)
                .copied()
                .unwrap_or(0.0)
                / dependent.distance as f64
        })
        .sum()
}

fn lock_entries_by_module(lock: &PackageLockManifest) -> BTreeMap<Name, &PackageLockEntry> {
    lock.entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect()
}

fn read_package_lock(loaded: &LoadedPackageRoot) -> Result<PackageLockManifest, CommandResult> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let full_lock_path = match join_package_path(&loaded.root, &lock_path, "package_lock.path") {
        Ok(path) => path,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![*diagnostic],
            ));
        }
    };
    let lock_source = match fs::read_to_string(&full_lock_path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![
                    CommandDiagnostic::error(DiagnosticKind::PackageLock, "package_lock_missing")
                        .with_path(PACKAGE_LOCK_PATH),
                ],
            ));
        }
        Err(_) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_lock_missing")
                        .with_path(PACKAGE_LOCK_PATH),
                ],
            ));
        }
    };
    parse_package_lock_json(&lock_source).map_err(|error| {
        CommandResult::failed(
            COMMAND,
            loaded.root_display.clone(),
            vec![CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH)],
        )
    })
}

fn read_optional_theorem_index(
    loaded: &LoadedPackageRoot,
) -> Result<Option<PackageTheoremIndex>, CommandResult> {
    let index_path = PackagePath::new(PACKAGE_THEOREM_INDEX_PATH);
    let full_index_path =
        match join_package_path(&loaded.root, &index_path, "generated.theorem_index.path") {
            Ok(path) => path,
            Err(diagnostic) => {
                return Err(CommandResult::failed(
                    COMMAND,
                    loaded.root_display.clone(),
                    vec![*diagnostic],
                ));
            }
        };
    let index_source = match fs::read_to_string(&full_index_path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![refactor_plan_theorem_index_invalid_diagnostic(None)],
            ));
        }
    };
    parse_package_theorem_index_json(&index_source)
        .map(Some)
        .map_err(|error| {
            CommandResult::failed(
                COMMAND,
                loaded.root_display.clone(),
                vec![refactor_plan_theorem_index_invalid_diagnostic(Some(&error))],
            )
        })
}

fn validate_requested_module(
    lock: &PackageLockManifest,
    requested: Option<&Name>,
    root_display: &str,
) -> Result<(), CommandResult> {
    let Some(requested) = requested else {
        return Ok(());
    };
    match lock_entry_for_module(lock, requested) {
        Some(entry) if entry.origin == PackageLockEntryOrigin::Local => Ok(()),
        Some(_) => Err(CommandResult::failed(
            COMMAND,
            root_display.to_owned(),
            vec![requested_module_diagnostic(
                "refactor_plan_module_not_local",
                requested,
            )],
        )),
        None => Err(CommandResult::failed(
            COMMAND,
            root_display.to_owned(),
            vec![requested_module_diagnostic(
                "refactor_plan_module_unknown",
                requested,
            )],
        )),
    }
}

fn lock_entry_for_module<'a>(
    lock: &'a PackageLockManifest,
    module: &Name,
) -> Option<&'a PackageLockEntry> {
    lock.entries.iter().find(|entry| &entry.module == module)
}

fn requested_module_diagnostic(reason_code: &'static str, module: &Name) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::PackageLock, reason_code)
        .with_field("--module")
        .with_module(module.as_dotted())
        .with_actual_value(module.as_dotted())
}

fn refactor_plan_theorem_index_invalid_diagnostic(
    error: Option<&PackageArtifactError>,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::TheoremIndex,
        "refactor_plan_theorem_index_invalid",
    )
    .with_path(PACKAGE_THEOREM_INDEX_PATH);
    if let Some(error) = error {
        diagnostic = diagnostic.with_field(error.field.clone().unwrap_or_else(|| {
            if error.path == "$" {
                "theorem_index".to_owned()
            } else {
                error.path.clone()
            }
        }));
        diagnostic = diagnostic.with_actual_value(error.reason_code.as_str());
    }
    diagnostic
}

fn refactor_plan_lock_graph_diagnostic(error: PackageArtifactError) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::PackageLock,
        "refactor_plan_lock_graph_invalid",
    )
    .with_field(error.field.unwrap_or(error.path))
    .with_actual_value(error.reason_code.as_str())
}

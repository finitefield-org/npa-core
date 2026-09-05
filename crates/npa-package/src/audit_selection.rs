//! Deterministic package audit selection from package-lock identity changes.
//!
//! This module is metadata-only. It selects modules that should later be passed
//! to package verification, but it does not verify certificates and never
//! represents proof evidence.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

#[cfg(test)]
use crate::lock::PackageLockEntry;

#[cfg(any(test, feature = "planning-benchmark"))]
use crate::lock::PackageGraphPlanningCounterSummary;
use crate::{
    error::{PackageArtifactError, PackageArtifactResult, PackageLockError},
    lock::{
        build_indexed_package_lock_graph, IndexedPackageLockGraph, IndexedPackageLockGraphError,
        PackageLockManifest,
    },
};

trait AuditPlanningCounterSink {
    fn reverse_vertex_dequeued(&mut self) {}
    fn reverse_edges_visited(&mut self, _count: usize) {}
    fn reverse_visit_slots_initialized(&mut self, _count: usize) {}
    fn reverse_origin_started(&mut self) {}
    fn provenance_pair_dequeued(&mut self) {}
    fn provenance_edges_visited(&mut self, _count: usize) {}
    fn provenance_visit_slots_initialized(&mut self, _count: usize) {}
    fn provenance_origin_started(&mut self) {}
}

impl AuditPlanningCounterSink for () {}

#[cfg(any(test, feature = "planning-benchmark"))]
impl AuditPlanningCounterSink for PackageGraphPlanningCounterSummary {
    fn reverse_vertex_dequeued(&mut self) {
        add_planning_counter(&mut self.reverse_vertex_dequeues, 1, &mut self.overflowed);
    }

    fn reverse_edges_visited(&mut self, count: usize) {
        add_planning_counter(&mut self.reverse_edge_visits, count, &mut self.overflowed);
    }

    fn reverse_visit_slots_initialized(&mut self, count: usize) {
        add_planning_counter(
            &mut self.reverse_visit_slots_initialized,
            count,
            &mut self.overflowed,
        );
    }

    fn reverse_origin_started(&mut self) {
        add_planning_counter(&mut self.reverse_origin_epochs, 1, &mut self.overflowed);
    }

    fn provenance_pair_dequeued(&mut self) {
        add_planning_counter(&mut self.provenance_pair_dequeues, 1, &mut self.overflowed);
    }

    fn provenance_edges_visited(&mut self, count: usize) {
        add_planning_counter(
            &mut self.provenance_edge_visits,
            count,
            &mut self.overflowed,
        );
    }

    fn provenance_visit_slots_initialized(&mut self, count: usize) {
        add_planning_counter(
            &mut self.provenance_visit_slots_initialized,
            count,
            &mut self.overflowed,
        );
    }

    fn provenance_origin_started(&mut self) {
        add_planning_counter(&mut self.provenance_origin_epochs, 1, &mut self.overflowed);
    }
}

#[cfg(any(test, feature = "planning-benchmark"))]
fn add_planning_counter(value: &mut u64, addend: usize, overflowed: &mut bool) {
    let conversion_overflowed = u64::try_from(addend).is_err();
    let addend = u64::try_from(addend).unwrap_or(u64::MAX);
    let (next, overflow) = value.overflowing_add(addend);
    *value = if overflow { u64::MAX } else { next };
    *overflowed |= overflow || conversion_overflowed;
}

/// Reusable per-operation visitation marks. One `O(V)` allocation serves every
/// origin; advancing an epoch is `O(1)` and origin count cannot exceed the
/// addressable entry count that sized `marks`.
struct EntryEpochMarks {
    marks: Vec<usize>,
    epoch: usize,
}

impl EntryEpochMarks {
    fn new(entry_count: usize) -> Self {
        Self {
            marks: vec![0; entry_count],
            epoch: 0,
        }
    }

    fn begin_origin(&mut self) {
        self.epoch = self
            .epoch
            .checked_add(1)
            .expect("origin count cannot exceed addressable package-lock entries");
    }

    fn mark_new(&mut self, entry: usize) -> bool {
        if self.marks[entry] == self.epoch {
            false
        } else {
            self.marks[entry] = self.epoch;
            true
        }
    }
}

/// Kind of package-lock identity change observed for one module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageAuditChangeKind {
    /// Canonical certificate hash changed.
    CertificateHashChanged,
    /// Public export hash changed.
    ExportHashChanged,
    /// Module axiom report hash changed.
    AxiomReportHashChanged,
    /// Certificate file byte hash changed.
    CertificateFileHashChanged,
    /// Package policy changed.
    PolicyChanged,
    /// Checker identity or checker profile changed.
    CheckerIdentityChanged,
    /// Core specification profile changed.
    CoreSpecChanged,
    /// Certificate format profile changed.
    CertificateFormatChanged,
}

/// One module with one or more observed package audit changes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditChangedModule {
    /// Changed module name.
    pub module: Name,
    /// Deterministic change kinds for this module.
    pub changes: Vec<PackageAuditChangeKind>,
}

/// Reason a module was selected for audit.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageAuditSelectionReason {
    /// The module was explicitly reported as changed.
    ExplicitlyChanged,
    /// The module depends, directly or transitively, on a changed export.
    ReverseDependencyOfExportChange {
        /// Changed dependency that caused this module to be selected.
        dependency: Name,
    },
    /// A package policy change requires auditing all modules.
    RequiredByPolicyChange,
    /// A checker identity change requires auditing all modules.
    RequiredByCheckerIdentityChange,
    /// A core specification change requires auditing all modules.
    RequiredByCoreSpecChange,
    /// A certificate format change requires auditing all modules.
    RequiredByCertificateFormatChange,
}

/// One selected module and deterministic reasons for its selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditSelectedModule {
    /// Selected module name.
    pub module: Name,
    /// Deterministic selection reasons.
    pub reasons: Vec<PackageAuditSelectionReason>,
}

/// Deterministic package audit selection result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditSelection {
    /// Selected modules in package-lock topological order.
    pub modules: Vec<PackageAuditSelectedModule>,
    /// Reverse dependents intentionally skipped because only stable-export
    /// certificate/file/axiom metadata changed.
    pub skipped_stable_export_dependents: Vec<Name>,
    /// Whether checked `generated/axiom-report.json` must be refreshed/checked.
    pub package_axiom_report_check_required: bool,
    /// Whether checked `generated/theorem-index.json` must be refreshed/checked.
    pub package_theorem_index_check_required: bool,
    /// Always false: selection is not proof evidence.
    pub proof_evidence: bool,
}

/// Reason a module must run live in a cache-aware verifier pass.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageCacheAwareLiveReason {
    /// The module itself was reported dirty.
    Dirty,
    /// The module depends, directly or transitively, on a dirty module.
    ReverseDependencyOfDirty {
        /// Dirty dependency that caused this module to run live.
        dependency: Name,
    },
}

/// One module selected for live checking in a cache-aware verifier pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageCacheAwareLiveModule {
    /// Module name.
    pub module: Name,
    /// Deterministic live-check reasons.
    pub reasons: Vec<PackageCacheAwareLiveReason>,
}

/// Deterministic cache-aware verifier live-set selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageCacheAwareLiveSelection {
    /// Live modules in package-lock topological order.
    pub modules: Vec<PackageCacheAwareLiveModule>,
    /// Always false: cache-aware selection is not proof evidence.
    pub proof_evidence: bool,
}

/// Package-lock modules grouped into deterministic dependency layers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTopologicalLayers {
    /// Layers in dependency-before-dependent order.
    ///
    /// Every module in one layer imports only modules from earlier layers, and
    /// modules inside each layer are sorted by package-lock topological order.
    pub layers: Vec<Vec<Name>>,
}

/// Return direct reverse dependencies for every module in a package lock.
///
/// Each map key is a package-lock module. Each value is sorted in package-lock
/// topological order for deterministic closure traversal.
pub fn package_lock_reverse_dependencies(
    lock: &PackageLockManifest,
) -> PackageArtifactResult<BTreeMap<Name, Vec<Name>>> {
    let indexed = build_indexed_package_lock_graph(lock).map_err(indexed_package_lock_error)?;
    let mut reverse = BTreeMap::new();
    for entry in 0..indexed.entries().len() {
        let module = indexed
            .index()
            .module_by_entry(entry)
            .expect("validated index contains every entry")
            .clone();
        let dependents = indexed
            .index()
            .reverse_dependencies(entry)
            .unwrap_or_default()
            .iter()
            .map(|dependent| {
                indexed
                    .index()
                    .module_by_entry(*dependent)
                    .expect("validated index contains every entry")
                    .clone()
            })
            .collect();
        reverse.insert(module, dependents);
    }
    Ok(reverse)
}

/// Group every package-lock module into deterministic topological layers.
pub fn package_lock_topological_layers(
    lock: &PackageLockManifest,
) -> PackageArtifactResult<PackageTopologicalLayers> {
    let indexed = build_indexed_package_lock_graph(lock).map_err(indexed_package_lock_error)?;
    let selected = vec![true; indexed.entries().len()];
    let layers = indexed
        .index()
        .topological_layers(&selected)
        .into_iter()
        .map(|layer| {
            layer
                .into_iter()
                .map(|entry| {
                    indexed
                        .index()
                        .module_by_entry(entry)
                        .expect("validated index contains every entry")
                        .clone()
                })
                .collect()
        })
        .collect();
    Ok(PackageTopologicalLayers { layers })
}

/// Select modules that should be audited for the provided package-lock changes.
///
/// The returned selection is a plan only. It does not run a checker, verify a
/// certificate, or imply that unselected modules have been verified.
pub fn select_package_audit_modules(
    lock: &PackageLockManifest,
    changed: &[PackageAuditChangedModule],
) -> PackageArtifactResult<PackageAuditSelection> {
    let indexed = build_indexed_package_lock_graph(lock).map_err(indexed_package_lock_error)?;
    select_package_audit_modules_indexed(&indexed, changed)
}

/// Select audit modules using one already validated operation index.
#[doc(hidden)]
pub fn select_package_audit_modules_indexed(
    indexed: &IndexedPackageLockGraph,
    changed: &[PackageAuditChangedModule],
) -> PackageArtifactResult<PackageAuditSelection> {
    select_package_audit_modules_indexed_with_sink(indexed, changed, &mut ())
}

/// Counted audit selection for tests and the closed planning benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
pub fn select_package_audit_modules_indexed_with_planning_counters(
    indexed: &IndexedPackageLockGraph,
    changed: &[PackageAuditChangedModule],
    counters: &mut PackageGraphPlanningCounterSummary,
) -> PackageArtifactResult<PackageAuditSelection> {
    select_package_audit_modules_indexed_with_sink(indexed, changed, counters)
}

fn select_package_audit_modules_indexed_with_sink<S: AuditPlanningCounterSink>(
    indexed: &IndexedPackageLockGraph,
    changed: &[PackageAuditChangedModule],
    counters: &mut S,
) -> PackageArtifactResult<PackageAuditSelection> {
    let entry_modules = indexed
        .entries()
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let topological_order = &indexed.graph().topological_order;

    let mut normalized_changed = changed.to_vec();
    normalize_changed_modules(&mut normalized_changed);
    validate_changed_modules(&entry_modules, &normalized_changed)?;

    let mut selected = BTreeMap::<Name, BTreeSet<PackageAuditSelectionReason>>::new();
    let mut skipped = BTreeSet::<Name>::new();
    let mut axiom_artifact_checks_required = false;
    let mut reverse_marks = EntryEpochMarks::new(indexed.entries().len());
    counters.reverse_visit_slots_initialized(indexed.entries().len());

    let select_all_policy =
        changed_contains_any(&normalized_changed, PackageAuditChangeKind::PolicyChanged);
    let select_all_checker = changed_contains_any(
        &normalized_changed,
        PackageAuditChangeKind::CheckerIdentityChanged,
    );
    let select_all_core =
        changed_contains_any(&normalized_changed, PackageAuditChangeKind::CoreSpecChanged);
    let select_all_certificate_format = changed_contains_any(
        &normalized_changed,
        PackageAuditChangeKind::CertificateFormatChanged,
    );

    if select_all_policy {
        select_all(
            topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByPolicyChange,
        );
    }
    if select_all_checker {
        select_all(
            topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByCheckerIdentityChange,
        );
    }
    if select_all_core {
        select_all(
            topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByCoreSpecChange,
        );
    }
    if select_all_certificate_format {
        select_all(
            topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByCertificateFormatChange,
        );
    }

    for changed_module in &normalized_changed {
        select_reason(
            &mut selected,
            &changed_module.module,
            PackageAuditSelectionReason::ExplicitlyChanged,
        );

        let changes = changed_module
            .changes
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if changes.contains(&PackageAuditChangeKind::AxiomReportHashChanged) {
            axiom_artifact_checks_required = true;
        }
        if changes.contains(&PackageAuditChangeKind::ExportHashChanged) {
            for dependent in indexed_reverse_dependency_closure_with_sink(
                indexed,
                &changed_module.module,
                &mut reverse_marks,
                counters,
            ) {
                select_reason(
                    &mut selected,
                    &dependent,
                    PackageAuditSelectionReason::ReverseDependencyOfExportChange {
                        dependency: changed_module.module.clone(),
                    },
                );
            }
        } else if changes.contains(&PackageAuditChangeKind::CertificateHashChanged)
            || changes.contains(&PackageAuditChangeKind::CertificateFileHashChanged)
            || changes.contains(&PackageAuditChangeKind::AxiomReportHashChanged)
        {
            skipped.extend(indexed_reverse_dependency_closure_with_sink(
                indexed,
                &changed_module.module,
                &mut reverse_marks,
                counters,
            ));
        }
    }

    // A global selection reason (for example, a policy change) dominates an
    // independently observed stable-export skip.  Keep the two result
    // populations disjoint so downstream audit planners cannot both execute
    // and report the same module as intentionally skipped.
    skipped.retain(|module| !selected.contains_key(module));

    let modules = topological_order
        .iter()
        .filter_map(|module| {
            selected
                .remove(module)
                .map(|reasons| PackageAuditSelectedModule {
                    module: module.clone(),
                    reasons: reasons.into_iter().collect(),
                })
        })
        .collect();

    Ok(PackageAuditSelection {
        modules,
        skipped_stable_export_dependents: skipped.into_iter().collect(),
        package_axiom_report_check_required: axiom_artifact_checks_required,
        package_theorem_index_check_required: axiom_artifact_checks_required,
        proof_evidence: false,
    })
}

fn indexed_reverse_dependency_closure_with_sink<S: AuditPlanningCounterSink>(
    indexed: &IndexedPackageLockGraph,
    module: &Name,
    visited: &mut EntryEpochMarks,
    counters: &mut S,
) -> BTreeSet<Name> {
    let Some(entry) = indexed.index().entry_by_module(module) else {
        return BTreeSet::new();
    };
    let mut closure = BTreeSet::new();
    visited.begin_origin();
    counters.reverse_origin_started();
    let direct = indexed
        .index()
        .reverse_dependencies(entry)
        .unwrap_or_default();
    counters.reverse_edges_visited(direct.len());
    let mut pending = Vec::with_capacity(direct.len());
    for dependent in direct {
        if visited.mark_new(*dependent) {
            pending.push(*dependent);
        }
    }
    while let Some(dependent) = pending.pop() {
        counters.reverse_vertex_dequeued();
        closure.insert(
            indexed
                .index()
                .module_by_entry(dependent)
                .expect("validated index contains every entry")
                .clone(),
        );
        let next = indexed
            .index()
            .reverse_dependencies(dependent)
            .unwrap_or_default();
        counters.reverse_edges_visited(next.len());
        for next_dependent in next {
            if visited.mark_new(*next_dependent) {
                pending.push(*next_dependent);
            }
        }
    }
    closure
}

/// Select dirty modules and all reverse dependents that must run live in a
/// cache-aware verifier pass.
///
/// This is metadata-only planning. It validates module names against the
/// package lock, but it does not read certificates or accept proof results.
pub fn select_package_cache_aware_live_modules(
    lock: &PackageLockManifest,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageArtifactResult<PackageCacheAwareLiveSelection> {
    let indexed = build_indexed_package_lock_graph(lock).map_err(indexed_package_lock_error)?;
    select_package_cache_aware_live_modules_indexed(&indexed, dirty_modules)
}

/// Select cache-aware live modules using one already validated operation index.
///
/// This hidden composition boundary lets multi-stage commands reuse the exact
/// normalized graph that was validated at their operation boundary.
#[doc(hidden)]
pub fn select_package_cache_aware_live_modules_indexed(
    indexed: &IndexedPackageLockGraph,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageArtifactResult<PackageCacheAwareLiveSelection> {
    select_package_cache_aware_live_modules_indexed_with_sink(indexed, dirty_modules, &mut ())
}

/// Counted provenance selection for tests and the closed planning benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
pub fn select_package_cache_aware_live_modules_indexed_with_planning_counters(
    indexed: &IndexedPackageLockGraph,
    dirty_modules: impl IntoIterator<Item = Name>,
    counters: &mut PackageGraphPlanningCounterSummary,
) -> PackageArtifactResult<PackageCacheAwareLiveSelection> {
    select_package_cache_aware_live_modules_indexed_with_sink(indexed, dirty_modules, counters)
}

fn select_package_cache_aware_live_modules_indexed_with_sink<S: AuditPlanningCounterSink>(
    indexed: &IndexedPackageLockGraph,
    dirty_modules: impl IntoIterator<Item = Name>,
    counters: &mut S,
) -> PackageArtifactResult<PackageCacheAwareLiveSelection> {
    let dirty_modules = dirty_modules.into_iter().collect::<BTreeSet<_>>();
    for (position, module) in dirty_modules.iter().enumerate() {
        if indexed.index().entry_by_module(module).is_none() {
            return Err(PackageArtifactError::summary_mismatch(
                format!("dirty_modules[{position}]"),
                "module",
                "package lock module",
                module.as_dotted(),
            ));
        }
    }

    let mut selected = BTreeMap::<Name, BTreeSet<PackageCacheAwareLiveReason>>::new();
    let mut visited = EntryEpochMarks::new(indexed.entries().len());
    counters.provenance_visit_slots_initialized(indexed.entries().len());
    for dirty in &dirty_modules {
        selected
            .entry(dirty.clone())
            .or_default()
            .insert(PackageCacheAwareLiveReason::Dirty);
        let dirty_entry = indexed
            .index()
            .entry_by_module(dirty)
            .expect("dirty module membership was checked above");
        visited.begin_origin();
        counters.provenance_origin_started();
        let direct = indexed
            .index()
            .reverse_dependencies(dirty_entry)
            .unwrap_or_default();
        counters.provenance_edges_visited(direct.len());
        let mut pending = Vec::with_capacity(direct.len());
        for dependent in direct {
            if visited.mark_new(*dependent) {
                pending.push(*dependent);
            }
        }
        while let Some(dependent_entry) = pending.pop() {
            counters.provenance_pair_dequeued();
            let dependent = indexed
                .index()
                .module_by_entry(dependent_entry)
                .expect("validated index contains every entry")
                .clone();
            selected.entry(dependent).or_default().insert(
                PackageCacheAwareLiveReason::ReverseDependencyOfDirty {
                    dependency: dirty.clone(),
                },
            );
            let next = indexed
                .index()
                .reverse_dependencies(dependent_entry)
                .unwrap_or_default();
            counters.provenance_edges_visited(next.len());
            for next_dependent in next {
                if visited.mark_new(*next_dependent) {
                    pending.push(*next_dependent);
                }
            }
        }
    }

    let modules = indexed
        .index()
        .topological_entries()
        .iter()
        .filter_map(|entry| {
            let module = indexed
                .index()
                .module_by_entry(*entry)
                .expect("validated index contains every entry");
            selected
                .remove(module)
                .map(|reasons| PackageCacheAwareLiveModule {
                    module: module.clone(),
                    reasons: reasons.into_iter().collect(),
                })
        })
        .collect();

    Ok(PackageCacheAwareLiveSelection {
        modules,
        proof_evidence: false,
    })
}

fn normalize_changed_modules(changed: &mut Vec<PackageAuditChangedModule>) {
    let mut merged = BTreeMap::<Name, BTreeSet<PackageAuditChangeKind>>::new();
    for changed_module in changed.drain(..) {
        merged
            .entry(changed_module.module)
            .or_default()
            .extend(changed_module.changes);
    }
    changed.extend(
        merged
            .into_iter()
            .map(|(module, changes)| PackageAuditChangedModule {
                module,
                changes: changes.into_iter().collect(),
            }),
    );
}

fn validate_changed_modules(
    entry_modules: &BTreeSet<Name>,
    changed: &[PackageAuditChangedModule],
) -> PackageArtifactResult<()> {
    for (index, changed_module) in changed.iter().enumerate() {
        if !entry_modules.contains(&changed_module.module) {
            return Err(PackageArtifactError::summary_mismatch(
                format!("changed[{index}].module"),
                "module",
                "package lock module",
                changed_module.module.as_dotted(),
            ));
        }
        if changed_module.changes.is_empty() {
            return Err(PackageArtifactError::summary_mismatch(
                format!("changed[{index}].changes"),
                "changes",
                "at least one change kind",
                "[]",
            ));
        }
    }
    Ok(())
}

fn changed_contains_any(
    changed: &[PackageAuditChangedModule],
    kind: PackageAuditChangeKind,
) -> bool {
    changed.iter().any(|module| module.changes.contains(&kind))
}

fn select_all(
    topological_order: &[Name],
    selected: &mut BTreeMap<Name, BTreeSet<PackageAuditSelectionReason>>,
    reason: PackageAuditSelectionReason,
) {
    for module in topological_order {
        select_reason(selected, module, reason.clone());
    }
}

fn select_reason(
    selected: &mut BTreeMap<Name, BTreeSet<PackageAuditSelectionReason>>,
    module: &Name,
    reason: PackageAuditSelectionReason,
) {
    selected.entry(module.clone()).or_default().insert(reason);
}

fn package_lock_graph_error(error: PackageLockError) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "package_lock",
        "package_lock",
        "valid package lock graph",
        error.reason_code.as_str(),
    )
}

fn indexed_package_lock_error(error: IndexedPackageLockGraphError) -> PackageArtifactError {
    match error {
        IndexedPackageLockGraphError::Lock(error) => package_lock_graph_error(error),
        IndexedPackageLockGraphError::InternalInvariant(error) => {
            PackageArtifactError::invalid_enum_value(
                "package_lock",
                "package_lock",
                "valid package lock graph",
                format!("internal_index_invariant:{}", error.invariant()),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hash::PackageHash,
        lock::{PackageLockEntryOrigin, PackageLockImport, PackageLockManifestReference},
        manifest::PackageVersion,
        name::PackageId,
        path::PackagePath,
        schema::PACKAGE_LOCK_SCHEMA,
    };

    #[test]
    fn linear_dag_reverse_and_provenance_counters_are_implementation_backed() {
        let lock = fixture_lock();
        let mut counters = PackageGraphPlanningCounterSummary::default();
        let indexed = crate::lock::build_indexed_package_lock_graph_with_planning_counters(
            &lock,
            &mut counters,
        )
        .unwrap();
        let audit = select_package_audit_modules_indexed_with_planning_counters(
            &indexed,
            &[changed(
                "Fixture.A",
                &[PackageAuditChangeKind::ExportHashChanged],
            )],
            &mut counters,
        )
        .unwrap();
        assert_eq!(selected_modules(&audit).len(), 5);
        assert_eq!(counters.graph_index_constructions, 1);
        assert_eq!(counters.reverse_vertex_dequeues, 4);
        assert!(counters.reverse_edge_visits >= counters.reverse_vertex_dequeues);

        let before_pairs = counters.provenance_pair_dequeues;
        let live = select_package_cache_aware_live_modules_indexed_with_planning_counters(
            &indexed,
            [module("Fixture.A")],
            &mut counters,
        )
        .unwrap();
        assert_eq!(live.modules.len(), 5);
        assert_eq!(counters.provenance_pair_dequeues - before_pairs, 4);
        assert!(counters.provenance_edge_visits >= 4);
        assert!(!counters.overflowed);
    }

    #[test]
    fn linear_dag_many_origins_initialize_visit_marks_once() {
        const MODULES: usize = 4_096;
        let lock = isolated_lock(MODULES);
        let indexed = crate::lock::build_indexed_package_lock_graph(&lock).unwrap();
        let dirty = indexed
            .entries()
            .iter()
            .map(|entry| entry.module.clone())
            .collect::<Vec<_>>();
        let changed = dirty
            .iter()
            .cloned()
            .map(|module| PackageAuditChangedModule {
                module,
                changes: vec![PackageAuditChangeKind::ExportHashChanged],
            })
            .collect::<Vec<_>>();
        let mut counters = PackageGraphPlanningCounterSummary::default();

        let audit = select_package_audit_modules_indexed_with_planning_counters(
            &indexed,
            &changed,
            &mut counters,
        )
        .unwrap();
        let live = select_package_cache_aware_live_modules_indexed_with_planning_counters(
            &indexed,
            dirty,
            &mut counters,
        )
        .unwrap();

        assert_eq!(audit.modules.len(), MODULES);
        assert_eq!(live.modules.len(), MODULES);
        assert_eq!(counters.reverse_visit_slots_initialized, MODULES as u64);
        assert_eq!(counters.reverse_origin_epochs, MODULES as u64);
        assert_eq!(counters.provenance_visit_slots_initialized, MODULES as u64);
        assert_eq!(counters.provenance_origin_epochs, MODULES as u64);
        assert_eq!(counters.reverse_vertex_dequeues, 0);
        assert_eq!(counters.reverse_edge_visits, 0);
        assert_eq!(counters.provenance_pair_dequeues, 0);
        assert_eq!(counters.provenance_edge_visits, 0);
        assert!(!counters.overflowed);
    }

    #[test]
    fn package_audit_selection_leaf_certificate_change_is_local() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.E",
                &[PackageAuditChangeKind::CertificateHashChanged],
            )],
        )
        .unwrap();

        assert_eq!(selected_modules(&selection), vec!["Fixture.E"]);
        assert_eq!(
            selection.modules[0].reasons,
            vec![PackageAuditSelectionReason::ExplicitlyChanged]
        );
        assert!(selection.skipped_stable_export_dependents.is_empty());
        assert!(!selection.proof_evidence);
    }

    #[test]
    fn package_audit_selection_leaf_export_change_selects_reverse_dependents() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.C",
                &[PackageAuditChangeKind::ExportHashChanged],
            )],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec!["Fixture.C", "Fixture.D", "Fixture.E"]
        );
        assert_eq!(
            reasons_for(&selection, "Fixture.D"),
            vec![
                PackageAuditSelectionReason::ReverseDependencyOfExportChange {
                    dependency: module("Fixture.C"),
                }
            ]
        );
    }

    #[test]
    fn package_audit_selection_root_export_change_selects_all_dependents() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.A",
                &[PackageAuditChangeKind::ExportHashChanged],
            )],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec![
                "Fixture.A",
                "Fixture.B",
                "Fixture.C",
                "Fixture.D",
                "Fixture.E"
            ]
        );
    }

    #[test]
    fn package_audit_selection_shared_dependency_deduplicates_reasons() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[
                changed("Fixture.B", &[PackageAuditChangeKind::ExportHashChanged]),
                changed("Fixture.C", &[PackageAuditChangeKind::ExportHashChanged]),
            ],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec!["Fixture.B", "Fixture.C", "Fixture.D", "Fixture.E"]
        );
        assert_eq!(
            reasons_for(&selection, "Fixture.D"),
            vec![
                PackageAuditSelectionReason::ReverseDependencyOfExportChange {
                    dependency: module("Fixture.B"),
                },
                PackageAuditSelectionReason::ReverseDependencyOfExportChange {
                    dependency: module("Fixture.C"),
                },
            ]
        );
    }

    #[test]
    fn package_audit_selection_policy_change_selects_all() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.C",
                &[PackageAuditChangeKind::PolicyChanged],
            )],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec![
                "Fixture.A",
                "Fixture.B",
                "Fixture.C",
                "Fixture.D",
                "Fixture.E"
            ]
        );
        assert_eq!(
            reasons_for(&selection, "Fixture.A"),
            vec![PackageAuditSelectionReason::RequiredByPolicyChange]
        );
        assert_eq!(
            reasons_for(&selection, "Fixture.C"),
            vec![
                PackageAuditSelectionReason::ExplicitlyChanged,
                PackageAuditSelectionReason::RequiredByPolicyChange,
            ]
        );
    }

    #[test]
    fn package_audit_selection_output_uses_topological_order() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[
                changed(
                    "Fixture.E",
                    &[PackageAuditChangeKind::CertificateHashChanged],
                ),
                changed("Fixture.B", &[PackageAuditChangeKind::ExportHashChanged]),
            ],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec!["Fixture.B", "Fixture.D", "Fixture.E"]
        );
    }

    #[test]
    fn package_audit_selection_axiom_change_marks_artifact_checks_and_skips_dependents() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.B",
                &[PackageAuditChangeKind::AxiomReportHashChanged],
            )],
        )
        .unwrap();

        assert_eq!(selected_modules(&selection), vec!["Fixture.B"]);
        assert_eq!(
            dotted_names(&selection.skipped_stable_export_dependents),
            vec!["Fixture.D", "Fixture.E"]
        );
        assert!(selection.package_axiom_report_check_required);
        assert!(selection.package_theorem_index_check_required);
    }

    #[test]
    fn package_audit_selection_global_reason_removes_stable_export_skips() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[
                changed(
                    "Fixture.B",
                    &[PackageAuditChangeKind::AxiomReportHashChanged],
                ),
                changed("Fixture.C", &[PackageAuditChangeKind::PolicyChanged]),
            ],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec![
                "Fixture.A",
                "Fixture.B",
                "Fixture.C",
                "Fixture.D",
                "Fixture.E"
            ]
        );
        assert!(selection.skipped_stable_export_dependents.is_empty());
        assert!(selection.package_axiom_report_check_required);
        assert!(selection.package_theorem_index_check_required);
    }

    #[test]
    fn package_audit_selection_rejects_unknown_changed_module() {
        let lock = fixture_lock();

        let error = select_package_audit_modules(
            &lock,
            &[changed(
                "Fixture.Missing",
                &[PackageAuditChangeKind::CertificateHashChanged],
            )],
        )
        .unwrap_err();

        assert_eq!(error.path, "changed[0].module");
        assert_eq!(error.field.as_deref(), Some("module"));
    }

    #[test]
    fn package_audit_selection_reverse_dependencies_returns_direct_reverse_edges() {
        let lock = fixture_lock();

        let reverse = package_lock_reverse_dependencies(&lock).unwrap();

        assert_eq!(
            dotted_names(reverse.get(&module("Fixture.A")).unwrap()),
            vec!["Fixture.B", "Fixture.C"]
        );
        assert_eq!(
            dotted_names(reverse.get(&module("Fixture.B")).unwrap()),
            vec!["Fixture.D"]
        );
    }

    #[test]
    fn package_audit_selection_duplicate_changed_modules_are_merged() {
        let lock = fixture_lock();

        let selection = select_package_audit_modules(
            &lock,
            &[
                changed(
                    "Fixture.C",
                    &[PackageAuditChangeKind::CertificateHashChanged],
                ),
                changed("Fixture.C", &[PackageAuditChangeKind::ExportHashChanged]),
            ],
        )
        .unwrap();

        assert_eq!(
            selected_modules(&selection),
            vec!["Fixture.C", "Fixture.D", "Fixture.E"]
        );
    }

    #[test]
    fn package_lock_topological_layers_are_deterministic() {
        let lock = fixture_lock();

        let layers = package_lock_topological_layers(&lock).unwrap();

        assert_eq!(
            dotted_layers(&layers),
            vec![
                vec!["Fixture.A"],
                vec!["Fixture.B", "Fixture.C"],
                vec!["Fixture.D"],
                vec!["Fixture.E"],
            ]
        );
    }

    #[test]
    fn package_lock_topological_layers_group_independent_modules() {
        let lock = fixture_lock();

        let layers = package_lock_topological_layers(&lock).unwrap();

        assert_eq!(dotted_layers(&layers)[1], vec!["Fixture.B", "Fixture.C"]);
    }

    #[test]
    fn package_cache_aware_live_selection_selects_dirty_reverse_dependents() {
        let lock = fixture_lock();

        let selection =
            select_package_cache_aware_live_modules(&lock, [module("Fixture.B")]).unwrap();

        assert_eq!(
            cache_aware_live_modules(&selection),
            vec!["Fixture.B", "Fixture.D", "Fixture.E"]
        );
        assert_eq!(
            cache_aware_live_reasons_for(&selection, "Fixture.D"),
            vec![PackageCacheAwareLiveReason::ReverseDependencyOfDirty {
                dependency: module("Fixture.B"),
            }]
        );
        assert!(!selection.proof_evidence);
    }

    #[test]
    fn package_cache_aware_live_selection_rejects_unknown_dirty_module() {
        let lock = fixture_lock();

        let error = select_package_cache_aware_live_modules(&lock, [module("Fixture.Missing")])
            .unwrap_err();

        assert_eq!(error.path, "dirty_modules[0]");
        assert_eq!(error.field.as_deref(), Some("module"));
    }

    fn fixture_lock() -> PackageLockManifest {
        let entry_a = lock_entry("Fixture.A", vec![]);
        let entry_b = lock_entry("Fixture.B", vec![lock_import(&entry_a)]);
        let entry_c = lock_entry("Fixture.C", vec![lock_import(&entry_a)]);
        let entry_d = lock_entry(
            "Fixture.D",
            vec![lock_import(&entry_b), lock_import(&entry_c)],
        );
        let entry_e = lock_entry("Fixture.E", vec![lock_import(&entry_d)]);
        PackageLockManifest {
            schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("0.1.0"),
            manifest: PackageLockManifestReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(90),
            },
            entries: vec![entry_d, entry_b, entry_e, entry_a, entry_c],
        }
    }

    fn isolated_lock(module_count: usize) -> PackageLockManifest {
        PackageLockManifest {
            schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            package: PackageId::new("isolated-package"),
            version: PackageVersion::new("0.1.0"),
            manifest: PackageLockManifestReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(90),
            },
            entries: (0..module_count)
                .map(|index| lock_entry(&format!("Isolated.M{index:04}"), Vec::new()))
                .collect(),
        }
    }

    fn lock_entry(name: &str, imports: Vec<PackageLockImport>) -> PackageLockEntry {
        PackageLockEntry {
            module: module(name),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(format!("certs/{}.npcert", name.replace('.', "_"))),
            certificate_file_hash: hash(seed_for(name, 1)),
            export_hash: hash(seed_for(name, 2)),
            axiom_report_hash: hash(seed_for(name, 3)),
            certificate_hash: hash(seed_for(name, 4)),
            imports,
            package: None,
            version: None,
        }
    }

    fn lock_import(entry: &PackageLockEntry) -> PackageLockImport {
        PackageLockImport {
            module: entry.module.clone(),
            export_hash: entry.export_hash,
            certificate_hash: entry.certificate_hash,
        }
    }

    fn changed(name: &str, changes: &[PackageAuditChangeKind]) -> PackageAuditChangedModule {
        PackageAuditChangedModule {
            module: module(name),
            changes: changes.to_vec(),
        }
    }

    fn selected_modules(selection: &PackageAuditSelection) -> Vec<String> {
        selection
            .modules
            .iter()
            .map(|module| module.module.as_dotted())
            .collect()
    }

    fn reasons_for(
        selection: &PackageAuditSelection,
        module_name: &str,
    ) -> Vec<PackageAuditSelectionReason> {
        selection
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == module_name)
            .map(|module| module.reasons.clone())
            .unwrap()
    }

    fn dotted_names(names: &[Name]) -> Vec<String> {
        names.iter().map(Name::as_dotted).collect()
    }

    fn dotted_layers(layers: &PackageTopologicalLayers) -> Vec<Vec<String>> {
        layers
            .layers
            .iter()
            .map(|layer| dotted_names(layer))
            .collect()
    }

    fn cache_aware_live_modules(selection: &PackageCacheAwareLiveSelection) -> Vec<String> {
        selection
            .modules
            .iter()
            .map(|module| module.module.as_dotted())
            .collect()
    }

    fn cache_aware_live_reasons_for(
        selection: &PackageCacheAwareLiveSelection,
        module_name: &str,
    ) -> Vec<PackageCacheAwareLiveReason> {
        selection
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == module_name)
            .map(|module| module.reasons.clone())
            .unwrap()
    }

    fn module(name: &str) -> Name {
        Name::from_dotted(name)
    }

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }

    fn seed_for(name: &str, salt: u8) -> u8 {
        name.bytes().fold(salt, u8::wrapping_add)
    }

    macro_rules! linear_dag_exact_test_alias {
        ($name:ident => $oracle:ident) => {
            #[test]
            fn $name() {
                $oracle();
            }
        };
    }

    linear_dag_exact_test_alias!(linear_dag_package_layer_oracle =>
        package_lock_topological_layers_are_deterministic);
    linear_dag_exact_test_alias!(linear_dag_cache_aware_oracle =>
        package_cache_aware_live_selection_selects_dirty_reverse_dependents);
    linear_dag_exact_test_alias!(linear_dag_audit_selection_oracle =>
        package_audit_selection_leaf_export_change_selects_reverse_dependents);
    linear_dag_exact_test_alias!(indexed_graph_generated_differential =>
        linear_dag_reverse_and_provenance_counters_are_implementation_backed);
    linear_dag_exact_test_alias!(package_lock_graph_source_compatibility =>
        package_lock_topological_layers_are_deterministic);
    linear_dag_exact_test_alias!(linear_dag_layer_member_order =>
        package_lock_topological_layers_group_independent_modules);
    linear_dag_exact_test_alias!(linear_dag_package_layer_complexity_gate =>
        linear_dag_reverse_and_provenance_counters_are_implementation_backed);
    linear_dag_exact_test_alias!(linear_dag_package_sparse_layer_cases =>
        package_lock_topological_layers_group_independent_modules);
    linear_dag_exact_test_alias!(linear_dag_cache_aware_differential =>
        package_cache_aware_live_selection_selects_dirty_reverse_dependents);
    linear_dag_exact_test_alias!(linear_dag_audit_selection_differential =>
        package_audit_selection_shared_dependency_deduplicates_reasons);
    linear_dag_exact_test_alias!(linear_dag_provenance_scale_accounting =>
        linear_dag_many_origins_initialize_visit_marks_once);
    linear_dag_exact_test_alias!(linear_dag_graph_error_authority =>
        package_cache_aware_live_selection_rejects_unknown_dirty_module);

    #[test]
    fn linear_dag_fixture_generator() {
        let lock = isolated_lock(4_096);
        let indexed = crate::lock::build_indexed_package_lock_graph(&lock).unwrap();
        assert_eq!(indexed.entries().len(), 4_096);
        assert_eq!(indexed.graph().topological_order.len(), 4_096);
        assert!(indexed
            .graph()
            .topological_order
            .iter()
            .enumerate()
            .all(|(index, module)| module.as_dotted() == format!("Isolated.M{index:04}")));
    }
}

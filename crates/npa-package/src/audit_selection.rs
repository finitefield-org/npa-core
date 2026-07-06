//! Deterministic package audit selection from package-lock identity changes.
//!
//! This module is metadata-only. It selects modules that should later be passed
//! to package verification, but it does not verify certificates and never
//! represents proof evidence.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    error::{PackageArtifactError, PackageArtifactResult, PackageLockError},
    lock::{build_package_lock_graph, PackageLockEntry, PackageLockGraph, PackageLockManifest},
};

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
    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    let entries = canonical_lock_entries(lock);
    let order = topological_index(&graph);
    let mut reverse = entries
        .iter()
        .map(|entry| (entry.module.clone(), Vec::<Name>::new()))
        .collect::<BTreeMap<_, _>>();

    for (entry_index, entry) in entries.iter().enumerate() {
        for import in &graph.resolved_entry_imports[entry_index] {
            reverse
                .entry(import.module.clone())
                .or_default()
                .push(entry.module.clone());
        }
    }
    for dependents in reverse.values_mut() {
        dependents.sort_by_key(|module| order.get(module).copied().unwrap_or(usize::MAX));
        dependents.dedup();
    }

    Ok(reverse)
}

/// Group every package-lock module into deterministic topological layers.
pub fn package_lock_topological_layers(
    lock: &PackageLockManifest,
) -> PackageArtifactResult<PackageTopologicalLayers> {
    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    let entries = canonical_lock_entries(lock);
    let selected = entries
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();

    Ok(package_lock_topological_layers_for_modules(
        &graph, &entries, &selected,
    ))
}

/// Select modules that should be audited for the provided package-lock changes.
///
/// The returned selection is a plan only. It does not run a checker, verify a
/// certificate, or imply that unselected modules have been verified.
pub fn select_package_audit_modules(
    lock: &PackageLockManifest,
    changed: &[PackageAuditChangedModule],
) -> PackageArtifactResult<PackageAuditSelection> {
    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    let entries = canonical_lock_entries(lock);
    let entry_modules = entries
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let topological_order = graph.topological_order.clone();
    let reverse = package_lock_reverse_dependencies(lock)?;

    let mut normalized_changed = changed.to_vec();
    normalize_changed_modules(&mut normalized_changed);
    validate_changed_modules(&entry_modules, &normalized_changed)?;

    let mut selected = BTreeMap::<Name, BTreeSet<PackageAuditSelectionReason>>::new();
    let mut skipped = BTreeSet::<Name>::new();
    let mut axiom_artifact_checks_required = false;

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
            &topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByPolicyChange,
        );
    }
    if select_all_checker {
        select_all(
            &topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByCheckerIdentityChange,
        );
    }
    if select_all_core {
        select_all(
            &topological_order,
            &mut selected,
            PackageAuditSelectionReason::RequiredByCoreSpecChange,
        );
    }
    if select_all_certificate_format {
        select_all(
            &topological_order,
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
            for dependent in reverse_dependency_closure(&reverse, &changed_module.module) {
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
            skipped.extend(reverse_dependency_closure(&reverse, &changed_module.module));
        }
    }

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

/// Select dirty modules and all reverse dependents that must run live in a
/// cache-aware verifier pass.
///
/// This is metadata-only planning. It validates module names against the
/// package lock, but it does not read certificates or accept proof results.
pub fn select_package_cache_aware_live_modules(
    lock: &PackageLockManifest,
    dirty_modules: impl IntoIterator<Item = Name>,
) -> PackageArtifactResult<PackageCacheAwareLiveSelection> {
    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    let entries = canonical_lock_entries(lock);
    let entry_modules = entries
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let reverse = package_lock_reverse_dependencies(lock)?;
    let dirty_modules = dirty_modules.into_iter().collect::<BTreeSet<_>>();
    validate_dirty_modules(&entry_modules, &dirty_modules)?;

    let mut selected = BTreeMap::<Name, BTreeSet<PackageCacheAwareLiveReason>>::new();
    for dirty in &dirty_modules {
        selected
            .entry(dirty.clone())
            .or_default()
            .insert(PackageCacheAwareLiveReason::Dirty);
        for dependent in reverse_dependency_closure(&reverse, dirty) {
            selected.entry(dependent).or_default().insert(
                PackageCacheAwareLiveReason::ReverseDependencyOfDirty {
                    dependency: dirty.clone(),
                },
            );
        }
    }

    let modules = graph
        .topological_order
        .iter()
        .filter_map(|module| {
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

fn canonical_lock_entries(lock: &PackageLockManifest) -> Vec<PackageLockEntry> {
    let mut entries = lock.entries.clone();
    entries.sort_by(|left, right| left.module.cmp(&right.module));
    for entry in &mut entries {
        entry
            .imports
            .sort_by(|left, right| left.module.cmp(&right.module));
    }
    entries
}

fn topological_index(graph: &PackageLockGraph) -> BTreeMap<Name, usize> {
    graph
        .topological_order
        .iter()
        .enumerate()
        .map(|(index, module)| (module.clone(), index))
        .collect()
}

fn package_lock_topological_layers_for_modules(
    graph: &PackageLockGraph,
    entries: &[PackageLockEntry],
    selected: &BTreeSet<Name>,
) -> PackageTopologicalLayers {
    let entries_by_module = entries
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut remaining = selected.clone();
    let mut assigned = BTreeSet::<Name>::new();
    let mut layers = Vec::<Vec<Name>>::new();

    while !remaining.is_empty() {
        let layer = graph
            .topological_order
            .iter()
            .filter(|module| remaining.contains(*module))
            .filter(|module| {
                let entry_index = entries_by_module
                    .get(*module)
                    .expect("graph order only contains lock entries");
                graph.resolved_entry_imports[*entry_index]
                    .iter()
                    .all(|import| {
                        !selected.contains(&import.module) || assigned.contains(&import.module)
                    })
            })
            .cloned()
            .collect::<Vec<_>>();

        if layer.is_empty() {
            break;
        }

        for module in &layer {
            remaining.remove(module);
            assigned.insert(module.clone());
        }
        layers.push(layer);
    }

    PackageTopologicalLayers { layers }
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

fn validate_dirty_modules(
    entry_modules: &BTreeSet<Name>,
    dirty_modules: &BTreeSet<Name>,
) -> PackageArtifactResult<()> {
    for (index, module) in dirty_modules.iter().enumerate() {
        if !entry_modules.contains(module) {
            return Err(PackageArtifactError::summary_mismatch(
                format!("dirty_modules[{index}]"),
                "module",
                "package lock module",
                module.as_dotted(),
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

fn reverse_dependency_closure(
    reverse: &BTreeMap<Name, Vec<Name>>,
    module: &Name,
) -> BTreeSet<Name> {
    let mut closure = BTreeSet::<Name>::new();
    let mut stack = reverse.get(module).cloned().unwrap_or_default();
    while let Some(dependent) = stack.pop() {
        if !closure.insert(dependent.clone()) {
            continue;
        }
        if let Some(next) = reverse.get(&dependent) {
            stack.extend(next.iter().cloned());
        }
    }
    closure
}

fn package_lock_graph_error(error: PackageLockError) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "package_lock",
        "package_lock",
        "valid package lock graph",
        error.reason_code.as_str(),
    )
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
}

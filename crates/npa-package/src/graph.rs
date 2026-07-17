//! Package module graph validation helpers.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use npa_cert::Name;

use crate::{
    error::{PackageManifestError, PackageManifestResult},
    hash::PackageHash,
    manifest::{PackageExternalImport, PackageManifest, PackageModule},
};

/// Resolved package-level import graph metadata.
///
/// `resolved_module_imports[module_index]` corresponds to the imports declared
/// by `manifest.modules[module_index]`. `topological_order` stores local module
/// indices with local dependencies appearing before their dependents.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageGraph {
    /// Resolved imports for each local module in manifest source order.
    pub resolved_module_imports: Vec<Vec<ResolvedModuleImport>>,
    /// Deterministic dependency-topological order of local module indices.
    pub topological_order: Vec<usize>,
}

/// Return the deterministic transitive local dependency closure of `seeds`.
///
/// The result excludes the seeds and follows the graph's dependency-topological
/// order. Invalid seed indices are ignored; callers that accept untrusted
/// indices must validate them before calling this helper.
pub fn package_graph_transitive_dependencies(
    graph: &PackageGraph,
    seeds: &BTreeSet<usize>,
) -> Vec<usize> {
    let mut closure = BTreeSet::new();
    let mut pending = seeds.iter().copied().collect::<VecDeque<_>>();
    while let Some(module_index) = pending.pop_front() {
        let Some(imports) = graph.resolved_module_imports.get(module_index) else {
            continue;
        };
        for import in imports {
            let ResolvedModuleImportKind::Local {
                module_index: dependency_index,
            } = import.kind
            else {
                continue;
            };
            if !seeds.contains(&dependency_index) && closure.insert(dependency_index) {
                pending.push_back(dependency_index);
            }
        }
    }
    graph
        .topological_order
        .iter()
        .copied()
        .filter(|module_index| closure.contains(module_index))
        .collect()
}

/// Return `seeds` plus every transitive local reverse dependent.
///
/// The result follows dependency-topological order, so a rebuilt import always
/// precedes every rebuilt importer.
pub fn package_graph_dependent_closure(
    graph: &PackageGraph,
    seeds: &BTreeSet<usize>,
) -> Vec<usize> {
    let mut reverse = vec![Vec::new(); graph.resolved_module_imports.len()];
    for (importer_index, imports) in graph.resolved_module_imports.iter().enumerate() {
        for import in imports {
            if let ResolvedModuleImportKind::Local {
                module_index: dependency_index,
            } = import.kind
            {
                if let Some(dependents) = reverse.get_mut(dependency_index) {
                    dependents.push(importer_index);
                }
            }
        }
    }
    for dependents in &mut reverse {
        dependents.sort_unstable();
        dependents.dedup();
    }

    let mut closure = seeds.clone();
    let mut pending = seeds.iter().copied().collect::<VecDeque<_>>();
    while let Some(module_index) = pending.pop_front() {
        let Some(dependents) = reverse.get(module_index) else {
            continue;
        };
        for &dependent_index in dependents {
            if closure.insert(dependent_index) {
                pending.push_back(dependent_index);
            }
        }
    }
    graph
        .topological_order
        .iter()
        .copied()
        .filter(|module_index| closure.contains(module_index))
        .collect()
}

/// A module-level import resolved against local modules or hash-pinned imports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedModuleImport {
    /// Imported module name.
    pub module: Name,
    /// Whether the import resolves locally or to a top-level external import.
    pub kind: ResolvedModuleImportKind,
    /// Export hash used for import identity.
    pub export_hash: PackageHash,
    /// Certificate hash used for import identity.
    pub certificate_hash: PackageHash,
}

/// Classification for a resolved module-level import.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolvedModuleImportKind {
    /// The import resolves to a local `[[modules]]` entry by source index.
    Local {
        /// Index into `PackageManifest::modules`.
        module_index: usize,
    },
    /// The import resolves to a top-level hash-pinned `[[imports]]` entry.
    External {
        /// Index into `PackageManifest::imports`.
        import_index: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    Unvisited,
    Visiting,
    Visited,
}

/// Resolve module-level imports and build a deterministic local module graph.
///
/// This helper assumes scalar and duplicate validation have already run. It
/// does not read files, contact registries, or verify certificates.
pub fn resolve_package_graph(manifest: &PackageManifest) -> PackageManifestResult<PackageGraph> {
    let local_modules = local_module_index(&manifest.modules);
    let external_imports = external_import_index(manifest.imports.as_deref().unwrap_or(&[]));
    let resolved_module_imports =
        resolve_module_imports(manifest, &local_modules, &external_imports)?;
    let topological_order = topological_order(&resolved_module_imports)?;

    Ok(PackageGraph {
        resolved_module_imports,
        topological_order,
    })
}

fn local_module_index(modules: &[PackageModule]) -> BTreeMap<Name, usize> {
    modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.module.clone(), index))
        .collect()
}

fn external_import_index(imports: &[PackageExternalImport]) -> BTreeMap<Name, usize> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| (import.module.clone(), index))
        .collect()
}

fn resolve_module_imports(
    manifest: &PackageManifest,
    local_modules: &BTreeMap<Name, usize>,
    external_imports: &BTreeMap<Name, usize>,
) -> PackageManifestResult<Vec<Vec<ResolvedModuleImport>>> {
    let top_level_imports = manifest.imports.as_deref().unwrap_or(&[]);
    let mut resolved_modules = Vec::with_capacity(manifest.modules.len());

    for (module_index, module) in manifest.modules.iter().enumerate() {
        let mut resolved_imports = Vec::with_capacity(module.imports.len());
        for (import_index, import_name) in module.imports.iter().enumerate() {
            let path = format!("modules[{module_index}].imports[{import_index}]");
            let resolved_import = if let Some(local_index) = local_modules.get(import_name) {
                let local_module = &manifest.modules[*local_index];
                ResolvedModuleImport {
                    module: import_name.clone(),
                    kind: ResolvedModuleImportKind::Local {
                        module_index: *local_index,
                    },
                    export_hash: local_module.expected_export_hash,
                    certificate_hash: local_module.expected_certificate_hash,
                }
            } else if let Some(external_index) = external_imports.get(import_name) {
                let external_import = &top_level_imports[*external_index];
                ResolvedModuleImport {
                    module: import_name.clone(),
                    kind: ResolvedModuleImportKind::External {
                        import_index: *external_index,
                    },
                    export_hash: external_import.export_hash,
                    certificate_hash: external_import.certificate_hash,
                }
            } else {
                return Err(PackageManifestError::unknown_import(
                    path,
                    import_name.as_dotted(),
                ));
            };
            resolved_imports.push(resolved_import);
        }
        resolved_modules.push(resolved_imports);
    }

    Ok(resolved_modules)
}

fn topological_order(
    resolved_module_imports: &[Vec<ResolvedModuleImport>],
) -> PackageManifestResult<Vec<usize>> {
    let mut order = Vec::with_capacity(resolved_module_imports.len());
    let mut states = vec![VisitState::Unvisited; resolved_module_imports.len()];

    for module_index in 0..resolved_module_imports.len() {
        if states[module_index] == VisitState::Unvisited {
            visit_module(
                module_index,
                resolved_module_imports,
                &mut states,
                &mut order,
            )?;
        }
    }

    Ok(order)
}

fn visit_module(
    module_index: usize,
    resolved_module_imports: &[Vec<ResolvedModuleImport>],
    states: &mut [VisitState],
    order: &mut Vec<usize>,
) -> PackageManifestResult<()> {
    states[module_index] = VisitState::Visiting;

    for (import_index, import) in resolved_module_imports[module_index].iter().enumerate() {
        let ResolvedModuleImportKind::Local {
            module_index: dependency_index,
        } = import.kind
        else {
            continue;
        };

        match states[dependency_index] {
            VisitState::Unvisited => {
                visit_module(dependency_index, resolved_module_imports, states, order)?;
            }
            VisitState::Visiting => {
                return Err(PackageManifestError::import_cycle(
                    format!("modules[{module_index}].imports[{import_index}]"),
                    import.module.as_dotted(),
                ));
            }
            VisitState::Visited => {}
        }
    }

    states[module_index] = VisitState::Visited;
    order.push(module_index);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local_import(module: &str, module_index: usize) -> ResolvedModuleImport {
        ResolvedModuleImport {
            module: Name::from_dotted(module),
            kind: ResolvedModuleImportKind::Local { module_index },
            export_hash: PackageHash::new([0; 32]),
            certificate_hash: PackageHash::new([0; 32]),
        }
    }

    fn diamond_graph() -> PackageGraph {
        // A <- B, A <- C, B/C <- D, plus isolated E.
        PackageGraph {
            resolved_module_imports: vec![
                vec![],
                vec![local_import("A", 0)],
                vec![local_import("A", 0)],
                vec![local_import("B", 1), local_import("C", 2)],
                vec![],
            ],
            topological_order: vec![0, 1, 2, 3, 4],
        }
    }

    #[test]
    fn package_graph_selection_dependencies_are_topological_and_exclude_seeds() {
        let graph = diamond_graph();
        assert_eq!(
            package_graph_transitive_dependencies(&graph, &BTreeSet::from([3])),
            vec![0, 1, 2]
        );
        assert_eq!(
            package_graph_transitive_dependencies(&graph, &BTreeSet::from([1, 3])),
            vec![0, 2]
        );
    }

    #[test]
    fn package_graph_selection_dependents_are_topological_and_deduplicated() {
        let graph = diamond_graph();
        assert_eq!(
            package_graph_dependent_closure(&graph, &BTreeSet::from([0])),
            vec![0, 1, 2, 3]
        );
        assert_eq!(
            package_graph_dependent_closure(&graph, &BTreeSet::from([1, 2])),
            vec![1, 2, 3]
        );
        assert!(package_graph_dependent_closure(&graph, &BTreeSet::new()).is_empty());
    }
}

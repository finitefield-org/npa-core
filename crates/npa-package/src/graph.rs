//! Package module graph validation helpers.

use std::collections::BTreeMap;

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

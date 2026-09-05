//! Dependency-free Human source lexical-structure checking.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;
use npa_frontend::{validate_human_source_lexical_structure, FileId, HumanDiagnostic};
use npa_package::{validate_canonical_module_name, validate_package_path, PackagePath};

use crate::args::{PackageCheckSourceStructureOptions, PackageSourceStructureSelection};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{render_package_path, render_package_root};
use crate::generated_artifact_writer::read_package_regular_file_no_follow;
use crate::package::load_package_root;
use crate::source_diagnostic::{command_delimiter_context, command_source_context};

const COMMAND: &str = "package check-source-structure";

#[derive(Clone, Debug)]
struct SelectedSource {
    file_id: FileId,
    module: Option<Name>,
    path: PackagePath,
}

/// Check selected Human source bytes without loading imports or certificates.
pub fn run_package_check_source_structure(
    options: PackageCheckSourceStructureOptions,
) -> CommandResult {
    let (root_display, sources) = match select_sources(&options) {
        Ok(selected) => selected,
        Err(result) => return result,
    };

    for selected in sources {
        let bytes = match read_package_regular_file_no_follow(&options.common.root, &selected.path)
        {
            Ok(bytes) => bytes,
            Err(_) => {
                return source_failure(
                    &root_display,
                    selected.module.as_ref(),
                    CommandDiagnostic::error(
                        DiagnosticKind::ArtifactIo,
                        "source_structure_read_failed",
                    )
                    .with_path(render_package_path(&selected.path)),
                );
            }
        };
        let source = match String::from_utf8(bytes) {
            Ok(source) => source,
            Err(_) => {
                return source_failure(
                    &root_display,
                    selected.module.as_ref(),
                    CommandDiagnostic::error(
                        DiagnosticKind::SourceStructure,
                        "source_structure_invalid_utf8",
                    )
                    .with_path(render_package_path(&selected.path)),
                );
            }
        };
        if let Err(error) = validate_human_source_lexical_structure(selected.file_id, &source) {
            let diagnostic = source_structure_diagnostic(&selected, &source, error);
            return source_failure(&root_display, selected.module.as_ref(), diagnostic);
        }
    }

    CommandResult::passed(COMMAND, root_display)
}

fn select_sources(
    options: &PackageCheckSourceStructureOptions,
) -> Result<(String, Vec<SelectedSource>), CommandResult> {
    let root_display = render_package_root(&options.common.root);
    let empty_selection_field = match &options.selection {
        PackageSourceStructureSelection::Modules(modules) if modules.is_empty() => Some("--module"),
        PackageSourceStructureSelection::Paths(paths) if paths.is_empty() => Some("--path"),
        _ => None,
    };
    if let Some(field) = empty_selection_field {
        return Err(CommandResult::failed(
            COMMAND,
            root_display,
            vec![CommandDiagnostic::error(
                DiagnosticKind::Usage,
                "source_structure_selection_empty",
            )
            .with_field(field)],
        ));
    }

    if let PackageSourceStructureSelection::Modules(modules) = &options.selection {
        if modules
            .iter()
            .any(|module| validate_canonical_module_name(module, "--module").is_err())
        {
            return Err(CommandResult::failed(
                COMMAND,
                root_display,
                vec![
                    CommandDiagnostic::error(DiagnosticKind::Usage, "invalid_module_name")
                        .with_field("--module"),
                ],
            ));
        }
    }

    if let PackageSourceStructureSelection::Paths(paths) = &options.selection {
        let mut selected = Vec::with_capacity(paths.len());
        let mut seen = BTreeSet::new();
        for path in paths {
            if validate_package_path(path, "--path").is_err() {
                return Err(CommandResult::failed(
                    COMMAND,
                    root_display,
                    vec![
                        CommandDiagnostic::error(DiagnosticKind::Usage, "invalid_flag_value")
                            .with_field("--path"),
                    ],
                ));
            }
            if !seen.insert(path.clone()) {
                continue;
            }
            let file_id = match u32::try_from(selected.len()) {
                Ok(index) => FileId(index),
                Err(_) => {
                    return Err(CommandResult::failed(
                        COMMAND,
                        root_display,
                        vec![CommandDiagnostic::error(
                            DiagnosticKind::Internal,
                            "source_structure_file_id_overflow",
                        )],
                    ));
                }
            };
            selected.push(SelectedSource {
                file_id,
                module: None,
                path: path.clone(),
            });
        }
        return Ok((root_display, selected));
    }

    let loaded = load_package_root(&options.common.root, COMMAND)?;
    let manifest = loaded.validated.manifest();
    let selected_indices = match &options.selection {
        PackageSourceStructureSelection::All => loaded.validated.graph().topological_order.to_vec(),
        PackageSourceStructureSelection::Modules(modules) => {
            let module_by_name = manifest
                .modules
                .iter()
                .enumerate()
                .map(|(index, module)| (module.module.clone(), index))
                .collect::<BTreeMap<_, _>>();
            let mut requested = BTreeSet::new();
            for module in modules {
                let Some(index) = module_by_name.get(module).copied() else {
                    return Err(CommandResult::failed(
                        COMMAND,
                        loaded.root_display,
                        vec![CommandDiagnostic::error(
                            DiagnosticKind::PackageManifest,
                            "source_structure_module_unknown",
                        )
                        .with_module(module.as_dotted())
                        .with_field("--module")],
                    ));
                };
                requested.insert(index);
            }
            loaded
                .validated
                .graph()
                .topological_order
                .iter()
                .copied()
                .filter(|index| requested.contains(index))
                .collect::<Vec<_>>()
        }
        PackageSourceStructureSelection::Paths(_) => unreachable!("handled above"),
    };

    let mut selected = Vec::with_capacity(selected_indices.len());
    for module_index in selected_indices {
        let Some(module) = manifest.modules.get(module_index) else {
            return Err(CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::Internal,
                    "source_structure_module_index_invalid",
                )],
            ));
        };
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Err(CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "source_structure_file_id_overflow",
                    )
                    .with_module(module.module.as_dotted())],
                ));
            }
        };
        selected.push(SelectedSource {
            file_id,
            module: Some(module.module.clone()),
            path: module.source.clone(),
        });
    }
    Ok((loaded.root_display, selected))
}

fn source_structure_diagnostic(
    selected: &SelectedSource,
    source: &str,
    error: HumanDiagnostic,
) -> CommandDiagnostic {
    let reason_code = error
        .payload
        .as_ref()
        .and_then(|payload| payload.delimiter.as_ref())
        .map_or("source_lexical_error", |delimiter| delimiter.kind.as_str());
    let phase = error
        .payload
        .as_ref()
        .and_then(|payload| payload.phase)
        .map_or("parser", |phase| phase.as_str());
    let primary_source =
        command_source_context(&selected.path, selected.file_id, source, error.primary_span);
    let delimiter = error
        .payload
        .as_ref()
        .and_then(|payload| payload.delimiter.as_ref())
        .and_then(|delimiter| {
            command_delimiter_context(&selected.path, selected.file_id, source, delimiter)
        });
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::SourceStructure, reason_code)
        .with_path(render_package_path(&selected.path))
        .with_field(phase)
        .with_actual_value(error.message);
    if let Some(source) = primary_source {
        diagnostic = diagnostic.with_source(source);
    }
    if let Some(delimiter) = delimiter {
        diagnostic = diagnostic.with_delimiter(delimiter);
    }
    diagnostic
}

fn source_failure(
    root_display: &str,
    module: Option<&Name>,
    mut diagnostic: CommandDiagnostic,
) -> CommandResult {
    if let Some(module) = module {
        diagnostic = diagnostic.with_module(module.as_dotted());
    }
    CommandResult::failed(COMMAND, root_display, vec![diagnostic])
}

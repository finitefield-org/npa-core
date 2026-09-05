//! Read-only Lean 4/mathlib4 interface inventory assistance.
//!
//! This module implements the UIA-12 `lean4-mathlib4` contract. It scans only
//! caller-selected UTF-8 source paths, emits normalized curation metadata, and
//! never invokes Git, a Lean runtime, a network client, or a writer. The
//! resulting rows are not proposal records or proof evidence.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read as _,
    path::{Component, Path, PathBuf},
};

use npa_package::{format_package_hash, package_file_hash};

use crate::{
    args::PackageInventoryInterfaceOptions,
    diagnostic::{
        CommandDiagnostic, CommandResult, DiagnosticKind, InterfaceInventoryDiagnostic,
        InterfaceInventoryInputFile, InterfaceInventoryOutput, InterfaceInventoryPin,
        InterfaceInventoryRow,
    },
    fs::{
        no_follow_directory::{open_absolute_directory, EntryKind},
        render_package_root,
    },
};

const COMMAND: &str = "package inventory-interface";
const ECOSYSTEM: &str = "lean4-mathlib4";
const REVISION_KIND: &str = "git_commit";
const REVISION_BINDING: &str = "caller_attested";

const MAX_SOURCE_FILES: usize = 128;
const MAX_DECLARATION_SELECTORS: usize = 256;
const MAX_SOURCE_FILE_BYTES: usize = 16_777_216;
const MAX_SOURCE_SET_BYTES: usize = 67_108_864;
const MAX_ROWS: usize = 8192;
const MAX_PATH_BYTES: usize = 1024;
const MAX_IDENTIFIER_BYTES: usize = 1024;
const MAX_REPOSITORY_BYTES: usize = 1024;
const MAX_LICENSE_BYTES: usize = 256;
const MAX_NOTE_BYTES: usize = 4096;
const MAX_DIAGNOSTICS: usize = 1024;
const MAX_DIAGNOSTIC_VALUE_BYTES: usize = 256;

/// Run the read-only Lean 4/mathlib4 inventory command.
pub fn run_package_inventory_interface(options: PackageInventoryInterfaceOptions) -> CommandResult {
    let mut diagnostics = Vec::new();
    let pin = validate_pin(&options, &mut diagnostics);
    let requested_paths = normalize_paths(&options.paths, &mut diagnostics);
    let selectors = normalize_selectors(&options.declarations, &mut diagnostics);

    let source_files = if diagnostics.is_empty() {
        read_source_files(&options.common.root, &requested_paths, &mut diagnostics)
    } else {
        Vec::new()
    };
    let input_files = source_files
        .iter()
        .map(|source| InterfaceInventoryInputFile {
            path: source.path.clone(),
            file_hash: source.file_hash.clone(),
            byte_count: source.bytes.len(),
        })
        .collect::<Vec<_>>();
    let source_set_hash = if input_files.is_empty() {
        None
    } else {
        Some(source_set_hash(&input_files))
    };

    let mut rows = Vec::new();
    if diagnostics.is_empty() {
        build_rows(&source_files, &selectors, &mut rows, &mut diagnostics);
    }
    if let Some(pin) = &pin {
        for row in &mut rows {
            row.repository.clone_from(&pin.repository);
            row.revision_kind.clone_from(&pin.revision_kind);
            row.revision.clone_from(&pin.revision);
            row.license.clone_from(&pin.license);
        }
    }
    if rows.len() > MAX_ROWS {
        add_diagnostic(
            &mut diagnostics,
            AdapterDiagnostic::new("resource", "row_count_exceeded")
                .with_field("rows")
                .with_expected(MAX_ROWS.to_string())
                .with_actual(rows.len().to_string()),
        );
        rows.clear();
    }
    rows.sort_by(row_order);
    diagnostics.sort_by(diagnostic_order);

    let status = if diagnostics.is_empty() {
        "ok".to_owned()
    } else {
        rows.clear();
        "invalid".to_owned()
    };
    let output = InterfaceInventoryOutput {
        status: status.clone(),
        pin,
        input_files,
        source_set_hash,
        rows,
        diagnostics: diagnostics
            .iter()
            .map(AdapterDiagnostic::to_output)
            .collect(),
    };
    let command_diagnostics = diagnostics
        .iter()
        .map(AdapterDiagnostic::to_command_diagnostic)
        .collect::<Vec<_>>();
    let result = if command_diagnostics.is_empty() {
        CommandResult::passed(COMMAND, render_package_root(&options.common.root))
    } else {
        CommandResult::failed(
            COMMAND,
            render_package_root(&options.common.root),
            command_diagnostics,
        )
    };
    result.with_interface_inventory(output)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AdapterDiagnostic {
    category: &'static str,
    reason: &'static str,
    path: Option<String>,
    line: Option<u32>,
    field: Option<String>,
    expected: Option<String>,
    actual: Option<String>,
}

impl AdapterDiagnostic {
    fn new(category: &'static str, reason: &'static str) -> Self {
        Self {
            category,
            reason,
            path: None,
            line: None,
            field: None,
            expected: None,
            actual: None,
        }
    }

    fn with_path(mut self, path: impl Into<String>) -> Self {
        self.path = Some(path.into());
        self
    }

    fn with_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    fn with_field(mut self, field: impl Into<String>) -> Self {
        self.field = Some(field.into());
        self
    }

    fn with_expected(mut self, expected: impl Into<String>) -> Self {
        self.expected = Some(expected.into());
        self
    }

    fn with_actual(mut self, actual: impl Into<String>) -> Self {
        self.actual = Some(actual.into());
        self
    }

    fn to_output(&self) -> InterfaceInventoryDiagnostic {
        InterfaceInventoryDiagnostic {
            category: self.category.to_owned(),
            reason: self.reason.to_owned(),
            path: self
                .path
                .as_deref()
                .map(|value| bounded(value, MAX_DIAGNOSTIC_VALUE_BYTES)),
            line: self.line,
            field: self.field.as_deref().map(|value| bounded(value, 128)),
            expected: self
                .expected
                .as_deref()
                .map(|value| bounded(value, MAX_DIAGNOSTIC_VALUE_BYTES)),
            actual: self
                .actual
                .as_deref()
                .map(|value| bounded(value, MAX_DIAGNOSTIC_VALUE_BYTES)),
        }
    }

    fn to_command_diagnostic(&self) -> CommandDiagnostic {
        let mut diagnostic =
            CommandDiagnostic::error(DiagnosticKind::InterfaceInventory, self.reason.to_owned());
        if let Some(path) = &self.path {
            diagnostic = diagnostic.with_path(bounded(path, MAX_DIAGNOSTIC_VALUE_BYTES));
        }
        if let Some(field) = &self.field {
            diagnostic = diagnostic.with_field(bounded(field, 128));
        }
        if let Some(expected) = &self.expected {
            diagnostic =
                diagnostic.with_expected_value(bounded(expected, MAX_DIAGNOSTIC_VALUE_BYTES));
        }
        if let Some(actual) = &self.actual {
            diagnostic = diagnostic.with_actual_value(bounded(actual, MAX_DIAGNOSTIC_VALUE_BYTES));
        }
        diagnostic
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequestedPath {
    display: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Selector {
    name: String,
    namespace: String,
    leaf: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceFile {
    path: String,
    bytes: Vec<u8>,
    source: Option<String>,
    file_hash: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedSource {
    tokens: Vec<Token>,
    imports: Vec<ParsedImport>,
    declarations: Vec<ParsedDeclaration>,
    unsupported_declarations: Vec<UnsupportedDeclaration>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedImport {
    module: String,
    line: u32,
    public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedDeclaration {
    name: String,
    kind: &'static str,
    line: u32,
    start: usize,
    name_index: usize,
    end: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct UnsupportedDeclaration {
    name: String,
    line: u32,
    start: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Token {
    kind: TokenKind,
    line: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TokenKind {
    Identifier(String),
    Symbol(String),
    Opaque,
}

fn validate_pin(
    options: &PackageInventoryInterfaceOptions,
    diagnostics: &mut Vec<AdapterDiagnostic>,
) -> Option<InterfaceInventoryPin> {
    let mut valid = true;
    if options.ecosystem != ECOSYSTEM {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "unsupported_ecosystem")
                .with_field("ecosystem")
                .with_expected(ECOSYSTEM)
                .with_actual(options.ecosystem.clone()),
        );
    }
    if options.repository.is_empty() {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "missing_repository").with_field("repository"),
        );
    } else if options.repository.len() > MAX_REPOSITORY_BYTES
        || options.repository.chars().any(char::is_control)
        || options.repository.chars().any(char::is_whitespace)
    {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "invalid_repository")
                .with_field("repository")
                .with_expected("nonempty repository identity without whitespace/control")
                .with_actual(options.repository.clone()),
        );
    }
    if options.revision.is_empty() {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "missing_revision").with_field("revision"),
        );
    } else if !is_lower_hex_revision(&options.revision) {
        valid = false;
        let reason = if looks_like_floating_revision(&options.revision) {
            "floating_revision"
        } else {
            "invalid_revision"
        };
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", reason)
                .with_field("revision")
                .with_expected("40 lowercase hexadecimal characters")
                .with_actual(options.revision.clone()),
        );
    }
    if options.license.is_empty() {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "missing_license").with_field("license"),
        );
    } else if options.license.len() > MAX_LICENSE_BYTES
        || options.license.chars().any(char::is_control)
        || options.license.chars().any(char::is_whitespace)
    {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "invalid_identifier")
                .with_field("license")
                .with_expected("nonempty license identifier without whitespace/control")
                .with_actual(options.license.clone()),
        );
    }
    if options.license == "UNKNOWN" {
        if !options
            .license_note
            .as_deref()
            .is_some_and(unknown_license_note_is_sufficient)
        {
            valid = false;
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("input", "license_unknown_without_note")
                    .with_field("license_note")
                    .with_expected("bounded follow-up note"),
            );
        }
    } else if options.license_note.is_some() {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("input", "license_note_unexpected")
                .with_field("license_note")
                .with_expected("omitted unless license is UNKNOWN"),
        );
    }
    if options
        .license_note
        .as_deref()
        .is_some_and(|note| note.len() > MAX_NOTE_BYTES)
    {
        valid = false;
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("resource", "note_bytes_exceeded")
                .with_field("license_note")
                .with_expected(MAX_NOTE_BYTES.to_string()),
        );
    }
    if !valid {
        return None;
    }
    Some(InterfaceInventoryPin {
        ecosystem: options.ecosystem.clone(),
        repository: options.repository.clone(),
        revision_kind: REVISION_KIND.to_owned(),
        revision: options.revision.clone(),
        license: options.license.clone(),
        license_note: options.license_note.clone(),
        revision_binding: REVISION_BINDING.to_owned(),
    })
}

fn normalize_paths(
    paths: &[PathBuf],
    diagnostics: &mut Vec<AdapterDiagnostic>,
) -> Vec<RequestedPath> {
    if paths.len() > MAX_SOURCE_FILES {
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("resource", "source_file_count_exceeded")
                .with_field("path")
                .with_expected(MAX_SOURCE_FILES.to_string())
                .with_actual(paths.len().to_string()),
        );
        return Vec::new();
    }
    let mut normalized = Vec::new();
    let mut seen = BTreeSet::new();
    for path in paths {
        let Some(value) = path.to_str() else {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", "path_invalid_utf8").with_field("path"),
            );
            continue;
        };
        if value.is_empty() {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", "path_missing").with_field("path"),
            );
            continue;
        }
        if value.len() > MAX_PATH_BYTES {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("resource", "path_bytes_exceeded")
                    .with_field("path")
                    .with_expected(MAX_PATH_BYTES.to_string())
                    .with_actual(value.len().to_string()),
            );
            continue;
        }
        let relative = Path::new(value);
        let components = relative.components().collect::<Vec<_>>();
        if relative.is_absolute()
            || components
                .iter()
                .any(|component| matches!(component, Component::CurDir | Component::ParentDir))
        {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", "path_escape")
                    .with_field("path")
                    .with_actual(value.to_owned()),
            );
            continue;
        }
        let first_is_mathlib = matches!(
            components.first(),
            Some(Component::Normal(component)) if component.to_str() == Some("Mathlib")
        );
        if !first_is_mathlib {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("normalization", "module_path_mismatch")
                    .with_field("path")
                    .with_expected("Mathlib/**/*.lean")
                    .with_actual(value.to_owned()),
            );
            continue;
        }
        if relative
            .extension()
            .and_then(|extension| extension.to_str())
            != Some("lean")
        {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", "wrong_extension")
                    .with_field("path")
                    .with_expected(".lean")
                    .with_actual(value.to_owned()),
            );
            continue;
        }
        if value
            .chars()
            .any(|character| character == '\t' || character == '\n')
        {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", "path_contains_control")
                    .with_field("path")
                    .with_actual(value.to_owned()),
            );
            continue;
        }
        if !seen.insert(value.to_owned()) {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("input", "duplicate_path")
                    .with_field("path")
                    .with_actual(value.to_owned()),
            );
            continue;
        }
        normalized.push(RequestedPath {
            display: value.to_owned(),
        });
    }
    normalized.sort_by(|left, right| left.display.as_bytes().cmp(right.display.as_bytes()));
    normalized
}

fn normalize_selectors(
    declarations: &[String],
    diagnostics: &mut Vec<AdapterDiagnostic>,
) -> Vec<Selector> {
    if declarations.len() > MAX_DECLARATION_SELECTORS {
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("resource", "selector_count_exceeded")
                .with_field("declaration")
                .with_expected(MAX_DECLARATION_SELECTORS.to_string())
                .with_actual(declarations.len().to_string()),
        );
        return Vec::new();
    }
    let mut selectors = Vec::new();
    let mut seen = BTreeSet::new();
    for declaration in declarations {
        if declaration.len() > MAX_IDENTIFIER_BYTES {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("resource", "identifier_bytes_exceeded")
                    .with_field("declaration")
                    .with_expected(MAX_IDENTIFIER_BYTES.to_string())
                    .with_actual(declaration.clone()),
            );
            continue;
        }
        if !is_ascii_dotted_identifier(declaration) {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("input", "invalid_identifier")
                    .with_field("declaration")
                    .with_actual(declaration.clone()),
            );
            continue;
        }
        if !seen.insert(declaration.clone()) {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("input", "duplicate_selector")
                    .with_field("declaration")
                    .with_actual(declaration.clone()),
            );
            continue;
        }
        let mut parts = declaration.rsplitn(2, '.');
        let leaf = parts.next().unwrap_or_default().to_owned();
        let namespace = parts.next().unwrap_or_default().to_owned();
        selectors.push(Selector {
            name: declaration.clone(),
            namespace,
            leaf,
        });
    }
    selectors.sort_by(|left, right| left.name.as_bytes().cmp(right.name.as_bytes()));
    selectors
}

fn read_source_files(
    root: &Path,
    paths: &[RequestedPath],
    diagnostics: &mut Vec<AdapterDiagnostic>,
) -> Vec<SourceFile> {
    let root_directory = match open_absolute_directory(root, false) {
        Ok(directory) => directory,
        Err(_) => {
            // This metadata lookup is diagnostic-only. Source access remains
            // anchored to the no-follow directory capability above.
            let reason = match fs::symlink_metadata(root) {
                Ok(metadata) if metadata.file_type().is_symlink() => "root_symlink",
                _ => "root_not_directory",
            };
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", reason).with_field("root"),
            );
            return Vec::new();
        }
    };
    let mut total_bytes = 0usize;
    let mut files = Vec::new();
    for requested in paths {
        let relative = Path::new(&requested.display);
        let components = relative.components().collect::<Vec<_>>();
        let Some((leaf, parents)) = components.split_last() else {
            continue;
        };
        let mut directory = match root_directory.try_clone() {
            Ok(directory) => directory,
            Err(_) => continue,
        };
        let mut invalid_reason = None;
        for component in parents {
            let Component::Normal(component) = component else {
                invalid_reason = Some("path_missing");
                break;
            };
            match directory.entry_kind(component) {
                Ok(Some(EntryKind::Directory)) => {
                    match directory.open_or_create_directory(component, false) {
                        Ok(child) => directory = child,
                        Err(_) => {
                            invalid_reason = Some("path_missing");
                            break;
                        }
                    }
                }
                Ok(Some(EntryKind::SymbolicLink)) => {
                    invalid_reason = Some("symlink_entry");
                    break;
                }
                Ok(Some(EntryKind::Regular | EntryKind::Other)) => {
                    invalid_reason = Some("non_regular_entry");
                    break;
                }
                Ok(None) | Err(_) => {
                    invalid_reason = Some("path_missing");
                    break;
                }
            }
        }
        let Component::Normal(leaf) = leaf else {
            continue;
        };
        if let Some(reason) = invalid_reason {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("filesystem", reason).with_path(requested.display.clone()),
            );
            continue;
        }
        match directory.entry_kind(leaf) {
            Ok(Some(EntryKind::Regular)) => {}
            Ok(Some(EntryKind::SymbolicLink)) => {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("filesystem", "symlink_entry")
                        .with_path(requested.display.clone()),
                );
                continue;
            }
            Ok(Some(EntryKind::Directory | EntryKind::Other)) => {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("filesystem", "non_regular_entry")
                        .with_path(requested.display.clone()),
                );
                continue;
            }
            Ok(None) | Err(_) => {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("filesystem", "path_missing")
                        .with_path(requested.display.clone()),
                );
                continue;
            }
        }
        let file = match directory.open_regular_file(leaf) {
            Ok(Some(file)) => file,
            Ok(None) | Err(_) => {
                let reason = match directory.entry_kind(leaf) {
                    Ok(Some(EntryKind::SymbolicLink)) => "symlink_entry",
                    Ok(Some(EntryKind::Directory | EntryKind::Other)) => "non_regular_entry",
                    Ok(Some(EntryKind::Regular)) => "read_failed",
                    Ok(None) | Err(_) => "path_missing",
                };
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("filesystem", reason)
                        .with_path(requested.display.clone()),
                );
                continue;
            }
        };
        let metadata = match file.metadata() {
            Ok(metadata) => metadata,
            Err(_) => continue,
        };
        if metadata.len() > MAX_SOURCE_FILE_BYTES as u64 {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("resource", "source_file_bytes_exceeded")
                    .with_path(requested.display.clone())
                    .with_expected(MAX_SOURCE_FILE_BYTES.to_string())
                    .with_actual(metadata.len().to_string()),
            );
            continue;
        }
        let file_bytes = metadata.len() as usize;
        if total_bytes.saturating_add(file_bytes) > MAX_SOURCE_SET_BYTES {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("resource", "source_set_bytes_exceeded")
                    .with_path(requested.display.clone())
                    .with_expected(MAX_SOURCE_SET_BYTES.to_string())
                    .with_actual(total_bytes.saturating_add(file_bytes).to_string()),
            );
            continue;
        }
        let mut bytes = Vec::new();
        let bytes = match file
            .take((MAX_SOURCE_FILE_BYTES as u64) + 1)
            .read_to_end(&mut bytes)
        {
            Ok(_) if bytes.len() <= MAX_SOURCE_FILE_BYTES => bytes,
            Ok(_) => continue,
            Err(_) => {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("filesystem", "read_failed")
                        .with_path(requested.display.clone()),
                );
                continue;
            }
        };
        total_bytes += bytes.len();
        let source = match String::from_utf8(bytes.clone()) {
            Ok(source) => Some(source),
            Err(_) => {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("syntax", "invalid_utf8")
                        .with_path(requested.display.clone()),
                );
                None
            }
        };
        files.push(SourceFile {
            path: requested.display.clone(),
            file_hash: format_package_hash(&package_file_hash(&bytes)),
            bytes,
            source,
        });
    }
    files.sort_by(|left, right| left.path.as_bytes().cmp(right.path.as_bytes()));
    files
}

fn source_set_hash(files: &[InterfaceInventoryInputFile]) -> String {
    let mut canonical = String::from("npa.mathlib.interface_inventory_source_set.v1\n");
    for file in files {
        canonical.push_str(&file.path);
        canonical.push('\t');
        canonical.push_str(&file.file_hash);
        canonical.push('\t');
        canonical.push_str(&file.byte_count.to_string());
        canonical.push('\n');
    }
    format_package_hash(&package_file_hash(canonical.as_bytes()))
}

fn build_rows(
    source_files: &[SourceFile],
    selectors: &[Selector],
    rows: &mut Vec<InterfaceInventoryRow>,
    diagnostics: &mut Vec<AdapterDiagnostic>,
) {
    let mut parsed_files = Vec::new();
    for source in source_files {
        let Some(text) = source.source.as_deref() else {
            return;
        };
        match parse_source(text) {
            Ok(parsed) => parsed_files.push((source, parsed)),
            Err(error) => add_diagnostic(diagnostics, error.with_path(source.path.clone())),
        }
    }
    if !diagnostics.is_empty() {
        return;
    }

    let mut selected = Vec::new();
    for selector in selectors {
        let mut matches = Vec::new();
        let mut unsupported_match = None;
        for (source, parsed) in &parsed_files {
            for declaration in &parsed.declarations {
                if declaration.name == selector.name {
                    matches.push((*source, declaration.clone()));
                }
            }
            for declaration in &parsed.unsupported_declarations {
                if declaration.name == selector.name {
                    unsupported_match = Some(declaration.clone());
                }
            }
        }
        match matches.len() {
            0 if unsupported_match.is_some() => add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("syntax", "unsupported_declaration")
                    .with_field("declaration")
                    .with_actual(selector.name.clone()),
            ),
            0 => add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("syntax", "declaration_not_found")
                    .with_field("declaration")
                    .with_actual(selector.name.clone()),
            ),
            1 => selected.push((selector, matches.remove(0))),
            _ => add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("normalization", "duplicate_row")
                    .with_field("declaration")
                    .with_actual(selector.name.clone()),
            ),
        }
    }
    if !diagnostics.is_empty() {
        return;
    }

    for (source, parsed) in &parsed_files {
        let module = module_name_from_path(&source.path);
        if !push_row(
            rows,
            diagnostics,
            InterfaceInventoryRow {
                row_kind: "module_layout".to_owned(),
                id: format!("module:{}", source.path),
                path: source.path.clone(),
                line: 1,
                repository: String::new(),
                revision_kind: REVISION_KIND.to_owned(),
                revision: String::new(),
                license: String::new(),
                source_module: Some(module.clone()),
                source_declaration: None,
                referenced_declaration: None,
                usage_kind: "module_layout".to_owned(),
                declaration_kind: None,
                import_visibility: None,
                notes: "module_path_derived=true".to_owned(),
            },
        ) {
            return;
        }
        for import in &parsed.imports {
            if !push_row(
                rows,
                diagnostics,
                InterfaceInventoryRow {
                    row_kind: "module_import".to_owned(),
                    id: format!("import:{}:{}:{}", source.path, import.line, import.module),
                    path: source.path.clone(),
                    line: import.line,
                    repository: String::new(),
                    revision_kind: REVISION_KIND.to_owned(),
                    revision: String::new(),
                    license: String::new(),
                    source_module: Some(import.module.clone()),
                    source_declaration: None,
                    referenced_declaration: None,
                    usage_kind: "module_import".to_owned(),
                    declaration_kind: None,
                    import_visibility: Some(
                        if import.public { "public" } else { "private" }.to_owned(),
                    ),
                    notes: format!(
                        "visibility={}",
                        if import.public { "public" } else { "private" }
                    ),
                },
            ) {
                return;
            }
        }
    }

    // Provenance is attached in one place after normalized rows are built.
    for (_, (source, declaration)) in &selected {
        let module = module_name_from_path(&source.path);
        if !push_row(
            rows,
            diagnostics,
            InterfaceInventoryRow {
                row_kind: "declaration".to_owned(),
                id: format!(
                    "declaration:{}:{}:{}",
                    source.path, declaration.line, declaration.name
                ),
                path: source.path.clone(),
                line: declaration.line,
                repository: String::new(),
                revision_kind: REVISION_KIND.to_owned(),
                revision: String::new(),
                license: String::new(),
                source_module: Some(module),
                source_declaration: Some(declaration.name.clone()),
                referenced_declaration: None,
                usage_kind: "declaration".to_owned(),
                declaration_kind: Some(declaration.kind.to_owned()),
                import_visibility: None,
                notes: format!("declaration_kind={}", declaration.kind),
            },
        ) {
            return;
        }
    }

    let target_specs = selectors.to_vec();
    let mut ordinals = BTreeMap::<(String, u32), u32>::new();
    for (_, (source, declaration)) in selected {
        let Some(parsed) = parsed_files
            .iter()
            .find(|(candidate, _)| candidate.path == source.path)
            .map(|(_, parsed)| parsed)
        else {
            continue;
        };
        if parsed.tokens[declaration.start..declaration.end]
            .iter()
            .any(|token| {
                matches!(
                    &token.kind,
                    TokenKind::Identifier(name)
                        if matches!(
                            name.as_str(),
                            "infer_instance"
                                | "inferInstance"
                                | "synthInstance"
                                | "synth_instance"
                        )
                )
            })
        {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("syntax", "unsupported_inference_use")
                    .with_path(source.path.clone())
                    .with_line(declaration.line)
                    .with_field("declaration"),
            );
            continue;
        }
        if let Some(token) = parsed.tokens[declaration.start..declaration.end]
            .iter()
            .find(|token| {
                matches!(
                    &token.kind,
                    TokenKind::Identifier(name)
                        if matches!(name.as_str(), "macro" | "syntax" | "elab" | "run_tac")
                )
            })
        {
            add_diagnostic(
                diagnostics,
                AdapterDiagnostic::new("syntax", "unsupported_command")
                    .with_path(source.path.clone())
                    .with_line(token.line)
                    .with_field("command"),
            );
            continue;
        }
        let namespace = namespace_of(&declaration.name);
        let mut index = declaration.start;
        while index < declaration.end {
            let Some((target, consumed)) =
                target_at(&parsed.tokens, index, &target_specs, &namespace)
            else {
                index += 1;
                continue;
            };
            if index == declaration.name_index {
                index += consumed;
                continue;
            }
            if consumed == 1
                && index > declaration.start
                && is_symbol(&parsed.tokens[index - 1], ".")
            {
                add_diagnostic(
                    diagnostics,
                    AdapterDiagnostic::new("syntax", "unsupported_reference")
                        .with_path(source.path.clone())
                        .with_line(parsed.tokens[index].line)
                        .with_field("reference")
                        .with_expected("explicit selected declaration reference")
                        .with_actual("dot-notation reference"),
                );
                index += consumed;
                continue;
            }
            let usage_kind = if is_rewrite_context(&parsed.tokens, index) {
                "rewrite"
            } else {
                "direct_application"
            };
            let line = parsed.tokens[index].line;
            let ordinal_key = (source.path.clone(), line);
            let ordinal = ordinals.entry(ordinal_key).or_insert(0);
            *ordinal += 1;
            if !push_row(
                rows,
                diagnostics,
                InterfaceInventoryRow {
                    row_kind: "use_site".to_owned(),
                    id: format!(
                        "use:{}:{}:{}:{}:{}:{}",
                        source.path, line, declaration.name, target.name, usage_kind, ordinal
                    ),
                    path: source.path.clone(),
                    line,
                    repository: String::new(),
                    revision_kind: REVISION_KIND.to_owned(),
                    revision: String::new(),
                    license: String::new(),
                    source_module: Some(module_name_from_path(&source.path)),
                    source_declaration: Some(declaration.name.clone()),
                    referenced_declaration: Some(target.name.clone()),
                    usage_kind: usage_kind.to_owned(),
                    declaration_kind: None,
                    import_visibility: None,
                    notes: format!(
                        "reference_form={}",
                        if usage_kind == "rewrite" {
                            "explicit_rule_list"
                        } else {
                            "explicit"
                        }
                    ),
                },
            ) {
                return;
            }
            index += consumed;
        }
    }
}

fn parse_source(source: &str) -> Result<ParsedSource, AdapterDiagnostic> {
    let tokens = lex_source(source)?;
    let mut imports = Vec::new();
    let mut declarations = Vec::new();
    let mut unsupported_declarations = Vec::new();
    let mut namespaces = Vec::<String>::new();
    let mut index = 0usize;
    while index < tokens.len() {
        let Some(identifier) = identifier_at(&tokens[index]) else {
            index += 1;
            continue;
        };
        if identifier == "public"
            && index + 1 < tokens.len()
            && is_identifier(&tokens[index + 1], "import")
        {
            if let Some((module, next)) = dotted_name_at(&tokens, index + 2) {
                imports.push(ParsedImport {
                    module,
                    line: tokens[index + 1].line,
                    public: true,
                });
                index = next;
                continue;
            }
            return Err(
                AdapterDiagnostic::new("syntax", "malformed_import").with_line(tokens[index].line)
            );
        }
        if identifier == "import" {
            if let Some((module, next)) = dotted_name_at(&tokens, index + 1) {
                imports.push(ParsedImport {
                    module,
                    line: tokens[index].line,
                    public: false,
                });
                index = next;
                continue;
            }
            return Err(
                AdapterDiagnostic::new("syntax", "malformed_import").with_line(tokens[index].line)
            );
        }
        if identifier == "namespace" {
            if let Some((namespace, next)) = dotted_name_at(&tokens, index + 1) {
                namespaces.push(namespace);
                index = next;
                continue;
            }
            return Err(AdapterDiagnostic::new("syntax", "unsupported_command")
                .with_line(tokens[index].line));
        }
        if identifier == "section" {
            namespaces.push(String::new());
            index += 1;
            continue;
        }
        if identifier == "end" {
            namespaces.pop();
            index += 1;
            continue;
        }
        if matches!(identifier, "def" | "theorem" | "lemma") {
            if let Some((name, next)) = dotted_name_at(&tokens, index + 1) {
                let qualified = qualify_name(&namespaces, &name);
                declarations.push(ParsedDeclaration {
                    name: qualified,
                    kind: match identifier {
                        "def" => "def",
                        "theorem" => "theorem",
                        _ => "lemma",
                    },
                    line: tokens[index].line,
                    start: index,
                    name_index: index + 1,
                    end: tokens.len(),
                });
                index = next;
                continue;
            }
            return Err(AdapterDiagnostic::new("syntax", "unsupported_declaration")
                .with_line(tokens[index].line));
        }
        if matches!(
            identifier,
            "axiom"
                | "example"
                | "instance"
                | "opaque"
                | "abbrev"
                | "inductive"
                | "class"
                | "structure"
        ) {
            if let Some((name, next)) = dotted_name_at(&tokens, index + 1) {
                unsupported_declarations.push(UnsupportedDeclaration {
                    name: qualify_name(&namespaces, &name),
                    line: tokens[index].line,
                    start: index,
                });
                index = next;
                continue;
            }
        }
        index += 1;
    }
    let mut boundaries = declarations
        .iter()
        .map(|declaration| declaration.start)
        .chain(
            unsupported_declarations
                .iter()
                .map(|unsupported| unsupported.start),
        )
        .collect::<Vec<_>>();
    boundaries.sort_unstable();
    boundaries.dedup();
    for declaration in &mut declarations {
        declaration.end = boundaries
            .iter()
            .copied()
            .find(|boundary| *boundary > declaration.start)
            .unwrap_or(tokens.len());
    }
    Ok(ParsedSource {
        tokens,
        imports,
        declarations,
        unsupported_declarations,
    })
}

fn lex_source(source: &str) -> Result<Vec<Token>, AdapterDiagnostic> {
    let mut tokens = Vec::new();
    let mut iterator = source.char_indices().peekable();
    let mut line = 1u32;
    while let Some((_, character)) = iterator.next() {
        if character.is_whitespace() {
            if character == '\n' {
                line = line.saturating_add(1);
            }
            continue;
        }
        if character == '-' && peek_is(&mut iterator, '-') {
            iterator.next();
            for (_, next) in iterator.by_ref() {
                if next == '\n' {
                    line = line.saturating_add(1);
                    break;
                }
            }
            continue;
        }
        if character == '/' && peek_is(&mut iterator, '-') {
            iterator.next();
            let start_line = line;
            let mut depth = 1usize;
            while let Some((_, next)) = iterator.next() {
                if next == '\n' {
                    line = line.saturating_add(1);
                }
                if next == '/' && peek_is(&mut iterator, '-') {
                    iterator.next();
                    depth += 1;
                } else if next == '-' && peek_is(&mut iterator, '/') {
                    iterator.next();
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        break;
                    }
                }
            }
            if depth != 0 {
                return Err(
                    AdapterDiagnostic::new("syntax", "malformed_comment_or_literal")
                        .with_line(start_line),
                );
            }
            continue;
        }
        if character == '"' {
            let start_line = line;
            let mut escaped = false;
            let mut closed = false;
            for (_, next) in iterator.by_ref() {
                if next == '\n' {
                    line = line.saturating_add(1);
                }
                if escaped {
                    escaped = false;
                } else if next == '\\' {
                    escaped = true;
                } else if next == '"' {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(
                    AdapterDiagnostic::new("syntax", "malformed_comment_or_literal")
                        .with_line(start_line),
                );
            }
            tokens.push(Token {
                kind: TokenKind::Opaque,
                line: start_line,
            });
            continue;
        }
        if character == '\'' {
            let start_line = line;
            let mut closed = false;
            for (_, next) in iterator.by_ref() {
                if next == '\n' {
                    line = line.saturating_add(1);
                }
                if next == '\'' {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(
                    AdapterDiagnostic::new("syntax", "malformed_comment_or_literal")
                        .with_line(start_line),
                );
            }
            tokens.push(Token {
                kind: TokenKind::Opaque,
                line: start_line,
            });
            continue;
        }
        if is_identifier_start(character) {
            let start_line = line;
            let mut value = String::from(character);
            while let Some((_, next)) = iterator.peek().copied() {
                if !is_identifier_continue(next) {
                    break;
                }
                iterator.next();
                value.push(next);
                if value.len() > MAX_IDENTIFIER_BYTES {
                    return Err(
                        AdapterDiagnostic::new("resource", "identifier_bytes_exceeded")
                            .with_field("identifier")
                            .with_expected(MAX_IDENTIFIER_BYTES.to_string())
                            .with_actual(value),
                    );
                }
            }
            tokens.push(Token {
                kind: TokenKind::Identifier(value),
                line: start_line,
            });
            continue;
        }
        tokens.push(Token {
            kind: TokenKind::Symbol(character.to_string()),
            line,
        });
    }
    Ok(tokens)
}

fn target_at<'a>(
    tokens: &[Token],
    index: usize,
    selectors: &'a [Selector],
    namespace: &str,
) -> Option<(&'a Selector, usize)> {
    let mut full_matches = Vec::new();
    for selector in selectors {
        let parts = selector.name.split('.').collect::<Vec<_>>();
        if dotted_tokens_match(tokens, index, &parts) {
            full_matches.push((selector, parts.len() * 2 - 1));
        }
    }
    if let Some(found) = full_matches.into_iter().next() {
        return Some(found);
    }
    let identifier = identifier_at(tokens.get(index)?)?;
    let matches = selectors
        .iter()
        .filter(|selector| selector.leaf == identifier && selector.namespace == namespace)
        .collect::<Vec<_>>();
    (matches.len() == 1).then(|| (matches[0], 1))
}

fn dotted_tokens_match(tokens: &[Token], index: usize, parts: &[&str]) -> bool {
    if parts.is_empty() || index + parts.len() * 2 - 1 > tokens.len() {
        return false;
    }
    for (part_index, part) in parts.iter().enumerate() {
        let token_index = index + part_index * 2;
        if !is_identifier(tokens.get(token_index).unwrap(), part) {
            return false;
        }
        if part_index + 1 < parts.len() && !is_symbol(tokens.get(token_index + 1).unwrap(), ".") {
            return false;
        }
    }
    true
}

fn is_rewrite_context(tokens: &[Token], index: usize) -> bool {
    let mut closing = 0usize;
    for cursor in (0..index).rev() {
        if is_symbol(&tokens[cursor], "]") {
            closing += 1;
        } else if is_symbol(&tokens[cursor], "[") {
            if closing > 0 {
                closing -= 1;
            } else {
                return cursor > 0
                    && matches!(
                        identifier_at(&tokens[cursor - 1]),
                        Some("rw" | "rwa" | "simp" | "simp_rw")
                    );
            }
        }
        if tokens[cursor].line + 3 < tokens[index].line {
            break;
        }
    }
    false
}

fn dotted_name_at(tokens: &[Token], index: usize) -> Option<(String, usize)> {
    let first = identifier_at(tokens.get(index)?)?.to_owned();
    let mut value = first;
    let mut cursor = index + 1;
    while cursor + 1 < tokens.len()
        && is_symbol(&tokens[cursor], ".")
        && identifier_at(&tokens[cursor + 1]).is_some()
    {
        value.push('.');
        value.push_str(identifier_at(&tokens[cursor + 1]).unwrap_or_default());
        cursor += 2;
    }
    Some((value, cursor))
}

fn qualify_name(namespaces: &[String], name: &str) -> String {
    let prefix = namespaces
        .iter()
        .filter(|namespace| !namespace.is_empty())
        .cloned()
        .collect::<Vec<_>>()
        .join(".");
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}.{name}")
    }
}

fn module_name_from_path(path: &str) -> String {
    path.strip_suffix(".lean").unwrap_or(path).replace('/', ".")
}

fn namespace_of(name: &str) -> String {
    name.rsplit_once('.')
        .map(|(namespace, _)| namespace.to_owned())
        .unwrap_or_default()
}

fn identifier_at(token: &Token) -> Option<&str> {
    match &token.kind {
        TokenKind::Identifier(value) => Some(value),
        TokenKind::Symbol(_) | TokenKind::Opaque => None,
    }
}

fn is_identifier(token: &Token, value: &str) -> bool {
    identifier_at(token) == Some(value)
}

fn is_symbol(token: &Token, value: &str) -> bool {
    matches!(&token.kind, TokenKind::Symbol(actual) if actual == value)
}

fn is_identifier_start(character: char) -> bool {
    character.is_ascii_alphabetic() || character == '_'
}

fn is_identifier_continue(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '_' | '\'')
}

fn is_ascii_dotted_identifier(value: &str) -> bool {
    value
        .split('.')
        .all(|part| !part.is_empty() && is_ascii_identifier(part))
}

fn is_ascii_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && characters
            .all(|character| character.is_ascii_alphanumeric() || matches!(character, '_' | '\''))
}

fn is_lower_hex_revision(value: &str) -> bool {
    value.len() == 40
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn looks_like_floating_revision(value: &str) -> bool {
    value.len() < 40
        && !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-' | b'/'))
}

fn unknown_license_note_is_sufficient(note: &str) -> bool {
    let lower = note.to_ascii_lowercase();
    ["follow", "pending", "resolve", "review", "confirm"]
        .iter()
        .any(|marker| lower.contains(marker))
}

fn peek_is<I>(iterator: &mut std::iter::Peekable<I>, expected: char) -> bool
where
    I: Iterator<Item = (usize, char)>,
{
    iterator
        .peek()
        .is_some_and(|(_, character)| *character == expected)
}

fn add_diagnostic(diagnostics: &mut Vec<AdapterDiagnostic>, diagnostic: AdapterDiagnostic) {
    if diagnostics
        .iter()
        .any(|existing| existing.reason == "diagnostic_count_exceeded")
    {
        return;
    }
    if diagnostics.len() + 1 < MAX_DIAGNOSTICS {
        diagnostics.push(diagnostic);
    } else {
        diagnostics.push(
            AdapterDiagnostic::new("resource", "diagnostic_count_exceeded")
                .with_field("diagnostics")
                .with_expected(MAX_DIAGNOSTICS.to_string())
                .with_actual((MAX_DIAGNOSTICS + 1).to_string()),
        );
    }
}

fn push_row(
    rows: &mut Vec<InterfaceInventoryRow>,
    diagnostics: &mut Vec<AdapterDiagnostic>,
    row: InterfaceInventoryRow,
) -> bool {
    if rows.len() >= MAX_ROWS {
        add_diagnostic(
            diagnostics,
            AdapterDiagnostic::new("resource", "row_count_exceeded")
                .with_field("rows")
                .with_expected(MAX_ROWS.to_string())
                .with_actual((MAX_ROWS + 1).to_string()),
        );
        return false;
    }
    rows.push(row);
    true
}

fn row_order(left: &InterfaceInventoryRow, right: &InterfaceInventoryRow) -> std::cmp::Ordering {
    left.path
        .as_bytes()
        .cmp(right.path.as_bytes())
        .then_with(|| left.line.cmp(&right.line))
        .then_with(|| row_kind_order(&left.row_kind).cmp(&row_kind_order(&right.row_kind)))
        .then_with(|| left.source_declaration.cmp(&right.source_declaration))
        .then_with(|| {
            left.referenced_declaration
                .cmp(&right.referenced_declaration)
        })
        .then_with(|| left.usage_kind.cmp(&right.usage_kind))
        .then_with(|| left.id.cmp(&right.id))
}

fn row_kind_order(kind: &str) -> u8 {
    match kind {
        "module_layout" => 0,
        "module_import" => 1,
        "declaration" => 2,
        "use_site" => 3,
        _ => 4,
    }
}

fn diagnostic_order(left: &AdapterDiagnostic, right: &AdapterDiagnostic) -> std::cmp::Ordering {
    left.path
        .cmp(&right.path)
        .then_with(|| left.line.cmp(&right.line))
        .then_with(|| left.category.cmp(right.category))
        .then_with(|| left.reason.cmp(right.reason))
        .then_with(|| left.field.cmp(&right.field))
}

fn bounded(value: &str, max_bytes: usize) -> String {
    if value.len() <= max_bytes {
        return value.to_owned();
    }
    let mut end = max_bytes;
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    value[..end].to_owned()
}

#[cfg(all(test, unix))]
mod tests {
    use std::{
        fs,
        os::unix::fs::symlink,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{read_source_files, AdapterDiagnostic, RequestedPath, MAX_SOURCE_FILE_BYTES};

    static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

    struct TestRoot {
        relative: PathBuf,
        absolute: PathBuf,
    }

    impl TestRoot {
        fn new(label: &str) -> Self {
            let relative = PathBuf::from(format!(
                ".npa-interface-inventory-{label}-{}-{}",
                std::process::id(),
                NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
            ));
            let absolute = std::env::current_dir()
                .expect("current directory")
                .join(&relative);
            fs::create_dir(&absolute).expect("create test root");
            Self { relative, absolute }
        }
    }

    impl Drop for TestRoot {
        fn drop(&mut self) {
            if self.absolute.is_dir() && !self.absolute.is_symlink() {
                let _ = fs::remove_dir_all(&self.absolute);
            }
        }
    }

    fn requested(path: &str) -> Vec<RequestedPath> {
        vec![RequestedPath {
            display: path.to_owned(),
        }]
    }

    fn reasons(diagnostics: &[AdapterDiagnostic]) -> Vec<&'static str> {
        diagnostics.iter().map(|item| item.reason).collect()
    }

    fn read(root: &Path, path: &str) -> (usize, Vec<&'static str>) {
        let mut diagnostics = Vec::new();
        let files = read_source_files(root, &requested(path), &mut diagnostics);
        (files.len(), reasons(&diagnostics))
    }

    #[test]
    fn interface_inventory_source_reader_is_relative_bounded_and_no_follow() {
        let valid = TestRoot::new("relative");
        fs::create_dir(valid.absolute.join("Mathlib")).expect("create Mathlib");
        fs::write(
            valid.absolute.join("Mathlib/Valid.lean"),
            b"theorem Mathlib.Valid : True := by trivial\n",
        )
        .expect("write source");
        assert_eq!(read(&valid.relative, "Mathlib/Valid.lean"), (1, vec![]));

        let final_link = TestRoot::new("final-link");
        fs::create_dir(final_link.absolute.join("Mathlib")).expect("create Mathlib");
        let outside = final_link.absolute.join("outside.lean");
        fs::write(&outside, b"theorem Outside : True := by trivial\n").expect("write outside");
        symlink(&outside, final_link.absolute.join("Mathlib/Linked.lean"))
            .expect("create final symlink");
        assert_eq!(
            read(&final_link.absolute, "Mathlib/Linked.lean"),
            (0, vec!["symlink_entry"])
        );

        let intermediate_link = TestRoot::new("intermediate-link");
        let outside_dir = intermediate_link.absolute.join("outside");
        fs::create_dir(&outside_dir).expect("create outside directory");
        fs::write(
            outside_dir.join("Linked.lean"),
            b"theorem Outside : True := by trivial\n",
        )
        .expect("write outside source");
        symlink(&outside_dir, intermediate_link.absolute.join("Mathlib"))
            .expect("create intermediate symlink");
        assert_eq!(
            read(&intermediate_link.absolute, "Mathlib/Linked.lean"),
            (0, vec!["symlink_entry"])
        );

        let oversized = TestRoot::new("oversized");
        fs::create_dir(oversized.absolute.join("Mathlib")).expect("create Mathlib");
        let file = fs::File::create(oversized.absolute.join("Mathlib/Huge.lean"))
            .expect("create sparse source");
        file.set_len((MAX_SOURCE_FILE_BYTES as u64) + 1)
            .expect("extend sparse source");
        assert_eq!(
            read(&oversized.absolute, "Mathlib/Huge.lean"),
            (0, vec!["source_file_bytes_exceeded"])
        );
    }
}

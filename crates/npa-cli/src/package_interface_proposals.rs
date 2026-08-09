//! Read-only discovery, proposal-set hashing, and frontend surface validation
//! for interface proposals.
//!
//! Discovery confines a caller-selected proposal root, scans only
//! `Mathlib/**/*.toml`, retains exact UTF-8 bytes in memory within the frozen
//! resource limits, and computes the deterministic proposal-set hash. Surface
//! validation consumes only caller-supplied in-memory verified import context.
//! All returned proposal data and frontend results remain untrusted curation
//! metadata; they are not proof evidence, catalog admission, or a Git/history
//! decision.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsStr,
    fs::{self, OpenOptions},
    io::{self, Read},
    path::{Component, Path, PathBuf},
};

#[cfg(unix)]
use std::os::unix::{ffi::OsStrExt, fs::OpenOptionsExt};

use npa_cert::Name;
use npa_frontend::{
    parse_human_module_with_source_interfaces, parse_human_term,
    resolve_human_module_with_source_interfaces, FileId, HumanCompileOptions, HumanDiagnostic,
    HumanDiagnosticKind, HumanExpr, HumanImportedSourceInterface, HumanItem, HumanLevel,
    HumanSourceDeclarationKind, VerifiedImport,
};
use npa_package::{
    format_package_hash, interface_proposal_file_hash, parse_interface_proposal,
    validate_interface_proposal, InterfaceProposal, InterfaceProposalChangeKind,
    InterfaceProposalDeclaration, InterfaceProposalDeclarationKind, InterfaceProposalError,
    InterfaceProposalErrorCategory, InterfaceProposalErrorReason, InterfaceProposalStatus,
    PackageHash, PackageModule, ValidatedPackageManifest, MAX_DIAGNOSTICS,
    MAX_DIAGNOSTIC_VALUE_BYTES, MAX_PATH_BYTES, MAX_PROPOSAL_FILES, MAX_PROPOSAL_FILE_BYTES,
    MAX_PROPOSAL_SET_BYTES,
};
use sha2::{Digest, Sha256};

use crate::args::PackageCheckInterfaceProposalsOptions;
use crate::diagnostic::{
    CommandDiagnostic, CommandResult, DiagnosticKind, InterfaceProposalCheckDiagnostic,
    InterfaceProposalCheckOutput, InterfaceProposalCheckRow, InterfaceProposalCheckSnapshot,
    InterfaceProposalStatusCounts,
};
use crate::package::load_package_root;

const INTERFACE_PROPOSAL_COMMAND: &str = "package check-interface-proposals";

const DEFAULT_PROPOSAL_ROOT: &str = "interface-proposals";
const CANONICAL_MODULE_ROOT: &str = "Mathlib";
const PROPOSAL_SET_HASH_SCHEMA: &[u8] = b"npa.mathlib.interface_proposal_set.v1\n";

/// A discovered canonical proposal file with its exact bytes and file hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalDiscoveredFile {
    /// Proposal-root-relative UTF-8 path, for example `Mathlib/Logic/Basic.toml`.
    pub relative_path: String,
    /// SHA-256 hash of the exact file bytes.
    pub file_hash: PackageHash,
    bytes: Vec<u8>,
}

impl InterfaceProposalDiscoveredFile {
    /// Return the exact UTF-8 TOML bytes read during discovery.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// In-memory deterministic summary of one canonical proposal-set scan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalDiscovery {
    /// Canonical proposal files sorted by relative-path UTF-8 byte order.
    pub files: Vec<InterfaceProposalDiscoveredFile>,
    /// Sum of exact bytes in all discovered proposal files.
    pub total_file_bytes: usize,
    /// SHA-256 hash of the canonical proposal-set rows.
    pub proposal_set_hash: PackageHash,
}

impl InterfaceProposalDiscovery {
    /// Return the number of discovered canonical proposal files.
    pub fn proposal_count(&self) -> usize {
        self.files.len()
    }
}

/// One parsed proposal record retaining its canonical relative path and file hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalRecord {
    /// Proposal-root-relative canonical TOML path.
    pub relative_path: String,
    /// SHA-256 hash of the exact proposal bytes.
    pub file_hash: PackageHash,
    /// Parsed proposal metadata.
    pub proposal: InterfaceProposal,
}

/// Parse every exact file in a discovered proposal set without reading any
/// additional filesystem state.
pub fn parse_interface_proposal_set(
    discovery: &InterfaceProposalDiscovery,
) -> Result<Vec<InterfaceProposalRecord>, InterfaceProposalError> {
    discovery
        .files
        .iter()
        .map(|file| {
            parse_interface_proposal(file.bytes())
                .map(|proposal| InterfaceProposalRecord {
                    relative_path: file.relative_path.clone(),
                    file_hash: file.file_hash,
                    proposal,
                })
                .map_err(|error| prefix_record_error(&file.relative_path, error))
        })
        .collect()
}

/// Run the public read-only interface-proposal curation check.
///
/// The command deliberately stays on the metadata side of the trust boundary:
/// it reads the package manifest and proposal roots, performs catalog and
/// caller-supplied previous-snapshot checks, and never invokes Git, a proof
/// checker, certificate acceptance, or a writer. Frontend surface validation is
/// exposed separately through [`validate_interface_proposal_surface`] because
/// its verified-import context is an explicit caller input rather than a
/// command-side proof decision.
pub fn run_package_check_interface_proposals(
    options: PackageCheckInterfaceProposalsOptions,
) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, INTERFACE_PROPOSAL_COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let mut errors = Vec::new();
    let current_root =
        match resolve_interface_proposal_root(&loaded.root, options.proposal_root.as_deref()) {
            Ok(root) => Some(root),
            Err(error) => {
                errors.push(error);
                None
            }
        };
    let current_discovery = current_root.as_deref().and_then(|root| {
        match discover_resolved_interface_proposal_set(root) {
            Ok(discovery) => Some(discovery),
            Err(error) => {
                errors.push(error);
                None
            }
        }
    });
    let (current_snapshot, current_records, current_parse_errors) = current_discovery
        .as_ref()
        .map(parse_interface_proposal_snapshot)
        .unwrap_or_else(empty_interface_proposal_snapshot);
    let current_parse_valid = current_discovery.is_some() && current_parse_errors.is_empty();
    errors.extend(current_parse_errors);

    if current_parse_valid {
        if let Err(error) = validate_interface_proposal_catalog(&current_records, &loaded.validated)
        {
            errors.push(error);
        }
    }

    let mut previous = None;
    let mut previous_root = None;
    let mut previous_discovery = None;
    let mut previous_parse_valid = false;
    let previous_supplied = options.previous_proposal_root.is_some();
    if let Some(requested_previous_root) = options.previous_proposal_root.as_deref() {
        let resolved_previous_root =
            match resolve_previous_interface_proposal_root(&loaded.root, requested_previous_root) {
                Ok(root) => Some(root),
                Err(error) => {
                    errors.push(error);
                    None
                }
            };
        if let (Some(current_root), Some(resolved_previous_root)) =
            (current_root.as_deref(), resolved_previous_root.as_deref())
        {
            if current_root == resolved_previous_root {
                errors.push(InterfaceProposalError::new(
                    InterfaceProposalErrorCategory::Io,
                    InterfaceProposalErrorReason::PreviousRootSameAsCurrent,
                    "previous-proposal-root",
                    Some("--previous-proposal-root".to_owned()),
                    Some("different canonical proposal roots".to_owned()),
                    Some("same as current proposal root".to_owned()),
                ));
            } else {
                previous_root = Some(resolved_previous_root.to_path_buf());
                previous_discovery =
                    match discover_resolved_interface_proposal_set(resolved_previous_root) {
                        Ok(discovery) => Some(discovery),
                        Err(error) => {
                            errors.push(error);
                            None
                        }
                    };
            }
        }
    }

    if let Some(discovery) = previous_discovery.as_ref() {
        let (snapshot, _records, parse_errors) = parse_interface_proposal_snapshot(discovery);
        previous = Some(snapshot);
        previous_parse_valid = parse_errors.is_empty();
        errors.extend(parse_errors);
    } else if previous_supplied {
        previous = Some(empty_interface_proposal_snapshot().0);
    }

    if let (
        Some(current_discovery),
        Some(previous_discovery),
        Some(current_root),
        Some(previous_root),
    ) = (
        current_discovery.as_ref(),
        previous_discovery.as_ref(),
        current_root.as_deref(),
        previous_root.as_deref(),
    ) {
        if current_parse_valid && previous_parse_valid {
            if let Err(error) = validate_interface_proposal_transition(
                current_root,
                previous_root,
                current_discovery,
                previous_discovery,
            ) {
                errors.push(error);
            }
        }
    }

    errors.sort_by(|left, right| {
        left.path
            .as_bytes()
            .cmp(right.path.as_bytes())
            .then_with(|| left.category.cmp(&right.category))
            .then_with(|| left.reason_code.as_str().cmp(right.reason_code.as_str()))
            .then_with(|| left.field.cmp(&right.field))
    });
    if errors.len() > MAX_DIAGNOSTICS {
        let actual = errors.len().to_string();
        errors.truncate(MAX_DIAGNOSTICS.saturating_sub(1));
        errors.push(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Resource,
            InterfaceProposalErrorReason::DiagnosticCountExceeded,
            "<diagnostics>",
            None,
            Some(MAX_DIAGNOSTICS.to_string()),
            Some(actual),
        ));
        errors.sort_by(|left, right| {
            left.path
                .as_bytes()
                .cmp(right.path.as_bytes())
                .then_with(|| left.category.cmp(&right.category))
                .then_with(|| left.reason_code.as_str().cmp(right.reason_code.as_str()))
                .then_with(|| left.field.cmp(&right.field))
        });
    }
    let output_diagnostics = errors
        .iter()
        .map(interface_proposal_command_diagnostic)
        .collect::<Vec<_>>();
    let diagnostics = errors
        .iter()
        .map(interface_proposal_command_diagnostic_for_result)
        .collect::<Vec<_>>();
    let output = InterfaceProposalCheckOutput {
        status: if errors.is_empty() {
            "ok".to_owned()
        } else {
            "invalid".to_owned()
        },
        current: current_snapshot,
        previous,
        diagnostics: output_diagnostics,
    };
    let result = if diagnostics.is_empty() {
        CommandResult::passed(INTERFACE_PROPOSAL_COMMAND, loaded.root_display)
    } else {
        CommandResult::failed(INTERFACE_PROPOSAL_COMMAND, loaded.root_display, diagnostics)
    };
    result.with_interface_proposals(output)
}

fn parse_interface_proposal_snapshot(
    discovery: &InterfaceProposalDiscovery,
) -> (
    InterfaceProposalCheckSnapshot,
    Vec<InterfaceProposalRecord>,
    Vec<InterfaceProposalError>,
) {
    let mut rows = Vec::with_capacity(discovery.files.len());
    let mut records = Vec::with_capacity(discovery.files.len());
    let mut errors = Vec::new();
    let mut status_counts = InterfaceProposalStatusCounts {
        observed: 0,
        proposed: 0,
        adopted: 0,
        withdrawn: 0,
        superseded: 0,
    };
    for file in &discovery.files {
        match parse_interface_proposal(file.bytes()) {
            Ok(proposal) => {
                match proposal.interface_status {
                    InterfaceProposalStatus::Observed => status_counts.observed += 1,
                    InterfaceProposalStatus::Proposed => status_counts.proposed += 1,
                    InterfaceProposalStatus::Adopted => status_counts.adopted += 1,
                    InterfaceProposalStatus::Withdrawn => status_counts.withdrawn += 1,
                    InterfaceProposalStatus::Superseded => status_counts.superseded += 1,
                }
                rows.push(InterfaceProposalCheckRow {
                    path: file.relative_path.clone(),
                    file_hash: format_package_hash(&file.file_hash),
                    proposal_id: Some(proposal.proposal_id.clone()),
                    module: Some(proposal.module.clone()),
                    proposal_revision: Some(proposal.proposal_revision),
                    interface_status: Some(proposal.interface_status.as_str().to_owned()),
                });
                records.push(InterfaceProposalRecord {
                    relative_path: file.relative_path.clone(),
                    file_hash: file.file_hash,
                    proposal,
                });
            }
            Err(error) => {
                errors.push(prefix_record_error(&file.relative_path, error));
                rows.push(InterfaceProposalCheckRow {
                    path: file.relative_path.clone(),
                    file_hash: format_package_hash(&file.file_hash),
                    proposal_id: None,
                    module: None,
                    proposal_revision: None,
                    interface_status: None,
                });
            }
        }
    }
    (
        InterfaceProposalCheckSnapshot {
            proposal_count: discovery.proposal_count(),
            status_counts,
            proposal_rows: rows,
            proposal_set_hash: Some(format_package_hash(&discovery.proposal_set_hash)),
        },
        records,
        errors,
    )
}

fn empty_interface_proposal_snapshot() -> (
    InterfaceProposalCheckSnapshot,
    Vec<InterfaceProposalRecord>,
    Vec<InterfaceProposalError>,
) {
    (
        InterfaceProposalCheckSnapshot {
            proposal_count: 0,
            status_counts: InterfaceProposalStatusCounts {
                observed: 0,
                proposed: 0,
                adopted: 0,
                withdrawn: 0,
                superseded: 0,
            },
            proposal_rows: Vec::new(),
            proposal_set_hash: None,
        },
        Vec::new(),
        Vec::new(),
    )
}

fn interface_proposal_command_diagnostic(
    error: &InterfaceProposalError,
) -> InterfaceProposalCheckDiagnostic {
    InterfaceProposalCheckDiagnostic {
        category: error.category.as_str().to_owned(),
        reason: error.reason_code.as_str().to_owned(),
        path: error.path.clone(),
        field: error.field.clone(),
        expected: error.expected.clone(),
        actual: error.actual.clone(),
    }
}

fn interface_proposal_command_diagnostic_for_result(
    error: &InterfaceProposalError,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::InterfaceProposal,
        error.reason_code.as_str(),
    )
    .with_path(error.path.clone());
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field.clone());
    }
    if let Some(expected) = &error.expected {
        diagnostic = diagnostic.with_expected_value(expected.clone());
    }
    if let Some(actual) = &error.actual {
        diagnostic = diagnostic.with_actual_value(actual.clone());
    }
    diagnostic
}

/// Parse and resolve the exact NPA surface terms of one proposal.
///
/// The caller supplies the already authenticated, in-memory import context.
/// This function never reads a package root or source file, fetches Git or
/// network data, elaborates a proof, or accepts a certificate. It only uses
/// the Human frontend parser and resolver to check the proposal's intended
/// declaration boundary.
pub fn validate_interface_proposal_surface(
    proposal: &InterfaceProposal,
    verified_imports: &[VerifiedImport],
    imported_source_interfaces: &[HumanImportedSourceInterface],
) -> Result<(), InterfaceProposalError> {
    let resolves_names = matches!(
        proposal.interface_status,
        InterfaceProposalStatus::Proposed | InterfaceProposalStatus::Adopted
    );
    let complete_surface = matches!(
        proposal.interface_status,
        InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
            | InterfaceProposalStatus::Superseded
    );
    for (index, declaration) in proposal.declarations.iter().enumerate() {
        let path = format!("declarations[{index}]");
        let Some(signature) = declaration.signature.as_deref() else {
            if complete_surface {
                return Err(surface_error(
                    InterfaceProposalErrorCategory::Contract,
                    InterfaceProposalErrorReason::InvalidSignature,
                    format!("{path}.signature"),
                    "signature",
                    "exact nonempty NPA declaration signature",
                    "missing",
                ));
            }
            if let Some(body) = declaration.body.as_deref() {
                validate_surface_term(
                    body,
                    &format!("{path}.body"),
                    SurfaceTermKind::DefinitionBody,
                )?;
            }
            continue;
        };
        validate_surface_term(
            signature,
            &format!("{path}.signature"),
            SurfaceTermKind::Signature,
        )?;

        match declaration.kind {
            InterfaceProposalDeclarationKind::Definition => {
                if matches!(
                    proposal.interface_status,
                    InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
                ) && declaration.body.is_none()
                {
                    return Err(surface_error(
                        InterfaceProposalErrorCategory::Contract,
                        InterfaceProposalErrorReason::InvalidDefinitionBody,
                        format!("{path}.body"),
                        "body",
                        "exact nonempty NPA definition body",
                        "missing",
                    ));
                }
                if let Some(body) = declaration.body.as_deref() {
                    validate_surface_term(
                        body,
                        &format!("{path}.body"),
                        SurfaceTermKind::DefinitionBody,
                    )?;
                }
            }
            InterfaceProposalDeclarationKind::Inductive => {
                if matches!(
                    proposal.interface_status,
                    InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
                ) && declaration.family_members.is_empty()
                {
                    return Err(surface_error(
                        InterfaceProposalErrorCategory::Contract,
                        InterfaceProposalErrorReason::IncompleteFamily,
                        format!("{path}.family_members"),
                        "family_members",
                        "complete ordered canonical inductive family",
                        "missing",
                    ));
                }
                validate_surface_family_members(declaration, &path)?;
                if declaration.body.is_some() {
                    return Err(surface_error(
                        InterfaceProposalErrorCategory::Contract,
                        InterfaceProposalErrorReason::InvalidDefinitionBody,
                        format!("{path}.body"),
                        "body",
                        "omitted for an inductive declaration",
                        "present",
                    ));
                }
            }
            InterfaceProposalDeclarationKind::Theorem => {
                if declaration.body.is_some() {
                    return Err(surface_error(
                        InterfaceProposalErrorCategory::Contract,
                        InterfaceProposalErrorReason::InvalidDefinitionBody,
                        format!("{path}.body"),
                        "body",
                        "omitted for a theorem",
                        "present",
                    ));
                }
            }
        }

        if resolves_names {
            validate_resolved_declaration(
                proposal,
                index,
                declaration,
                verified_imports,
                imported_source_interfaces,
            )?;
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum SurfaceTermKind {
    Signature,
    DefinitionBody,
}

impl SurfaceTermKind {
    fn field(self) -> &'static str {
        match self {
            Self::Signature => "signature",
            Self::DefinitionBody => "body",
        }
    }

    fn syntax_reason(self) -> InterfaceProposalErrorReason {
        match self {
            Self::Signature => InterfaceProposalErrorReason::InvalidSignature,
            Self::DefinitionBody => InterfaceProposalErrorReason::InvalidDefinitionBody,
        }
    }

    fn placeholder_reason(self) -> InterfaceProposalErrorReason {
        match self {
            Self::Signature => InterfaceProposalErrorReason::PlaceholderSignature,
            Self::DefinitionBody => InterfaceProposalErrorReason::PlaceholderDefinitionBody,
        }
    }

    fn expected(self) -> &'static str {
        match self {
            Self::Signature => "exact nonempty NPA type expression",
            Self::DefinitionBody => "exact nonempty NPA term",
        }
    }
}

fn validate_surface_term(
    source: &str,
    path: &str,
    kind: SurfaceTermKind,
) -> Result<(), InterfaceProposalError> {
    if source.trim().is_empty() {
        return Err(surface_error(
            InterfaceProposalErrorCategory::Contract,
            kind.syntax_reason(),
            path.to_owned(),
            kind.field(),
            kind.expected(),
            "empty",
        ));
    }
    if is_surface_placeholder(source) {
        return Err(surface_error(
            InterfaceProposalErrorCategory::Contract,
            kind.placeholder_reason(),
            path.to_owned(),
            kind.field(),
            kind.expected(),
            source,
        ));
    }
    parse_human_term(FileId(0), source)
        .map(|_| ())
        .map_err(|diagnostic| frontend_parse_error(path, kind, diagnostic))
}

fn validate_surface_family_members(
    declaration: &InterfaceProposalDeclaration,
    path: &str,
) -> Result<(), InterfaceProposalError> {
    let mut seen = BTreeSet::new();
    for (index, member) in declaration.family_members.iter().enumerate() {
        if !seen.insert(member.as_str()) {
            return Err(surface_error(
                InterfaceProposalErrorCategory::Contract,
                InterfaceProposalErrorReason::DuplicateFamilyMember,
                format!("{path}.family_members[{index}]"),
                "family_members",
                "duplicate-free ordered canonical family",
                member,
            ));
        }
        if !Name::from_dotted(member).is_canonical() {
            return Err(surface_error(
                InterfaceProposalErrorCategory::Contract,
                InterfaceProposalErrorReason::InvalidFamily,
                format!("{path}.family_members[{index}]"),
                "family_members",
                "canonical generated declaration name",
                member,
            ));
        }
    }
    Ok(())
}

fn validate_resolved_declaration(
    proposal: &InterfaceProposal,
    target_index: usize,
    declaration: &InterfaceProposalDeclaration,
    verified_imports: &[VerifiedImport],
    imported_source_interfaces: &[HumanImportedSourceInterface],
) -> Result<(), InterfaceProposalError> {
    let (direct_verified_imports, direct_source_interfaces) =
        declared_import_context(proposal, verified_imports, imported_source_interfaces)?;
    let source = build_surface_source(proposal, target_index, None)?;
    let parsed =
        parse_human_module_with_source_interfaces(FileId(0), &source, &direct_source_interfaces)
            .map_err(|diagnostic| {
                frontend_surface_error(
                    proposal,
                    &format!("declarations[{target_index}].signature"),
                    SurfaceTermKind::Signature,
                    diagnostic,
                )
            })?;
    let expected_name = declaration.name.as_str();
    let target_item = parsed
        .items
        .iter()
        .find(|item| human_item_name(item).as_deref() == Some(expected_name));
    if !target_item.is_some_and(|item| item_kind_matches(item, declaration.kind)) {
        return Err(surface_error(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::InvalidSignature,
            format!("declarations[{target_index}].kind"),
            "kind",
            declaration.kind.as_str(),
            target_item
                .and_then(human_item_kind_name)
                .unwrap_or("missing target declaration"),
        ));
    }
    let resolved = resolve_human_module_with_source_interfaces(
        Name::from_dotted(&proposal.module),
        parsed,
        &direct_verified_imports,
        &direct_source_interfaces,
        &HumanCompileOptions::default(),
    )
    .map_err(|diagnostic| {
        frontend_surface_error(
            proposal,
            &format!("declarations[{target_index}].signature"),
            SurfaceTermKind::Signature,
            diagnostic,
        )
    })?;
    let expected_kind = match declaration.kind {
        InterfaceProposalDeclarationKind::Definition => HumanSourceDeclarationKind::Def,
        InterfaceProposalDeclarationKind::Inductive => HumanSourceDeclarationKind::Inductive,
        InterfaceProposalDeclarationKind::Theorem => HumanSourceDeclarationKind::Theorem,
    };
    let metadata = resolved
        .state
        .source_interfaces
        .current
        .declarations
        .iter()
        .find(|metadata| metadata.name.as_dotted() == expected_name);
    if !metadata.is_some_and(|metadata| metadata.kind == expected_kind) {
        return Err(surface_error(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::InvalidSignature,
            format!("declarations[{target_index}].kind"),
            "kind",
            declaration.kind.as_str(),
            metadata
                .map(|metadata| source_declaration_kind_name(metadata.kind))
                .unwrap_or("missing target declaration"),
        ));
    }
    if let Some(body) = declaration.body.as_deref() {
        let source = build_surface_source(proposal, target_index, Some(body))?;
        let parsed = parse_human_module_with_source_interfaces(
            FileId(0),
            &source,
            &direct_source_interfaces,
        )
        .map_err(|diagnostic| {
            frontend_surface_error(
                proposal,
                &format!("declarations[{target_index}].body"),
                SurfaceTermKind::DefinitionBody,
                diagnostic,
            )
        })?;
        resolve_human_module_with_source_interfaces(
            Name::from_dotted(&proposal.module),
            parsed,
            &direct_verified_imports,
            &direct_source_interfaces,
            &HumanCompileOptions::default(),
        )
        .map_err(|diagnostic| {
            frontend_surface_error(
                proposal,
                &format!("declarations[{target_index}].body"),
                SurfaceTermKind::DefinitionBody,
                diagnostic,
            )
        })?;
    }
    Ok(())
}

fn declared_import_context(
    proposal: &InterfaceProposal,
    verified_imports: &[VerifiedImport],
    imported_source_interfaces: &[HumanImportedSourceInterface],
) -> Result<(Vec<VerifiedImport>, Vec<HumanImportedSourceInterface>), InterfaceProposalError> {
    let mut direct_verified_imports = Vec::with_capacity(proposal.imports.len());
    let mut direct_source_interfaces = Vec::new();
    for (index, import) in proposal.imports.iter().enumerate() {
        let module = Name::from_dotted(import);
        let matches = verified_imports
            .iter()
            .filter(|verified| verified.module == module)
            .collect::<Vec<_>>();
        let Some(verified) = matches.first() else {
            return Err(surface_error(
                InterfaceProposalErrorCategory::Graph,
                InterfaceProposalErrorReason::ImportUnresolved,
                format!("imports[{index}]"),
                "imports",
                "exactly one supplied verified import interface",
                import,
            ));
        };
        if matches.len() != 1 {
            return Err(surface_error(
                InterfaceProposalErrorCategory::Graph,
                InterfaceProposalErrorReason::ImportUnresolved,
                format!("imports[{index}]"),
                "imports",
                "exactly one supplied verified import interface",
                "ambiguous supplied import interfaces",
            ));
        }
        direct_verified_imports.push((*verified).clone());
        direct_source_interfaces.extend(
            imported_source_interfaces
                .iter()
                .filter(|interface| interface.module == module)
                .cloned(),
        );
    }
    Ok((direct_verified_imports, direct_source_interfaces))
}

fn build_surface_source(
    proposal: &InterfaceProposal,
    target_index: usize,
    target_body: Option<&str>,
) -> Result<String, InterfaceProposalError> {
    let declaration_names = proposal
        .declarations
        .iter()
        .enumerate()
        .map(|(index, declaration)| (declaration.name.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let mut closure = BTreeSet::new();
    let mut pending = vec![target_index];
    while let Some(index) = pending.pop() {
        if !closure.insert(index) {
            continue;
        }
        for dependency in &proposal.declarations[index].depends_on {
            let Some(&dependency_index) = declaration_names.get(dependency.as_str()) else {
                return Err(surface_error(
                    InterfaceProposalErrorCategory::Graph,
                    InterfaceProposalErrorReason::UnresolvedDependency,
                    format!("declarations[{index}].depends_on"),
                    "depends_on",
                    "declaration name in this proposal",
                    dependency,
                ));
            };
            pending.push(dependency_index);
        }
    }

    let mut source = String::new();
    for import in &proposal.imports {
        source.push_str("import ");
        source.push_str(import);
        source.push('\n');
    }
    for (index, declaration) in proposal.declarations.iter().enumerate() {
        if closure.contains(&index) && index != target_index {
            append_surface_stub(&mut source, declaration, index);
        }
    }
    append_surface_target(
        &mut source,
        &proposal.declarations[target_index],
        target_body,
    );
    Ok(source)
}

/// Build the in-memory Human source used by the surface-drift checker.
///
/// Definitions retain their proposed bodies. Theorem declarations are emitted
/// as surface-only axioms so their proof terms are never elaborated or treated
/// as interface evidence.
pub(crate) fn build_surface_core_source(proposal: &InterfaceProposal) -> String {
    let mut source = String::new();
    for import in &proposal.imports {
        source.push_str("import ");
        source.push_str(import);
        source.push('\n');
    }
    for (index, declaration) in proposal.declarations.iter().enumerate() {
        match declaration.kind {
            InterfaceProposalDeclarationKind::Definition => {
                source.push_str("def ");
                source.push_str(&declaration.name);
                append_declaration_universe_params(
                    &mut source,
                    &declaration_universe_params(declaration),
                );
                source.push_str(" : ");
                source.push_str(declaration.signature.as_deref().unwrap_or("Sort 0"));
                source.push_str(" := ");
                source.push_str(declaration.body.as_deref().unwrap_or("Sort 0"));
                source.push('\n');
            }
            InterfaceProposalDeclarationKind::Theorem => {
                source.push_str("axiom ");
                source.push_str(&declaration.name);
                append_declaration_universe_params(
                    &mut source,
                    &declaration_universe_params(declaration),
                );
                source.push_str(" : ");
                source.push_str(declaration.signature.as_deref().unwrap_or("Sort 0"));
                source.push('\n');
            }
            InterfaceProposalDeclarationKind::Inductive => append_surface_inductive(
                &mut source,
                &declaration.name,
                declaration.signature.as_deref().unwrap_or("Sort 0"),
                &declaration.family_members,
                index,
                &declaration_universe_params(declaration),
            ),
        }
    }
    source
}

fn append_surface_stub(
    source: &mut String,
    declaration: &InterfaceProposalDeclaration,
    index: usize,
) {
    match declaration.kind {
        InterfaceProposalDeclarationKind::Inductive => append_surface_inductive(
            source,
            &declaration.name,
            "Sort 0",
            &declaration.family_members,
            index,
            &declaration_universe_params(declaration),
        ),
        InterfaceProposalDeclarationKind::Definition
        | InterfaceProposalDeclarationKind::Theorem => {
            source.push_str("axiom ");
            source.push_str(&declaration.name);
            append_declaration_universe_params(source, &declaration_universe_params(declaration));
            source.push_str(" : ");
            source.push_str(declaration.signature.as_deref().unwrap_or("Sort 0"));
            source.push('\n');
        }
    }
}

fn append_surface_target(
    source: &mut String,
    declaration: &InterfaceProposalDeclaration,
    target_body: Option<&str>,
) {
    match declaration.kind {
        InterfaceProposalDeclarationKind::Definition => {
            source.push_str("def ");
            source.push_str(&declaration.name);
            append_declaration_universe_params(source, &declaration_universe_params(declaration));
            source.push_str(" : ");
            source.push_str(declaration.signature.as_deref().unwrap_or("Sort 0"));
            source.push_str(" := ");
            source.push_str(target_body.unwrap_or("Sort 0"));
            source.push('\n');
        }
        InterfaceProposalDeclarationKind::Theorem => {
            source.push_str("theorem ");
            source.push_str(&declaration.name);
            append_declaration_universe_params(source, &declaration_universe_params(declaration));
            source.push_str(" : ");
            source.push_str(declaration.signature.as_deref().unwrap_or("Sort 0"));
            source.push_str(" := by simp-lite\n");
        }
        InterfaceProposalDeclarationKind::Inductive => append_surface_inductive(
            source,
            &declaration.name,
            declaration.signature.as_deref().unwrap_or("Sort 0"),
            &declaration.family_members,
            0,
            &declaration_universe_params(declaration),
        ),
    }
}

fn declaration_universe_params(declaration: &InterfaceProposalDeclaration) -> Vec<String> {
    let mut params = Vec::new();
    for term in [
        declaration.signature.as_deref(),
        declaration.body.as_deref(),
    ] {
        let Some(term) = term else {
            continue;
        };
        let Ok(expr) = parse_human_term(FileId(0), term) else {
            continue;
        };
        collect_human_universe_params(&expr, &mut params);
    }
    params
}

fn collect_human_universe_params(expr: &HumanExpr, params: &mut Vec<String>) {
    match expr {
        HumanExpr::Ident { universe_args, .. } => {
            if let Some(levels) = universe_args {
                for level in levels {
                    collect_human_level_params(level, params);
                }
            }
        }
        HumanExpr::Sort { level, .. } => collect_human_level_params(level, params),
        HumanExpr::App { func, arg, .. } => {
            collect_human_universe_params(func, params);
            collect_human_universe_params(arg, params);
        }
        HumanExpr::Lam { binders, body, .. } | HumanExpr::Pi { binders, body, .. } => {
            for binder in binders {
                if let Some(ty) = &binder.ty {
                    collect_human_universe_params(ty, params);
                }
            }
            collect_human_universe_params(body, params);
        }
        HumanExpr::Let {
            ty, value, body, ..
        } => {
            if let Some(ty) = ty {
                collect_human_universe_params(ty, params);
            }
            collect_human_universe_params(value, params);
            collect_human_universe_params(body, params);
        }
        HumanExpr::Annot { expr, ty, .. } => {
            collect_human_universe_params(expr, params);
            collect_human_universe_params(ty, params);
        }
        HumanExpr::Arrow {
            domain, codomain, ..
        } => {
            collect_human_universe_params(domain, params);
            collect_human_universe_params(codomain, params);
        }
        HumanExpr::Hole { .. } => {}
        HumanExpr::NotationApp { args, .. } => {
            for arg in args {
                collect_human_universe_params(arg, params);
            }
        }
    }
}

fn collect_human_level_params(level: &HumanLevel, params: &mut Vec<String>) {
    match level {
        HumanLevel::Nat { .. } => {}
        HumanLevel::Param { name, .. } => {
            if !params.iter().any(|param| param == name) {
                params.push(name.clone());
            }
        }
        HumanLevel::Succ { level, .. } => collect_human_level_params(level, params),
        HumanLevel::Max { lhs, rhs, .. } | HumanLevel::IMax { lhs, rhs, .. } => {
            collect_human_level_params(lhs, params);
            collect_human_level_params(rhs, params);
        }
    }
}

fn append_declaration_universe_params(source: &mut String, params: &[String]) {
    if params.is_empty() {
        return;
    }
    source.push_str(".{");
    source.push_str(&params.join(","));
    source.push('}');
}

fn append_surface_inductive(
    source: &mut String,
    name: &str,
    signature: &str,
    family_members: &[String],
    seed: usize,
    universe_params: &[String],
) {
    source.push_str("inductive ");
    source.push_str(name);
    append_declaration_universe_params(source, universe_params);
    source.push_str(" : ");
    source.push_str(signature);
    source.push_str(" where\n");
    let prefix = format!("{name}.");
    let mut constructor_count = 0;
    for member in family_members {
        let Some(child) = member.strip_prefix(&prefix) else {
            continue;
        };
        if child.is_empty() || child == "rec" {
            continue;
        }
        source.push_str("| ");
        source.push_str(child);
        source.push_str(" : ");
        source.push_str(name);
        source.push('\n');
        constructor_count += 1;
    }
    if constructor_count == 0 {
        source.push_str("| __npa_interface_surface_ctor_");
        source.push_str(&seed.to_string());
        source.push_str(" : ");
        source.push_str(name);
        source.push('\n');
    }
}

fn human_item_name(item: &HumanItem) -> Option<String> {
    match item {
        HumanItem::Def(definition) => Some(definition.declaration.name.as_dotted()),
        HumanItem::Theorem(declaration) => Some(declaration.name.as_dotted()),
        HumanItem::Inductive(declaration) => Some(declaration.name.as_dotted()),
        _ => None,
    }
}

fn item_kind_matches(item: &HumanItem, kind: InterfaceProposalDeclarationKind) -> bool {
    matches!(
        (item, kind),
        (
            HumanItem::Def(_),
            InterfaceProposalDeclarationKind::Definition
        ) | (
            HumanItem::Theorem(_),
            InterfaceProposalDeclarationKind::Theorem
        ) | (
            HumanItem::Inductive(_),
            InterfaceProposalDeclarationKind::Inductive
        )
    )
}

fn human_item_kind_name(item: &HumanItem) -> Option<&'static str> {
    match item {
        HumanItem::Def(_) => Some("definition"),
        HumanItem::Theorem(_) => Some("theorem"),
        HumanItem::Inductive(_) => Some("inductive"),
        _ => None,
    }
}

fn source_declaration_kind_name(kind: HumanSourceDeclarationKind) -> &'static str {
    match kind {
        HumanSourceDeclarationKind::Def => "definition",
        HumanSourceDeclarationKind::Theorem => "theorem",
        HumanSourceDeclarationKind::Inductive => "inductive",
        _ => "other",
    }
}

fn is_surface_placeholder(value: &str) -> bool {
    let lower = value.to_ascii_lowercase();
    value.contains("...")
        || value.contains('…')
        || value.contains("???")
        || lower.contains("todo")
        || lower.contains("placeholder")
        || lower.contains("not yet specified")
}

fn frontend_parse_error(
    path: &str,
    kind: SurfaceTermKind,
    diagnostic: HumanDiagnostic,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Contract,
        kind.syntax_reason(),
        path,
        Some(kind.field().to_owned()),
        Some(kind.expected().to_owned()),
        Some(diagnostic.message),
    )
}

fn frontend_surface_error(
    proposal: &InterfaceProposal,
    path: &str,
    kind: SurfaceTermKind,
    diagnostic: HumanDiagnostic,
) -> InterfaceProposalError {
    let unresolved = matches!(
        diagnostic.kind,
        HumanDiagnosticKind::ImportResolutionError
            | HumanDiagnosticKind::MissingVerifiedImport
            | HumanDiagnosticKind::UnknownNamespace
            | HumanDiagnosticKind::UnknownIdentifier
            | HumanDiagnosticKind::ForwardReference
            | HumanDiagnosticKind::AmbiguousName
            | HumanDiagnosticKind::AmbiguousConstructor
    );
    let local_name = unresolved
        && matches!(
            diagnostic.kind,
            HumanDiagnosticKind::UnknownIdentifier
                | HumanDiagnosticKind::ForwardReference
                | HumanDiagnosticKind::AmbiguousName
                | HumanDiagnosticKind::AmbiguousConstructor
        )
        && proposal.declarations.iter().any(|declaration| {
            diagnostic.message.contains(&declaration.name)
                || diagnostic.payload.as_ref().is_some_and(|payload| {
                    payload
                        .candidates
                        .iter()
                        .any(|candidate| candidate == &declaration.name)
                })
        });
    let reason = if local_name {
        InterfaceProposalErrorReason::UnresolvedDependency
    } else if unresolved {
        InterfaceProposalErrorReason::ImportUnresolved
    } else {
        kind.syntax_reason()
    };
    let category = if unresolved {
        InterfaceProposalErrorCategory::Graph
    } else {
        InterfaceProposalErrorCategory::Contract
    };
    InterfaceProposalError::new(
        category,
        reason,
        path,
        Some(kind.field().to_owned()),
        Some(if unresolved {
            "all referenced names resolve through the declared boundary".to_owned()
        } else {
            kind.expected().to_owned()
        }),
        Some(diagnostic.message),
    )
}

fn surface_error(
    category: InterfaceProposalErrorCategory,
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        category,
        reason,
        path,
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

/// Validate one parsed proposal set against a validated current package
/// manifest.
///
/// This is a deterministic, read-only catalog-boundary check. It validates
/// the proposal records themselves, their canonical paths, current catalog
/// change relations, proposal supersession links, declaration collisions, and
/// the module-level import graph. It does not read artifacts or certificates;
/// surface-term resolution remains the frontend-only check above.
pub fn validate_interface_proposal_catalog(
    records: &[InterfaceProposalRecord],
    manifest: &ValidatedPackageManifest,
) -> Result<(), InterfaceProposalError> {
    let mut ordered = (0..records.len()).collect::<Vec<_>>();
    ordered.sort_by(|left, right| {
        records[*left]
            .relative_path
            .as_bytes()
            .cmp(records[*right].relative_path.as_bytes())
    });

    for &index in &ordered {
        let record = &records[index];
        validate_interface_proposal(&record.proposal)
            .map_err(|error| prefix_record_error(&record.relative_path, error))?;
        validate_proposal_record_path(record)?;
    }

    let mut proposal_ids = BTreeMap::<String, usize>::new();
    let mut active_modules = BTreeMap::<String, usize>::new();
    for &index in &ordered {
        let proposal = &records[index].proposal;
        if let Some(previous_index) = proposal_ids.insert(proposal.proposal_id.clone(), index) {
            let reason = if is_terminal_status(proposal.interface_status)
                || is_terminal_status(records[previous_index].proposal.interface_status)
            {
                InterfaceProposalErrorReason::TerminalIdReused
            } else {
                InterfaceProposalErrorReason::ProposalIdReused
            };
            return Err(catalog_record_error(
                &records[index],
                reason,
                "proposal_id",
                "globally unique proposal ID",
                &proposal.proposal_id,
            ));
        }
        if is_active_status(proposal.interface_status) {
            if let Some(previous_index) = active_modules.insert(proposal.module.clone(), index) {
                return Err(catalog_record_error(
                    &records[index],
                    InterfaceProposalErrorReason::ActiveModuleCollision,
                    "module",
                    "unique active target module",
                    &format!(
                        "{} also targeted by {}",
                        proposal.module, records[previous_index].relative_path
                    ),
                ));
            }
        }
    }

    let current_modules = manifest
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.as_dotted())
        .collect::<BTreeSet<_>>();
    for &index in &ordered {
        if is_active_status(records[index].proposal.interface_status) {
            validate_catalog_change_relation(&records[index], &current_modules)?;
        }
    }
    validate_split_groups(records, &ordered)?;
    validate_supersession_links(records, &ordered, &proposal_ids)?;
    validate_catalog_declaration_collisions(records, &ordered, manifest, &current_modules)?;
    validate_proposal_import_graph(records, &ordered, manifest, &current_modules)?;
    Ok(())
}

/// Validate a current proposal snapshot against the caller-supplied
/// immediately preceding snapshot.
///
/// The two roots are canonicalized only to reject an accidental self
/// comparison. The caller remains responsible for selecting the immediate
/// predecessor; this function does not inspect Git, a history ledger, or a
/// remote repository. The proposal discoveries contain the exact file hashes
/// used for the per-record continuity checks.
pub fn validate_interface_proposal_transition(
    current_root: &Path,
    previous_root: &Path,
    current: &InterfaceProposalDiscovery,
    previous: &InterfaceProposalDiscovery,
) -> Result<(), InterfaceProposalError> {
    let current_root = canonical_transition_root(current_root, false)?;
    let previous_root = canonical_transition_root(previous_root, true)?;
    if current_root == previous_root {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            InterfaceProposalErrorReason::PreviousRootSameAsCurrent,
            "previous-proposal-root",
            Some("--previous-proposal-root".to_owned()),
            Some("different canonical proposal roots".to_owned()),
            Some("same as current proposal root".to_owned()),
        ));
    }

    let current_records = parse_interface_proposal_set(current)?;
    let previous_records =
        parse_interface_proposal_set(previous).map_err(previous_snapshot_validation_error)?;
    validate_interface_proposal_record_transition(&current_records, &previous_records)
}

/// Validate a pair of already parsed proposal records without accessing any
/// filesystem state.
pub fn validate_interface_proposal_record_transition(
    current: &[InterfaceProposalRecord],
    previous: &[InterfaceProposalRecord],
) -> Result<(), InterfaceProposalError> {
    validate_proposal_snapshot_records(current)?;
    validate_proposal_snapshot_records(previous).map_err(previous_snapshot_validation_error)?;

    let current_order = ordered_record_indices(current);
    let previous_order = ordered_record_indices(previous);
    let current_by_id = current
        .iter()
        .enumerate()
        .map(|(index, record)| (record.proposal.proposal_id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let previous_by_id = previous
        .iter()
        .enumerate()
        .map(|(index, record)| (record.proposal.proposal_id.clone(), index))
        .collect::<BTreeMap<_, _>>();

    for &previous_index in &previous_order {
        let previous_record = &previous[previous_index];
        let Some(&current_index) = current_by_id.get(&previous_record.proposal.proposal_id) else {
            return Err(transition_record_error(
                previous_record,
                InterfaceProposalErrorReason::PreviousRecordRemoved,
                "proposal_id",
                "every previous canonical record retained in current snapshot",
                &previous_record.proposal.proposal_id,
            ));
        };
        let current_record = &current[current_index];

        if is_terminal_status(previous_record.proposal.interface_status) {
            if current_record.relative_path != previous_record.relative_path
                || current_record.file_hash != previous_record.file_hash
                || current_record.proposal != previous_record.proposal
            {
                return Err(transition_record_error(
                    current_record,
                    InterfaceProposalErrorReason::TerminalRecordChanged,
                    "file_hash",
                    "terminal record byte-identical after first terminal snapshot",
                    "changed terminal record",
                ));
            }
            continue;
        }

        if current_record.relative_path != previous_record.relative_path
            || current_record.proposal.module != previous_record.proposal.module
        {
            return Err(transition_record_error(
                current_record,
                InterfaceProposalErrorReason::RecordIdentityChanged,
                "module",
                "unchanged proposal path and target module for one proposal ID",
                &format!(
                    "{} -> {}",
                    previous_record.proposal.module, current_record.proposal.module
                ),
            ));
        }

        let changed = current_record.file_hash != previous_record.file_hash
            || current_record.proposal != previous_record.proposal;
        if !changed {
            continue;
        }

        validate_revision_binding(current_record, previous_record)?;
        validate_status_transition(previous_record, current_record)?;

        if matches!(
            (
                previous_record.proposal.interface_status,
                current_record.proposal.interface_status,
            ),
            (
                InterfaceProposalStatus::Observed,
                InterfaceProposalStatus::Withdrawn
            ) | (
                InterfaceProposalStatus::Proposed,
                InterfaceProposalStatus::Withdrawn
            )
        ) && !same_withdrawal_surface(previous_record, current_record)
        {
            return Err(transition_record_error(
                current_record,
                InterfaceProposalErrorReason::WithdrawnSurfaceChanged,
                "withdrawal_rationale",
                "previous unadopted surface unchanged except revision, hash, status, and rationale",
                "declaration or import surface changed",
            ));
        }

        if previous_record.proposal.interface_status == InterfaceProposalStatus::Adopted {
            match current_record.proposal.interface_status {
                InterfaceProposalStatus::Proposed => {
                    validate_adopted_rework(previous_record, current_record)?;
                }
                InterfaceProposalStatus::Adopted => {
                    validate_readoption(previous_record, current_record)?;
                }
                InterfaceProposalStatus::Superseded
                    if !same_superseded_surface(previous_record, current_record) =>
                {
                    return Err(transition_record_error(
                        current_record,
                        InterfaceProposalErrorReason::TerminalRecordChanged,
                        "declarations",
                        "adopted surface retained when superseded",
                        "adopted surface changed while becoming terminal",
                    ));
                }
                _ => {}
            }
        }
    }

    for &current_index in &current_order {
        let current_record = &current[current_index];
        if previous_by_id.contains_key(&current_record.proposal.proposal_id) {
            continue;
        }
        if current_record.proposal.proposal_revision != 1 {
            return Err(transition_contract_error(
                current_record,
                InterfaceProposalErrorReason::InvalidRevision,
                "proposal_revision",
                "revision 1 for a newly introduced proposal record",
                &current_record.proposal.proposal_revision.to_string(),
            ));
        }
        if current_record.proposal.previous_proposal_hash.is_some() {
            return Err(transition_contract_error(
                current_record,
                InterfaceProposalErrorReason::InvalidRevision,
                "previous_proposal_hash",
                "omitted for a newly introduced revision-1 proposal record",
                "present",
            ));
        }
    }

    Ok(())
}

fn validate_proposal_snapshot_records(
    records: &[InterfaceProposalRecord],
) -> Result<(), InterfaceProposalError> {
    let ordered = ordered_record_indices(records);
    let mut proposal_ids = BTreeMap::<String, usize>::new();
    let mut active_modules = BTreeMap::<String, usize>::new();

    for &index in &ordered {
        let record = &records[index];
        validate_interface_proposal(&record.proposal)
            .map_err(|error| prefix_record_error(&record.relative_path, error))?;
        validate_proposal_record_path(record)?;
        if let Some(previous_index) =
            proposal_ids.insert(record.proposal.proposal_id.clone(), index)
        {
            let reason = if is_terminal_status(record.proposal.interface_status)
                || is_terminal_status(records[previous_index].proposal.interface_status)
            {
                InterfaceProposalErrorReason::TerminalIdReused
            } else {
                InterfaceProposalErrorReason::ProposalIdReused
            };
            return Err(snapshot_record_error(
                record,
                reason,
                "proposal_id",
                "globally unique proposal ID",
                &record.proposal.proposal_id,
            ));
        }
        if is_active_status(record.proposal.interface_status) {
            if let Some(previous_index) =
                active_modules.insert(record.proposal.module.clone(), index)
            {
                return Err(snapshot_record_error(
                    record,
                    InterfaceProposalErrorReason::ActiveModuleCollision,
                    "module",
                    "unique active target module",
                    &format!(
                        "{} also targeted by {}",
                        record.proposal.module, records[previous_index].relative_path
                    ),
                ));
            }
        }
    }
    validate_split_groups(records, &ordered)?;
    validate_supersession_links(records, &ordered, &proposal_ids)
}

fn ordered_record_indices(records: &[InterfaceProposalRecord]) -> Vec<usize> {
    let mut ordered = (0..records.len()).collect::<Vec<_>>();
    ordered.sort_by(|left, right| {
        records[*left]
            .relative_path
            .as_bytes()
            .cmp(records[*right].relative_path.as_bytes())
    });
    ordered
}

fn validate_revision_binding(
    current: &InterfaceProposalRecord,
    previous: &InterfaceProposalRecord,
) -> Result<(), InterfaceProposalError> {
    let expected_revision = previous.proposal.proposal_revision.checked_add(1);
    if expected_revision != Some(current.proposal.proposal_revision) {
        return Err(transition_record_error(
            current,
            InterfaceProposalErrorReason::RevisionNotIncremented,
            "proposal_revision",
            &format!(
                "exactly {} after previous revision",
                previous.proposal.proposal_revision.saturating_add(1)
            ),
            &current.proposal.proposal_revision.to_string(),
        ));
    }
    if current.proposal.previous_proposal_hash != Some(previous.file_hash) {
        return Err(transition_record_error(
            current,
            InterfaceProposalErrorReason::PreviousHashMismatch,
            "previous_proposal_hash",
            &format_package_hash(&previous.file_hash),
            current
                .proposal
                .previous_proposal_hash
                .as_ref()
                .map(format_package_hash)
                .as_deref()
                .unwrap_or("missing"),
        ));
    }
    Ok(())
}

fn validate_status_transition(
    previous: &InterfaceProposalRecord,
    current: &InterfaceProposalRecord,
) -> Result<(), InterfaceProposalError> {
    let old_status = previous.proposal.interface_status;
    let new_status = current.proposal.interface_status;
    let valid = old_status == new_status
        || matches!(
            (old_status, new_status),
            (
                InterfaceProposalStatus::Observed,
                InterfaceProposalStatus::Proposed
            ) | (
                InterfaceProposalStatus::Observed,
                InterfaceProposalStatus::Withdrawn
            ) | (
                InterfaceProposalStatus::Proposed,
                InterfaceProposalStatus::Adopted
            ) | (
                InterfaceProposalStatus::Proposed,
                InterfaceProposalStatus::Withdrawn
            ) | (
                InterfaceProposalStatus::Adopted,
                InterfaceProposalStatus::Proposed
            ) | (
                InterfaceProposalStatus::Adopted,
                InterfaceProposalStatus::Adopted
            ) | (
                InterfaceProposalStatus::Adopted,
                InterfaceProposalStatus::Superseded
            )
        );
    if valid {
        return Ok(());
    }
    Err(transition_record_error(
        current,
        InterfaceProposalErrorReason::InvalidStatusTransition,
        "interface_status",
        "observed -> proposed/withdrawn, proposed -> adopted/withdrawn, adopted -> proposed/adopted/superseded, or unchanged",
        &format!("{} -> {}", old_status.as_str(), new_status.as_str()),
    ))
}

fn validate_adopted_rework(
    previous: &InterfaceProposalRecord,
    current: &InterfaceProposalRecord,
) -> Result<(), InterfaceProposalError> {
    let same_module_revision = current.proposal.change_kind == previous.proposal.change_kind
        || (current.proposal.change_kind == InterfaceProposalChangeKind::Revise
            && current.proposal.source_modules == vec![current.proposal.module.clone()]);
    if same_module_revision {
        return Ok(());
    }
    Err(transition_record_error(
        current,
        InterfaceProposalErrorReason::InvalidStatusTransition,
        "change_kind",
        "same-module adopted rework retaining its change kind or using revise[module]",
        current.proposal.change_kind.as_str(),
    ))
}

fn validate_readoption(
    previous: &InterfaceProposalRecord,
    current: &InterfaceProposalRecord,
) -> Result<(), InterfaceProposalError> {
    let refreshed_adoption = current.proposal.adoption_date != previous.proposal.adoption_date
        || current.proposal.adoption_rationale != previous.proposal.adoption_rationale;
    if !refreshed_adoption {
        return Err(transition_record_error(
            current,
            InterfaceProposalErrorReason::AdoptedReworkNotReadopted,
            "adoption_date",
            "fresh adoption_date and adoption_rationale after adopted rework",
            "unchanged adoption metadata",
        ));
    }
    if current
        .proposal
        .re_adoption_rationale
        .as_deref()
        .is_none_or(|rationale| rationale.trim().is_empty())
    {
        return Err(transition_record_error(
            current,
            InterfaceProposalErrorReason::AdoptedReworkNotReadopted,
            "re_adoption_rationale",
            "nonempty explanation of the completed re-adoption",
            "missing or empty",
        ));
    }
    Ok(())
}

fn same_withdrawal_surface(
    previous: &InterfaceProposalRecord,
    current: &InterfaceProposalRecord,
) -> bool {
    let mut previous = previous.proposal.clone();
    let mut current = current.proposal.clone();
    for proposal in [&mut previous, &mut current] {
        proposal.proposal_revision = 0;
        proposal.previous_proposal_hash = None;
        proposal.interface_status = InterfaceProposalStatus::Observed;
        proposal.withdrawal_rationale = None;
    }
    previous == current
}

fn same_superseded_surface(
    previous: &InterfaceProposalRecord,
    current: &InterfaceProposalRecord,
) -> bool {
    let mut previous = previous.proposal.clone();
    let mut current = current.proposal.clone();
    for proposal in [&mut previous, &mut current] {
        proposal.proposal_revision = 0;
        proposal.previous_proposal_hash = None;
        proposal.interface_status = InterfaceProposalStatus::Adopted;
        proposal.superseded_by = None;
    }
    previous == current
}

fn canonical_transition_root(
    root: &Path,
    previous: bool,
) -> Result<PathBuf, InterfaceProposalError> {
    let (reason, path, field) = if previous {
        (
            InterfaceProposalErrorReason::PreviousRootNotDirectory,
            "previous-proposal-root",
            "--previous-proposal-root",
        )
    } else {
        (
            InterfaceProposalErrorReason::ProposalRootNotDirectory,
            "current-proposal-root",
            "--proposal-root",
        )
    };
    let canonical = fs::canonicalize(root).map_err(|error| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            reason,
            path,
            Some(field.to_owned()),
            Some("existing directory".to_owned()),
            Some(io_error_kind(&error)),
        )
    })?;
    let metadata = fs::metadata(&canonical).map_err(|error| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            reason,
            path,
            Some(field.to_owned()),
            Some("readable directory".to_owned()),
            Some(io_error_kind(&error)),
        )
    })?;
    if !metadata.is_dir() {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            reason,
            path,
            Some(field.to_owned()),
            Some("directory".to_owned()),
            Some("non-directory".to_owned()),
        ));
    }
    Ok(canonical)
}

fn previous_snapshot_validation_error(error: InterfaceProposalError) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Comparison,
        InterfaceProposalErrorReason::PreviousSnapshotInvalid,
        error.path,
        error.field,
        Some("independently valid proposal snapshot".to_owned()),
        Some(error.reason_code.as_str().to_owned()),
    )
}

fn transition_record_error(
    record: &InterfaceProposalRecord,
    reason: InterfaceProposalErrorReason,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Comparison,
        reason,
        record.relative_path.as_str(),
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

fn snapshot_record_error(
    record: &InterfaceProposalRecord,
    reason: InterfaceProposalErrorReason,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        catalog_reason_category(reason),
        reason,
        record.relative_path.as_str(),
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

fn transition_contract_error(
    record: &InterfaceProposalRecord,
    reason: InterfaceProposalErrorReason,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Contract,
        reason,
        record.relative_path.as_str(),
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

fn validate_proposal_record_path(
    record: &InterfaceProposalRecord,
) -> Result<(), InterfaceProposalError> {
    let module = &record.proposal.module;
    if !module.starts_with("Mathlib.") || !Name::from_dotted(module).is_canonical() {
        return Err(catalog_record_error(
            record,
            InterfaceProposalErrorReason::InvalidModuleName,
            "module",
            "canonical Mathlib.* module name",
            module,
        ));
    }
    let expected = format!("{}.toml", module.replace('.', "/"));
    if record.relative_path != expected {
        return Err(catalog_record_error(
            record,
            InterfaceProposalErrorReason::ModulePathMismatch,
            "module",
            &expected,
            module,
        ));
    }
    Ok(())
}

fn validate_catalog_change_relation(
    record: &InterfaceProposalRecord,
    current_modules: &BTreeSet<String>,
) -> Result<(), InterfaceProposalError> {
    let proposal = &record.proposal;
    match proposal.change_kind {
        InterfaceProposalChangeKind::Add => {
            if current_modules.contains(&proposal.module)
                && !is_materialized_adopted_add(proposal, current_modules)
            {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetExists,
                    "module",
                    "target module absent from current catalog",
                    &proposal.module,
                ));
            }
        }
        InterfaceProposalChangeKind::Revise => {
            if !current_modules.contains(&proposal.module) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetMissing,
                    "module",
                    "target module present in current catalog",
                    &proposal.module,
                ));
            }
        }
        InterfaceProposalChangeKind::Rename | InterfaceProposalChangeKind::Replace => {
            let Some(source) = proposal.source_modules.first() else {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::InvalidSourceModules,
                    "source_modules",
                    "one source module for rename or replace",
                    "empty",
                ));
            };
            if !current_modules.contains(source) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetMissing,
                    "source_modules[0]",
                    "source module present in current catalog",
                    source,
                ));
            }
            if current_modules.contains(&proposal.module) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetExists,
                    "module",
                    "new target module absent from current catalog",
                    &proposal.module,
                ));
            }
        }
        InterfaceProposalChangeKind::Split => {
            let Some(source) = proposal.source_modules.first() else {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::InvalidSourceModules,
                    "source_modules",
                    "one source module for split",
                    "empty",
                ));
            };
            if !current_modules.contains(source) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetMissing,
                    "source_modules[0]",
                    "source module present in current catalog",
                    source,
                ));
            }
            if current_modules.contains(&proposal.module) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetExists,
                    "module",
                    "split target module absent from current catalog",
                    &proposal.module,
                ));
            }
        }
        InterfaceProposalChangeKind::Merge => {
            for (index, source) in proposal.source_modules.iter().enumerate() {
                if !current_modules.contains(source) {
                    return Err(catalog_record_error(
                        record,
                        InterfaceProposalErrorReason::CatalogTargetMissing,
                        &format!("source_modules[{index}]"),
                        "every source module present in current catalog",
                        source,
                    ));
                }
            }
            if current_modules.contains(&proposal.module) {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogTargetExists,
                    "module",
                    "merge target module absent from current catalog",
                    &proposal.module,
                ));
            }
            if proposal
                .source_modules
                .iter()
                .any(|source| source == &proposal.module)
            {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::CatalogSourceCardinality,
                    "source_modules",
                    "merge target distinct from every source module",
                    &proposal.module,
                ));
            }
        }
    }
    Ok(())
}

/// An adopted `add` proposal remains a useful historical curation record after
/// its target is materialized. The exact target surface is checked separately
/// by `check-interface-proposal-surface`; this metadata-only validator must not
/// reject the canonical proposal merely because the later catalog transaction
/// succeeded.
fn is_materialized_adopted_add(
    proposal: &InterfaceProposal,
    current_modules: &BTreeSet<String>,
) -> bool {
    proposal.interface_status == InterfaceProposalStatus::Adopted
        && proposal.change_kind == InterfaceProposalChangeKind::Add
        && current_modules.contains(&proposal.module)
}

fn validate_split_groups(
    records: &[InterfaceProposalRecord],
    ordered: &[usize],
) -> Result<(), InterfaceProposalError> {
    let mut groups = BTreeMap::<(String, String), Vec<usize>>::new();
    for &index in ordered {
        let proposal = &records[index].proposal;
        if proposal.interface_status == InterfaceProposalStatus::Withdrawn
            || proposal.interface_status == InterfaceProposalStatus::Superseded
            || proposal.change_kind != InterfaceProposalChangeKind::Split
        {
            continue;
        }
        let Some(group) = proposal.change_group.as_deref() else {
            return Err(catalog_record_error(
                &records[index],
                InterfaceProposalErrorReason::InvalidChangeGroup,
                "change_group",
                "nonempty group for an active split",
                "missing",
            ));
        };
        let Some(source) = proposal.source_modules.first() else {
            return Err(catalog_record_error(
                &records[index],
                InterfaceProposalErrorReason::InvalidSourceModules,
                "source_modules",
                "one source module for split",
                "empty",
            ));
        };
        groups
            .entry((source.clone(), group.to_owned()))
            .or_default()
            .push(index);
    }
    for ((source, group), members) in groups {
        if members.len() < 2 {
            let index = members[0];
            return Err(catalog_record_error(
                &records[index],
                InterfaceProposalErrorReason::InvalidChangeGroup,
                "change_group",
                "at least two active split targets for one source module and group",
                &format!("{source}:{group}"),
            ));
        }
    }
    Ok(())
}

fn validate_supersession_links(
    records: &[InterfaceProposalRecord],
    ordered: &[usize],
    proposal_ids: &BTreeMap<String, usize>,
) -> Result<(), InterfaceProposalError> {
    for &index in ordered {
        let proposal = &records[index].proposal;
        for (link_index, successor_id) in proposal.supersedes.iter().enumerate() {
            let Some(&old_index) = proposal_ids.get(successor_id) else {
                return Err(catalog_record_error(
                    &records[index],
                    InterfaceProposalErrorReason::SupersessionNotReciprocal,
                    &format!("supersedes[{link_index}]"),
                    "proposal ID present as a superseded historical record",
                    successor_id,
                ));
            };
            let old = &records[old_index].proposal;
            let reciprocal = old.interface_status == InterfaceProposalStatus::Superseded
                && old.module != proposal.module
                && old.superseded_by.as_deref().is_some_and(|successors| {
                    successors.iter().any(|id| id == &proposal.proposal_id)
                });
            if !reciprocal {
                return Err(catalog_record_error(
                    &records[index],
                    InterfaceProposalErrorReason::SupersessionNotReciprocal,
                    &format!("supersedes[{link_index}]"),
                    "superseded record with reciprocal successor link and a different target module",
                    successor_id,
                ));
            }
        }
    }

    for &index in ordered {
        let proposal = &records[index].proposal;
        if proposal.interface_status != InterfaceProposalStatus::Superseded {
            continue;
        }
        let Some(successors) = proposal.superseded_by.as_deref() else {
            return Err(catalog_record_error(
                &records[index],
                InterfaceProposalErrorReason::SupersessionNotReciprocal,
                "superseded_by",
                "successor IDs present in the current proposal set",
                "missing",
            ));
        };
        for (successor_index, successor_id) in successors.iter().enumerate() {
            let Some(&successor_record_index) = proposal_ids.get(successor_id) else {
                return Err(catalog_record_error(
                    &records[index],
                    InterfaceProposalErrorReason::SupersessionNotReciprocal,
                    &format!("superseded_by[{successor_index}]"),
                    "proposal ID present in the current proposal set",
                    successor_id,
                ));
            };
            let successor = &records[successor_record_index].proposal;
            if successor.module == proposal.module
                || !successor
                    .supersedes
                    .iter()
                    .any(|id| id == &proposal.proposal_id)
            {
                return Err(catalog_record_error(
                    &records[index],
                    InterfaceProposalErrorReason::SupersessionNotReciprocal,
                    &format!("superseded_by[{successor_index}]"),
                    "successor with reciprocal supersedes link and a different target module",
                    successor_id,
                ));
            }
        }
    }
    Ok(())
}

fn validate_catalog_declaration_collisions(
    records: &[InterfaceProposalRecord],
    ordered: &[usize],
    manifest: &ValidatedPackageManifest,
    current_modules: &BTreeSet<String>,
) -> Result<(), InterfaceProposalError> {
    let catalog_declarations = manifest
        .manifest()
        .modules
        .iter()
        .flat_map(catalog_module_declarations)
        .collect::<BTreeMap<_, _>>();
    let mut active_declarations = BTreeMap::<String, usize>::new();

    for &index in ordered {
        let record = &records[index];
        if !is_active_status(record.proposal.interface_status) {
            continue;
        }
        let replacing_same_module = record.proposal.change_kind
            == InterfaceProposalChangeKind::Revise
            && record
                .proposal
                .source_modules
                .first()
                .is_some_and(|source| source == &record.proposal.module);
        let materialized_adopted_add =
            is_materialized_adopted_add(&record.proposal, current_modules);
        for (declaration_index, declaration) in record.proposal.declarations.iter().enumerate() {
            let names = std::iter::once(declaration.name.clone())
                .chain(declaration.family_members.iter().cloned());
            for name in names {
                let qualified = qualify_proposal_member(&record.proposal.module, &name);
                if catalog_declarations.contains_key(&qualified)
                    && !replacing_same_module
                    && !materialized_adopted_add
                {
                    return Err(catalog_record_error(
                        record,
                        InterfaceProposalErrorReason::CatalogDeclarationCollision,
                        &format!("declarations[{declaration_index}].name"),
                        "declaration name absent from unaffected catalog modules",
                        &qualified,
                    ));
                }
                if let Some(previous_index) = active_declarations.insert(qualified.clone(), index) {
                    return Err(catalog_record_error(
                        record,
                        InterfaceProposalErrorReason::CatalogDeclarationCollision,
                        &format!("declarations[{declaration_index}].name"),
                        "globally unique active proposal declaration name",
                        &format!(
                            "{} also declared by {}",
                            qualified, records[previous_index].relative_path
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn catalog_module_declarations(
    module: &PackageModule,
) -> BTreeMap<String, InterfaceProposalDeclarationKind> {
    let mut declarations = BTreeMap::new();
    for (kind, names) in [
        (
            InterfaceProposalDeclarationKind::Inductive,
            module.inductives.as_deref(),
        ),
        (
            InterfaceProposalDeclarationKind::Definition,
            module.definitions.as_deref(),
        ),
        (
            InterfaceProposalDeclarationKind::Theorem,
            module.theorems.as_deref(),
        ),
    ] {
        if let Some(names) = names {
            for name in names {
                declarations.insert(
                    qualify_catalog_member(&module.module.as_dotted(), name),
                    kind,
                );
            }
        }
    }
    declarations
}

fn qualify_catalog_member(module: &str, name: &Name) -> String {
    let dotted = name.as_dotted();
    if dotted == module || dotted.starts_with(&format!("{module}.")) {
        dotted
    } else {
        format!("{module}.{dotted}")
    }
}

fn qualify_proposal_member(module: &str, name: &str) -> String {
    if name == module || name.starts_with(&format!("{module}.")) {
        name.to_owned()
    } else {
        format!("{module}.{name}")
    }
}

fn validate_proposal_import_graph(
    records: &[InterfaceProposalRecord],
    ordered: &[usize],
    manifest: &ValidatedPackageManifest,
    current_modules: &BTreeSet<String>,
) -> Result<(), InterfaceProposalError> {
    let external_modules = manifest
        .manifest()
        .imports
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|import| import.module.as_dotted())
        .collect::<BTreeSet<_>>();
    let adopted_modules = records
        .iter()
        .enumerate()
        .filter(|(_, record)| record.proposal.interface_status == InterfaceProposalStatus::Adopted)
        .map(|(index, record)| (record.proposal.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut proposal_graph = BTreeMap::<String, BTreeSet<String>>::new();

    for &index in ordered {
        let record = &records[index];
        if !matches!(
            record.proposal.interface_status,
            InterfaceProposalStatus::Proposed | InterfaceProposalStatus::Adopted
        ) {
            continue;
        }
        for (import_index, import) in record.proposal.imports.iter().enumerate() {
            if import == &record.proposal.module {
                return Err(catalog_record_error(
                    record,
                    InterfaceProposalErrorReason::ImportCycle,
                    &format!("imports[{import_index}]"),
                    "acyclic import boundary without a self-import",
                    import,
                ));
            }
            if current_modules.contains(import) || external_modules.contains(import) {
                continue;
            }
            if adopted_modules.contains_key(import) {
                proposal_graph
                    .entry(record.proposal.module.clone())
                    .or_default()
                    .insert(import.clone());
                continue;
            }
            return Err(catalog_record_error(
                record,
                InterfaceProposalErrorReason::ImportUnresolved,
                &format!("imports[{import_index}]"),
                "current catalog module, immutable package import, or adopted proposal module",
                import,
            ));
        }
    }

    if let Some(cycle) = find_import_cycle(&proposal_graph) {
        let source_module = &cycle[0];
        let next_module = &cycle[1];
        let Some(&source_index) = adopted_modules.get(source_module) else {
            return Err(catalog_graph_error(
                InterfaceProposalErrorReason::ImportCycle,
                "imports",
                "acyclic proposed/adopted proposal import graph",
                &cycle.join(" -> "),
            ));
        };
        let record = &records[source_index];
        let import_index = record
            .proposal
            .imports
            .iter()
            .position(|import| import == next_module)
            .unwrap_or(0);
        return Err(catalog_record_error(
            record,
            InterfaceProposalErrorReason::ImportCycle,
            &format!("imports[{import_index}]"),
            "acyclic proposed/adopted proposal import graph",
            &cycle.join(" -> "),
        ));
    }
    Ok(())
}

fn find_import_cycle(graph: &BTreeMap<String, BTreeSet<String>>) -> Option<Vec<String>> {
    let mut states = BTreeMap::<String, ImportVisitState>::new();
    let mut path = Vec::new();
    let mut positions = BTreeMap::<String, usize>::new();
    for node in graph.keys() {
        if states
            .get(node)
            .copied()
            .unwrap_or(ImportVisitState::Unvisited)
            == ImportVisitState::Unvisited
        {
            if let Some(cycle) =
                find_import_cycle_from(node, graph, &mut states, &mut path, &mut positions)
            {
                return Some(cycle);
            }
        }
    }
    None
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ImportVisitState {
    Unvisited,
    Visiting,
    Visited,
}

fn find_import_cycle_from(
    node: &str,
    graph: &BTreeMap<String, BTreeSet<String>>,
    states: &mut BTreeMap<String, ImportVisitState>,
    path: &mut Vec<String>,
    positions: &mut BTreeMap<String, usize>,
) -> Option<Vec<String>> {
    states.insert(node.to_owned(), ImportVisitState::Visiting);
    positions.insert(node.to_owned(), path.len());
    path.push(node.to_owned());
    for next in graph.get(node).into_iter().flat_map(|edges| edges.iter()) {
        match states
            .get(next)
            .copied()
            .unwrap_or(ImportVisitState::Unvisited)
        {
            ImportVisitState::Unvisited => {
                if let Some(cycle) = find_import_cycle_from(next, graph, states, path, positions) {
                    return Some(cycle);
                }
            }
            ImportVisitState::Visiting => {
                let start = positions[next];
                let mut cycle = path[start..].to_vec();
                cycle.push(next.clone());
                return Some(cycle);
            }
            ImportVisitState::Visited => {}
        }
    }
    path.pop();
    positions.remove(node);
    states.insert(node.to_owned(), ImportVisitState::Visited);
    None
}

fn is_active_status(status: InterfaceProposalStatus) -> bool {
    matches!(
        status,
        InterfaceProposalStatus::Observed
            | InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
    )
}

fn is_terminal_status(status: InterfaceProposalStatus) -> bool {
    matches!(
        status,
        InterfaceProposalStatus::Withdrawn | InterfaceProposalStatus::Superseded
    )
}

fn prefix_record_error(path: &str, error: InterfaceProposalError) -> InterfaceProposalError {
    let field = if error.path == "$" {
        error.field
    } else {
        Some(error.path.clone())
    };
    InterfaceProposalError::new(
        error.category,
        error.reason_code,
        path,
        field,
        error.expected,
        error.actual,
    )
}

fn catalog_record_error(
    record: &InterfaceProposalRecord,
    reason: InterfaceProposalErrorReason,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        catalog_reason_category(reason),
        reason,
        record.relative_path.as_str(),
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

fn catalog_reason_category(reason: InterfaceProposalErrorReason) -> InterfaceProposalErrorCategory {
    match reason {
        InterfaceProposalErrorReason::InvalidModuleName
        | InterfaceProposalErrorReason::ModulePathMismatch
        | InterfaceProposalErrorReason::InvalidChangeGroup
        | InterfaceProposalErrorReason::DuplicateDeclarationName => {
            InterfaceProposalErrorCategory::Contract
        }
        InterfaceProposalErrorReason::ProposalIdReused
        | InterfaceProposalErrorReason::TerminalIdReused => {
            InterfaceProposalErrorCategory::Lifecycle
        }
        InterfaceProposalErrorReason::SupersessionNotReciprocal => {
            InterfaceProposalErrorCategory::Comparison
        }
        InterfaceProposalErrorReason::ImportUnresolved
        | InterfaceProposalErrorReason::ImportCycle => InterfaceProposalErrorCategory::Graph,
        _ => InterfaceProposalErrorCategory::Catalog,
    }
}

fn catalog_graph_error(
    reason: InterfaceProposalErrorReason,
    path: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Graph,
        reason,
        path,
        None,
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

/// Resolve an optional proposal-root path beneath a real package root.
///
/// The default is `interface-proposals`. Absolute paths and `..` components
/// are rejected as path escapes. Existing symlink components are rejected;
/// this function never creates a missing directory.
pub fn resolve_interface_proposal_root(
    root: &Path,
    proposal_root: Option<&Path>,
) -> Result<PathBuf, InterfaceProposalError> {
    let root_metadata = fs::metadata(root).map_err(|error| {
        root_io_error(
            InterfaceProposalErrorReason::RootNotDirectory,
            error,
            "package root directory",
        )
    })?;
    if !root_metadata.is_dir() {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            InterfaceProposalErrorReason::RootNotDirectory,
            "<root>",
            Some("--root".to_owned()),
            Some("real directory".to_owned()),
            Some("non-directory".to_owned()),
        ));
    }
    let real_root = fs::canonicalize(root).map_err(|error| {
        root_io_error(
            InterfaceProposalErrorReason::RootNotDirectory,
            error,
            "canonical package root directory",
        )
    })?;

    let requested = proposal_root.unwrap_or_else(|| Path::new(DEFAULT_PROPOSAL_ROOT));
    let relative = validate_root_relative_path(requested)?;
    let mut current = real_root.clone();
    let mut relative_prefix = PathBuf::new();
    for component in relative.components() {
        let Component::Normal(component) = component else {
            continue;
        };
        current.push(component);
        relative_prefix.push(component);
        let metadata = fs::symlink_metadata(&current).map_err(|error| {
            proposal_root_io_error(
                &relative_prefix,
                error,
                InterfaceProposalErrorReason::ProposalRootNotDirectory,
            )
        })?;
        if metadata.file_type().is_symlink() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::SymlinkEntry,
                path_string_or_placeholder(&relative_prefix),
                None,
                Some("real non-symlink entry"),
                Some("symlink"),
            ));
        }
        if !metadata.is_dir() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::ProposalRootNotDirectory,
                path_string_or_placeholder(&relative_prefix),
                Some("--proposal-root"),
                Some("real directory"),
                Some("non-directory"),
            ));
        }
    }

    let metadata = fs::symlink_metadata(&current).map_err(|error| {
        proposal_root_io_error(
            &relative,
            error,
            InterfaceProposalErrorReason::ProposalRootNotDirectory,
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(discovery_error(
            InterfaceProposalErrorReason::ProposalRootNotDirectory,
            path_string_or_placeholder(&relative),
            Some("--proposal-root"),
            Some("real directory"),
            Some("non-directory"),
        ));
    }
    if current.strip_prefix(&real_root).is_err() {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathEscape,
            "proposal-root".to_owned(),
            Some("--proposal-root"),
            Some("path confined beneath --root"),
            Some("escaped path"),
        ));
    }
    Ok(current)
}

/// Scan one proposal root and compute its deterministic proposal-set hash.
///
/// `proposal_root` is relative to `root` when supplied. The scanner reads no
/// files outside the resolved root, excludes README/generated files by
/// construction, and does not create or write any path.
pub fn discover_interface_proposal_set(
    root: &Path,
    proposal_root: Option<&Path>,
) -> Result<InterfaceProposalDiscovery, InterfaceProposalError> {
    let proposal_root = resolve_interface_proposal_root(root, proposal_root)?;
    discover_resolved_interface_proposal_set(&proposal_root)
}

fn discover_resolved_interface_proposal_set(
    proposal_root: &Path,
) -> Result<InterfaceProposalDiscovery, InterfaceProposalError> {
    let module_root = proposal_root.join(CANONICAL_MODULE_ROOT);
    let module_relative = PathBuf::from(CANONICAL_MODULE_ROOT);
    let module_metadata = match fs::symlink_metadata(&module_root) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(build_discovery(Vec::new(), 0));
        }
        Err(error) => {
            return Err(proposal_root_io_error(
                &module_relative,
                error,
                InterfaceProposalErrorReason::ReadFailed,
            ));
        }
    };
    if module_metadata.file_type().is_symlink() {
        return Err(discovery_error(
            InterfaceProposalErrorReason::SymlinkEntry,
            CANONICAL_MODULE_ROOT.to_owned(),
            None,
            Some("real non-symlink directory"),
            Some("symlink"),
        ));
    }
    if !module_metadata.is_dir() {
        return Err(discovery_error(
            InterfaceProposalErrorReason::NonRegularEntry,
            CANONICAL_MODULE_ROOT.to_owned(),
            None,
            Some("directory"),
            Some("non-directory"),
        ));
    }

    let mut files = Vec::new();
    let mut total_file_bytes = 0usize;
    scan_module_tree(
        &module_root,
        &module_relative,
        proposal_root,
        &mut files,
        &mut total_file_bytes,
    )?;
    files.sort_by(|left, right| {
        left.relative_path
            .as_bytes()
            .cmp(right.relative_path.as_bytes())
    });
    Ok(build_discovery(files, total_file_bytes))
}

fn resolve_previous_interface_proposal_root(
    package_root: &Path,
    requested: &Path,
) -> Result<PathBuf, InterfaceProposalError> {
    let candidate = if requested.is_absolute() {
        requested.to_path_buf()
    } else {
        package_root.join(requested)
    };
    let metadata = fs::symlink_metadata(&candidate).map_err(|error| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            InterfaceProposalErrorReason::PreviousRootNotDirectory,
            "previous-proposal-root",
            Some("--previous-proposal-root".to_owned()),
            Some("real directory".to_owned()),
            Some(io_error_kind(&error)),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            InterfaceProposalErrorReason::PreviousRootNotDirectory,
            "previous-proposal-root",
            Some("--previous-proposal-root".to_owned()),
            Some("real directory".to_owned()),
            Some(if metadata.file_type().is_symlink() {
                "symlink".to_owned()
            } else {
                "non-directory".to_owned()
            }),
        ));
    }
    fs::canonicalize(&candidate).map_err(|error| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Io,
            InterfaceProposalErrorReason::PreviousRootNotDirectory,
            "previous-proposal-root",
            Some("--previous-proposal-root".to_owned()),
            Some("canonical real directory".to_owned()),
            Some(io_error_kind(&error)),
        )
    })
}

fn build_discovery(
    files: Vec<InterfaceProposalDiscoveredFile>,
    total_file_bytes: usize,
) -> InterfaceProposalDiscovery {
    let proposal_set_hash = proposal_set_hash(&files);
    InterfaceProposalDiscovery {
        files,
        total_file_bytes,
        proposal_set_hash,
    }
}

fn scan_module_tree(
    directory: &Path,
    relative_directory: &Path,
    proposal_root: &Path,
    files: &mut Vec<InterfaceProposalDiscoveredFile>,
    total_file_bytes: &mut usize,
) -> Result<(), InterfaceProposalError> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| {
            proposal_root_io_error(
                relative_directory,
                error,
                InterfaceProposalErrorReason::ReadFailed,
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            proposal_root_io_error(
                relative_directory,
                error,
                InterfaceProposalErrorReason::ReadFailed,
            )
        })?;
    entries.sort_by(|left, right| {
        raw_os_bytes(&left.file_name()).cmp(&raw_os_bytes(&right.file_name()))
    });

    for entry in entries {
        let name = entry.file_name();
        let relative_path = relative_directory.join(&name);
        let display_path = validate_discovered_relative_path(&relative_path)?;
        let full_path = proposal_root.join(&relative_path);
        if full_path.strip_prefix(proposal_root).is_err() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::PathEscape,
                display_path,
                None,
                Some("path confined beneath proposal root"),
                Some("escaped path"),
            ));
        }
        let metadata = fs::symlink_metadata(&full_path).map_err(|error| {
            proposal_root_io_error(
                &relative_path,
                error,
                InterfaceProposalErrorReason::ReadFailed,
            )
        })?;
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::SymlinkEntry,
                display_path,
                None,
                Some("real non-symlink entry"),
                Some("symlink"),
            ));
        }
        if file_type.is_dir() {
            scan_module_tree(
                &full_path,
                &relative_path,
                proposal_root,
                files,
                total_file_bytes,
            )?;
            continue;
        }
        if !file_type.is_file() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::NonRegularEntry,
                display_path,
                None,
                Some("regular file or directory"),
                Some("non-regular entry"),
            ));
        }
        if relative_path.extension().and_then(OsStr::to_str) != Some("toml") {
            return Err(discovery_error(
                InterfaceProposalErrorReason::NoncanonicalExtension,
                display_path,
                None,
                Some(".toml"),
                Some("non-canonical extension"),
            ));
        }
        if files.len() >= MAX_PROPOSAL_FILES {
            let expected = MAX_PROPOSAL_FILES.to_string();
            let actual = (files.len() + 1).to_string();
            return Err(discovery_error(
                InterfaceProposalErrorReason::ProposalCountExceeded,
                display_path,
                None,
                Some(&expected),
                Some(&actual),
            ));
        }
        let metadata_bytes = metadata.len();
        if metadata_bytes > MAX_PROPOSAL_FILE_BYTES as u64 {
            return Err(resource_error(
                InterfaceProposalErrorReason::ProposalFileBytesExceeded,
                display_path,
                MAX_PROPOSAL_FILE_BYTES,
                metadata_bytes,
            ));
        }
        let metadata_total = total_file_bytes
            .checked_add(metadata_bytes as usize)
            .ok_or_else(|| {
                resource_error(
                    InterfaceProposalErrorReason::ProposalSetBytesExceeded,
                    display_path.clone(),
                    MAX_PROPOSAL_SET_BYTES,
                    u64::MAX,
                )
            })?;
        if metadata_total > MAX_PROPOSAL_SET_BYTES {
            return Err(resource_error(
                InterfaceProposalErrorReason::ProposalSetBytesExceeded,
                display_path.clone(),
                MAX_PROPOSAL_SET_BYTES,
                metadata_total as u64,
            ));
        }
        let bytes = read_regular_file_no_follow(&full_path).map_err(|error| {
            proposal_root_io_error(
                &relative_path,
                error,
                InterfaceProposalErrorReason::ReadFailed,
            )
        })?;
        if bytes.len() > MAX_PROPOSAL_FILE_BYTES {
            return Err(resource_error(
                InterfaceProposalErrorReason::ProposalFileBytesExceeded,
                display_path,
                MAX_PROPOSAL_FILE_BYTES,
                bytes.len() as u64,
            ));
        }
        if std::str::from_utf8(&bytes).is_err() {
            return Err(discovery_error(
                InterfaceProposalErrorReason::InvalidUtf8,
                display_path,
                None,
                Some("UTF-8 TOML bytes"),
                Some("invalid UTF-8"),
            ));
        }
        let next_total = total_file_bytes.checked_add(bytes.len()).ok_or_else(|| {
            resource_error(
                InterfaceProposalErrorReason::ProposalSetBytesExceeded,
                display_path.clone(),
                MAX_PROPOSAL_SET_BYTES,
                u64::MAX,
            )
        })?;
        if next_total > MAX_PROPOSAL_SET_BYTES {
            return Err(resource_error(
                InterfaceProposalErrorReason::ProposalSetBytesExceeded,
                display_path,
                MAX_PROPOSAL_SET_BYTES,
                next_total as u64,
            ));
        }
        *total_file_bytes = next_total;
        files.push(InterfaceProposalDiscoveredFile {
            relative_path: validate_discovered_relative_path(&relative_path)?,
            file_hash: interface_proposal_file_hash(&bytes),
            bytes,
        });
    }
    Ok(())
}

fn proposal_set_hash(files: &[InterfaceProposalDiscoveredFile]) -> PackageHash {
    let mut hasher = Sha256::new();
    hasher.update(PROPOSAL_SET_HASH_SCHEMA);
    for file in files {
        hasher.update(file.relative_path.as_bytes());
        hasher.update(b"\t");
        hasher.update(format_package_hash(&file.file_hash).as_bytes());
        hasher.update(b"\n");
    }
    let digest = hasher.finalize();
    let mut bytes = [0_u8; 32];
    bytes.copy_from_slice(&digest);
    PackageHash::new(bytes)
}

fn validate_root_relative_path(path: &Path) -> Result<PathBuf, InterfaceProposalError> {
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::Prefix(_) | Component::RootDir | Component::ParentDir
            )
        })
    {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathEscape,
            "proposal-root".to_owned(),
            Some("--proposal-root"),
            Some("relative path confined beneath --root"),
            Some("absolute or parent path"),
        ));
    }
    let Some(raw_path) = path.to_str() else {
        return Err(discovery_error(
            InterfaceProposalErrorReason::InvalidPathUtf8,
            "<invalid-utf8>".to_owned(),
            Some("--proposal-root"),
            Some("UTF-8 relative path"),
            Some("invalid UTF-8 path"),
        ));
    };
    let display = canonical_path_text(raw_path);
    if has_noncanonical_separator(&display) {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathEscape,
            "proposal-root".to_owned(),
            Some("--proposal-root"),
            Some("relative path using `/` separators"),
            Some("backslash separator"),
        ));
    }
    if display.len() > MAX_PATH_BYTES {
        return Err(resource_error(
            InterfaceProposalErrorReason::PathBytesExceeded,
            "proposal-root".to_owned(),
            MAX_PATH_BYTES,
            display.len() as u64,
        ));
    }
    if display
        .bytes()
        .any(|byte| byte == b'\t' || byte == b'\n' || byte == b'\r')
    {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathContainsTabOrNewline,
            "proposal-root".to_owned(),
            Some("--proposal-root"),
            Some("path without tab or newline"),
            Some("control character"),
        ));
    }
    Ok(path.to_path_buf())
}

fn validate_discovered_relative_path(path: &Path) -> Result<String, InterfaceProposalError> {
    let Some(path) = path.to_str() else {
        return Err(discovery_error(
            InterfaceProposalErrorReason::InvalidPathUtf8,
            "<invalid-utf8>".to_owned(),
            None,
            Some("UTF-8 relative path"),
            Some("invalid UTF-8 path"),
        ));
    };
    let path = canonical_path_text(path);
    if has_noncanonical_separator(&path) {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathEscape,
            bounded_path(&path),
            None,
            Some("relative path using `/` separators"),
            Some("backslash separator"),
        ));
    }
    if path.len() > MAX_PATH_BYTES {
        return Err(resource_error(
            InterfaceProposalErrorReason::PathBytesExceeded,
            bounded_path(&path),
            MAX_PATH_BYTES,
            path.len() as u64,
        ));
    }
    if path
        .bytes()
        .any(|byte| byte == b'\t' || byte == b'\n' || byte == b'\r')
    {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathContainsTabOrNewline,
            bounded_path(&path),
            None,
            Some("path without tab or newline"),
            Some("control character"),
        ));
    }
    if Path::new(&path).is_absolute()
        || Path::new(&path).components().any(|component| {
            matches!(
                component,
                Component::Prefix(_) | Component::RootDir | Component::ParentDir
            )
        })
    {
        return Err(discovery_error(
            InterfaceProposalErrorReason::PathEscape,
            bounded_path(&path),
            None,
            Some("relative path beneath proposal root"),
            Some("escaped path"),
        ));
    }
    Ok(path)
}

fn path_string_or_placeholder(path: &Path) -> String {
    path.to_str()
        .map(canonical_path_text)
        .map(|value| bounded_path(&value))
        .unwrap_or_else(|| "<invalid-utf8>".to_owned())
}

fn canonical_path_text(path: &str) -> String {
    #[cfg(windows)]
    {
        path.replace('\\', "/")
    }
    #[cfg(not(windows))]
    {
        path.to_owned()
    }
}

fn has_noncanonical_separator(path: &str) -> bool {
    #[cfg(windows)]
    {
        let _ = path;
        false
    }
    #[cfg(not(windows))]
    {
        path.contains('\\')
    }
}

fn bounded_path(path: &str) -> String {
    if path.len() <= MAX_PATH_BYTES {
        return path.to_owned();
    }
    let mut end = MAX_PATH_BYTES;
    while !path.is_char_boundary(end) {
        end -= 1;
    }
    path[..end].to_owned()
}

fn raw_os_bytes(value: &OsStr) -> Vec<u8> {
    #[cfg(unix)]
    {
        value.as_bytes().to_vec()
    }
    #[cfg(not(unix))]
    {
        value.to_string_lossy().as_bytes().to_vec()
    }
}

fn read_regular_file_no_follow(path: &Path) -> io::Result<Vec<u8>> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_NOFOLLOW);
    let file = options.open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "proposal entry is not a regular file",
        ));
    }
    let capacity = metadata.len().min(MAX_PROPOSAL_FILE_BYTES as u64 + 1) as usize;
    let mut bytes = Vec::with_capacity(capacity);
    file.take(MAX_PROPOSAL_FILE_BYTES as u64 + 1)
        .read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn discovery_error(
    reason: InterfaceProposalErrorReason,
    path: String,
    field: Option<&str>,
    expected: Option<&str>,
    actual: Option<&str>,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        discovery_category(reason),
        reason,
        path,
        field.map(str::to_owned),
        expected.map(str::to_owned),
        actual.map(str::to_owned),
    )
}

fn resource_error(
    reason: InterfaceProposalErrorReason,
    path: String,
    expected: usize,
    actual: u64,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Resource,
        reason,
        path,
        None,
        Some(expected.to_string()),
        Some(actual.to_string()),
    )
}

fn discovery_category(reason: InterfaceProposalErrorReason) -> InterfaceProposalErrorCategory {
    match reason {
        InterfaceProposalErrorReason::InvalidUtf8 => InterfaceProposalErrorCategory::Syntax,
        InterfaceProposalErrorReason::InvalidPathUtf8
        | InterfaceProposalErrorReason::PathContainsTabOrNewline
        | InterfaceProposalErrorReason::SymlinkEntry
        | InterfaceProposalErrorReason::NonRegularEntry
        | InterfaceProposalErrorReason::PathEscape
        | InterfaceProposalErrorReason::NoncanonicalExtension
        | InterfaceProposalErrorReason::ProposalCountExceeded
        | InterfaceProposalErrorReason::ProposalFileBytesExceeded
        | InterfaceProposalErrorReason::ProposalSetBytesExceeded => {
            InterfaceProposalErrorCategory::Discovery
        }
        InterfaceProposalErrorReason::ProposalRootNotDirectory
        | InterfaceProposalErrorReason::ReadFailed => InterfaceProposalErrorCategory::Io,
        _ => InterfaceProposalErrorCategory::Discovery,
    }
}

fn root_io_error(
    reason: InterfaceProposalErrorReason,
    error: io::Error,
    expected: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Io,
        reason,
        "<root>",
        Some("--root".to_owned()),
        Some(expected.to_owned()),
        Some(io_error_kind(&error)),
    )
}

fn proposal_root_io_error(
    path: &Path,
    error: io::Error,
    reason: InterfaceProposalErrorReason,
) -> InterfaceProposalError {
    discovery_error(
        reason,
        path_string_or_placeholder(path),
        Some("--proposal-root"),
        Some("readable real directory"),
        Some(&io_error_kind(&error)),
    )
}

fn io_error_kind(error: &io::Error) -> String {
    bounded_value(&format!("{:?}", error.kind()))
}

fn bounded_value(value: &str) -> String {
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        return value.to_owned();
    }
    let mut end = MAX_DIAGNOSTIC_VALUE_BYTES;
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    value[..end].to_owned()
}

#[cfg(test)]
mod discovery {
    use std::{
        ffi::OsString,
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
        time::{SystemTime, UNIX_EPOCH},
    };

    use npa_package::{format_package_hash, package_file_hash};

    use super::*;

    #[cfg(unix)]
    use std::os::unix::ffi::OsStringExt;

    struct TempRoot {
        path: PathBuf,
    }

    impl TempRoot {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let counter = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "npa-interface-discovery-{}-{nonce}-{counter}",
                std::process::id()
            ));
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }
    }

    impl Drop for TempRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn proposal_root(temp: &TempRoot) -> PathBuf {
        let root = temp.path.join("interface-proposals").join("Mathlib");
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn scans_only_canonical_toml_files_in_relative_byte_order() {
        let temp = TempRoot::new();
        let mathlib = proposal_root(&temp);
        fs::create_dir_all(mathlib.join("Logic")).unwrap();
        fs::write(mathlib.join("Z.toml"), b"z\n").unwrap();
        fs::write(mathlib.join("Logic").join("A.toml"), b"a\n").unwrap();
        fs::write(
            temp.path.join("interface-proposals").join("README.md"),
            b"ignored\n",
        )
        .unwrap();
        fs::create_dir_all(temp.path.join("interface-proposals").join("generated")).unwrap();
        fs::write(
            temp.path
                .join("interface-proposals")
                .join("generated/index.json"),
            b"ignored\n",
        )
        .unwrap();

        let first = discover_interface_proposal_set(&temp.path, None).unwrap();
        let second = discover_interface_proposal_set(&temp.path, None).unwrap();
        assert_eq!(first, second);
        assert_eq!(first.proposal_count(), 2);
        assert_eq!(
            first
                .files
                .iter()
                .map(|file| file.relative_path.as_str())
                .collect::<Vec<_>>(),
            vec!["Mathlib/Logic/A.toml", "Mathlib/Z.toml"]
        );
        assert_eq!(first.files[0].bytes(), b"a\n");

        let rows = format!(
            "npa.mathlib.interface_proposal_set.v1\nMathlib/Logic/A.toml\t{}\nMathlib/Z.toml\t{}\n",
            format_package_hash(&package_file_hash(b"a\n")),
            format_package_hash(&package_file_hash(b"z\n")),
        );
        assert_eq!(first.proposal_set_hash, package_file_hash(rows.as_bytes()));
    }

    #[test]
    fn rejects_missing_or_escaped_roots_without_creating_paths() {
        let temp = TempRoot::new();
        let missing = temp.path.join("missing");
        let error =
            discover_interface_proposal_set(&temp.path, Some(Path::new("missing"))).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProposalRootNotDirectory
        );
        assert!(!missing.exists());

        let error =
            resolve_interface_proposal_root(&temp.path, Some(Path::new("../outside"))).unwrap_err();
        assert_eq!(error.reason_code, InterfaceProposalErrorReason::PathEscape);
        let error =
            resolve_interface_proposal_root(&temp.path, Some(Path::new("/tmp"))).unwrap_err();
        assert_eq!(error.reason_code, InterfaceProposalErrorReason::PathEscape);
    }

    #[test]
    fn rejects_wrong_extensions_invalid_utf8_and_control_paths() {
        let temp = TempRoot::new();
        let mathlib = proposal_root(&temp);
        fs::write(mathlib.join("README.md"), b"not canonical").unwrap();
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::NoncanonicalExtension
        );

        fs::remove_file(mathlib.join("README.md")).unwrap();
        fs::write(mathlib.join("bad\t.toml"), b"valid utf8").unwrap();
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PathContainsTabOrNewline
        );

        fs::remove_file(mathlib.join("bad\t.toml")).unwrap();
        fs::write(mathlib.join("invalid.toml"), [0xff, 0xfe]).unwrap();
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(error.reason_code, InterfaceProposalErrorReason::InvalidUtf8);
        assert_eq!(error.category, InterfaceProposalErrorCategory::Syntax);
    }

    #[test]
    fn rejects_symlinked_entries_and_non_directory_module_root() {
        let temp = TempRoot::new();
        let mathlib = proposal_root(&temp);
        fs::write(mathlib.join("target.toml"), b"valid").unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink(mathlib.join("target.toml"), mathlib.join("link.toml")).unwrap();
        #[cfg(unix)]
        {
            assert!(fs::symlink_metadata(mathlib.join("link.toml"))
                .unwrap()
                .file_type()
                .is_symlink());
            let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
            assert_eq!(
                error.reason_code,
                InterfaceProposalErrorReason::SymlinkEntry
            );

            fs::remove_file(mathlib.join("link.toml")).unwrap();
            let outside = temp.path.join("outside");
            fs::create_dir_all(&outside).unwrap();
            std::os::unix::fs::symlink(&outside, mathlib.join("link-dir")).unwrap();
            let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
            assert_eq!(
                error.reason_code,
                InterfaceProposalErrorReason::SymlinkEntry
            );
            fs::remove_file(mathlib.join("link-dir")).unwrap();
        }

        fs::remove_dir_all(&mathlib).unwrap();
        fs::write(
            temp.path.join("interface-proposals").join("Mathlib"),
            b"not a directory",
        )
        .unwrap();
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::NonRegularEntry
        );
    }

    #[test]
    fn enforces_file_and_set_byte_limits() {
        let temp = TempRoot::new();
        let mathlib = proposal_root(&temp);
        fs::write(
            mathlib.join("large.toml"),
            vec![b'a'; MAX_PROPOSAL_FILE_BYTES + 1],
        )
        .unwrap();
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProposalFileBytesExceeded
        );

        fs::remove_file(mathlib.join("large.toml")).unwrap();
        for index in 0..=(MAX_PROPOSAL_SET_BYTES / MAX_PROPOSAL_FILE_BYTES) {
            fs::write(
                mathlib.join(format!("set-{index}.toml")),
                vec![b'a'; MAX_PROPOSAL_FILE_BYTES],
            )
            .unwrap();
        }
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProposalSetBytesExceeded
        );
    }

    #[test]
    fn enforces_proposal_count_limit() {
        let temp = TempRoot::new();
        let mathlib = proposal_root(&temp);
        for index in 0..=MAX_PROPOSAL_FILES {
            fs::write(mathlib.join(format!("count-{index:04}.toml")), []).unwrap();
        }
        let error = discover_interface_proposal_set(&temp.path, None).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProposalCountExceeded
        );
    }

    #[test]
    fn enforces_canonical_path_limit_and_rejects_invalid_utf8_paths() {
        let long_path = PathBuf::from("Mathlib").join("x".repeat(MAX_PATH_BYTES));
        let error = validate_discovered_relative_path(&long_path).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PathBytesExceeded
        );

        #[cfg(unix)]
        {
            let invalid_name = OsString::from_vec(vec![b'i', 0xff, b'.', b't', b'o', b'm', b'l']);
            let invalid_path = PathBuf::from("Mathlib").join(invalid_name);
            let error = validate_discovered_relative_path(&invalid_path).unwrap_err();
            assert_eq!(
                error.reason_code,
                InterfaceProposalErrorReason::InvalidPathUtf8
            );
        }
    }
}

#[cfg(test)]
mod surface {
    use super::*;
    use npa_package::{InterfaceProposalChangeKind, InterfaceProposalSurface};

    fn empty_verified_import(module: &str) -> VerifiedImport {
        VerifiedImport {
            module: Name::from_dotted(module),
            export_hash: [0; 32],
            certificate_hash: None,
            exports: Vec::new(),
            decl_interface_hashes: BTreeMap::new(),
            kernel_decls: Vec::new(),
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn base_proposal(status: InterfaceProposalStatus) -> InterfaceProposal {
        InterfaceProposal {
            schema: npa_package::INTERFACE_PROPOSAL_SCHEMA.to_owned(),
            proposal_id: "Mathlib.Test.Surface".to_owned(),
            proposal_revision: 1,
            previous_proposal_hash: None,
            module: "Mathlib.Test.Surface".to_owned(),
            change_kind: InterfaceProposalChangeKind::Add,
            source_modules: Vec::new(),
            change_group: None,
            interface_status: status,
            proof_evidence: false,
            summary: "A frontend surface fixture.".to_owned(),
            scope: "Only the frontend surface fixture.".to_owned(),
            imports: Vec::new(),
            adoption_date: None,
            adoption_rationale: None,
            re_adoption_rationale: None,
            withdrawal_rationale: None,
            alternatives_review: Some("No material alternative was selected.".to_owned()),
            supersedes: Vec::new(),
            superseded_by: None,
            declarations: Vec::new(),
            observations: Vec::new(),
            proof_references: Vec::new(),
            alternatives: Vec::new(),
        }
    }

    fn declaration(
        name: &str,
        kind: InterfaceProposalDeclarationKind,
        signature: &str,
        body: Option<&str>,
        depends_on: &[&str],
    ) -> InterfaceProposalDeclaration {
        InterfaceProposalDeclaration {
            name: name.to_owned(),
            kind,
            surface: InterfaceProposalSurface::Public,
            signature: Some(signature.to_owned()),
            body: body.map(ToOwned::to_owned),
            family_members: Vec::new(),
            semantic_role: "A focused surface fixture.".to_owned(),
            depends_on: depends_on.iter().map(|name| (*name).to_owned()).collect(),
            evidence_ids: Vec::new(),
            foundation_exception: Some("A self-contained frontend fixture.".to_owned()),
            support_rationale: None,
            proof_reference_ids: Vec::new(),
            proof_reference_exception: None,
        }
    }

    #[test]
    fn accepts_real_surface_terms_and_only_declared_local_dependencies() {
        let mut proposal = base_proposal(InterfaceProposalStatus::Proposed);
        proposal.declarations = vec![
            declaration(
                "helper",
                InterfaceProposalDeclarationKind::Definition,
                "Sort 0",
                Some("Sort 0"),
                &[],
            ),
            declaration(
                "target",
                InterfaceProposalDeclarationKind::Definition,
                "forall (x : Nat), helper",
                Some("fun x => helper"),
                &["helper"],
            ),
        ];
        validate_interface_proposal_surface(&proposal, &[], &[]).unwrap();
    }

    #[test]
    fn accepts_the_current_pilot_surface_with_supplied_import_context() {
        let proposal = npa_package::parse_interface_proposal_str(include_str!(
            "../../../../npa-mathlib/interface-proposals/Mathlib/Logic/Function/Basic.toml"
        ))
        .unwrap();
        npa_package::validate_interface_proposal(&proposal).unwrap();
        let imports = [
            empty_verified_import("Mathlib.Logic.Eq"),
            empty_verified_import("Std.Logic.Eq"),
        ];
        validate_interface_proposal_surface(&proposal, &imports, &[]).unwrap();
    }

    #[test]
    fn preserves_universe_parameters_when_building_pilot_surface_source() {
        let proposal = npa_package::parse_interface_proposal_str(include_str!(
            "../../../../npa-mathlib/interface-proposals/Mathlib/Logic/Function/Basic.toml"
        ))
        .unwrap();
        let source = build_surface_core_source(&proposal);
        assert!(source.contains("def comp.{u1,u2,u3} :"), "{source}");
        assert!(
            source.contains("axiom comp_assoc.{u1,u2,u3,u4} :"),
            "{source}"
        );
    }

    #[test]
    fn distinguishes_surface_syntax_local_dependency_and_import_failures() {
        let mut syntax = base_proposal(InterfaceProposalStatus::Proposed);
        syntax.declarations = vec![declaration(
            "target",
            InterfaceProposalDeclarationKind::Definition,
            "forall (",
            Some("Sort 0"),
            &[],
        )];
        let error = validate_interface_proposal_surface(&syntax, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidSignature
        );

        syntax.declarations[0].signature = Some("...".to_owned());
        let error = validate_interface_proposal_surface(&syntax, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PlaceholderSignature
        );

        let mut local = base_proposal(InterfaceProposalStatus::Proposed);
        local.declarations = vec![
            declaration(
                "helper",
                InterfaceProposalDeclarationKind::Definition,
                "Sort 0",
                Some("Sort 0"),
                &[],
            ),
            declaration(
                "target",
                InterfaceProposalDeclarationKind::Definition,
                "helper",
                Some("Sort 0"),
                &[],
            ),
        ];
        let error = validate_interface_proposal_surface(&local, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::UnresolvedDependency
        );

        let mut external = base_proposal(InterfaceProposalStatus::Proposed);
        external.declarations = vec![declaration(
            "target",
            InterfaceProposalDeclarationKind::Definition,
            "Mathlib.Unprovided.value",
            Some("Sort 0"),
            &[],
        )];
        let error = validate_interface_proposal_surface(&external, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ImportUnresolved
        );
    }

    #[test]
    fn classifies_definition_body_resolution_failures_at_the_body_path() {
        let mut proposal = base_proposal(InterfaceProposalStatus::Proposed);
        proposal.declarations = vec![declaration(
            "target",
            InterfaceProposalDeclarationKind::Definition,
            "Nat",
            Some("Mathlib.Unprovided.body"),
            &[],
        )];
        let error = validate_interface_proposal_surface(&proposal, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ImportUnresolved
        );
        assert_eq!(error.path, "declarations[0].body");
    }

    #[test]
    fn rejects_an_undeclared_import_before_frontend_resolution() {
        let mut proposal = base_proposal(InterfaceProposalStatus::Proposed);
        proposal.imports = vec!["Mathlib.Test.Missing".to_owned()];
        proposal.declarations = vec![declaration(
            "target",
            InterfaceProposalDeclarationKind::Definition,
            "Nat",
            Some("Sort 0"),
            &[],
        )];
        let error = validate_interface_proposal_surface(&proposal, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ImportUnresolved
        );
        assert_eq!(error.path, "imports[0]");
    }

    #[test]
    fn keeps_superseded_validation_syntax_only_and_checks_inductive_kind() {
        let mut superseded = base_proposal(InterfaceProposalStatus::Superseded);
        superseded.declarations = vec![declaration(
            "historical",
            InterfaceProposalDeclarationKind::Definition,
            "Retired.Imported.Type",
            Some("Retired.Imported.body"),
            &[],
        )];
        validate_interface_proposal_surface(&superseded, &[], &[]).unwrap();

        let mut inductive = base_proposal(InterfaceProposalStatus::Adopted);
        let mut declaration = declaration(
            "thing",
            InterfaceProposalDeclarationKind::Inductive,
            "Sort 0",
            None,
            &[],
        );
        declaration.family_members = vec!["thing.mk".to_owned(), "thing.rec".to_owned()];
        inductive.declarations = vec![declaration];
        validate_interface_proposal_surface(&inductive, &[], &[]).unwrap();
    }

    #[test]
    fn rejects_kind_mismatched_definition_body() {
        let mut proposal = base_proposal(InterfaceProposalStatus::Proposed);
        proposal.declarations = vec![declaration(
            "theorem_like",
            InterfaceProposalDeclarationKind::Theorem,
            "Nat",
            Some("Sort 0"),
            &[],
        )];
        let error = validate_interface_proposal_surface(&proposal, &[], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidDefinitionBody
        );
    }
}

#[cfg(test)]
mod catalog {
    use super::*;

    fn manifest(modules: &[&str], external_eq: bool) -> ValidatedPackageManifest {
        let mut source = String::from(
            r#"schema = "npa.package.v0.1"
package = "npa-mathlib"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
        );
        for module in modules {
            let path = module.replace('.', "/");
            source.push_str(&format!(
                r#"
[[modules]]
module = "{module}"
source = "{path}/source.npa"
certificate = "{path}/certificate.npcert"
expected_source_hash = "sha256:{hash}"
expected_certificate_file_hash = "sha256:{hash}"
expected_export_hash = "sha256:{hash}"
expected_axiom_report_hash = "sha256:{hash}"
expected_certificate_hash = "sha256:{hash}"
imports = []
definitions = ["catalog_decl"]
theorems = []
axioms = []
"#,
                hash = "0000000000000000000000000000000000000000000000000000000000000000"
            ));
        }
        if external_eq {
            source.push_str(
                r#"
[[imports]]
module = "Std.Logic.Eq"
package = "npa-std"
version = "0.1.0"
certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert"
export_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
certificate_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
"#,
            );
        }
        npa_package::parse_and_validate_manifest_str(&source).unwrap()
    }

    fn proposal(
        module: &str,
        change_kind: InterfaceProposalChangeKind,
        source_modules: &[&str],
        status: InterfaceProposalStatus,
        imports: &[&str],
    ) -> InterfaceProposal {
        let adopted = matches!(
            status,
            InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
        );
        InterfaceProposal {
            schema: npa_package::INTERFACE_PROPOSAL_SCHEMA.to_owned(),
            proposal_id: module.to_owned(),
            proposal_revision: 1,
            previous_proposal_hash: None,
            module: module.to_owned(),
            change_kind,
            source_modules: source_modules
                .iter()
                .map(|value| (*value).to_owned())
                .collect(),
            change_group: None,
            interface_status: status,
            proof_evidence: false,
            summary: "A catalog-boundary fixture.".to_owned(),
            scope: "Only the catalog-boundary fixture.".to_owned(),
            imports: imports.iter().map(|value| (*value).to_owned()).collect(),
            adoption_date: adopted.then(|| "2026-08-02".to_owned()),
            adoption_rationale: adopted
                .then(|| "The fixture has a complete reviewed surface.".to_owned()),
            re_adoption_rationale: None,
            withdrawal_rationale: (status == InterfaceProposalStatus::Withdrawn)
                .then(|| "The fixture is no longer pursued.".to_owned()),
            alternatives_review: matches!(
                status,
                InterfaceProposalStatus::Proposed
                    | InterfaceProposalStatus::Adopted
                    | InterfaceProposalStatus::Superseded
            )
            .then(|| "The focused fixture boundary was selected after review.".to_owned()),
            supersedes: Vec::new(),
            superseded_by: None,
            declarations: if status == InterfaceProposalStatus::Withdrawn {
                Vec::new()
            } else {
                vec![InterfaceProposalDeclaration {
                    name: "target_decl".to_owned(),
                    kind: InterfaceProposalDeclarationKind::Definition,
                    surface: npa_package::InterfaceProposalSurface::Public,
                    signature: Some("Nat".to_owned()),
                    body: Some("Sort 0".to_owned()),
                    family_members: Vec::new(),
                    semantic_role: "A catalog-boundary fixture declaration.".to_owned(),
                    depends_on: Vec::new(),
                    evidence_ids: Vec::new(),
                    foundation_exception: Some("A self-contained fixture primitive.".to_owned()),
                    support_rationale: None,
                    proof_reference_ids: Vec::new(),
                    proof_reference_exception: None,
                }]
            },
            observations: Vec::new(),
            proof_references: Vec::new(),
            alternatives: Vec::new(),
        }
    }

    fn record(proposal: InterfaceProposal) -> InterfaceProposalRecord {
        InterfaceProposalRecord {
            relative_path: format!("{}.toml", proposal.module.replace('.', "/")),
            file_hash: PackageHash::new([0; 32]),
            proposal,
        }
    }

    #[test]
    fn accepts_all_change_kinds_and_adopted_proposal_imports() {
        let manifest = manifest(
            &[
                "Mathlib.Catalog.A",
                "Mathlib.Catalog.B",
                "Mathlib.Catalog.C",
                "Mathlib.Catalog.D",
                "Mathlib.Catalog.E",
                "Mathlib.Catalog.F",
            ],
            true,
        );
        let mut split_one = proposal(
            "Mathlib.New.SplitOne",
            InterfaceProposalChangeKind::Split,
            &["Mathlib.Catalog.C"],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        split_one.change_group = Some("split-c".to_owned());
        let mut split_two = proposal(
            "Mathlib.New.SplitTwo",
            InterfaceProposalChangeKind::Split,
            &["Mathlib.Catalog.C"],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        split_two.change_group = Some("split-c".to_owned());
        let adopted = proposal(
            "Mathlib.New.Adopted",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Adopted,
            &["Std.Logic.Eq"],
        );
        let records = vec![
            record(proposal(
                "Mathlib.New.Add",
                InterfaceProposalChangeKind::Add,
                &[],
                InterfaceProposalStatus::Proposed,
                &["Mathlib.New.Adopted"],
            )),
            record(adopted),
            record(proposal(
                "Mathlib.Catalog.A",
                InterfaceProposalChangeKind::Revise,
                &["Mathlib.Catalog.A"],
                InterfaceProposalStatus::Proposed,
                &[],
            )),
            record(proposal(
                "Mathlib.New.Rename",
                InterfaceProposalChangeKind::Rename,
                &["Mathlib.Catalog.B"],
                InterfaceProposalStatus::Proposed,
                &[],
            )),
            record(split_one),
            record(split_two),
            record(proposal(
                "Mathlib.New.Merge",
                InterfaceProposalChangeKind::Merge,
                &["Mathlib.Catalog.D", "Mathlib.Catalog.E"],
                InterfaceProposalStatus::Proposed,
                &[],
            )),
            record(proposal(
                "Mathlib.New.Replace",
                InterfaceProposalChangeKind::Replace,
                &["Mathlib.Catalog.F"],
                InterfaceProposalStatus::Proposed,
                &[],
            )),
        ];
        validate_interface_proposal_catalog(&records, &manifest).unwrap();
    }

    #[test]
    fn rejects_path_ids_and_declaration_contract_collisions() {
        let manifest = manifest(&["Mathlib.Catalog.A"], false);
        let mut path = record(proposal(
            "Mathlib.New.Path",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        ));
        path.relative_path = "Mathlib/Wrong.toml".to_owned();
        let error = validate_interface_proposal_catalog(&[path], &manifest).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ModulePathMismatch
        );

        let mut duplicate = proposal(
            "Mathlib.New.Duplicate",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        duplicate
            .declarations
            .push(duplicate.declarations[0].clone());
        let error =
            validate_interface_proposal_catalog(&[record(duplicate)], &manifest).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::DuplicateDeclarationName
        );

        let mut first = proposal(
            "Mathlib.New.First",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        first.proposal_revision = 2;
        first.previous_proposal_hash = Some(PackageHash::new([1; 32]));
        first.proposal_id = "shared-id".to_owned();
        let mut second = proposal(
            "Mathlib.New.Second",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        second.proposal_revision = 2;
        second.previous_proposal_hash = Some(PackageHash::new([2; 32]));
        second.proposal_id = "shared-id".to_owned();
        let error =
            validate_interface_proposal_catalog(&[record(first), record(second)], &manifest)
                .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProposalIdReused
        );

        let first_module = proposal(
            "Mathlib.New.Shared",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        let mut second_module = first_module.clone();
        second_module.proposal_revision = 2;
        second_module.previous_proposal_hash = Some(PackageHash::new([3; 32]));
        second_module.proposal_id = "Mathlib.New.Shared.Revision".to_owned();
        let error = validate_interface_proposal_catalog(
            &[record(first_module), record(second_module)],
            &manifest,
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ActiveModuleCollision
        );

        let invalid_source = record(proposal(
            "Mathlib.New.BadSource",
            InterfaceProposalChangeKind::Add,
            &["Mathlib.Catalog.A"],
            InterfaceProposalStatus::Proposed,
            &[],
        ));
        let error = validate_interface_proposal_catalog(&[invalid_source], &manifest).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidSourceModules
        );
    }

    #[test]
    fn rejects_bad_catalog_relations_imports_and_incomplete_split_groups() {
        let manifest = manifest(&["Mathlib.Catalog.A"], true);
        let existing_target = record(proposal(
            "Mathlib.Catalog.A",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        ));
        let error = validate_interface_proposal_catalog(&[existing_target], &manifest).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::CatalogTargetExists
        );

        let unresolved_import = record(proposal(
            "Mathlib.New.Unresolved",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &["Mathlib.Missing"],
        ));
        let error =
            validate_interface_proposal_catalog(&[unresolved_import], &manifest).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ImportUnresolved
        );

        let mut incomplete_split = proposal(
            "Mathlib.New.Split",
            InterfaceProposalChangeKind::Split,
            &["Mathlib.Catalog.A"],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        incomplete_split.change_group = Some("split-a".to_owned());
        let error = validate_interface_proposal_catalog(&[record(incomplete_split)], &manifest)
            .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidChangeGroup
        );
    }

    #[test]
    fn accepts_materialized_adopted_add_after_catalog_admission() {
        let manifest = manifest(&["Mathlib.Catalog.A"], false);
        let mut adopted = proposal(
            "Mathlib.Catalog.A",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Adopted,
            &[],
        );
        adopted.declarations[0].name = "catalog_decl".to_owned();

        validate_interface_proposal_catalog(&[record(adopted)], &manifest).unwrap();
    }

    #[test]
    fn rejects_nonreciprocal_supersession_and_import_cycles_deterministically() {
        let manifest = manifest(&["Mathlib.Catalog.Anchor"], false);
        let new = proposal(
            "Mathlib.New.Successor",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Proposed,
            &[],
        );
        let mut old = proposal(
            "Mathlib.Old.Historical",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Superseded,
            &[],
        );
        old.superseded_by = Some(vec![new.proposal_id.clone()]);
        let error = validate_interface_proposal_catalog(&[record(old), record(new)], &manifest)
            .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::SupersessionNotReciprocal
        );

        let mut left = proposal(
            "Mathlib.Cycle.Left",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Adopted,
            &[],
        );
        left.imports = vec!["Mathlib.Cycle.Right".to_owned()];
        let mut right = proposal(
            "Mathlib.Cycle.Right",
            InterfaceProposalChangeKind::Add,
            &[],
            InterfaceProposalStatus::Adopted,
            &[],
        );
        right.imports = vec!["Mathlib.Cycle.Left".to_owned()];
        let records = vec![record(right), record(left)];
        let first = validate_interface_proposal_catalog(&records, &manifest).unwrap_err();
        let second = validate_interface_proposal_catalog(&records, &manifest).unwrap_err();
        assert_eq!(first.reason_code, InterfaceProposalErrorReason::ImportCycle);
        assert_eq!(first, second);
        assert!(first.actual.unwrap().contains("Mathlib.Cycle.Left"));
    }
}

#[cfg(test)]
mod transition {
    use super::*;

    fn proposal(module: &str, status: InterfaceProposalStatus) -> InterfaceProposal {
        let reviewable = matches!(
            status,
            InterfaceProposalStatus::Proposed
                | InterfaceProposalStatus::Adopted
                | InterfaceProposalStatus::Superseded
        );
        let adopted = matches!(
            status,
            InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
        );
        InterfaceProposal {
            schema: npa_package::INTERFACE_PROPOSAL_SCHEMA.to_owned(),
            proposal_id: module.to_owned(),
            proposal_revision: 1,
            previous_proposal_hash: None,
            module: module.to_owned(),
            change_kind: InterfaceProposalChangeKind::Add,
            source_modules: Vec::new(),
            change_group: None,
            interface_status: status,
            proof_evidence: false,
            summary: "A transition fixture.".to_owned(),
            scope: "Only the transition fixture surface.".to_owned(),
            imports: Vec::new(),
            adoption_date: adopted.then(|| "2026-08-01".to_owned()),
            adoption_rationale: adopted
                .then(|| "The exact fixture surface was adopted.".to_owned()),
            re_adoption_rationale: None,
            withdrawal_rationale: (status == InterfaceProposalStatus::Withdrawn)
                .then(|| "The unadopted fixture is no longer pursued.".to_owned()),
            alternatives_review: reviewable
                .then(|| "No material alternative was found for this fixture.".to_owned()),
            supersedes: Vec::new(),
            superseded_by: None,
            declarations: if reviewable {
                vec![InterfaceProposalDeclaration {
                    name: "target".to_owned(),
                    kind: InterfaceProposalDeclarationKind::Definition,
                    surface: npa_package::InterfaceProposalSurface::Public,
                    signature: Some("Nat".to_owned()),
                    body: Some("Sort 0".to_owned()),
                    family_members: Vec::new(),
                    semantic_role: "The transition fixture declaration.".to_owned(),
                    depends_on: Vec::new(),
                    evidence_ids: Vec::new(),
                    foundation_exception: Some("A self-contained transition fixture.".to_owned()),
                    support_rationale: None,
                    proof_reference_ids: Vec::new(),
                    proof_reference_exception: None,
                }]
            } else {
                Vec::new()
            },
            observations: Vec::new(),
            proof_references: Vec::new(),
            alternatives: Vec::new(),
        }
    }

    fn record(proposal: InterfaceProposal, hash: u8) -> InterfaceProposalRecord {
        InterfaceProposalRecord {
            relative_path: format!("{}.toml", proposal.module.replace('.', "/")),
            file_hash: PackageHash::new([hash; 32]),
            proposal,
        }
    }

    fn revised(
        previous: &InterfaceProposalRecord,
        status: InterfaceProposalStatus,
        hash: u8,
    ) -> InterfaceProposalRecord {
        let mut proposal = previous.proposal.clone();
        proposal.proposal_revision += 1;
        proposal.previous_proposal_hash = Some(previous.file_hash);
        proposal.interface_status = status;
        if matches!(
            status,
            InterfaceProposalStatus::Observed | InterfaceProposalStatus::Proposed
        ) {
            proposal.adoption_date = None;
            proposal.adoption_rationale = None;
            proposal.re_adoption_rationale = None;
            proposal.withdrawal_rationale = None;
            proposal.superseded_by = None;
        }
        if status == InterfaceProposalStatus::Withdrawn {
            proposal.adoption_date = None;
            proposal.adoption_rationale = None;
            proposal.re_adoption_rationale = None;
            proposal.superseded_by = None;
        }
        record(proposal, hash)
    }

    #[test]
    fn accepts_rework_readoption_withdrawal_and_one_to_many_supersession() {
        let previous_adopted = record(
            proposal(
                "Mathlib.Transition.Rework",
                InterfaceProposalStatus::Adopted,
            ),
            1,
        );
        let rework = revised(&previous_adopted, InterfaceProposalStatus::Proposed, 2);
        assert!(
            validate_interface_proposal_record_transition(&[rework], &[previous_adopted]).is_ok()
        );

        let previous_readoption = record(
            proposal(
                "Mathlib.Transition.Readopt",
                InterfaceProposalStatus::Adopted,
            ),
            3,
        );
        let mut readopted = revised(&previous_readoption, InterfaceProposalStatus::Adopted, 4);
        readopted.proposal.adoption_date = Some("2026-08-02".to_owned());
        readopted.proposal.adoption_rationale =
            Some("The revised exact fixture surface was adopted after review.".to_owned());
        readopted.proposal.re_adoption_rationale =
            Some("The completed fixture rework was reviewed and adopted again.".to_owned());
        assert!(validate_interface_proposal_record_transition(
            &[readopted],
            &[previous_readoption]
        )
        .is_ok());

        let previous_withdrawal = record(
            proposal(
                "Mathlib.Transition.Withdraw",
                InterfaceProposalStatus::Proposed,
            ),
            5,
        );
        let mut withdrawn = revised(&previous_withdrawal, InterfaceProposalStatus::Withdrawn, 6);
        withdrawn.proposal.withdrawal_rationale =
            Some("The unadopted fixture was withdrawn after review.".to_owned());
        assert!(validate_interface_proposal_record_transition(
            &[withdrawn],
            &[previous_withdrawal]
        )
        .is_ok());

        let previous_old = record(
            proposal("Mathlib.Transition.Old", InterfaceProposalStatus::Adopted),
            7,
        );
        let mut old = revised(&previous_old, InterfaceProposalStatus::Superseded, 8);
        old.proposal.superseded_by = Some(vec![
            "Mathlib.Transition.Left".to_owned(),
            "Mathlib.Transition.Right".to_owned(),
        ]);
        let mut left = proposal("Mathlib.Transition.Left", InterfaceProposalStatus::Proposed);
        left.supersedes = vec![previous_old.proposal.proposal_id.clone()];
        let mut right = proposal(
            "Mathlib.Transition.Right",
            InterfaceProposalStatus::Proposed,
        );
        right.supersedes = vec![previous_old.proposal.proposal_id.clone()];
        let current = vec![old, record(right, 10), record(left, 9)];
        assert!(validate_interface_proposal_record_transition(&current, &[previous_old]).is_ok());
    }

    #[test]
    fn rejects_revision_identity_removal_and_new_record_continuity_errors() {
        let previous = record(
            proposal(
                "Mathlib.Transition.Continuity",
                InterfaceProposalStatus::Proposed,
            ),
            11,
        );
        let mut wrong_hash = revised(&previous, InterfaceProposalStatus::Proposed, 12);
        wrong_hash.proposal.previous_proposal_hash = Some(PackageHash::new([99; 32]));
        let error = validate_interface_proposal_record_transition(
            &[wrong_hash],
            std::slice::from_ref(&previous),
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PreviousHashMismatch
        );

        let mut skipped = revised(&previous, InterfaceProposalStatus::Proposed, 13);
        skipped.proposal.proposal_revision = 3;
        let error = validate_interface_proposal_record_transition(
            &[skipped],
            std::slice::from_ref(&previous),
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::RevisionNotIncremented
        );

        let error =
            validate_interface_proposal_record_transition(&[], std::slice::from_ref(&previous))
                .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PreviousRecordRemoved
        );

        let mut changed_identity = revised(&previous, InterfaceProposalStatus::Proposed, 14);
        changed_identity.proposal.module = "Mathlib.Transition.Other".to_owned();
        changed_identity.relative_path = "Mathlib/Transition/Other.toml".to_owned();
        let error = validate_interface_proposal_record_transition(
            &[changed_identity],
            std::slice::from_ref(&previous),
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::RecordIdentityChanged
        );

        let mut new_record = record(
            proposal("Mathlib.Transition.New", InterfaceProposalStatus::Observed),
            15,
        );
        new_record.proposal.proposal_revision = 2;
        new_record.proposal.previous_proposal_hash = Some(PackageHash::new([16; 32]));
        let error = validate_interface_proposal_record_transition(&[new_record], &[]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidRevision
        );
    }

    #[test]
    fn rejects_invalid_lifecycle_surfaces_terminal_edits_and_same_roots() {
        let previous = record(
            proposal(
                "Mathlib.Transition.Status",
                InterfaceProposalStatus::Proposed,
            ),
            17,
        );
        let invalid_status = revised(&previous, InterfaceProposalStatus::Observed, 18);
        let error = validate_interface_proposal_record_transition(&[invalid_status], &[previous])
            .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidStatusTransition
        );

        let previous_withdrawal = record(
            proposal(
                "Mathlib.Transition.Surface",
                InterfaceProposalStatus::Proposed,
            ),
            19,
        );
        let mut changed_withdrawal =
            revised(&previous_withdrawal, InterfaceProposalStatus::Withdrawn, 20);
        changed_withdrawal.proposal.declarations[0].name = "changed".to_owned();
        changed_withdrawal.proposal.withdrawal_rationale =
            Some("The changed surface must be rejected.".to_owned());
        let error = validate_interface_proposal_record_transition(
            &[changed_withdrawal],
            &[previous_withdrawal],
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::WithdrawnSurfaceChanged
        );

        let previous_readoption = record(
            proposal(
                "Mathlib.Transition.ReadoptionError",
                InterfaceProposalStatus::Adopted,
            ),
            23,
        );
        let unchanged_adoption =
            revised(&previous_readoption, InterfaceProposalStatus::Adopted, 24);
        let error = validate_interface_proposal_record_transition(
            &[unchanged_adoption],
            std::slice::from_ref(&previous_readoption),
        )
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::AdoptedReworkNotReadopted
        );

        let previous_terminal = record(
            proposal(
                "Mathlib.Transition.Terminal",
                InterfaceProposalStatus::Withdrawn,
            ),
            21,
        );
        let mut edited_terminal = previous_terminal.clone();
        edited_terminal.proposal.summary = "Edited terminal record.".to_owned();
        edited_terminal.file_hash = PackageHash::new([22; 32]);
        let error =
            validate_interface_proposal_record_transition(&[edited_terminal], &[previous_terminal])
                .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::TerminalRecordChanged
        );

        let empty = InterfaceProposalDiscovery {
            files: Vec::new(),
            total_file_bytes: 0,
            proposal_set_hash: PackageHash::new([0; 32]),
        };
        let error =
            validate_interface_proposal_transition(Path::new("."), Path::new("."), &empty, &empty)
                .unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PreviousRootSameAsCurrent
        );

        let mut invalid_previous = record(
            proposal(
                "Mathlib.Transition.InvalidPrevious",
                InterfaceProposalStatus::Observed,
            ),
            25,
        );
        invalid_previous.relative_path = "Mathlib/Wrong.toml".to_owned();
        let error =
            validate_interface_proposal_record_transition(&[], &[invalid_previous]).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::PreviousSnapshotInvalid
        );
    }
}

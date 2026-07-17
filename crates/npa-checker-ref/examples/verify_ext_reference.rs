// This reference-renderer bridge intentionally propagates the complete,
// value-owned checker diagnostic on a cold failure path.
#![allow(clippy::result_large_err)]

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use npa_cert::{decode_module_cert_with_import_offsets, Hash, ImportEntry, ModuleCert};
use npa_checker_ref::{
    check_certificate, verify_certificate_hashes, ReferenceCertificateSection, ReferenceCheckError,
    ReferenceCheckErrorKind, ReferenceCheckImportTarget, ReferenceCheckReason,
    ReferenceCheckReference, ReferenceCheckResolvedImportIdentity, ReferenceCheckResult,
    ReferenceCheckedModule, ReferenceCheckerPolicy, ReferenceHashObject, ReferenceImportStore,
    ReferenceTrustMode, REFERENCE_CERTIFICATE_FORMAT, REFERENCE_CORE_SPEC,
};
use sha2::{Digest, Sha256};

#[path = "../../npa-cert/examples/support/policy_toml.rs"]
mod policy_toml;
#[path = "../../npa-cert/examples/support/source_free_fs.rs"]
mod source_free_fs;

const CHECKER_ID: &str = "npa-checker-ref";
const RAW_SCHEMA: &str = "npa.independent-checker.checker_raw_result.v1";
const MAX_IMPORT_CANDIDATES: usize = 4_096;
const MAX_IMPORT_DEPTH: usize = 1_024;
const MAX_IMPORT_DIRECTORY_DEPTH: usize = 128;
const MAX_IMPORT_DIRECTORY_ENTRIES: usize = 16_384;
const MAX_CERTIFICATE_BYTES: usize = 64 * 1024 * 1024;
const MAX_IMPORT_CANDIDATE_BYTES: usize = MAX_CERTIFICATE_BYTES;

struct Candidate {
    bytes: Vec<u8>,
    certificate: ModuleCert,
    import_offsets: Vec<usize>,
}

struct ClosureFailure {
    error: ReferenceCheckError,
    certificate: Option<Box<ModuleCert>>,
}

enum CandidatePathError {
    Unavailable,
    SourceInputForbidden,
    ResourceLimit(ReferenceCertificateSection),
    CandidateBytes(usize),
}

enum BoundedReadError {
    Unavailable,
    ResourceLimit,
}

fn is_source_or_replay_path(path: &Path) -> bool {
    source_free_fs::is_source_or_replay_path(path)
}

fn read_bounded_file(path: &Path, limit: usize) -> Result<Vec<u8>, BoundedReadError> {
    match source_free_fs::read_bounded_file(path, limit) {
        Ok(bytes) => Ok(bytes),
        Err(source_free_fs::SourceFreeFsError::ResourceLimit { .. }) => {
            Err(BoundedReadError::ResourceLimit)
        }
        Err(
            source_free_fs::SourceFreeFsError::Unavailable
            | source_free_fs::SourceFreeFsError::Symlink,
        ) => Err(BoundedReadError::Unavailable),
    }
}

fn candidate_files(
    directory: &Path,
) -> Result<Vec<source_free_fs::CollectedFile>, CandidatePathError> {
    if is_source_or_replay_path(directory) {
        return Err(CandidatePathError::SourceInputForbidden);
    }
    source_free_fs::collect_bounded_files(
        directory,
        std::ffi::OsStr::new("npcert"),
        MAX_IMPORT_DIRECTORY_DEPTH,
        MAX_IMPORT_DIRECTORY_ENTRIES,
        MAX_IMPORT_CANDIDATES,
        MAX_IMPORT_CANDIDATE_BYTES,
        &is_source_or_replay_path,
    )
    .map_err(|error| match error {
        source_free_fs::SourceFreeFsError::Unavailable => CandidatePathError::Unavailable,
        source_free_fs::SourceFreeFsError::Symlink => CandidatePathError::SourceInputForbidden,
        source_free_fs::SourceFreeFsError::ResourceLimit { kind, offset } => match kind {
            source_free_fs::ResourceLimitKind::DirectoryDepth => {
                CandidatePathError::ResourceLimit(ReferenceCertificateSection::ImportStore)
            }
            source_free_fs::ResourceLimitKind::DirectoryEntries
            | source_free_fs::ResourceLimitKind::CandidateCount => {
                CandidatePathError::ResourceLimit(ReferenceCertificateSection::Imports)
            }
            source_free_fs::ResourceLimitKind::CandidateBytes => {
                CandidatePathError::CandidateBytes(offset)
            }
        },
    })
}

fn candidate_bridge_decode_error() -> ReferenceCheckError {
    ReferenceCheckError {
        kind: ReferenceCheckErrorKind::MalformedCertificate,
        section: ReferenceCertificateSection::FullCertificate,
        offset: 0,
        reason: None,
        reference: None,
    }
}

fn prepare_candidate(bytes: Vec<u8>) -> Result<Candidate, ReferenceCheckError> {
    verify_certificate_hashes(&bytes)?;
    let (certificate, import_offsets) = decode_module_cert_with_import_offsets(&bytes)
        .map_err(|_| candidate_bridge_decode_error())?;
    Ok(Candidate {
        bytes,
        certificate,
        import_offsets,
    })
}

#[cfg(test)]
fn load_candidates_from_paths_with_budget(
    paths: Vec<PathBuf>,
    max_candidate_bytes: usize,
) -> Result<Vec<Candidate>, ReferenceCheckError> {
    let mut total_bytes = 0;
    let mut candidates = Vec::with_capacity(paths.len());
    for path in paths {
        let remaining_bytes = max_candidate_bytes
            .checked_sub(total_bytes)
            .ok_or_else(|| {
                candidate_resource_error(ReferenceCertificateSection::FullCertificate, 0)
            })?;
        let bytes = match read_bounded_file(&path, remaining_bytes) {
            Ok(bytes) => bytes,
            Err(BoundedReadError::Unavailable) => {
                return Err(graph_error(ReferenceCheckReason::MissingImport, 0));
            }
            Err(BoundedReadError::ResourceLimit) => {
                return Err(candidate_resource_error(
                    ReferenceCertificateSection::FullCertificate,
                    remaining_bytes,
                ));
            }
        };
        total_bytes = total_bytes.checked_add(bytes.len()).ok_or_else(|| {
            candidate_resource_error(ReferenceCertificateSection::FullCertificate, 0)
        })?;
        candidates.push(prepare_candidate(bytes)?);
    }
    Ok(candidates)
}

fn graph_error(reason: ReferenceCheckReason, offset: usize) -> ReferenceCheckError {
    ReferenceCheckError {
        kind: ReferenceCheckErrorKind::ImportResolution,
        section: ReferenceCertificateSection::Imports,
        offset,
        reason: Some(reason),
        reference: None,
    }
}

fn candidate_resource_error(
    section: ReferenceCertificateSection,
    offset: usize,
) -> ReferenceCheckError {
    ReferenceCheckError {
        kind: ReferenceCheckErrorKind::MalformedCertificate,
        section,
        offset,
        reason: Some(ReferenceCheckReason::ResourceLimit),
        reference: None,
    }
}

fn source_input_error() -> ReferenceCheckError {
    ReferenceCheckError {
        kind: ReferenceCheckErrorKind::MalformedCertificate,
        section: ReferenceCertificateSection::Imports,
        offset: 0,
        reason: Some(ReferenceCheckReason::SourceInputForbidden),
        reference: None,
    }
}

fn validate_unique_candidates(candidates: &[Candidate]) -> Result<(), ReferenceCheckError> {
    let mut seen = BTreeSet::new();
    for candidate in candidates {
        if !seen.insert((
            candidate.certificate.header.module.clone(),
            candidate.certificate.hashes.export_hash,
            candidate.certificate.hashes.certificate_hash,
        )) {
            return Err(graph_error(ReferenceCheckReason::DuplicateImport, 0));
        }
    }
    Ok(())
}

fn find_candidate(
    candidates: &[Candidate],
    import: &ImportEntry,
    offset: usize,
) -> Result<usize, ReferenceCheckError> {
    let same_module = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| candidate.certificate.header.module == import.module)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    if same_module.is_empty() {
        return Err(graph_error(ReferenceCheckReason::MissingImport, offset));
    }
    let same_export = same_module
        .into_iter()
        .filter(|index| candidates[*index].certificate.hashes.export_hash == import.export_hash)
        .collect::<Vec<_>>();
    if same_export.is_empty() {
        return Err(graph_error(
            ReferenceCheckReason::ImportExportHashMismatch,
            offset,
        ));
    }
    let Some(certificate_hash) = import.certificate_hash else {
        return Err(graph_error(
            ReferenceCheckReason::MissingImportCertificateHash,
            offset,
        ));
    };
    let matches = same_export
        .into_iter()
        .filter(|index| candidates[*index].certificate.hashes.certificate_hash == certificate_hash)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(graph_error(
            ReferenceCheckReason::ImportCertificateHashMismatch,
            offset,
        )),
        _ => Err(graph_error(ReferenceCheckReason::DuplicateImport, offset)),
    }
}

fn checked_store(
    checked: &BTreeMap<Hash, ReferenceCheckedModule>,
) -> Result<ReferenceImportStore, ReferenceCheckError> {
    ReferenceImportStore::from_checked_modules(checked.values().cloned())
}

fn check_candidate(
    index: usize,
    depth: usize,
    candidates: &[Candidate],
    visiting: &mut BTreeSet<Hash>,
    checked: &mut BTreeMap<Hash, ReferenceCheckedModule>,
    policy: &ReferenceCheckerPolicy,
) -> Result<(), ClosureFailure> {
    let candidate = &candidates[index];
    if depth > MAX_IMPORT_DEPTH {
        return Err(ClosureFailure {
            error: graph_error(ReferenceCheckReason::ResourceLimit, 0),
            certificate: Some(Box::new(candidate.certificate.clone())),
        });
    }
    let identity = candidate.certificate.hashes.certificate_hash;
    if checked.contains_key(&identity) {
        return Ok(());
    }
    if !visiting.insert(identity) {
        return Err(ClosureFailure {
            error: graph_error(ReferenceCheckReason::ImportCycle, 0),
            certificate: Some(Box::new(candidate.certificate.clone())),
        });
    }

    for (import, offset) in candidate
        .certificate
        .imports
        .iter()
        .zip(&candidate.import_offsets)
    {
        let dependency =
            find_candidate(candidates, import, *offset).map_err(|error| ClosureFailure {
                error,
                certificate: Some(Box::new(candidate.certificate.clone())),
            })?;
        check_candidate(dependency, depth + 1, candidates, visiting, checked, policy)?;
    }

    visiting.remove(&identity);
    let store = checked_store(checked).map_err(|error| ClosureFailure {
        error,
        certificate: Some(Box::new(candidate.certificate.clone())),
    })?;
    match check_certificate(&candidate.bytes, &store, policy) {
        ReferenceCheckResult::Checked(module) => {
            checked.insert(identity, module);
            Ok(())
        }
        ReferenceCheckResult::Rejected(error) => Err(ClosureFailure {
            error,
            certificate: Some(Box::new(candidate.certificate.clone())),
        }),
    }
}

fn check_leaf(
    bytes: &[u8],
    import_directory: &Path,
    policy: &ReferenceCheckerPolicy,
) -> Result<ReferenceCheckedModule, ClosureFailure> {
    let bridge_decoded = decode_module_cert_with_import_offsets(bytes);
    if let Err(error) = verify_certificate_hashes(bytes) {
        return Err(ClosureFailure {
            error,
            certificate: bridge_decoded
                .as_ref()
                .ok()
                .map(|(certificate, _)| Box::new(certificate.clone())),
        });
    }
    let (certificate, import_offsets) = bridge_decoded.map_err(|_| ClosureFailure {
        error: candidate_bridge_decode_error(),
        certificate: None,
    })?;
    let candidate_files = candidate_files(import_directory).map_err(|error| ClosureFailure {
        error: match error {
            CandidatePathError::Unavailable => graph_error(ReferenceCheckReason::MissingImport, 0),
            CandidatePathError::SourceInputForbidden => source_input_error(),
            CandidatePathError::ResourceLimit(section) => candidate_resource_error(section, 0),
            CandidatePathError::CandidateBytes(offset) => {
                candidate_resource_error(ReferenceCertificateSection::FullCertificate, offset)
            }
        },
        certificate: Some(Box::new(certificate.clone())),
    })?;
    let candidates = candidate_files
        .into_iter()
        .map(|file| prepare_candidate(file.bytes))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| ClosureFailure {
            error,
            certificate: Some(Box::new(certificate.clone())),
        })?;
    validate_unique_candidates(&candidates).map_err(|error| ClosureFailure {
        error,
        certificate: Some(Box::new(certificate.clone())),
    })?;
    let mut visiting = BTreeSet::new();
    let mut checked = BTreeMap::new();
    for (import, offset) in certificate.imports.iter().zip(import_offsets) {
        let dependency =
            find_candidate(&candidates, import, offset).map_err(|error| ClosureFailure {
                error,
                certificate: Some(Box::new(certificate.clone())),
            })?;
        check_candidate(
            dependency,
            1,
            &candidates,
            &mut visiting,
            &mut checked,
            policy,
        )
        .map_err(|failure| ClosureFailure {
            error: failure.error,
            certificate: Some(Box::new(certificate.clone())),
        })?;
    }
    let store = checked_store(&checked).map_err(|error| ClosureFailure {
        error,
        certificate: Some(Box::new(certificate.clone())),
    })?;
    match check_certificate(bytes, &store, policy) {
        ReferenceCheckResult::Checked(module) => Ok(module),
        ReferenceCheckResult::Rejected(error) => Err(ClosureFailure {
            error,
            certificate: Some(Box::new(certificate)),
        }),
    }
}

fn load_policy(path: &Path) -> Result<ReferenceCheckerPolicy, ()> {
    let source = String::from_utf8(read_bounded_file(path, MAX_CERTIFICATE_BYTES).map_err(|_| ())?)
        .map_err(|_| ())?;
    let allowed_axioms = policy_toml::parse(&source)?;
    Ok(ReferenceCheckerPolicy {
        trust_mode: ReferenceTrustMode::HighTrust,
        allowed_axioms,
        deny_sorry: true,
        deny_custom_axioms: true,
        supported_core_features: Vec::new(),
    })
}

fn hash_wire(hash: &[u8; 32]) -> String {
    let mut wire = String::from("sha256:");
    for byte in hash {
        wire.push_str(&format!("{byte:02x}"));
    }
    wire
}

fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000c}' => out.push_str("\\f"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str(&format!("\\u{:04x}", ch as u32));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn append_import_identity(path: &mut Vec<String>, identity: &ReferenceCheckResolvedImportIdentity) {
    path.push(format!("module={}", identity.module.dotted()));
    path.push(format!("export_hash={}", hash_wire(&identity.export_hash)));
}

fn append_import_target(path: &mut Vec<String>, target: &ReferenceCheckImportTarget) {
    match target {
        ReferenceCheckImportTarget::Unresolved { import_index, .. } => {
            path.push(format!("imports[{import_index}]"));
        }
        ReferenceCheckImportTarget::Resolved(identity) => {
            path.push(format!("imports[{}]", identity.import_index));
            append_import_identity(path, identity);
        }
        _ => {}
    }
}

fn append_owner_import_path(
    path: &mut Vec<String>,
    owner_import: &ReferenceCheckResolvedImportIdentity,
) {
    path.push(format!("imports[{}]", owner_import.import_index));
    append_import_identity(path, owner_import);
    path.push("public_environment".to_owned());
}

fn reference_projection(reference: &ReferenceCheckReference) -> (Option<String>, Vec<String>) {
    match reference {
        ReferenceCheckReference::Builtin { declaration, .. } => (
            Some(declaration.dotted()),
            vec!["reference".to_owned(), "builtin".to_owned()],
        ),
        ReferenceCheckReference::Imported {
            owner_import,
            import,
            declaration,
            ..
        } => {
            let mut path = vec!["reference".to_owned(), "imported".to_owned()];
            if let Some(owner_import) = owner_import {
                append_owner_import_path(&mut path, owner_import);
            }
            append_import_target(&mut path, import);
            (Some(declaration.dotted()), path)
        }
        ReferenceCheckReference::Local {
            owner_import,
            declaration_index,
            declaration,
            ..
        } => {
            let mut path = if let Some(owner_import) = owner_import {
                let mut path = vec!["reference".to_owned(), "imported".to_owned()];
                append_owner_import_path(&mut path, owner_import);
                path.push("local".to_owned());
                path
            } else {
                vec!["reference".to_owned(), "local".to_owned()]
            };
            path.push(format!("declarations[{declaration_index}]"));
            (declaration.as_ref().map(|name| name.dotted()), path)
        }
        ReferenceCheckReference::LocalGenerated {
            owner_import,
            declaration_index,
            declaration,
            ..
        } => {
            let mut path = if let Some(owner_import) = owner_import {
                let mut path = vec!["reference".to_owned(), "imported".to_owned()];
                append_owner_import_path(&mut path, owner_import);
                path.push("local_generated".to_owned());
                path
            } else {
                vec!["reference".to_owned(), "local_generated".to_owned()]
            };
            path.push(format!("declarations[{declaration_index}]"));
            (Some(declaration.dotted()), path)
        }
        _ => (None, Vec::new()),
    }
}

fn checker_build_hash() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(
        format!(
            "{CHECKER_ID}:{}:{REFERENCE_CORE_SPEC}:{REFERENCE_CERTIFICATE_FORMAT}",
            env!("CARGO_PKG_VERSION")
        )
        .as_bytes(),
    );
    hasher.finalize().into()
}

fn error_kind(error: &ReferenceCheckError) -> &'static str {
    match error.kind {
        ReferenceCheckErrorKind::EmptyCertificate => "certificate_decode_error",
        ReferenceCheckErrorKind::MalformedCertificate => match error.reason {
            Some(
                ReferenceCheckReason::NonCanonicalUvar
                | ReferenceCheckReason::InvalidUtf8
                | ReferenceCheckReason::EmptyModuleName
                | ReferenceCheckReason::EmptyModuleNameComponent
                | ReferenceCheckReason::DottedNameComponent
                | ReferenceCheckReason::InvalidNameComponent
                | ReferenceCheckReason::DuplicateName
                | ReferenceCheckReason::DuplicateDeclarationName
                | ReferenceCheckReason::NonCanonicalOrder
                | ReferenceCheckReason::NonNormalizedLevel
                | ReferenceCheckReason::NonNormalizedTerm
                | ReferenceCheckReason::UnusedTableEntry,
            ) => "noncanonical_encoding",
            Some(ReferenceCheckReason::ConstrainedExportRequiresFormatUpgrade) => {
                "unsupported_schema_version"
            }
            Some(ReferenceCheckReason::DuplicateUniverseConstraint) => "universe_inconsistency",
            _ => "certificate_decode_error",
        },
        ReferenceCheckErrorKind::HashMismatch => match error.reason {
            Some(ReferenceCheckReason::HashMismatch {
                object:
                    ReferenceHashObject::DeclInterfaceDependencyMaterial
                    | ReferenceHashObject::DeclCertificateDependencyMaterial,
            }) => "dependency_hash_mismatch",
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::ExportBlock,
            }) => "export_hash_mismatch",
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::AxiomReport,
            }) => "axiom_report_mismatch",
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::ModuleCertificate,
            }) => "certificate_hash_mismatch",
            Some(ReferenceCheckReason::HashMismatch { .. }) => "declaration_hash_mismatch",
            _ => "certificate_hash_mismatch",
        },
        ReferenceCheckErrorKind::ImportResolution => match error.reason {
            Some(ReferenceCheckReason::ImportExportHashMismatch)
            | Some(ReferenceCheckReason::ImportCertificateHashMismatch) => "import_hash_mismatch",
            _ => "import_not_found",
        },
        ReferenceCheckErrorKind::AxiomReportMismatch => "axiom_report_mismatch",
        ReferenceCheckErrorKind::AxiomPolicy => "forbidden_axiom",
        ReferenceCheckErrorKind::TypeCheck => match error.reason {
            Some(ReferenceCheckReason::NonPositiveOccurrence) => "positivity_failure",
            Some(ReferenceCheckReason::BadConstructorResult)
            | Some(ReferenceCheckReason::BadRecursorRule)
            | Some(ReferenceCheckReason::BadRecursorParam)
            | Some(ReferenceCheckReason::BadRecursorMotive)
            | Some(ReferenceCheckReason::BadRecursorMajor)
            | Some(ReferenceCheckReason::BadRecursorMinor)
            | Some(ReferenceCheckReason::BadRecursorResult)
            | Some(ReferenceCheckReason::BadRecursorType) => "inductive_invalid",
            Some(ReferenceCheckReason::BadUniverseArity)
            | Some(ReferenceCheckReason::DuplicateUniverseParam)
            | Some(ReferenceCheckReason::DuplicateUniverseConstraint)
            | Some(ReferenceCheckReason::UnresolvedMetavariable)
            | Some(ReferenceCheckReason::UnsupportedUniverseConstraint)
            | Some(ReferenceCheckReason::UnsatisfiableUniverseConstraints)
            | Some(ReferenceCheckReason::UniverseConstraintViolation)
            | Some(ReferenceCheckReason::ConstructorUniverseBoundViolation) => {
                "universe_inconsistency"
            }
            Some(ReferenceCheckReason::ResourceLimit) => "conversion_failure",
            _ => "type_mismatch",
        },
        ReferenceCheckErrorKind::UnsupportedSkeleton => "unsupported_schema_version",
        ReferenceCheckErrorKind::UnsupportedCoreFeature => "unsupported_core_feature",
    }
}

fn section_name(section: ReferenceCertificateSection) -> &'static str {
    match section {
        ReferenceCertificateSection::HeaderFormat => "header_format",
        ReferenceCertificateSection::HeaderCoreSpec => "header_core_spec",
        ReferenceCertificateSection::HeaderModule => "header_module",
        ReferenceCertificateSection::Imports => "imports",
        ReferenceCertificateSection::NameTable => "name_table",
        ReferenceCertificateSection::LevelTable => "level_table",
        ReferenceCertificateSection::TermTable => "term_table",
        ReferenceCertificateSection::Declarations => "declarations",
        ReferenceCertificateSection::ExportBlock => "export_block",
        ReferenceCertificateSection::AxiomReport => "axiom_report",
        ReferenceCertificateSection::Hashes => "hashes",
        ReferenceCertificateSection::ImportStore => "import_store",
        ReferenceCertificateSection::FullCertificate => "full_certificate",
    }
}

fn reason_code(error: &ReferenceCheckError) -> Option<&'static str> {
    match error.reason {
        None if error.kind == ReferenceCheckErrorKind::EmptyCertificate => Some("unexpected_eof"),
        None => None,
        Some(ReferenceCheckReason::UnexpectedEof) => Some("unexpected_eof"),
        Some(ReferenceCheckReason::NonCanonicalUvar) => Some("noncanonical_uvar"),
        Some(ReferenceCheckReason::UvarOverflow) => Some("uvar_overflow"),
        Some(ReferenceCheckReason::LengthOverflow) => Some("length_overflow"),
        Some(ReferenceCheckReason::UnknownTag { .. }) => Some("unknown_tag"),
        Some(ReferenceCheckReason::InvalidUtf8) => Some("invalid_utf8"),
        Some(ReferenceCheckReason::FormatMismatch) => Some("format_mismatch"),
        Some(ReferenceCheckReason::CoreSpecMismatch) => Some("core_spec_mismatch"),
        Some(ReferenceCheckReason::ConstrainedExportRequiresFormatUpgrade) => {
            Some("constrained_export_requires_format_upgrade")
        }
        Some(ReferenceCheckReason::EmptyModuleName) => Some("empty_name"),
        Some(ReferenceCheckReason::EmptyModuleNameComponent) => Some("empty_name_component"),
        Some(ReferenceCheckReason::DottedNameComponent) => Some("dotted_name_component"),
        Some(ReferenceCheckReason::InvalidNameComponent) => Some("invalid_name_component"),
        Some(ReferenceCheckReason::DanglingReference) => Some("dangling_reference"),
        Some(ReferenceCheckReason::NonCanonicalOrder) => Some("noncanonical_order"),
        Some(ReferenceCheckReason::DuplicateName) => Some("duplicate_name"),
        Some(ReferenceCheckReason::DuplicateDeclarationName) => Some("duplicate_declaration"),
        Some(ReferenceCheckReason::ReservedCorePrimitive) => Some("reserved_core_primitive"),
        Some(ReferenceCheckReason::DuplicateImport) => Some("duplicate_import"),
        Some(ReferenceCheckReason::ImportCycle) => Some("import_cycle"),
        Some(ReferenceCheckReason::NonNormalizedLevel) => Some("non_normalized_level"),
        Some(ReferenceCheckReason::NonNormalizedTerm) => Some("non_normalized_term"),
        Some(ReferenceCheckReason::UnusedTableEntry) => Some("unused_table_entry"),
        Some(ReferenceCheckReason::TrailingBytes) => Some("trailing_bytes"),
        Some(ReferenceCheckReason::SourceInputForbidden) => Some("source_input_forbidden"),
        Some(ReferenceCheckReason::MissingImport) => Some("missing_import"),
        Some(ReferenceCheckReason::ImportExportHashMismatch) => Some("import_export_hash_mismatch"),
        Some(ReferenceCheckReason::MissingImportCertificateHash) => {
            Some("missing_import_certificate_hash")
        }
        Some(ReferenceCheckReason::ImportCertificateHashMismatch) => {
            Some("import_certificate_hash_mismatch")
        }
        Some(ReferenceCheckReason::UncheckedImport) => Some("unchecked_import"),
        Some(ReferenceCheckReason::UnknownReference) => Some("unknown_reference"),
        Some(ReferenceCheckReason::UnsupportedCoreFeature) => Some("unsupported_core_feature"),
        Some(ReferenceCheckReason::BadUniverseArity) => Some("bad_universe_arity"),
        Some(ReferenceCheckReason::DuplicateUniverseParam) => Some("duplicate_universe_param"),
        Some(ReferenceCheckReason::DuplicateUniverseConstraint) => {
            Some("duplicate_universe_constraint")
        }
        Some(ReferenceCheckReason::UnresolvedMetavariable) => Some("unresolved_metavariable"),
        Some(ReferenceCheckReason::UnsupportedUniverseConstraint) => {
            Some("unsupported_universe_constraint")
        }
        Some(ReferenceCheckReason::UnsatisfiableUniverseConstraints) => {
            Some("unsatisfiable_universe_constraints")
        }
        Some(ReferenceCheckReason::UniverseConstraintViolation) => {
            Some("universe_constraint_violation")
        }
        Some(ReferenceCheckReason::InvalidBVar) => Some("invalid_bvar"),
        Some(ReferenceCheckReason::ExpectedSort) => Some("expected_sort"),
        Some(ReferenceCheckReason::ExpectedFunction) => Some("expected_function"),
        Some(ReferenceCheckReason::TypeMismatch) => Some("type_mismatch"),
        Some(ReferenceCheckReason::ResourceLimit) => Some("resource_limit"),
        Some(ReferenceCheckReason::BadConstructorResult)
        | Some(ReferenceCheckReason::BadRecursorRule)
        | Some(ReferenceCheckReason::BadRecursorParam)
        | Some(ReferenceCheckReason::BadRecursorMotive)
        | Some(ReferenceCheckReason::BadRecursorMajor)
        | Some(ReferenceCheckReason::BadRecursorMinor)
        | Some(ReferenceCheckReason::BadRecursorResult)
        | Some(ReferenceCheckReason::BadRecursorType) => Some("inductive_invalid"),
        Some(ReferenceCheckReason::ConstructorUniverseBoundViolation) => {
            Some("constructor_universe_bound_violation")
        }
        Some(ReferenceCheckReason::NonPositiveOccurrence) => Some("positivity_failure"),
        Some(ReferenceCheckReason::HashMismatch {
            object:
                ReferenceHashObject::DeclInterface
                | ReferenceHashObject::DeclInterfaceDependencyMaterial,
        }) => Some("decl_interface_hash_mismatch"),
        Some(ReferenceCheckReason::HashMismatch {
            object:
                ReferenceHashObject::DeclCertificate
                | ReferenceHashObject::DeclCertificateDependencyMaterial,
        }) => Some("decl_certificate_hash_mismatch"),
        Some(ReferenceCheckReason::HashMismatch {
            object: ReferenceHashObject::ExportBlock,
        }) => Some("export_hash_mismatch"),
        Some(ReferenceCheckReason::HashMismatch {
            object: ReferenceHashObject::AxiomReport,
        }) => Some("axiom_report_mismatch"),
        Some(ReferenceCheckReason::HashMismatch {
            object: ReferenceHashObject::ModuleCertificate,
        }) => Some("certificate_hash_mismatch"),
        Some(ReferenceCheckReason::AxiomReportMismatch) => Some("axiom_report_mismatch"),
        Some(ReferenceCheckReason::SorryDenied) => Some("sorry_denied"),
        Some(ReferenceCheckReason::ForbiddenAxiom) => Some("forbidden_axiom"),
        Some(ReferenceCheckReason::ReferenceCheckerBodyUnimplemented) => {
            Some("reference_checker_body_unimplemented")
        }
    }
}

fn checked_json(module: &ReferenceCheckedModule) -> String {
    format!(
        "{{\"schema\":\"{RAW_SCHEMA}\",\"checker_id\":\"{CHECKER_ID}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"status\":\"checked\",\"module\":\"{}\",\"certificate_hash\":\"{}\",\"export_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}",
        env!("CARGO_PKG_VERSION"),
        hash_wire(&checker_build_hash()),
        module.module().dotted(),
        hash_wire(module.certificate_hash()),
        hash_wire(module.export_hash()),
        hash_wire(module.axiom_report_hash()),
    )
}

fn failed_json_with_context(
    error: &ReferenceCheckError,
    certificate: Option<&ModuleCert>,
) -> String {
    failed_json_fields(
        error_kind(error),
        reason_code(error),
        section_name(error.section),
        error.offset,
        certificate,
        error.reference.as_ref(),
    )
}

fn failed_json_fields(
    kind: &str,
    reason_code: Option<&str>,
    section: &str,
    offset: usize,
    certificate: Option<&ModuleCert>,
    reference: Option<&ReferenceCheckReference>,
) -> String {
    let mut error_fields = vec![format!("\"kind\":{}", json_string(kind))];
    if let Some(reason_code) = reason_code {
        error_fields.push(format!("\"reason_code\":{}", json_string(reason_code)));
    }
    if let Some(reference) = reference {
        let (declaration, core_path) = reference_projection(reference);
        if let Some(declaration) = declaration {
            error_fields.push(format!("\"declaration\":{}", json_string(&declaration)));
        }
        if !core_path.is_empty() {
            error_fields.push(format!(
                "\"core_path\":[{}]",
                core_path
                    .iter()
                    .map(|token| json_string(token))
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
    }
    error_fields.push(format!("\"section\":{}", json_string(section)));
    error_fields.push(format!("\"offset\":{offset}"));
    let context = certificate
        .map(|certificate| {
            format!(
                ",\"module\":\"{}\",\"certificate_hash\":\"{}\"",
                certificate.header.module.as_dotted(),
                hash_wire(&certificate.hashes.certificate_hash),
            )
        })
        .unwrap_or_default();
    format!(
        "{{\"schema\":\"{RAW_SCHEMA}\",\"checker_id\":\"{CHECKER_ID}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"status\":\"failed\"{},\"error\":{{{}}}}}",
        env!("CARGO_PKG_VERSION"),
        hash_wire(&checker_build_hash()),
        context,
        error_fields.join(","),
    )
}

fn certificate_input_json() -> String {
    failed_json_fields(
        "certificate_decode_error",
        Some("certificate_input_unavailable"),
        "certificate",
        0,
        None,
        None,
    )
}

fn policy_input_json(bytes: &[u8]) -> String {
    let certificate = decode_module_cert_with_import_offsets(bytes)
        .ok()
        .map(|(certificate, _)| certificate);
    failed_json_fields(
        "policy_input_error",
        Some("request_axiom_policy_invalid"),
        "policy",
        0,
        certificate.as_ref(),
        None,
    )
}

fn failed_json(failure: &ClosureFailure) -> String {
    failed_json_with_context(&failure.error, failure.certificate.as_deref())
}

fn main() -> ExitCode {
    let mut arguments = env::args_os().skip(1);
    let Some(certificate_path) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_reference CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    let Some(import_directory) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_reference CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    let Some(policy_path) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_reference CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    if arguments.next().is_some() {
        eprintln!("usage: verify_ext_reference CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    }
    if is_source_or_replay_path(&certificate_path)
        || !source_free_fs::is_certificate_path(&certificate_path)
    {
        println!("{}", certificate_input_json());
        return ExitCode::from(1);
    }
    let bytes = match read_bounded_file(&certificate_path, MAX_CERTIFICATE_BYTES) {
        Ok(bytes) => bytes,
        Err(BoundedReadError::Unavailable) => {
            println!("{}", certificate_input_json());
            return ExitCode::from(1);
        }
        Err(BoundedReadError::ResourceLimit) => {
            let error = candidate_resource_error(
                ReferenceCertificateSection::FullCertificate,
                MAX_CERTIFICATE_BYTES,
            );
            println!("{}", failed_json_with_context(&error, None));
            return ExitCode::from(1);
        }
    };
    if is_source_or_replay_path(&policy_path) {
        println!("{}", policy_input_json(&bytes));
        return ExitCode::from(1);
    }
    let policy = match load_policy(&policy_path) {
        Ok(policy) => policy,
        Err(()) => {
            println!("{}", policy_input_json(&bytes));
            return ExitCode::from(1);
        }
    };
    match check_leaf(&bytes, &import_directory, &policy) {
        Ok(module) => {
            println!("{}", checked_json(&module));
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!("{}", failed_json(&failure));
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const INDEXED: &[u8] = include_bytes!(
        "../../../checkers/npa-checker-ext/test/fixtures/conformance/indexed-v0.2.npcert"
    );
    const MUTUAL: &[u8] = include_bytes!(
        "../../../checkers/npa-checker-ext/test/fixtures/conformance/mutual-v0.2.npcert"
    );

    fn candidate(bytes: &[u8]) -> Candidate {
        let (certificate, import_offsets) = decode_module_cert_with_import_offsets(bytes)
            .expect("committed conformance certificate");
        Candidate {
            bytes: bytes.to_vec(),
            certificate,
            import_offsets,
        }
    }

    #[test]
    fn malformed_leaf_failures_do_not_require_bridge_context() {
        for (bytes, expected_reason, expected_code) in [
            (&b""[..], None, "unexpected_eof"),
            (
                &b"\x01X"[..],
                Some(ReferenceCheckReason::FormatMismatch),
                "format_mismatch",
            ),
        ] {
            let failure = match check_leaf(
                bytes,
                Path::new("unused-import-directory"),
                &ReferenceCheckerPolicy::default(),
            ) {
                Ok(_) => panic!("malformed leaf must reject"),
                Err(failure) => failure,
            };
            assert_eq!(failure.error.reason, expected_reason);
            assert!(failure.certificate.is_none());
            let raw = failed_json(&failure);
            assert!(raw.contains("\"status\":\"failed\""));
            assert!(raw.contains(&format!("\"reason_code\":\"{expected_code}\"")));
        }
    }

    fn reference_name(value: &str) -> npa_checker_ref::ReferenceModuleName {
        npa_checker_ref::ReferenceModuleName::from_dotted(value).unwrap()
    }

    #[test]
    fn failure_renderer_matches_nested_unknown_reference_projection_contract() {
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 417,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(ReferenceCheckReference::Imported {
                owner_import: Some(ReferenceCheckResolvedImportIdentity::new(
                    0,
                    reference_name("Owner.Module"),
                    [0xab; 32],
                )),
                import: ReferenceCheckImportTarget::Resolved(
                    ReferenceCheckResolvedImportIdentity::new(
                        3,
                        reference_name("Std.Logic.Eq"),
                        [0xcd; 32],
                    ),
                ),
                declaration: reference_name("Std.Logic.Eq.rec"),
                decl_interface_hash: [0xef; 32],
            }),
        };

        let raw = failed_json_with_context(&error, None);
        let expected_error = format!(
            "\"error\":{{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"declaration\":\"Std.Logic.Eq.rec\",\"core_path\":[\"reference\",\"imported\",\"imports[0]\",\"module=Owner.Module\",\"export_hash={}\",\"public_environment\",\"imports[3]\",\"module=Std.Logic.Eq\",\"export_hash={}\"],\"section\":\"declarations\",\"offset\":417}}",
            hash_wire(&[0xab; 32]),
            hash_wire(&[0xcd; 32]),
        );
        assert!(raw.contains(&expected_error), "{raw}");
    }

    #[test]
    fn failure_renderer_matches_imported_environment_local_projection_contract() {
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 31,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(ReferenceCheckReference::Local {
                owner_import: Some(ReferenceCheckResolvedImportIdentity::new(
                    2,
                    reference_name("Owner.Module"),
                    [0x22; 32],
                )),
                declaration_index: 6,
                declaration: None,
            }),
        };

        let raw = failed_json_with_context(&error, None);
        let expected_error = format!(
            "\"error\":{{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"core_path\":[\"reference\",\"imported\",\"imports[2]\",\"module=Owner.Module\",\"export_hash={}\",\"public_environment\",\"local\",\"declarations[6]\"],\"section\":\"declarations\",\"offset\":31}}",
            hash_wire(&[0x22; 32]),
        );
        assert!(raw.contains(&expected_error), "{raw}");
    }

    #[test]
    fn failure_renderer_keeps_context_free_universe_unknown_reference() {
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 13,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: None,
        };

        let raw = failed_json_with_context(&error, None);
        assert!(raw.contains(
            "\"error\":{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"section\":\"declarations\",\"offset\":13}"
        ));
        assert!(!raw.contains("\"declaration\""));
        assert!(!raw.contains("\"core_path\""));
    }

    #[test]
    fn candidate_preparation_rejects_malformed_and_hash_mismatched_bytes() {
        assert!(prepare_candidate(b"not a certificate".to_vec()).is_err());

        let mut corrupted = MUTUAL.to_vec();
        *corrupted.last_mut().expect("certificate hash trailer") ^= 1;
        let error = match prepare_candidate(corrupted) {
            Ok(_) => panic!("hash-mismatched candidate must reject"),
            Err(error) => error,
        };
        assert_eq!(error.kind, ReferenceCheckErrorKind::HashMismatch);
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::ModuleCertificate,
            })
        );
    }

    #[test]
    fn candidate_loading_enforces_aggregate_bytes_and_source_exclusion() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../checkers/npa-checker-ext/test/fixtures/conformance/mutual-v0.2.npcert");
        let aggregate_bytes = MUTUAL.len() * 2;
        assert_eq!(
            load_candidates_from_paths_with_budget(
                vec![fixture.clone(), fixture.clone()],
                aggregate_bytes,
            )
            .expect("exact aggregate byte budget")
            .len(),
            2
        );
        let error = match load_candidates_from_paths_with_budget(
            vec![fixture.clone(), fixture],
            aggregate_bytes - 1,
        ) {
            Ok(_) => panic!("aggregate candidate byte budget must reject"),
            Err(error) => error,
        };
        assert_eq!(error.reason, Some(ReferenceCheckReason::ResourceLimit));
        assert_eq!(error.offset, MUTUAL.len() - 1);
        assert!(is_source_or_replay_path(Path::new(
            "/imports/hidden.npa/unrelated.npcert"
        )));
        assert!(is_source_or_replay_path(Path::new(
            "/imports/replay.json/unrelated.npcert"
        )));
        assert!(!is_source_or_replay_path(Path::new(
            "/imports/replay.json.backup/unrelated.npcert"
        )));
        assert!(source_free_fs::is_certificate_path(Path::new(
            "/certs/.npcert"
        )));
        assert!(!source_free_fs::is_certificate_path(Path::new(
            "/certs/module.npa"
        )));
    }

    fn request(certificate: &ModuleCert) -> ImportEntry {
        ImportEntry {
            module: certificate.header.module.clone(),
            export_hash: certificate.hashes.export_hash,
            certificate_hash: Some(certificate.hashes.certificate_hash),
        }
    }

    #[test]
    fn planner_rejects_missing_pins_duplicate_candidates_and_cycles() {
        let mutual = candidate(MUTUAL);
        let mut unpinned = request(&mutual.certificate);
        unpinned.certificate_hash = None;
        let error = find_candidate(&[candidate(MUTUAL)], &unpinned, 17)
            .expect_err("high-trust imports require a certificate pin");
        assert_eq!(error.offset, 17);
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::MissingImportCertificateHash)
        );

        assert_eq!(
            validate_unique_candidates(&[candidate(MUTUAL), candidate(MUTUAL)])
                .expect_err("candidate identities must be unique")
                .reason,
            Some(ReferenceCheckReason::DuplicateImport)
        );

        let mut indexed_cycle = candidate(INDEXED);
        let mut mutual_cycle = candidate(MUTUAL);
        indexed_cycle.certificate.imports = vec![request(&mutual_cycle.certificate)];
        indexed_cycle.import_offsets = vec![14];
        mutual_cycle.certificate.imports = vec![request(&indexed_cycle.certificate)];
        mutual_cycle.import_offsets = vec![13];
        let candidates = [indexed_cycle, mutual_cycle];
        let failure = check_candidate(
            0,
            1,
            &candidates,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
            &ReferenceCheckerPolicy::default(),
        )
        .expect_err("cyclic high-trust closure must be rejected by the planner");
        assert_eq!(
            failure.error.reason,
            Some(ReferenceCheckReason::ImportCycle)
        );
    }
}

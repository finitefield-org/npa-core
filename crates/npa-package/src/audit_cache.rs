//! Package audit cache identity and untrusted result-entry serialization.
//!
//! This module defines deterministic package audit cache keys and result
//! artifacts. It is metadata-only: it does not read files, run checkers, or make
//! cache entries part of proof evidence.

use std::collections::BTreeMap;

use npa_cert::Name;

use crate::{
    artifacts::{
        checker_summary_json, expect_object, field_path, hash_json, json_array, json_bool,
        json_object_in_order, json_string, parse_artifact_json, parse_checker_summary_at_path,
        reject_unknown_fields, required_array, required_bool, required_hash, required_name,
        required_string, validate_checker_summaries, validate_module_name,
        validate_package_identity, validate_plain_string, PackageCheckerMode,
        PackageCheckerSummary,
    },
    error::{PackageArtifactError, PackageArtifactResult, PackageLockError},
    hash::{format_package_hash, package_file_hash, parse_package_hash, PackageHash},
    lock::{
        build_package_lock_graph, PackageLockEntry, PackageLockEntryOrigin, PackageLockManifest,
    },
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
};

/// Cache key input schema for package audit result entries.
pub const PACKAGE_AUDIT_CACHE_SCHEMA: &str = "npa.package.audit_cache.v0.1";

/// Cache result entry schema for package audit checker outcomes.
pub const PACKAGE_AUDIT_RESULT_SCHEMA: &str = "npa.package.audit_result.v0.1";

/// Process-local package audit memo key schema.
///
/// These keys are never serialized as proof evidence. They use the same
/// deterministic identity material as audit cache entries, but the schema keeps
/// process-local memoization disjoint from disk-backed cache artifacts.
pub const PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA: &str = "npa.package.audit_process_memo.v0.1";

/// Disk-backed package verifier memo key schema.
///
/// This local-only memo uses the same deterministic key material as the
/// process-local verifier memo, but the schema keeps it separate from
/// process-only keys and from package audit result-store entries.
pub const PACKAGE_AUDIT_DISK_MEMO_SCHEMA: &str = "npa.package.audit_disk_memo.v0.1";

/// Disk-backed package verifier memo result schema.
pub const PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA: &str = "npa.package.audit_disk_memo_result.v0.1";

/// Disk-backed reference checker summary cache key schema.
pub const PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA: &str = "npa.package.reference_summary_cache.v0.1";

/// Disk-backed reference checker summary cache entry schema.
pub const PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA: &str =
    "npa.package.reference_summary_cache_entry.v0.1";

/// Disk-backed import-context export-data cache key schema.
pub const PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA: &str =
    "npa.package.import_context_export_cache.v0.1";

/// Disk-backed import-context export-data cache entry schema.
pub const PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA: &str =
    "npa.package.import_context_export_cache_entry.v0.1";

/// Verified export summary schema reserved for the package audit acceleration plan.
pub const PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA: &str = "npa.package.verified_export_summary.v0.1";

/// Default local package audit result-store layout.
pub const PACKAGE_AUDIT_CACHE_LAYOUT_DIR: &str = "target/npa-package-audit-cache/results-v0.1";

/// Default local disk-backed verifier memo layout.
pub const PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR: &str =
    "target/npa-package-audit-cache/verifier-memo-v0.1";

/// Default local disk-backed reference checker summary cache layout.
pub const PACKAGE_REFERENCE_SUMMARY_CACHE_LAYOUT_DIR: &str =
    "target/npa-package-audit-cache/reference-summary-v0.1";

/// Default local disk-backed import-context export-data cache layout.
pub const PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR: &str =
    "target/npa-package-audit-cache/import-context-export-v0.1";

/// Checker identity included in package audit cache keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditCheckerIdentity {
    /// Checker mode, for example `fast` or `reference`.
    pub mode: String,
    /// Stable checker implementation id.
    pub checker_id: String,
    /// Stable checker implementation version.
    pub checker_version: String,
    /// Exact checker build hash.
    pub checker_build_hash: PackageHash,
    /// Checker profile used for this audit.
    pub checker_profile: String,
    /// Optional runner policy hash for process-based checker modes.
    pub runner_policy_hash: Option<PackageHash>,
}

/// Direct import identity included in package audit cache keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditImportIdentity {
    /// Imported module name.
    pub module: Name,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Complete deterministic cache key input for one audited package-lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditCacheKeyInput {
    /// Cache key input schema string; must equal [`PACKAGE_AUDIT_CACHE_SCHEMA`].
    pub schema: String,
    /// Package identity from the package manifest or package lock.
    pub package_id: PackageId,
    /// Package version from the package manifest or package lock.
    pub package_version: PackageVersion,
    /// Package-lock schema string covered by this cache identity.
    pub package_lock_schema: String,
    /// Core specification profile.
    pub core_spec: String,
    /// Canonical certificate format profile.
    pub certificate_format: String,
    /// Exact hash of the checked package lock bytes.
    pub package_lock_hash: PackageHash,
    /// Exact hash of the package audit policy material.
    pub package_policy_hash: PackageHash,
    /// Checker identity.
    pub checker: PackageAuditCheckerIdentity,
    /// Audited module name.
    pub module: Name,
    /// Whether the audited module is local or external.
    pub origin: PackageLockEntryOrigin,
    /// Package-relative certificate path covered by this cache identity.
    pub certificate: PackagePath,
    /// Exact hash of the audited certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Canonical certificate hash declared by the certificate.
    pub certificate_hash: PackageHash,
    /// Canonical export hash declared by the certificate.
    pub export_hash: PackageHash,
    /// Canonical axiom report hash declared by the certificate.
    pub axiom_report_hash: PackageHash,
    /// Direct import identities.
    pub direct_imports: Vec<PackageAuditImportIdentity>,
    /// Optional dependency summary hash used by later acceleration milestones.
    pub dependency_summary_hash: Option<PackageHash>,
    /// Enabled core feature names.
    pub enabled_core_features: Vec<String>,
}

/// Cached checker status recorded in an untrusted package audit result entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageAuditCachedStatus {
    /// The live checker accepted the module for this exact key input.
    Accepted,
    /// The live checker rejected the module for this exact key input.
    Rejected,
}

impl PackageAuditCachedStatus {
    /// Return the stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "accepted" => Ok(Self::Accepted),
            "rejected" => Ok(Self::Rejected),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "status",
                "accepted or rejected",
                value,
            )),
        }
    }
}

/// One untrusted package audit result-store entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditResultEntry {
    /// Result entry schema string; must equal [`PACKAGE_AUDIT_RESULT_SCHEMA`].
    pub schema: String,
    /// Deterministic cache key for [`Self::key_input`].
    pub cache_key: String,
    /// Must be false: cache entries are never proof evidence.
    pub trusted: bool,
    /// Must be false: cache entries are never proof evidence.
    pub proof_evidence: bool,
    /// Exact key input covered by this result.
    pub key_input: PackageAuditCacheKeyInput,
    /// Cached checker status.
    pub status: PackageAuditCachedStatus,
    /// Optional deterministic diagnostic reason for rejected entries.
    pub diagnostic_reason: Option<String>,
    /// Human-readable trust-boundary note.
    pub trust_boundary: String,
}

/// One untrusted reference checker summary cache entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageReferenceSummaryCacheEntry {
    /// Reference summary cache entry schema.
    pub schema: String,
    /// Deterministic cache key for [`Self::key_input`].
    pub cache_key: String,
    /// Must be false: cache entries are never proof evidence.
    pub trusted: bool,
    /// Must be false: cache entries are never proof evidence.
    pub proof_evidence: bool,
    /// Exact key input covered by this summary.
    pub key_input: PackageAuditCacheKeyInput,
    /// Cached reference checker summary.
    pub summary: PackageCheckerSummary,
    /// Human-readable trust-boundary note.
    pub trust_boundary: String,
}

/// One dependency export identity stored in an import-context export cache.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageImportContextExportData {
    /// Imported dependency module.
    pub module: Name,
    /// Whether the dependency is local or external in the package lock.
    pub origin: PackageLockEntryOrigin,
    /// External package id when [`Self::origin`] is external.
    pub package: Option<PackageId>,
    /// External package version when [`Self::origin`] is external.
    pub version: Option<PackageVersion>,
    /// Dependency export hash from the package lock.
    pub export_hash: PackageHash,
    /// Dependency certificate hash from the package lock.
    pub certificate_hash: PackageHash,
    /// Dependency axiom-report hash from the package lock.
    pub axiom_report_hash: PackageHash,
    /// Certificate format profile used to materialize the dependency context.
    pub certificate_format: String,
}

/// Import-context export-data cache key input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageImportContextExportCacheKeyInput {
    /// Cache key schema.
    pub schema: String,
    /// Package id for the package being checked.
    pub package_id: PackageId,
    /// Package version for the package being checked.
    pub package_version: PackageVersion,
    /// Package lock schema string.
    pub package_lock_schema: String,
    /// Core specification profile.
    pub core_spec: String,
    /// Certificate format profile.
    pub certificate_format: String,
    /// Verifier policy hash for the materialized import context.
    pub checker_policy_hash: PackageHash,
    /// Owner module whose direct import context is cached.
    pub owner_module: Name,
    /// Ordered direct dependency export identities.
    pub dependency_exports: Vec<PackageImportContextExportData>,
}

/// One untrusted import-context export-data cache entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageImportContextExportCacheEntry {
    /// Cache entry schema.
    pub schema: String,
    /// Deterministic cache key for [`Self::key_input`].
    pub cache_key: String,
    /// Must be false: cache entries are never proof evidence.
    pub trusted: bool,
    /// Must be false: cache entries are never proof evidence.
    pub proof_evidence: bool,
    /// Exact key input covered by this cache entry.
    pub key_input: PackageImportContextExportCacheKeyInput,
    /// Materialized dependency export data for this import context.
    pub dependency_exports: Vec<PackageImportContextExportData>,
    /// Human-readable trust-boundary note.
    pub trust_boundary: String,
}

/// Package-lock graph inventory used by audit speed measurements and planning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditGraphInventory {
    /// Number of local package modules.
    pub local_module_count: u64,
    /// Number of external package import entries.
    pub external_import_count: u64,
    /// Total package-lock entry count.
    pub lock_entry_count: u64,
    /// Total direct import edges recorded in the package lock.
    pub direct_import_edge_count: u64,
    /// Direct import edges from local entries to local entries.
    pub local_reverse_edge_count: u64,
    /// Number of deterministic topological verification layers.
    pub topological_layer_count: u64,
}

/// Serialize canonical cache key material for one package audit input.
pub fn package_audit_cache_key_material(input: &PackageAuditCacheKeyInput) -> String {
    cache_key_input_json(&normalized_cache_key_input(input))
}

/// Compute the deterministic package audit cache key for one input.
pub fn package_audit_cache_key(input: &PackageAuditCacheKeyInput) -> String {
    format_package_hash(&package_file_hash(
        package_audit_cache_key_material(input).as_bytes(),
    ))
}

/// Compute a deterministic process-local package audit memo key.
///
/// The key material is normalized in the same way as disk-backed audit cache
/// key material, but it is schema-separated so a process memo entry can never be
/// confused with a persisted cache artifact.
pub fn package_audit_process_memo_key(input: &PackageAuditCacheKeyInput) -> String {
    let mut memo_input = normalized_cache_key_input(input);
    memo_input.schema = PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA.to_owned();
    format_package_hash(&package_file_hash(
        cache_key_input_json(&memo_input).as_bytes(),
    ))
}

/// Compute a deterministic disk-backed package verifier memo key.
///
/// The key material intentionally matches the process-local verifier memo
/// material except for the schema string, which prevents disk entries from
/// being confused with process-only memo values or audit result-store entries.
pub fn package_audit_disk_memo_key(input: &PackageAuditCacheKeyInput) -> String {
    let mut memo_input = normalized_cache_key_input(input);
    memo_input.schema = PACKAGE_AUDIT_DISK_MEMO_SCHEMA.to_owned();
    format_package_hash(&package_file_hash(
        cache_key_input_json(&memo_input).as_bytes(),
    ))
}

/// Return normalized disk memo key input for serialization.
pub fn package_audit_disk_memo_key_input(
    input: &PackageAuditCacheKeyInput,
) -> PackageAuditCacheKeyInput {
    let mut memo_input = normalized_cache_key_input(input);
    memo_input.schema = PACKAGE_AUDIT_DISK_MEMO_SCHEMA.to_owned();
    memo_input
}

/// Compute a deterministic disk-backed reference checker summary cache key.
pub fn package_reference_summary_cache_key(input: &PackageAuditCacheKeyInput) -> String {
    let mut summary_input = normalized_cache_key_input(input);
    summary_input.schema = PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA.to_owned();
    format_package_hash(&package_file_hash(
        cache_key_input_json(&summary_input).as_bytes(),
    ))
}

/// Return normalized reference checker summary cache key input for serialization.
pub fn package_reference_summary_cache_key_input(
    input: &PackageAuditCacheKeyInput,
) -> PackageAuditCacheKeyInput {
    let mut summary_input = normalized_cache_key_input(input);
    summary_input.schema = PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA.to_owned();
    summary_input
}

/// Compute a deterministic import-context export-data cache key.
pub fn package_import_context_export_cache_key(
    input: &PackageImportContextExportCacheKeyInput,
) -> String {
    let mut key_input = normalized_import_context_export_cache_key_input(input);
    key_input.schema = PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA.to_owned();
    format_package_hash(&package_file_hash(
        import_context_export_cache_key_input_json(&key_input).as_bytes(),
    ))
}

/// Serialize one package audit result entry as canonical JSON.
pub fn package_audit_result_entry_json(entry: &PackageAuditResultEntry) -> String {
    result_entry_json_unchecked(&normalized_result_entry(entry))
}

/// Serialize one disk-backed verifier memo result entry as canonical JSON.
pub fn package_audit_disk_memo_result_entry_json(entry: &PackageAuditResultEntry) -> String {
    result_entry_json_unchecked(&normalized_result_entry(entry))
}

/// Serialize one reference checker summary cache entry as canonical JSON.
pub fn package_reference_summary_cache_entry_json(
    entry: &PackageReferenceSummaryCacheEntry,
) -> String {
    reference_summary_cache_entry_json_unchecked(&normalized_reference_summary_cache_entry(entry))
}

/// Serialize one import-context export-data cache entry as canonical JSON.
pub fn package_import_context_export_cache_entry_json(
    entry: &PackageImportContextExportCacheEntry,
) -> String {
    import_context_export_cache_entry_json_unchecked(&normalized_import_context_export_cache_entry(
        entry,
    ))
}

/// Parse and validate a canonical package audit result entry JSON artifact.
pub fn parse_package_audit_result_entry_json(
    source: &str,
) -> PackageArtifactResult<PackageAuditResultEntry> {
    let root = parse_artifact_json(source)?;
    let entry = parse_result_entry_value(&root)?;
    validate_package_audit_result_entry(&entry)?;
    let canonical = package_audit_result_entry_json(&entry);
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package audit result entry JSON bytes",
        ));
    }
    Ok(entry)
}

/// Parse and validate a canonical disk-backed verifier memo result entry JSON artifact.
pub fn parse_package_audit_disk_memo_result_entry_json(
    source: &str,
) -> PackageArtifactResult<PackageAuditResultEntry> {
    let root = parse_artifact_json(source)?;
    let entry = parse_result_entry_value(&root)?;
    validate_package_audit_disk_memo_result_entry(&entry)?;
    let canonical = package_audit_disk_memo_result_entry_json(&entry);
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package audit disk memo result entry JSON bytes",
        ));
    }
    Ok(entry)
}

/// Parse and validate a canonical reference checker summary cache entry JSON artifact.
pub fn parse_package_reference_summary_cache_entry_json(
    source: &str,
) -> PackageArtifactResult<PackageReferenceSummaryCacheEntry> {
    let root = parse_artifact_json(source)?;
    let entry = parse_reference_summary_cache_entry_value(&root)?;
    validate_package_reference_summary_cache_entry(&entry)?;
    let canonical = package_reference_summary_cache_entry_json(&entry);
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "reference summary cache entry JSON bytes",
        ));
    }
    Ok(entry)
}

/// Parse and validate a canonical import-context export-data cache entry JSON
/// artifact.
pub fn parse_package_import_context_export_cache_entry_json(
    source: &str,
) -> PackageArtifactResult<PackageImportContextExportCacheEntry> {
    let root = parse_artifact_json(source)?;
    let entry = parse_import_context_export_cache_entry_value(&root)?;
    validate_package_import_context_export_cache_entry(&entry)?;
    let canonical = package_import_context_export_cache_entry_json(&entry);
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "import context export cache entry JSON bytes",
        ));
    }
    Ok(entry)
}

/// Validate one package audit result entry without reading files or running checkers.
pub fn validate_package_audit_result_entry(
    entry: &PackageAuditResultEntry,
) -> PackageArtifactResult<()> {
    validate_result_entry_with_schemas(
        entry,
        PACKAGE_AUDIT_RESULT_SCHEMA,
        PACKAGE_AUDIT_CACHE_SCHEMA,
    )
}

/// Validate one disk-backed verifier memo result entry without reading files or
/// running checkers.
pub fn validate_package_audit_disk_memo_result_entry(
    entry: &PackageAuditResultEntry,
) -> PackageArtifactResult<()> {
    validate_result_entry_with_schemas(
        entry,
        PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA,
        PACKAGE_AUDIT_DISK_MEMO_SCHEMA,
    )
}

/// Validate one reference checker summary cache entry without reading files or
/// running checkers.
pub fn validate_package_reference_summary_cache_entry(
    entry: &PackageReferenceSummaryCacheEntry,
) -> PackageArtifactResult<()> {
    if entry.schema != PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA,
            entry.schema.clone(),
        ));
    }
    validate_hash_string(&entry.cache_key, "cache_key")?;
    if entry.trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "trusted", "trusted", "false", "true",
        ));
    }
    if entry.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    validate_cache_key_input_with_schema(&entry.key_input, PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA)?;
    let expected_key = package_reference_summary_cache_key(&entry.key_input);
    if expected_key != entry.cache_key {
        return Err(PackageArtifactError::self_hash_mismatch(
            "cache_key",
            "cache_key",
            expected_key,
            entry.cache_key.clone(),
        ));
    }
    validate_checker_summaries(std::slice::from_ref(&entry.summary))?;
    if entry.summary.mode != PackageCheckerMode::Reference {
        return Err(PackageArtifactError::invalid_enum_value(
            "summary.mode",
            "mode",
            "reference",
            entry.summary.mode.as_str(),
        ));
    }
    if entry.summary.module != entry.key_input.module {
        return Err(PackageArtifactError::invalid_enum_value(
            "summary.module",
            "module",
            entry.key_input.module.as_dotted(),
            entry.summary.module.as_dotted(),
        ));
    }
    if entry.summary.checker != entry.key_input.checker.checker_id {
        return Err(PackageArtifactError::invalid_enum_value(
            "summary.checker",
            "checker",
            &entry.key_input.checker.checker_id,
            &entry.summary.checker,
        ));
    }
    if entry.summary.profile != entry.key_input.checker.checker_profile {
        return Err(PackageArtifactError::invalid_enum_value(
            "summary.profile",
            "profile",
            &entry.key_input.checker.checker_profile,
            &entry.summary.profile,
        ));
    }
    if entry.summary.status != "passed" {
        return Err(PackageArtifactError::invalid_enum_value(
            "summary.status",
            "status",
            "passed",
            &entry.summary.status,
        ));
    }
    if entry.summary.export_hash != entry.key_input.export_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "summary.export_hash",
            "export_hash",
            format_package_hash(&entry.key_input.export_hash),
            format_package_hash(&entry.summary.export_hash),
        ));
    }
    if entry.summary.certificate_hash != entry.key_input.certificate_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "summary.certificate_hash",
            "certificate_hash",
            format_package_hash(&entry.key_input.certificate_hash),
            format_package_hash(&entry.summary.certificate_hash),
        ));
    }
    if entry.summary.axiom_report_hash != entry.key_input.axiom_report_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "summary.axiom_report_hash",
            "axiom_report_hash",
            format_package_hash(&entry.key_input.axiom_report_hash),
            format_package_hash(&entry.summary.axiom_report_hash),
        ));
    }
    validate_plain_string(&entry.trust_boundary, "trust_boundary")
}

/// Validate one import-context export-data cache entry without reading files or
/// running checkers.
pub fn validate_package_import_context_export_cache_entry(
    entry: &PackageImportContextExportCacheEntry,
) -> PackageArtifactResult<()> {
    if entry.schema != PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA,
            entry.schema.clone(),
        ));
    }
    validate_hash_string(&entry.cache_key, "cache_key")?;
    if entry.trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "trusted", "trusted", "false", "true",
        ));
    }
    if entry.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    validate_import_context_export_cache_key_input(&entry.key_input)?;
    let expected_key = package_import_context_export_cache_key(&entry.key_input);
    if expected_key != entry.cache_key {
        return Err(PackageArtifactError::self_hash_mismatch(
            "cache_key",
            "cache_key",
            expected_key,
            entry.cache_key.clone(),
        ));
    }
    validate_import_context_export_data_list(
        &entry.dependency_exports,
        "dependency_exports",
        &entry.key_input.certificate_format,
    )?;
    if entry.dependency_exports != entry.key_input.dependency_exports {
        return Err(PackageArtifactError::summary_mismatch(
            "dependency_exports",
            "key_input.dependency_exports",
            "same dependency export data",
            "different dependency export data",
        ));
    }
    validate_plain_string(&entry.trust_boundary, "trust_boundary")
}

fn validate_import_context_export_cache_key_input(
    input: &PackageImportContextExportCacheKeyInput,
) -> PackageArtifactResult<()> {
    if input.schema != PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "key_input.schema",
            "schema",
            PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA,
            input.schema.clone(),
        ));
    }
    validate_package_identity(&input.package_id, &input.package_version)?;
    validate_plain_string(&input.package_lock_schema, "key_input.package_lock_schema")?;
    validate_plain_string(&input.core_spec, "key_input.core_spec")?;
    validate_plain_string(&input.certificate_format, "key_input.certificate_format")?;
    validate_hash_string(
        &format_package_hash(&input.checker_policy_hash),
        "key_input.checker_policy_hash",
    )?;
    validate_module_name(&input.owner_module, "key_input.owner_module")?;
    validate_import_context_export_data_list(
        &input.dependency_exports,
        "key_input.dependency_exports",
        &input.certificate_format,
    )
}

fn validate_import_context_export_data_list(
    exports: &[PackageImportContextExportData],
    path: &str,
    expected_certificate_format: &str,
) -> PackageArtifactResult<()> {
    for (index, export) in exports.iter().enumerate() {
        validate_import_context_export_data(
            export,
            &format!("{path}[{index}]"),
            expected_certificate_format,
        )?;
    }
    Ok(())
}

fn validate_import_context_export_data(
    export: &PackageImportContextExportData,
    path: &str,
    expected_certificate_format: &str,
) -> PackageArtifactResult<()> {
    validate_module_name(&export.module, field_path(path, "module"))?;
    match export.origin {
        PackageLockEntryOrigin::Local => {
            if export.package.is_some() {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(path, "package"),
                    "package",
                    "absent for local imports",
                    export.package.as_ref().map(PackageId::as_str).unwrap_or(""),
                ));
            }
            if export.version.is_some() {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(path, "version"),
                    "version",
                    "absent for local imports",
                    export
                        .version
                        .as_ref()
                        .map(PackageVersion::as_str)
                        .unwrap_or(""),
                ));
            }
        }
        PackageLockEntryOrigin::External => {
            let Some(package) = &export.package else {
                return Err(PackageArtifactError::missing_field(path, "package"));
            };
            let Some(version) = &export.version else {
                return Err(PackageArtifactError::missing_field(path, "version"));
            };
            validate_package_identity(package, version)?;
        }
    }
    if export.certificate_format != expected_certificate_format {
        return Err(PackageArtifactError::invalid_enum_value(
            field_path(path, "certificate_format"),
            "certificate_format",
            expected_certificate_format,
            &export.certificate_format,
        ));
    }
    validate_plain_string(
        &export.certificate_format,
        field_path(path, "certificate_format"),
    )
}

fn validate_result_entry_with_schemas(
    entry: &PackageAuditResultEntry,
    result_schema: &str,
    key_schema: &str,
) -> PackageArtifactResult<()> {
    if entry.schema != result_schema {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            result_schema,
            entry.schema.clone(),
        ));
    }
    validate_hash_string(&entry.cache_key, "cache_key")?;
    if entry.trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "trusted", "trusted", "false", "true",
        ));
    }
    if entry.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    validate_cache_key_input_with_schema(&entry.key_input, key_schema)?;
    let expected_key = match key_schema {
        PACKAGE_AUDIT_DISK_MEMO_SCHEMA => package_audit_disk_memo_key(&entry.key_input),
        _ => package_audit_cache_key(&entry.key_input),
    };
    if expected_key != entry.cache_key {
        return Err(PackageArtifactError::self_hash_mismatch(
            "cache_key",
            "cache_key",
            expected_key,
            entry.cache_key.clone(),
        ));
    }
    if let Some(reason) = &entry.diagnostic_reason {
        validate_plain_string(reason, "diagnostic_reason")?;
    }
    validate_plain_string(&entry.trust_boundary, "trust_boundary")
}

/// Return canonical direct import identities for one package-lock entry.
pub fn package_audit_direct_imports_for_entry(
    entry: &PackageLockEntry,
) -> Vec<PackageAuditImportIdentity> {
    let mut imports = entry
        .imports
        .iter()
        .map(|import| PackageAuditImportIdentity {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
        })
        .collect::<Vec<_>>();
    normalize_direct_imports(&mut imports);
    imports
}

/// Compute package-lock graph inventory without reading source, replay, or cache data.
pub fn package_audit_graph_inventory(
    lock: &PackageLockManifest,
) -> PackageArtifactResult<PackageAuditGraphInventory> {
    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    let mut entries = lock.entries.clone();
    entries.sort_by(|left, right| left.module.cmp(&right.module));

    let local_module_count = entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
        .count() as u64;
    let external_import_count = entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::External)
        .count() as u64;
    let direct_import_edge_count = entries
        .iter()
        .map(|entry| entry.imports.len() as u64)
        .sum::<u64>();
    let local_reverse_edge_count = graph
        .resolved_entry_imports
        .iter()
        .enumerate()
        .map(|(entry_index, imports)| {
            if entries[entry_index].origin != PackageLockEntryOrigin::Local {
                return 0_u64;
            }
            imports
                .iter()
                .filter(|import| {
                    entries[import.entry_index].origin == PackageLockEntryOrigin::Local
                })
                .count() as u64
        })
        .sum::<u64>();

    Ok(PackageAuditGraphInventory {
        local_module_count,
        external_import_count,
        lock_entry_count: entries.len() as u64,
        direct_import_edge_count,
        local_reverse_edge_count,
        topological_layer_count: topological_layer_count(
            &entries,
            &graph.topological_order,
            &graph.resolved_entry_imports,
        )?,
    })
}

fn validate_cache_key_input_with_schema(
    input: &PackageAuditCacheKeyInput,
    expected_schema: &str,
) -> PackageArtifactResult<()> {
    if input.schema != expected_schema {
        return Err(PackageArtifactError::unsupported_schema(
            "key_input.schema",
            "schema",
            expected_schema,
            input.schema.clone(),
        ));
    }
    validate_plain_string(input.package_id.as_str(), "key_input.package_id")?;
    validate_plain_string(input.package_version.as_str(), "key_input.package_version")?;
    validate_plain_string(&input.package_lock_schema, "key_input.package_lock_schema")?;
    validate_plain_string(&input.core_spec, "key_input.core_spec")?;
    validate_plain_string(&input.certificate_format, "key_input.certificate_format")?;
    validate_checker_identity(&input.checker)?;
    validate_module_name(&input.module, "key_input.module")?;
    validate_plain_string(input.origin.as_str(), "key_input.origin")?;
    validate_plain_string(input.certificate.as_str(), "key_input.certificate")?;
    for (index, import) in input.direct_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            format!("key_input.direct_imports[{index}].module"),
        )?;
    }
    for (index, feature) in input.enabled_core_features.iter().enumerate() {
        validate_plain_string(feature, format!("key_input.enabled_core_features[{index}]"))?;
    }
    Ok(())
}

fn validate_checker_identity(identity: &PackageAuditCheckerIdentity) -> PackageArtifactResult<()> {
    validate_plain_string(&identity.mode, "key_input.checker.mode")?;
    validate_plain_string(&identity.checker_id, "key_input.checker.checker_id")?;
    validate_plain_string(
        &identity.checker_version,
        "key_input.checker.checker_version",
    )?;
    validate_plain_string(
        &identity.checker_profile,
        "key_input.checker.checker_profile",
    )
}

fn validate_hash_string(value: &str, path: &str) -> PackageArtifactResult<()> {
    parse_package_hash(value, path)
        .map(|_| ())
        .map_err(|_| PackageArtifactError::invalid_hash_format(path, value))
}

fn normalized_result_entry(entry: &PackageAuditResultEntry) -> PackageAuditResultEntry {
    let mut normalized = entry.clone();
    normalized.key_input = normalized_cache_key_input(&normalized.key_input);
    normalized
}

fn normalized_reference_summary_cache_entry(
    entry: &PackageReferenceSummaryCacheEntry,
) -> PackageReferenceSummaryCacheEntry {
    let mut normalized = entry.clone();
    normalized.key_input = normalized_cache_key_input(&normalized.key_input);
    normalized
}

fn normalized_import_context_export_cache_entry(
    entry: &PackageImportContextExportCacheEntry,
) -> PackageImportContextExportCacheEntry {
    let mut normalized = entry.clone();
    normalized.key_input = normalized_import_context_export_cache_key_input(&normalized.key_input);
    normalized.dependency_exports =
        normalized_import_context_export_data_list(&normalized.dependency_exports);
    normalized
}

fn normalized_import_context_export_cache_key_input(
    input: &PackageImportContextExportCacheKeyInput,
) -> PackageImportContextExportCacheKeyInput {
    let mut normalized = input.clone();
    normalized.schema = PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA.to_owned();
    normalized.dependency_exports =
        normalized_import_context_export_data_list(&normalized.dependency_exports);
    normalized
}

fn normalized_import_context_export_data_list(
    exports: &[PackageImportContextExportData],
) -> Vec<PackageImportContextExportData> {
    exports.to_vec()
}

fn normalized_cache_key_input(input: &PackageAuditCacheKeyInput) -> PackageAuditCacheKeyInput {
    let mut normalized = input.clone();
    normalize_direct_imports(&mut normalized.direct_imports);
    normalized.enabled_core_features.sort();
    normalized.enabled_core_features.dedup();
    normalized
}

fn normalize_direct_imports(imports: &mut Vec<PackageAuditImportIdentity>) {
    imports.sort_by(|left, right| {
        left.module
            .cmp(&right.module)
            .then_with(|| left.export_hash.cmp(&right.export_hash))
            .then_with(|| left.certificate_hash.cmp(&right.certificate_hash))
    });
    imports.dedup_by(|left, right| {
        left.module == right.module
            && left.export_hash == right.export_hash
            && left.certificate_hash == right.certificate_hash
    });
}

fn topological_layer_count(
    entries: &[PackageLockEntry],
    topological_order: &[Name],
    resolved_entry_imports: &[Vec<crate::lock::PackageLockResolvedImport>],
) -> PackageArtifactResult<u64> {
    if entries.is_empty() {
        return Ok(0);
    }

    let entry_indices = entries
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut layers = vec![None::<u64>; entries.len()];

    for module in topological_order {
        let Some(entry_index) = entry_indices.get(module).copied() else {
            return Err(PackageArtifactError::summary_mismatch(
                "package_lock.topological_order",
                "module",
                "package lock entry module",
                module.as_dotted(),
            ));
        };
        let layer = resolved_entry_imports[entry_index]
            .iter()
            .map(|import| layers[import.entry_index].unwrap_or(0) + 1)
            .max()
            .unwrap_or(0);
        layers[entry_index] = Some(layer);
    }

    Ok(layers.into_iter().flatten().max().unwrap_or(0) + 1)
}

fn package_lock_graph_error(error: PackageLockError) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "package_lock",
        "package_lock",
        "valid package lock graph",
        error.reason_code.as_str(),
    )
}

fn cache_key_input_json(input: &PackageAuditCacheKeyInput) -> String {
    let mut fields = vec![
        ("schema", json_string(&input.schema)),
        ("package_id", json_string(input.package_id.as_str())),
        (
            "package_version",
            json_string(input.package_version.as_str()),
        ),
        (
            "package_lock_schema",
            json_string(&input.package_lock_schema),
        ),
        ("core_spec", json_string(&input.core_spec)),
        ("certificate_format", json_string(&input.certificate_format)),
        ("package_lock_hash", hash_json(input.package_lock_hash)),
        ("package_policy_hash", hash_json(input.package_policy_hash)),
        ("checker", checker_identity_json(&input.checker)),
        ("module", json_string(&input.module.as_dotted())),
        ("origin", json_string(input.origin.as_str())),
        ("certificate", json_string(input.certificate.as_str())),
        (
            "certificate_file_hash",
            hash_json(input.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(input.certificate_hash)),
        ("export_hash", hash_json(input.export_hash)),
        ("axiom_report_hash", hash_json(input.axiom_report_hash)),
        (
            "direct_imports",
            json_array(
                input
                    .direct_imports
                    .iter()
                    .map(import_identity_json)
                    .collect(),
            ),
        ),
    ];
    if let Some(hash) = input.dependency_summary_hash {
        fields.push(("dependency_summary_hash", hash_json(hash)));
    }
    fields.push((
        "enabled_core_features",
        json_array(
            input
                .enabled_core_features
                .iter()
                .map(|feature| json_string(feature))
                .collect(),
        ),
    ));
    json_object_in_order(fields)
}

fn checker_identity_json(identity: &PackageAuditCheckerIdentity) -> String {
    let mut fields = vec![
        ("mode", json_string(&identity.mode)),
        ("checker_id", json_string(&identity.checker_id)),
        ("checker_version", json_string(&identity.checker_version)),
        ("checker_build_hash", hash_json(identity.checker_build_hash)),
        ("checker_profile", json_string(&identity.checker_profile)),
    ];
    if let Some(hash) = identity.runner_policy_hash {
        fields.push(("runner_policy_hash", hash_json(hash)));
    }
    json_object_in_order(fields)
}

fn import_identity_json(import: &PackageAuditImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn result_entry_json_unchecked(entry: &PackageAuditResultEntry) -> String {
    let mut fields = vec![
        ("schema", json_string(&entry.schema)),
        ("cache_key", json_string(&entry.cache_key)),
        ("trusted", json_bool(entry.trusted)),
        ("proof_evidence", json_bool(entry.proof_evidence)),
        ("key_input", cache_key_input_json(&entry.key_input)),
        ("status", json_string(entry.status.as_str())),
    ];
    if let Some(reason) = &entry.diagnostic_reason {
        fields.push(("diagnostic_reason", json_string(reason)));
    }
    fields.push(("trust_boundary", json_string(&entry.trust_boundary)));
    json_object_in_order(fields)
}

fn reference_summary_cache_entry_json_unchecked(
    entry: &PackageReferenceSummaryCacheEntry,
) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&entry.schema)),
        ("cache_key", json_string(&entry.cache_key)),
        ("trusted", json_bool(entry.trusted)),
        ("proof_evidence", json_bool(entry.proof_evidence)),
        ("key_input", cache_key_input_json(&entry.key_input)),
        ("summary", checker_summary_json(&entry.summary)),
        ("trust_boundary", json_string(&entry.trust_boundary)),
    ])
}

fn import_context_export_cache_entry_json_unchecked(
    entry: &PackageImportContextExportCacheEntry,
) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&entry.schema)),
        ("cache_key", json_string(&entry.cache_key)),
        ("trusted", json_bool(entry.trusted)),
        ("proof_evidence", json_bool(entry.proof_evidence)),
        (
            "key_input",
            import_context_export_cache_key_input_json(&entry.key_input),
        ),
        (
            "dependency_exports",
            import_context_export_data_list_json(&entry.dependency_exports),
        ),
        ("trust_boundary", json_string(&entry.trust_boundary)),
    ])
}

fn import_context_export_cache_key_input_json(
    input: &PackageImportContextExportCacheKeyInput,
) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&input.schema)),
        ("package_id", json_string(input.package_id.as_str())),
        (
            "package_version",
            json_string(input.package_version.as_str()),
        ),
        (
            "package_lock_schema",
            json_string(&input.package_lock_schema),
        ),
        ("core_spec", json_string(&input.core_spec)),
        ("certificate_format", json_string(&input.certificate_format)),
        ("checker_policy_hash", hash_json(input.checker_policy_hash)),
        ("owner_module", json_string(&input.owner_module.as_dotted())),
        (
            "dependency_exports",
            import_context_export_data_list_json(&input.dependency_exports),
        ),
    ])
}

fn import_context_export_data_list_json(exports: &[PackageImportContextExportData]) -> String {
    json_array(
        exports
            .iter()
            .map(import_context_export_data_json)
            .collect::<Vec<_>>(),
    )
}

fn import_context_export_data_json(export: &PackageImportContextExportData) -> String {
    let mut fields = vec![
        ("module", json_string(&export.module.as_dotted())),
        ("origin", json_string(export.origin.as_str())),
    ];
    if let Some(package) = &export.package {
        fields.push(("package", json_string(package.as_str())));
    }
    if let Some(version) = &export.version {
        fields.push(("version", json_string(version.as_str())));
    }
    fields.extend([
        ("export_hash", hash_json(export.export_hash)),
        ("certificate_hash", hash_json(export.certificate_hash)),
        ("axiom_report_hash", hash_json(export.axiom_report_hash)),
        (
            "certificate_format",
            json_string(&export.certificate_format),
        ),
    ]);
    json_object_in_order(fields)
}

fn parse_reference_summary_cache_entry_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageReferenceSummaryCacheEntry> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, REFERENCE_SUMMARY_CACHE_ENTRY_FIELDS)?;
    Ok(PackageReferenceSummaryCacheEntry {
        schema: required_string(members, "$", "schema")?,
        cache_key: required_string(members, "$", "cache_key")?,
        trusted: required_bool(members, "$", "trusted")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
        key_input: parse_cache_key_input(crate::artifacts::required_value(
            members,
            "$",
            "key_input",
        )?)?,
        summary: parse_checker_summary_at_path(
            crate::artifacts::required_value(members, "$", "summary")?,
            "summary",
        )?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
    })
}

fn parse_import_context_export_cache_entry_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageImportContextExportCacheEntry> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_FIELDS)?;
    Ok(PackageImportContextExportCacheEntry {
        schema: required_string(members, "$", "schema")?,
        cache_key: required_string(members, "$", "cache_key")?,
        trusted: required_bool(members, "$", "trusted")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
        key_input: parse_import_context_export_cache_key_input(crate::artifacts::required_value(
            members,
            "$",
            "key_input",
        )?)?,
        dependency_exports: parse_import_context_export_data_list(
            crate::artifacts::required_value(members, "$", "dependency_exports")?,
            "dependency_exports",
        )?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
    })
}

fn parse_import_context_export_cache_key_input(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageImportContextExportCacheKeyInput> {
    let path = "key_input";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, IMPORT_CONTEXT_EXPORT_CACHE_KEY_INPUT_FIELDS)?;
    Ok(PackageImportContextExportCacheKeyInput {
        schema: required_string(members, path, "schema")?,
        package_id: PackageId::new(required_string(members, path, "package_id")?),
        package_version: PackageVersion::new(required_string(members, path, "package_version")?),
        package_lock_schema: required_string(members, path, "package_lock_schema")?,
        core_spec: required_string(members, path, "core_spec")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        checker_policy_hash: required_hash(members, path, "checker_policy_hash")?,
        owner_module: required_name(members, path, "owner_module")?,
        dependency_exports: parse_import_context_export_data_list(
            crate::artifacts::required_value(members, path, "dependency_exports")?,
            "key_input.dependency_exports",
        )?,
    })
}

fn parse_import_context_export_data_list(
    value: &crate::json::JsonValue,
    path: &str,
) -> PackageArtifactResult<Vec<PackageImportContextExportData>> {
    let values = value.array_elements().ok_or_else(|| {
        PackageArtifactError::wrong_type(path, None, "array", value.kind().as_str())
    })?;
    values
        .iter()
        .enumerate()
        .map(|(index, value)| parse_import_context_export_data(value, &format!("{path}[{index}]")))
        .collect()
}

fn parse_import_context_export_data(
    value: &crate::json::JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageImportContextExportData> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, IMPORT_CONTEXT_EXPORT_DATA_FIELDS)?;
    let origin = parse_lock_entry_origin(&required_string(members, path, "origin")?, path)?;
    Ok(PackageImportContextExportData {
        module: required_name(members, path, "module")?,
        origin,
        package: optional_string(members, path, "package")?.map(PackageId::new),
        version: optional_string(members, path, "version")?.map(PackageVersion::new),
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        certificate_format: required_string(members, path, "certificate_format")?,
    })
}

fn parse_result_entry_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAuditResultEntry> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, RESULT_ENTRY_FIELDS)?;
    let status_path = field_path("$", "status");
    Ok(PackageAuditResultEntry {
        schema: required_string(members, "$", "schema")?,
        cache_key: required_string(members, "$", "cache_key")?,
        trusted: required_bool(members, "$", "trusted")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
        key_input: parse_cache_key_input(crate::artifacts::required_value(
            members,
            "$",
            "key_input",
        )?)?,
        status: PackageAuditCachedStatus::parse(
            &required_string(members, "$", "status")?,
            &status_path,
        )?,
        diagnostic_reason: optional_string(members, "$", "diagnostic_reason")?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
    })
}

fn parse_cache_key_input(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAuditCacheKeyInput> {
    let path = "key_input";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CACHE_KEY_INPUT_FIELDS)?;
    Ok(PackageAuditCacheKeyInput {
        schema: required_string(members, path, "schema")?,
        package_id: PackageId::new(required_string(members, path, "package_id")?),
        package_version: PackageVersion::new(required_string(members, path, "package_version")?),
        package_lock_schema: required_string(members, path, "package_lock_schema")?,
        core_spec: required_string(members, path, "core_spec")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        package_lock_hash: required_hash(members, path, "package_lock_hash")?,
        package_policy_hash: required_hash(members, path, "package_policy_hash")?,
        checker: parse_checker_identity(crate::artifacts::required_value(
            members, path, "checker",
        )?)?,
        module: required_name(members, path, "module")?,
        origin: parse_lock_entry_origin(&required_string(members, path, "origin")?, path)?,
        certificate: PackagePath::new(required_string(members, path, "certificate")?),
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        direct_imports: required_array(members, path, "direct_imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_import_identity(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        dependency_summary_hash: optional_hash(members, path, "dependency_summary_hash")?,
        enabled_core_features: parse_string_array(members, path, "enabled_core_features")?,
    })
}

fn parse_lock_entry_origin(
    value: &str,
    path: &str,
) -> PackageArtifactResult<PackageLockEntryOrigin> {
    match value {
        "local" => Ok(PackageLockEntryOrigin::Local),
        "external" => Ok(PackageLockEntryOrigin::External),
        _ => Err(PackageArtifactError::invalid_enum_value(
            format!("{path}.origin"),
            "origin",
            "local or external",
            value,
        )),
    }
}

fn parse_checker_identity(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAuditCheckerIdentity> {
    let path = "key_input.checker";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CHECKER_IDENTITY_FIELDS)?;
    Ok(PackageAuditCheckerIdentity {
        mode: required_string(members, path, "mode")?,
        checker_id: required_string(members, path, "checker_id")?,
        checker_version: required_string(members, path, "checker_version")?,
        checker_build_hash: required_hash(members, path, "checker_build_hash")?,
        checker_profile: required_string(members, path, "checker_profile")?,
        runner_policy_hash: optional_hash(members, path, "runner_policy_hash")?,
    })
}

fn parse_import_identity(
    index: usize,
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAuditImportIdentity> {
    let path = format!("key_input.direct_imports[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_IDENTITY_FIELDS)?;
    Ok(PackageAuditImportIdentity {
        module: required_name(members, &path, "module")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

fn parse_string_array(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<String>> {
    required_array(members, path, field)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn optional_hash(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<PackageHash>> {
    if members.iter().any(|member| member.key() == field) {
        required_hash(members, path, field).map(Some)
    } else {
        Ok(None)
    }
}

fn optional_string(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<String>> {
    if members.iter().any(|member| member.key() == field) {
        required_string(members, path, field).map(Some)
    } else {
        Ok(None)
    }
}

const RESULT_ENTRY_FIELDS: &[&str] = &[
    "schema",
    "cache_key",
    "trusted",
    "proof_evidence",
    "key_input",
    "status",
    "diagnostic_reason",
    "trust_boundary",
];
const REFERENCE_SUMMARY_CACHE_ENTRY_FIELDS: &[&str] = &[
    "schema",
    "cache_key",
    "trusted",
    "proof_evidence",
    "key_input",
    "summary",
    "trust_boundary",
];
const IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_FIELDS: &[&str] = &[
    "schema",
    "cache_key",
    "trusted",
    "proof_evidence",
    "key_input",
    "dependency_exports",
    "trust_boundary",
];
const IMPORT_CONTEXT_EXPORT_CACHE_KEY_INPUT_FIELDS: &[&str] = &[
    "schema",
    "package_id",
    "package_version",
    "package_lock_schema",
    "core_spec",
    "certificate_format",
    "checker_policy_hash",
    "owner_module",
    "dependency_exports",
];
const IMPORT_CONTEXT_EXPORT_DATA_FIELDS: &[&str] = &[
    "module",
    "origin",
    "package",
    "version",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
    "certificate_format",
];
const CACHE_KEY_INPUT_FIELDS: &[&str] = &[
    "schema",
    "package_id",
    "package_version",
    "package_lock_schema",
    "core_spec",
    "certificate_format",
    "package_lock_hash",
    "package_policy_hash",
    "checker",
    "module",
    "origin",
    "certificate",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
    "axiom_report_hash",
    "direct_imports",
    "dependency_summary_hash",
    "enabled_core_features",
];
const CHECKER_IDENTITY_FIELDS: &[&str] = &[
    "mode",
    "checker_id",
    "checker_version",
    "checker_build_hash",
    "checker_profile",
    "runner_policy_hash",
];
const IMPORT_IDENTITY_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        error::PackageArtifactErrorReason,
        lock::{PackageLockImport, PackageLockManifestReference},
        manifest::PackageVersion,
        name::PackageId,
        path::PackagePath,
        schema::PACKAGE_LOCK_SCHEMA,
    };

    #[test]
    fn package_audit_cache_key_is_deterministic() {
        let input = fixture_key_input();

        assert_eq!(
            package_audit_cache_key_material(&input),
            package_audit_cache_key_material(&input)
        );
        assert_eq!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&input)
        );
    }

    #[test]
    fn package_audit_cache_key_changes_for_package_lock_hash() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.package_lock_hash = hash(99);

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_cache_key_changes_for_persistent_result_identity() {
        let input = fixture_key_input();
        let base_key = package_audit_cache_key(&input);

        let mut changed = input.clone();
        changed.package_id = PackageId::new("other-package");
        assert_ne!(base_key, package_audit_cache_key(&changed));

        let mut changed = input.clone();
        changed.package_version = PackageVersion::new("9.9.9");
        assert_ne!(base_key, package_audit_cache_key(&changed));

        let mut changed = input.clone();
        changed.package_lock_schema = "npa.package.lock.v9".to_owned();
        assert_ne!(base_key, package_audit_cache_key(&changed));

        let mut changed = input.clone();
        changed.origin = PackageLockEntryOrigin::External;
        assert_ne!(base_key, package_audit_cache_key(&changed));

        let mut changed = input.clone();
        changed.certificate = PackagePath::new("Fixture/Target/changed.npcert");
        assert_ne!(base_key, package_audit_cache_key(&changed));
    }

    #[test]
    fn package_audit_cache_key_changes_for_checker_build_hash() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.checker.checker_build_hash = hash(99);

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_cache_key_changes_for_certificate_hash() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.certificate_hash = hash(99);

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_cache_key_sorts_direct_imports() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.direct_imports = vec![
            PackageAuditImportIdentity {
                module: module("Fixture.ImportB"),
                export_hash: hash(21),
                certificate_hash: hash(22),
            },
            PackageAuditImportIdentity {
                module: module("Fixture.ImportA"),
                export_hash: hash(19),
                certificate_hash: hash(20),
            },
            PackageAuditImportIdentity {
                module: module("Fixture.ImportA"),
                export_hash: hash(19),
                certificate_hash: hash(20),
            },
        ];

        assert_eq!(
            package_audit_cache_key_material(&input),
            package_audit_cache_key_material(&changed)
        );
        assert_eq!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_cache_key_changes_for_direct_import_identity() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.direct_imports[0].export_hash = hash(99);

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_cache_key_changes_for_enabled_core_feature() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.enabled_core_features.push("quot".to_owned());

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_cache_key(&changed)
        );
    }

    #[test]
    fn package_audit_result_entry_requires_trusted_false() {
        let mut entry = fixture_result_entry(PackageAuditCachedStatus::Accepted);
        entry.trusted = true;

        let error = validate_package_audit_result_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("trusted"));
    }

    #[test]
    fn package_audit_result_entry_requires_proof_evidence_false() {
        let mut entry = fixture_result_entry(PackageAuditCachedStatus::Accepted);
        entry.proof_evidence = true;

        let error = validate_package_audit_result_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("proof_evidence"));
    }

    #[test]
    fn package_audit_result_entry_round_trips_canonical_json() {
        let mut entry = fixture_result_entry(PackageAuditCachedStatus::Rejected);
        entry.key_input.enabled_core_features = vec![
            "unit".to_owned(),
            "inductive".to_owned(),
            "inductive".to_owned(),
        ];
        entry.cache_key = package_audit_cache_key(&entry.key_input);
        entry.diagnostic_reason = Some("checker_rejected".to_owned());

        let json = package_audit_result_entry_json(&entry);
        let parsed = parse_package_audit_result_entry_json(&json).unwrap();

        assert_eq!(package_audit_result_entry_json(&parsed), json);
        assert_eq!(parsed.status, PackageAuditCachedStatus::Rejected);
        assert_eq!(
            parsed.key_input.enabled_core_features,
            vec!["inductive".to_owned(), "unit".to_owned()]
        );
        assert!(json.contains("\"trusted\":false"));
        assert!(json.contains("\"proof_evidence\":false"));
    }

    #[test]
    fn package_audit_disk_memo_key_is_schema_separated() {
        let input = fixture_key_input();

        assert_ne!(
            package_audit_cache_key(&input),
            package_audit_disk_memo_key(&input)
        );
        assert_ne!(
            package_audit_process_memo_key(&input),
            package_audit_disk_memo_key(&input)
        );
        assert_eq!(
            package_audit_disk_memo_key_input(&input).schema,
            PACKAGE_AUDIT_DISK_MEMO_SCHEMA
        );
    }

    #[test]
    fn package_audit_disk_memo_result_entry_round_trips_canonical_json() {
        let key_input = package_audit_disk_memo_key_input(&fixture_key_input());
        let entry = PackageAuditResultEntry {
            schema: PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA.to_owned(),
            cache_key: package_audit_disk_memo_key(&key_input),
            trusted: false,
            proof_evidence: false,
            key_input,
            status: PackageAuditCachedStatus::Accepted,
            diagnostic_reason: None,
            trust_boundary: "disk memo entry is not proof evidence".to_owned(),
        };

        let json = package_audit_disk_memo_result_entry_json(&entry);
        let parsed = parse_package_audit_disk_memo_result_entry_json(&json).unwrap();

        assert_eq!(package_audit_disk_memo_result_entry_json(&parsed), json);
        assert_eq!(parsed.schema, PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA);
        assert_eq!(parsed.key_input.schema, PACKAGE_AUDIT_DISK_MEMO_SCHEMA);
        assert!(!parsed.trusted);
        assert!(!parsed.proof_evidence);
    }

    #[test]
    fn package_reference_summary_cache_key_is_schema_separated() {
        let input = fixture_key_input();
        let reference_input = package_reference_summary_cache_key_input(&input);

        assert_ne!(
            package_audit_cache_key(&input),
            package_reference_summary_cache_key(&reference_input)
        );
        assert_ne!(
            package_audit_disk_memo_key(&input),
            package_reference_summary_cache_key(&reference_input)
        );
        assert_eq!(
            reference_input.schema,
            PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA
        );
    }

    #[test]
    fn package_reference_summary_cache_entry_round_trips_canonical_json() {
        let entry = fixture_reference_summary_cache_entry();

        let json = package_reference_summary_cache_entry_json(&entry);
        let parsed = parse_package_reference_summary_cache_entry_json(&json).unwrap();

        assert_eq!(package_reference_summary_cache_entry_json(&parsed), json);
        assert_eq!(parsed.schema, PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA);
        assert_eq!(
            parsed.key_input.schema,
            PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA
        );
        assert_eq!(parsed.summary.mode, PackageCheckerMode::Reference);
        assert!(!parsed.trusted);
        assert!(!parsed.proof_evidence);
    }

    #[test]
    fn package_reference_summary_cache_entry_requires_proof_evidence_false() {
        let mut entry = fixture_reference_summary_cache_entry();
        entry.proof_evidence = true;

        let error = validate_package_reference_summary_cache_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("proof_evidence"));
    }

    #[test]
    fn package_import_context_export_cache_entry_round_trips_canonical_json() {
        let entry = fixture_import_context_export_cache_entry();

        let json = package_import_context_export_cache_entry_json(&entry);
        let parsed = parse_package_import_context_export_cache_entry_json(&json).unwrap();

        assert_eq!(
            package_import_context_export_cache_entry_json(&parsed),
            json
        );
        assert_eq!(
            parsed.schema,
            PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA
        );
        assert_eq!(
            parsed.key_input.schema,
            PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA
        );
        assert_eq!(
            parsed.dependency_exports,
            parsed.key_input.dependency_exports
        );
        assert!(!parsed.trusted);
        assert!(!parsed.proof_evidence);
        assert!(!json.contains("/tmp/"));
    }

    #[test]
    fn package_import_context_export_cache_key_preserves_dependency_order() {
        let input = fixture_import_context_export_cache_key_input();
        let mut reordered = input.clone();
        reordered.dependency_exports.swap(0, 1);

        assert_ne!(
            package_import_context_export_cache_key(&input),
            package_import_context_export_cache_key(&reordered)
        );
    }

    #[test]
    fn package_import_context_export_cache_key_changes_for_external_package_identity() {
        let input = fixture_import_context_export_cache_key_input();
        let mut changed = input.clone();
        changed.dependency_exports[1].version = Some(PackageVersion::new("0.2.0"));

        assert_ne!(
            package_import_context_export_cache_key(&input),
            package_import_context_export_cache_key(&changed)
        );
    }

    #[test]
    fn package_import_context_export_cache_rejects_local_package_identity() {
        let mut entry = fixture_import_context_export_cache_entry();
        entry.dependency_exports[0].package = Some(PackageId::new("unexpected-package"));
        entry.key_input.dependency_exports = entry.dependency_exports.clone();
        entry.cache_key = package_import_context_export_cache_key(&entry.key_input);

        let error = validate_package_import_context_export_cache_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("package"));
    }

    #[test]
    fn package_audit_graph_inventory_counts_entries_edges_and_layers() {
        let external = lock_entry("Fixture.External", PackageLockEntryOrigin::External, vec![]);
        let local_b = lock_entry(
            "Fixture.B",
            PackageLockEntryOrigin::Local,
            vec![lock_import(&external)],
        );
        let local_a = lock_entry(
            "Fixture.A",
            PackageLockEntryOrigin::Local,
            vec![lock_import(&local_b), lock_import(&external)],
        );
        let lock = PackageLockManifest {
            schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("0.1.0"),
            manifest: PackageLockManifestReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(90),
            },
            entries: vec![local_a, external, local_b],
        };

        let inventory = package_audit_graph_inventory(&lock).unwrap();

        assert_eq!(
            inventory,
            PackageAuditGraphInventory {
                local_module_count: 2,
                external_import_count: 1,
                lock_entry_count: 3,
                direct_import_edge_count: 3,
                local_reverse_edge_count: 1,
                topological_layer_count: 3,
            }
        );
    }

    fn fixture_result_entry(status: PackageAuditCachedStatus) -> PackageAuditResultEntry {
        let key_input = fixture_key_input();
        PackageAuditResultEntry {
            schema: PACKAGE_AUDIT_RESULT_SCHEMA.to_owned(),
            cache_key: package_audit_cache_key(&key_input),
            trusted: false,
            proof_evidence: false,
            key_input,
            status,
            diagnostic_reason: None,
            trust_boundary: "cache entry is not proof evidence".to_owned(),
        }
    }

    fn fixture_reference_summary_cache_entry() -> PackageReferenceSummaryCacheEntry {
        let mut key_input = fixture_key_input();
        key_input.schema = PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA.to_owned();
        key_input.checker.mode = "reference".to_owned();
        key_input.checker.checker_id = "npa-checker-ref".to_owned();
        key_input.checker.checker_profile = "npa.checker.reference.v0.1".to_owned();
        let summary = PackageCheckerSummary {
            module: key_input.module.clone(),
            checker: key_input.checker.checker_id.clone(),
            profile: key_input.checker.checker_profile.clone(),
            mode: PackageCheckerMode::Reference,
            status: "passed".to_owned(),
            export_hash: key_input.export_hash,
            certificate_hash: key_input.certificate_hash,
            axiom_report_hash: key_input.axiom_report_hash,
        };
        let cache_key = package_reference_summary_cache_key(&key_input);
        PackageReferenceSummaryCacheEntry {
            schema: PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA.to_owned(),
            cache_key,
            trusted: false,
            proof_evidence: false,
            key_input,
            summary,
            trust_boundary: "reference summary cache entry is not proof evidence".to_owned(),
        }
    }

    fn fixture_import_context_export_cache_entry() -> PackageImportContextExportCacheEntry {
        let key_input = fixture_import_context_export_cache_key_input();
        PackageImportContextExportCacheEntry {
            schema: PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA.to_owned(),
            cache_key: package_import_context_export_cache_key(&key_input),
            trusted: false,
            proof_evidence: false,
            dependency_exports: key_input.dependency_exports.clone(),
            key_input,
            trust_boundary: "import context export cache entry is not proof evidence".to_owned(),
        }
    }

    fn fixture_import_context_export_cache_key_input() -> PackageImportContextExportCacheKeyInput {
        PackageImportContextExportCacheKeyInput {
            schema: PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA.to_owned(),
            package_id: PackageId::new("fixture-package"),
            package_version: PackageVersion::new("0.1.0"),
            package_lock_schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            core_spec: "npa.core.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_policy_hash: hash(42),
            owner_module: module("Fixture.Target"),
            dependency_exports: vec![
                PackageImportContextExportData {
                    module: module("Fixture.LocalImport"),
                    origin: PackageLockEntryOrigin::Local,
                    package: None,
                    version: None,
                    export_hash: hash(43),
                    certificate_hash: hash(44),
                    axiom_report_hash: hash(45),
                    certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
                },
                PackageImportContextExportData {
                    module: module("Fixture.ExternalImport"),
                    origin: PackageLockEntryOrigin::External,
                    package: Some(PackageId::new("external-package")),
                    version: Some(PackageVersion::new("0.1.0")),
                    export_hash: hash(46),
                    certificate_hash: hash(47),
                    axiom_report_hash: hash(48),
                    certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
                },
            ],
        }
    }

    fn fixture_key_input() -> PackageAuditCacheKeyInput {
        PackageAuditCacheKeyInput {
            schema: PACKAGE_AUDIT_CACHE_SCHEMA.to_owned(),
            package_id: PackageId::new("fixture-package"),
            package_version: PackageVersion::new("0.1.0"),
            package_lock_schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            core_spec: "npa.core.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            package_lock_hash: hash(1),
            package_policy_hash: hash(2),
            checker: PackageAuditCheckerIdentity {
                mode: "reference".to_owned(),
                checker_id: "npa-checker-ref".to_owned(),
                checker_version: "0.1.0".to_owned(),
                checker_build_hash: hash(3),
                checker_profile: "npa.checker.reference.v0.1".to_owned(),
                runner_policy_hash: Some(hash(4)),
            },
            module: module("Fixture.Target"),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new("Fixture/Target/certificate.npcert"),
            certificate_file_hash: hash(5),
            certificate_hash: hash(6),
            export_hash: hash(7),
            axiom_report_hash: hash(8),
            direct_imports: vec![
                PackageAuditImportIdentity {
                    module: module("Fixture.ImportA"),
                    export_hash: hash(19),
                    certificate_hash: hash(20),
                },
                PackageAuditImportIdentity {
                    module: module("Fixture.ImportB"),
                    export_hash: hash(21),
                    certificate_hash: hash(22),
                },
            ],
            dependency_summary_hash: Some(hash(9)),
            enabled_core_features: vec!["unit".to_owned(), "inductive".to_owned()],
        }
    }

    fn lock_entry(
        name: &str,
        origin: PackageLockEntryOrigin,
        imports: Vec<PackageLockImport>,
    ) -> PackageLockEntry {
        PackageLockEntry {
            module: module(name),
            origin,
            certificate: PackagePath::new(format!("certs/{}.npcert", name.replace('.', "_"))),
            certificate_file_hash: hash(seed_for(name, 1)),
            export_hash: hash(seed_for(name, 2)),
            axiom_report_hash: hash(seed_for(name, 3)),
            certificate_hash: hash(seed_for(name, 4)),
            imports,
            package: (origin == PackageLockEntryOrigin::External)
                .then(|| PackageId::new("external-package")),
            version: (origin == PackageLockEntryOrigin::External)
                .then(|| PackageVersion::new("0.1.0")),
        }
    }

    fn lock_import(entry: &PackageLockEntry) -> PackageLockImport {
        PackageLockImport {
            module: entry.module.clone(),
            export_hash: entry.export_hash,
            certificate_hash: entry.certificate_hash,
        }
    }

    fn module(value: &str) -> Name {
        Name::from_dotted(value)
    }

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }

    fn seed_for(name: &str, offset: u8) -> u8 {
        name.bytes().fold(offset, u8::wrapping_add)
    }
}

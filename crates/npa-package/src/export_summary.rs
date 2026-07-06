//! Verified export summary artifact model and canonical JSON.
//!
//! The summary is deterministic source-free metadata derived from package-lock
//! identity and certificate bytes. It is explicitly not proof evidence and does
//! not replace certificate bytes or checker verdicts.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        duplicate_key_error, expect_object, field_path, global_ref_json, global_ref_sort_key,
        hash_json, json_array, json_bool, json_object_in_order, json_string, parse_artifact_json,
        parse_global_ref, reject_unknown_fields, required_array, required_bool, required_hash,
        required_name, required_path, required_string, validate_artifact_path, validate_global_ref,
        validate_module_name, validate_package_identity, validate_plain_string,
        PackageArtifactOrigin, PackageGlobalRef,
    },
    audit_cache::{
        package_audit_direct_imports_for_entry, PackageAuditImportIdentity,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA,
    },
    error::{
        PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult, PackageLockError,
    },
    hash::{format_package_hash, package_file_hash, PackageHash},
    incremental_projection::{
        add_changed_reason, package_incremental_full_projection_plan,
        package_incremental_projection_plan_from_changed_modules, push_reason,
        PackageIncrementalProjectionPlan,
    },
    lock::{
        build_package_lock_graph, PackageLockEntry, PackageLockEntryOrigin, PackageLockManifest,
    },
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
};

/// Default package-relative path for checked verified export summaries.
pub const PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH: &str = "generated/verified-export-summary.json";

/// Deterministic module ordering used by verified export summaries.
pub const PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL: &str =
    "package-lock-topological";

/// Stable trust-boundary note embedded in verified export summaries.
pub const PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY: &str =
    "verified export summary is not proof evidence; certificate bytes and checker verdicts dominate";

/// Deterministic source-free package export summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedExportSummary {
    /// Summary schema string; must equal [`PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA`].
    pub schema: String,
    /// Package identity copied from the validated package manifest.
    pub package: PackageId,
    /// Exact package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Core specification profile copied from the package manifest.
    pub core_spec: String,
    /// Canonical certificate format profile copied from the package manifest.
    pub certificate_format: String,
    /// Exact generated package-lock file hash used for extraction.
    pub package_lock_hash: PackageHash,
    /// Deterministic module ordering used by [`Self::modules`].
    pub module_order: String,
    /// Must be false: summaries are never proof evidence.
    pub trusted: bool,
    /// Human-readable trust-boundary note.
    pub trust_boundary: String,
    /// Per-module source-free summaries.
    pub modules: Vec<PackageVerifiedExportSummaryModule>,
    /// Self hash of canonical summary bytes excluding this field.
    pub summary_hash: PackageHash,
}

impl PackageVerifiedExportSummary {
    /// Return this summary with schema-defined array ordering and computed self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_verified_export_summary(&mut self);
        self.summary_hash = compute_package_verified_export_summary_hash(&self)?;
        Ok(self)
    }

    /// Serialize this summary as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_package_verified_export_summary(self)?;
        let mut normalized = self.clone();
        normalize_verified_export_summary(&mut normalized);
        Ok(verified_export_summary_json_unchecked(&normalized, true))
    }
}

/// One module entry in a verified export summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedExportSummaryModule {
    /// Module name.
    pub module: Name,
    /// Whether this entry is local or external.
    pub origin: PackageArtifactOrigin,
    /// Package-relative certificate artifact path.
    pub certificate: PackagePath,
    /// Exact SHA-256 hash of the certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Canonical module export hash.
    pub export_hash: PackageHash,
    /// Canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Direct import identities declared by the certificate and package lock.
    pub direct_imports: Vec<PackageAuditImportIdentity>,
    /// Public exported global declaration identities.
    pub exported_globals: Vec<PackageGlobalRef>,
    /// Module-level axiom identities.
    pub module_axioms: Vec<PackageGlobalRef>,
    /// Core feature names required by this module.
    pub core_features: Vec<String>,
}

/// Parse and validate canonical verified export summary JSON.
pub fn parse_package_verified_export_summary_json(
    source: &str,
) -> PackageArtifactResult<PackageVerifiedExportSummary> {
    let root = parse_artifact_json(source)?;
    let summary = parse_verified_export_summary_value(&root)?;
    validate_package_verified_export_summary(&summary)?;
    let canonical = summary.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "verified export summary JSON bytes",
        ));
    }
    Ok(summary)
}

/// Validate a verified export summary without reading files or running checkers.
pub fn validate_package_verified_export_summary(
    summary: &PackageVerifiedExportSummary,
) -> PackageArtifactResult<()> {
    validate_verified_export_summary_shape_without_self_hash(summary)?;
    let expected_hash = compute_package_verified_export_summary_hash(summary)?;
    if expected_hash != summary.summary_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "summary_hash",
            "summary_hash",
            format_package_hash(&expected_hash),
            format_package_hash(&summary.summary_hash),
        ));
    }
    Ok(())
}

/// Validate summary module identities against a package lock.
pub fn validate_package_verified_export_summary_against_lock(
    summary: &PackageVerifiedExportSummary,
    lock: &PackageLockManifest,
    package_lock_hash: PackageHash,
) -> PackageArtifactResult<()> {
    validate_package_verified_export_summary(summary)?;
    if summary.package_lock_hash != package_lock_hash {
        return Err(PackageArtifactError::summary_mismatch(
            "package_lock_hash",
            "package_lock_hash",
            format_package_hash(&package_lock_hash),
            format_package_hash(&summary.package_lock_hash),
        ));
    }

    let graph = build_package_lock_graph(lock).map_err(package_lock_graph_error)?;
    if summary.modules.len() != graph.topological_order.len() {
        return Err(PackageArtifactError::summary_mismatch(
            "modules",
            "modules",
            graph.topological_order.len().to_string(),
            summary.modules.len().to_string(),
        ));
    }

    let entries = lock
        .entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect::<BTreeMap<_, _>>();
    for (index, expected_module) in graph.topological_order.iter().enumerate() {
        let module = &summary.modules[index];
        if module.module != *expected_module {
            return Err(PackageArtifactError::summary_mismatch(
                format!("modules[{index}].module"),
                "module",
                expected_module.as_dotted(),
                module.module.as_dotted(),
            ));
        }
        let entry = entries.get(expected_module).ok_or_else(|| {
            PackageArtifactError::summary_mismatch(
                format!("modules[{index}].module"),
                "module",
                "package lock entry",
                expected_module.as_dotted(),
            )
        })?;
        validate_summary_module_against_lock_entry(module, entry, index)?;
    }

    Ok(())
}

/// Compute the verified export summary self hash over canonical bytes excluding
/// the self-hash field.
pub fn compute_package_verified_export_summary_hash(
    summary: &PackageVerifiedExportSummary,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = summary.clone();
    normalize_verified_export_summary(&mut normalized);
    validate_verified_export_summary_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        verified_export_summary_json_unchecked(&normalized, false).as_bytes(),
    ))
}

/// Plan an incremental verified export-summary check against current package metadata.
///
/// The plan is optimization metadata only. It uses the current package-lock hash
/// plus per-module certificate, export, axiom-report, and direct-import
/// identities as the invalidation boundary.
pub fn package_verified_export_summary_incremental_projection_plan(
    summary: &PackageVerifiedExportSummary,
    package: &PackageId,
    version: &PackageVersion,
    core_spec: &str,
    certificate_format: &str,
    package_lock_hash: PackageHash,
    current_lock: &PackageLockManifest,
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let mut full_reasons = Vec::new();
    push_reason(
        &mut full_reasons,
        summary.schema != PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA,
        "projection_schema_changed",
    );
    push_reason(
        &mut full_reasons,
        &summary.package != package || &summary.version != version,
        "package_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        summary.core_spec != core_spec,
        "core_spec_changed",
    );
    push_reason(
        &mut full_reasons,
        summary.certificate_format != certificate_format,
        "certificate_format_changed",
    );
    push_reason(
        &mut full_reasons,
        summary.module_order != PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL,
        "module_order_changed",
    );
    push_reason(&mut full_reasons, summary.trusted, "trusted_flag_changed");
    push_reason(
        &mut full_reasons,
        summary.trust_boundary != PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY,
        "trust_boundary_changed",
    );
    push_reason(
        &mut full_reasons,
        current_lock.schema != crate::schema::PACKAGE_LOCK_SCHEMA,
        "package_lock_schema_changed",
    );

    let changed_modules = export_summary_changed_modules(summary, current_lock, &mut full_reasons);
    if summary.package_lock_hash != package_lock_hash
        && changed_modules.is_empty()
        && full_reasons.is_empty()
    {
        return package_incremental_full_projection_plan(
            "verified-export-summary",
            current_lock,
            ["package_lock_unattributed_change"],
        );
    }

    package_incremental_projection_plan_from_changed_modules(
        "verified-export-summary",
        current_lock,
        full_reasons,
        changed_modules,
    )
}

fn validate_verified_export_summary_shape_without_self_hash(
    summary: &PackageVerifiedExportSummary,
) -> PackageArtifactResult<()> {
    if summary.schema != PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA,
            summary.schema.clone(),
        ));
    }
    validate_package_identity(&summary.package, &summary.version)?;
    validate_plain_string(&summary.core_spec, "core_spec")?;
    validate_plain_string(&summary.certificate_format, "certificate_format")?;
    if summary.module_order != PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL {
        return Err(PackageArtifactError::invalid_enum_value(
            "module_order",
            "module_order",
            PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL,
            summary.module_order.clone(),
        ));
    }
    if summary.trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "trusted", "trusted", "false", "true",
        ));
    }
    if summary.trust_boundary != PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY {
        return Err(PackageArtifactError::invalid_enum_value(
            "trust_boundary",
            "trust_boundary",
            PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY,
            summary.trust_boundary.clone(),
        ));
    }
    let mut modules = BTreeSet::<Name>::new();
    for (index, module) in summary.modules.iter().enumerate() {
        validate_summary_module(module, index)?;
        if !modules.insert(module.module.clone()) {
            return Err(duplicate_key_error(
                format!("modules[{index}].module"),
                "module",
                PackageArtifactErrorReason::DuplicateModule,
                module.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_summary_module(
    module: &PackageVerifiedExportSummaryModule,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("modules[{index}]");
    validate_module_name(&module.module, field_path(&path, "module"))?;
    validate_artifact_path(&module.certificate, field_path(&path, "certificate"))?;
    validate_import_identities(&module.direct_imports, &path)?;
    validate_global_refs(
        &module.exported_globals,
        &path,
        "exported_globals",
        PackageArtifactErrorReason::DuplicateTheoremEntry,
    )?;
    validate_global_refs(
        &module.module_axioms,
        &path,
        "module_axioms",
        PackageArtifactErrorReason::DuplicateAxiom,
    )?;
    for (feature_index, feature) in module.core_features.iter().enumerate() {
        validate_plain_string(feature, format!("{path}.core_features[{feature_index}]"))?;
    }
    Ok(())
}

fn validate_import_identities(
    imports: &[PackageAuditImportIdentity],
    path: &str,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, import) in imports.iter().enumerate() {
        let path = format!("{path}.direct_imports[{index}]");
        validate_module_name(&import.module, field_path(&path, "module"))?;
        let key = import_identity_json(import);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                field_path(&path, "module"),
                "direct_imports",
                PackageArtifactErrorReason::DuplicateModule,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_global_refs(
    refs: &[PackageGlobalRef],
    path: &str,
    field: &str,
    duplicate_reason: PackageArtifactErrorReason,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, global_ref) in refs.iter().enumerate() {
        let path = format!("{path}.{field}[{index}]");
        validate_global_ref(global_ref, &path)?;
        let key = global_ref_sort_key(global_ref);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                field_path(&path, "name"),
                field,
                duplicate_reason,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_summary_module_against_lock_entry(
    module: &PackageVerifiedExportSummaryModule,
    entry: &PackageLockEntry,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("modules[{index}]");
    compare_field(
        &path,
        "origin",
        origin_from_lock(entry.origin).as_str(),
        module.origin.as_str(),
    )?;
    compare_field(
        &path,
        "certificate",
        entry.certificate.as_str(),
        module.certificate.as_str(),
    )?;
    compare_hash(
        &path,
        "certificate_file_hash",
        entry.certificate_file_hash,
        module.certificate_file_hash,
    )?;
    compare_hash(&path, "export_hash", entry.export_hash, module.export_hash)?;
    compare_hash(
        &path,
        "certificate_hash",
        entry.certificate_hash,
        module.certificate_hash,
    )?;
    compare_hash(
        &path,
        "axiom_report_hash",
        entry.axiom_report_hash,
        module.axiom_report_hash,
    )?;
    let expected_imports = package_audit_direct_imports_for_entry(entry);
    if expected_imports != module.direct_imports {
        return Err(PackageArtifactError::summary_mismatch(
            field_path(&path, "direct_imports"),
            "direct_imports",
            json_array(expected_imports.iter().map(import_identity_json).collect()),
            json_array(
                module
                    .direct_imports
                    .iter()
                    .map(import_identity_json)
                    .collect(),
            ),
        ));
    }
    Ok(())
}

fn compare_field(
    path: &str,
    field: &str,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactResult<()> {
    let expected = expected.into();
    let actual = actual.into();
    if expected == actual {
        return Ok(());
    }
    Err(PackageArtifactError::summary_mismatch(
        field_path(path, field),
        field,
        expected,
        actual,
    ))
}

fn compare_hash(
    path: &str,
    field: &str,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageArtifactResult<()> {
    if expected == actual {
        return Ok(());
    }
    Err(PackageArtifactError::summary_mismatch(
        field_path(path, field),
        field,
        format_package_hash(&expected),
        format_package_hash(&actual),
    ))
}

fn export_summary_changed_modules(
    summary: &PackageVerifiedExportSummary,
    current_lock: &PackageLockManifest,
    full_reasons: &mut Vec<String>,
) -> BTreeMap<Name, BTreeSet<String>> {
    let previous = summary
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();
    let current = current_lock
        .entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect::<BTreeMap<_, _>>();
    let mut changed = BTreeMap::<Name, BTreeSet<String>>::new();

    for module in previous.keys() {
        if !current.contains_key(module) {
            full_reasons.push("module_removed".to_owned());
        }
    }
    for (module, entry) in current {
        let Some(previous) = previous.get(&module) else {
            changed
                .entry(module)
                .or_default()
                .insert("module_added".to_owned());
            continue;
        };
        add_changed_reason(
            &mut changed,
            &module,
            !lock_origin_matches_artifact(entry.origin, previous.origin),
            "module_origin_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.certificate != previous.certificate,
            "certificate_path_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.certificate_file_hash != previous.certificate_file_hash,
            "certificate_file_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.export_hash != previous.export_hash,
            "export_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.certificate_hash != previous.certificate_hash,
            "certificate_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.axiom_report_hash != previous.axiom_report_hash,
            "axiom_report_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            package_audit_direct_imports_for_entry(entry) != previous.direct_imports,
            "direct_import_identity_changed",
        );
    }

    changed
}

fn lock_origin_matches_artifact(
    lock_origin: PackageLockEntryOrigin,
    artifact_origin: PackageArtifactOrigin,
) -> bool {
    matches!(
        (lock_origin, artifact_origin),
        (PackageLockEntryOrigin::Local, PackageArtifactOrigin::Local)
            | (
                PackageLockEntryOrigin::External,
                PackageArtifactOrigin::External
            )
    )
}

fn normalize_verified_export_summary(summary: &mut PackageVerifiedExportSummary) {
    for module in &mut summary.modules {
        normalize_summary_module(module);
    }
}

fn normalize_summary_module(module: &mut PackageVerifiedExportSummaryModule) {
    module.direct_imports.sort_by_key(import_identity_json);
    module.direct_imports.dedup_by(|left, right| {
        left.module == right.module
            && left.export_hash == right.export_hash
            && left.certificate_hash == right.certificate_hash
    });
    module.exported_globals.sort_by_key(global_ref_sort_key);
    module
        .exported_globals
        .dedup_by(|left, right| left == right);
    module.module_axioms.sort_by_key(global_ref_sort_key);
    module.module_axioms.dedup_by(|left, right| left == right);
    module.core_features.sort();
    module.core_features.dedup();
}

fn verified_export_summary_json_unchecked(
    summary: &PackageVerifiedExportSummary,
    include_hash: bool,
) -> String {
    let mut fields = vec![
        ("schema", json_string(&summary.schema)),
        ("package", json_string(summary.package.as_str())),
        ("version", json_string(summary.version.as_str())),
        ("core_spec", json_string(&summary.core_spec)),
        (
            "certificate_format",
            json_string(&summary.certificate_format),
        ),
        ("package_lock_hash", hash_json(summary.package_lock_hash)),
        ("module_order", json_string(&summary.module_order)),
        ("trusted", json_bool(summary.trusted)),
        ("trust_boundary", json_string(&summary.trust_boundary)),
        (
            "modules",
            json_array(summary.modules.iter().map(summary_module_json).collect()),
        ),
    ];
    if include_hash {
        fields.push(("summary_hash", hash_json(summary.summary_hash)));
    }
    json_object_in_order(fields)
}

fn summary_module_json(module: &PackageVerifiedExportSummaryModule) -> String {
    json_object_in_order(vec![
        ("module", json_string(&module.module.as_dotted())),
        ("origin", json_string(module.origin.as_str())),
        ("certificate", json_string(module.certificate.as_str())),
        (
            "certificate_file_hash",
            hash_json(module.certificate_file_hash),
        ),
        ("export_hash", hash_json(module.export_hash)),
        ("certificate_hash", hash_json(module.certificate_hash)),
        ("axiom_report_hash", hash_json(module.axiom_report_hash)),
        (
            "direct_imports",
            json_array(
                module
                    .direct_imports
                    .iter()
                    .map(import_identity_json)
                    .collect(),
            ),
        ),
        (
            "exported_globals",
            json_array(
                module
                    .exported_globals
                    .iter()
                    .map(global_ref_json)
                    .collect(),
            ),
        ),
        (
            "module_axioms",
            json_array(module.module_axioms.iter().map(global_ref_json).collect()),
        ),
        (
            "core_features",
            json_array(
                module
                    .core_features
                    .iter()
                    .map(|feature| json_string(feature))
                    .collect(),
            ),
        ),
    ])
}

fn import_identity_json(import: &PackageAuditImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn parse_verified_export_summary_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageVerifiedExportSummary> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, VERIFIED_EXPORT_SUMMARY_FIELDS)?;
    Ok(PackageVerifiedExportSummary {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        core_spec: required_string(members, "$", "core_spec")?,
        certificate_format: required_string(members, "$", "certificate_format")?,
        package_lock_hash: required_hash(members, "$", "package_lock_hash")?,
        module_order: required_string(members, "$", "module_order")?,
        trusted: required_bool(members, "$", "trusted")?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
        modules: required_array(members, "$", "modules")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_summary_module(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        summary_hash: required_hash(members, "$", "summary_hash")?,
    })
}

fn parse_summary_module(
    index: usize,
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageVerifiedExportSummaryModule> {
    let path = format!("modules[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, VERIFIED_EXPORT_SUMMARY_MODULE_FIELDS)?;
    let origin_path = field_path(&path, "origin");
    Ok(PackageVerifiedExportSummaryModule {
        module: required_name(members, &path, "module")?,
        origin: PackageArtifactOrigin::parse(
            &required_string(members, &path, "origin")?,
            &origin_path,
        )?,
        certificate: required_path(members, &path, "certificate")?,
        certificate_file_hash: required_hash(members, &path, "certificate_file_hash")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, &path, "axiom_report_hash")?,
        direct_imports: required_array(members, &path, "direct_imports")?
            .iter()
            .enumerate()
            .map(|(import_index, value)| parse_import_identity(&path, import_index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        exported_globals: required_array(members, &path, "exported_globals")?
            .iter()
            .enumerate()
            .map(|(global_index, value)| {
                parse_global_ref(value, &format!("{path}.exported_globals[{global_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        module_axioms: required_array(members, &path, "module_axioms")?
            .iter()
            .enumerate()
            .map(|(axiom_index, value)| {
                parse_global_ref(value, &format!("{path}.module_axioms[{axiom_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        core_features: required_array(members, &path, "core_features")?
            .iter()
            .enumerate()
            .map(|(feature_index, value)| {
                value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        format!("{path}.core_features[{feature_index}]"),
                        Some("core_features".to_owned()),
                        "string",
                        value.kind().as_str(),
                    )
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_import_identity(
    owner_path: &str,
    index: usize,
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAuditImportIdentity> {
    let path = format!("{owner_path}.direct_imports[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_IDENTITY_FIELDS)?;
    Ok(PackageAuditImportIdentity {
        module: required_name(members, &path, "module")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

fn origin_from_lock(origin: PackageLockEntryOrigin) -> PackageArtifactOrigin {
    match origin {
        PackageLockEntryOrigin::Local => PackageArtifactOrigin::Local,
        PackageLockEntryOrigin::External => PackageArtifactOrigin::External,
    }
}

fn package_lock_graph_error(error: PackageLockError) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "package_lock",
        "package_lock",
        "valid package lock graph",
        error.reason_code.as_str(),
    )
}

const VERIFIED_EXPORT_SUMMARY_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "core_spec",
    "certificate_format",
    "package_lock_hash",
    "module_order",
    "trusted",
    "trust_boundary",
    "modules",
    "summary_hash",
];

const VERIFIED_EXPORT_SUMMARY_MODULE_FIELDS: &[&str] = &[
    "module",
    "origin",
    "certificate",
    "certificate_file_hash",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
    "direct_imports",
    "exported_globals",
    "module_axioms",
    "core_features",
];

const IMPORT_IDENTITY_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lock::{PackageLockImport, PackageLockManifestReference},
        manifest::PackageVersion,
        schema::PACKAGE_LOCK_SCHEMA,
    };

    #[test]
    fn verified_export_summary_is_deterministic() {
        let mut summary = fixture_summary();
        summary.modules[1].core_features = vec![
            "feature_beta".to_owned(),
            "feature_alpha".to_owned(),
            "feature_alpha".to_owned(),
        ];

        let first = summary.clone().with_computed_hash().unwrap();
        let second = summary.with_computed_hash().unwrap();

        assert_eq!(
            first.canonical_json().unwrap(),
            second.canonical_json().unwrap()
        );
        let parsed =
            parse_package_verified_export_summary_json(&first.canonical_json().unwrap()).unwrap();
        assert_eq!(parsed, first);
        assert!(first
            .canonical_json()
            .unwrap()
            .contains("not proof evidence"));
    }

    #[test]
    fn verified_export_summary_requires_trusted_false() {
        let mut summary = fixture_summary().with_computed_hash().unwrap();
        summary.trusted = true;

        let error = validate_package_verified_export_summary(&summary).unwrap_err();

        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("trusted"));
    }

    #[test]
    fn verified_export_summary_rejects_tampered_export_hash() {
        let lock = fixture_lock();
        let mut summary = fixture_summary().with_computed_hash().unwrap();
        summary.modules[0].export_hash = hash(99);
        summary = summary.with_computed_hash().unwrap();

        let error =
            validate_package_verified_export_summary_against_lock(&summary, &lock, hash(90))
                .unwrap_err();

        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::SummaryMismatch
        );
        assert_eq!(error.field.as_deref(), Some("export_hash"));
    }

    #[test]
    fn verified_export_summary_rejects_tampered_direct_import() {
        let lock = fixture_lock();
        let mut summary = fixture_summary().with_computed_hash().unwrap();
        summary.modules[1].direct_imports[0].certificate_hash = hash(77);
        summary = summary.with_computed_hash().unwrap();

        let error =
            validate_package_verified_export_summary_against_lock(&summary, &lock, hash(90))
                .unwrap_err();

        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::SummaryMismatch
        );
        assert_eq!(error.field.as_deref(), Some("direct_imports"));
    }

    fn fixture_summary() -> PackageVerifiedExportSummary {
        PackageVerifiedExportSummary {
            schema: PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("0.1.0"),
            core_spec: "npa.core.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            package_lock_hash: hash(90),
            module_order: PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL.to_owned(),
            trusted: false,
            trust_boundary: PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY.to_owned(),
            modules: vec![summary_module_a(), summary_module_b()],
            summary_hash: PackageHash::new([0_u8; 32]),
        }
    }

    fn summary_module_a() -> PackageVerifiedExportSummaryModule {
        PackageVerifiedExportSummaryModule {
            module: module("Fixture.A"),
            origin: PackageArtifactOrigin::Local,
            certificate: PackagePath::new("certs/Fixture_A.npcert"),
            certificate_file_hash: hash(11),
            export_hash: hash(12),
            axiom_report_hash: hash(13),
            certificate_hash: hash(14),
            direct_imports: Vec::new(),
            exported_globals: vec![global("Fixture.A", "Fixture.A.id", 12, 14, 15)],
            module_axioms: Vec::new(),
            core_features: Vec::new(),
        }
    }

    fn summary_module_b() -> PackageVerifiedExportSummaryModule {
        PackageVerifiedExportSummaryModule {
            module: module("Fixture.B"),
            origin: PackageArtifactOrigin::Local,
            certificate: PackagePath::new("certs/Fixture_B.npcert"),
            certificate_file_hash: hash(21),
            export_hash: hash(22),
            axiom_report_hash: hash(23),
            certificate_hash: hash(24),
            direct_imports: vec![PackageAuditImportIdentity {
                module: module("Fixture.A"),
                export_hash: hash(12),
                certificate_hash: hash(14),
            }],
            exported_globals: vec![global("Fixture.B", "Fixture.B.id", 22, 24, 25)],
            module_axioms: Vec::new(),
            core_features: vec!["feature_alpha".to_owned()],
        }
    }

    fn fixture_lock() -> PackageLockManifest {
        let entry_a = lock_entry("Fixture.A", 11, 12, 13, 14, vec![]);
        let entry_b = lock_entry(
            "Fixture.B",
            21,
            22,
            23,
            24,
            vec![PackageLockImport {
                module: entry_a.module.clone(),
                export_hash: entry_a.export_hash,
                certificate_hash: entry_a.certificate_hash,
            }],
        );
        PackageLockManifest {
            schema: PACKAGE_LOCK_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("0.1.0"),
            manifest: PackageLockManifestReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(80),
            },
            entries: vec![entry_b, entry_a],
        }
    }

    fn lock_entry(
        name: &str,
        file_seed: u8,
        export_seed: u8,
        axiom_seed: u8,
        certificate_seed: u8,
        imports: Vec<PackageLockImport>,
    ) -> PackageLockEntry {
        PackageLockEntry {
            module: module(name),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(format!("certs/{}.npcert", name.replace('.', "_"))),
            certificate_file_hash: hash(file_seed),
            export_hash: hash(export_seed),
            axiom_report_hash: hash(axiom_seed),
            certificate_hash: hash(certificate_seed),
            imports,
            package: None,
            version: None,
        }
    }

    fn global(
        module_name: &str,
        declaration: &str,
        export_seed: u8,
        certificate_seed: u8,
        interface_seed: u8,
    ) -> PackageGlobalRef {
        PackageGlobalRef {
            module: module(module_name),
            name: module(declaration),
            export_hash: hash(export_seed),
            certificate_hash: hash(certificate_seed),
            decl_interface_hash: hash(interface_seed),
        }
    }

    fn module(name: &str) -> Name {
        Name::from_dotted(name)
    }

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }
}

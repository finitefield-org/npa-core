//! Registry module seed entry model and canonical JSON.
//!
//! Registry entries are distribution and search metadata. They help downstream
//! packages pin certificate artifacts, but they are not proof evidence and do
//! not replace local source-free certificate verification.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, field_path, file_reference_json, hash_json, json_array,
        json_object_in_order, json_string, parse_artifact_json, parse_file_reference,
        reject_unknown_fields, required_array, required_hash, required_name, required_string,
        validate_artifact_file_reference, validate_module_name, validate_package_identity,
        validate_plain_string, PackageArtifactFileReference, PackageArtifactOrigin,
        PackageCheckerMode, PackageCheckerSummary,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, PackageHash},
    json::{JsonMember, JsonValue},
    lock::{PackageLockEntry, PackageLockEntryOrigin, PackageLockImport, PackageLockManifest},
    manifest::{PackageManifest, PackageVersion},
    name::PackageId,
    schema::REGISTRY_MODULE_SCHEMA,
};

/// Generated `npa.registry.module.v0.1` module registry seed entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageRegistryModule {
    /// Registry module schema string; must equal [`REGISTRY_MODULE_SCHEMA`].
    pub schema: String,
    /// Package identity.
    pub package: PackageId,
    /// Package version.
    pub package_version: PackageVersion,
    /// Local package module represented by this registry entry.
    pub module: Name,
    /// Core spec profile.
    pub core_spec: String,
    /// Kernel profile.
    pub kernel_profile: String,
    /// Certificate format profile.
    pub certificate_format: String,
    /// Module export hash.
    pub export_hash: PackageHash,
    /// Module certificate hash.
    pub certificate_hash: PackageHash,
    /// Module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Certificate artifact identity.
    pub certificate: PackageArtifactFileReference,
    /// Direct imports sorted by module in canonical JSON.
    pub imports: Vec<PackageRegistryImport>,
    /// Source-free checker result metadata sorted canonically.
    pub checker_results: Vec<PackageRegistryCheckerResult>,
    /// Release artifact hashes relevant to this module.
    pub artifact_hashes: PackageRegistryArtifactHashes,
}

impl PackageRegistryModule {
    /// Serialize this registry entry as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_registry_module(self)?;
        let mut normalized = self.clone();
        normalize_registry_module(&mut normalized);
        Ok(registry_module_json_unchecked(&normalized))
    }
}

/// Direct import recorded in a registry module entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageRegistryImport {
    /// Imported module name.
    pub module: Name,
    /// Whether the import is local to this package or external.
    pub origin: PackageArtifactOrigin,
    /// External package id when [`Self::origin`] is external.
    pub package: Option<PackageId>,
    /// External package version when [`Self::origin`] is external.
    pub version: Option<PackageVersion>,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Registry checker status.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageRegistryCheckerStatus {
    /// Checker accepted this module.
    Accepted,
    /// Checker rejected this module.
    Rejected,
    /// Checker was not run.
    NotRun,
}

impl PackageRegistryCheckerStatus {
    /// Return the registry checker status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::NotRun => "not_run",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "accepted" => Ok(Self::Accepted),
            "rejected" => Ok(Self::Rejected),
            "not_run" => Ok(Self::NotRun),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "status",
                "accepted, rejected, or not_run",
                value,
            )),
        }
    }
}

/// Source-free checker result metadata recorded in a registry entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageRegistryCheckerResult {
    /// Checker identifier, for example `npa-checker-ref`.
    pub checker: String,
    /// Checker profile string.
    pub profile: String,
    /// Checker mode string, for example `reference`.
    pub mode: String,
    /// Stable checker status.
    pub status: PackageRegistryCheckerStatus,
    /// Verified module export hash.
    pub export_hash: PackageHash,
    /// Verified module certificate hash.
    pub certificate_hash: PackageHash,
    /// Verified module axiom report hash.
    pub axiom_report_hash: PackageHash,
}

/// Release artifact hashes copied into a registry entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageRegistryArtifactHashes {
    /// Exact file hash of `generated/package-lock.json`.
    pub package_lock_file_hash: PackageHash,
    /// Exact file hash of `generated/axiom-report.json`.
    pub axiom_report_file_hash: PackageHash,
    /// Exact file hash of `generated/theorem-index.json`.
    pub theorem_index_file_hash: PackageHash,
}

/// Inputs used to project module registry seed entries for a package release.
pub struct PackageRegistryModuleSeedInput<'a> {
    /// Validated package manifest metadata.
    pub manifest: &'a PackageManifest,
    /// Fresh package lock metadata.
    pub package_lock: &'a PackageLockManifest,
    /// Source-free checker summaries collected for publish metadata.
    pub checker_summaries: &'a [PackageCheckerSummary],
    /// Release artifact hashes copied into each registry entry.
    pub artifact_hashes: PackageRegistryArtifactHashes,
}

/// Build deterministic `npa.registry.module.v0.1` seed entries for local modules.
///
/// External package imports are included only as dependency pins in local
/// modules' direct import lists. No registry lookup, filesystem traversal, or
/// checker execution happens here.
pub fn build_package_registry_modules(
    input: PackageRegistryModuleSeedInput<'_>,
) -> PackageArtifactResult<Vec<PackageRegistryModule>> {
    ensure_lock_matches_manifest(input.manifest, input.package_lock)?;
    ensure_manifest_modules_locked(input.manifest, input.package_lock)?;
    let mut entries = input
        .package_lock
        .entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
        .map(|entry| registry_module_from_lock_entry(&input, entry))
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    validate_unique_registry_seed_modules(&entries)?;
    for entry in &mut entries {
        normalize_registry_module(entry);
        validate_registry_module(entry)?;
    }
    entries.sort_by_key(registry_module_sort_key);
    Ok(entries)
}

/// Parse and validate a checked-in registry module JSON artifact.
pub fn parse_registry_module_json(source: &str) -> PackageArtifactResult<PackageRegistryModule> {
    let root = parse_artifact_json(source)?;
    let entry = parse_registry_module_value(&root, "$")?;
    validate_registry_module(&entry)?;
    let canonical = entry.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "registry module JSON bytes",
        ));
    }
    Ok(entry)
}

/// Validate a registry module model without reading files or contacting a registry.
pub fn validate_registry_module(entry: &PackageRegistryModule) -> PackageArtifactResult<()> {
    if entry.schema != REGISTRY_MODULE_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            REGISTRY_MODULE_SCHEMA,
            entry.schema.clone(),
        ));
    }
    validate_package_identity(&entry.package, &entry.package_version)?;
    validate_module_name(&entry.module, "module")?;
    validate_plain_string(&entry.core_spec, "core_spec")?;
    validate_plain_string(&entry.kernel_profile, "kernel_profile")?;
    validate_plain_string(&entry.certificate_format, "certificate_format")?;
    validate_artifact_file_reference(&entry.certificate, "certificate")?;
    validate_registry_imports(&entry.imports)?;
    validate_registry_checker_results(&entry.checker_results)?;
    Ok(())
}

fn validate_unique_registry_seed_modules(
    entries: &[PackageRegistryModule],
) -> PackageArtifactResult<()> {
    let mut modules = BTreeSet::<String>::new();
    for (index, entry) in entries.iter().enumerate() {
        let module = entry.module.as_dotted();
        if modules.insert(module.clone()) {
            continue;
        }
        return Err(PackageArtifactError::duplicate(
            format!("module_registry_entries[{index}].module"),
            "module_registry_entries",
            PackageArtifactErrorReason::DuplicateModule,
            module,
        ));
    }
    Ok(())
}

fn ensure_manifest_modules_locked(
    manifest: &PackageManifest,
    lock: &PackageLockManifest,
) -> PackageArtifactResult<()> {
    for module in &manifest.modules {
        if lock.entries.iter().any(|entry| {
            entry.origin == PackageLockEntryOrigin::Local && entry.module == module.module
        }) {
            continue;
        }
        return Err(PackageArtifactError::missing_field(
            "package_lock.entries",
            module.module.as_dotted(),
        ));
    }
    Ok(())
}

fn ensure_lock_matches_manifest(
    manifest: &PackageManifest,
    lock: &PackageLockManifest,
) -> PackageArtifactResult<()> {
    if lock.package != manifest.package {
        return Err(PackageArtifactError::invalid_enum_value(
            "package_lock.package",
            "package",
            manifest.package.as_str(),
            lock.package.as_str(),
        ));
    }
    if lock.version != manifest.version {
        return Err(PackageArtifactError::invalid_enum_value(
            "package_lock.version",
            "version",
            manifest.version.as_str(),
            lock.version.as_str(),
        ));
    }
    Ok(())
}

fn registry_module_from_lock_entry(
    input: &PackageRegistryModuleSeedInput<'_>,
    entry: &PackageLockEntry,
) -> PackageArtifactResult<PackageRegistryModule> {
    ensure_local_entry_declared(input.manifest, entry)?;
    let module_path = format!("module_registry_entries.{}", entry.module.as_dotted());
    Ok(PackageRegistryModule {
        schema: REGISTRY_MODULE_SCHEMA.to_owned(),
        package: input.manifest.package.clone(),
        package_version: input.manifest.version.clone(),
        module: entry.module.clone(),
        core_spec: input.manifest.core_spec.clone(),
        kernel_profile: input.manifest.kernel_profile.clone(),
        certificate_format: input.manifest.certificate_format.clone(),
        export_hash: entry.export_hash,
        certificate_hash: entry.certificate_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate: PackageArtifactFileReference {
            path: entry.certificate.clone(),
            file_hash: entry.certificate_file_hash,
        },
        imports: entry
            .imports
            .iter()
            .enumerate()
            .map(|(index, import)| {
                registry_import_from_lock_import(
                    input.package_lock,
                    import,
                    &format!("{module_path}.imports[{index}]"),
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_results: registry_checker_results_for_entry(
            entry,
            input.checker_summaries,
            &input.manifest.checker_profile,
            &module_path,
        )?,
        artifact_hashes: input.artifact_hashes.clone(),
    })
}

fn ensure_local_entry_declared(
    manifest: &PackageManifest,
    entry: &PackageLockEntry,
) -> PackageArtifactResult<()> {
    let Some(module) = manifest
        .modules
        .iter()
        .find(|module| module.module == entry.module)
    else {
        return Err(PackageArtifactError::missing_field(
            "modules",
            entry.module.as_dotted(),
        ));
    };
    if module.certificate != entry.certificate {
        return Err(PackageArtifactError::invalid_enum_value(
            "modules.certificate",
            "certificate",
            module.certificate.as_str(),
            entry.certificate.as_str(),
        ));
    }
    assert_registry_hash(
        "modules.expected_certificate_file_hash",
        "expected_certificate_file_hash",
        module.expected_certificate_file_hash,
        entry.certificate_file_hash,
    )?;
    assert_registry_hash(
        "modules.expected_export_hash",
        "expected_export_hash",
        module.expected_export_hash,
        entry.export_hash,
    )?;
    assert_registry_hash(
        "modules.expected_certificate_hash",
        "expected_certificate_hash",
        module.expected_certificate_hash,
        entry.certificate_hash,
    )?;
    assert_registry_hash(
        "modules.expected_axiom_report_hash",
        "expected_axiom_report_hash",
        module.expected_axiom_report_hash,
        entry.axiom_report_hash,
    )
}

fn registry_import_from_lock_import(
    lock: &PackageLockManifest,
    import: &PackageLockImport,
    path: &str,
) -> PackageArtifactResult<PackageRegistryImport> {
    let Some(entry) = lock.entries.iter().find(|entry| {
        entry.module == import.module
            && entry.export_hash == import.export_hash
            && entry.certificate_hash == import.certificate_hash
    }) else {
        if let Some(entry) = lock
            .entries
            .iter()
            .find(|entry| entry.module == import.module)
        {
            assert_registry_hash(
                field_path(path, "export_hash"),
                "export_hash",
                entry.export_hash,
                import.export_hash,
            )?;
            assert_registry_hash(
                field_path(path, "certificate_hash"),
                "certificate_hash",
                entry.certificate_hash,
                import.certificate_hash,
            )?;
        }
        return Err(PackageArtifactError::missing_field(
            path,
            format!("{} identity", import.module.as_dotted()),
        ));
    };
    let (origin, package, version) = match entry.origin {
        PackageLockEntryOrigin::Local => (PackageArtifactOrigin::Local, None, None),
        PackageLockEntryOrigin::External => (
            PackageArtifactOrigin::External,
            Some(
                entry
                    .package
                    .clone()
                    .ok_or_else(|| PackageArtifactError::missing_field(path, "package"))?,
            ),
            Some(
                entry
                    .version
                    .clone()
                    .ok_or_else(|| PackageArtifactError::missing_field(path, "version"))?,
            ),
        ),
    };
    Ok(PackageRegistryImport {
        module: import.module.clone(),
        origin,
        package,
        version,
        export_hash: import.export_hash,
        certificate_hash: import.certificate_hash,
    })
}

fn registry_checker_results_for_entry(
    entry: &PackageLockEntry,
    summaries: &[PackageCheckerSummary],
    checker_profile: &str,
    path: &str,
) -> PackageArtifactResult<Vec<PackageRegistryCheckerResult>> {
    let mut found_reference = false;
    let mut results = Vec::new();
    for summary in summaries
        .iter()
        .filter(|summary| summary.module == entry.module)
    {
        let summary_path = format!("{}.checker_results.{}", path, summary.mode.as_str());
        assert_registry_hash(
            field_path(&summary_path, "export_hash"),
            "export_hash",
            entry.export_hash,
            summary.export_hash,
        )?;
        assert_registry_hash(
            field_path(&summary_path, "certificate_hash"),
            "certificate_hash",
            entry.certificate_hash,
            summary.certificate_hash,
        )?;
        assert_registry_hash(
            field_path(&summary_path, "axiom_report_hash"),
            "axiom_report_hash",
            entry.axiom_report_hash,
            summary.axiom_report_hash,
        )?;
        if summary.status != "passed" {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&summary_path, "status"),
                "status",
                "passed",
                &summary.status,
            ));
        }
        if summary.mode == PackageCheckerMode::Reference {
            if summary.checker != "npa-checker-ref" {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&summary_path, "checker"),
                    "checker",
                    "npa-checker-ref",
                    &summary.checker,
                ));
            }
            if summary.profile != checker_profile {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&summary_path, "profile"),
                    "profile",
                    checker_profile,
                    &summary.profile,
                ));
            }
            found_reference = true;
        }
        results.push(PackageRegistryCheckerResult {
            checker: summary.checker.clone(),
            profile: summary.profile.clone(),
            mode: summary.mode.as_str().to_owned(),
            status: PackageRegistryCheckerStatus::Accepted,
            export_hash: summary.export_hash,
            certificate_hash: summary.certificate_hash,
            axiom_report_hash: summary.axiom_report_hash,
        });
    }
    if !found_reference {
        return Err(PackageArtifactError::missing_field(
            format!("{path}.checker_results"),
            "reference",
        ));
    }
    Ok(results)
}

fn assert_registry_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageArtifactResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

pub(crate) fn parse_registry_module_value(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageRegistryModule> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REGISTRY_MODULE_FIELDS)?;
    Ok(PackageRegistryModule {
        schema: required_string(members, path, "schema")?,
        package: PackageId::new(required_string(members, path, "package")?),
        package_version: PackageVersion::new(required_string(members, path, "package_version")?),
        module: required_name(members, path, "module")?,
        core_spec: required_string(members, path, "core_spec")?,
        kernel_profile: required_string(members, path, "kernel_profile")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        certificate: parse_file_reference(
            required_value(members, path, "certificate")?,
            &field_path(path, "certificate"),
        )?,
        imports: required_array(members, path, "imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_registry_import(value, &array_path(path, "imports", index)))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_results: required_array(members, path, "checker_results")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_registry_checker_result(value, &array_path(path, "checker_results", index))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        artifact_hashes: parse_registry_artifact_hashes(
            required_value(members, path, "artifact_hashes")?,
            &field_path(path, "artifact_hashes"),
        )?,
    })
}

pub(crate) fn normalize_registry_module(entry: &mut PackageRegistryModule) {
    entry.imports.sort_by_key(registry_import_sort_key);
    entry
        .checker_results
        .sort_by_key(registry_checker_result_sort_key);
}

pub(crate) fn registry_module_sort_key(entry: &PackageRegistryModule) -> String {
    entry.module.as_dotted()
}

pub(crate) fn registry_module_json_unchecked(entry: &PackageRegistryModule) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&entry.schema)),
        ("package", json_string(entry.package.as_str())),
        (
            "package_version",
            json_string(entry.package_version.as_str()),
        ),
        ("module", json_string(&entry.module.as_dotted())),
        ("core_spec", json_string(&entry.core_spec)),
        ("kernel_profile", json_string(&entry.kernel_profile)),
        ("certificate_format", json_string(&entry.certificate_format)),
        ("export_hash", hash_json(entry.export_hash)),
        ("certificate_hash", hash_json(entry.certificate_hash)),
        ("axiom_report_hash", hash_json(entry.axiom_report_hash)),
        ("certificate", file_reference_json(&entry.certificate)),
        (
            "imports",
            json_array(entry.imports.iter().map(registry_import_json).collect()),
        ),
        (
            "checker_results",
            json_array(
                entry
                    .checker_results
                    .iter()
                    .map(registry_checker_result_json)
                    .collect(),
            ),
        ),
        (
            "artifact_hashes",
            registry_artifact_hashes_json(&entry.artifact_hashes),
        ),
    ])
}

fn validate_registry_imports(imports: &[PackageRegistryImport]) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, import) in imports.iter().enumerate() {
        let path = format!("imports[{index}]");
        validate_module_name(&import.module, field_path(&path, "module"))?;
        match import.origin {
            PackageArtifactOrigin::External => {
                let package = import
                    .package
                    .as_ref()
                    .ok_or_else(|| PackageArtifactError::missing_field(&path, "package"))?;
                let version = import
                    .version
                    .as_ref()
                    .ok_or_else(|| PackageArtifactError::missing_field(&path, "version"))?;
                validate_package_identity(package, version)?;
            }
            PackageArtifactOrigin::Local => {
                if import.package.is_some() {
                    return Err(PackageArtifactError::unknown_field(&path, "package"));
                }
                if import.version.is_some() {
                    return Err(PackageArtifactError::unknown_field(&path, "version"));
                }
            }
        }
        let key = import.module.as_dotted();
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "module"),
                "imports",
                PackageArtifactErrorReason::DuplicateModule,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_registry_checker_results(
    results: &[PackageRegistryCheckerResult],
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, result) in results.iter().enumerate() {
        let path = format!("checker_results[{index}]");
        validate_plain_string(&result.checker, field_path(&path, "checker"))?;
        validate_plain_string(&result.profile, field_path(&path, "profile"))?;
        validate_plain_string(&result.mode, field_path(&path, "mode"))?;
        let key = registry_checker_result_sort_key(result);
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "checker"),
                "checker_results",
                PackageArtifactErrorReason::DuplicateCheckerSummary,
                key,
            ));
        }
    }
    Ok(())
}

fn parse_registry_import(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageRegistryImport> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REGISTRY_IMPORT_FIELDS)?;
    let origin_path = field_path(path, "origin");
    Ok(PackageRegistryImport {
        module: required_name(members, path, "module")?,
        origin: PackageArtifactOrigin::parse(
            &required_string(members, path, "origin")?,
            &origin_path,
        )?,
        package: optional_string(members, path, "package")?.map(PackageId::new),
        version: optional_string(members, path, "version")?.map(PackageVersion::new),
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
    })
}

fn parse_registry_checker_result(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageRegistryCheckerResult> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REGISTRY_CHECKER_RESULT_FIELDS)?;
    let status_path = field_path(path, "status");
    Ok(PackageRegistryCheckerResult {
        checker: required_string(members, path, "checker")?,
        profile: required_string(members, path, "profile")?,
        mode: required_string(members, path, "mode")?,
        status: PackageRegistryCheckerStatus::parse(
            &required_string(members, path, "status")?,
            &status_path,
        )?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
    })
}

fn parse_registry_artifact_hashes(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageRegistryArtifactHashes> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REGISTRY_ARTIFACT_HASHES_FIELDS)?;
    Ok(PackageRegistryArtifactHashes {
        package_lock_file_hash: required_hash(members, path, "package_lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
    })
}

fn optional_string(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<String>> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(|member| {
            member
                .value()
                .string_value()
                .map(ToOwned::to_owned)
                .ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        field_path(path, field),
                        Some(field.to_owned()),
                        "string",
                        member.value().kind().as_str(),
                    )
                })
        })
        .transpose()
}

fn registry_import_json(import: &PackageRegistryImport) -> String {
    let mut fields = vec![
        ("module", json_string(&import.module.as_dotted())),
        ("origin", json_string(import.origin.as_str())),
    ];
    if let Some(package) = &import.package {
        fields.push(("package", json_string(package.as_str())));
    }
    if let Some(version) = &import.version {
        fields.push(("version", json_string(version.as_str())));
    }
    fields.push(("export_hash", hash_json(import.export_hash)));
    fields.push(("certificate_hash", hash_json(import.certificate_hash)));
    json_object_in_order(fields)
}

fn registry_checker_result_json(result: &PackageRegistryCheckerResult) -> String {
    json_object_in_order(vec![
        ("checker", json_string(&result.checker)),
        ("profile", json_string(&result.profile)),
        ("mode", json_string(&result.mode)),
        ("status", json_string(result.status.as_str())),
        ("export_hash", hash_json(result.export_hash)),
        ("certificate_hash", hash_json(result.certificate_hash)),
        ("axiom_report_hash", hash_json(result.axiom_report_hash)),
    ])
}

fn registry_artifact_hashes_json(hashes: &PackageRegistryArtifactHashes) -> String {
    json_object_in_order(vec![
        (
            "package_lock_file_hash",
            hash_json(hashes.package_lock_file_hash),
        ),
        (
            "axiom_report_file_hash",
            hash_json(hashes.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(hashes.theorem_index_file_hash),
        ),
    ])
}

fn registry_import_sort_key(import: &PackageRegistryImport) -> String {
    import.module.as_dotted()
}

fn registry_checker_result_sort_key(result: &PackageRegistryCheckerResult) -> String {
    [
        result.mode.clone(),
        result.checker.clone(),
        result.profile.clone(),
    ]
    .join("\u{001f}")
}

fn required_value<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<&'a JsonValue> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| PackageArtifactError::missing_field(path, field))
}

fn array_path(path: &str, field: &str, index: usize) -> String {
    if path == "$" {
        format!("{field}[{index}]")
    } else {
        format!("{path}.{field}[{index}]")
    }
}

const REGISTRY_MODULE_FIELDS: &[&str] = &[
    "schema",
    "package",
    "package_version",
    "module",
    "core_spec",
    "kernel_profile",
    "certificate_format",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
    "certificate",
    "imports",
    "checker_results",
    "artifact_hashes",
];
const REGISTRY_IMPORT_FIELDS: &[&str] = &[
    "module",
    "origin",
    "package",
    "version",
    "export_hash",
    "certificate_hash",
];
const REGISTRY_CHECKER_RESULT_FIELDS: &[&str] = &[
    "checker",
    "profile",
    "mode",
    "status",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
];
const REGISTRY_ARTIFACT_HASHES_FIELDS: &[&str] = &[
    "package_lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
];

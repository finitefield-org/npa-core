//! Package publish-plan model and canonical JSON.
//!
//! Publish plans are untrusted release metadata. They summarize checked package
//! artifacts and registry seed entries, but they are not checker evidence and
//! never replace local source-free certificate verification.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        checker_summary_json, expect_object, field_path, hash_json, json_array, json_bool,
        json_object_in_order, json_string, json_u64, normalize_checker_summaries,
        parse_artifact_json, parse_checker_summary, parse_checker_summary_at_path,
        reject_unknown_fields, required_array, required_bool, required_hash, required_name,
        required_path, required_string, required_u64, validate_artifact_path,
        validate_checker_summaries, validate_declaration_name, validate_module_name,
        validate_package_identity, validate_plain_string, PackageArtifactFileReference,
        PackageArtifactOrigin, PackageCheckerMode, PackageCheckerSummary,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    incremental_projection::{
        add_changed_reason, checker_summaries_match, package_incremental_full_projection_plan,
        package_incremental_projection_plan_from_changed_modules, push_reason,
        PackageIncrementalProjectionPlan,
    },
    json::{JsonMember, JsonValue},
    lock::{PackageLockEntry, PackageLockEntryOrigin, PackageLockManifest},
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
    registry::{
        normalize_registry_module, parse_registry_module_value, registry_module_json_unchecked,
        registry_module_sort_key, validate_registry_module, PackageRegistryImport,
        PackageRegistryModule,
    },
    schema::{
        PACKAGE_AXIOM_REPORT_SCHEMA, PACKAGE_LOCK_SCHEMA, PACKAGE_MANIFEST_SCHEMA,
        PACKAGE_PUBLISH_PLAN_SCHEMA, PACKAGE_THEOREM_INDEX_SCHEMA,
    },
    theorem_index::PackageTheoremIndex,
};

/// Package-relative path owned by CLR-06 publish-plan write mode.
pub const PACKAGE_PUBLISH_PLAN_PATH: &str = "generated/publish-plan.json";

/// Generated `npa.package.publish_plan.v0.1` publish-plan artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePublishPlan {
    /// Publish-plan schema string; must equal [`PACKAGE_PUBLISH_PLAN_SCHEMA`].
    pub schema: String,
    /// Package identity.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Release metadata references.
    pub release: PackagePublishRelease,
    /// Release artifact list sorted canonically.
    pub artifacts: Vec<PackagePublishArtifact>,
    /// Registry seed entries for local modules, sorted by module.
    pub module_registry_entries: Vec<PackageRegistryModule>,
    /// Embedded downstream import bundle.
    pub downstream_import_bundle: PackageDownstreamImportBundle,
    /// Source-free checker summaries used to validate release metadata.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// MVP checksum-only signature policy.
    pub signature_policy: PackageSignaturePolicy,
    /// Deterministic publish-plan summary counts.
    pub summary: PackagePublishSummary,
    /// Self hash of canonical publish-plan bytes excluding this field.
    pub publish_plan_hash: PackageHash,
}

impl PackagePublishPlan {
    /// Return this publish plan with schema-defined ordering and computed self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_publish_plan(&mut self);
        self.publish_plan_hash = compute_package_publish_plan_hash(&self)?;
        Ok(self)
    }

    /// Serialize this publish plan as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_package_publish_plan(self)?;
        let mut normalized = self.clone();
        normalize_publish_plan(&mut normalized);
        Ok(publish_plan_json_unchecked(&normalized, true))
    }
}

/// Release metadata references recorded in a publish plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePublishRelease {
    /// Core spec profile.
    pub core_spec: String,
    /// Kernel profile.
    pub kernel_profile: String,
    /// Certificate format profile.
    pub certificate_format: String,
    /// Checker profile.
    pub checker_profile: String,
    /// Package manifest identity.
    pub manifest: PackagePublishReleaseReference,
    /// Package lock identity.
    pub package_lock: PackagePublishReleaseReference,
    /// Package axiom report identity.
    pub axiom_report: PackagePublishReleaseReference,
    /// Package theorem index identity.
    pub theorem_index: PackagePublishReleaseReference,
}

/// File reference used by release metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePublishReleaseReference {
    /// Package-relative path.
    pub path: PackagePath,
    /// Exact SHA-256 hash of referenced file bytes.
    pub file_hash: PackageHash,
    /// Content self hash when the referenced artifact has one.
    pub content_hash: Option<PackageHash>,
    /// Schema string when applicable.
    pub schema: Option<String>,
}

/// Publish-plan release artifact role.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackagePublishArtifactRole {
    /// `npa-package.toml`.
    PackageManifest,
    /// `generated/package-lock.json`.
    PackageLock,
    /// `generated/axiom-report.json`.
    AxiomReport,
    /// `generated/theorem-index.json`.
    TheoremIndex,
    /// Local module certificate.
    LocalCertificate,
    /// External import certificate.
    ExternalImportCertificate,
}

impl PackagePublishArtifactRole {
    /// Return the publish artifact role string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PackageManifest => "package_manifest",
            Self::PackageLock => "package_lock",
            Self::AxiomReport => "axiom_report",
            Self::TheoremIndex => "theorem_index",
            Self::LocalCertificate => "local_certificate",
            Self::ExternalImportCertificate => "external_import_certificate",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "package_manifest" => Ok(Self::PackageManifest),
            "package_lock" => Ok(Self::PackageLock),
            "axiom_report" => Ok(Self::AxiomReport),
            "theorem_index" => Ok(Self::TheoremIndex),
            "local_certificate" => Ok(Self::LocalCertificate),
            "external_import_certificate" => Ok(Self::ExternalImportCertificate),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "role",
                "publish artifact role",
                value,
            )),
        }
    }
}

/// One artifact listed by a publish plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePublishArtifact {
    /// Artifact role.
    pub role: PackagePublishArtifactRole,
    /// Package-relative path.
    pub path: PackagePath,
    /// Exact SHA-256 file hash.
    pub file_hash: PackageHash,
    /// Module name when applicable.
    pub module: Option<Name>,
    /// Local or external origin when applicable.
    pub origin: Option<PackageArtifactOrigin>,
    /// Schema string when applicable.
    pub schema: Option<String>,
}

/// Downstream import bundle embedded in a publish plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageDownstreamImportBundle {
    /// Package identity.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Released modules sorted by module in canonical JSON.
    pub modules: Vec<PackageDownstreamImportModule>,
}

/// One module entry in a downstream import bundle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageDownstreamImportModule {
    /// Module name.
    pub module: Name,
    /// Package identity to pin in downstream `[[imports]]`.
    pub package: PackageId,
    /// Package version to pin in downstream `[[imports]]`.
    pub version: PackageVersion,
    /// Exported declaration identifiers from the checked theorem index.
    pub exported_declarations: Vec<Name>,
    /// Module export hash.
    pub export_hash: PackageHash,
    /// Module certificate hash.
    pub certificate_hash: PackageHash,
    /// Module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Certificate path to fetch from release artifacts.
    pub certificate: PackagePath,
    /// Exact SHA-256 hash of certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Source-free checker summaries for this released module.
    pub checker_summaries: Vec<PackageCheckerSummary>,
}

/// Checksum-only signature policy for CLR-06 MVP publish plans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageSignaturePolicy {
    /// Signature policy mode. CLR-06 supports only `checksum-only`.
    pub mode: String,
    /// Hash algorithm. CLR-06 supports only `sha256`.
    pub hash_algorithm: String,
    /// Whether cryptographic signatures are required.
    pub signature_required: bool,
    /// Signature payloads. CLR-06 requires this to be empty.
    pub signatures: Vec<String>,
}

/// Input references used to build a deterministic publish-plan artifact list.
pub struct PackagePublishArtifactListInput<'a> {
    /// Exact package manifest file identity.
    pub manifest: PackageArtifactFileReference,
    /// Exact package-lock file identity.
    pub package_lock: PackageArtifactFileReference,
    /// Exact package axiom-report file identity.
    pub axiom_report: PackageArtifactFileReference,
    /// Exact package theorem-index file identity.
    pub theorem_index: PackageArtifactFileReference,
    /// Parsed package lock whose entries provide certificate artifact identities.
    pub package_lock_manifest: &'a PackageLockManifest,
}

/// Inputs used to build an embedded downstream import bundle from registry seeds.
pub struct PackageDownstreamImportBundleInput<'a> {
    /// Package identity from the validated manifest.
    pub package: &'a PackageId,
    /// Package version from the validated manifest.
    pub version: &'a PackageVersion,
    /// Local module registry seed entries generated for this package.
    pub module_registry_entries: &'a [PackageRegistryModule],
    /// Checked theorem index used to list exported declarations.
    pub theorem_index: &'a PackageTheoremIndex,
    /// Source-free checker summaries copied into downstream module entries.
    pub checker_summaries: &'a [PackageCheckerSummary],
}

/// Deterministic publish-plan summary counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePublishSummary {
    /// Number of local modules.
    pub local_module_count: u64,
    /// Number of external import certificate artifacts.
    pub external_import_count: u64,
    /// Number of release artifacts.
    pub artifact_count: u64,
    /// Number of registry seed entries.
    pub registry_entry_count: u64,
    /// Number of checker summaries.
    pub checker_summary_count: u64,
}

/// Return the explicit CLR-06 checksum-only MVP signature policy.
pub fn package_checksum_only_signature_policy() -> PackageSignaturePolicy {
    PackageSignaturePolicy {
        mode: "checksum-only".to_owned(),
        hash_algorithm: "sha256".to_owned(),
        signature_required: false,
        signatures: Vec::new(),
    }
}

/// Build the deterministic release artifact list for a publish plan.
///
/// The function is pure: callers provide exact file identities and the parsed
/// package lock. It does not read files, walk the filesystem, contact a
/// registry, or inspect source/replay/metadata sidecars.
pub fn build_package_publish_artifacts(
    input: PackagePublishArtifactListInput<'_>,
) -> PackageArtifactResult<Vec<PackagePublishArtifact>> {
    let mut artifacts = vec![
        schema_artifact(
            PackagePublishArtifactRole::PackageManifest,
            input.manifest,
            PACKAGE_MANIFEST_SCHEMA,
        ),
        schema_artifact(
            PackagePublishArtifactRole::PackageLock,
            input.package_lock,
            PACKAGE_LOCK_SCHEMA,
        ),
        schema_artifact(
            PackagePublishArtifactRole::AxiomReport,
            input.axiom_report,
            PACKAGE_AXIOM_REPORT_SCHEMA,
        ),
        schema_artifact(
            PackagePublishArtifactRole::TheoremIndex,
            input.theorem_index,
            PACKAGE_THEOREM_INDEX_SCHEMA,
        ),
    ];

    artifacts.extend(input.package_lock_manifest.entries.iter().map(|entry| {
        let (role, origin) = match entry.origin {
            PackageLockEntryOrigin::Local => (
                PackagePublishArtifactRole::LocalCertificate,
                PackageArtifactOrigin::Local,
            ),
            PackageLockEntryOrigin::External => (
                PackagePublishArtifactRole::ExternalImportCertificate,
                PackageArtifactOrigin::External,
            ),
        };
        PackagePublishArtifact {
            role,
            path: entry.certificate.clone(),
            file_hash: entry.certificate_file_hash,
            module: Some(entry.module.clone()),
            origin: Some(origin),
            schema: None,
        }
    }));

    artifacts.sort_by_key(publish_artifact_sort_key);
    validate_publish_artifacts(&artifacts, None)?;
    Ok(artifacts)
}

/// Build the deterministic downstream import bundle embedded in a publish plan.
///
/// The function projects only local module registry seed entries for the current
/// package. It does not add registry URLs, latest-version markers, fetch hints,
/// or any other network-resolution metadata.
pub fn build_package_downstream_import_bundle(
    input: PackageDownstreamImportBundleInput<'_>,
) -> PackageArtifactResult<PackageDownstreamImportBundle> {
    validate_registry_entries(input.module_registry_entries, input.package, input.version)?;
    validate_downstream_theorem_index_identity(input.theorem_index, input.package, input.version)?;
    let mut bundle = PackageDownstreamImportBundle {
        package: input.package.clone(),
        version: input.version.clone(),
        modules: input
            .module_registry_entries
            .iter()
            .map(|entry| {
                downstream_import_module_from_registry_entry(
                    entry,
                    input.theorem_index,
                    input.checker_summaries,
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    };
    for module in &mut bundle.modules {
        module.exported_declarations.sort();
        normalize_checker_summaries(&mut module.checker_summaries);
    }
    bundle
        .modules
        .sort_by_key(downstream_import_module_sort_key);
    validate_downstream_import_bundle(&bundle, input.package, input.version)?;
    validate_downstream_import_bundle_matches_registry(&bundle, input.module_registry_entries)?;
    Ok(bundle)
}

fn validate_downstream_theorem_index_identity(
    theorem_index: &PackageTheoremIndex,
    package: &PackageId,
    version: &PackageVersion,
) -> PackageArtifactResult<()> {
    validate_package_identity(&theorem_index.package, &theorem_index.version)?;
    if &theorem_index.package == package && &theorem_index.version == version {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            "theorem_index.package",
            "package",
            format!("{} {}", package.as_str(), version.as_str()),
            format!(
                "{} {}",
                theorem_index.package.as_str(),
                theorem_index.version.as_str()
            ),
        ))
    }
}

fn schema_artifact(
    role: PackagePublishArtifactRole,
    reference: PackageArtifactFileReference,
    schema: &'static str,
) -> PackagePublishArtifact {
    PackagePublishArtifact {
        role,
        path: reference.path,
        file_hash: reference.file_hash,
        module: None,
        origin: None,
        schema: Some(schema.to_owned()),
    }
}

/// Parse and validate a checked-in package publish-plan JSON artifact.
pub fn parse_package_publish_plan_json(source: &str) -> PackageArtifactResult<PackagePublishPlan> {
    let root = parse_artifact_json(source)?;
    let plan = parse_publish_plan_value(&root)?;
    validate_package_publish_plan(&plan)?;
    let canonical = plan.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package publish-plan JSON bytes",
        ));
    }
    Ok(plan)
}

/// Validate a package publish plan model without reading files or contacting a registry.
pub fn validate_package_publish_plan(plan: &PackagePublishPlan) -> PackageArtifactResult<()> {
    if plan.schema != PACKAGE_PUBLISH_PLAN_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_PUBLISH_PLAN_SCHEMA,
            plan.schema.clone(),
        ));
    }
    validate_publish_plan_shape_without_self_hash(plan)?;
    let expected_hash = compute_package_publish_plan_hash(plan)?;
    if expected_hash != plan.publish_plan_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "publish_plan_hash",
            "publish_plan_hash",
            format_package_hash(&expected_hash),
            format_package_hash(&plan.publish_plan_hash),
        ));
    }
    Ok(())
}

/// Compute the publish-plan self hash over canonical bytes excluding the self-hash field.
pub fn compute_package_publish_plan_hash(
    plan: &PackagePublishPlan,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = plan.clone();
    normalize_publish_plan(&mut normalized);
    validate_publish_plan_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        publish_plan_json_unchecked(&normalized, false).as_bytes(),
    ))
}

/// Plan an incremental publish-plan check against current package metadata.
///
/// The plan is optimization metadata only. It is not proof evidence and uses
/// package-lock identity plus per-local-module registry identities as the
/// invalidation boundary.
pub fn package_publish_plan_incremental_projection_plan(
    plan: &PackagePublishPlan,
    package: &PackageId,
    version: &PackageVersion,
    expected_release: &PackagePublishRelease,
    current_lock: &PackageLockManifest,
    checker_summaries: &[PackageCheckerSummary],
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let mut full_reasons = Vec::new();
    push_reason(
        &mut full_reasons,
        plan.schema != PACKAGE_PUBLISH_PLAN_SCHEMA,
        "projection_schema_changed",
    );
    push_reason(
        &mut full_reasons,
        &plan.package != package || &plan.version != version,
        "package_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        !release_profiles_match(&plan.release, expected_release),
        "release_profile_changed",
    );
    push_reason(
        &mut full_reasons,
        !release_reference_static_identity_matches(
            &plan.release.manifest,
            &expected_release.manifest,
        ) || plan.release.manifest.file_hash != expected_release.manifest.file_hash,
        "manifest_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        !release_reference_static_identity_matches(
            &plan.release.package_lock,
            &expected_release.package_lock,
        ),
        "package_lock_release_reference_changed",
    );
    push_reason(
        &mut full_reasons,
        !release_reference_static_identity_matches(
            &plan.release.axiom_report,
            &expected_release.axiom_report,
        ),
        "axiom_report_release_reference_changed",
    );
    push_reason(
        &mut full_reasons,
        !release_reference_static_identity_matches(
            &plan.release.theorem_index,
            &expected_release.theorem_index,
        ),
        "theorem_index_release_reference_changed",
    );
    push_reason(
        &mut full_reasons,
        plan.signature_policy != package_checksum_only_signature_policy(),
        "signature_policy_changed",
    );
    push_reason(
        &mut full_reasons,
        !checker_summaries_match(&plan.checker_summaries, checker_summaries),
        "checker_profile_or_summary_changed",
    );
    push_reason(
        &mut full_reasons,
        current_lock.schema != PACKAGE_LOCK_SCHEMA,
        "package_lock_schema_changed",
    );

    let changed_modules = publish_plan_changed_modules(plan, current_lock, &mut full_reasons);
    if publish_release_hashes_changed(&plan.release, expected_release)
        && changed_modules.is_empty()
        && full_reasons.is_empty()
    {
        return package_incremental_full_projection_plan(
            "publish-plan",
            current_lock,
            ["generated_artifact_unattributed_change"],
        );
    }

    package_incremental_projection_plan_from_changed_modules(
        "publish-plan",
        current_lock,
        full_reasons,
        changed_modules,
    )
}

fn release_profiles_match(
    checked: &PackagePublishRelease,
    expected: &PackagePublishRelease,
) -> bool {
    checked.core_spec == expected.core_spec
        && checked.kernel_profile == expected.kernel_profile
        && checked.certificate_format == expected.certificate_format
        && checked.checker_profile == expected.checker_profile
}

fn release_reference_static_identity_matches(
    checked: &PackagePublishReleaseReference,
    expected: &PackagePublishReleaseReference,
) -> bool {
    checked.path == expected.path && checked.schema == expected.schema
}

fn publish_release_hashes_changed(
    checked: &PackagePublishRelease,
    expected: &PackagePublishRelease,
) -> bool {
    checked.package_lock.file_hash != expected.package_lock.file_hash
        || checked.axiom_report.file_hash != expected.axiom_report.file_hash
        || checked.axiom_report.content_hash != expected.axiom_report.content_hash
        || checked.theorem_index.file_hash != expected.theorem_index.file_hash
        || checked.theorem_index.content_hash != expected.theorem_index.content_hash
}

fn publish_plan_changed_modules(
    plan: &PackagePublishPlan,
    current_lock: &PackageLockManifest,
    full_reasons: &mut Vec<String>,
) -> BTreeMap<Name, BTreeSet<String>> {
    let previous = plan
        .module_registry_entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect::<BTreeMap<_, _>>();
    let current = current_lock
        .entries
        .iter()
        .filter(|entry| entry.origin == PackageLockEntryOrigin::Local)
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
            entry.certificate != previous.certificate.path,
            "certificate_path_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            entry.certificate_file_hash != previous.certificate.file_hash,
            "certificate_file_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            registry_imports_for_lock_entry(entry, current_lock) != previous.imports,
            "direct_import_identity_changed",
        );
    }

    changed
}

fn registry_imports_for_lock_entry(
    entry: &PackageLockEntry,
    lock: &PackageLockManifest,
) -> Vec<PackageRegistryImport> {
    let mut imports = entry
        .imports
        .iter()
        .filter_map(|import| {
            let provider = lock.entries.iter().find(|candidate| {
                candidate.module == import.module
                    && candidate.export_hash == import.export_hash
                    && candidate.certificate_hash == import.certificate_hash
            })?;
            Some(PackageRegistryImport {
                module: import.module.clone(),
                origin: lock_origin_to_artifact_origin(provider.origin),
                package: provider.package.clone(),
                version: provider.version.clone(),
                export_hash: import.export_hash,
                certificate_hash: import.certificate_hash,
            })
        })
        .collect::<Vec<_>>();
    imports.sort_by_key(registry_import_key);
    imports
}

fn lock_origin_to_artifact_origin(origin: PackageLockEntryOrigin) -> PackageArtifactOrigin {
    match origin {
        PackageLockEntryOrigin::Local => PackageArtifactOrigin::Local,
        PackageLockEntryOrigin::External => PackageArtifactOrigin::External,
    }
}

fn registry_import_key(import: &PackageRegistryImport) -> String {
    format!(
        "{}\u{001f}{}\u{001f}{}\u{001f}{}",
        import.module.as_dotted(),
        import.origin.as_str(),
        format_package_hash(&import.export_hash),
        format_package_hash(&import.certificate_hash)
    )
}

fn validate_publish_plan_shape_without_self_hash(
    plan: &PackagePublishPlan,
) -> PackageArtifactResult<()> {
    if plan.schema != PACKAGE_PUBLISH_PLAN_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_PUBLISH_PLAN_SCHEMA,
            plan.schema.clone(),
        ));
    }
    validate_package_identity(&plan.package, &plan.version)?;
    validate_release(&plan.release)?;
    validate_publish_artifacts(&plan.artifacts, Some(&plan.release))?;
    validate_registry_entries(&plan.module_registry_entries, &plan.package, &plan.version)?;
    validate_downstream_import_bundle(
        &plan.downstream_import_bundle,
        &plan.package,
        &plan.version,
    )?;
    validate_downstream_import_bundle_matches_registry(
        &plan.downstream_import_bundle,
        &plan.module_registry_entries,
    )?;
    validate_downstream_certificate_artifacts(&plan.artifacts, &plan.downstream_import_bundle)?;
    validate_checker_summaries(&plan.checker_summaries)?;
    validate_downstream_checker_summaries_match_top_level(
        &plan.downstream_import_bundle,
        &plan.checker_summaries,
    )?;
    validate_signature_policy(&plan.signature_policy)?;
    validate_publish_summary(plan)?;
    Ok(())
}

fn parse_publish_plan_value(value: &JsonValue) -> PackageArtifactResult<PackagePublishPlan> {
    let path = "$";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, PUBLISH_PLAN_FIELDS)?;
    Ok(PackagePublishPlan {
        schema: required_string(members, path, "schema")?,
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        release: parse_release(required_value(members, path, "release")?)?,
        artifacts: required_array(members, path, "artifacts")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_publish_artifact(value, &format!("artifacts[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        module_registry_entries: required_array(members, path, "module_registry_entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_registry_module_value(value, &format!("module_registry_entries[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        downstream_import_bundle: parse_downstream_import_bundle(required_value(
            members,
            path,
            "downstream_import_bundle",
        )?)?,
        checker_summaries: required_array(members, path, "checker_summaries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_checker_summary(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        signature_policy: parse_signature_policy(required_value(
            members,
            path,
            "signature_policy",
        )?)?,
        summary: parse_publish_summary(required_value(members, path, "summary")?)?,
        publish_plan_hash: required_hash(members, path, "publish_plan_hash")?,
    })
}

fn normalize_publish_plan(plan: &mut PackagePublishPlan) {
    plan.artifacts.sort_by_key(publish_artifact_sort_key);
    for entry in &mut plan.module_registry_entries {
        normalize_registry_module(entry);
    }
    plan.module_registry_entries
        .sort_by_key(registry_module_sort_key);
    plan.downstream_import_bundle
        .modules
        .sort_by_key(downstream_import_module_sort_key);
    for module in &mut plan.downstream_import_bundle.modules {
        module.exported_declarations.sort();
        normalize_checker_summaries(&mut module.checker_summaries);
    }
    normalize_checker_summaries(&mut plan.checker_summaries);
}

fn publish_plan_json_unchecked(plan: &PackagePublishPlan, include_hash: bool) -> String {
    let mut fields = vec![
        ("schema", json_string(&plan.schema)),
        ("package", json_string(plan.package.as_str())),
        ("version", json_string(plan.version.as_str())),
        ("release", release_json(&plan.release)),
        (
            "artifacts",
            json_array(plan.artifacts.iter().map(publish_artifact_json).collect()),
        ),
        (
            "module_registry_entries",
            json_array(
                plan.module_registry_entries
                    .iter()
                    .map(registry_module_json_unchecked)
                    .collect(),
            ),
        ),
        (
            "downstream_import_bundle",
            downstream_import_bundle_json(&plan.downstream_import_bundle),
        ),
        (
            "checker_summaries",
            json_array(
                plan.checker_summaries
                    .iter()
                    .map(checker_summary_json)
                    .collect(),
            ),
        ),
        (
            "signature_policy",
            signature_policy_json(&plan.signature_policy),
        ),
        ("summary", publish_summary_json(&plan.summary)),
    ];
    if include_hash {
        fields.push(("publish_plan_hash", hash_json(plan.publish_plan_hash)));
    }
    json_object_in_order(fields)
}

fn validate_release(release: &PackagePublishRelease) -> PackageArtifactResult<()> {
    validate_plain_string(&release.core_spec, "release.core_spec")?;
    validate_plain_string(&release.kernel_profile, "release.kernel_profile")?;
    validate_plain_string(&release.certificate_format, "release.certificate_format")?;
    validate_plain_string(&release.checker_profile, "release.checker_profile")?;
    validate_release_reference(
        &release.manifest,
        "release.manifest",
        Some(PACKAGE_MANIFEST_SCHEMA),
        false,
    )?;
    validate_release_reference(
        &release.package_lock,
        "release.package_lock",
        Some(PACKAGE_LOCK_SCHEMA),
        false,
    )?;
    validate_release_reference(
        &release.axiom_report,
        "release.axiom_report",
        Some(PACKAGE_AXIOM_REPORT_SCHEMA),
        true,
    )?;
    validate_release_reference(
        &release.theorem_index,
        "release.theorem_index",
        Some(PACKAGE_THEOREM_INDEX_SCHEMA),
        true,
    )
}

fn validate_release_reference(
    reference: &PackagePublishReleaseReference,
    path: &str,
    expected_schema: Option<&str>,
    content_hash_required: bool,
) -> PackageArtifactResult<()> {
    validate_artifact_path(&reference.path, field_path(path, "path"))?;
    if content_hash_required && reference.content_hash.is_none() {
        return Err(PackageArtifactError::missing_field(path, "content_hash"));
    }
    if let Some(expected_schema) = expected_schema {
        match &reference.schema {
            Some(actual) if actual == expected_schema => {}
            Some(actual) => {
                return Err(PackageArtifactError::unsupported_schema(
                    field_path(path, "schema"),
                    "schema",
                    expected_schema,
                    actual,
                ));
            }
            None => return Err(PackageArtifactError::missing_field(path, "schema")),
        }
    }
    if let Some(schema) = &reference.schema {
        validate_plain_string(schema, field_path(path, "schema"))?;
    }
    Ok(())
}

fn validate_publish_artifacts(
    artifacts: &[PackagePublishArtifact],
    release: Option<&PackagePublishRelease>,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    let mut singleton_roles = BTreeSet::<&'static str>::new();
    for (index, artifact) in artifacts.iter().enumerate() {
        let path = format!("artifacts[{index}]");
        validate_artifact_path(&artifact.path, field_path(&path, "path"))?;
        if artifact.path.as_str() == PACKAGE_PUBLISH_PLAN_PATH {
            return Err(PackageArtifactError::release_artifact_self_reference(
                field_path(&path, "path"),
                artifact.path.as_str(),
            ));
        }
        if let Some(module) = &artifact.module {
            validate_module_name(module, field_path(&path, "module"))?;
        }
        if let Some(schema) = &artifact.schema {
            validate_plain_string(schema, field_path(&path, "schema"))?;
        }
        validate_publish_artifact_role_fields(artifact, &path)?;
        if is_singleton_artifact_role(artifact.role) {
            let role = artifact.role.as_str();
            if !singleton_roles.insert(role) {
                return Err(PackageArtifactError::duplicate(
                    field_path(&path, "role"),
                    "artifacts",
                    PackageArtifactErrorReason::DuplicateArtifact,
                    role,
                ));
            }
        }
        let key = artifact.path.as_str().to_owned();
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "path"),
                "artifacts",
                PackageArtifactErrorReason::DuplicateArtifact,
                key,
            ));
        }
    }
    if let Some(release) = release {
        validate_required_release_artifact(
            artifacts,
            PackagePublishArtifactRole::PackageManifest,
            &release.manifest,
        )?;
        validate_required_release_artifact(
            artifacts,
            PackagePublishArtifactRole::PackageLock,
            &release.package_lock,
        )?;
        validate_required_release_artifact(
            artifacts,
            PackagePublishArtifactRole::AxiomReport,
            &release.axiom_report,
        )?;
        validate_required_release_artifact(
            artifacts,
            PackagePublishArtifactRole::TheoremIndex,
            &release.theorem_index,
        )?;
    }
    Ok(())
}

fn validate_publish_artifact_role_fields(
    artifact: &PackagePublishArtifact,
    path: &str,
) -> PackageArtifactResult<()> {
    match artifact.role {
        PackagePublishArtifactRole::PackageManifest => {
            validate_schema_artifact_fields(artifact, path, PACKAGE_MANIFEST_SCHEMA)
        }
        PackagePublishArtifactRole::PackageLock => {
            validate_schema_artifact_fields(artifact, path, PACKAGE_LOCK_SCHEMA)
        }
        PackagePublishArtifactRole::AxiomReport => {
            validate_schema_artifact_fields(artifact, path, PACKAGE_AXIOM_REPORT_SCHEMA)
        }
        PackagePublishArtifactRole::TheoremIndex => {
            validate_schema_artifact_fields(artifact, path, PACKAGE_THEOREM_INDEX_SCHEMA)
        }
        PackagePublishArtifactRole::LocalCertificate => {
            validate_certificate_artifact_fields(artifact, path, PackageArtifactOrigin::Local)
        }
        PackagePublishArtifactRole::ExternalImportCertificate => {
            validate_certificate_artifact_fields(artifact, path, PackageArtifactOrigin::External)
        }
    }
}

fn validate_schema_artifact_fields(
    artifact: &PackagePublishArtifact,
    path: &str,
    expected_schema: &'static str,
) -> PackageArtifactResult<()> {
    if artifact.module.is_some() {
        return Err(unexpected_publish_artifact_field(path, "module", "absent"));
    }
    if artifact.origin.is_some() {
        return Err(unexpected_publish_artifact_field(path, "origin", "absent"));
    }
    match &artifact.schema {
        Some(schema) if schema == expected_schema => Ok(()),
        Some(schema) => Err(PackageArtifactError::unsupported_schema(
            field_path(path, "schema"),
            "schema",
            expected_schema,
            schema,
        )),
        None => Err(PackageArtifactError::missing_field(path, "schema")),
    }
}

fn validate_certificate_artifact_fields(
    artifact: &PackagePublishArtifact,
    path: &str,
    expected_origin: PackageArtifactOrigin,
) -> PackageArtifactResult<()> {
    if artifact.module.is_none() {
        return Err(PackageArtifactError::missing_field(path, "module"));
    }
    match artifact.origin {
        Some(origin) if origin == expected_origin => {}
        Some(origin) => {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(path, "origin"),
                "origin",
                expected_origin.as_str(),
                origin.as_str(),
            ));
        }
        None => return Err(PackageArtifactError::missing_field(path, "origin")),
    }
    if artifact.schema.is_some() {
        return Err(unexpected_publish_artifact_field(path, "schema", "absent"));
    }
    Ok(())
}

fn unexpected_publish_artifact_field(
    path: &str,
    field: &'static str,
    expected: &'static str,
) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(field_path(path, field), field, expected, "present")
}

fn is_singleton_artifact_role(role: PackagePublishArtifactRole) -> bool {
    matches!(
        role,
        PackagePublishArtifactRole::PackageManifest
            | PackagePublishArtifactRole::PackageLock
            | PackagePublishArtifactRole::AxiomReport
            | PackagePublishArtifactRole::TheoremIndex
    )
}

fn validate_required_release_artifact(
    artifacts: &[PackagePublishArtifact],
    role: PackagePublishArtifactRole,
    reference: &PackagePublishReleaseReference,
) -> PackageArtifactResult<()> {
    let path = format!("artifacts.{}", role.as_str());
    let Some(artifact) = artifacts.iter().find(|artifact| artifact.role == role) else {
        return Err(PackageArtifactError::missing_field(
            "artifacts",
            role.as_str(),
        ));
    };
    assert_release_artifact_field(
        &path,
        "path",
        reference.path.as_str(),
        artifact.path.as_str(),
    )?;
    assert_release_artifact_field(
        &path,
        "file_hash",
        format_package_hash(&reference.file_hash),
        format_package_hash(&artifact.file_hash),
    )?;
    assert_release_artifact_field(
        &path,
        "schema",
        reference.schema.as_deref().unwrap_or("absent"),
        artifact.schema.as_deref().unwrap_or("absent"),
    )
}

fn assert_release_artifact_field(
    path: &str,
    field: &'static str,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactResult<()> {
    let expected = expected.into();
    let actual = actual.into();
    if expected == actual {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            field_path(path, field),
            field,
            expected,
            actual,
        ))
    }
}

fn validate_registry_entries(
    entries: &[PackageRegistryModule],
    package: &PackageId,
    version: &PackageVersion,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, entry) in entries.iter().enumerate() {
        validate_registry_module(entry)?;
        if &entry.package != package || &entry.package_version != version {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("module_registry_entries[{index}].package"),
                "package",
                format!("{} {}", package.as_str(), version.as_str()),
                format!(
                    "{} {}",
                    entry.package.as_str(),
                    entry.package_version.as_str()
                ),
            ));
        }
        let key = entry.module.as_dotted();
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                format!("module_registry_entries[{index}].module"),
                "module_registry_entries",
                PackageArtifactErrorReason::DuplicateModule,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_downstream_import_bundle(
    bundle: &PackageDownstreamImportBundle,
    package: &PackageId,
    version: &PackageVersion,
) -> PackageArtifactResult<()> {
    validate_package_identity(&bundle.package, &bundle.version)?;
    if &bundle.package != package || &bundle.version != version {
        return Err(PackageArtifactError::invalid_enum_value(
            "downstream_import_bundle.package",
            "package",
            format!("{} {}", package.as_str(), version.as_str()),
            format!("{} {}", bundle.package.as_str(), bundle.version.as_str()),
        ));
    }
    let mut keys = BTreeSet::<String>::new();
    for (index, module) in bundle.modules.iter().enumerate() {
        let path = format!("downstream_import_bundle.modules[{index}]");
        validate_module_name(&module.module, field_path(&path, "module"))?;
        validate_package_identity(&module.package, &module.version)?;
        validate_exported_declarations(
            &module.exported_declarations,
            &field_path(&path, "exported_declarations"),
        )?;
        validate_artifact_path(&module.certificate, field_path(&path, "certificate"))?;
        validate_downstream_checker_summaries(module, &path)?;
        let key = module.module.as_dotted();
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "module"),
                "modules",
                PackageArtifactErrorReason::DuplicateModule,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_downstream_import_bundle_matches_registry(
    bundle: &PackageDownstreamImportBundle,
    entries: &[PackageRegistryModule],
) -> PackageArtifactResult<()> {
    for (index, module) in bundle.modules.iter().enumerate() {
        let path = format!("downstream_import_bundle.modules[{index}]");
        let Some(entry) = entries.iter().find(|entry| entry.module == module.module) else {
            return Err(PackageArtifactError::missing_field(
                "module_registry_entries",
                module.module.as_dotted(),
            ));
        };
        assert_downstream_import_field(
            &path,
            "package",
            entry.package.as_str(),
            module.package.as_str(),
        )?;
        assert_downstream_import_field(
            &path,
            "version",
            entry.package_version.as_str(),
            module.version.as_str(),
        )?;
        assert_downstream_import_field(
            &path,
            "export_hash",
            format_package_hash(&entry.export_hash),
            format_package_hash(&module.export_hash),
        )?;
        assert_downstream_import_field(
            &path,
            "certificate_hash",
            format_package_hash(&entry.certificate_hash),
            format_package_hash(&module.certificate_hash),
        )?;
        assert_downstream_import_field(
            &path,
            "axiom_report_hash",
            format_package_hash(&entry.axiom_report_hash),
            format_package_hash(&module.axiom_report_hash),
        )?;
        assert_downstream_import_field(
            &path,
            "certificate",
            entry.certificate.path.as_str(),
            module.certificate.as_str(),
        )?;
        assert_downstream_import_field(
            &path,
            "certificate_file_hash",
            format_package_hash(&entry.certificate.file_hash),
            format_package_hash(&module.certificate_file_hash),
        )?;
        validate_downstream_checker_summaries_match_registry(&path, module, entry)?;
    }

    for entry in entries {
        if bundle
            .modules
            .iter()
            .any(|module| module.module == entry.module)
        {
            continue;
        }
        return Err(PackageArtifactError::missing_field(
            "downstream_import_bundle.modules",
            entry.module.as_dotted(),
        ));
    }
    Ok(())
}

fn validate_exported_declarations(declarations: &[Name], path: &str) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, declaration) in declarations.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        validate_declaration_name(declaration, &item_path)?;
        let key = declaration.as_dotted();
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                item_path,
                "exported_declarations",
                PackageArtifactErrorReason::DuplicateTheoremEntry,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_downstream_checker_summaries(
    module: &PackageDownstreamImportModule,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_checker_summaries(&module.checker_summaries)?;
    let mut found_reference = false;
    for (index, summary) in module.checker_summaries.iter().enumerate() {
        let summary_path = format!("{path}.checker_summaries[{index}]");
        assert_downstream_import_field(
            &summary_path,
            "module",
            module.module.as_dotted(),
            summary.module.as_dotted(),
        )?;
        assert_downstream_import_field(
            &summary_path,
            "export_hash",
            format_package_hash(&module.export_hash),
            format_package_hash(&summary.export_hash),
        )?;
        assert_downstream_import_field(
            &summary_path,
            "certificate_hash",
            format_package_hash(&module.certificate_hash),
            format_package_hash(&summary.certificate_hash),
        )?;
        assert_downstream_import_field(
            &summary_path,
            "axiom_report_hash",
            format_package_hash(&module.axiom_report_hash),
            format_package_hash(&summary.axiom_report_hash),
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
            found_reference = true;
        }
    }
    if found_reference {
        Ok(())
    } else {
        Err(PackageArtifactError::missing_field(
            field_path(path, "checker_summaries"),
            "reference",
        ))
    }
}

fn validate_downstream_checker_summaries_match_top_level(
    bundle: &PackageDownstreamImportBundle,
    summaries: &[PackageCheckerSummary],
) -> PackageArtifactResult<()> {
    for module in &bundle.modules {
        let path = format!(
            "downstream_import_bundle.modules.{}",
            module.module.as_dotted()
        );
        for summary in summaries
            .iter()
            .filter(|summary| summary.module == module.module)
        {
            if module.checker_summaries.contains(summary) {
                continue;
            }
            return Err(PackageArtifactError::missing_field(
                field_path(&path, "checker_summaries"),
                checker_summary_key(summary),
            ));
        }
        for summary in &module.checker_summaries {
            if summaries.contains(summary) {
                continue;
            }
            return Err(PackageArtifactError::downstream_import_bundle_mismatch(
                field_path(&path, "checker_summaries"),
                "checker_summaries",
                "top-level checker_summaries entry",
                checker_summary_key(summary),
            ));
        }
    }
    Ok(())
}

fn validate_downstream_checker_summaries_match_registry(
    path: &str,
    module: &PackageDownstreamImportModule,
    entry: &PackageRegistryModule,
) -> PackageArtifactResult<()> {
    for summary in &module.checker_summaries {
        if entry
            .checker_results
            .iter()
            .any(|result| registry_checker_result_matches_summary(result, summary))
        {
            continue;
        }
        return Err(PackageArtifactError::downstream_import_bundle_mismatch(
            field_path(path, "checker_summaries"),
            "checker_summaries",
            "module_registry_entries checker result",
            checker_summary_key(summary),
        ));
    }
    for result in &entry.checker_results {
        if module
            .checker_summaries
            .iter()
            .any(|summary| registry_checker_result_matches_summary(result, summary))
        {
            continue;
        }
        return Err(PackageArtifactError::missing_field(
            field_path(path, "checker_summaries"),
            format!("{} {} {}", result.mode, result.checker, result.profile),
        ));
    }
    Ok(())
}

fn registry_checker_result_matches_summary(
    result: &crate::registry::PackageRegistryCheckerResult,
    summary: &PackageCheckerSummary,
) -> bool {
    result.checker == summary.checker
        && result.profile == summary.profile
        && result.mode == summary.mode.as_str()
        && result.status.as_str() == "accepted"
        && summary.status == "passed"
        && result.export_hash == summary.export_hash
        && result.certificate_hash == summary.certificate_hash
        && result.axiom_report_hash == summary.axiom_report_hash
}

fn checker_summary_key(summary: &PackageCheckerSummary) -> String {
    [
        summary.module.as_dotted(),
        summary.mode.as_str().to_owned(),
        summary.checker.clone(),
        summary.profile.clone(),
    ]
    .join(" ")
}

fn assert_downstream_import_field(
    path: &str,
    field: &'static str,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactResult<()> {
    let expected = expected.into();
    let actual = actual.into();
    if expected == actual {
        Ok(())
    } else {
        Err(PackageArtifactError::downstream_import_bundle_mismatch(
            field_path(path, field),
            field,
            expected,
            actual,
        ))
    }
}

fn validate_downstream_certificate_artifacts(
    artifacts: &[PackagePublishArtifact],
    bundle: &PackageDownstreamImportBundle,
) -> PackageArtifactResult<()> {
    for module in &bundle.modules {
        let path = format!("artifacts.local_certificate.{}", module.module.as_dotted());
        let Some(artifact) = artifacts.iter().find(|artifact| {
            artifact.role == PackagePublishArtifactRole::LocalCertificate
                && artifact.module.as_ref() == Some(&module.module)
        }) else {
            return Err(PackageArtifactError::missing_field(
                "artifacts",
                module.module.as_dotted(),
            ));
        };
        assert_release_artifact_field(
            &path,
            "path",
            module.certificate.as_str(),
            artifact.path.as_str(),
        )?;
        assert_release_artifact_field(
            &path,
            "file_hash",
            format_package_hash(&module.certificate_file_hash),
            format_package_hash(&artifact.file_hash),
        )?;
    }
    Ok(())
}

fn downstream_import_module_from_registry_entry(
    entry: &PackageRegistryModule,
    theorem_index: &PackageTheoremIndex,
    checker_summaries: &[PackageCheckerSummary],
) -> PackageArtifactResult<PackageDownstreamImportModule> {
    Ok(PackageDownstreamImportModule {
        module: entry.module.clone(),
        package: entry.package.clone(),
        version: entry.package_version.clone(),
        exported_declarations: exported_declarations_for_entry(entry, theorem_index)?,
        export_hash: entry.export_hash,
        certificate_hash: entry.certificate_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate: entry.certificate.path.clone(),
        certificate_file_hash: entry.certificate.file_hash,
        checker_summaries: checker_summaries_for_entry(entry, checker_summaries)?,
    })
}

fn exported_declarations_for_entry(
    entry: &PackageRegistryModule,
    theorem_index: &PackageTheoremIndex,
) -> PackageArtifactResult<Vec<Name>> {
    let path = format!(
        "downstream_import_bundle.modules.{}.exported_declarations",
        entry.module.as_dotted()
    );
    let mut declarations = Vec::new();
    for theorem in theorem_index
        .entries
        .iter()
        .filter(|theorem| theorem.global_ref.module == entry.module)
    {
        assert_downstream_import_field(
            &path,
            "export_hash",
            format_package_hash(&entry.export_hash),
            format_package_hash(&theorem.global_ref.export_hash),
        )?;
        assert_downstream_import_field(
            &path,
            "certificate_hash",
            format_package_hash(&entry.certificate_hash),
            format_package_hash(&theorem.global_ref.certificate_hash),
        )?;
        declarations.push(theorem.global_ref.name.clone());
    }
    declarations.sort();
    declarations.dedup();
    validate_exported_declarations(&declarations, &path)?;
    Ok(declarations)
}

fn checker_summaries_for_entry(
    entry: &PackageRegistryModule,
    checker_summaries: &[PackageCheckerSummary],
) -> PackageArtifactResult<Vec<PackageCheckerSummary>> {
    let module_path = format!(
        "downstream_import_bundle.modules.{}",
        entry.module.as_dotted()
    );
    let mut summaries = checker_summaries
        .iter()
        .filter(|summary| summary.module == entry.module)
        .cloned()
        .collect::<Vec<_>>();
    normalize_checker_summaries(&mut summaries);
    let module = PackageDownstreamImportModule {
        module: entry.module.clone(),
        package: entry.package.clone(),
        version: entry.package_version.clone(),
        exported_declarations: Vec::new(),
        export_hash: entry.export_hash,
        certificate_hash: entry.certificate_hash,
        axiom_report_hash: entry.axiom_report_hash,
        certificate: entry.certificate.path.clone(),
        certificate_file_hash: entry.certificate.file_hash,
        checker_summaries: summaries,
    };
    validate_downstream_checker_summaries(&module, &module_path)?;
    validate_downstream_checker_summaries_match_registry(&module_path, &module, entry)?;
    Ok(module.checker_summaries)
}

fn validate_signature_policy(policy: &PackageSignaturePolicy) -> PackageArtifactResult<()> {
    if policy.mode != "checksum-only" {
        return Err(PackageArtifactError::invalid_enum_value(
            "signature_policy.mode",
            "mode",
            "checksum-only",
            policy.mode.clone(),
        ));
    }
    if policy.hash_algorithm != "sha256" {
        return Err(PackageArtifactError::invalid_enum_value(
            "signature_policy.hash_algorithm",
            "hash_algorithm",
            "sha256",
            policy.hash_algorithm.clone(),
        ));
    }
    if policy.signature_required {
        return Err(PackageArtifactError::invalid_enum_value(
            "signature_policy.signature_required",
            "signature_required",
            "false",
            "true",
        ));
    }
    if !policy.signatures.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "signature_policy.signatures",
            "signatures",
            "empty array",
            "signature payloads",
        ));
    }
    Ok(())
}

fn validate_publish_summary(plan: &PackagePublishPlan) -> PackageArtifactResult<()> {
    let expected = PackagePublishSummary {
        local_module_count: u64::try_from(plan.module_registry_entries.len()).unwrap(),
        external_import_count: u64::try_from(
            plan.artifacts
                .iter()
                .filter(|artifact| {
                    artifact.role == PackagePublishArtifactRole::ExternalImportCertificate
                })
                .count(),
        )
        .unwrap(),
        artifact_count: u64::try_from(plan.artifacts.len()).unwrap(),
        registry_entry_count: u64::try_from(plan.module_registry_entries.len()).unwrap(),
        checker_summary_count: u64::try_from(plan.checker_summaries.len()).unwrap(),
    };
    assert_summary_field(
        "summary.local_module_count",
        "local_module_count",
        expected.local_module_count,
        plan.summary.local_module_count,
    )?;
    assert_summary_field(
        "summary.external_import_count",
        "external_import_count",
        expected.external_import_count,
        plan.summary.external_import_count,
    )?;
    assert_summary_field(
        "summary.artifact_count",
        "artifact_count",
        expected.artifact_count,
        plan.summary.artifact_count,
    )?;
    assert_summary_field(
        "summary.registry_entry_count",
        "registry_entry_count",
        expected.registry_entry_count,
        plan.summary.registry_entry_count,
    )?;
    assert_summary_field(
        "summary.checker_summary_count",
        "checker_summary_count",
        expected.checker_summary_count,
        plan.summary.checker_summary_count,
    )
}

fn assert_summary_field(
    path: &str,
    field: &str,
    expected: u64,
    actual: u64,
) -> PackageArtifactResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageArtifactError::summary_mismatch(
            path,
            field,
            expected.to_string(),
            actual.to_string(),
        ))
    }
}

fn parse_release(value: &JsonValue) -> PackageArtifactResult<PackagePublishRelease> {
    let path = "release";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, RELEASE_FIELDS)?;
    Ok(PackagePublishRelease {
        core_spec: required_string(members, path, "core_spec")?,
        kernel_profile: required_string(members, path, "kernel_profile")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        checker_profile: required_string(members, path, "checker_profile")?,
        manifest: parse_release_reference(
            required_value(members, path, "manifest")?,
            "release.manifest",
        )?,
        package_lock: parse_release_reference(
            required_value(members, path, "package_lock")?,
            "release.package_lock",
        )?,
        axiom_report: parse_release_reference(
            required_value(members, path, "axiom_report")?,
            "release.axiom_report",
        )?,
        theorem_index: parse_release_reference(
            required_value(members, path, "theorem_index")?,
            "release.theorem_index",
        )?,
    })
}

fn parse_release_reference(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackagePublishReleaseReference> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, RELEASE_REFERENCE_FIELDS)?;
    Ok(PackagePublishReleaseReference {
        path: required_path(members, path, "path")?,
        file_hash: required_hash(members, path, "file_hash")?,
        content_hash: optional_hash(members, path, "content_hash")?,
        schema: optional_string(members, path, "schema")?,
    })
}

fn parse_publish_artifact(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackagePublishArtifact> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, PUBLISH_ARTIFACT_FIELDS)?;
    let role_path = field_path(path, "role");
    Ok(PackagePublishArtifact {
        role: PackagePublishArtifactRole::parse(
            &required_string(members, path, "role")?,
            &role_path,
        )?,
        path: required_path(members, path, "path")?,
        file_hash: required_hash(members, path, "file_hash")?,
        module: optional_name(members, path, "module")?,
        origin: optional_origin(members, path, "origin")?,
        schema: optional_string(members, path, "schema")?,
    })
}

fn parse_downstream_import_bundle(
    value: &JsonValue,
) -> PackageArtifactResult<PackageDownstreamImportBundle> {
    let path = "downstream_import_bundle";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, DOWNSTREAM_IMPORT_BUNDLE_FIELDS)?;
    Ok(PackageDownstreamImportBundle {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        modules: required_array(members, path, "modules")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_downstream_import_module(
                    value,
                    &format!("downstream_import_bundle.modules[{index}]"),
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_downstream_import_module(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageDownstreamImportModule> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, DOWNSTREAM_IMPORT_MODULE_FIELDS)?;
    Ok(PackageDownstreamImportModule {
        module: required_name(members, path, "module")?,
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        exported_declarations: required_array(members, path, "exported_declarations")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                value.string_value().map(Name::from_dotted).ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        format!("{path}.exported_declarations[{index}]"),
                        Some("exported_declarations".to_owned()),
                        "string",
                        value.kind().as_str(),
                    )
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        certificate: required_path(members, path, "certificate")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        checker_summaries: required_array(members, path, "checker_summaries")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_checker_summary_at_path(value, &format!("{path}.checker_summaries[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_signature_policy(value: &JsonValue) -> PackageArtifactResult<PackageSignaturePolicy> {
    let path = "signature_policy";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SIGNATURE_POLICY_FIELDS)?;
    Ok(PackageSignaturePolicy {
        mode: required_string(members, path, "mode")?,
        hash_algorithm: required_string(members, path, "hash_algorithm")?,
        signature_required: required_bool(members, path, "signature_required")?,
        signatures: required_array(members, path, "signatures")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        format!("signature_policy.signatures[{index}]"),
                        Some("signatures".to_owned()),
                        "string",
                        value.kind().as_str(),
                    )
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_publish_summary(value: &JsonValue) -> PackageArtifactResult<PackagePublishSummary> {
    let path = "summary";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, PUBLISH_SUMMARY_FIELDS)?;
    Ok(PackagePublishSummary {
        local_module_count: required_u64(members, path, "local_module_count")?,
        external_import_count: required_u64(members, path, "external_import_count")?,
        artifact_count: required_u64(members, path, "artifact_count")?,
        registry_entry_count: required_u64(members, path, "registry_entry_count")?,
        checker_summary_count: required_u64(members, path, "checker_summary_count")?,
    })
}

fn release_json(release: &PackagePublishRelease) -> String {
    json_object_in_order(vec![
        ("core_spec", json_string(&release.core_spec)),
        ("kernel_profile", json_string(&release.kernel_profile)),
        (
            "certificate_format",
            json_string(&release.certificate_format),
        ),
        ("checker_profile", json_string(&release.checker_profile)),
        ("manifest", release_reference_json(&release.manifest)),
        (
            "package_lock",
            release_reference_json(&release.package_lock),
        ),
        (
            "axiom_report",
            release_reference_json(&release.axiom_report),
        ),
        (
            "theorem_index",
            release_reference_json(&release.theorem_index),
        ),
    ])
}

fn release_reference_json(reference: &PackagePublishReleaseReference) -> String {
    let mut fields = vec![
        ("path", json_string(reference.path.as_str())),
        ("file_hash", hash_json(reference.file_hash)),
    ];
    if let Some(content_hash) = reference.content_hash {
        fields.push(("content_hash", hash_json(content_hash)));
    }
    if let Some(schema) = &reference.schema {
        fields.push(("schema", json_string(schema)));
    }
    json_object_in_order(fields)
}

fn publish_artifact_json(artifact: &PackagePublishArtifact) -> String {
    let mut fields = vec![
        ("role", json_string(artifact.role.as_str())),
        ("path", json_string(artifact.path.as_str())),
        ("file_hash", hash_json(artifact.file_hash)),
    ];
    if let Some(module) = &artifact.module {
        fields.push(("module", json_string(&module.as_dotted())));
    }
    if let Some(origin) = artifact.origin {
        fields.push(("origin", json_string(origin.as_str())));
    }
    if let Some(schema) = &artifact.schema {
        fields.push(("schema", json_string(schema)));
    }
    json_object_in_order(fields)
}

fn downstream_import_bundle_json(bundle: &PackageDownstreamImportBundle) -> String {
    json_object_in_order(vec![
        ("package", json_string(bundle.package.as_str())),
        ("version", json_string(bundle.version.as_str())),
        (
            "modules",
            json_array(
                bundle
                    .modules
                    .iter()
                    .map(downstream_import_module_json)
                    .collect(),
            ),
        ),
    ])
}

fn downstream_import_module_json(module: &PackageDownstreamImportModule) -> String {
    json_object_in_order(vec![
        ("module", json_string(&module.module.as_dotted())),
        ("package", json_string(module.package.as_str())),
        ("version", json_string(module.version.as_str())),
        (
            "exported_declarations",
            json_array(
                module
                    .exported_declarations
                    .iter()
                    .map(|declaration| json_string(&declaration.as_dotted()))
                    .collect(),
            ),
        ),
        ("export_hash", hash_json(module.export_hash)),
        ("certificate_hash", hash_json(module.certificate_hash)),
        ("axiom_report_hash", hash_json(module.axiom_report_hash)),
        ("certificate", json_string(module.certificate.as_str())),
        (
            "certificate_file_hash",
            hash_json(module.certificate_file_hash),
        ),
        (
            "checker_summaries",
            json_array(
                module
                    .checker_summaries
                    .iter()
                    .map(checker_summary_json)
                    .collect(),
            ),
        ),
    ])
}

fn signature_policy_json(policy: &PackageSignaturePolicy) -> String {
    json_object_in_order(vec![
        ("mode", json_string(&policy.mode)),
        ("hash_algorithm", json_string(&policy.hash_algorithm)),
        ("signature_required", json_bool(policy.signature_required)),
        (
            "signatures",
            json_array(
                policy
                    .signatures
                    .iter()
                    .map(|signature| json_string(signature))
                    .collect(),
            ),
        ),
    ])
}

fn publish_summary_json(summary: &PackagePublishSummary) -> String {
    json_object_in_order(vec![
        ("local_module_count", json_u64(summary.local_module_count)),
        (
            "external_import_count",
            json_u64(summary.external_import_count),
        ),
        ("artifact_count", json_u64(summary.artifact_count)),
        (
            "registry_entry_count",
            json_u64(summary.registry_entry_count),
        ),
        (
            "checker_summary_count",
            json_u64(summary.checker_summary_count),
        ),
    ])
}

fn publish_artifact_sort_key(artifact: &PackagePublishArtifact) -> String {
    [
        artifact.role.as_str().to_owned(),
        artifact
            .module
            .as_ref()
            .map(Name::as_dotted)
            .unwrap_or_default(),
        artifact.path.as_str().to_owned(),
    ]
    .join("\u{001f}")
}

fn downstream_import_module_sort_key(module: &PackageDownstreamImportModule) -> String {
    module.module.as_dotted()
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

fn optional_hash(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<PackageHash>> {
    optional_string(members, path, field)?
        .map(|value| {
            crate::parse_package_hash(&value, field_path(path, field)).map_err(|_| {
                PackageArtifactError::invalid_hash_format(field_path(path, field), value)
            })
        })
        .transpose()
}

fn optional_name(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<Name>> {
    optional_string(members, path, field).map(|value| value.map(Name::from_dotted))
}

fn optional_origin(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<PackageArtifactOrigin>> {
    optional_string(members, path, field)?
        .map(|value| PackageArtifactOrigin::parse(&value, &field_path(path, field)))
        .transpose()
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

const PUBLISH_PLAN_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "release",
    "artifacts",
    "module_registry_entries",
    "downstream_import_bundle",
    "checker_summaries",
    "signature_policy",
    "summary",
    "publish_plan_hash",
];
const RELEASE_FIELDS: &[&str] = &[
    "core_spec",
    "kernel_profile",
    "certificate_format",
    "checker_profile",
    "manifest",
    "package_lock",
    "axiom_report",
    "theorem_index",
];
const RELEASE_REFERENCE_FIELDS: &[&str] = &["path", "file_hash", "content_hash", "schema"];
const PUBLISH_ARTIFACT_FIELDS: &[&str] =
    &["role", "path", "file_hash", "module", "origin", "schema"];
const DOWNSTREAM_IMPORT_BUNDLE_FIELDS: &[&str] = &["package", "version", "modules"];
const DOWNSTREAM_IMPORT_MODULE_FIELDS: &[&str] = &[
    "module",
    "package",
    "version",
    "exported_declarations",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
    "certificate",
    "certificate_file_hash",
    "checker_summaries",
];
const SIGNATURE_POLICY_FIELDS: &[&str] =
    &["mode", "hash_algorithm", "signature_required", "signatures"];
const PUBLISH_SUMMARY_FIELDS: &[&str] = &[
    "local_module_count",
    "external_import_count",
    "artifact_count",
    "registry_entry_count",
    "checker_summary_count",
];

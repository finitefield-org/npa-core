//! Package-level generated theorem index model and canonical JSON.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        axiom_reference_json, axiom_reference_sort_key, checker_summary_json, duplicate_key_error,
        expect_object, field_path, file_reference_json, global_ref_json, global_ref_sort_key,
        global_ref_view_json, global_ref_view_sort_key, hash_json, json_array,
        json_object_in_order, json_string, json_u64, normalize_checker_summaries,
        parse_artifact_json, parse_axiom_reference, parse_checker_summary, parse_file_reference,
        parse_global_ref, parse_global_ref_view, reject_unknown_fields, required_array,
        required_hash, required_string, required_u64, required_value,
        validate_artifact_file_reference, validate_artifact_path, validate_axiom_reference,
        validate_checker_summaries, validate_global_ref, validate_global_ref_view,
        validate_package_identity, PackageArtifactFileReference, PackageArtifactOrigin,
        PackageAxiomReference, PackageCheckerSummary, PackageGlobalRef, PackageGlobalRefView,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    incremental_projection::{
        add_changed_reason, checker_summaries_match, package_incremental_full_projection_plan,
        package_incremental_projection_plan_from_changed_modules, push_reason,
        PackageIncrementalProjectionPlan,
    },
    json::JsonValue,
    lock::{PackageLockEntryOrigin, PackageLockManifest},
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
    schema::PACKAGE_THEOREM_INDEX_SCHEMA,
};

/// CLR-05 certificate-derived theorem index profile.
pub const PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE: &str =
    "npa.package.theorem_index.v0.1.certificate_derived";

/// Generated `npa.package.theorem_index.v0.1` package theorem index artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremIndex {
    /// Theorem index schema string; must equal [`PACKAGE_THEOREM_INDEX_SCHEMA`].
    pub schema: String,
    /// Package identity copied from the validated package manifest.
    pub package: PackageId,
    /// Exact package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Exact package manifest file identity used for extraction.
    pub manifest: PackageArtifactFileReference,
    /// Exact generated package lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Deterministic index projection profile.
    pub index_profile: String,
    /// Public theorem and axiom exports sorted by global reference in canonical JSON.
    pub entries: Vec<PackageTheoremIndexEntry>,
    /// Source-free checker summaries sorted by module, mode, checker, and profile.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// Deterministic package-level theorem index summary.
    pub summary: PackageTheoremIndexSummary,
    /// Self hash of canonical theorem index bytes excluding this field.
    pub theorem_index_hash: PackageHash,
}

impl PackageTheoremIndex {
    /// Return this index with schema-defined array ordering and computed self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_theorem_index(&mut self);
        self.theorem_index_hash = compute_package_theorem_index_hash(&self)?;
        Ok(self)
    }

    /// Serialize this index as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_package_theorem_index(self)?;
        let mut normalized = self.clone();
        normalize_theorem_index(&mut normalized);
        Ok(theorem_index_json_unchecked(&normalized, true))
    }
}

/// One public theorem or axiom export in a package theorem index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremIndexEntry {
    /// Full declaration identity.
    pub global_ref: PackageGlobalRef,
    /// Indexed export kind.
    pub kind: PackageTheoremIndexKind,
    /// Certificate-derived statement projection.
    pub statement: PackageTheoremStatement,
    /// Deterministic search-mode hints.
    pub modes: Vec<PackageTheoremIndexMode>,
    /// Deterministic package tags.
    pub tags: Vec<String>,
    /// Certificate-derived axiom dependencies.
    pub axiom_dependencies: Vec<PackageAxiomReference>,
    /// Module certificate axiom report hash.
    pub module_axiom_report_hash: PackageHash,
    /// Certificate artifact locator.
    pub artifact: PackageTheoremIndexArtifact,
}

/// Package theorem index entry kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremIndexKind {
    /// Theorem export.
    Theorem,
    /// Axiom export.
    Axiom,
}

impl PackageTheoremIndexKind {
    /// Return the generated artifact kind string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Theorem => "theorem",
            Self::Axiom => "axiom",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "theorem" => Ok(Self::Theorem),
            "axiom" => Ok(Self::Axiom),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "kind",
                "theorem or axiom",
                value,
            )),
        }
    }
}

/// Certificate-derived theorem statement projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremStatement {
    /// Structural hash of the statement type.
    pub core_hash: PackageHash,
    /// Optional head global reference view.
    pub head: Option<PackageGlobalRefView>,
    /// Constant global reference views used by the statement, sorted canonically.
    pub constants: Vec<PackageGlobalRefView>,
}

/// Package theorem index search mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremIndexMode {
    /// Exact search mode.
    Exact,
    /// Forward/backward apply search mode.
    Apply,
    /// Rewrite search mode.
    Rw,
    /// Simplifier search mode.
    Simp,
}

impl PackageTheoremIndexMode {
    /// Return the generated artifact mode string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Apply => "apply",
            Self::Exact => "exact",
            Self::Rw => "rw",
            Self::Simp => "simp",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "apply" => Ok(Self::Apply),
            "exact" => Ok(Self::Exact),
            "rw" => Ok(Self::Rw),
            "simp" => Ok(Self::Simp),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "modes",
                "exact, apply, rw, or simp",
                value,
            )),
        }
    }
}

/// Certificate artifact locator for one theorem index entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremIndexArtifact {
    /// Whether the certificate belongs to the local package or an external import.
    pub origin: PackageArtifactOrigin,
    /// Package-relative certificate path.
    pub certificate: PackagePath,
}

/// Deterministic package theorem index summary counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremIndexSummary {
    /// Total indexed entry count.
    pub entry_count: u64,
    /// Theorem entry count.
    pub theorem_count: u64,
    /// Axiom entry count.
    pub axiom_count: u64,
    /// Number of modules represented by indexed entries.
    pub module_count: u64,
    /// Number of entries with non-empty axiom dependencies.
    pub entries_with_axioms_count: u64,
}

/// Parse and validate a checked-in package theorem index JSON artifact.
pub fn parse_package_theorem_index_json(
    source: &str,
) -> PackageArtifactResult<PackageTheoremIndex> {
    let root = parse_artifact_json(source)?;
    let index = parse_theorem_index_value(&root)?;
    validate_package_theorem_index(&index)?;
    let canonical = index.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package theorem index JSON bytes",
        ));
    }
    Ok(index)
}

/// Validate a package theorem index model without reading files or running checkers.
pub fn validate_package_theorem_index(index: &PackageTheoremIndex) -> PackageArtifactResult<()> {
    if index.schema != PACKAGE_THEOREM_INDEX_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_THEOREM_INDEX_SCHEMA,
            index.schema.clone(),
        ));
    }
    validate_package_identity(&index.package, &index.version)?;
    validate_artifact_file_reference(&index.manifest, "manifest")?;
    validate_artifact_file_reference(&index.package_lock, "package_lock")?;
    if index.index_profile != PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE {
        return Err(PackageArtifactError::invalid_enum_value(
            "index_profile",
            "index_profile",
            PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE,
            index.index_profile.clone(),
        ));
    }
    validate_theorem_entries(&index.entries)?;
    validate_checker_summaries(&index.checker_summaries)?;
    validate_theorem_index_summary(index)?;

    let expected_hash = compute_package_theorem_index_hash(index)?;
    if expected_hash != index.theorem_index_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "theorem_index_hash",
            "theorem_index_hash",
            format_package_hash(&expected_hash),
            format_package_hash(&index.theorem_index_hash),
        ));
    }
    Ok(())
}

/// Compute the package theorem index self hash over canonical bytes excluding the self-hash field.
pub fn compute_package_theorem_index_hash(
    index: &PackageTheoremIndex,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = index.clone();
    normalize_theorem_index(&mut normalized);
    validate_theorem_index_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        theorem_index_json_unchecked(&normalized, false).as_bytes(),
    ))
}

/// Compute deterministic package theorem index summary counts for entries.
pub fn package_theorem_index_summary(
    entries: &[PackageTheoremIndexEntry],
) -> PackageTheoremIndexSummary {
    expected_theorem_index_summary(entries)
}

/// Plan an incremental package theorem-index check against current package metadata.
///
/// The plan is optimization metadata only. It uses the current package-lock hash
/// plus per-module export, certificate, certificate-file, and axiom-report hashes
/// recovered from checked theorem-index entries as the invalidation boundary.
pub fn package_theorem_index_incremental_projection_plan(
    index: &PackageTheoremIndex,
    package: &PackageId,
    version: &PackageVersion,
    manifest: &PackageArtifactFileReference,
    package_lock: &PackageArtifactFileReference,
    checker_summaries: &[PackageCheckerSummary],
    current_lock: &PackageLockManifest,
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let mut full_reasons = Vec::new();
    push_reason(
        &mut full_reasons,
        index.schema != PACKAGE_THEOREM_INDEX_SCHEMA,
        "projection_schema_changed",
    );
    push_reason(
        &mut full_reasons,
        &index.package != package || &index.version != version,
        "package_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        &index.manifest != manifest,
        "manifest_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        index.package_lock.path != package_lock.path,
        "package_lock_path_changed",
    );
    push_reason(
        &mut full_reasons,
        index.index_profile != PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE,
        "index_profile_changed",
    );
    push_reason(
        &mut full_reasons,
        !checker_summaries_match(&index.checker_summaries, checker_summaries),
        "checker_profile_or_summary_changed",
    );
    push_reason(
        &mut full_reasons,
        current_lock.schema != crate::schema::PACKAGE_LOCK_SCHEMA,
        "package_lock_schema_changed",
    );

    let lock_hash_changed = index.package_lock.file_hash != package_lock.file_hash;
    let changed_modules =
        theorem_index_changed_modules(index, current_lock, lock_hash_changed, &mut full_reasons);
    if lock_hash_changed && changed_modules.is_empty() && full_reasons.is_empty() {
        return package_incremental_full_projection_plan(
            "theorem-index",
            current_lock,
            ["package_lock_unattributed_change"],
        );
    }

    package_incremental_projection_plan_from_changed_modules(
        "theorem-index",
        current_lock,
        full_reasons,
        changed_modules,
    )
}

fn validate_theorem_index_shape_without_self_hash(
    index: &PackageTheoremIndex,
) -> PackageArtifactResult<()> {
    if index.schema != PACKAGE_THEOREM_INDEX_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_THEOREM_INDEX_SCHEMA,
            index.schema.clone(),
        ));
    }
    validate_package_identity(&index.package, &index.version)?;
    validate_artifact_file_reference(&index.manifest, "manifest")?;
    validate_artifact_file_reference(&index.package_lock, "package_lock")?;
    if index.index_profile != PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE {
        return Err(PackageArtifactError::invalid_enum_value(
            "index_profile",
            "index_profile",
            PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE,
            index.index_profile.clone(),
        ));
    }
    validate_theorem_entries(&index.entries)?;
    validate_checker_summaries(&index.checker_summaries)?;
    validate_theorem_index_summary(index)
}

fn validate_theorem_entries(entries: &[PackageTheoremIndexEntry]) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, entry) in entries.iter().enumerate() {
        let path = format!("entries[{index}]");
        validate_global_ref(&entry.global_ref, &format!("{path}.global_ref"))?;
        let key = global_ref_sort_key(&entry.global_ref);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                field_path(&path, "global_ref"),
                "global_ref",
                PackageArtifactErrorReason::DuplicateTheoremEntry,
                key,
            ));
        }
        validate_statement(&entry.statement, &format!("{path}.statement"))?;
        validate_modes(&entry.modes, &format!("{path}.modes"))?;
        validate_tags(&entry.tags, &format!("{path}.tags"))?;
        validate_axiom_dependencies(
            &entry.axiom_dependencies,
            &format!("{path}.axiom_dependencies"),
        )?;
        validate_artifact_path(
            &entry.artifact.certificate,
            format!("{path}.artifact.certificate"),
        )?;
    }
    Ok(())
}

fn validate_statement(
    statement: &PackageTheoremStatement,
    path: &str,
) -> PackageArtifactResult<()> {
    if let Some(head) = &statement.head {
        validate_global_ref_view(head, &field_path(path, "head"))?;
    }
    let mut keys = BTreeSet::<String>::new();
    for (index, constant) in statement.constants.iter().enumerate() {
        let item_path = format!("{path}.constants[{index}]");
        validate_global_ref_view(constant, &item_path)?;
        let key = global_ref_view_sort_key(constant);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                item_path,
                "constants",
                PackageArtifactErrorReason::DuplicateConstant,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_modes(modes: &[PackageTheoremIndexMode], path: &str) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::<PackageTheoremIndexMode>::new();
    for (index, mode) in modes.iter().enumerate() {
        if !seen.insert(*mode) {
            return Err(duplicate_key_error(
                format!("{path}[{index}]"),
                "modes",
                PackageArtifactErrorReason::DuplicateMode,
                mode.as_str(),
            ));
        }
    }
    if !seen.contains(&PackageTheoremIndexMode::Exact) {
        return Err(PackageArtifactError::summary_mismatch(
            path,
            "modes",
            "exact mode present",
            "missing",
        ));
    }
    Ok(())
}

fn validate_tags(tags: &[String], path: &str) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::<String>::new();
    for (index, tag) in tags.iter().enumerate() {
        if tag.is_empty()
            || tag.chars().any(char::is_control)
            || tag.contains('/')
            || tag.contains('\\')
            || tag.contains(':')
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}[{index}]"),
                "tags",
                "deterministic tag without path or URL characters",
                tag,
            ));
        }
        if !seen.insert(tag.clone()) {
            return Err(duplicate_key_error(
                format!("{path}[{index}]"),
                "tags",
                PackageArtifactErrorReason::DuplicateTag,
                tag,
            ));
        }
    }
    Ok(())
}

fn validate_axiom_dependencies(
    axioms: &[PackageAxiomReference],
    path: &str,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, axiom) in axioms.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        validate_axiom_reference(axiom, &item_path)?;
        let key = axiom_reference_sort_key(axiom);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                item_path,
                "axiom_dependencies",
                PackageArtifactErrorReason::DuplicateAxiom,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_theorem_index_summary(index: &PackageTheoremIndex) -> PackageArtifactResult<()> {
    let expected = expected_theorem_index_summary(&index.entries);
    check_summary_count(
        "summary.entry_count",
        "entry_count",
        expected.entry_count,
        index.summary.entry_count,
    )?;
    check_summary_count(
        "summary.theorem_count",
        "theorem_count",
        expected.theorem_count,
        index.summary.theorem_count,
    )?;
    check_summary_count(
        "summary.axiom_count",
        "axiom_count",
        expected.axiom_count,
        index.summary.axiom_count,
    )?;
    check_summary_count(
        "summary.module_count",
        "module_count",
        expected.module_count,
        index.summary.module_count,
    )?;
    check_summary_count(
        "summary.entries_with_axioms_count",
        "entries_with_axioms_count",
        expected.entries_with_axioms_count,
        index.summary.entries_with_axioms_count,
    )
}

fn expected_theorem_index_summary(
    entries: &[PackageTheoremIndexEntry],
) -> PackageTheoremIndexSummary {
    let mut modules = BTreeSet::<String>::new();
    let mut theorem_count = 0_u64;
    let mut axiom_count = 0_u64;
    let mut entries_with_axioms_count = 0_u64;

    for entry in entries {
        modules.insert(entry.global_ref.module.as_dotted());
        match entry.kind {
            PackageTheoremIndexKind::Theorem => theorem_count += 1,
            PackageTheoremIndexKind::Axiom => axiom_count += 1,
        }
        if !entry.axiom_dependencies.is_empty() {
            entries_with_axioms_count += 1;
        }
    }

    PackageTheoremIndexSummary {
        entry_count: entries.len() as u64,
        theorem_count,
        axiom_count,
        module_count: modules.len() as u64,
        entries_with_axioms_count,
    }
}

#[derive(Clone, Debug, Default)]
struct TheoremIndexModuleIdentity {
    origins: BTreeSet<PackageArtifactOrigin>,
    certificates: BTreeSet<PackagePath>,
    export_hashes: BTreeSet<PackageHash>,
    certificate_hashes: BTreeSet<PackageHash>,
    axiom_report_hashes: BTreeSet<PackageHash>,
}

fn theorem_index_changed_modules(
    index: &PackageTheoremIndex,
    current_lock: &PackageLockManifest,
    lock_hash_changed: bool,
    full_reasons: &mut Vec<String>,
) -> BTreeMap<Name, BTreeSet<String>> {
    let previous = theorem_index_module_identities(index, full_reasons);
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
            if lock_hash_changed {
                full_reasons.push("theorem_index_module_absent_from_checked_artifact".to_owned());
            }
            continue;
        };
        add_changed_reason(
            &mut changed,
            &module,
            !single_origin_matches_lock(&previous.origins, entry.origin),
            "module_origin_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            !single_path_matches(&previous.certificates, &entry.certificate),
            "certificate_path_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            !single_hash_matches(&previous.export_hashes, entry.export_hash),
            "export_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            !single_hash_matches(&previous.certificate_hashes, entry.certificate_hash),
            "certificate_hash_changed",
        );
        add_changed_reason(
            &mut changed,
            &module,
            !single_hash_matches(&previous.axiom_report_hashes, entry.axiom_report_hash),
            "axiom_report_hash_changed",
        );
    }

    changed
}

fn theorem_index_module_identities(
    index: &PackageTheoremIndex,
    full_reasons: &mut Vec<String>,
) -> BTreeMap<Name, TheoremIndexModuleIdentity> {
    let mut modules = BTreeMap::<Name, TheoremIndexModuleIdentity>::new();
    for entry in &index.entries {
        let module = modules.entry(entry.global_ref.module.clone()).or_default();
        module.origins.insert(entry.artifact.origin);
        module
            .certificates
            .insert(entry.artifact.certificate.clone());
        module.export_hashes.insert(entry.global_ref.export_hash);
        module
            .certificate_hashes
            .insert(entry.global_ref.certificate_hash);
        module
            .axiom_report_hashes
            .insert(entry.module_axiom_report_hash);
    }
    for identity in modules.values() {
        if identity.origins.len() > 1
            || identity.certificates.len() > 1
            || identity.export_hashes.len() > 1
            || identity.certificate_hashes.len() > 1
            || identity.axiom_report_hashes.len() > 1
        {
            full_reasons.push("theorem_index_module_identity_ambiguous".to_owned());
        }
    }
    modules
}

fn single_origin_matches_lock(
    origins: &BTreeSet<PackageArtifactOrigin>,
    lock_origin: PackageLockEntryOrigin,
) -> bool {
    let Some(origin) = single_value(origins) else {
        return false;
    };
    matches!(
        (lock_origin, *origin),
        (PackageLockEntryOrigin::Local, PackageArtifactOrigin::Local)
            | (
                PackageLockEntryOrigin::External,
                PackageArtifactOrigin::External
            )
    )
}

fn single_path_matches(paths: &BTreeSet<PackagePath>, expected: &PackagePath) -> bool {
    single_value(paths).is_some_and(|actual| actual == expected)
}

fn single_hash_matches(hashes: &BTreeSet<PackageHash>, expected: PackageHash) -> bool {
    single_value(hashes).is_some_and(|actual| *actual == expected)
}

fn single_value<T>(values: &BTreeSet<T>) -> Option<&T> {
    let mut iter = values.iter();
    let value = iter.next()?;
    iter.next().is_none().then_some(value)
}

fn check_summary_count(
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

fn normalize_theorem_index(index: &mut PackageTheoremIndex) {
    index
        .entries
        .sort_by_key(|entry| global_ref_sort_key(&entry.global_ref));
    for entry in &mut index.entries {
        entry.modes.sort_by_key(|mode| mode.as_str());
        entry.tags.sort();
        entry
            .statement
            .constants
            .sort_by_key(global_ref_view_sort_key);
        entry
            .axiom_dependencies
            .sort_by_key(axiom_reference_sort_key);
    }
    normalize_checker_summaries(&mut index.checker_summaries);
}

fn parse_theorem_index_value(value: &JsonValue) -> PackageArtifactResult<PackageTheoremIndex> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, TOP_LEVEL_FIELDS)?;
    Ok(PackageTheoremIndex {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        manifest: parse_file_reference(required_value(members, "$", "manifest")?, "manifest")?,
        package_lock: parse_file_reference(
            required_value(members, "$", "package_lock")?,
            "package_lock",
        )?,
        index_profile: required_string(members, "$", "index_profile")?,
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_summaries: required_array(members, "$", "checker_summaries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_checker_summary(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        summary: parse_summary(required_value(members, "$", "summary")?)?,
        theorem_index_hash: required_hash(members, "$", "theorem_index_hash")?,
    })
}

fn parse_entry(index: usize, value: &JsonValue) -> PackageArtifactResult<PackageTheoremIndexEntry> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    let kind_path = field_path(&path, "kind");
    Ok(PackageTheoremIndexEntry {
        global_ref: parse_global_ref(
            required_value(members, &path, "global_ref")?,
            &field_path(&path, "global_ref"),
        )?,
        kind: PackageTheoremIndexKind::parse(
            &required_string(members, &path, "kind")?,
            &kind_path,
        )?,
        statement: parse_statement(
            required_value(members, &path, "statement")?,
            &format!("{path}.statement"),
        )?,
        modes: parse_modes(
            required_array(members, &path, "modes")?,
            &format!("{path}.modes"),
        )?,
        tags: parse_tags(
            required_array(members, &path, "tags")?,
            &format!("{path}.tags"),
        )?,
        axiom_dependencies: required_array(members, &path, "axiom_dependencies")?
            .iter()
            .enumerate()
            .map(|(axiom_index, value)| {
                parse_axiom_reference(value, &format!("{path}.axiom_dependencies[{axiom_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        module_axiom_report_hash: required_hash(members, &path, "module_axiom_report_hash")?,
        artifact: parse_artifact(
            required_value(members, &path, "artifact")?,
            &format!("{path}.artifact"),
        )?,
    })
}

fn parse_statement(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremStatement> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, STATEMENT_FIELDS)?;
    Ok(PackageTheoremStatement {
        core_hash: required_hash(members, path, "core_hash")?,
        head: parse_optional_global_ref_view(
            required_value(members, path, "head")?,
            &field_path(path, "head"),
        )?,
        constants: required_array(members, path, "constants")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_global_ref_view(value, &format!("{path}.constants[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_optional_global_ref_view(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<Option<PackageGlobalRefView>> {
    if matches!(value, JsonValue::Null) {
        Ok(None)
    } else {
        parse_global_ref_view(value, path).map(Some)
    }
}

fn parse_modes(
    values: &[JsonValue],
    path: &str,
) -> PackageArtifactResult<Vec<PackageTheoremIndexMode>> {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let item_path = format!("{path}[{index}]");
            let Some(mode) = value.string_value() else {
                return Err(PackageArtifactError::wrong_type(
                    item_path,
                    Some("modes".to_owned()),
                    "string",
                    value.kind().as_str(),
                ));
            };
            PackageTheoremIndexMode::parse(mode, &item_path)
        })
        .collect()
}

fn parse_tags(values: &[JsonValue], path: &str) -> PackageArtifactResult<Vec<String>> {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}[{index}]"),
                    Some("tags".to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn parse_artifact(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremIndexArtifact> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ARTIFACT_FIELDS)?;
    let origin_path = field_path(path, "origin");
    Ok(PackageTheoremIndexArtifact {
        origin: PackageArtifactOrigin::parse(
            &required_string(members, path, "origin")?,
            &origin_path,
        )?,
        certificate: PackagePath::new(required_string(members, path, "certificate")?),
    })
}

fn parse_summary(value: &JsonValue) -> PackageArtifactResult<PackageTheoremIndexSummary> {
    let path = "summary";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SUMMARY_FIELDS)?;
    Ok(PackageTheoremIndexSummary {
        entry_count: required_u64(members, path, "entry_count")?,
        theorem_count: required_u64(members, path, "theorem_count")?,
        axiom_count: required_u64(members, path, "axiom_count")?,
        module_count: required_u64(members, path, "module_count")?,
        entries_with_axioms_count: required_u64(members, path, "entries_with_axioms_count")?,
    })
}

fn theorem_index_json_unchecked(index: &PackageTheoremIndex, include_self_hash: bool) -> String {
    let mut fields = vec![
        ("schema", json_string(&index.schema)),
        ("package", json_string(index.package.as_str())),
        ("version", json_string(index.version.as_str())),
        ("manifest", file_reference_json(&index.manifest)),
        ("package_lock", file_reference_json(&index.package_lock)),
        ("index_profile", json_string(&index.index_profile)),
        (
            "entries",
            json_array(index.entries.iter().map(entry_json).collect()),
        ),
        (
            "checker_summaries",
            json_array(
                index
                    .checker_summaries
                    .iter()
                    .map(checker_summary_json)
                    .collect(),
            ),
        ),
        ("summary", summary_json(&index.summary)),
    ];
    if include_self_hash {
        fields.push(("theorem_index_hash", hash_json(index.theorem_index_hash)));
    }
    json_object_in_order(fields)
}

fn entry_json(entry: &PackageTheoremIndexEntry) -> String {
    json_object_in_order(vec![
        ("global_ref", global_ref_json(&entry.global_ref)),
        ("kind", json_string(entry.kind.as_str())),
        ("statement", statement_json(&entry.statement)),
        (
            "modes",
            json_array(
                entry
                    .modes
                    .iter()
                    .map(|mode| json_string(mode.as_str()))
                    .collect(),
            ),
        ),
        (
            "tags",
            json_array(entry.tags.iter().map(|tag| json_string(tag)).collect()),
        ),
        (
            "axiom_dependencies",
            json_array(
                entry
                    .axiom_dependencies
                    .iter()
                    .map(axiom_reference_json)
                    .collect(),
            ),
        ),
        (
            "module_axiom_report_hash",
            hash_json(entry.module_axiom_report_hash),
        ),
        ("artifact", artifact_json(&entry.artifact)),
    ])
}

fn statement_json(statement: &PackageTheoremStatement) -> String {
    json_object_in_order(vec![
        ("core_hash", hash_json(statement.core_hash)),
        (
            "head",
            statement
                .head
                .as_ref()
                .map(global_ref_view_json)
                .unwrap_or_else(|| "null".to_owned()),
        ),
        (
            "constants",
            json_array(
                statement
                    .constants
                    .iter()
                    .map(global_ref_view_json)
                    .collect(),
            ),
        ),
    ])
}

fn artifact_json(artifact: &PackageTheoremIndexArtifact) -> String {
    json_object_in_order(vec![
        ("origin", json_string(artifact.origin.as_str())),
        ("certificate", json_string(artifact.certificate.as_str())),
    ])
}

fn summary_json(summary: &PackageTheoremIndexSummary) -> String {
    json_object_in_order(vec![
        ("entry_count", json_u64(summary.entry_count)),
        ("theorem_count", json_u64(summary.theorem_count)),
        ("axiom_count", json_u64(summary.axiom_count)),
        ("module_count", json_u64(summary.module_count)),
        (
            "entries_with_axioms_count",
            json_u64(summary.entries_with_axioms_count),
        ),
    ])
}

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "manifest",
    "package_lock",
    "index_profile",
    "entries",
    "checker_summaries",
    "summary",
    "theorem_index_hash",
];
const ENTRY_FIELDS: &[&str] = &[
    "global_ref",
    "kind",
    "statement",
    "modes",
    "tags",
    "axiom_dependencies",
    "module_axiom_report_hash",
    "artifact",
];
const STATEMENT_FIELDS: &[&str] = &["core_hash", "head", "constants"];
const ARTIFACT_FIELDS: &[&str] = &["origin", "certificate"];
const SUMMARY_FIELDS: &[&str] = &[
    "entry_count",
    "theorem_count",
    "axiom_count",
    "module_count",
    "entries_with_axioms_count",
];

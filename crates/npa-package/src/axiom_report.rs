//! Package-level generated axiom report model and canonical JSON.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        axiom_reference_json, axiom_reference_sort_key, checker_summary_json, duplicate_key_error,
        expect_object, field_path, file_reference_json, hash_json, json_array,
        json_object_in_order, json_string, json_u64, normalize_checker_summaries, normalize_policy,
        parse_artifact_json, parse_axiom_reference, parse_checker_summary, parse_file_reference,
        parse_policy, reject_unknown_fields, required_array, required_hash, required_name,
        required_string, required_u64, validate_artifact_file_reference, validate_axiom_reference,
        validate_checker_summaries, validate_module_name, validate_package_identity,
        validate_policy, PackageArtifactFileReference, PackageArtifactOrigin,
        PackageArtifactPolicy, PackageAxiomReference, PackageCheckerSummary,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    incremental_projection::{
        add_changed_reason, checker_summaries_match, package_incremental_full_projection_plan,
        package_incremental_projection_plan_from_changed_modules, push_reason,
        PackageIncrementalProjectionPlan,
    },
    lock::{PackageLockEntryOrigin, PackageLockManifest},
    manifest::PackageVersion,
    name::PackageId,
    schema::PACKAGE_AXIOM_REPORT_SCHEMA,
};

/// Generated `npa.package.axiom_report.v0.1` package axiom report artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomReport {
    /// Axiom report schema string; must equal [`PACKAGE_AXIOM_REPORT_SCHEMA`].
    pub schema: String,
    /// Package identity copied from the validated package manifest.
    pub package: PackageId,
    /// Exact package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Exact package manifest file identity used for extraction.
    pub manifest: PackageArtifactFileReference,
    /// Exact generated package lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Package axiom policy copied from `npa-package.toml`.
    pub policy: PackageArtifactPolicy,
    /// Module axiom summaries sorted by module name in canonical JSON.
    pub modules: Vec<PackageAxiomReportModule>,
    /// Source-free checker summaries sorted by module, mode, checker, and profile.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// Deterministic package-level axiom summary.
    pub summary: PackageAxiomReportSummary,
    /// Self hash of canonical axiom report bytes excluding this field.
    pub package_axiom_report_hash: PackageHash,
}

impl PackageAxiomReport {
    /// Return this report with schema-defined array ordering and computed self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_axiom_report(&mut self);
        self.package_axiom_report_hash = compute_package_axiom_report_hash(&self)?;
        Ok(self)
    }

    /// Serialize this report as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_package_axiom_report(self)?;
        let mut normalized = self.clone();
        normalize_axiom_report(&mut normalized);
        Ok(axiom_report_json_unchecked(&normalized, true))
    }
}

/// One module entry in a package axiom report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomReportModule {
    /// Module name.
    pub module: Name,
    /// Whether this entry is local or external.
    pub origin: PackageArtifactOrigin,
    /// Module export hash.
    pub export_hash: PackageHash,
    /// Module certificate hash.
    pub certificate_hash: PackageHash,
    /// Module certificate axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Exact SHA-256 hash of the certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Direct axioms declared by or directly used inside the module.
    pub direct_axioms: Vec<PackageAxiomReference>,
    /// Direct axioms plus dependency axiom reports.
    pub transitive_axioms: Vec<PackageAxiomReference>,
    /// Package policy result for this module.
    pub policy_status: PackageAxiomPolicyStatus,
}

/// Package policy result for one module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomPolicyStatus {
    /// Stable policy status.
    pub status: PackageAxiomPolicyStatusKind,
    /// Deterministic policy violations.
    pub violations: Vec<PackageAxiomPolicyViolation>,
}

/// Stable package axiom policy status.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageAxiomPolicyStatusKind {
    /// Module satisfies package axiom policy.
    Ok,
    /// Module violates package axiom policy.
    Violation,
}

impl PackageAxiomPolicyStatusKind {
    /// Return the generated artifact status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Violation => "violation",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "ok" => Ok(Self::Ok),
            "violation" => Ok(Self::Violation),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "status",
                "ok or violation",
                value,
            )),
        }
    }
}

/// One package axiom policy violation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomPolicyViolation {
    /// Violating axiom reference.
    pub axiom: PackageAxiomReference,
    /// Stable violation reason.
    pub reason_code: PackageAxiomPolicyViolationReason,
}

/// Stable package axiom policy violation reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageAxiomPolicyViolationReason {
    /// Custom axioms are disallowed by package policy.
    CustomAxiomDisallowed,
    /// Axiom is absent from the package allowlist.
    AxiomNotAllowlisted,
    /// `sorry` or a `sorry`-equivalent axiom is disallowed.
    SorryDisallowed,
}

impl PackageAxiomPolicyViolationReason {
    /// Return the generated artifact reason string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CustomAxiomDisallowed => "custom_axiom_disallowed",
            Self::AxiomNotAllowlisted => "axiom_not_allowlisted",
            Self::SorryDisallowed => "sorry_disallowed",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "custom_axiom_disallowed" => Ok(Self::CustomAxiomDisallowed),
            "axiom_not_allowlisted" => Ok(Self::AxiomNotAllowlisted),
            "sorry_disallowed" => Ok(Self::SorryDisallowed),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "reason_code",
                "custom_axiom_disallowed, axiom_not_allowlisted, or sorry_disallowed",
                value,
            )),
        }
    }
}

/// Deterministic package axiom report summary counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomReportSummary {
    /// Total module count.
    pub module_count: u64,
    /// Local module count.
    pub local_module_count: u64,
    /// External module count.
    pub external_module_count: u64,
    /// Unique package-wide direct axiom count.
    pub direct_axiom_count: u64,
    /// Unique package-wide transitive axiom count.
    pub transitive_axiom_count: u64,
    /// Total package policy violation count.
    pub policy_violation_count: u64,
}

/// Parse and validate a checked-in package axiom report JSON artifact.
pub fn parse_package_axiom_report_json(source: &str) -> PackageArtifactResult<PackageAxiomReport> {
    let root = parse_artifact_json(source)?;
    let report = parse_axiom_report_value(&root)?;
    validate_package_axiom_report(&report)?;
    let canonical = report.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package axiom report JSON bytes",
        ));
    }
    Ok(report)
}

/// Validate a package axiom report model without reading files or running checkers.
pub fn validate_package_axiom_report(report: &PackageAxiomReport) -> PackageArtifactResult<()> {
    if report.schema != PACKAGE_AXIOM_REPORT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_AXIOM_REPORT_SCHEMA,
            report.schema.clone(),
        ));
    }
    validate_package_identity(&report.package, &report.version)?;
    validate_artifact_file_reference(&report.manifest, "manifest")?;
    validate_artifact_file_reference(&report.package_lock, "package_lock")?;
    validate_policy(&report.policy)?;
    validate_axiom_report_modules(&report.modules)?;
    validate_checker_summaries(&report.checker_summaries)?;
    validate_axiom_report_summary(report)?;

    let expected_hash = compute_package_axiom_report_hash(report)?;
    if expected_hash != report.package_axiom_report_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "package_axiom_report_hash",
            "package_axiom_report_hash",
            format_package_hash(&expected_hash),
            format_package_hash(&report.package_axiom_report_hash),
        ));
    }
    Ok(())
}

/// Compute the package axiom report self hash over canonical bytes excluding the self-hash field.
pub fn compute_package_axiom_report_hash(
    report: &PackageAxiomReport,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = report.clone();
    normalize_axiom_report(&mut normalized);
    validate_axiom_report_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        axiom_report_json_unchecked(&normalized, false).as_bytes(),
    ))
}

/// Compute deterministic package axiom report summary counts from module entries.
pub fn package_axiom_report_summary(
    modules: &[PackageAxiomReportModule],
) -> PackageAxiomReportSummary {
    expected_axiom_report_summary(modules)
}

/// Plan an incremental package axiom-report check against current package metadata.
///
/// The plan is optimization metadata only. It is never proof evidence and uses
/// the current package-lock hash plus per-module export, certificate,
/// certificate-file, and axiom-report hashes as the invalidation boundary.
pub fn package_axiom_report_incremental_projection_plan(
    input: PackageAxiomReportIncrementalProjectionInput<'_>,
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let mut full_reasons = Vec::new();
    push_reason(
        &mut full_reasons,
        input.report.schema != PACKAGE_AXIOM_REPORT_SCHEMA,
        "projection_schema_changed",
    );
    push_reason(
        &mut full_reasons,
        input.report.package != *input.package || input.report.version != *input.version,
        "package_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        input.report.manifest != *input.manifest,
        "manifest_identity_changed",
    );
    push_reason(
        &mut full_reasons,
        input.report.package_lock.path != input.package_lock.path,
        "package_lock_path_changed",
    );
    push_reason(
        &mut full_reasons,
        input.report.policy != *input.policy,
        "policy_changed",
    );
    push_reason(
        &mut full_reasons,
        !checker_summaries_match(&input.report.checker_summaries, input.checker_summaries),
        "checker_profile_or_summary_changed",
    );
    push_reason(
        &mut full_reasons,
        input.current_lock.schema != crate::schema::PACKAGE_LOCK_SCHEMA,
        "package_lock_schema_changed",
    );

    let changed_modules =
        axiom_report_changed_modules(input.report, input.current_lock, &mut full_reasons);
    if input.report.package_lock.file_hash != input.package_lock.file_hash
        && changed_modules.is_empty()
        && full_reasons.is_empty()
    {
        return package_incremental_full_projection_plan(
            "axiom-report",
            input.current_lock,
            ["package_lock_unattributed_change"],
        );
    }

    package_incremental_projection_plan_from_changed_modules(
        "axiom-report",
        input.current_lock,
        full_reasons,
        changed_modules,
    )
}

/// Inputs for incremental package axiom-report projection planning.
pub struct PackageAxiomReportIncrementalProjectionInput<'a> {
    /// Checked package axiom report.
    pub report: &'a PackageAxiomReport,
    /// Current package id from the validated manifest.
    pub package: &'a PackageId,
    /// Current package version from the validated manifest.
    pub version: &'a PackageVersion,
    /// Current manifest file identity.
    pub manifest: &'a PackageArtifactFileReference,
    /// Current package-lock file identity.
    pub package_lock: &'a PackageArtifactFileReference,
    /// Current package axiom policy.
    pub policy: &'a PackageArtifactPolicy,
    /// Current checker summaries used by projection.
    pub checker_summaries: &'a [PackageCheckerSummary],
    /// Current package lock manifest.
    pub current_lock: &'a PackageLockManifest,
}

fn validate_axiom_report_shape_without_self_hash(
    report: &PackageAxiomReport,
) -> PackageArtifactResult<()> {
    if report.schema != PACKAGE_AXIOM_REPORT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_AXIOM_REPORT_SCHEMA,
            report.schema.clone(),
        ));
    }
    validate_package_identity(&report.package, &report.version)?;
    validate_artifact_file_reference(&report.manifest, "manifest")?;
    validate_artifact_file_reference(&report.package_lock, "package_lock")?;
    validate_policy(&report.policy)?;
    validate_axiom_report_modules(&report.modules)?;
    validate_checker_summaries(&report.checker_summaries)?;
    validate_axiom_report_summary(report)
}

fn validate_axiom_report_modules(
    modules: &[PackageAxiomReportModule],
) -> PackageArtifactResult<()> {
    let mut module_names = BTreeSet::<Name>::new();
    for (index, module) in modules.iter().enumerate() {
        let path = format!("modules[{index}]");
        validate_module_name(&module.module, field_path(&path, "module"))?;
        if !module_names.insert(module.module.clone()) {
            return Err(duplicate_key_error(
                field_path(&path, "module"),
                "module",
                PackageArtifactErrorReason::DuplicateModule,
                module.module.as_dotted(),
            ));
        }
        validate_axiom_list(&module.direct_axioms, &format!("{path}.direct_axioms"))?;
        validate_axiom_list(
            &module.transitive_axioms,
            &format!("{path}.transitive_axioms"),
        )?;
        validate_policy_status(&module.policy_status, &format!("{path}.policy_status"))?;
    }
    Ok(())
}

fn validate_axiom_list(axioms: &[PackageAxiomReference], path: &str) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, axiom) in axioms.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        validate_axiom_reference(axiom, &item_path)?;
        let key = axiom_reference_sort_key(axiom);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                item_path,
                "axiom",
                PackageArtifactErrorReason::DuplicateAxiom,
                key,
            ));
        }
    }
    Ok(())
}

fn validate_policy_status(
    status: &PackageAxiomPolicyStatus,
    path: &str,
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, violation) in status.violations.iter().enumerate() {
        let item_path = format!("{path}.violations[{index}]");
        validate_axiom_reference(&violation.axiom, &format!("{item_path}.axiom"))?;
        let key = violation_sort_key(violation);
        if !keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                item_path,
                "violation",
                PackageArtifactErrorReason::DuplicateViolation,
                key,
            ));
        }
    }
    if status.status == PackageAxiomPolicyStatusKind::Ok && !status.violations.is_empty() {
        return Err(PackageArtifactError::summary_mismatch(
            field_path(path, "status"),
            "status",
            "violation when violations are present",
            status.status.as_str(),
        ));
    }
    if status.status == PackageAxiomPolicyStatusKind::Violation && status.violations.is_empty() {
        return Err(PackageArtifactError::summary_mismatch(
            field_path(path, "violations"),
            "violations",
            "at least one violation",
            "0",
        ));
    }
    Ok(())
}

fn validate_axiom_report_summary(report: &PackageAxiomReport) -> PackageArtifactResult<()> {
    let expected = expected_axiom_report_summary(&report.modules);
    check_summary_count(
        "summary.module_count",
        "module_count",
        expected.module_count,
        report.summary.module_count,
    )?;
    check_summary_count(
        "summary.local_module_count",
        "local_module_count",
        expected.local_module_count,
        report.summary.local_module_count,
    )?;
    check_summary_count(
        "summary.external_module_count",
        "external_module_count",
        expected.external_module_count,
        report.summary.external_module_count,
    )?;
    check_summary_count(
        "summary.direct_axiom_count",
        "direct_axiom_count",
        expected.direct_axiom_count,
        report.summary.direct_axiom_count,
    )?;
    check_summary_count(
        "summary.transitive_axiom_count",
        "transitive_axiom_count",
        expected.transitive_axiom_count,
        report.summary.transitive_axiom_count,
    )?;
    check_summary_count(
        "summary.policy_violation_count",
        "policy_violation_count",
        expected.policy_violation_count,
        report.summary.policy_violation_count,
    )
}

fn expected_axiom_report_summary(
    modules: &[PackageAxiomReportModule],
) -> PackageAxiomReportSummary {
    let mut direct_axioms = BTreeSet::<String>::new();
    let mut transitive_axioms = BTreeSet::<String>::new();
    let mut local_module_count = 0_u64;
    let mut external_module_count = 0_u64;
    let mut policy_violation_count = 0_u64;

    for module in modules {
        match module.origin {
            PackageArtifactOrigin::Local => local_module_count += 1,
            PackageArtifactOrigin::External => external_module_count += 1,
        }
        direct_axioms.extend(module.direct_axioms.iter().map(axiom_reference_sort_key));
        transitive_axioms.extend(
            module
                .transitive_axioms
                .iter()
                .map(axiom_reference_sort_key),
        );
        policy_violation_count += module.policy_status.violations.len() as u64;
    }

    PackageAxiomReportSummary {
        module_count: modules.len() as u64,
        local_module_count,
        external_module_count,
        direct_axiom_count: direct_axioms.len() as u64,
        transitive_axiom_count: transitive_axioms.len() as u64,
        policy_violation_count,
    }
}

fn axiom_report_changed_modules(
    report: &PackageAxiomReport,
    current_lock: &PackageLockManifest,
    full_reasons: &mut Vec<String>,
) -> BTreeMap<Name, BTreeSet<String>> {
    let previous = report
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
            entry.certificate_file_hash != previous.certificate_file_hash,
            "certificate_file_hash_changed",
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

fn normalize_axiom_report(report: &mut PackageAxiomReport) {
    normalize_policy(&mut report.policy);
    report.modules.sort_by_key(|module| module.module.clone());
    for module in &mut report.modules {
        module.direct_axioms.sort_by_key(axiom_reference_sort_key);
        module
            .transitive_axioms
            .sort_by_key(axiom_reference_sort_key);
        module
            .policy_status
            .violations
            .sort_by_key(violation_sort_key);
    }
    normalize_checker_summaries(&mut report.checker_summaries);
}

fn parse_axiom_report_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAxiomReport> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, TOP_LEVEL_FIELDS)?;
    Ok(PackageAxiomReport {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        manifest: parse_file_reference(required_value(members, "$", "manifest")?, "manifest")?,
        package_lock: parse_file_reference(
            required_value(members, "$", "package_lock")?,
            "package_lock",
        )?,
        policy: parse_policy(required_value(members, "$", "policy")?)?,
        modules: required_array(members, "$", "modules")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_axiom_report_module(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_summaries: required_array(members, "$", "checker_summaries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_checker_summary(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        summary: parse_summary(required_value(members, "$", "summary")?)?,
        package_axiom_report_hash: required_hash(members, "$", "package_axiom_report_hash")?,
    })
}

fn required_value<'a>(
    members: &'a [crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<&'a crate::json::JsonValue> {
    crate::artifacts::required_value(members, path, field)
}

fn parse_axiom_report_module(
    index: usize,
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAxiomReportModule> {
    let path = format!("modules[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, MODULE_FIELDS)?;
    let origin_path = field_path(&path, "origin");
    Ok(PackageAxiomReportModule {
        module: required_name(members, &path, "module")?,
        origin: PackageArtifactOrigin::parse(
            &required_string(members, &path, "origin")?,
            &origin_path,
        )?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, &path, "axiom_report_hash")?,
        certificate_file_hash: required_hash(members, &path, "certificate_file_hash")?,
        direct_axioms: required_array(members, &path, "direct_axioms")?
            .iter()
            .enumerate()
            .map(|(axiom_index, value)| {
                parse_axiom_reference(value, &format!("{path}.direct_axioms[{axiom_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        transitive_axioms: required_array(members, &path, "transitive_axioms")?
            .iter()
            .enumerate()
            .map(|(axiom_index, value)| {
                parse_axiom_reference(value, &format!("{path}.transitive_axioms[{axiom_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        policy_status: parse_policy_status(
            required_value(members, &path, "policy_status")?,
            &format!("{path}.policy_status"),
        )?,
    })
}

fn parse_policy_status(
    value: &crate::json::JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageAxiomPolicyStatus> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, POLICY_STATUS_FIELDS)?;
    let status_path = field_path(path, "status");
    Ok(PackageAxiomPolicyStatus {
        status: PackageAxiomPolicyStatusKind::parse(
            &required_string(members, path, "status")?,
            &status_path,
        )?,
        violations: required_array(members, path, "violations")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_policy_violation(value, &format!("{path}.violations[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_policy_violation(
    value: &crate::json::JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageAxiomPolicyViolation> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, POLICY_VIOLATION_FIELDS)?;
    let reason_path = field_path(path, "reason_code");
    Ok(PackageAxiomPolicyViolation {
        axiom: parse_axiom_reference(
            required_value(members, path, "axiom")?,
            &field_path(path, "axiom"),
        )?,
        reason_code: PackageAxiomPolicyViolationReason::parse(
            &required_string(members, path, "reason_code")?,
            &reason_path,
        )?,
    })
}

fn parse_summary(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageAxiomReportSummary> {
    let path = "summary";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SUMMARY_FIELDS)?;
    Ok(PackageAxiomReportSummary {
        module_count: required_u64(members, path, "module_count")?,
        local_module_count: required_u64(members, path, "local_module_count")?,
        external_module_count: required_u64(members, path, "external_module_count")?,
        direct_axiom_count: required_u64(members, path, "direct_axiom_count")?,
        transitive_axiom_count: required_u64(members, path, "transitive_axiom_count")?,
        policy_violation_count: required_u64(members, path, "policy_violation_count")?,
    })
}

fn axiom_report_json_unchecked(report: &PackageAxiomReport, include_self_hash: bool) -> String {
    let mut fields = vec![
        ("schema", json_string(&report.schema)),
        ("package", json_string(report.package.as_str())),
        ("version", json_string(report.version.as_str())),
        ("manifest", file_reference_json(&report.manifest)),
        ("package_lock", file_reference_json(&report.package_lock)),
        ("policy", crate::artifacts::policy_json(&report.policy)),
        (
            "modules",
            json_array(report.modules.iter().map(module_json).collect()),
        ),
        (
            "checker_summaries",
            json_array(
                report
                    .checker_summaries
                    .iter()
                    .map(checker_summary_json)
                    .collect(),
            ),
        ),
        ("summary", summary_json(&report.summary)),
    ];
    if include_self_hash {
        fields.push((
            "package_axiom_report_hash",
            hash_json(report.package_axiom_report_hash),
        ));
    }
    json_object_in_order(fields)
}

fn module_json(module: &PackageAxiomReportModule) -> String {
    json_object_in_order(vec![
        ("module", json_string(&module.module.as_dotted())),
        ("origin", json_string(module.origin.as_str())),
        ("export_hash", hash_json(module.export_hash)),
        ("certificate_hash", hash_json(module.certificate_hash)),
        ("axiom_report_hash", hash_json(module.axiom_report_hash)),
        (
            "certificate_file_hash",
            hash_json(module.certificate_file_hash),
        ),
        (
            "direct_axioms",
            json_array(
                module
                    .direct_axioms
                    .iter()
                    .map(axiom_reference_json)
                    .collect(),
            ),
        ),
        (
            "transitive_axioms",
            json_array(
                module
                    .transitive_axioms
                    .iter()
                    .map(axiom_reference_json)
                    .collect(),
            ),
        ),
        ("policy_status", policy_status_json(&module.policy_status)),
    ])
}

fn policy_status_json(status: &PackageAxiomPolicyStatus) -> String {
    json_object_in_order(vec![
        ("status", json_string(status.status.as_str())),
        (
            "violations",
            json_array(
                status
                    .violations
                    .iter()
                    .map(policy_violation_json)
                    .collect(),
            ),
        ),
    ])
}

fn policy_violation_json(violation: &PackageAxiomPolicyViolation) -> String {
    json_object_in_order(vec![
        ("axiom", axiom_reference_json(&violation.axiom)),
        ("reason_code", json_string(violation.reason_code.as_str())),
    ])
}

fn summary_json(summary: &PackageAxiomReportSummary) -> String {
    json_object_in_order(vec![
        ("module_count", json_u64(summary.module_count)),
        ("local_module_count", json_u64(summary.local_module_count)),
        (
            "external_module_count",
            json_u64(summary.external_module_count),
        ),
        ("direct_axiom_count", json_u64(summary.direct_axiom_count)),
        (
            "transitive_axiom_count",
            json_u64(summary.transitive_axiom_count),
        ),
        (
            "policy_violation_count",
            json_u64(summary.policy_violation_count),
        ),
    ])
}

fn violation_sort_key(violation: &PackageAxiomPolicyViolation) -> String {
    format!(
        "{}\u{001f}{}",
        axiom_reference_sort_key(&violation.axiom),
        violation.reason_code.as_str()
    )
}

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "manifest",
    "package_lock",
    "policy",
    "modules",
    "checker_summaries",
    "summary",
    "package_axiom_report_hash",
];
const MODULE_FIELDS: &[&str] = &[
    "module",
    "origin",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
    "certificate_file_hash",
    "direct_axioms",
    "transitive_axioms",
    "policy_status",
];
const POLICY_STATUS_FIELDS: &[&str] = &["status", "violations"];
const POLICY_VIOLATION_FIELDS: &[&str] = &["axiom", "reason_code"];
const SUMMARY_FIELDS: &[&str] = &[
    "module_count",
    "local_module_count",
    "external_module_count",
    "direct_axiom_count",
    "transitive_axiom_count",
    "policy_violation_count",
];

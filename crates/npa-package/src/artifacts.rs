//! Shared generated package artifact data types and canonical JSON helpers.
//!
//! CLR-05 package artifacts are untrusted generated metadata. They summarize
//! package/certificate identities for review, CI, search, and later publish
//! metadata, but they are never proof evidence and never become checker input.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, parse_package_hash, PackageHash},
    json::{parse_json, JsonMember, JsonValue},
    manifest::PackageVersion,
    name::{validate_package_id, PackageId},
    path::{validate_package_path, PackagePath},
    validate::validate_package_version,
};

/// Package-relative file identity recorded in generated package artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactFileReference {
    /// Package-relative artifact path.
    pub path: PackagePath,
    /// Exact SHA-256 hash of the referenced file bytes.
    pub file_hash: PackageHash,
}

/// Local or external package artifact origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageArtifactOrigin {
    /// Artifact entry belongs to the local package.
    Local,
    /// Artifact entry comes from a hash-pinned external package import.
    External,
}

impl PackageArtifactOrigin {
    /// Return the generated artifact origin string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::External => "external",
        }
    }

    pub(crate) fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "local" => Ok(Self::Local),
            "external" => Ok(Self::External),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "origin",
                "local or external",
                value,
            )),
        }
    }
}

/// Canonical certificate-derived axiom reference used by package artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAxiomReference {
    /// Module exporting the axiom.
    pub module: Name,
    /// Axiom declaration name.
    pub name: Name,
    /// Export hash of the module that provides this axiom.
    pub export_hash: PackageHash,
    /// Declaration interface hash of the axiom.
    pub decl_interface_hash: PackageHash,
}

/// Checker mode recorded in generated package checker summaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageCheckerMode {
    /// Fast in-process kernel verifier mode.
    Fast,
    /// Independent reference checker mode.
    Reference,
}

impl PackageCheckerMode {
    /// Return the generated artifact checker mode string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Fast => "fast",
            Self::Reference => "reference",
        }
    }

    pub(crate) fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "fast" => Ok(Self::Fast),
            "reference" => Ok(Self::Reference),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "mode",
                "fast or reference",
                value,
            )),
        }
    }
}

/// Source-free checker summary attached to generated package artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageCheckerSummary {
    /// Verified module name.
    pub module: Name,
    /// Checker identifier, for example `npa-kernel` or `npa-checker-ref`.
    pub checker: String,
    /// Checker profile string.
    pub profile: String,
    /// Checker mode.
    pub mode: PackageCheckerMode,
    /// Deterministic checker status label.
    pub status: String,
    /// Verified module export hash.
    pub export_hash: PackageHash,
    /// Verified module certificate hash.
    pub certificate_hash: PackageHash,
    /// Verified module axiom report hash.
    pub axiom_report_hash: PackageHash,
}

/// Release evidence mode recorded for verified artifact identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageReleaseEvidenceKind {
    /// Release evidence came from the normal source-free reference checker.
    ReferenceCheckerOnly,
    /// Release evidence came from the opt-in high-trust package gate.
    HighTrust,
}

impl PackageReleaseEvidenceKind {
    /// Return the generated artifact release-evidence string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReferenceCheckerOnly => "reference_checker_only",
            Self::HighTrust => "high_trust",
        }
    }

    /// Parse a generated artifact release-evidence string.
    pub fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "reference_checker_only" => Ok(Self::ReferenceCheckerOnly),
            "high_trust" => Ok(Self::HighTrust),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "release_evidence_kind",
                "reference_checker_only or high_trust",
                value,
            )),
        }
    }
}

/// Verifier identity captured by package/release evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageReleaseVerifierIdentity {
    /// Checker profile, for example `reference` or `external`.
    pub profile: String,
    /// Exact checker binary hash.
    pub binary_hash: PackageHash,
    /// Exact checker version or build hash.
    pub version_or_build_hash: PackageHash,
}

/// Certificate-bound release identity for a verified artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageReleaseIdentity {
    /// Exact canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Exact verified export hash.
    pub export_hash: PackageHash,
    /// Exact axiom-report hash.
    pub axiom_report_hash: PackageHash,
    /// Optional package manifest hash.
    pub package_manifest_hash: Option<PackageHash>,
    /// Optional package lock hash.
    pub package_lock_hash: Option<PackageHash>,
    /// Verifier identity that produced the release evidence.
    pub verifier: PackageReleaseVerifierIdentity,
    /// Evidence mode, distinguishing reference-only from opt-in high-trust.
    pub evidence_kind: PackageReleaseEvidenceKind,
    /// Exact hash of the release evidence artifact.
    pub evidence_hash: PackageHash,
}

impl PackageReleaseIdentity {
    /// Validate the release identity shape without reading files or running checkers.
    pub fn validate(&self) -> PackageArtifactResult<()> {
        if self.package_manifest_hash.is_none() && self.package_lock_hash.is_none() {
            return Err(PackageArtifactError::missing_field(
                "$",
                "package_manifest_hash_or_package_lock_hash",
            ));
        }
        validate_plain_string(&self.verifier.profile, "verifier.profile")
    }
}

/// Package-level policy copied into an axiom report artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactPolicy {
    /// Whether axioms outside [`Self::allowed_axioms`] may appear.
    pub allow_custom_axioms: bool,
    /// Exact axiom names permitted by package policy.
    pub allowed_axioms: Vec<Name>,
}

/// Full theorem index global reference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageGlobalRef {
    /// Module exporting the declaration.
    pub module: Name,
    /// Declaration name.
    pub name: Name,
    /// Export hash of the containing module.
    pub export_hash: PackageHash,
    /// Certificate hash of the containing module.
    pub certificate_hash: PackageHash,
    /// Declaration interface hash.
    pub decl_interface_hash: PackageHash,
}

/// Statement global reference view used in theorem-index statement projections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageGlobalRefView {
    /// Module exporting the declaration.
    pub module: Name,
    /// Declaration name.
    pub name: Name,
    /// Export hash of the containing module.
    pub export_hash: PackageHash,
    /// Declaration interface hash.
    pub decl_interface_hash: PackageHash,
}

pub(crate) fn parse_artifact_json(source: &str) -> PackageArtifactResult<JsonValue> {
    parse_json(source).map_err(|error| PackageArtifactError::invalid_json(error.to_string()))
}

pub(crate) fn validate_package_identity(
    package: &PackageId,
    version: &PackageVersion,
) -> PackageArtifactResult<()> {
    validate_package_id(package, "package")
        .map_err(|_| PackageArtifactError::invalid_package_id("package", package.as_str()))?;
    validate_package_version(version, "version")
        .map_err(|_| PackageArtifactError::invalid_version("version", version.as_str()))?;
    Ok(())
}

pub(crate) fn validate_artifact_file_reference(
    reference: &PackageArtifactFileReference,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_artifact_path(&reference.path, field_path(path, "path"))
}

pub(crate) fn validate_artifact_path(
    value: &PackagePath,
    path: impl Into<String>,
) -> PackageArtifactResult<()> {
    let path = path.into();
    validate_package_path(value, &path)
        .map_err(|_| PackageArtifactError::invalid_path(path, value.as_str()))
}

pub(crate) fn validate_module_name(
    name: &Name,
    path: impl Into<String>,
) -> PackageArtifactResult<()> {
    let path = path.into();
    if name.is_canonical() {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_module_name(
            path,
            name.as_dotted(),
        ))
    }
}

pub(crate) fn validate_declaration_name(
    name: &Name,
    path: impl Into<String>,
) -> PackageArtifactResult<()> {
    let path = path.into();
    if name.is_canonical() {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_declaration_name(
            path,
            name.as_dotted(),
        ))
    }
}

pub(crate) fn validate_policy(policy: &PackageArtifactPolicy) -> PackageArtifactResult<()> {
    let mut names = BTreeSet::<String>::new();
    for (index, name) in policy.allowed_axioms.iter().enumerate() {
        let path = format!("policy.allowed_axioms[{index}]");
        validate_declaration_name(name, &path)?;
        let dotted = name.as_dotted();
        if !names.insert(dotted.clone()) {
            return Err(PackageArtifactError::duplicate(
                path,
                "allowed_axioms",
                PackageArtifactErrorReason::DuplicateAxiom,
                dotted,
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_axiom_reference(
    axiom: &PackageAxiomReference,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_module_name(&axiom.module, field_path(path, "module"))?;
    validate_declaration_name(&axiom.name, field_path(path, "name"))?;
    Ok(())
}

pub(crate) fn validate_global_ref(
    global_ref: &PackageGlobalRef,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_module_name(&global_ref.module, field_path(path, "module"))?;
    validate_declaration_name(&global_ref.name, field_path(path, "name"))?;
    Ok(())
}

pub(crate) fn validate_global_ref_view(
    global_ref: &PackageGlobalRefView,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_module_name(&global_ref.module, field_path(path, "module"))?;
    validate_declaration_name(&global_ref.name, field_path(path, "name"))?;
    Ok(())
}

pub(crate) fn validate_checker_summaries(
    summaries: &[PackageCheckerSummary],
) -> PackageArtifactResult<()> {
    let mut keys = BTreeSet::<String>::new();
    for (index, summary) in summaries.iter().enumerate() {
        let path = format!("checker_summaries[{index}]");
        validate_module_name(&summary.module, field_path(&path, "module"))?;
        validate_plain_string(&summary.checker, field_path(&path, "checker"))?;
        validate_plain_string(&summary.profile, field_path(&path, "profile"))?;
        validate_plain_string(&summary.status, field_path(&path, "status"))?;
        let key = checker_summary_sort_key(summary);
        if !keys.insert(key.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "module"),
                "checker_summaries",
                PackageArtifactErrorReason::DuplicateCheckerSummary,
                key,
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_plain_string(
    value: &str,
    path: impl Into<String>,
) -> PackageArtifactResult<()> {
    if !value.is_empty() && !value.chars().any(char::is_control) {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            path,
            "string",
            "non-empty string without control characters",
            value,
        ))
    }
}

pub(crate) fn normalize_policy(policy: &mut PackageArtifactPolicy) {
    policy.allowed_axioms.sort();
}

pub(crate) fn normalize_checker_summaries(summaries: &mut [PackageCheckerSummary]) {
    summaries.sort_by_key(checker_summary_sort_key);
}

pub(crate) fn axiom_reference_sort_key(axiom: &PackageAxiomReference) -> String {
    axiom_reference_json(axiom)
}

pub(crate) fn global_ref_sort_key(global_ref: &PackageGlobalRef) -> String {
    global_ref_json(global_ref)
}

pub(crate) fn global_ref_view_sort_key(global_ref: &PackageGlobalRefView) -> String {
    global_ref_view_json(global_ref)
}

pub(crate) fn checker_summary_sort_key(summary: &PackageCheckerSummary) -> String {
    [
        summary.module.as_dotted(),
        summary.mode.as_str().to_owned(),
        summary.checker.clone(),
        summary.profile.clone(),
    ]
    .join("\u{001f}")
}

pub(crate) fn duplicate_key_error(
    path: impl Into<String>,
    field: impl Into<String>,
    reason: PackageArtifactErrorReason,
    actual: impl Into<String>,
) -> PackageArtifactError {
    PackageArtifactError::duplicate(path, field, reason, actual)
}

pub(crate) fn expect_object<'a>(
    value: &'a JsonValue,
    path: &str,
) -> PackageArtifactResult<&'a [JsonMember]> {
    value.object_members().ok_or_else(|| {
        PackageArtifactError::wrong_type(path, None, "object", value.kind().as_str())
    })
}

pub(crate) fn reject_unknown_fields(
    path: &str,
    members: &[JsonMember],
    allowed: &[&str],
) -> PackageArtifactResult<()> {
    let mut counts = BTreeMap::<&str, usize>::new();
    for member in members {
        *counts.entry(member.key()).or_insert(0) += 1;
    }

    if let Some((field, _)) = counts.iter().find(|(_, count)| **count > 1) {
        return Err(PackageArtifactError::duplicate_field(path, *field));
    }
    if let Some((field, _)) = counts
        .iter()
        .find(|(field, _)| !allowed.iter().any(|allowed| allowed == *field))
    {
        return Err(PackageArtifactError::unknown_field(path, *field));
    }
    Ok(())
}

pub(crate) fn required_value<'a>(
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

pub(crate) fn required_string(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<String> {
    let value = required_value(members, path, field)?;
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "string",
            value.kind().as_str(),
        )
    })
}

pub(crate) fn required_bool(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<bool> {
    let value = required_value(members, path, field)?;
    value.bool_value().ok_or_else(|| {
        PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "bool",
            value.kind().as_str(),
        )
    })
}

pub(crate) fn required_u64(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<u64> {
    let value = required_value(members, path, field)?;
    let Some(number) = value.number_value() else {
        return Err(PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "unsigned integer",
            value.kind().as_str(),
        ));
    };
    if number.starts_with('-')
        || number.contains('.')
        || number.contains('e')
        || number.contains('E')
        || (number.len() > 1 && number.starts_with('0'))
    {
        return Err(PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "unsigned integer",
            number,
        ));
    }
    number.parse::<u64>().map_err(|_| {
        PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "unsigned integer",
            number,
        )
    })
}

pub(crate) fn required_array<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<&'a [JsonValue]> {
    let value = required_value(members, path, field)?;
    value.array_elements().ok_or_else(|| {
        PackageArtifactError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "array",
            value.kind().as_str(),
        )
    })
}

pub(crate) fn required_hash(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<PackageHash> {
    let field_path = field_path(path, field);
    let value = required_string(members, path, field)?;
    parse_package_hash(&value, &field_path)
        .map_err(|_| PackageArtifactError::invalid_hash_format(field_path, value))
}

pub(crate) fn required_name(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Name> {
    Ok(Name::from_dotted(required_string(members, path, field)?))
}

pub(crate) fn required_path(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<PackagePath> {
    Ok(PackagePath::new(required_string(members, path, field)?))
}

pub(crate) fn parse_file_reference(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageArtifactFileReference> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, FILE_REFERENCE_FIELDS)?;
    Ok(PackageArtifactFileReference {
        path: required_path(members, path, "path")?,
        file_hash: required_hash(members, path, "file_hash")?,
    })
}

pub(crate) fn parse_policy(value: &JsonValue) -> PackageArtifactResult<PackageArtifactPolicy> {
    let path = "policy";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, POLICY_FIELDS)?;
    Ok(PackageArtifactPolicy {
        allow_custom_axioms: required_bool(members, path, "allow_custom_axioms")?,
        allowed_axioms: required_array(members, path, "allowed_axioms")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                value.string_value().map(Name::from_dotted).ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        format!("{path}.allowed_axioms[{index}]"),
                        Some("allowed_axioms".to_owned()),
                        "string",
                        value.kind().as_str(),
                    )
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

pub(crate) fn parse_axiom_reference(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageAxiomReference> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, AXIOM_REFERENCE_FIELDS)?;
    Ok(PackageAxiomReference {
        module: required_name(members, path, "module")?,
        name: required_name(members, path, "name")?,
        export_hash: required_hash(members, path, "export_hash")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
    })
}

pub(crate) fn parse_checker_summary(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<PackageCheckerSummary> {
    let path = format!("checker_summaries[{index}]");
    parse_checker_summary_at_path(value, &path)
}

pub(crate) fn parse_checker_summary_at_path(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageCheckerSummary> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CHECKER_SUMMARY_FIELDS)?;
    let mode_path = field_path(path, "mode");
    Ok(PackageCheckerSummary {
        module: required_name(members, path, "module")?,
        checker: required_string(members, path, "checker")?,
        profile: required_string(members, path, "profile")?,
        mode: PackageCheckerMode::parse(&required_string(members, path, "mode")?, &mode_path)?,
        status: required_string(members, path, "status")?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
    })
}

pub(crate) fn parse_global_ref(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageGlobalRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GLOBAL_REF_FIELDS)?;
    Ok(PackageGlobalRef {
        module: required_name(members, path, "module")?,
        name: required_name(members, path, "name")?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
    })
}

pub(crate) fn parse_global_ref_view(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageGlobalRefView> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GLOBAL_REF_VIEW_FIELDS)?;
    Ok(PackageGlobalRefView {
        module: required_name(members, path, "module")?,
        name: required_name(members, path, "name")?,
        export_hash: required_hash(members, path, "export_hash")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
    })
}

pub(crate) fn json_object_in_order(fields: Vec<(&str, String)>) -> String {
    let mut out = String::new();
    out.push('{');
    for (index, (key, value)) in fields.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(key));
        out.push(':');
        out.push_str(value);
    }
    out.push('}');
    out
}

pub(crate) fn json_array(values: Vec<String>) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(value);
    }
    out.push(']');
    out
}

pub(crate) fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str("\\u00");
                out.push(hex_digit((ch as u8) >> 4));
                out.push(hex_digit((ch as u8) & 0x0f));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

pub(crate) fn json_bool(value: bool) -> String {
    if value {
        "true".to_owned()
    } else {
        "false".to_owned()
    }
}

pub(crate) fn json_u64(value: u64) -> String {
    value.to_string()
}

pub(crate) fn hash_json(hash: PackageHash) -> String {
    json_string(&format_package_hash(&hash))
}

pub(crate) fn file_reference_json(reference: &PackageArtifactFileReference) -> String {
    json_object_in_order(vec![
        ("path", json_string(reference.path.as_str())),
        ("file_hash", hash_json(reference.file_hash)),
    ])
}

pub(crate) fn policy_json(policy: &PackageArtifactPolicy) -> String {
    json_object_in_order(vec![
        ("allow_custom_axioms", json_bool(policy.allow_custom_axioms)),
        (
            "allowed_axioms",
            json_array(
                policy
                    .allowed_axioms
                    .iter()
                    .map(|name| json_string(&name.as_dotted()))
                    .collect(),
            ),
        ),
    ])
}

pub(crate) fn axiom_reference_json(axiom: &PackageAxiomReference) -> String {
    json_object_in_order(vec![
        ("module", json_string(&axiom.module.as_dotted())),
        ("name", json_string(&axiom.name.as_dotted())),
        ("export_hash", hash_json(axiom.export_hash)),
        ("decl_interface_hash", hash_json(axiom.decl_interface_hash)),
    ])
}

pub(crate) fn checker_summary_json(summary: &PackageCheckerSummary) -> String {
    json_object_in_order(vec![
        ("module", json_string(&summary.module.as_dotted())),
        ("checker", json_string(&summary.checker)),
        ("profile", json_string(&summary.profile)),
        ("mode", json_string(summary.mode.as_str())),
        ("status", json_string(&summary.status)),
        ("export_hash", hash_json(summary.export_hash)),
        ("certificate_hash", hash_json(summary.certificate_hash)),
        ("axiom_report_hash", hash_json(summary.axiom_report_hash)),
    ])
}

pub(crate) fn global_ref_json(global_ref: &PackageGlobalRef) -> String {
    json_object_in_order(vec![
        ("module", json_string(&global_ref.module.as_dotted())),
        ("name", json_string(&global_ref.name.as_dotted())),
        ("export_hash", hash_json(global_ref.export_hash)),
        ("certificate_hash", hash_json(global_ref.certificate_hash)),
        (
            "decl_interface_hash",
            hash_json(global_ref.decl_interface_hash),
        ),
    ])
}

pub(crate) fn global_ref_view_json(global_ref: &PackageGlobalRefView) -> String {
    json_object_in_order(vec![
        ("module", json_string(&global_ref.module.as_dotted())),
        ("name", json_string(&global_ref.name.as_dotted())),
        ("export_hash", hash_json(global_ref.export_hash)),
        (
            "decl_interface_hash",
            hash_json(global_ref.decl_interface_hash),
        ),
    ])
}

pub(crate) fn field_path(path: &str, field: &str) -> String {
    if path == "$" {
        field.to_owned()
    } else {
        format!("{path}.{field}")
    }
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex digit out of range"),
    }
}

const FILE_REFERENCE_FIELDS: &[&str] = &["path", "file_hash"];
const POLICY_FIELDS: &[&str] = &["allow_custom_axioms", "allowed_axioms"];
const AXIOM_REFERENCE_FIELDS: &[&str] = &["module", "name", "export_hash", "decl_interface_hash"];
const CHECKER_SUMMARY_FIELDS: &[&str] = &[
    "module",
    "checker",
    "profile",
    "mode",
    "status",
    "export_hash",
    "certificate_hash",
    "axiom_report_hash",
];
const GLOBAL_REF_FIELDS: &[&str] = &[
    "module",
    "name",
    "export_hash",
    "certificate_hash",
    "decl_interface_hash",
];
const GLOBAL_REF_VIEW_FIELDS: &[&str] = &["module", "name", "export_hash", "decl_interface_hash"];

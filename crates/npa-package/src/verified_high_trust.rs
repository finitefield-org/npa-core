//! Package-level `verified_high_trust` release evidence model.
//!
//! The artifact records that package release/high-trust gates produced the
//! expected source-free checker and auxiliary evidence. It remains metadata:
//! downstream verification must still rerun from certificates and imports.

use std::collections::BTreeSet;

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_object_in_order, json_string,
        parse_artifact_json, reject_unknown_fields, required_array, required_hash, required_string,
        validate_package_identity, validate_plain_string, PackageReleaseEvidenceKind,
        PackageReleaseIdentity, PackageReleaseVerifierIdentity,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    manifest::PackageVersion,
    name::PackageId,
    schema::PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA,
};

/// Package-relative path owned by CLR-08 high-trust write mode.
pub const PACKAGE_VERIFIED_HIGH_TRUST_PATH: &str = "generated/verified-high-trust.json";

/// Required high-trust checker profiles in canonical artifact order.
pub const REQUIRED_HIGH_TRUST_CHECKER_PROFILES: &[&str] = &[
    "fast-kernel",
    "reference",
    "external",
    "high-trust-reference",
];

/// Generated `npa.package.verified_high_trust.v0.1` release evidence artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedHighTrust {
    /// Artifact schema string; must equal [`PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA`].
    pub schema: String,
    /// Package identity.
    pub package: PackageId,
    /// Exact package version.
    pub package_version: PackageVersion,
    /// Exact hash of `generated/package-lock.json` bytes.
    pub package_lock_hash: PackageHash,
    /// Content hash of the checked package axiom report.
    pub axiom_report_hash: PackageHash,
    /// Content hash of the checked package theorem index.
    pub theorem_index_hash: PackageHash,
    /// Optional content hash of the checked publish plan.
    pub publish_plan_hash: Option<PackageHash>,
    /// Phase 8 high-trust release policy hash.
    pub release_policy_hash: PackageHash,
    /// Phase 8 runner policy hash.
    pub runner_policy_hash: PackageHash,
    /// Phase 8 challenge runner policy hash.
    pub challenge_runner_policy_hash: PackageHash,
    /// Target normalized checker-result hash.
    pub normalized_result_hash: PackageHash,
    /// Release audit bundle manifest hash.
    pub release_audit_bundle_manifest_hash: PackageHash,
    /// Required checker profiles.
    pub required_checker_profiles: Vec<String>,
    /// Checker identities that produced the target normalized result.
    pub checker_identities: Vec<PackageVerifiedHighTrustCheckerIdentity>,
    /// Passed auxiliary evidence referenced by the release audit bundle.
    pub auxiliary_results: Vec<PackageVerifiedHighTrustAuxiliaryResult>,
    /// Generator identity for auditability.
    pub generated_by: PackageVerifiedHighTrustGeneratedBy,
    /// Self hash over canonical bytes excluding this field.
    pub artifact_hash: PackageHash,
}

impl PackageVerifiedHighTrust {
    /// Return this artifact with canonical ordering and computed self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_verified_high_trust(&mut self);
        self.artifact_hash = compute_package_verified_high_trust_hash(&self)?;
        Ok(self)
    }

    /// Serialize this artifact as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        let mut normalized = self.clone();
        normalize_verified_high_trust(&mut normalized);
        validate_package_verified_high_trust(&normalized)?;
        Ok(verified_high_trust_json_unchecked(&normalized, true))
    }

    /// Build the high-trust release identity for one certificate/export pair.
    pub fn release_identity_for_verifier(
        &self,
        certificate_hash: PackageHash,
        export_hash: PackageHash,
        verifier_profile: &str,
    ) -> PackageArtifactResult<PackageReleaseIdentity> {
        validate_package_verified_high_trust(self)?;
        let checker_identity = self
            .checker_identities
            .iter()
            .find(|identity| identity.profile == verifier_profile)
            .ok_or_else(|| {
                PackageArtifactError::missing_field("checker_identities", verifier_profile)
            })?;
        let identity = PackageReleaseIdentity {
            certificate_hash,
            export_hash,
            axiom_report_hash: self.axiom_report_hash,
            package_manifest_hash: None,
            package_lock_hash: Some(self.package_lock_hash),
            verifier: PackageReleaseVerifierIdentity {
                profile: checker_identity.profile.clone(),
                binary_hash: checker_identity.binary_hash,
                version_or_build_hash: checker_identity.build_hash,
            },
            evidence_kind: PackageReleaseEvidenceKind::HighTrust,
            evidence_hash: self.artifact_hash,
        };
        identity.validate()?;
        Ok(identity)
    }
}

/// One checker identity included in high-trust evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedHighTrustCheckerIdentity {
    /// Checker profile, for example `external`.
    pub profile: String,
    /// Checker implementation id.
    pub checker_id: String,
    /// Checker version, when the result exposed one.
    pub checker_version: Option<String>,
    /// Runner-owned checker binary id.
    pub binary_id: String,
    /// Exact checker binary hash.
    pub binary_hash: PackageHash,
    /// Exact checker build hash.
    pub build_hash: PackageHash,
    /// MachineCheckResult result hash.
    pub result_hash: PackageHash,
    /// Stable checker status, normally `checked`.
    pub status: String,
}

/// Auxiliary result kind recorded in high-trust evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageVerifiedHighTrustAuxiliaryKind {
    /// Package axiom policy auxiliary check.
    AxiomPolicy,
    /// Checker reproducibility auxiliary check.
    Reproducibility,
    /// Release audit bundle validation auxiliary check.
    AuditBundle,
    /// High-trust import certificate hash auxiliary check.
    ImportCertificateHash,
    /// Challenge coverage summary, when challenge inputs are configured.
    ChallengeCoverage,
}

impl PackageVerifiedHighTrustAuxiliaryKind {
    /// Return the stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AxiomPolicy => "axiom_policy",
            Self::Reproducibility => "reproducibility",
            Self::AuditBundle => "audit_bundle",
            Self::ImportCertificateHash => "import_certificate_hash",
            Self::ChallengeCoverage => "challenge_coverage",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "axiom_policy" => Ok(Self::AxiomPolicy),
            "reproducibility" => Ok(Self::Reproducibility),
            "audit_bundle" => Ok(Self::AuditBundle),
            "import_certificate_hash" => Ok(Self::ImportCertificateHash),
            "challenge_coverage" => Ok(Self::ChallengeCoverage),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "kind",
                "high-trust auxiliary kind",
                value,
            )),
        }
    }
}

/// One passed auxiliary result referenced by high-trust evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedHighTrustAuxiliaryResult {
    /// Auxiliary result kind.
    pub kind: PackageVerifiedHighTrustAuxiliaryKind,
    /// Stable auxiliary status. CLR-08 requires `passed`.
    pub status: String,
    /// Release or runner policy hash attached to the auxiliary result.
    pub policy_hash: PackageHash,
    /// Auxiliary result hash or summary hash.
    pub result_hash: PackageHash,
    /// Artifact hash covered by this auxiliary result.
    pub artifact_hash: PackageHash,
}

/// Generator identity recorded in high-trust evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageVerifiedHighTrustGeneratedBy {
    /// Generator command name.
    pub command: String,
    /// Generator implementation id.
    pub generator: String,
    /// Generator implementation version.
    pub version: String,
}

/// Parse and validate a checked-in `verified_high_trust` JSON artifact.
pub fn parse_package_verified_high_trust_json(
    source: &str,
) -> PackageArtifactResult<PackageVerifiedHighTrust> {
    let root = parse_artifact_json(source)?;
    let artifact = parse_verified_high_trust_value(&root)?;
    validate_package_verified_high_trust(&artifact)?;
    let canonical = artifact.canonical_json()?;
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package verified_high_trust JSON bytes",
        ));
    }
    Ok(artifact)
}

/// Validate a `verified_high_trust` model without reading files or running checkers.
pub fn validate_package_verified_high_trust(
    artifact: &PackageVerifiedHighTrust,
) -> PackageArtifactResult<()> {
    if artifact.schema != PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA,
            artifact.schema.clone(),
        ));
    }
    validate_package_identity(&artifact.package, &artifact.package_version)?;
    validate_required_checker_profiles(&artifact.required_checker_profiles)?;
    validate_checker_identities(
        &artifact.required_checker_profiles,
        &artifact.checker_identities,
    )?;
    validate_auxiliary_results(&artifact.auxiliary_results)?;
    validate_generated_by(&artifact.generated_by)?;

    let expected_hash = compute_package_verified_high_trust_hash(artifact)?;
    if expected_hash != artifact.artifact_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "artifact_hash",
            "artifact_hash",
            format_package_hash(&expected_hash),
            format_package_hash(&artifact.artifact_hash),
        ));
    }
    Ok(())
}

/// Compute the artifact self hash over canonical bytes excluding `artifact_hash`.
pub fn compute_package_verified_high_trust_hash(
    artifact: &PackageVerifiedHighTrust,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = artifact.clone();
    normalize_verified_high_trust(&mut normalized);
    validate_verified_high_trust_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        verified_high_trust_json_unchecked(&normalized, false).as_bytes(),
    ))
}

fn validate_verified_high_trust_shape_without_self_hash(
    artifact: &PackageVerifiedHighTrust,
) -> PackageArtifactResult<()> {
    if artifact.schema != PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA,
            artifact.schema.clone(),
        ));
    }
    validate_package_identity(&artifact.package, &artifact.package_version)?;
    validate_required_checker_profiles(&artifact.required_checker_profiles)?;
    validate_checker_identities(
        &artifact.required_checker_profiles,
        &artifact.checker_identities,
    )?;
    validate_auxiliary_results(&artifact.auxiliary_results)?;
    validate_generated_by(&artifact.generated_by)
}

fn validate_required_checker_profiles(profiles: &[String]) -> PackageArtifactResult<()> {
    let expected = REQUIRED_HIGH_TRUST_CHECKER_PROFILES
        .iter()
        .copied()
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    if profiles != expected {
        return Err(PackageArtifactError::invalid_enum_value(
            "required_checker_profiles",
            "required_checker_profiles",
            expected.join(","),
            profiles.join(","),
        ));
    }
    Ok(())
}

fn validate_checker_identities(
    required_profiles: &[String],
    identities: &[PackageVerifiedHighTrustCheckerIdentity],
) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::<String>::new();
    for (index, identity) in identities.iter().enumerate() {
        let path = format!("checker_identities[{index}]");
        if !required_profiles.contains(&identity.profile) {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "profile"),
                "profile",
                "required_checker_profile",
                &identity.profile,
            ));
        }
        validate_plain_string(&identity.checker_id, field_path(&path, "checker_id"))?;
        if let Some(version) = &identity.checker_version {
            validate_plain_string(version, field_path(&path, "checker_version"))?;
        }
        validate_plain_string(&identity.binary_id, field_path(&path, "binary_id"))?;
        validate_plain_string(&identity.status, field_path(&path, "status"))?;
        if identity.status != "checked" {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "status"),
                "status",
                "checked",
                &identity.status,
            ));
        }
        if !seen.insert(identity.profile.clone()) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "profile"),
                "profile",
                PackageArtifactErrorReason::DuplicateArtifact,
                &identity.profile,
            ));
        }
    }
    for profile in required_profiles {
        if !seen.contains(profile) {
            return Err(PackageArtifactError::missing_field(
                "checker_identities",
                profile,
            ));
        }
    }
    Ok(())
}

fn validate_auxiliary_results(
    results: &[PackageVerifiedHighTrustAuxiliaryResult],
) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::<PackageVerifiedHighTrustAuxiliaryKind>::new();
    for (index, result) in results.iter().enumerate() {
        let path = format!("auxiliary_results[{index}]");
        if result.status != "passed" {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "status"),
                "status",
                "passed",
                &result.status,
            ));
        }
        if !seen.insert(result.kind) {
            return Err(PackageArtifactError::duplicate(
                field_path(&path, "kind"),
                "kind",
                PackageArtifactErrorReason::DuplicateArtifact,
                result.kind.as_str(),
            ));
        }
    }
    for required in [
        PackageVerifiedHighTrustAuxiliaryKind::AxiomPolicy,
        PackageVerifiedHighTrustAuxiliaryKind::Reproducibility,
        PackageVerifiedHighTrustAuxiliaryKind::AuditBundle,
        PackageVerifiedHighTrustAuxiliaryKind::ImportCertificateHash,
    ] {
        if !seen.contains(&required) {
            return Err(PackageArtifactError::missing_field(
                "auxiliary_results",
                required.as_str(),
            ));
        }
    }
    Ok(())
}

fn validate_generated_by(
    generated_by: &PackageVerifiedHighTrustGeneratedBy,
) -> PackageArtifactResult<()> {
    validate_plain_string(&generated_by.command, "generated_by.command")?;
    validate_plain_string(&generated_by.generator, "generated_by.generator")?;
    validate_plain_string(&generated_by.version, "generated_by.version")
}

fn parse_verified_high_trust_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageVerifiedHighTrust> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, VERIFIED_HIGH_TRUST_FIELDS)?;
    Ok(PackageVerifiedHighTrust {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        package_version: PackageVersion::new(required_string(members, "$", "package_version")?),
        package_lock_hash: required_hash(members, "$", "package_lock_hash")?,
        axiom_report_hash: required_hash(members, "$", "axiom_report_hash")?,
        theorem_index_hash: required_hash(members, "$", "theorem_index_hash")?,
        publish_plan_hash: optional_hash(members, "$", "publish_plan_hash")?,
        release_policy_hash: required_hash(members, "$", "release_policy_hash")?,
        runner_policy_hash: required_hash(members, "$", "runner_policy_hash")?,
        challenge_runner_policy_hash: required_hash(members, "$", "challenge_runner_policy_hash")?,
        normalized_result_hash: required_hash(members, "$", "normalized_result_hash")?,
        release_audit_bundle_manifest_hash: required_hash(
            members,
            "$",
            "release_audit_bundle_manifest_hash",
        )?,
        required_checker_profiles: required_array(members, "$", "required_checker_profiles")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                    PackageArtifactError::wrong_type(
                        format!("required_checker_profiles[{index}]"),
                        Some("required_checker_profiles".to_owned()),
                        "string",
                        value.kind().as_str(),
                    )
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_identities: parse_checker_identities(members)?,
        auxiliary_results: parse_auxiliary_results(members)?,
        generated_by: parse_generated_by(members)?,
        artifact_hash: required_hash(members, "$", "artifact_hash")?,
    })
}

fn parse_checker_identities(
    members: &[crate::json::JsonMember],
) -> PackageArtifactResult<Vec<PackageVerifiedHighTrustCheckerIdentity>> {
    required_array(members, "$", "checker_identities")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("checker_identities[{index}]");
            let members = expect_object(value, &path)?;
            reject_unknown_fields(&path, members, CHECKER_IDENTITY_FIELDS)?;
            Ok(PackageVerifiedHighTrustCheckerIdentity {
                profile: required_string(members, &path, "profile")?,
                checker_id: required_string(members, &path, "checker_id")?,
                checker_version: optional_string(members, &path, "checker_version")?,
                binary_id: required_string(members, &path, "binary_id")?,
                binary_hash: required_hash(members, &path, "binary_hash")?,
                build_hash: required_hash(members, &path, "build_hash")?,
                result_hash: required_hash(members, &path, "result_hash")?,
                status: required_string(members, &path, "status")?,
            })
        })
        .collect()
}

fn parse_auxiliary_results(
    members: &[crate::json::JsonMember],
) -> PackageArtifactResult<Vec<PackageVerifiedHighTrustAuxiliaryResult>> {
    required_array(members, "$", "auxiliary_results")?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("auxiliary_results[{index}]");
            let members = expect_object(value, &path)?;
            reject_unknown_fields(&path, members, AUXILIARY_RESULT_FIELDS)?;
            let kind = PackageVerifiedHighTrustAuxiliaryKind::parse(
                &required_string(members, &path, "kind")?,
                &field_path(&path, "kind"),
            )?;
            Ok(PackageVerifiedHighTrustAuxiliaryResult {
                kind,
                status: required_string(members, &path, "status")?,
                policy_hash: required_hash(members, &path, "policy_hash")?,
                result_hash: required_hash(members, &path, "result_hash")?,
                artifact_hash: required_hash(members, &path, "artifact_hash")?,
            })
        })
        .collect()
}

fn parse_generated_by(
    members: &[crate::json::JsonMember],
) -> PackageArtifactResult<PackageVerifiedHighTrustGeneratedBy> {
    let value = crate::artifacts::required_value(members, "$", "generated_by")?;
    let path = "generated_by";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GENERATED_BY_FIELDS)?;
    Ok(PackageVerifiedHighTrustGeneratedBy {
        command: required_string(members, path, "command")?,
        generator: required_string(members, path, "generator")?,
        version: required_string(members, path, "version")?,
    })
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

fn normalize_verified_high_trust(artifact: &mut PackageVerifiedHighTrust) {
    artifact.required_checker_profiles = REQUIRED_HIGH_TRUST_CHECKER_PROFILES
        .iter()
        .copied()
        .map(ToOwned::to_owned)
        .collect();
    artifact
        .checker_identities
        .sort_by_key(|identity| checker_identity_sort_key(&identity.profile));
    artifact
        .auxiliary_results
        .sort_by_key(|result| result.kind.as_str());
}

fn checker_identity_sort_key(profile: &str) -> usize {
    REQUIRED_HIGH_TRUST_CHECKER_PROFILES
        .iter()
        .position(|required| *required == profile)
        .unwrap_or(usize::MAX)
}

fn verified_high_trust_json_unchecked(
    artifact: &PackageVerifiedHighTrust,
    include_self_hash: bool,
) -> String {
    let mut fields = vec![
        ("schema", json_string(&artifact.schema)),
        ("package", json_string(artifact.package.as_str())),
        (
            "package_version",
            json_string(artifact.package_version.as_str()),
        ),
        ("package_lock_hash", hash_json(artifact.package_lock_hash)),
        ("axiom_report_hash", hash_json(artifact.axiom_report_hash)),
        ("theorem_index_hash", hash_json(artifact.theorem_index_hash)),
    ];
    if let Some(hash) = artifact.publish_plan_hash {
        fields.push(("publish_plan_hash", hash_json(hash)));
    }
    fields.extend([
        (
            "release_policy_hash",
            hash_json(artifact.release_policy_hash),
        ),
        ("runner_policy_hash", hash_json(artifact.runner_policy_hash)),
        (
            "challenge_runner_policy_hash",
            hash_json(artifact.challenge_runner_policy_hash),
        ),
        (
            "normalized_result_hash",
            hash_json(artifact.normalized_result_hash),
        ),
        (
            "release_audit_bundle_manifest_hash",
            hash_json(artifact.release_audit_bundle_manifest_hash),
        ),
        (
            "required_checker_profiles",
            json_array(
                artifact
                    .required_checker_profiles
                    .iter()
                    .map(|profile| json_string(profile))
                    .collect(),
            ),
        ),
        (
            "checker_identities",
            json_array(
                artifact
                    .checker_identities
                    .iter()
                    .map(checker_identity_json)
                    .collect(),
            ),
        ),
        (
            "auxiliary_results",
            json_array(
                artifact
                    .auxiliary_results
                    .iter()
                    .map(auxiliary_result_json)
                    .collect(),
            ),
        ),
        ("generated_by", generated_by_json(&artifact.generated_by)),
    ]);
    if include_self_hash {
        fields.push(("artifact_hash", hash_json(artifact.artifact_hash)));
    }
    json_object_in_order(fields)
}

fn checker_identity_json(identity: &PackageVerifiedHighTrustCheckerIdentity) -> String {
    let mut fields = vec![
        ("profile", json_string(&identity.profile)),
        ("checker_id", json_string(&identity.checker_id)),
    ];
    if let Some(version) = &identity.checker_version {
        fields.push(("checker_version", json_string(version)));
    }
    fields.extend([
        ("binary_id", json_string(&identity.binary_id)),
        ("binary_hash", hash_json(identity.binary_hash)),
        ("build_hash", hash_json(identity.build_hash)),
        ("result_hash", hash_json(identity.result_hash)),
        ("status", json_string(&identity.status)),
    ]);
    json_object_in_order(fields)
}

fn auxiliary_result_json(result: &PackageVerifiedHighTrustAuxiliaryResult) -> String {
    json_object_in_order(vec![
        ("kind", json_string(result.kind.as_str())),
        ("status", json_string(&result.status)),
        ("policy_hash", hash_json(result.policy_hash)),
        ("result_hash", hash_json(result.result_hash)),
        ("artifact_hash", hash_json(result.artifact_hash)),
    ])
}

fn generated_by_json(generated_by: &PackageVerifiedHighTrustGeneratedBy) -> String {
    json_object_in_order(vec![
        ("command", json_string(&generated_by.command)),
        ("generator", json_string(&generated_by.generator)),
        ("version", json_string(&generated_by.version)),
    ])
}

const VERIFIED_HIGH_TRUST_FIELDS: &[&str] = &[
    "schema",
    "package",
    "package_version",
    "package_lock_hash",
    "axiom_report_hash",
    "theorem_index_hash",
    "publish_plan_hash",
    "release_policy_hash",
    "runner_policy_hash",
    "challenge_runner_policy_hash",
    "normalized_result_hash",
    "release_audit_bundle_manifest_hash",
    "required_checker_profiles",
    "checker_identities",
    "auxiliary_results",
    "generated_by",
    "artifact_hash",
];
const CHECKER_IDENTITY_FIELDS: &[&str] = &[
    "profile",
    "checker_id",
    "checker_version",
    "binary_id",
    "binary_hash",
    "build_hash",
    "result_hash",
    "status",
];
const AUXILIARY_RESULT_FIELDS: &[&str] = &[
    "kind",
    "status",
    "policy_hash",
    "result_hash",
    "artifact_hash",
];
const GENERATED_BY_FIELDS: &[&str] = &["command", "generator", "version"];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::PackageArtifactErrorReason;

    #[test]
    fn verified_high_trust_round_trips_canonical_json_and_hash() {
        let artifact = fixture_artifact().with_computed_hash().unwrap();
        let json = artifact.canonical_json().unwrap();
        let parsed = parse_package_verified_high_trust_json(&json).unwrap();

        assert_eq!(parsed, artifact);
        assert!(json.contains("\"schema\":\"npa.package.verified_high_trust.v0.1\""));
        assert!(json.contains("\"required_checker_profiles\":[\"fast-kernel\",\"reference\",\"external\",\"high-trust-reference\"]"));
    }

    #[test]
    fn verified_high_trust_records_release_gate_hashes_and_auxiliary_results() {
        let artifact = fixture_artifact().with_computed_hash().unwrap();
        let json = artifact.canonical_json().unwrap();

        assert_eq!(artifact.package_lock_hash, hash(1));
        assert_eq!(artifact.axiom_report_hash, hash(2));
        assert_eq!(artifact.theorem_index_hash, hash(3));
        assert_eq!(artifact.publish_plan_hash, Some(hash(4)));
        assert_eq!(artifact.release_policy_hash, hash(5));
        assert_eq!(artifact.runner_policy_hash, hash(6));
        assert_eq!(artifact.challenge_runner_policy_hash, hash(7));
        assert_eq!(artifact.normalized_result_hash, hash(8));
        assert_eq!(artifact.release_audit_bundle_manifest_hash, hash(9));
        assert_eq!(artifact.checker_identities.len(), 4);
        assert!(artifact
            .checker_identities
            .iter()
            .all(|identity| identity.status == "checked"));

        let auxiliary_kinds = artifact
            .auxiliary_results
            .iter()
            .map(|result| result.kind)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            auxiliary_kinds,
            BTreeSet::from([
                PackageVerifiedHighTrustAuxiliaryKind::AxiomPolicy,
                PackageVerifiedHighTrustAuxiliaryKind::Reproducibility,
                PackageVerifiedHighTrustAuxiliaryKind::AuditBundle,
                PackageVerifiedHighTrustAuxiliaryKind::ImportCertificateHash,
            ])
        );

        for field in [
            "package_lock_hash",
            "axiom_report_hash",
            "theorem_index_hash",
            "publish_plan_hash",
            "release_policy_hash",
            "runner_policy_hash",
            "challenge_runner_policy_hash",
            "normalized_result_hash",
            "release_audit_bundle_manifest_hash",
            "checker_identities",
            "auxiliary_results",
            "result_hash",
            "artifact_hash",
        ] {
            assert!(json.contains(field), "missing {field}");
        }
    }

    #[test]
    fn verified_high_trust_rejects_reference_only_checker_evidence() {
        let mut artifact = fixture_artifact().with_computed_hash().unwrap();
        artifact
            .checker_identities
            .retain(|identity| identity.profile == "reference");

        let error = validate_package_verified_high_trust(&artifact).unwrap_err();
        assert_eq!(error.reason_code, PackageArtifactErrorReason::MissingField);
        assert_eq!(error.path, "checker_identities");
        assert_eq!(error.field.as_deref(), Some("fast-kernel"));
    }

    #[test]
    fn verified_high_trust_rejects_failed_auxiliary_evidence() {
        let mut artifact = fixture_artifact().with_computed_hash().unwrap();
        artifact.auxiliary_results[0].status = "failed".to_owned();
        artifact.artifact_hash = hash(99);

        let error = validate_package_verified_high_trust(&artifact).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("status"));
    }

    #[test]
    fn verified_high_trust_release_identity_is_high_trust_and_certificate_bound() {
        let artifact = fixture_artifact().with_computed_hash().unwrap();
        let identity = artifact
            .release_identity_for_verifier(hash(90), hash(91), "external")
            .unwrap();

        identity.validate().unwrap();
        assert_eq!(identity.certificate_hash, hash(90));
        assert_eq!(identity.export_hash, hash(91));
        assert_eq!(identity.axiom_report_hash, artifact.axiom_report_hash);
        assert_eq!(identity.package_lock_hash, Some(artifact.package_lock_hash));
        assert_eq!(identity.verifier.profile, "external");
        assert_eq!(
            identity.evidence_kind,
            PackageReleaseEvidenceKind::HighTrust
        );
        assert_ne!(
            identity.evidence_kind,
            PackageReleaseEvidenceKind::ReferenceCheckerOnly
        );
        assert_eq!(identity.evidence_hash, artifact.artifact_hash);
    }

    #[test]
    fn verified_high_trust_release_identity_rejects_unknown_profile() {
        let artifact = fixture_artifact().with_computed_hash().unwrap();

        let error = artifact
            .release_identity_for_verifier(hash(90), hash(91), "missing-profile")
            .unwrap_err();
        assert_eq!(error.reason_code, PackageArtifactErrorReason::MissingField);
        assert_eq!(error.path, "checker_identities");
        assert_eq!(error.field.as_deref(), Some("missing-profile"));
    }

    fn fixture_artifact() -> PackageVerifiedHighTrust {
        PackageVerifiedHighTrust {
            schema: PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            package_version: PackageVersion::new("0.1.0"),
            package_lock_hash: hash(1),
            axiom_report_hash: hash(2),
            theorem_index_hash: hash(3),
            publish_plan_hash: Some(hash(4)),
            release_policy_hash: hash(5),
            runner_policy_hash: hash(6),
            challenge_runner_policy_hash: hash(7),
            normalized_result_hash: hash(8),
            release_audit_bundle_manifest_hash: hash(9),
            required_checker_profiles: vec![
                "reference".to_owned(),
                "external".to_owned(),
                "fast-kernel".to_owned(),
                "high-trust-reference".to_owned(),
            ],
            checker_identities: REQUIRED_HIGH_TRUST_CHECKER_PROFILES
                .iter()
                .enumerate()
                .map(|(index, profile)| PackageVerifiedHighTrustCheckerIdentity {
                    profile: (*profile).to_owned(),
                    checker_id: format!("checker-{profile}"),
                    checker_version: Some("0.1.0".to_owned()),
                    binary_id: format!("binary-{profile}"),
                    binary_hash: hash(10 + index as u8),
                    build_hash: hash(20 + index as u8),
                    result_hash: hash(30 + index as u8),
                    status: "checked".to_owned(),
                })
                .collect(),
            auxiliary_results: vec![
                PackageVerifiedHighTrustAuxiliaryResult {
                    kind: PackageVerifiedHighTrustAuxiliaryKind::Reproducibility,
                    status: "passed".to_owned(),
                    policy_hash: hash(5),
                    result_hash: hash(40),
                    artifact_hash: hash(41),
                },
                PackageVerifiedHighTrustAuxiliaryResult {
                    kind: PackageVerifiedHighTrustAuxiliaryKind::AxiomPolicy,
                    status: "passed".to_owned(),
                    policy_hash: hash(5),
                    result_hash: hash(42),
                    artifact_hash: hash(43),
                },
                PackageVerifiedHighTrustAuxiliaryResult {
                    kind: PackageVerifiedHighTrustAuxiliaryKind::AuditBundle,
                    status: "passed".to_owned(),
                    policy_hash: hash(5),
                    result_hash: hash(44),
                    artifact_hash: hash(45),
                },
                PackageVerifiedHighTrustAuxiliaryResult {
                    kind: PackageVerifiedHighTrustAuxiliaryKind::ImportCertificateHash,
                    status: "passed".to_owned(),
                    policy_hash: hash(5),
                    result_hash: hash(46),
                    artifact_hash: hash(47),
                },
            ],
            generated_by: PackageVerifiedHighTrustGeneratedBy {
                command: "package high-trust".to_owned(),
                generator: "npa-cli".to_owned(),
                version: "0.1.0".to_owned(),
            },
            artifact_hash: hash(0),
        }
    }

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }
}

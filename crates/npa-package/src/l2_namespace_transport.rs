//! Canonical policy, request, and typed semantic projection for namespace transport.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{
    BinderType, CertReducibility, ConstructorSpec, DeclPayload, GlobalRef, LevelId, LevelNode,
    ModuleCert, MutualInductiveSpec, Name, NameId, Opacity, RecursorSpec, TermId, TermNode,
    UniverseConstraintSpec,
};

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_string, required_u64, validate_declaration_name,
        validate_module_name, validate_package_identity, validate_plain_string,
        PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, parse_package_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    schema::{
        L2_NAMESPACE_TRANSPORT_ATTESTATION_SCHEMA, L2_NAMESPACE_TRANSPORT_POLICY_SCHEMA,
        L2_NAMESPACE_TRANSPORT_REQUEST_SCHEMA,
    },
};

const POLICY_FIELDS: &[&str] = &[
    "schema",
    "policy_id",
    "policy_version",
    "validator_profile",
    "transport_profile",
    "source_acceptance_policy_id",
    "source_acceptance_policy_version",
    "source_acceptance_policy_file_hash",
    "target_package",
    "allowed_source_prefixes",
    "allowed_target_prefixes",
    "allow_declaration_renames",
    "allow_module_split_or_merge",
    "require_source_free_reference_verification",
    "proof_evidence",
];
const REQUEST_FIELDS: &[&str] = &[
    "schema",
    "source",
    "target",
    "module_mappings",
    "proof_evidence",
];
const IDENTITY_FIELDS: &[&str] = &["package", "version"];
const MAPPING_FIELDS: &[&str] = &["role", "source", "target", "declaration_mapping", "renames"];
const ENDPOINT_FIELDS: &[&str] = &["origin", "package", "version", "module"];
const RENAME_FIELDS: &[&str] = &["source", "target"];
const ATTESTATION_FIELDS: &[&str] = &[
    "schema",
    "transport_policy_id",
    "transport_policy_version",
    "transport_policy_file_hash",
    "acceptance_policy_id",
    "acceptance_policy_version",
    "acceptance_policy_file_hash",
    "mapping_request_file_hash",
    "source_acceptance_file_hash",
    "source_package",
    "source_version",
    "target_baseline_version",
    "target_package",
    "target_version",
    "source_manifest_hash",
    "target_baseline_manifest_hash",
    "target_manifest_hash",
    "source_lock_hash",
    "target_baseline_lock_hash",
    "target_lock_hash",
    "source_axiom_report_hash",
    "target_baseline_axiom_report_hash",
    "target_axiom_report_hash",
    "source_theorem_index_hash",
    "target_baseline_theorem_index_hash",
    "target_theorem_index_hash",
    "source_checker_identities",
    "target_baseline_checker_identities",
    "target_checker_identities",
    "changed_paths",
    "module_pairs",
    "theorem_pairs",
    "derived_mapping_hash",
    "normalized_closure_hash",
    "status",
    "proof_evidence",
];
const ATTESTATION_PAIR_FIELDS: &[&str] = &[
    "role",
    "source_module",
    "target_module",
    "source_source_file_hash",
    "target_source_file_hash",
    "source_certificate_file_hash",
    "target_certificate_file_hash",
    "source_certificate_hash",
    "target_certificate_hash",
    "source_export_hash",
    "target_export_hash",
    "source_axiom_report_hash",
    "target_axiom_report_hash",
];
const ATTESTATION_CHANGED_PATH_FIELDS: &[&str] =
    &["path", "baseline_file_hash", "target_file_hash"];
const ATTESTATION_THEOREM_PAIR_FIELDS: &[&str] = &[
    "source_module",
    "source_theorem",
    "source_statement_hash",
    "target_module",
    "target_theorem",
    "target_statement_hash",
];

/// Current strict namespace transport policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2NamespaceTransportPolicy {
    /// Schema identifier.
    pub schema: String,
    /// Stable policy identifier.
    pub policy_id: String,
    /// Policy version.
    pub policy_version: u64,
    /// Validator profile.
    pub validator_profile: String,
    /// Structural transport profile.
    pub transport_profile: String,
    /// Bound acceptance policy identifier.
    pub source_acceptance_policy_id: String,
    /// Bound acceptance policy version.
    pub source_acceptance_policy_version: u64,
    /// Bound acceptance policy file hash.
    pub source_acceptance_policy_file_hash: PackageHash,
    /// Required target package.
    pub target_package: PackageId,
    /// Allowed source namespace prefixes.
    pub allowed_source_prefixes: Vec<String>,
    /// Allowed target namespace prefixes.
    pub allowed_target_prefixes: Vec<String>,
    /// Whether explicit declaration renames are allowed.
    pub allow_declaration_renames: bool,
    /// Whether module split or merge is allowed.
    pub allow_module_split_or_merge: bool,
    /// Whether source-free reference verification is mandatory.
    pub require_source_free_reference_verification: bool,
    /// Always false.
    pub proof_evidence: bool,
}
impl L2NamespaceTransportPolicy {
    /// Serialize canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_policy(self)?;
        Ok(format!("{}\n", policy_json(self)))
    }
}

/// A package identity in a transport request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2TransportPackageIdentity {
    /// Package identifier.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
}

/// One complete module endpoint.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct L2TransportEndpoint {
    /// Artifact origin.
    pub origin: PackageArtifactOrigin,
    /// Package identifier.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Module name.
    pub module: Name,
}

/// One explicit global rename.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct L2TransportDeclarationRename {
    /// Source name.
    pub source: Name,
    /// Target name.
    pub target: Name,
}

/// Mapping role.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum L2TransportModuleRole {
    /// Newly materialized module.
    Selected,
    /// Existing unchanged dependency.
    Dependency,
}
impl L2TransportModuleRole {
    /// Stable spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Selected => "selected",
            Self::Dependency => "dependency",
        }
    }
}

/// One one-to-one module mapping.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2TransportModuleMapping {
    /// Mapping role.
    pub role: L2TransportModuleRole,
    /// Source endpoint.
    pub source: L2TransportEndpoint,
    /// Target endpoint.
    pub target: L2TransportEndpoint,
    /// Mapping strategy.
    pub declaration_mapping: String,
    /// Explicit rename exceptions.
    pub renames: Vec<L2TransportDeclarationRename>,
}

/// Canonical identity-only mapping request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2NamespaceTransportRequest {
    /// Schema identifier.
    pub schema: String,
    /// Source package.
    pub source: L2TransportPackageIdentity,
    /// Target package.
    pub target: L2TransportPackageIdentity,
    /// Module mappings.
    pub module_mappings: Vec<L2TransportModuleMapping>,
    /// Always false.
    pub proof_evidence: bool,
}
impl L2NamespaceTransportRequest {
    /// Serialize canonical JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_request(self)?;
        Ok(format!("{}\n", request_json(self)))
    }
    /// Apply the complete declared mapping to one global identity.
    pub fn map_global(&self, module: &Name, global: &Name) -> Option<(Name, Name)> {
        let m = self
            .module_mappings
            .iter()
            .find(|m| m.source.module == *module)?;
        let name = m
            .renames
            .iter()
            .find(|r| r.source == *global)
            .map_or_else(|| global.clone(), |r| r.target.clone());
        Some((m.target.module.clone(), name))
    }
}

/// One selected or dependency module pair recorded by a transport attestation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2TransportAttestationModulePair {
    /// Mapping role.
    pub role: L2TransportModuleRole,
    /// Source module name.
    pub source_module: Name,
    /// Target module name.
    pub target_module: Name,
    /// Exact source file hash, absent for checked external source modules.
    pub source_source_file_hash: Option<PackageHash>,
    /// Exact target source file hash.
    pub target_source_file_hash: PackageHash,
    /// Exact source certificate file hash.
    pub source_certificate_file_hash: PackageHash,
    /// Exact target certificate file hash.
    pub target_certificate_file_hash: PackageHash,
    /// Actual source certificate hash.
    pub source_certificate_hash: PackageHash,
    /// Actual target certificate hash.
    pub target_certificate_hash: PackageHash,
    /// Source export hash.
    pub source_export_hash: PackageHash,
    /// Target export hash.
    pub target_export_hash: PackageHash,
    /// Source axiom-report hash.
    pub source_axiom_report_hash: PackageHash,
    /// Target axiom-report hash.
    pub target_axiom_report_hash: PackageHash,
}

/// One path changed between the clean target baseline and materialized target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2TransportAttestationChangedPath {
    /// Package-relative logical path.
    pub path: PackagePath,
    /// Baseline file hash, or `None` for an added file.
    pub baseline_file_hash: Option<PackageHash>,
    /// Exact target file hash.
    pub target_file_hash: PackageHash,
}

/// One transported public theorem identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2TransportAttestationTheoremPair {
    /// Source module.
    pub source_module: Name,
    /// Source theorem.
    pub source_theorem: Name,
    /// Source statement hash.
    pub source_statement_hash: PackageHash,
    /// Target module.
    pub target_module: Name,
    /// Target theorem.
    pub target_theorem: Name,
    /// Target statement hash.
    pub target_statement_hash: PackageHash,
}

/// Canonical source-owned namespace transport attestation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2NamespaceTransportAttestation {
    /// Schema identifier.
    pub schema: String,
    /// Transport policy identity.
    pub transport_policy_id: String,
    /// Transport policy version.
    pub transport_policy_version: u64,
    /// Exact transport policy file hash.
    pub transport_policy_file_hash: PackageHash,
    /// Acceptance policy identity.
    pub acceptance_policy_id: String,
    /// Acceptance policy version.
    pub acceptance_policy_version: u64,
    /// Exact acceptance policy file hash.
    pub acceptance_policy_file_hash: PackageHash,
    /// Exact mapping request file hash.
    pub mapping_request_file_hash: PackageHash,
    /// Exact source acceptance file hash.
    pub source_acceptance_file_hash: PackageHash,
    /// Source package identity.
    pub source_package: PackageId,
    /// Source package version.
    pub source_version: PackageVersion,
    /// Clean baseline version.
    pub target_baseline_version: PackageVersion,
    /// Target package identity.
    pub target_package: PackageId,
    /// Materialized target version.
    pub target_version: PackageVersion,
    /// Source manifest file hash.
    pub source_manifest_hash: PackageHash,
    /// Baseline manifest file hash.
    pub target_baseline_manifest_hash: PackageHash,
    /// Target manifest file hash.
    pub target_manifest_hash: PackageHash,
    /// Source checked lock file hash.
    pub source_lock_hash: PackageHash,
    /// Baseline checked lock file hash.
    pub target_baseline_lock_hash: PackageHash,
    /// Target checked lock file hash.
    pub target_lock_hash: PackageHash,
    /// Exact source axiom-report file hash.
    pub source_axiom_report_hash: PackageHash,
    /// Exact target-baseline axiom-report file hash.
    pub target_baseline_axiom_report_hash: PackageHash,
    /// Exact target axiom-report file hash.
    pub target_axiom_report_hash: PackageHash,
    /// Exact source theorem-index file hash.
    pub source_theorem_index_hash: PackageHash,
    /// Exact target-baseline theorem-index file hash.
    pub target_baseline_theorem_index_hash: PackageHash,
    /// Exact target theorem-index file hash.
    pub target_theorem_index_hash: PackageHash,
    /// Source live checker identities.
    pub source_checker_identities: Vec<String>,
    /// Target-baseline live checker identities.
    pub target_baseline_checker_identities: Vec<String>,
    /// Target live checker identities.
    pub target_checker_identities: Vec<String>,
    /// Closed baseline-to-target changed-path inventory.
    pub changed_paths: Vec<L2TransportAttestationChangedPath>,
    /// Transported module pairs.
    pub module_pairs: Vec<L2TransportAttestationModulePair>,
    /// Transported theorem identities.
    pub theorem_pairs: Vec<L2TransportAttestationTheoremPair>,
    /// Complete mapping request semantic hash.
    pub derived_mapping_hash: PackageHash,
    /// Equal normalized closure projection hash.
    pub normalized_closure_hash: PackageHash,
    /// Always `accepted_namespace_transport`.
    pub status: String,
    /// Always false.
    pub proof_evidence: bool,
}

impl L2NamespaceTransportAttestation {
    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_attestation(self)?;
        Ok(format!("{}\n", attestation_json(self)))
    }
}

/// Parse a canonical namespace transport attestation.
pub fn parse_l2_namespace_transport_attestation_json(
    source: &str,
) -> PackageArtifactResult<L2NamespaceTransportAttestation> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, ATTESTATION_FIELDS)?;
    let attestation = L2NamespaceTransportAttestation {
        schema: required_string(members, "$", "schema")?,
        transport_policy_id: required_string(members, "$", "transport_policy_id")?,
        transport_policy_version: required_u64(members, "$", "transport_policy_version")?,
        transport_policy_file_hash: required_hash(members, "$", "transport_policy_file_hash")?,
        acceptance_policy_id: required_string(members, "$", "acceptance_policy_id")?,
        acceptance_policy_version: required_u64(members, "$", "acceptance_policy_version")?,
        acceptance_policy_file_hash: required_hash(members, "$", "acceptance_policy_file_hash")?,
        mapping_request_file_hash: required_hash(members, "$", "mapping_request_file_hash")?,
        source_acceptance_file_hash: required_hash(members, "$", "source_acceptance_file_hash")?,
        source_package: PackageId::new(required_string(members, "$", "source_package")?),
        source_version: PackageVersion::new(required_string(members, "$", "source_version")?),
        target_baseline_version: PackageVersion::new(required_string(
            members,
            "$",
            "target_baseline_version",
        )?),
        target_package: PackageId::new(required_string(members, "$", "target_package")?),
        target_version: PackageVersion::new(required_string(members, "$", "target_version")?),
        source_manifest_hash: required_hash(members, "$", "source_manifest_hash")?,
        target_baseline_manifest_hash: required_hash(
            members,
            "$",
            "target_baseline_manifest_hash",
        )?,
        target_manifest_hash: required_hash(members, "$", "target_manifest_hash")?,
        source_lock_hash: required_hash(members, "$", "source_lock_hash")?,
        target_baseline_lock_hash: required_hash(members, "$", "target_baseline_lock_hash")?,
        target_lock_hash: required_hash(members, "$", "target_lock_hash")?,
        source_axiom_report_hash: required_hash(members, "$", "source_axiom_report_hash")?,
        target_baseline_axiom_report_hash: required_hash(
            members,
            "$",
            "target_baseline_axiom_report_hash",
        )?,
        target_axiom_report_hash: required_hash(members, "$", "target_axiom_report_hash")?,
        source_theorem_index_hash: required_hash(members, "$", "source_theorem_index_hash")?,
        target_baseline_theorem_index_hash: required_hash(
            members,
            "$",
            "target_baseline_theorem_index_hash",
        )?,
        target_theorem_index_hash: required_hash(members, "$", "target_theorem_index_hash")?,
        source_checker_identities: string_array(members, "$", "source_checker_identities")?,
        target_baseline_checker_identities: string_array(
            members,
            "$",
            "target_baseline_checker_identities",
        )?,
        target_checker_identities: string_array(members, "$", "target_checker_identities")?,
        changed_paths: required_array(members, "$", "changed_paths")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_attestation_changed_path(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        module_pairs: required_array(members, "$", "module_pairs")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_attestation_pair(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        theorem_pairs: required_array(members, "$", "theorem_pairs")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_attestation_theorem_pair(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        derived_mapping_hash: required_hash(members, "$", "derived_mapping_hash")?,
        normalized_closure_hash: required_hash(members, "$", "normalized_closure_hash")?,
        status: required_string(members, "$", "status")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_attestation(&attestation)?;
    if source != attestation.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "transport attestation JSON bytes",
        ));
    }
    Ok(attestation)
}

fn validate_attestation(
    attestation: &L2NamespaceTransportAttestation,
) -> PackageArtifactResult<()> {
    if attestation.schema != L2_NAMESPACE_TRANSPORT_ATTESTATION_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_NAMESPACE_TRANSPORT_ATTESTATION_SCHEMA,
            &attestation.schema,
        ));
    }
    validate_package_identity(&attestation.source_package, &attestation.source_version)?;
    validate_package_identity(&attestation.target_package, &attestation.target_version)?;
    validate_package_identity(
        &attestation.target_package,
        &attestation.target_baseline_version,
    )?;
    validate_plain_string(&attestation.transport_policy_id, "transport_policy_id")?;
    validate_plain_string(&attestation.acceptance_policy_id, "acceptance_policy_id")?;
    if attestation.transport_policy_version == 0
        || attestation.acceptance_policy_version == 0
        || attestation.module_pairs.is_empty()
        || attestation.theorem_pairs.is_empty()
        || attestation.changed_paths.is_empty()
        || attestation.source_checker_identities.is_empty()
        || attestation.target_baseline_checker_identities.is_empty()
        || attestation.target_checker_identities.is_empty()
        || attestation.status != "accepted_namespace_transport"
        || attestation.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "attestation",
            "accepted non-proof transport",
            "mismatch",
        ));
    }
    let mut previous = None;
    for pair in &attestation.module_pairs {
        validate_module_name(&pair.source_module, "module_pairs.source_module")?;
        validate_module_name(&pair.target_module, "module_pairs.target_module")?;
        if pair.role == L2TransportModuleRole::Selected && pair.source_source_file_hash.is_none() {
            return Err(PackageArtifactError::invalid_enum_value(
                "module_pairs.source_source_file_hash",
                "source_source_file_hash",
                "hash for selected source module",
                "null",
            ));
        }
        let key = (&pair.source_module, &pair.target_module);
        if previous.is_some_and(|old| old >= key) {
            return Err(PackageArtifactError::non_canonical(
                "module_pairs",
                "sorted unique module pairs",
            ));
        }
        previous = Some(key);
    }
    validate_sorted_plain_strings(
        &attestation.source_checker_identities,
        "source_checker_identities",
    )?;
    validate_sorted_plain_strings(
        &attestation.target_baseline_checker_identities,
        "target_baseline_checker_identities",
    )?;
    validate_sorted_plain_strings(
        &attestation.target_checker_identities,
        "target_checker_identities",
    )?;
    let mut previous_path = None;
    for changed in &attestation.changed_paths {
        let path = changed.path.as_str();
        if validate_package_path(&changed.path, "changed_paths.path").is_err() {
            return Err(PackageArtifactError::invalid_enum_value(
                "changed_paths.path",
                "path",
                "package-relative path",
                path,
            ));
        }
        if previous_path.is_some_and(|old| old >= path) {
            return Err(PackageArtifactError::non_canonical(
                "changed_paths",
                "sorted unique paths",
            ));
        }
        previous_path = Some(path);
    }
    let mut previous_theorem = None;
    for pair in &attestation.theorem_pairs {
        validate_module_name(&pair.source_module, "theorem_pairs.source_module")?;
        validate_declaration_name(&pair.source_theorem, "theorem_pairs.source_theorem")?;
        validate_module_name(&pair.target_module, "theorem_pairs.target_module")?;
        validate_declaration_name(&pair.target_theorem, "theorem_pairs.target_theorem")?;
        let key = (
            &pair.source_module,
            &pair.source_theorem,
            &pair.target_module,
            &pair.target_theorem,
        );
        if previous_theorem.is_some_and(|old| old >= key) {
            return Err(PackageArtifactError::non_canonical(
                "theorem_pairs",
                "sorted unique theorem pairs",
            ));
        }
        previous_theorem = Some(key);
    }
    Ok(())
}

fn validate_sorted_plain_strings(values: &[String], path: &str) -> PackageArtifactResult<()> {
    let mut previous = None;
    for value in values {
        validate_plain_string(value, path)?;
        if previous.is_some_and(|old: &String| old >= value) {
            return Err(PackageArtifactError::non_canonical(
                path,
                "sorted unique strings",
            ));
        }
        previous = Some(value);
    }
    Ok(())
}

fn parse_attestation_pair(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2TransportAttestationModulePair> {
    let path = format!("module_pairs[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ATTESTATION_PAIR_FIELDS)?;
    Ok(L2TransportAttestationModulePair {
        role: match required_string(members, &path, "role")?.as_str() {
            "selected" => L2TransportModuleRole::Selected,
            "dependency" => L2TransportModuleRole::Dependency,
            actual => {
                return Err(PackageArtifactError::invalid_enum_value(
                    &path,
                    "role",
                    "selected or dependency",
                    actual,
                ))
            }
        },
        source_module: required_name(members, &path, "source_module")?,
        target_module: required_name(members, &path, "target_module")?,
        source_source_file_hash: optional_hash(members, &path, "source_source_file_hash")?,
        target_source_file_hash: required_hash(members, &path, "target_source_file_hash")?,
        source_certificate_file_hash: required_hash(
            members,
            &path,
            "source_certificate_file_hash",
        )?,
        target_certificate_file_hash: required_hash(
            members,
            &path,
            "target_certificate_file_hash",
        )?,
        source_certificate_hash: required_hash(members, &path, "source_certificate_hash")?,
        target_certificate_hash: required_hash(members, &path, "target_certificate_hash")?,
        source_export_hash: required_hash(members, &path, "source_export_hash")?,
        target_export_hash: required_hash(members, &path, "target_export_hash")?,
        source_axiom_report_hash: required_hash(members, &path, "source_axiom_report_hash")?,
        target_axiom_report_hash: required_hash(members, &path, "target_axiom_report_hash")?,
    })
}

fn parse_attestation_changed_path(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2TransportAttestationChangedPath> {
    let path = format!("changed_paths[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ATTESTATION_CHANGED_PATH_FIELDS)?;
    Ok(L2TransportAttestationChangedPath {
        path: PackagePath::new(required_string(members, &path, "path")?),
        baseline_file_hash: optional_hash(members, &path, "baseline_file_hash")?,
        target_file_hash: required_hash(members, &path, "target_file_hash")?,
    })
}

fn parse_attestation_theorem_pair(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2TransportAttestationTheoremPair> {
    let path = format!("theorem_pairs[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ATTESTATION_THEOREM_PAIR_FIELDS)?;
    Ok(L2TransportAttestationTheoremPair {
        source_module: required_name(members, &path, "source_module")?,
        source_theorem: required_name(members, &path, "source_theorem")?,
        source_statement_hash: required_hash(members, &path, "source_statement_hash")?,
        target_module: required_name(members, &path, "target_module")?,
        target_theorem: required_name(members, &path, "target_theorem")?,
        target_statement_hash: required_hash(members, &path, "target_statement_hash")?,
    })
}

/// Parse a canonical transport policy.
pub fn parse_l2_namespace_transport_policy_json(
    source: &str,
) -> PackageArtifactResult<L2NamespaceTransportPolicy> {
    let v = parse_artifact_json(source)?;
    let m = expect_object(&v, "$")?;
    reject_unknown_fields("$", m, POLICY_FIELDS)?;
    let p = L2NamespaceTransportPolicy {
        schema: required_string(m, "$", "schema")?,
        policy_id: required_string(m, "$", "policy_id")?,
        policy_version: required_u64(m, "$", "policy_version")?,
        validator_profile: required_string(m, "$", "validator_profile")?,
        transport_profile: required_string(m, "$", "transport_profile")?,
        source_acceptance_policy_id: required_string(m, "$", "source_acceptance_policy_id")?,
        source_acceptance_policy_version: required_u64(m, "$", "source_acceptance_policy_version")?,
        source_acceptance_policy_file_hash: required_hash(
            m,
            "$",
            "source_acceptance_policy_file_hash",
        )?,
        target_package: PackageId::new(required_string(m, "$", "target_package")?),
        allowed_source_prefixes: string_array(m, "$", "allowed_source_prefixes")?,
        allowed_target_prefixes: string_array(m, "$", "allowed_target_prefixes")?,
        allow_declaration_renames: required_bool(m, "$", "allow_declaration_renames")?,
        allow_module_split_or_merge: required_bool(m, "$", "allow_module_split_or_merge")?,
        require_source_free_reference_verification: required_bool(
            m,
            "$",
            "require_source_free_reference_verification",
        )?,
        proof_evidence: required_bool(m, "$", "proof_evidence")?,
    };
    validate_policy(&p)?;
    if source != p.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "transport policy JSON bytes",
        ));
    }
    Ok(p)
}

/// Parse a canonical transport mapping request.
pub fn parse_l2_namespace_transport_request_json(
    source: &str,
) -> PackageArtifactResult<L2NamespaceTransportRequest> {
    let v = parse_artifact_json(source)?;
    let m = expect_object(&v, "$")?;
    reject_unknown_fields("$", m, REQUEST_FIELDS)?;
    let r = L2NamespaceTransportRequest {
        schema: required_string(m, "$", "schema")?,
        source: parse_identity(required_value(m, "$", "source")?, "source")?,
        target: parse_identity(required_value(m, "$", "target")?, "target")?,
        module_mappings: required_array(m, "$", "module_mappings")?
            .iter()
            .enumerate()
            .map(|(i, v)| parse_mapping(v, i))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        proof_evidence: required_bool(m, "$", "proof_evidence")?,
    };
    validate_request(&r)?;
    if source != r.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "transport request JSON bytes",
        ));
    }
    Ok(r)
}

fn validate_policy(p: &L2NamespaceTransportPolicy) -> PackageArtifactResult<()> {
    if p.schema != L2_NAMESPACE_TRANSPORT_POLICY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_NAMESPACE_TRANSPORT_POLICY_SCHEMA,
            &p.schema,
        ));
    }
    validate_plain_string(&p.policy_id, "policy_id")?;
    if p.policy_version == 0
        || p.source_acceptance_policy_version == 0
        || p.validator_profile != "npa.l2_namespace_transport.validator.v1"
        || p.transport_profile != "canonical-certificate-global-rename-only.v1"
        || !p.allow_declaration_renames
        || p.allow_module_split_or_merge
        || !p.require_source_free_reference_verification
        || p.proof_evidence
        || p.allowed_source_prefixes.is_empty()
        || p.allowed_target_prefixes.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "policy",
            "strict v1 transport policy",
            "mismatch",
        ));
    }
    Ok(())
}
fn validate_request(r: &L2NamespaceTransportRequest) -> PackageArtifactResult<()> {
    if r.schema != L2_NAMESPACE_TRANSPORT_REQUEST_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_NAMESPACE_TRANSPORT_REQUEST_SCHEMA,
            &r.schema,
        ));
    }
    validate_package_identity(&r.source.package, &r.source.version)?;
    validate_package_identity(&r.target.package, &r.target.version)?;
    if r.proof_evidence
        || !r
            .module_mappings
            .iter()
            .any(|m| m.role == L2TransportModuleRole::Selected)
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "request",
            "selected mapping and false proof_evidence",
            "mismatch",
        ));
    }
    let (mut ss, mut ts) = (BTreeSet::new(), BTreeSet::new());
    let mut previous = None;
    for (index, m) in r.module_mappings.iter().enumerate() {
        validate_module_name(&m.source.module, "source.module")?;
        validate_module_name(&m.target.module, "target.module")?;
        validate_package_identity(&m.source.package, &m.source.version)?;
        validate_package_identity(&m.target.package, &m.target.version)?;
        if m.declaration_mapping != "same-name-except-explicit"
            || !ss.insert(m.source.clone())
            || !ts.insert(m.target.clone())
            || m.target.origin != PackageArtifactOrigin::Local
            || (m.role == L2TransportModuleRole::Selected
                && m.source.origin != PackageArtifactOrigin::Local)
            || (m.source.origin == PackageArtifactOrigin::Local
                && (m.source.package != r.source.package || m.source.version != r.source.version))
            || m.target.package != r.target.package
            || m.target.version != r.target.version
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("module_mappings[{index}]"),
                "mapping",
                "one-to-one endpoints",
                "mismatch",
            ));
        }
        let key = (&m.source, &m.target);
        if previous.is_some_and(|old| old >= key) {
            return Err(PackageArtifactError::non_canonical(
                "module_mappings",
                "sorted mappings",
            ));
        }
        previous = Some(key);
        let (mut rs, mut rt) = (BTreeSet::new(), BTreeSet::new());
        let mut prior = None;
        for rename in &m.renames {
            validate_declaration_name(&rename.source, "renames.source")?;
            validate_declaration_name(&rename.target, "renames.target")?;
            if !rs.insert(rename.source.clone())
                || !rt.insert(rename.target.clone())
                || prior.as_ref().is_some_and(|old| old >= rename)
            {
                return Err(PackageArtifactError::non_canonical(
                    "renames",
                    "sorted injective renames",
                ));
            }
            prior = Some(rename.clone());
        }
    }
    Ok(())
}

/// Build an ID-independent typed semantic certificate projection.
///
/// The projection resolves name, term, level, import, local declaration, and generated-global
/// indexes recursively. Rename-sensitive derived hashes are intentionally omitted.
pub fn l2_transport_module_projection(
    cert: &ModuleCert,
    request: &L2NamespaceTransportRequest,
    map_source: bool,
) -> PackageArtifactResult<Vec<u8>> {
    l2_transport_module_projection_internal(cert, request, map_source, None, true)
}

/// Build a projection for an identity-selected declaration subset.
///
/// This is used for already-public dependency modules, whose unrelated target declarations and
/// imports are outside the selected closure.
pub fn l2_transport_module_projection_subset(
    cert: &ModuleCert,
    request: &L2NamespaceTransportRequest,
    map_source: bool,
    declaration_names: &BTreeSet<Name>,
) -> PackageArtifactResult<Vec<u8>> {
    l2_transport_module_projection_internal(
        cert,
        request,
        map_source,
        Some(declaration_names),
        false,
    )
}

/// Return mapped, ID-independent source declaration names for subset comparison.
pub fn l2_transport_module_declaration_names(
    cert: &ModuleCert,
    request: &L2NamespaceTransportRequest,
    map_source: bool,
) -> PackageArtifactResult<BTreeSet<Name>> {
    let context = Projection {
        cert,
        request,
        map_source,
    };
    cert.export_block
        .iter()
        .map(|entry| {
            context
                .name(entry.name)
                .map(|name| context.mapped(&cert.header.module, &name).1)
        })
        .collect()
}

fn l2_transport_module_projection_internal(
    cert: &ModuleCert,
    request: &L2NamespaceTransportRequest,
    map_source: bool,
    declaration_names: Option<&BTreeSet<Name>>,
    include_import_inventory: bool,
) -> PackageArtifactResult<Vec<u8>> {
    let mapping = if map_source {
        request
            .module_mappings
            .iter()
            .find(|m| m.source.module == cert.header.module)
    } else {
        request
            .module_mappings
            .iter()
            .find(|m| m.target.module == cert.header.module)
    }
    .ok_or_else(|| {
        PackageArtifactError::invalid_enum_value(
            "module",
            "mapping",
            "mapped module",
            cert.header.module.as_dotted(),
        )
    })?;
    let c = Projection {
        cert,
        request,
        map_source,
    };
    let mut out = Vec::new();
    put_str(&mut out, "NPA-L2-TRANSPORT-PROJECTION-v1");
    put_name(&mut out, &mapping.target.module);
    let mut imports = cert
        .imports
        .iter()
        .map(|i| {
            if map_source {
                request
                    .module_mappings
                    .iter()
                    .find(|m| m.source.module == i.module)
                    .map_or_else(|| i.module.clone(), |m| m.target.module.clone())
            } else {
                i.module.clone()
            }
        })
        .collect::<Vec<_>>();
    if !include_import_inventory {
        imports.clear();
    }
    imports.sort();
    put_u64(&mut out, imports.len() as u64);
    for i in imports {
        put_name(&mut out, &i);
    }
    let mut decls = cert
        .declarations
        .iter()
        .enumerate()
        .map(|(i, d)| {
            let mut b = Vec::new();
            c.decl(&mut b, &d.decl)?;
            let mut dependencies = Vec::new();
            for dependency in &d.dependencies {
                let mut identity = Vec::new();
                c.global(&mut identity, &dependency.global_ref)?;
                dependencies.push(identity);
            }
            dependencies.sort();
            put_u64(&mut b, dependencies.len() as u64);
            for identity in dependencies {
                put_bytes(&mut b, &identity);
            }
            let mut axioms = Vec::new();
            for axiom in &d.axiom_dependencies {
                let mut identity = Vec::new();
                c.global(&mut identity, &axiom.global_ref)?;
                axioms.push(identity);
            }
            axioms.sort();
            put_u64(&mut b, axioms.len() as u64);
            for identity in axioms {
                put_bytes(&mut b, &identity);
            }
            let name = c.decl_name(i)?;
            Ok((name, b))
        })
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    if let Some(names) = declaration_names {
        decls.retain(|(name, _)| names.contains(name));
    }
    decls.sort_by(|a, b| a.0.cmp(&b.0));
    put_u64(&mut out, decls.len() as u64);
    for (n, b) in decls {
        put_name(&mut out, &n);
        put_bytes(&mut out, &b);
    }
    Ok(out)
}

/// Hash an equal normalized closure projection with the v1 domain separator.
pub fn l2_transport_normalized_closure_hash(bytes: &[u8]) -> PackageHash {
    let mut v = b"NPA-L2-TRANSPORT-CLOSURE-v1\0".to_vec();
    v.extend_from_slice(bytes);
    package_file_hash(&v)
}

/// Hash the complete expanded module/global map with the v1 transport-map domain separator.
///
/// The caller supplies every verified source certificate named by the request. Rows include
/// implicit same-name mappings and generated exports, and are sorted by their complete source
/// and target identities rather than by request storage order.
pub fn l2_transport_derived_mapping_hash(
    request: &L2NamespaceTransportRequest,
    source_certificates: &BTreeMap<Name, ModuleCert>,
) -> PackageArtifactResult<PackageHash> {
    let mut rows = Vec::new();
    for mapping in &request.module_mappings {
        let cert = source_certificates
            .get(&mapping.source.module)
            .ok_or_else(|| {
                PackageArtifactError::invalid_enum_value(
                    "module_mappings.source.module",
                    "module",
                    "loaded source certificate",
                    mapping.source.module.as_dotted(),
                )
            })?;
        if cert.header.module != mapping.source.module {
            return Err(PackageArtifactError::invalid_enum_value(
                "module_mappings.source.module",
                "module",
                mapping.source.module.as_dotted(),
                cert.header.module.as_dotted(),
            ));
        }
        for export in &cert.export_block {
            let source_name = cert.name_table.get(export.name).cloned().ok_or_else(|| {
                PackageArtifactError::invalid_enum_value(
                    "export_block.name",
                    "name",
                    "valid name-table entry",
                    export.name.to_string(),
                )
            })?;
            let (target_module, target_name) = request
                .map_global(&mapping.source.module, &source_name)
                .ok_or_else(|| {
                    PackageArtifactError::invalid_enum_value(
                        "module_mappings",
                        "mapping",
                        "complete global mapping",
                        source_name.as_dotted(),
                    )
                })?;
            rows.push((
                mapping.source.clone(),
                source_name,
                mapping.target.clone(),
                target_module,
                target_name,
            ));
        }
    }
    rows.sort();

    let mut bytes = Vec::new();
    put_u64(&mut bytes, rows.len() as u64);
    for (source, source_name, target, target_module, target_name) in rows {
        put_str(&mut bytes, source.origin.as_str());
        put_str(&mut bytes, source.package.as_str());
        put_str(&mut bytes, source.version.as_str());
        put_name(&mut bytes, &source.module);
        put_name(&mut bytes, &source_name);
        put_str(&mut bytes, target.origin.as_str());
        put_str(&mut bytes, target.package.as_str());
        put_str(&mut bytes, target.version.as_str());
        put_name(&mut bytes, &target_module);
        put_name(&mut bytes, &target_name);
    }
    let mut input = b"NPA-L2-TRANSPORT-MAP-v1\0".to_vec();
    input.extend_from_slice(&bytes);
    Ok(package_file_hash(&input))
}

struct Projection<'a> {
    cert: &'a ModuleCert,
    request: &'a L2NamespaceTransportRequest,
    map_source: bool,
}
impl Projection<'_> {
    fn name(&self, id: NameId) -> PackageArtifactResult<Name> {
        self.cert.name_table.get(id).cloned().ok_or_else(|| {
            PackageArtifactError::invalid_enum_value("name_table", "id", "valid", id.to_string())
        })
    }
    fn raw_decl_name(&self, i: usize) -> PackageArtifactResult<Name> {
        self.name(decl_name_id(
            &self
                .cert
                .declarations
                .get(i)
                .ok_or_else(|| {
                    PackageArtifactError::invalid_enum_value(
                        "declarations",
                        "index",
                        "valid",
                        i.to_string(),
                    )
                })?
                .decl,
        ))
    }
    fn mapped(&self, module: &Name, name: &Name) -> (Name, Name) {
        if self.map_source {
            self.request
                .map_global(module, name)
                .unwrap_or_else(|| (module.clone(), name.clone()))
        } else {
            (module.clone(), name.clone())
        }
    }
    fn decl_name(&self, i: usize) -> PackageArtifactResult<Name> {
        let n = self.raw_decl_name(i)?;
        Ok(self.mapped(&self.cert.header.module, &n).1)
    }
    fn global(&self, o: &mut Vec<u8>, g: &GlobalRef) -> PackageArtifactResult<()> {
        let (m, n) = match g {
            GlobalRef::Builtin { name, .. } => (Name::from_dotted("$builtin"), self.name(*name)?),
            GlobalRef::Imported {
                import_index, name, ..
            } => (
                self.cert
                    .imports
                    .get(*import_index)
                    .ok_or_else(|| {
                        PackageArtifactError::invalid_enum_value(
                            "imports",
                            "index",
                            "valid",
                            import_index.to_string(),
                        )
                    })?
                    .module
                    .clone(),
                self.name(*name)?,
            ),
            GlobalRef::Local { decl_index } => (
                self.cert.header.module.clone(),
                self.raw_decl_name(*decl_index)?,
            ),
            GlobalRef::LocalGenerated { name, .. } => {
                (self.cert.header.module.clone(), self.name(*name)?)
            }
        };
        let (m, n) = self.mapped(&m, &n);
        put_name(o, &m);
        put_name(o, &n);
        Ok(())
    }
    fn level(&self, o: &mut Vec<u8>, id: LevelId) -> PackageArtifactResult<()> {
        match self.cert.level_table.get(id).ok_or_else(|| {
            PackageArtifactError::invalid_enum_value("level_table", "id", "valid", id.to_string())
        })? {
            LevelNode::Zero => o.push(0),
            LevelNode::Succ(a) => {
                o.push(1);
                self.level(o, *a)?
            }
            LevelNode::Max(a, b) => {
                o.push(2);
                self.level(o, *a)?;
                self.level(o, *b)?
            }
            LevelNode::IMax(a, b) => {
                o.push(3);
                self.level(o, *a)?;
                self.level(o, *b)?
            }
            LevelNode::Param(n) => {
                o.push(4);
                put_name(o, &self.name(*n)?);
            }
        }
        Ok(())
    }
    fn term(&self, o: &mut Vec<u8>, id: TermId) -> PackageArtifactResult<()> {
        match self.cert.term_table.get(id).ok_or_else(|| {
            PackageArtifactError::invalid_enum_value("term_table", "id", "valid", id.to_string())
        })? {
            TermNode::Sort(l) => {
                o.push(0);
                self.level(o, *l)?
            }
            TermNode::BVar(i) => {
                o.push(1);
                put_u64(o, *i as u64)
            }
            TermNode::Const { global_ref, levels } => {
                o.push(2);
                self.global(o, global_ref)?;
                put_u64(o, levels.len() as u64);
                for l in levels {
                    self.level(o, *l)?
                }
            }
            TermNode::App(a, b) => {
                o.push(3);
                self.term(o, *a)?;
                self.term(o, *b)?
            }
            TermNode::Lam { ty, body } => {
                o.push(4);
                self.term(o, *ty)?;
                self.term(o, *body)?
            }
            TermNode::Pi { ty, body } => {
                o.push(5);
                self.term(o, *ty)?;
                self.term(o, *body)?
            }
            TermNode::Let { ty, value, body } => {
                o.push(6);
                self.term(o, *ty)?;
                self.term(o, *value)?;
                self.term(o, *body)?
            }
        }
        Ok(())
    }
    fn decl(&self, o: &mut Vec<u8>, d: &DeclPayload) -> PackageArtifactResult<()> {
        match d {
            DeclPayload::Axiom {
                name,
                universe_params,
                ty,
            } => self.basic_decl(o, 0, *name, universe_params, *ty, None)?,
            DeclPayload::AxiomConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
            } => {
                self.basic_decl(o, 1, *name, universe_params, *ty, None)?;
                self.constraints(o, universe_constraints)?;
            }
            DeclPayload::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            } => {
                self.basic_decl(o, 2, *name, universe_params, *ty, Some(*value))?;
                o.push(reducibility_tag(*reducibility));
            }
            DeclPayload::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            } => {
                self.basic_decl(o, 3, *name, universe_params, *ty, Some(*value))?;
                self.constraints(o, universe_constraints)?;
                o.push(reducibility_tag(*reducibility));
            }
            DeclPayload::Theorem {
                name,
                universe_params,
                ty,
                proof,
                opacity,
            } => {
                self.basic_decl(o, 4, *name, universe_params, *ty, Some(*proof))?;
                o.push(opacity_tag(*opacity));
            }
            DeclPayload::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
                opacity,
            } => {
                self.basic_decl(o, 5, *name, universe_params, *ty, Some(*proof))?;
                self.constraints(o, universe_constraints)?;
                o.push(opacity_tag(*opacity));
            }
            DeclPayload::Inductive {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
            } => {
                o.push(6);
                self.names(o, universe_params)?;
                self.inductive(o, *name, params, indices, *sort, constructors, recursor)?;
            }
            DeclPayload::InductiveConstrained {
                name,
                universe_params,
                universe_constraints,
                params,
                indices,
                sort,
                constructors,
                recursor,
            } => {
                o.push(7);
                self.names(o, universe_params)?;
                self.constraints(o, universe_constraints)?;
                self.inductive(o, *name, params, indices, *sort, constructors, recursor)?;
            }
            DeclPayload::MutualInductiveBlock {
                name,
                universe_params,
                universe_constraints,
                inductives,
            } => {
                o.push(8);
                let raw = self.name(*name)?;
                put_name(o, &self.mapped(&self.cert.header.module, &raw).1);
                self.names(o, universe_params)?;
                self.constraints(o, universe_constraints)?;
                put_u64(o, inductives.len() as u64);
                for inductive in inductives {
                    self.mutual_inductive(o, inductive)?;
                }
            }
        }
        Ok(())
    }

    fn basic_decl(
        &self,
        out: &mut Vec<u8>,
        tag: u8,
        name: NameId,
        universe_params: &[NameId],
        ty: TermId,
        body: Option<TermId>,
    ) -> PackageArtifactResult<()> {
        out.push(tag);
        let raw = self.name(name)?;
        put_name(out, &self.mapped(&self.cert.header.module, &raw).1);
        self.names(out, universe_params)?;
        self.term(out, ty)?;
        if let Some(body) = body {
            self.term(out, body)?;
        }
        Ok(())
    }

    fn names(&self, out: &mut Vec<u8>, names: &[NameId]) -> PackageArtifactResult<()> {
        put_u64(out, names.len() as u64);
        for name in names {
            put_name(out, &self.name(*name)?);
        }
        Ok(())
    }

    fn constraints(
        &self,
        out: &mut Vec<u8>,
        constraints: &[UniverseConstraintSpec],
    ) -> PackageArtifactResult<()> {
        put_u64(out, constraints.len() as u64);
        for constraint in constraints {
            self.level(out, constraint.lhs)?;
            let relation = format!("{:?}", constraint.relation);
            put_str(out, &relation);
            self.level(out, constraint.rhs)?;
        }
        Ok(())
    }

    fn binders(&self, out: &mut Vec<u8>, binders: &[BinderType]) -> PackageArtifactResult<()> {
        put_u64(out, binders.len() as u64);
        for binder in binders {
            self.term(out, binder.ty)?;
        }
        Ok(())
    }

    fn constructors(
        &self,
        out: &mut Vec<u8>,
        constructors: &[ConstructorSpec],
    ) -> PackageArtifactResult<()> {
        put_u64(out, constructors.len() as u64);
        for constructor in constructors {
            let raw = self.name(constructor.name)?;
            put_name(out, &self.mapped(&self.cert.header.module, &raw).1);
            self.term(out, constructor.ty)?;
        }
        Ok(())
    }

    fn recursor(
        &self,
        out: &mut Vec<u8>,
        recursor: &Option<RecursorSpec>,
    ) -> PackageArtifactResult<()> {
        match recursor {
            None => out.push(0),
            Some(recursor) => {
                out.push(1);
                let raw = self.name(recursor.name)?;
                put_name(out, &self.mapped(&self.cert.header.module, &raw).1);
                self.names(out, &recursor.universe_params)?;
                self.term(out, recursor.ty)?;
                put_u64(out, recursor.rules.minor_start as u64);
                put_u64(out, recursor.rules.major_index as u64);
            }
        }
        Ok(())
    }

    // The certificate schema exposes these semantic children as separate fields; keeping them
    // explicit prevents an index-bearing intermediate representation from entering the hash.
    #[allow(clippy::too_many_arguments)]
    fn inductive(
        &self,
        out: &mut Vec<u8>,
        name: NameId,
        params: &[BinderType],
        indices: &[BinderType],
        sort: LevelId,
        constructors: &[ConstructorSpec],
        recursor: &Option<RecursorSpec>,
    ) -> PackageArtifactResult<()> {
        let raw = self.name(name)?;
        put_name(out, &self.mapped(&self.cert.header.module, &raw).1);
        self.binders(out, params)?;
        self.binders(out, indices)?;
        self.level(out, sort)?;
        self.constructors(out, constructors)?;
        self.recursor(out, recursor)
    }

    fn mutual_inductive(
        &self,
        out: &mut Vec<u8>,
        inductive: &MutualInductiveSpec,
    ) -> PackageArtifactResult<()> {
        self.inductive(
            out,
            inductive.name,
            &inductive.params,
            &inductive.indices,
            inductive.sort,
            &inductive.constructors,
            &inductive.recursor,
        )
    }
}

const fn reducibility_tag(value: CertReducibility) -> u8 {
    match value {
        CertReducibility::Reducible => 0,
        CertReducibility::Opaque => 1,
    }
}

const fn opacity_tag(value: Opacity) -> u8 {
    match value {
        Opacity::Opaque => 0,
    }
}
fn decl_name_id(d: &DeclPayload) -> NameId {
    match d {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}
fn put_u64(o: &mut Vec<u8>, v: u64) {
    o.extend_from_slice(&v.to_le_bytes())
}
fn put_bytes(o: &mut Vec<u8>, v: &[u8]) {
    put_u64(o, v.len() as u64);
    o.extend_from_slice(v)
}
fn put_str(o: &mut Vec<u8>, v: &str) {
    put_bytes(o, v.as_bytes())
}
fn put_name(o: &mut Vec<u8>, v: &Name) {
    put_str(o, &v.as_dotted())
}
fn required_value<'a>(
    m: &'a [crate::json::JsonMember],
    p: &str,
    f: &str,
) -> PackageArtifactResult<&'a JsonValue> {
    m.iter()
        .find(|x| x.key() == f)
        .map(|x| x.value())
        .ok_or_else(|| PackageArtifactError::missing_field(format!("{p}.{f}"), f))
}
fn string_array(
    m: &[crate::json::JsonMember],
    p: &str,
    f: &str,
) -> PackageArtifactResult<Vec<String>> {
    required_array(m, p, f)?
        .iter()
        .map(|v| {
            if let JsonValue::String(s) = v {
                Ok(s.clone())
            } else {
                Err(PackageArtifactError::invalid_enum_value(
                    p,
                    f,
                    "string",
                    "non-string",
                ))
            }
        })
        .collect()
}
fn optional_hash(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<PackageHash>> {
    match required_value(members, path, field)? {
        JsonValue::Null => Ok(None),
        JsonValue::String(value) => parse_package_hash(value, format!("{path}.{field}"))
            .map(Some)
            .map_err(|_| {
                PackageArtifactError::invalid_hash_format(format!("{path}.{field}"), value)
            }),
        _ => Err(PackageArtifactError::invalid_enum_value(
            format!("{path}.{field}"),
            field,
            "hash string or null",
            "non-string",
        )),
    }
}
fn parse_identity(v: &JsonValue, p: &str) -> PackageArtifactResult<L2TransportPackageIdentity> {
    let m = expect_object(v, p)?;
    reject_unknown_fields(p, m, IDENTITY_FIELDS)?;
    Ok(L2TransportPackageIdentity {
        package: PackageId::new(required_string(m, p, "package")?),
        version: PackageVersion::new(required_string(m, p, "version")?),
    })
}
fn parse_endpoint(v: &JsonValue, p: &str) -> PackageArtifactResult<L2TransportEndpoint> {
    let m = expect_object(v, p)?;
    reject_unknown_fields(p, m, ENDPOINT_FIELDS)?;
    Ok(L2TransportEndpoint {
        origin: PackageArtifactOrigin::parse(
            &required_string(m, p, "origin")?,
            &format!("{p}.origin"),
        )?,
        package: PackageId::new(required_string(m, p, "package")?),
        version: PackageVersion::new(required_string(m, p, "version")?),
        module: required_name(m, p, "module")?,
    })
}
fn parse_mapping(v: &JsonValue, i: usize) -> PackageArtifactResult<L2TransportModuleMapping> {
    let p = format!("module_mappings[{i}]");
    let m = expect_object(v, &p)?;
    reject_unknown_fields(&p, m, MAPPING_FIELDS)?;
    let role = match required_string(m, &p, "role")?.as_str() {
        "selected" => L2TransportModuleRole::Selected,
        "dependency" => L2TransportModuleRole::Dependency,
        x => {
            return Err(PackageArtifactError::invalid_enum_value(
                &p,
                "role",
                "selected or dependency",
                x,
            ))
        }
    };
    Ok(L2TransportModuleMapping {
        role,
        source: parse_endpoint(required_value(m, &p, "source")?, "source")?,
        target: parse_endpoint(required_value(m, &p, "target")?, "target")?,
        declaration_mapping: required_string(m, &p, "declaration_mapping")?,
        renames: required_array(m, &p, "renames")?
            .iter()
            .map(|v| {
                let m = expect_object(v, "rename")?;
                reject_unknown_fields("rename", m, RENAME_FIELDS)?;
                Ok(L2TransportDeclarationRename {
                    source: required_name(m, "rename", "source")?,
                    target: required_name(m, "rename", "target")?,
                })
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}
fn identity_json(i: &L2TransportPackageIdentity) -> String {
    json_object_in_order(vec![
        ("package", json_string(i.package.as_str())),
        ("version", json_string(i.version.as_str())),
    ])
}
fn endpoint_json(e: &L2TransportEndpoint) -> String {
    json_object_in_order(vec![
        ("origin", json_string(e.origin.as_str())),
        ("package", json_string(e.package.as_str())),
        ("version", json_string(e.version.as_str())),
        ("module", json_string(&e.module.as_dotted())),
    ])
}
fn attestation_json(a: &L2NamespaceTransportAttestation) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&a.schema)),
        ("transport_policy_id", json_string(&a.transport_policy_id)),
        (
            "transport_policy_version",
            json_u64(a.transport_policy_version),
        ),
        (
            "transport_policy_file_hash",
            hash_json(a.transport_policy_file_hash),
        ),
        ("acceptance_policy_id", json_string(&a.acceptance_policy_id)),
        (
            "acceptance_policy_version",
            json_u64(a.acceptance_policy_version),
        ),
        (
            "acceptance_policy_file_hash",
            hash_json(a.acceptance_policy_file_hash),
        ),
        (
            "mapping_request_file_hash",
            hash_json(a.mapping_request_file_hash),
        ),
        (
            "source_acceptance_file_hash",
            hash_json(a.source_acceptance_file_hash),
        ),
        ("source_package", json_string(a.source_package.as_str())),
        ("source_version", json_string(a.source_version.as_str())),
        (
            "target_baseline_version",
            json_string(a.target_baseline_version.as_str()),
        ),
        ("target_package", json_string(a.target_package.as_str())),
        ("target_version", json_string(a.target_version.as_str())),
        ("source_manifest_hash", hash_json(a.source_manifest_hash)),
        (
            "target_baseline_manifest_hash",
            hash_json(a.target_baseline_manifest_hash),
        ),
        ("target_manifest_hash", hash_json(a.target_manifest_hash)),
        ("source_lock_hash", hash_json(a.source_lock_hash)),
        (
            "target_baseline_lock_hash",
            hash_json(a.target_baseline_lock_hash),
        ),
        ("target_lock_hash", hash_json(a.target_lock_hash)),
        (
            "source_axiom_report_hash",
            hash_json(a.source_axiom_report_hash),
        ),
        (
            "target_baseline_axiom_report_hash",
            hash_json(a.target_baseline_axiom_report_hash),
        ),
        (
            "target_axiom_report_hash",
            hash_json(a.target_axiom_report_hash),
        ),
        (
            "source_theorem_index_hash",
            hash_json(a.source_theorem_index_hash),
        ),
        (
            "target_baseline_theorem_index_hash",
            hash_json(a.target_baseline_theorem_index_hash),
        ),
        (
            "target_theorem_index_hash",
            hash_json(a.target_theorem_index_hash),
        ),
        (
            "source_checker_identities",
            json_array(
                a.source_checker_identities
                    .iter()
                    .map(|value| json_string(value))
                    .collect(),
            ),
        ),
        (
            "target_baseline_checker_identities",
            json_array(
                a.target_baseline_checker_identities
                    .iter()
                    .map(|value| json_string(value))
                    .collect(),
            ),
        ),
        (
            "target_checker_identities",
            json_array(
                a.target_checker_identities
                    .iter()
                    .map(|value| json_string(value))
                    .collect(),
            ),
        ),
        (
            "changed_paths",
            json_array(
                a.changed_paths
                    .iter()
                    .map(|changed| {
                        json_object_in_order(vec![
                            ("path", json_string(changed.path.as_str())),
                            (
                                "baseline_file_hash",
                                changed
                                    .baseline_file_hash
                                    .map_or_else(|| "null".to_owned(), hash_json),
                            ),
                            ("target_file_hash", hash_json(changed.target_file_hash)),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "module_pairs",
            json_array(
                a.module_pairs
                    .iter()
                    .map(|pair| {
                        json_object_in_order(vec![
                            ("role", json_string(pair.role.as_str())),
                            (
                                "source_module",
                                json_string(&pair.source_module.as_dotted()),
                            ),
                            (
                                "target_module",
                                json_string(&pair.target_module.as_dotted()),
                            ),
                            (
                                "source_source_file_hash",
                                pair.source_source_file_hash
                                    .map_or_else(|| "null".to_owned(), hash_json),
                            ),
                            (
                                "target_source_file_hash",
                                hash_json(pair.target_source_file_hash),
                            ),
                            (
                                "source_certificate_file_hash",
                                hash_json(pair.source_certificate_file_hash),
                            ),
                            (
                                "target_certificate_file_hash",
                                hash_json(pair.target_certificate_file_hash),
                            ),
                            (
                                "source_certificate_hash",
                                hash_json(pair.source_certificate_hash),
                            ),
                            (
                                "target_certificate_hash",
                                hash_json(pair.target_certificate_hash),
                            ),
                            ("source_export_hash", hash_json(pair.source_export_hash)),
                            ("target_export_hash", hash_json(pair.target_export_hash)),
                            (
                                "source_axiom_report_hash",
                                hash_json(pair.source_axiom_report_hash),
                            ),
                            (
                                "target_axiom_report_hash",
                                hash_json(pair.target_axiom_report_hash),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "theorem_pairs",
            json_array(
                a.theorem_pairs
                    .iter()
                    .map(|pair| {
                        json_object_in_order(vec![
                            (
                                "source_module",
                                json_string(&pair.source_module.as_dotted()),
                            ),
                            (
                                "source_theorem",
                                json_string(&pair.source_theorem.as_dotted()),
                            ),
                            (
                                "source_statement_hash",
                                hash_json(pair.source_statement_hash),
                            ),
                            (
                                "target_module",
                                json_string(&pair.target_module.as_dotted()),
                            ),
                            (
                                "target_theorem",
                                json_string(&pair.target_theorem.as_dotted()),
                            ),
                            (
                                "target_statement_hash",
                                hash_json(pair.target_statement_hash),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("derived_mapping_hash", hash_json(a.derived_mapping_hash)),
        (
            "normalized_closure_hash",
            hash_json(a.normalized_closure_hash),
        ),
        ("status", json_string(&a.status)),
        ("proof_evidence", json_bool(a.proof_evidence)),
    ])
}
fn policy_json(p: &L2NamespaceTransportPolicy) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&p.schema)),
        ("policy_id", json_string(&p.policy_id)),
        ("policy_version", json_u64(p.policy_version)),
        ("validator_profile", json_string(&p.validator_profile)),
        ("transport_profile", json_string(&p.transport_profile)),
        (
            "source_acceptance_policy_id",
            json_string(&p.source_acceptance_policy_id),
        ),
        (
            "source_acceptance_policy_version",
            json_u64(p.source_acceptance_policy_version),
        ),
        (
            "source_acceptance_policy_file_hash",
            hash_json(p.source_acceptance_policy_file_hash),
        ),
        ("target_package", json_string(p.target_package.as_str())),
        (
            "allowed_source_prefixes",
            json_array(
                p.allowed_source_prefixes
                    .iter()
                    .map(|x| json_string(x))
                    .collect(),
            ),
        ),
        (
            "allowed_target_prefixes",
            json_array(
                p.allowed_target_prefixes
                    .iter()
                    .map(|x| json_string(x))
                    .collect(),
            ),
        ),
        (
            "allow_declaration_renames",
            json_bool(p.allow_declaration_renames),
        ),
        (
            "allow_module_split_or_merge",
            json_bool(p.allow_module_split_or_merge),
        ),
        (
            "require_source_free_reference_verification",
            json_bool(p.require_source_free_reference_verification),
        ),
        ("proof_evidence", json_bool(p.proof_evidence)),
    ])
}
fn request_json(r: &L2NamespaceTransportRequest) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&r.schema)),
        ("source", identity_json(&r.source)),
        ("target", identity_json(&r.target)),
        (
            "module_mappings",
            json_array(
                r.module_mappings
                    .iter()
                    .map(|m| {
                        json_object_in_order(vec![
                            ("role", json_string(m.role.as_str())),
                            ("source", endpoint_json(&m.source)),
                            ("target", endpoint_json(&m.target)),
                            ("declaration_mapping", json_string(&m.declaration_mapping)),
                            (
                                "renames",
                                json_array(
                                    m.renames
                                        .iter()
                                        .map(|x| {
                                            json_object_in_order(vec![
                                                ("source", json_string(&x.source.as_dotted())),
                                                ("target", json_string(&x.target.as_dotted())),
                                            ])
                                        })
                                        .collect(),
                                ),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("proof_evidence", json_bool(r.proof_evidence)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(seed: u8) -> PackageHash {
        PackageHash::from([seed; 32])
    }

    #[test]
    fn transport_policy_and_request_round_trip_canonically() {
        let policy = L2NamespaceTransportPolicy {
            schema: L2_NAMESPACE_TRANSPORT_POLICY_SCHEMA.to_owned(),
            policy_id: "finitefield-org.npa-mathlib.l2-namespace-transport".to_owned(),
            policy_version: 1,
            validator_profile: "npa.l2_namespace_transport.validator.v1".to_owned(),
            transport_profile: "canonical-certificate-global-rename-only.v1".to_owned(),
            source_acceptance_policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
            source_acceptance_policy_version: 2,
            source_acceptance_policy_file_hash: hash(1),
            target_package: PackageId::new("npa-mathlib"),
            allowed_source_prefixes: vec!["Proofs.Ai.".to_owned()],
            allowed_target_prefixes: vec!["Mathlib.".to_owned()],
            allow_declaration_renames: true,
            allow_module_split_or_merge: false,
            require_source_free_reference_verification: true,
            proof_evidence: false,
        };
        let policy_json = policy.canonical_json().unwrap();
        assert_eq!(
            parse_l2_namespace_transport_policy_json(&policy_json).unwrap(),
            policy
        );

        let request = L2NamespaceTransportRequest {
            schema: L2_NAMESPACE_TRANSPORT_REQUEST_SCHEMA.to_owned(),
            source: L2TransportPackageIdentity {
                package: PackageId::new("npa-proof-corpus"),
                version: PackageVersion::new("0.1.0"),
            },
            target: L2TransportPackageIdentity {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.2"),
            },
            module_mappings: vec![L2TransportModuleMapping {
                role: L2TransportModuleRole::Selected,
                source: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: PackageId::new("npa-proof-corpus"),
                    version: PackageVersion::new("0.1.0"),
                    module: Name::from_dotted("Proofs.Ai.Finite"),
                },
                target: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: PackageId::new("npa-mathlib"),
                    version: PackageVersion::new("0.2.2"),
                    module: Name::from_dotted("Mathlib.Finite"),
                },
                declaration_mapping: "same-name-except-explicit".to_owned(),
                renames: vec![L2TransportDeclarationRename {
                    source: Name::from_dotted("old_name"),
                    target: Name::from_dotted("public_name"),
                }],
            }],
            proof_evidence: false,
        };
        let json = request.canonical_json().unwrap();
        assert_eq!(
            parse_l2_namespace_transport_request_json(&json).unwrap(),
            request
        );
        assert_eq!(
            request.map_global(
                &Name::from_dotted("Proofs.Ai.Finite"),
                &Name::from_dotted("old_name")
            ),
            Some((
                Name::from_dotted("Mathlib.Finite"),
                Name::from_dotted("public_name")
            ))
        );

        let attestation = L2NamespaceTransportAttestation {
            schema: L2_NAMESPACE_TRANSPORT_ATTESTATION_SCHEMA.to_owned(),
            transport_policy_id: policy.policy_id.clone(),
            transport_policy_version: 1,
            transport_policy_file_hash: hash(2),
            acceptance_policy_id: policy.source_acceptance_policy_id.clone(),
            acceptance_policy_version: 2,
            acceptance_policy_file_hash: hash(3),
            mapping_request_file_hash: hash(4),
            source_acceptance_file_hash: hash(5),
            source_package: request.source.package.clone(),
            source_version: request.source.version.clone(),
            target_baseline_version: PackageVersion::new("0.2.1"),
            target_package: request.target.package.clone(),
            target_version: request.target.version.clone(),
            source_manifest_hash: hash(6),
            target_baseline_manifest_hash: hash(7),
            target_manifest_hash: hash(8),
            source_lock_hash: hash(9),
            target_baseline_lock_hash: hash(10),
            target_lock_hash: hash(11),
            source_axiom_report_hash: hash(12),
            target_baseline_axiom_report_hash: hash(13),
            target_axiom_report_hash: hash(14),
            source_theorem_index_hash: hash(15),
            target_baseline_theorem_index_hash: hash(16),
            target_theorem_index_hash: hash(17),
            source_checker_identities: vec!["npa-checker-ref:reference.v1:reference".to_owned()],
            target_baseline_checker_identities: vec![
                "npa-checker-ref:reference.v1:reference".to_owned()
            ],
            target_checker_identities: vec!["npa-checker-ref:reference.v1:reference".to_owned()],
            changed_paths: vec![L2TransportAttestationChangedPath {
                path: PackagePath::new("generated/theorem-index.json"),
                baseline_file_hash: Some(hash(18)),
                target_file_hash: hash(19),
            }],
            module_pairs: vec![L2TransportAttestationModulePair {
                role: L2TransportModuleRole::Selected,
                source_module: Name::from_dotted("Proofs.Ai.Finite"),
                target_module: Name::from_dotted("Mathlib.Finite"),
                source_source_file_hash: Some(hash(20)),
                target_source_file_hash: hash(21),
                source_certificate_file_hash: hash(22),
                target_certificate_file_hash: hash(23),
                source_certificate_hash: hash(24),
                target_certificate_hash: hash(25),
                source_export_hash: hash(26),
                target_export_hash: hash(27),
                source_axiom_report_hash: hash(28),
                target_axiom_report_hash: hash(29),
            }],
            theorem_pairs: vec![L2TransportAttestationTheoremPair {
                source_module: Name::from_dotted("Proofs.Ai.Finite"),
                source_theorem: Name::from_dotted("finite"),
                source_statement_hash: hash(30),
                target_module: Name::from_dotted("Mathlib.Finite"),
                target_theorem: Name::from_dotted("finite"),
                target_statement_hash: hash(31),
            }],
            derived_mapping_hash: hash(32),
            normalized_closure_hash: hash(33),
            status: "accepted_namespace_transport".to_owned(),
            proof_evidence: false,
        };
        let json = attestation.canonical_json().unwrap();
        assert_eq!(
            parse_l2_namespace_transport_attestation_json(&json).unwrap(),
            attestation
        );
    }

    #[test]
    fn declaration_inventory_includes_and_renames_generated_exports() {
        let certificate = std::fs::read(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert",
        ))
        .unwrap();
        let cert = npa_cert::verify_module_cert_hashes(&certificate).unwrap();
        let source_declarations = cert
            .declarations
            .iter()
            .map(|declaration| cert.name_table[decl_name_id(&declaration.decl)].clone())
            .collect::<BTreeSet<_>>();
        let generated = cert
            .export_block
            .iter()
            .map(|entry| cert.name_table[entry.name].clone())
            .find(|name| !source_declarations.contains(name))
            .expect("fixture must contain a generated export");
        let renamed = Name::from_dotted("renamed_generated_export");
        let request = L2NamespaceTransportRequest {
            schema: L2_NAMESPACE_TRANSPORT_REQUEST_SCHEMA.to_owned(),
            source: L2TransportPackageIdentity {
                package: PackageId::new("npa-std"),
                version: PackageVersion::new("0.1.0"),
            },
            target: L2TransportPackageIdentity {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.2"),
            },
            module_mappings: vec![L2TransportModuleMapping {
                role: L2TransportModuleRole::Dependency,
                source: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: PackageId::new("npa-std"),
                    version: PackageVersion::new("0.1.0"),
                    module: cert.header.module.clone(),
                },
                target: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: PackageId::new("npa-mathlib"),
                    version: PackageVersion::new("0.2.2"),
                    module: Name::from_dotted("Mathlib.Data.Nat.Basic"),
                },
                declaration_mapping: "same-name-except-explicit".to_owned(),
                renames: vec![L2TransportDeclarationRename {
                    source: generated,
                    target: renamed.clone(),
                }],
            }],
            proof_evidence: false,
        };
        let names = l2_transport_module_declaration_names(&cert, &request, true).unwrap();
        assert_eq!(names.len(), cert.export_block.len());
        assert!(names.contains(&renamed));

        let certificates = BTreeMap::from([(cert.header.module.clone(), cert.clone())]);
        let mapped_hash = l2_transport_derived_mapping_hash(&request, &certificates).unwrap();
        let mut changed = request.clone();
        changed.module_mappings[0].renames[0].target =
            Name::from_dotted("another_generated_export");
        let changed_hash = l2_transport_derived_mapping_hash(&changed, &certificates).unwrap();
        assert_ne!(mapped_hash, changed_hash);
    }
}

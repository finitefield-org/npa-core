//! Canonical governance attestation for one catalog registry reconciliation.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_string, required_u64, required_value,
        validate_module_name,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, parse_package_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::validate_package_path,
    promotion_registry_v3::{
        catalog_target_revision_hash, CatalogChangeEvent, CatalogChangeRequestRef,
        CatalogGovernanceFileRef, CatalogTargetProjection,
    },
    schema::{
        MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA, MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA,
        MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA, MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA,
    },
};

const DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-REGISTRY-SYNC-ATTESTATION-v1\0";
const COMMAND: &str = "package reconcile-promotion-origin-registry";
const FIELDS: &[&str] = &[
    "schema",
    "command",
    "input_registry",
    "previous_target",
    "target",
    "change_set_hash",
    "audit",
    "request",
    "comparisons",
    "unchanged_count",
    "revised_count",
    "added_count",
    "lifecycle_change_count",
    "gates",
    "attestation_hash",
    "proof_evidence",
];
const INPUT_FIELDS: &[&str] = &["schema", "file_hash", "registry_hash"];
const FILE_FIELDS: &[&str] = &["path", "file_hash"];
const REQUEST_FIELDS: &[&str] = &["path", "file_hash", "request_hash"];
const COMPARISON_FIELDS: &[&str] = &[
    "module",
    "status",
    "owner_id",
    "old_revision_hash",
    "new_revision_hash",
];
const PROJECTION_FIELDS: &[&str] = &[
    "package",
    "version",
    "manifest_file_hash",
    "package_lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
    "export_summary_file_hash",
    "publish_plan_file_hash",
];
const MAX_COMPARISONS: usize = 4096;
const REQUIRED_GATES: &[&str] = &[
    "previous:package_check",
    "previous:package_check_hashes",
    "previous:package_build_certs_check_full_cache_off",
    "previous:package_verify_certs_reference_audit_cache_off_verifier_memo_off_jobs_1_checked_lock",
    "previous:checked_axiom_report",
    "previous:checked_theorem_index",
    "current:package_check",
    "current:package_check_hashes",
    "current:package_build_certs_check_full_cache_off",
    "current:package_verify_certs_reference_audit_cache_off_verifier_memo_off_jobs_1_checked_lock",
    "current:checked_axiom_report",
    "current:checked_theorem_index",
    "current:checked_export_summary",
    "current:checked_publish_plan",
];

/// Exact identity of the registry consumed by reconciliation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogRegistryInputIdentity {
    /// Input registry schema.
    pub schema: String,
    /// Exact canonical input file hash.
    pub file_hash: PackageHash,
    /// Input registry self-hash.
    pub registry_hash: PackageHash,
}

/// One module-level comparison recorded in the attestation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogRegistryComparison {
    /// Public module name.
    pub module: Name,
    /// Deterministic comparison status.
    pub status: String,
    /// Effective owner ID, when present.
    pub owner_id: Option<PackageHash>,
    /// Previous effective revision hash, when present.
    pub old_revision_hash: Option<PackageHash>,
    /// New effective revision hash, when present.
    pub new_revision_hash: Option<PackageHash>,
}

/// Canonical catalog reconciliation attestation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogRegistrySyncAttestation {
    /// Exact schema.
    pub schema: String,
    /// Exact producing command.
    pub command: String,
    /// Input registry identity.
    pub input_registry: CatalogRegistryInputIdentity,
    /// Previous checked target projection.
    pub previous_target: CatalogTargetProjection,
    /// Current checked target projection.
    pub target: CatalogTargetProjection,
    /// Event change-set hash.
    pub change_set_hash: PackageHash,
    /// Audit reference.
    pub audit: CatalogGovernanceFileRef,
    /// Optional lifecycle request reference.
    pub request: Option<CatalogChangeRequestRef>,
    /// Complete sorted module comparison.
    pub comparisons: Vec<CatalogRegistryComparison>,
    /// Number of unchanged modules.
    pub unchanged_count: u64,
    /// Number of revised routes.
    pub revised_count: u64,
    /// Number of added targets.
    pub added_count: u64,
    /// Number of lifecycle changes.
    pub lifecycle_change_count: u64,
    /// Exact successful gate inventory.
    pub gates: Vec<String>,
    /// Domain-separated self-hash.
    pub attestation_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl CatalogRegistrySyncAttestation {
    /// Create the fixed successful gate inventory.
    pub fn required_gates() -> Vec<String> {
        REQUIRED_GATES
            .iter()
            .map(|gate| (*gate).to_owned())
            .collect()
    }

    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_catalog_registry_sync_attestation(self)?;
        Ok(format!("{}\n", attestation_json(self)))
    }

    /// Recompute the domain-separated self-hash.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.attestation_hash = catalog_registry_sync_attestation_hash(self)?;
        Ok(())
    }
}

/// Parse and validate one strict canonical reconciliation attestation.
pub fn parse_catalog_registry_sync_attestation_json(
    source: &str,
) -> PackageArtifactResult<CatalogRegistrySyncAttestation> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, FIELDS)?;
    let input = expect_object(
        required_value(members, "$", "input_registry")?,
        "$.input_registry",
    )?;
    reject_unknown_fields("$.input_registry", input, INPUT_FIELDS)?;
    let audit = expect_object(required_value(members, "$", "audit")?, "$.audit")?;
    reject_unknown_fields("$.audit", audit, FILE_FIELDS)?;
    let request = match required_value(members, "$", "request")? {
        JsonValue::Null => None,
        value => {
            let request = expect_object(value, "$.request")?;
            reject_unknown_fields("$.request", request, REQUEST_FIELDS)?;
            Some(CatalogChangeRequestRef {
                path: crate::artifacts::required_path(request, "$.request", "path")?,
                file_hash: required_hash(request, "$.request", "file_hash")?,
                request_hash: required_hash(request, "$.request", "request_hash")?,
            })
        }
    };
    let comparison_values = required_array(members, "$", "comparisons")?;
    if comparison_values.len() > MAX_COMPARISONS {
        return Err(invalid());
    }
    let comparisons = comparison_values
        .iter()
        .enumerate()
        .map(|(index, value)| parse_comparison(value, &format!("$.comparisons[{index}]")))
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    let gate_values = required_array(members, "$", "gates")?;
    if gate_values.len() != REQUIRED_GATES.len() {
        return Err(invalid());
    }
    let gates = gate_values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(str::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("$.gates[{index}]"),
                    Some("gates".to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    let attestation = CatalogRegistrySyncAttestation {
        schema: required_string(members, "$", "schema")?,
        command: required_string(members, "$", "command")?,
        input_registry: CatalogRegistryInputIdentity {
            schema: required_string(input, "$.input_registry", "schema")?,
            file_hash: required_hash(input, "$.input_registry", "file_hash")?,
            registry_hash: required_hash(input, "$.input_registry", "registry_hash")?,
        },
        previous_target: parse_projection(
            required_value(members, "$", "previous_target")?,
            "$.previous_target",
        )?,
        target: parse_projection(required_value(members, "$", "target")?, "$.target")?,
        change_set_hash: required_hash(members, "$", "change_set_hash")?,
        audit: CatalogGovernanceFileRef {
            path: crate::artifacts::required_path(audit, "$.audit", "path")?,
            file_hash: required_hash(audit, "$.audit", "file_hash")?,
        },
        request,
        comparisons,
        unchanged_count: required_u64(members, "$", "unchanged_count")?,
        revised_count: required_u64(members, "$", "revised_count")?,
        added_count: required_u64(members, "$", "added_count")?,
        lifecycle_change_count: required_u64(members, "$", "lifecycle_change_count")?,
        gates,
        attestation_hash: required_hash(members, "$", "attestation_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_catalog_registry_sync_attestation(&attestation)?;
    if source != attestation.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "canonical catalog reconciliation attestation",
        ));
    }
    Ok(attestation)
}

/// Compute the domain-separated attestation self-hash.
pub fn catalog_registry_sync_attestation_hash(
    attestation: &CatalogRegistrySyncAttestation,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = attestation.clone();
    copy.attestation_hash = PackageHash::new([0; 32]);
    validate_shape(&copy, false)?;
    let mut bytes = DOMAIN.to_vec();
    bytes.extend_from_slice(attestation_json(&copy).as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Validate attestation shape, inventories, counts, and self-hash.
pub fn validate_catalog_registry_sync_attestation(
    attestation: &CatalogRegistrySyncAttestation,
) -> PackageArtifactResult<()> {
    validate_shape(attestation, true)
}

/// Validate that an attestation describes the supplied registry event exactly.
pub fn validate_catalog_registry_sync_attestation_against_event(
    attestation: &CatalogRegistrySyncAttestation,
    event: &CatalogChangeEvent,
) -> PackageArtifactResult<()> {
    validate_catalog_registry_sync_attestation(attestation)?;
    if attestation.input_registry.file_hash != event.input_registry_hash
        || attestation.previous_target != event.previous_target
        || attestation.target != event.target
        || attestation.change_set_hash != event.change_set_hash
        || attestation.audit != event.audit
        || attestation.request != event.request
        || attestation.revised_count != event.revised_routes.len() as u64
        || attestation.added_count != event.added_targets.len() as u64
        || attestation.lifecycle_change_count != event.lifecycle_changes.len() as u64
        || attestation.attestation_hash != event.attestation.payload_hash
    {
        return Err(invalid());
    }
    let mut matched_non_unchanged = BTreeSet::new();
    for revised in &event.revised_routes {
        let expected_new = catalog_target_revision_hash(&revised.target_revision)?;
        let row = attestation
            .comparisons
            .iter()
            .find(|row| row.module == revised.target_module)
            .ok_or_else(invalid)?;
        if row.status != "revision_appended"
            || row.owner_id != Some(revised.owner_id)
            || row.old_revision_hash != Some(revised.previous_revision_hash)
            || row.new_revision_hash != Some(expected_new)
        {
            return Err(invalid());
        }
        matched_non_unchanged.insert(row.module.clone());
    }
    for added in &event.added_targets {
        let row = attestation
            .comparisons
            .iter()
            .find(|row| row.module == added.target_module)
            .ok_or_else(invalid)?;
        if row.status != "catalog_target_added"
            || row.owner_id != Some(added.owner_id)
            || row.old_revision_hash.is_some()
            || row.new_revision_hash != Some(added.first_revision_hash)
        {
            return Err(invalid());
        }
        matched_non_unchanged.insert(row.module.clone());
    }
    for lifecycle in &event.lifecycle_changes {
        let expected_status = match lifecycle.kind.as_str() {
            "rename" => "renamed",
            "replacement" => "replaced",
            "split" => "split",
            "merge" => "merged",
            "retirement" => "retired",
            _ => return Err(invalid()),
        };
        for route in &lifecycle.old_routes {
            let row = attestation
                .comparisons
                .iter()
                .find(|row| row.module == route.target_module)
                .ok_or_else(invalid)?;
            if row.status != expected_status || row.owner_id != Some(route.owner_id) {
                return Err(invalid());
            }
            matched_non_unchanged.insert(row.module.clone());
        }
    }
    if attestation.comparisons.iter().any(|row| {
        row.status != "unchanged"
            && row.status != "catalog_target_added"
            && !matched_non_unchanged.contains(&row.module)
    }) {
        return Err(invalid());
    }
    Ok(())
}

/// Validate event binding plus the transition context that is not stored in the event.
///
/// The event intentionally records the input registry file hash, while the
/// attestation also records its canonical self-hash. Callers that possess the
/// input registry must supply that self-hash here. `expected_comparisons` is
/// the complete, independently derived comparison inventory.
pub fn validate_catalog_registry_sync_attestation_against_transition(
    attestation: &CatalogRegistrySyncAttestation,
    event: &CatalogChangeEvent,
    input_registry_hash: PackageHash,
    expected_comparisons: &[CatalogRegistryComparison],
) -> PackageArtifactResult<()> {
    validate_catalog_registry_sync_attestation_against_event(attestation, event)?;
    if attestation.input_registry.registry_hash != input_registry_hash
        || attestation.comparisons != expected_comparisons
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_shape(
    attestation: &CatalogRegistrySyncAttestation,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    const STATUSES: &[&str] = &[
        "unchanged",
        "revision_appended",
        "catalog_target_added",
        "renamed",
        "replaced",
        "split",
        "merged",
        "retired",
    ];
    if attestation.schema != MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA
        || attestation.command != COMMAND
        || !matches!(
            attestation.input_registry.schema.as_str(),
            MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA
                | MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA
                | MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA
        )
        || attestation.proof_evidence
        || attestation.previous_target.package != attestation.target.package
        || !version_greater(
            &attestation.target.version,
            &attestation.previous_target.version,
        )
        || attestation.comparisons.len() > MAX_COMPARISONS
        || attestation
            .comparisons
            .windows(2)
            .any(|pair| pair[0].module >= pair[1].module)
        || attestation
            .comparisons
            .iter()
            .any(|row| !STATUSES.contains(&row.status.as_str()))
        || attestation.gates != CatalogRegistrySyncAttestation::required_gates()
        || attestation.unchanged_count
            != attestation
                .comparisons
                .iter()
                .filter(|row| row.status == "unchanged")
                .count() as u64
        || attestation.revised_count
            != attestation
                .comparisons
                .iter()
                .filter(|row| row.status == "revision_appended")
                .count() as u64
        || attestation.added_count
            != attestation
                .comparisons
                .iter()
                .filter(|row| row.status == "catalog_target_added")
                .count() as u64
    {
        return Err(invalid());
    }
    validate_package_path(&attestation.audit.path, "$.audit.path").map_err(|_| invalid())?;
    if let Some(request) = &attestation.request {
        validate_package_path(&request.path, "$.request.path").map_err(|_| invalid())?;
    }
    for row in &attestation.comparisons {
        validate_module_name(&row.module, "$.comparisons.module")?;
        let valid_identity_shape = match row.status.as_str() {
            "unchanged" => {
                row.owner_id.is_some()
                    && row.old_revision_hash.is_some()
                    && row.old_revision_hash == row.new_revision_hash
            }
            "revision_appended" => {
                row.owner_id.is_some()
                    && row.old_revision_hash.is_some()
                    && row.new_revision_hash.is_some()
                    && row.old_revision_hash != row.new_revision_hash
            }
            "catalog_target_added" => {
                row.owner_id.is_some()
                    && row.old_revision_hash.is_none()
                    && row.new_revision_hash.is_some()
            }
            _ => {
                row.owner_id.is_some()
                    && row.old_revision_hash.is_some()
                    && row.new_revision_hash.is_none()
            }
        };
        if !valid_identity_shape {
            return Err(invalid());
        }
    }
    if check_hash
        && attestation.attestation_hash != catalog_registry_sync_attestation_hash(attestation)?
    {
        return Err(invalid());
    }
    Ok(())
}

fn parse_comparison(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogRegistryComparison> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, COMPARISON_FIELDS)?;
    Ok(CatalogRegistryComparison {
        module: required_name(members, path, "module")?,
        status: required_string(members, path, "status")?,
        owner_id: optional_hash(required_value(members, path, "owner_id")?, path)?,
        old_revision_hash: optional_hash(
            required_value(members, path, "old_revision_hash")?,
            path,
        )?,
        new_revision_hash: optional_hash(
            required_value(members, path, "new_revision_hash")?,
            path,
        )?,
    })
}

fn parse_projection(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogTargetProjection> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, PROJECTION_FIELDS)?;
    Ok(CatalogTargetProjection {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        package_lock_file_hash: required_hash(members, path, "package_lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
        export_summary_file_hash: required_hash(members, path, "export_summary_file_hash")?,
        publish_plan_file_hash: required_hash(members, path, "publish_plan_file_hash")?,
    })
}

fn optional_hash(value: &JsonValue, path: &str) -> PackageArtifactResult<Option<PackageHash>> {
    match value {
        JsonValue::Null => Ok(None),
        JsonValue::String(value) => parse_package_hash(value, path)
            .map(Some)
            .map_err(|_| PackageArtifactError::invalid_hash_format(path, value)),
        _ => Err(PackageArtifactError::wrong_type(
            path,
            None,
            "hash string or null",
            value.kind().as_str(),
        )),
    }
}

fn attestation_json(attestation: &CatalogRegistrySyncAttestation) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&attestation.schema)),
        ("command", json_string(&attestation.command)),
        (
            "input_registry",
            json_object_in_order(vec![
                ("schema", json_string(&attestation.input_registry.schema)),
                ("file_hash", hash_json(attestation.input_registry.file_hash)),
                (
                    "registry_hash",
                    hash_json(attestation.input_registry.registry_hash),
                ),
            ]),
        ),
        (
            "previous_target",
            projection_json(&attestation.previous_target),
        ),
        ("target", projection_json(&attestation.target)),
        ("change_set_hash", hash_json(attestation.change_set_hash)),
        (
            "audit",
            json_object_in_order(vec![
                ("path", json_string(attestation.audit.path.as_str())),
                ("file_hash", hash_json(attestation.audit.file_hash)),
            ]),
        ),
        (
            "request",
            attestation.request.as_ref().map_or_else(
                || "null".to_owned(),
                |request| {
                    json_object_in_order(vec![
                        ("path", json_string(request.path.as_str())),
                        ("file_hash", hash_json(request.file_hash)),
                        ("request_hash", hash_json(request.request_hash)),
                    ])
                },
            ),
        ),
        (
            "comparisons",
            json_array(
                attestation
                    .comparisons
                    .iter()
                    .map(comparison_json)
                    .collect(),
            ),
        ),
        ("unchanged_count", json_u64(attestation.unchanged_count)),
        ("revised_count", json_u64(attestation.revised_count)),
        ("added_count", json_u64(attestation.added_count)),
        (
            "lifecycle_change_count",
            json_u64(attestation.lifecycle_change_count),
        ),
        (
            "gates",
            json_array(
                attestation
                    .gates
                    .iter()
                    .map(|gate| json_string(gate))
                    .collect(),
            ),
        ),
        ("attestation_hash", hash_json(attestation.attestation_hash)),
        ("proof_evidence", json_bool(attestation.proof_evidence)),
    ])
}

fn comparison_json(row: &CatalogRegistryComparison) -> String {
    let optional = |value: Option<PackageHash>| value.map_or_else(|| "null".to_owned(), hash_json);
    json_object_in_order(vec![
        ("module", json_string(&row.module.as_dotted())),
        ("status", json_string(&row.status)),
        ("owner_id", optional(row.owner_id)),
        ("old_revision_hash", optional(row.old_revision_hash)),
        ("new_revision_hash", optional(row.new_revision_hash)),
    ])
}

fn projection_json(projection: &CatalogTargetProjection) -> String {
    json_object_in_order(vec![
        ("package", json_string(projection.package.as_str())),
        ("version", json_string(projection.version.as_str())),
        (
            "manifest_file_hash",
            hash_json(projection.manifest_file_hash),
        ),
        (
            "package_lock_file_hash",
            hash_json(projection.package_lock_file_hash),
        ),
        (
            "axiom_report_file_hash",
            hash_json(projection.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(projection.theorem_index_file_hash),
        ),
        (
            "export_summary_file_hash",
            hash_json(projection.export_summary_file_hash),
        ),
        (
            "publish_plan_file_hash",
            hash_json(projection.publish_plan_file_hash),
        ),
    ])
}

fn invalid() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "catalog_registry_sync_attestation",
        "canonical event-bound attestation",
        "mismatch",
    )
}

fn version_greater(left: &PackageVersion, right: &PackageVersion) -> bool {
    let parse = |value: &PackageVersion| {
        let parts = value
            .as_str()
            .split('.')
            .map(str::parse::<u64>)
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        (parts.len() == 3).then(|| (parts[0], parts[1], parts[2]))
    };
    parse(left)
        .zip(parse(right))
        .is_some_and(|(left, right)| left > right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        name::PackageId,
        path::PackagePath,
        promotion_registry_v3::{CatalogAttestationRef, CatalogTargetProjection},
    };

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }

    fn event() -> CatalogChangeEvent {
        CatalogChangeEvent {
            event_id: hash(1),
            kind: "catalog_registry_sync_v1".to_owned(),
            input_registry_hash: hash(2),
            change_set_hash: hash(3),
            previous_target: projection("0.2.1"),
            target: projection("0.2.4"),
            audit: CatalogGovernanceFileRef {
                path: PackagePath::new("docs/promotion/audit.md"),
                file_hash: hash(4),
            },
            request: None,
            attestation: CatalogAttestationRef {
                path: PackagePath::new("docs/promotion/sync.json"),
                payload_hash: hash(0),
            },
            revised_routes: Vec::new(),
            added_targets: Vec::new(),
            lifecycle_changes: Vec::new(),
        }
    }

    fn projection(version: &str) -> CatalogTargetProjection {
        CatalogTargetProjection {
            package: PackageId::new("npa-mathlib"),
            version: PackageVersion::new(version),
            manifest_file_hash: hash(10),
            package_lock_file_hash: hash(11),
            axiom_report_file_hash: hash(12),
            theorem_index_file_hash: hash(13),
            export_summary_file_hash: hash(14),
            publish_plan_file_hash: hash(15),
        }
    }

    #[test]
    fn strict_round_trip_and_event_binding() {
        let mut event = event();
        let mut value = CatalogRegistrySyncAttestation {
            schema: MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA.to_owned(),
            command: COMMAND.to_owned(),
            input_registry: CatalogRegistryInputIdentity {
                schema: "npa.mathlib.promotion_origin_registry.v1".to_owned(),
                file_hash: event.input_registry_hash,
                registry_hash: hash(20),
            },
            previous_target: event.previous_target.clone(),
            target: event.target.clone(),
            change_set_hash: event.change_set_hash,
            audit: event.audit.clone(),
            request: None,
            comparisons: Vec::new(),
            unchanged_count: 0,
            revised_count: 0,
            added_count: 0,
            lifecycle_change_count: 0,
            gates: CatalogRegistrySyncAttestation::required_gates(),
            attestation_hash: hash(0),
            proof_evidence: false,
        };
        value.refresh_hash().unwrap();
        event.attestation.payload_hash = value.attestation_hash;
        let json = value.canonical_json().unwrap();
        let parsed = parse_catalog_registry_sync_attestation_json(&json).unwrap();
        validate_catalog_registry_sync_attestation_against_event(&parsed, &event).unwrap();
        assert!(parse_catalog_registry_sync_attestation_json(&json.replacen(
            "\"command\":",
            "\"unknown\":false,\"command\":",
            1
        ))
        .is_err());
    }

    #[test]
    fn transition_binding_rejects_wrong_registry_and_incomplete_inventory() {
        let mut event = event();
        let module = Name::from_dotted("Mathlib.Example");
        let mut value = CatalogRegistrySyncAttestation {
            schema: MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA.to_owned(),
            command: COMMAND.to_owned(),
            input_registry: CatalogRegistryInputIdentity {
                schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA.to_owned(),
                file_hash: event.input_registry_hash,
                registry_hash: hash(20),
            },
            previous_target: event.previous_target.clone(),
            target: event.target.clone(),
            change_set_hash: event.change_set_hash,
            audit: event.audit.clone(),
            request: None,
            comparisons: Vec::new(),
            unchanged_count: 0,
            revised_count: 0,
            added_count: 0,
            lifecycle_change_count: 0,
            gates: CatalogRegistrySyncAttestation::required_gates(),
            attestation_hash: hash(0),
            proof_evidence: false,
        };
        value.refresh_hash().unwrap();
        event.attestation.payload_hash = value.attestation_hash;

        assert!(
            validate_catalog_registry_sync_attestation_against_transition(
                &value,
                &event,
                hash(21),
                &[],
            )
            .is_err()
        );
        assert!(
            validate_catalog_registry_sync_attestation_against_transition(
                &value,
                &event,
                hash(20),
                &[CatalogRegistryComparison {
                    module,
                    status: "unchanged".to_owned(),
                    owner_id: Some(hash(30)),
                    old_revision_hash: Some(hash(31)),
                    new_revision_hash: Some(hash(31)),
                }],
            )
            .is_err()
        );
    }
}

//! Catalog-change-aware mathlib promotion-origin registry v3.
//!
//! V3 preserves v1/v2 source-owned rows, adds explicit target-only owners, and
//! records later target revisions and lifecycle changes as immutable overlays.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_path, required_string, required_u64, required_value,
        validate_module_name,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    promotion_registry::{
        parse_reservation as parse_v1_reservation, reservation_json as v1_reservation_json,
        PromotionLegacyTargetReservation, PromotionOriginLookup, PromotionOriginRegistry,
        MATHLIB_PROMOTION_REGISTRY_ID,
    },
    promotion_registry_v2::{
        entry_json as v2_entry_json, migrate_promotion_origin_registry_v1_to_v2,
        parse_entry as parse_v2_entry, parse_revision, revision_json,
        validate_promotion_origin_registry_v2, validate_promotion_origin_registry_v2_transition,
        PromotionDeclarationTargetRevision, PromotionOriginEntryV2, PromotionOriginRegistryV2,
    },
    schema::{
        MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA, MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA,
    },
};

const REGISTRY_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-ORIGIN-REGISTRY-v3\0";
const CATALOG_TARGET_DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-TARGET-v1\0";
const REVISION_DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-TARGET-REVISION-v1\0";
const CHANGE_SET_DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-CHANGE-SET-v1\0";
const EVENT_DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-CHANGE-EVENT-v1\0";

const REGISTRY_FIELDS: &[&str] = &[
    "schema",
    "registry_id",
    "registry_version",
    "generation",
    "target_package",
    "entries",
    "unresolved_legacy_targets",
    "catalog_change_events",
    "registry_hash",
    "proof_evidence",
];
const CATALOG_ENTRY_FIELDS: &[&str] = &[
    "kind",
    "catalog_target_id",
    "lifecycle",
    "introduced_version",
    "target_module",
    "first_revision",
    "evidence",
];
const CATALOG_EVIDENCE_FIELDS: &[&str] =
    &["kind", "audit_path", "audit_file_hash", "change_set_hash"];
const EVENT_FIELDS: &[&str] = &[
    "event_id",
    "kind",
    "input_registry_hash",
    "change_set_hash",
    "previous_target",
    "target",
    "audit",
    "request",
    "attestation",
    "revised_routes",
    "added_targets",
    "lifecycle_changes",
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
const FILE_REF_FIELDS: &[&str] = &["path", "file_hash"];
const REQUEST_REF_FIELDS: &[&str] = &["path", "file_hash", "request_hash"];
const ATTESTATION_REF_FIELDS: &[&str] = &["path", "payload_hash"];
const REVISED_FIELDS: &[&str] = &[
    "owner_kind",
    "owner_id",
    "target_module",
    "previous_revision_hash",
    "target_revision",
];
const ADDED_FIELDS: &[&str] = &[
    "owner_kind",
    "owner_id",
    "target_module",
    "first_revision_hash",
];
const LIFECYCLE_FIELDS: &[&str] = &["kind", "effective_version", "old_routes", "new_routes"];
const ROUTE_FIELDS: &[&str] = &["owner_kind", "owner_id", "target_module"];

const MAX_ENTRIES: usize = 4096;
const MAX_EVENTS: usize = 4096;
const MAX_EVENT_ROWS: usize = 4096;

/// Exact checked target-package projection bound by one catalog event.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogTargetProjection {
    /// Package ID.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Manifest file hash.
    pub manifest_file_hash: PackageHash,
    /// Package-lock file hash.
    pub package_lock_file_hash: PackageHash,
    /// Axiom-report file hash.
    pub axiom_report_file_hash: PackageHash,
    /// Theorem-index file hash.
    pub theorem_index_file_hash: PackageHash,
    /// Verified-export-summary file hash.
    pub export_summary_file_hash: PackageHash,
    /// Publish-plan file hash.
    pub publish_plan_file_hash: PackageHash,
}

/// Hash-bound governance file reference.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogGovernanceFileRef {
    /// Target-root-relative path.
    pub path: PackagePath,
    /// Exact file hash.
    pub file_hash: PackageHash,
}

/// Optional lifecycle request reference.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogChangeRequestRef {
    /// Target-root-relative path.
    pub path: PackagePath,
    /// Exact file hash.
    pub file_hash: PackageHash,
    /// Canonical request self-hash.
    pub request_hash: PackageHash,
}

/// Reconciliation attestation reference.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogAttestationRef {
    /// Target-root-relative path.
    pub path: PackagePath,
    /// Canonical attestation payload hash.
    pub payload_hash: PackageHash,
}

/// Evidence for one target-only catalog owner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogTargetEvidence {
    /// Exactly `catalog_registry_sync_v1`.
    pub kind: String,
    /// Audit path.
    pub audit_path: PackagePath,
    /// Audit file hash.
    pub audit_file_hash: PackageHash,
    /// Catalog change-set hash.
    pub change_set_hash: PackageHash,
}

/// One explicit target-only catalog owner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogTargetEntry {
    /// Stable owner ID.
    pub catalog_target_id: PackageHash,
    /// Base lifecycle, exactly `active`.
    pub lifecycle: String,
    /// First registry-observed target version.
    pub introduced_version: PackageVersion,
    /// Public target module.
    pub target_module: Name,
    /// First registry-observed artifact identity.
    pub first_revision: PromotionDeclarationTargetRevision,
    /// Governance evidence.
    pub evidence: CatalogTargetEvidence,
}

/// One registry v3 owner variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PromotionOriginEntryV3 {
    /// Losslessly preserved v2 sourced route.
    SourceV2(PromotionOriginEntryV2),
    /// Target-only direct catalog route.
    CatalogTargetV1(Box<CatalogTargetEntry>),
}

impl PromotionOriginEntryV3 {
    /// Stable owner ID.
    pub fn owner_id(&self) -> PackageHash {
        match self {
            Self::SourceV2(entry) => entry.promotion_id(),
            Self::CatalogTargetV1(entry) => entry.catalog_target_id,
        }
    }

    /// Stable owner-kind discriminator.
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::SourceV2(PromotionOriginEntryV2::WholeModuleV1(_)) => "whole_module_v1",
            Self::SourceV2(PromotionOriginEntryV2::DeclarationClosureV1(_)) => {
                "declaration_closure_v1"
            }
            Self::CatalogTargetV1(_) => "catalog_target_v1",
        }
    }
}

/// Exact owner/module route reference used by event overlays.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogRouteRef {
    /// Owner-kind discriminator.
    pub owner_kind: String,
    /// Stable owner ID.
    pub owner_id: PackageHash,
    /// Public target module.
    pub target_module: Name,
}

/// One later target revision overlay.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogRevisedRoute {
    /// Owner-kind discriminator.
    pub owner_kind: String,
    /// Stable owner ID.
    pub owner_id: PackageHash,
    /// Public target module.
    pub target_module: Name,
    /// Hash of the previous effective unified revision.
    pub previous_revision_hash: PackageHash,
    /// Complete new unified target revision.
    pub target_revision: PromotionDeclarationTargetRevision,
}

/// One target owner introduced by an event.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogAddedTarget {
    /// Exactly `catalog_target_v1`.
    pub owner_kind: String,
    /// Stable owner ID.
    pub owner_id: PackageHash,
    /// Public target module.
    pub target_module: Name,
    /// Hash of the first unified target revision.
    pub first_revision_hash: PackageHash,
}

/// One route-level lifecycle relation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogLifecycleChange {
    /// `rename`, `replacement`, `split`, `merge`, or `retirement`.
    pub kind: String,
    /// Target version where the relation becomes effective.
    pub effective_version: PackageVersion,
    /// Active routes retired by this event.
    pub old_routes: Vec<CatalogRouteRef>,
    /// New routes created by this event.
    pub new_routes: Vec<CatalogRouteRef>,
}

/// One immutable catalog synchronization event.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogChangeEvent {
    /// Domain-separated event ID.
    pub event_id: PackageHash,
    /// Exactly `catalog_registry_sync_v1`.
    pub kind: String,
    /// Exact input registry file hash.
    pub input_registry_hash: PackageHash,
    /// Domain-separated change-set hash.
    pub change_set_hash: PackageHash,
    /// Previous target projection.
    pub previous_target: CatalogTargetProjection,
    /// New target projection.
    pub target: CatalogTargetProjection,
    /// Audit reference.
    pub audit: CatalogGovernanceFileRef,
    /// Optional lifecycle request reference.
    pub request: Option<CatalogChangeRequestRef>,
    /// Reconciliation attestation reference.
    pub attestation: CatalogAttestationRef,
    /// Later target revisions.
    pub revised_routes: Vec<CatalogRevisedRoute>,
    /// Newly introduced target-only owners.
    pub added_targets: Vec<CatalogAddedTarget>,
    /// Route-level lifecycle changes.
    pub lifecycle_changes: Vec<CatalogLifecycleChange>,
}

/// Canonical catalog-change-aware promotion-origin registry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionOriginRegistryV3 {
    /// Exact schema.
    pub schema: String,
    /// Stable registry ID.
    pub registry_id: String,
    /// Exactly 3.
    pub registry_version: u64,
    /// Monotonic content generation.
    pub generation: u64,
    /// Target package.
    pub target_package: PackageId,
    /// Sourced and target-only owners.
    pub entries: Vec<PromotionOriginEntryV3>,
    /// Immutable historical unresolved reservations.
    pub unresolved_legacy_targets: Vec<PromotionLegacyTargetReservation>,
    /// Immutable catalog change events.
    pub catalog_change_events: Vec<CatalogChangeEvent>,
    /// Domain-separated self-hash.
    pub registry_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl PromotionOriginRegistryV3 {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_promotion_origin_registry_v3(self)?;
        Ok(format!("{}\n", registry_json(self)))
    }

    /// Recompute the registry self-hash.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.registry_hash = promotion_origin_registry_v3_hash(self)?;
        Ok(())
    }
}

/// Losslessly migrate a v2 registry to v3 without changing generation.
pub fn migrate_promotion_origin_registry_v2_to_v3(
    registry: &PromotionOriginRegistryV2,
) -> PackageArtifactResult<PromotionOriginRegistryV3> {
    validate_promotion_origin_registry_v2(registry)?;
    let mut out = PromotionOriginRegistryV3 {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA.to_owned(),
        registry_id: registry.registry_id.clone(),
        registry_version: 3,
        generation: registry.generation,
        target_package: registry.target_package.clone(),
        entries: registry
            .entries
            .iter()
            .cloned()
            .map(PromotionOriginEntryV3::SourceV2)
            .collect(),
        unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
        catalog_change_events: Vec::new(),
        registry_hash: zero_hash(),
        proof_evidence: false,
    };
    out.refresh_hash()?;
    Ok(out)
}

/// Losslessly migrate a v1 registry to v3 without changing generation.
pub fn migrate_promotion_origin_registry_v1_to_v3(
    registry: &PromotionOriginRegistry,
) -> PackageArtifactResult<PromotionOriginRegistryV3> {
    migrate_promotion_origin_registry_v2_to_v3(&migrate_promotion_origin_registry_v1_to_v2(
        registry,
    )?)
}

/// Parse and validate strict canonical registry v3 JSON.
pub fn parse_promotion_origin_registry_v3_json(
    source: &str,
) -> PackageArtifactResult<PromotionOriginRegistryV3> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, REGISTRY_FIELDS)?;
    let registry = PromotionOriginRegistryV3 {
        schema: required_string(members, "$", "schema")?,
        registry_id: required_string(members, "$", "registry_id")?,
        registry_version: required_u64(members, "$", "registry_version")?,
        generation: required_u64(members, "$", "generation")?,
        target_package: PackageId::new(required_string(members, "$", "target_package")?),
        entries: {
            let values = required_array(members, "$", "entries")?;
            if values.len() > MAX_ENTRIES {
                return Err(PackageArtifactError::invalid_enum_value(
                    "$",
                    "entries",
                    format!("at most {MAX_ENTRIES} rows"),
                    values.len().to_string(),
                ));
            }
            values
                .iter()
                .enumerate()
                .map(|(index, value)| parse_entry(value, index))
                .collect::<PackageArtifactResult<Vec<_>>>()?
        },
        unresolved_legacy_targets: {
            let values = required_array(members, "$", "unresolved_legacy_targets")?;
            if values.len() > MAX_ENTRIES {
                return Err(PackageArtifactError::invalid_enum_value(
                    "$",
                    "unresolved_legacy_targets",
                    format!("at most {MAX_ENTRIES} rows"),
                    values.len().to_string(),
                ));
            }
            values
                .iter()
                .enumerate()
                .map(|(index, value)| parse_v1_reservation(value, index))
                .collect::<PackageArtifactResult<Vec<_>>>()?
        },
        catalog_change_events: parse_bounded_array(
            members,
            "$",
            "catalog_change_events",
            MAX_EVENTS,
            parse_event,
        )?,
        registry_hash: required_hash(members, "$", "registry_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_promotion_origin_registry_v3(&registry)?;
    if source != registry.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "canonical registry v3 JSON bytes",
        ));
    }
    Ok(registry)
}

/// Compute the domain-separated unified target revision hash.
pub fn catalog_target_revision_hash(
    revision: &PromotionDeclarationTargetRevision,
) -> PackageArtifactResult<PackageHash> {
    validate_revision(revision, "revision")?;
    let json = revision_json(revision);
    Ok(domain_hash(REVISION_DOMAIN, &json))
}

/// Compute a stable catalog-target owner ID.
pub fn catalog_target_id(
    target_module: &Name,
    revision: &PromotionDeclarationTargetRevision,
) -> PackageArtifactResult<PackageHash> {
    validate_module_name(target_module, "target_module")?;
    validate_revision(revision, "first_revision")?;
    let json = json_object_in_order(vec![
        ("target_module", json_string(&target_module.as_dotted())),
        ("first_revision", revision_json(revision)),
    ]);
    Ok(domain_hash(CATALOG_TARGET_DOMAIN, &json))
}

/// Compute a catalog event change-set hash.
pub fn catalog_change_set_hash(event: &CatalogChangeEvent) -> PackageArtifactResult<PackageHash> {
    let mut copy = event.clone();
    copy.event_id = zero_hash();
    copy.change_set_hash = zero_hash();
    copy.attestation = CatalogAttestationRef {
        path: PackagePath::new("docs/promotion/attestation-placeholder.json".to_owned()),
        payload_hash: zero_hash(),
    };
    let json = event_json(&copy);
    Ok(domain_hash(CHANGE_SET_DOMAIN, &json))
}

/// Compute a catalog event ID.
pub fn catalog_change_event_id(event: &CatalogChangeEvent) -> PackageArtifactResult<PackageHash> {
    let mut copy = event.clone();
    copy.event_id = zero_hash();
    let json = event_json(&copy);
    Ok(domain_hash(EVENT_DOMAIN, &json))
}

/// Compute the registry v3 self-hash.
pub fn promotion_origin_registry_v3_hash(
    registry: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = registry.clone();
    copy.registry_hash = zero_hash();
    validate_registry_shape(&copy, false)?;
    Ok(domain_hash(REGISTRY_DOMAIN, &registry_json(&copy)))
}

/// Validate registry v3 shape, event overlays, collisions, and self-hash.
pub fn validate_promotion_origin_registry_v3(
    registry: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<()> {
    validate_registry_shape(registry, true)
}

/// Validate one source-backed promotion appended to a registry v3 catalog.
///
/// Source-backed promotion retains the v2 entry contract inside v3. It advances
/// the generation by one without creating a catalog reconciliation event.
pub fn validate_promotion_origin_registry_v3_source_promotion_transition(
    previous: &PromotionOriginRegistryV3,
    next: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<()> {
    validate_promotion_origin_registry_v3(previous)?;
    validate_promotion_origin_registry_v3(next)?;
    if previous.registry_id != next.registry_id
        || previous.target_package != next.target_package
        || next.generation
            != previous
                .generation
                .checked_add(1)
                .ok_or_else(transition_error)?
        || previous.unresolved_legacy_targets != next.unresolved_legacy_targets
        || previous.catalog_change_events != next.catalog_change_events
    {
        return Err(transition_error());
    }

    let source_registry = |registry: &PromotionOriginRegistryV3| {
        let mut source = PromotionOriginRegistryV2 {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
            registry_id: registry.registry_id.clone(),
            registry_version: 2,
            generation: registry.generation,
            target_package: registry.target_package.clone(),
            entries: registry
                .entries
                .iter()
                .filter_map(|entry| match entry {
                    PromotionOriginEntryV3::SourceV2(entry) => Some(entry.clone()),
                    PromotionOriginEntryV3::CatalogTargetV1(_) => None,
                })
                .collect(),
            unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
            registry_hash: zero_hash(),
            proof_evidence: false,
        };
        source.refresh_hash()?;
        Ok::<_, PackageArtifactError>(source)
    };
    validate_promotion_origin_registry_v2_transition(
        &source_registry(previous)?,
        &source_registry(next)?,
    )?;

    let previous_catalog_entries = previous
        .entries
        .iter()
        .filter(|entry| matches!(entry, PromotionOriginEntryV3::CatalogTargetV1(_)))
        .collect::<Vec<_>>();
    let next_catalog_entries = next
        .entries
        .iter()
        .filter(|entry| matches!(entry, PromotionOriginEntryV3::CatalogTargetV1(_)))
        .collect::<Vec<_>>();
    if previous_catalog_entries != next_catalog_entries {
        return Err(transition_error());
    }
    Ok(())
}

/// Validate a lossless v1-to-v3 migration plus one reconciliation event.
pub fn validate_promotion_origin_registry_v1_to_v3_reconciliation(
    previous: &PromotionOriginRegistry,
    next: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<()> {
    let migrated = migrate_promotion_origin_registry_v1_to_v3(previous)?;
    validate_reconciliation_transition(
        &migrated,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        None,
    )
}

/// Validate v1-to-v3 reconciliation using previous-package completion hashes
/// for legacy revisions that did not store meta/replay identities.
pub fn validate_promotion_origin_registry_v1_to_v3_reconciliation_with_previous_hashes(
    previous: &PromotionOriginRegistry,
    next: &PromotionOriginRegistryV3,
    previous_revision_hashes: &BTreeMap<String, PackageHash>,
) -> PackageArtifactResult<()> {
    let migrated = migrate_promotion_origin_registry_v1_to_v3(previous)?;
    validate_reconciliation_transition(
        &migrated,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        Some(previous_revision_hashes),
    )
}

/// Validate a lossless v2-to-v3 migration plus one reconciliation event.
pub fn validate_promotion_origin_registry_v2_to_v3_reconciliation(
    previous: &PromotionOriginRegistryV2,
    next: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<()> {
    let migrated = migrate_promotion_origin_registry_v2_to_v3(previous)?;
    validate_reconciliation_transition(
        &migrated,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        None,
    )
}

/// Validate v2-to-v3 reconciliation with explicit legacy completion hashes.
pub fn validate_promotion_origin_registry_v2_to_v3_reconciliation_with_previous_hashes(
    previous: &PromotionOriginRegistryV2,
    next: &PromotionOriginRegistryV3,
    previous_revision_hashes: &BTreeMap<String, PackageHash>,
) -> PackageArtifactResult<()> {
    let migrated = migrate_promotion_origin_registry_v2_to_v3(previous)?;
    validate_reconciliation_transition(
        &migrated,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        Some(previous_revision_hashes),
    )
}

/// Validate one append-only v3 reconciliation transition.
pub fn validate_promotion_origin_registry_v3_transition(
    previous: &PromotionOriginRegistryV3,
    next: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<()> {
    validate_reconciliation_transition(
        previous,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        None,
    )
}

/// Validate a v3 transition with explicit legacy completion hashes.
pub fn validate_promotion_origin_registry_v3_transition_with_previous_hashes(
    previous: &PromotionOriginRegistryV3,
    next: &PromotionOriginRegistryV3,
    previous_revision_hashes: &BTreeMap<String, PackageHash>,
) -> PackageArtifactResult<()> {
    validate_reconciliation_transition(
        previous,
        next,
        package_file_hash(previous.canonical_json()?.as_bytes()),
        Some(previous_revision_hashes),
    )
}

fn validate_reconciliation_transition(
    previous: &PromotionOriginRegistryV3,
    next: &PromotionOriginRegistryV3,
    expected_input_file_hash: PackageHash,
    previous_revision_hashes: Option<&BTreeMap<String, PackageHash>>,
) -> PackageArtifactResult<()> {
    validate_promotion_origin_registry_v3(previous)?;
    validate_promotion_origin_registry_v3(next)?;
    if previous.registry_id != next.registry_id
        || previous.target_package != next.target_package
        || next.generation
            != previous
                .generation
                .checked_add(1)
                .ok_or_else(transition_error)?
        || previous.unresolved_legacy_targets != next.unresolved_legacy_targets
        || next.catalog_change_events.len() != previous.catalog_change_events.len() + 1
        || !next
            .catalog_change_events
            .starts_with(&previous.catalog_change_events)
    {
        return Err(transition_error());
    }
    let old_entries = previous
        .entries
        .iter()
        .map(|entry| (entry.owner_id(), entry))
        .collect::<BTreeMap<_, _>>();
    let new_entries = next
        .entries
        .iter()
        .map(|entry| (entry.owner_id(), entry))
        .collect::<BTreeMap<_, _>>();
    if old_entries
        .iter()
        .any(|(id, old)| new_entries.get(id).is_none_or(|new| *new != *old))
    {
        return Err(transition_error());
    }
    let event = next
        .catalog_change_events
        .last()
        .ok_or_else(transition_error)?;
    if event.input_registry_hash != expected_input_file_hash {
        return Err(transition_error());
    }
    let previous_routes = effective_routes(previous)?;
    for row in &event.revised_routes {
        let Some(previous_route) = previous_routes.get(&row.target_module.as_dotted()) else {
            return Err(transition_error());
        };
        if legacy_revision_is_incomplete(&previous_route.revision) {
            let expected = previous_revision_hashes
                .and_then(|hashes| hashes.get(&row.target_module.as_dotted()))
                .copied()
                .unwrap_or(catalog_target_revision_hash(&previous_route.revision)?);
            if row.previous_revision_hash != expected {
                return Err(transition_error());
            }
        }
    }
    let added_ids = event
        .added_targets
        .iter()
        .map(|row| row.owner_id)
        .collect::<BTreeSet<_>>();
    let actual_added = new_entries
        .keys()
        .filter(|id| !old_entries.contains_key(id))
        .copied()
        .collect::<BTreeSet<_>>();
    if added_ids != actual_added {
        return Err(transition_error());
    }
    Ok(())
}

/// Look up a source candidate against registry v3 base routes and active target identities.
pub fn lookup_promotion_origin_v3(
    registry: &PromotionOriginRegistryV3,
    source: &crate::promotion_registry::PromotionSourceOrigin,
    target_modules: &[Name],
    target_artifacts: &[(PackageHash, PackageHash)],
) -> PromotionOriginLookup {
    let base = PromotionOriginRegistryV2 {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
        registry_id: registry.registry_id.clone(),
        registry_version: 2,
        generation: registry.generation,
        target_package: registry.target_package.clone(),
        entries: registry
            .entries
            .iter()
            .filter_map(|entry| match entry {
                PromotionOriginEntryV3::SourceV2(entry) => Some(entry.clone()),
                PromotionOriginEntryV3::CatalogTargetV1(_) => None,
            })
            .collect(),
        unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
        registry_hash: zero_hash(),
        proof_evidence: false,
    };
    let base_result = crate::promotion_registry_v2::lookup_promotion_origin_v2(
        &base,
        source,
        target_modules,
        target_artifacts,
    );
    if base_result != PromotionOriginLookup::NoRegistryMatch {
        return base_result;
    }
    let Ok(routes) = effective_routes(registry) else {
        return PromotionOriginLookup::TargetModuleCollision;
    };
    if target_modules
        .iter()
        .any(|module| routes.contains_key(&module.as_dotted()))
    {
        return PromotionOriginLookup::TargetModuleCollision;
    }
    if target_artifacts.iter().any(|artifact| {
        routes.values().any(|route| {
            (
                route.revision.target_certificate_hash,
                route.revision.target_export_hash,
            ) == *artifact
        })
    }) {
        return PromotionOriginLookup::TargetArtifactCollision;
    }
    PromotionOriginLookup::NoRegistryMatch
}

/// Return active effective target revisions keyed by public module name.
pub fn active_catalog_target_revisions(
    registry: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<BTreeMap<String, PromotionDeclarationTargetRevision>> {
    Ok(effective_routes(registry)?
        .into_iter()
        .map(|(module, state)| (module, state.revision))
        .collect())
}

/// Return active effective owner references and revisions keyed by public module name.
pub fn active_catalog_routes(
    registry: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<BTreeMap<String, (CatalogRouteRef, PromotionDeclarationTargetRevision)>>
{
    Ok(effective_routes(registry)?
        .into_iter()
        .map(|(module, state)| (module, (state.route, state.revision)))
        .collect())
}

#[derive(Clone)]
struct EffectiveRoute {
    route: CatalogRouteRef,
    revision: PromotionDeclarationTargetRevision,
    active: bool,
}

fn validate_registry_shape(
    registry: &PromotionOriginRegistryV3,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    if registry.schema != MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA
        || registry.registry_id != MATHLIB_PROMOTION_REGISTRY_ID
        || registry.registry_version != 3
        || registry.generation == 0
        || registry.target_package.as_str() != "npa-mathlib"
        || registry.proof_evidence
        || registry.entries.len() > MAX_ENTRIES
        || registry.catalog_change_events.len() > MAX_EVENTS
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "registry",
            "strict npa-mathlib registry v3",
            "mismatch",
        ));
    }
    ensure_strict_by(
        &registry.entries,
        "entries",
        PromotionOriginEntryV3::owner_id,
    )?;
    let base_entries = registry
        .entries
        .iter()
        .filter_map(|entry| match entry {
            PromotionOriginEntryV3::SourceV2(entry) => Some(entry.clone()),
            PromotionOriginEntryV3::CatalogTargetV1(_) => None,
        })
        .collect::<Vec<_>>();
    let mut base = PromotionOriginRegistryV2 {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
        registry_id: registry.registry_id.clone(),
        registry_version: 2,
        generation: registry.generation,
        target_package: registry.target_package.clone(),
        entries: base_entries,
        unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
        registry_hash: zero_hash(),
        proof_evidence: false,
    };
    base.refresh_hash()?;
    validate_promotion_origin_registry_v2(&base)?;

    for (index, entry) in registry.entries.iter().enumerate() {
        if let PromotionOriginEntryV3::CatalogTargetV1(entry) = entry {
            validate_catalog_entry(entry, index)?;
        }
    }
    let mut previous_event_version = None;
    let mut previous_target = None;
    for (index, event) in registry.catalog_change_events.iter().enumerate() {
        validate_event(event, index)?;
        if previous_event_version
            .as_ref()
            .is_some_and(|version| !version_is_strictly_greater(&event.target.version, version))
            || previous_target
                .as_ref()
                .is_some_and(|projection| projection != &event.previous_target)
        {
            return Err(PackageArtifactError::non_canonical(
                "catalog_change_events",
                "strict chained target versions",
            ));
        }
        previous_event_version = Some(event.target.version.clone());
        previous_target = Some(event.target.clone());
    }
    let _ = effective_routes(registry)?;
    if check_hash && registry.registry_hash != promotion_origin_registry_v3_hash(registry)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "registry_hash",
            "registry_hash",
            "recomputed registry v3 hash",
            "mismatch",
        ));
    }
    Ok(())
}

fn validate_catalog_entry(entry: &CatalogTargetEntry, index: usize) -> PackageArtifactResult<()> {
    let path = format!("entries[{index}].catalog_target_v1");
    validate_module_name(&entry.target_module, format!("{path}.target_module"))?;
    validate_revision(&entry.first_revision, &format!("{path}.first_revision"))?;
    validate_package_path(
        &entry.evidence.audit_path,
        format!("{path}.evidence.audit_path"),
    )
    .map_err(|_| {
        PackageArtifactError::invalid_path(
            format!("{path}.evidence.audit_path"),
            entry.evidence.audit_path.as_str(),
        )
    })?;
    if !entry.target_module.as_dotted().starts_with("Mathlib.")
        || entry.lifecycle != "active"
        || entry.introduced_version != entry.first_revision.target_version
        || entry.evidence.kind != "catalog_registry_sync_v1"
        || entry.catalog_target_id
            != catalog_target_id(&entry.target_module, &entry.first_revision)?
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "catalog_target_v1",
            "derived active target-only owner",
            "mismatch",
        ));
    }
    Ok(())
}

fn validate_event(event: &CatalogChangeEvent, index: usize) -> PackageArtifactResult<()> {
    let path = format!("catalog_change_events[{index}]");
    validate_projection(&event.previous_target, &format!("{path}.previous_target"))?;
    validate_projection(&event.target, &format!("{path}.target"))?;
    validate_path_ref(&event.audit.path, &format!("{path}.audit.path"))?;
    validate_path_ref(&event.attestation.path, &format!("{path}.attestation.path"))?;
    if let Some(request) = &event.request {
        validate_path_ref(&request.path, &format!("{path}.request.path"))?;
    }
    ensure_strict(&event.revised_routes, &format!("{path}.revised_routes"))?;
    ensure_strict(&event.added_targets, &format!("{path}.added_targets"))?;
    ensure_strict(
        &event.lifecycle_changes,
        &format!("{path}.lifecycle_changes"),
    )?;
    if event.kind != "catalog_registry_sync_v1"
        || event.previous_target.package != event.target.package
        || !version_is_strictly_greater(&event.target.version, &event.previous_target.version)
        || event.revised_routes.len() > MAX_EVENT_ROWS
        || event.added_targets.len() > MAX_EVENT_ROWS
        || event.lifecycle_changes.len() > MAX_EVENT_ROWS
        || event.request.is_some() == event.lifecycle_changes.is_empty()
        || event.change_set_hash != catalog_change_set_hash(event)?
        || event.event_id != catalog_change_event_id(event)?
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "event",
            "derived catalog registry sync event",
            "mismatch",
        ));
    }
    for row in &event.revised_routes {
        validate_owner_kind(&row.owner_kind, &path)?;
        validate_module_name(&row.target_module, format!("{path}.target_module"))?;
        validate_revision(&row.target_revision, &format!("{path}.target_revision"))?;
        if row.target_revision.target_version != event.target.version {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "target_revision.target_version",
                event.target.version.as_str(),
                row.target_revision.target_version.as_str(),
            ));
        }
    }
    for row in &event.added_targets {
        if row.owner_kind != "catalog_target_v1" {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "added_targets.owner_kind",
                "catalog_target_v1",
                &row.owner_kind,
            ));
        }
    }
    for row in &event.lifecycle_changes {
        validate_lifecycle(row, &path)?;
        if row.effective_version != event.target.version {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "effective_version",
                event.target.version.as_str(),
                row.effective_version.as_str(),
            ));
        }
    }
    Ok(())
}

fn effective_routes(
    registry: &PromotionOriginRegistryV3,
) -> PackageArtifactResult<BTreeMap<String, EffectiveRoute>> {
    let mut routes = BTreeMap::new();
    for entry in &registry.entries {
        match entry {
            PromotionOriginEntryV3::SourceV2(PromotionOriginEntryV2::WholeModuleV1(entry)) => {
                for route in &entry.module_routes {
                    let revision = route.target_revisions.last().ok_or_else(collision_error)?;
                    let unified = unify_v1_revision(revision);
                    insert_route(
                        &mut routes,
                        CatalogRouteRef {
                            owner_kind: "whole_module_v1".to_owned(),
                            owner_id: entry.promotion_id,
                            target_module: route.target_module.clone(),
                        },
                        unified,
                        matches!(
                            entry.lifecycle,
                            crate::promotion_registry::PromotionLifecycle::Active
                        ),
                    )?;
                }
            }
            PromotionOriginEntryV3::SourceV2(PromotionOriginEntryV2::DeclarationClosureV1(
                entry,
            )) => {
                insert_route(
                    &mut routes,
                    CatalogRouteRef {
                        owner_kind: "declaration_closure_v1".to_owned(),
                        owner_id: entry.promotion_id,
                        target_module: entry.target_module.clone(),
                    },
                    entry.target_revisions[0].clone(),
                    entry.lifecycle == "active",
                )?;
            }
            PromotionOriginEntryV3::CatalogTargetV1(entry) => {
                insert_route(
                    &mut routes,
                    CatalogRouteRef {
                        owner_kind: "catalog_target_v1".to_owned(),
                        owner_id: entry.catalog_target_id,
                        target_module: entry.target_module.clone(),
                    },
                    entry.first_revision.clone(),
                    entry.lifecycle == "active",
                )?;
            }
        }
    }
    for reservation in &registry.unresolved_legacy_targets {
        let revision = reservation
            .target_revisions
            .last()
            .ok_or_else(collision_error)?;
        insert_route(
            &mut routes,
            CatalogRouteRef {
                owner_kind: "legacy_reservation".to_owned(),
                owner_id: reservation.reservation_id,
                target_module: reservation.target_module.clone(),
            },
            unify_v1_revision(revision),
            matches!(
                reservation.lifecycle,
                crate::promotion_registry::PromotionLifecycle::Active
            ),
        )?;
    }
    for event in &registry.catalog_change_events {
        for row in &event.revised_routes {
            let key = row.target_module.as_dotted();
            let state = routes.get_mut(&key).ok_or_else(collision_error)?;
            let stored_revision_hash = catalog_target_revision_hash(&state.revision)?;
            let legacy_revision_completed_externally =
                legacy_revision_is_incomplete(&state.revision)
                    && row.previous_revision_hash != stored_revision_hash;
            if !state.active
                || state.route.owner_id != row.owner_id
                || state.route.owner_kind != row.owner_kind
                || (stored_revision_hash != row.previous_revision_hash
                    && !legacy_revision_completed_externally)
                || !version_is_strictly_greater(
                    &row.target_revision.target_version,
                    &state.revision.target_version,
                )
            {
                return Err(collision_error());
            }
            state.revision = row.target_revision.clone();
        }
        for added in &event.added_targets {
            let entry = registry
                .entries
                .iter()
                .find_map(|entry| match entry {
                    PromotionOriginEntryV3::CatalogTargetV1(entry)
                        if entry.catalog_target_id == added.owner_id =>
                    {
                        Some(entry)
                    }
                    _ => None,
                })
                .ok_or_else(collision_error)?;
            if entry.target_module != added.target_module
                || catalog_target_revision_hash(&entry.first_revision)? != added.first_revision_hash
                || entry.evidence.change_set_hash != event.change_set_hash
            {
                return Err(collision_error());
            }
        }
        for change in &event.lifecycle_changes {
            for old in &change.old_routes {
                let state = routes
                    .get_mut(&old.target_module.as_dotted())
                    .ok_or_else(collision_error)?;
                if !state.active || state.route != *old {
                    return Err(collision_error());
                }
                state.active = false;
            }
            for new in &change.new_routes {
                let state = routes
                    .get(&new.target_module.as_dotted())
                    .ok_or_else(collision_error)?;
                if !state.active || state.route != *new {
                    return Err(collision_error());
                }
            }
        }
    }
    routes.retain(|_, state| state.active);
    let mut artifacts = BTreeSet::new();
    for state in routes.values() {
        if !artifacts.insert((
            state.revision.target_certificate_hash,
            state.revision.target_export_hash,
        )) {
            return Err(collision_error());
        }
    }
    Ok(routes)
}

fn legacy_revision_is_incomplete(revision: &PromotionDeclarationTargetRevision) -> bool {
    let zero = zero_hash();
    revision.target_meta_file_hash == zero || revision.target_replay_file_hash == zero
}

fn insert_route(
    routes: &mut BTreeMap<String, EffectiveRoute>,
    route: CatalogRouteRef,
    revision: PromotionDeclarationTargetRevision,
    active: bool,
) -> PackageArtifactResult<()> {
    if routes
        .insert(
            route.target_module.as_dotted(),
            EffectiveRoute {
                route,
                revision,
                active,
            },
        )
        .is_some()
    {
        return Err(collision_error());
    }
    Ok(())
}

fn unify_v1_revision<T>(
    revision: &crate::promotion_registry::PromotionTargetRevision<T>,
) -> PromotionDeclarationTargetRevision
where
    T: V1TargetTheorem,
{
    PromotionDeclarationTargetRevision {
        target_version: revision.target_version.clone(),
        target_source_file_hash: revision.target_source_file_hash,
        target_meta_file_hash: zero_hash(),
        target_replay_file_hash: zero_hash(),
        target_certificate_file_hash: revision.target_certificate_file_hash,
        target_certificate_hash: revision.target_certificate_hash,
        target_export_hash: revision.target_export_hash,
        target_axiom_report_hash: revision.target_axiom_report_hash,
        theorems: revision
            .theorems
            .iter()
            .map(
                |theorem| crate::promotion_registry_v2::PromotionDeclarationTargetTheorem {
                    target_name: theorem.target_name().clone(),
                    statement_hash: theorem.statement_hash(),
                },
            )
            .collect(),
    }
}

trait V1TargetTheorem {
    fn target_name(&self) -> &Name;
    fn statement_hash(&self) -> PackageHash;
}

impl V1TargetTheorem for crate::promotion_registry::PromotionReservedTheorem {
    fn target_name(&self) -> &Name {
        &self.target_name
    }
    fn statement_hash(&self) -> PackageHash {
        self.target_statement_hash
    }
}

impl V1TargetTheorem for crate::promotion_registry::PromotionRouteTheorem {
    fn target_name(&self) -> &Name {
        &self.target_name
    }
    fn statement_hash(&self) -> PackageHash {
        self.target_statement_hash
    }
}

fn validate_projection(value: &CatalogTargetProjection, path: &str) -> PackageArtifactResult<()> {
    if value.package.as_str() != "npa-mathlib" {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "package",
            "npa-mathlib",
            value.package.as_str(),
        ));
    }
    Ok(())
}

fn validate_revision(
    revision: &PromotionDeclarationTargetRevision,
    path: &str,
) -> PackageArtifactResult<()> {
    if revision.theorems.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(PackageArtifactError::non_canonical(
            path,
            "strict theorem order",
        ));
    }
    Ok(())
}

fn validate_lifecycle(value: &CatalogLifecycleChange, path: &str) -> PackageArtifactResult<()> {
    ensure_strict(&value.old_routes, &format!("{path}.old_routes"))?;
    ensure_strict(&value.new_routes, &format!("{path}.new_routes"))?;
    for route in value.old_routes.iter().chain(&value.new_routes) {
        validate_owner_kind(&route.owner_kind, path)?;
        validate_module_name(&route.target_module, format!("{path}.target_module"))?;
    }
    let valid = match value.kind.as_str() {
        "rename" | "replacement" => value.old_routes.len() == 1 && value.new_routes.len() == 1,
        "split" => value.old_routes.len() == 1 && value.new_routes.len() >= 2,
        "merge" => value.old_routes.len() >= 2 && value.new_routes.len() == 1,
        "retirement" => !value.old_routes.is_empty() && value.new_routes.is_empty(),
        _ => false,
    };
    if !valid {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "lifecycle",
            "valid rename/replacement/split/merge/retirement cardinality",
            &value.kind,
        ));
    }
    Ok(())
}

fn validate_owner_kind(value: &str, path: &str) -> PackageArtifactResult<()> {
    if matches!(
        value,
        "whole_module_v1" | "declaration_closure_v1" | "catalog_target_v1" | "legacy_reservation"
    ) {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            path,
            "owner_kind",
            "known registry owner kind",
            value,
        ))
    }
}

fn validate_path_ref(path: &PackagePath, field: &str) -> PackageArtifactResult<()> {
    validate_package_path(path, field)
        .map_err(|_| PackageArtifactError::invalid_path(field, path.as_str()))
}

fn parse_entry(value: &JsonValue, index: usize) -> PackageArtifactResult<PromotionOriginEntryV3> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    let kind = required_string(members, &path, "kind")?;
    if kind == "catalog_target_v1" {
        reject_unknown_fields(&path, members, CATALOG_ENTRY_FIELDS)?;
        Ok(PromotionOriginEntryV3::CatalogTargetV1(Box::new(
            CatalogTargetEntry {
                catalog_target_id: required_hash(members, &path, "catalog_target_id")?,
                lifecycle: required_string(members, &path, "lifecycle")?,
                introduced_version: PackageVersion::new(required_string(
                    members,
                    &path,
                    "introduced_version",
                )?),
                target_module: required_name(members, &path, "target_module")?,
                first_revision: parse_revision(
                    required_value(members, &path, "first_revision")?,
                    &format!("{path}.first_revision"),
                )?,
                evidence: parse_catalog_evidence(
                    required_value(members, &path, "evidence")?,
                    &format!("{path}.evidence"),
                )?,
            },
        )))
    } else {
        parse_v2_entry(value, index).map(PromotionOriginEntryV3::SourceV2)
    }
}

fn parse_catalog_evidence(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogTargetEvidence> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CATALOG_EVIDENCE_FIELDS)?;
    Ok(CatalogTargetEvidence {
        kind: required_string(members, path, "kind")?,
        audit_path: required_path(members, path, "audit_path")?,
        audit_file_hash: required_hash(members, path, "audit_file_hash")?,
        change_set_hash: required_hash(members, path, "change_set_hash")?,
    })
}

fn parse_event(value: &JsonValue, path: &str) -> PackageArtifactResult<CatalogChangeEvent> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, EVENT_FIELDS)?;
    let request = match required_value(members, path, "request")? {
        JsonValue::Null => None,
        value => Some(parse_request_ref(value, &format!("{path}.request"))?),
    };
    Ok(CatalogChangeEvent {
        event_id: required_hash(members, path, "event_id")?,
        kind: required_string(members, path, "kind")?,
        input_registry_hash: required_hash(members, path, "input_registry_hash")?,
        change_set_hash: required_hash(members, path, "change_set_hash")?,
        previous_target: parse_projection(
            required_value(members, path, "previous_target")?,
            &format!("{path}.previous_target"),
        )?,
        target: parse_projection(
            required_value(members, path, "target")?,
            &format!("{path}.target"),
        )?,
        audit: parse_file_ref(
            required_value(members, path, "audit")?,
            &format!("{path}.audit"),
        )?,
        request,
        attestation: parse_attestation_ref(
            required_value(members, path, "attestation")?,
            &format!("{path}.attestation"),
        )?,
        revised_routes: parse_bounded_array(
            members,
            path,
            "revised_routes",
            MAX_EVENT_ROWS,
            parse_revised,
        )?,
        added_targets: parse_bounded_array(
            members,
            path,
            "added_targets",
            MAX_EVENT_ROWS,
            parse_added,
        )?,
        lifecycle_changes: parse_bounded_array(
            members,
            path,
            "lifecycle_changes",
            MAX_EVENT_ROWS,
            parse_lifecycle,
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

fn parse_file_ref(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogGovernanceFileRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, FILE_REF_FIELDS)?;
    Ok(CatalogGovernanceFileRef {
        path: required_path(members, path, "path")?,
        file_hash: required_hash(members, path, "file_hash")?,
    })
}

fn parse_request_ref(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogChangeRequestRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REQUEST_REF_FIELDS)?;
    Ok(CatalogChangeRequestRef {
        path: required_path(members, path, "path")?,
        file_hash: required_hash(members, path, "file_hash")?,
        request_hash: required_hash(members, path, "request_hash")?,
    })
}

fn parse_attestation_ref(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogAttestationRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ATTESTATION_REF_FIELDS)?;
    Ok(CatalogAttestationRef {
        path: required_path(members, path, "path")?,
        payload_hash: required_hash(members, path, "payload_hash")?,
    })
}

fn parse_revised(value: &JsonValue, path: &str) -> PackageArtifactResult<CatalogRevisedRoute> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REVISED_FIELDS)?;
    Ok(CatalogRevisedRoute {
        owner_kind: required_string(members, path, "owner_kind")?,
        owner_id: required_hash(members, path, "owner_id")?,
        target_module: required_name(members, path, "target_module")?,
        previous_revision_hash: required_hash(members, path, "previous_revision_hash")?,
        target_revision: parse_revision(
            required_value(members, path, "target_revision")?,
            &format!("{path}.target_revision"),
        )?,
    })
}

fn parse_added(value: &JsonValue, path: &str) -> PackageArtifactResult<CatalogAddedTarget> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ADDED_FIELDS)?;
    Ok(CatalogAddedTarget {
        owner_kind: required_string(members, path, "owner_kind")?,
        owner_id: required_hash(members, path, "owner_id")?,
        target_module: required_name(members, path, "target_module")?,
        first_revision_hash: required_hash(members, path, "first_revision_hash")?,
    })
}

fn parse_lifecycle(value: &JsonValue, path: &str) -> PackageArtifactResult<CatalogLifecycleChange> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, LIFECYCLE_FIELDS)?;
    Ok(CatalogLifecycleChange {
        kind: required_string(members, path, "kind")?,
        effective_version: PackageVersion::new(required_string(
            members,
            path,
            "effective_version",
        )?),
        old_routes: parse_bounded_array(members, path, "old_routes", MAX_EVENT_ROWS, parse_route)?,
        new_routes: parse_bounded_array(members, path, "new_routes", MAX_EVENT_ROWS, parse_route)?,
    })
}

fn parse_route(value: &JsonValue, path: &str) -> PackageArtifactResult<CatalogRouteRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ROUTE_FIELDS)?;
    Ok(CatalogRouteRef {
        owner_kind: required_string(members, path, "owner_kind")?,
        owner_id: required_hash(members, path, "owner_id")?,
        target_module: required_name(members, path, "target_module")?,
    })
}

fn parse_bounded_array<T>(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
    maximum: usize,
    parser: fn(&JsonValue, &str) -> PackageArtifactResult<T>,
) -> PackageArtifactResult<Vec<T>> {
    let values = required_array(members, path, field)?;
    if values.len() > maximum {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            field,
            format!("at most {maximum} rows"),
            values.len().to_string(),
        ));
    }
    values
        .iter()
        .enumerate()
        .map(|(index, value)| parser(value, &format!("{path}.{field}[{index}]")))
        .collect()
}

fn registry_json(registry: &PromotionOriginRegistryV3) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&registry.schema)),
        ("registry_id", json_string(&registry.registry_id)),
        ("registry_version", json_u64(registry.registry_version)),
        ("generation", json_u64(registry.generation)),
        (
            "target_package",
            json_string(registry.target_package.as_str()),
        ),
        (
            "entries",
            json_array(registry.entries.iter().map(entry_json).collect()),
        ),
        (
            "unresolved_legacy_targets",
            json_array(
                registry
                    .unresolved_legacy_targets
                    .iter()
                    .map(v1_reservation_json)
                    .collect(),
            ),
        ),
        (
            "catalog_change_events",
            json_array(
                registry
                    .catalog_change_events
                    .iter()
                    .map(event_json)
                    .collect(),
            ),
        ),
        ("registry_hash", hash_json(registry.registry_hash)),
        ("proof_evidence", json_bool(registry.proof_evidence)),
    ])
}

fn entry_json(entry: &PromotionOriginEntryV3) -> String {
    match entry {
        PromotionOriginEntryV3::SourceV2(entry) => v2_entry_json(entry),
        PromotionOriginEntryV3::CatalogTargetV1(entry) => json_object_in_order(vec![
            ("kind", json_string("catalog_target_v1")),
            ("catalog_target_id", hash_json(entry.catalog_target_id)),
            ("lifecycle", json_string(&entry.lifecycle)),
            (
                "introduced_version",
                json_string(entry.introduced_version.as_str()),
            ),
            (
                "target_module",
                json_string(&entry.target_module.as_dotted()),
            ),
            ("first_revision", revision_json(&entry.first_revision)),
            (
                "evidence",
                json_object_in_order(vec![
                    ("kind", json_string(&entry.evidence.kind)),
                    (
                        "audit_path",
                        json_string(entry.evidence.audit_path.as_str()),
                    ),
                    ("audit_file_hash", hash_json(entry.evidence.audit_file_hash)),
                    ("change_set_hash", hash_json(entry.evidence.change_set_hash)),
                ]),
            ),
        ]),
    }
}

fn event_json(event: &CatalogChangeEvent) -> String {
    json_object_in_order(vec![
        ("event_id", hash_json(event.event_id)),
        ("kind", json_string(&event.kind)),
        ("input_registry_hash", hash_json(event.input_registry_hash)),
        ("change_set_hash", hash_json(event.change_set_hash)),
        ("previous_target", projection_json(&event.previous_target)),
        ("target", projection_json(&event.target)),
        ("audit", file_ref_json(&event.audit)),
        (
            "request",
            event
                .request
                .as_ref()
                .map_or_else(|| "null".to_owned(), request_ref_json),
        ),
        ("attestation", attestation_ref_json(&event.attestation)),
        (
            "revised_routes",
            json_array(event.revised_routes.iter().map(revised_json).collect()),
        ),
        (
            "added_targets",
            json_array(event.added_targets.iter().map(added_json).collect()),
        ),
        (
            "lifecycle_changes",
            json_array(event.lifecycle_changes.iter().map(lifecycle_json).collect()),
        ),
    ])
}

fn projection_json(value: &CatalogTargetProjection) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        ("manifest_file_hash", hash_json(value.manifest_file_hash)),
        (
            "package_lock_file_hash",
            hash_json(value.package_lock_file_hash),
        ),
        (
            "axiom_report_file_hash",
            hash_json(value.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(value.theorem_index_file_hash),
        ),
        (
            "export_summary_file_hash",
            hash_json(value.export_summary_file_hash),
        ),
        (
            "publish_plan_file_hash",
            hash_json(value.publish_plan_file_hash),
        ),
    ])
}

fn file_ref_json(value: &CatalogGovernanceFileRef) -> String {
    json_object_in_order(vec![
        ("path", json_string(value.path.as_str())),
        ("file_hash", hash_json(value.file_hash)),
    ])
}

fn request_ref_json(value: &CatalogChangeRequestRef) -> String {
    json_object_in_order(vec![
        ("path", json_string(value.path.as_str())),
        ("file_hash", hash_json(value.file_hash)),
        ("request_hash", hash_json(value.request_hash)),
    ])
}

fn attestation_ref_json(value: &CatalogAttestationRef) -> String {
    json_object_in_order(vec![
        ("path", json_string(value.path.as_str())),
        ("payload_hash", hash_json(value.payload_hash)),
    ])
}

fn revised_json(value: &CatalogRevisedRoute) -> String {
    json_object_in_order(vec![
        ("owner_kind", json_string(&value.owner_kind)),
        ("owner_id", hash_json(value.owner_id)),
        (
            "target_module",
            json_string(&value.target_module.as_dotted()),
        ),
        (
            "previous_revision_hash",
            hash_json(value.previous_revision_hash),
        ),
        ("target_revision", revision_json(&value.target_revision)),
    ])
}

fn added_json(value: &CatalogAddedTarget) -> String {
    json_object_in_order(vec![
        ("owner_kind", json_string(&value.owner_kind)),
        ("owner_id", hash_json(value.owner_id)),
        (
            "target_module",
            json_string(&value.target_module.as_dotted()),
        ),
        ("first_revision_hash", hash_json(value.first_revision_hash)),
    ])
}

fn lifecycle_json(value: &CatalogLifecycleChange) -> String {
    json_object_in_order(vec![
        ("kind", json_string(&value.kind)),
        (
            "effective_version",
            json_string(value.effective_version.as_str()),
        ),
        (
            "old_routes",
            json_array(value.old_routes.iter().map(route_json).collect()),
        ),
        (
            "new_routes",
            json_array(value.new_routes.iter().map(route_json).collect()),
        ),
    ])
}

fn route_json(value: &CatalogRouteRef) -> String {
    json_object_in_order(vec![
        ("owner_kind", json_string(&value.owner_kind)),
        ("owner_id", hash_json(value.owner_id)),
        (
            "target_module",
            json_string(&value.target_module.as_dotted()),
        ),
    ])
}

fn ensure_strict<T: Ord>(values: &[T], path: &str) -> PackageArtifactResult<()> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        Err(PackageArtifactError::non_canonical(path, "strict order"))
    } else {
        Ok(())
    }
}

fn ensure_strict_by<T, K: Ord>(
    values: &[T],
    path: &str,
    key: fn(&T) -> K,
) -> PackageArtifactResult<()> {
    if values.windows(2).any(|pair| key(&pair[0]) >= key(&pair[1])) {
        Err(PackageArtifactError::non_canonical(path, "strict order"))
    } else {
        Ok(())
    }
}

fn version_is_strictly_greater(left: &PackageVersion, right: &PackageVersion) -> bool {
    version_parts(left).is_some_and(|left| version_parts(right).is_some_and(|right| left > right))
}

fn version_parts(version: &PackageVersion) -> Option<(u64, u64, u64)> {
    let values = version
        .as_str()
        .split('.')
        .map(str::parse::<u64>)
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    (values.len() == 3).then(|| (values[0], values[1], values[2]))
}

fn domain_hash(domain: &[u8], json: &str) -> PackageHash {
    let mut bytes = Vec::with_capacity(domain.len() + json.len());
    bytes.extend_from_slice(domain);
    bytes.extend_from_slice(json.as_bytes());
    package_file_hash(&bytes)
}

const fn zero_hash() -> PackageHash {
    PackageHash::new([0; 32])
}

fn collision_error() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "registry_routes",
        "unique coherent active target ownership",
        "collision",
    )
}

fn transition_error() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "registry_transition",
        "one valid append-only v3 transition",
        "mismatch",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::promotion_registry::{
        promotion_legacy_target_reservation_id, PromotionAuditLocation, PromotionEvidence,
        PromotionLifecycle, PromotionReservedTheorem, PromotionTargetRevision,
    };

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }

    fn empty_v2() -> PromotionOriginRegistryV2 {
        let mut registry = PromotionOriginRegistryV2 {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 2,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries: Vec::new(),
            unresolved_legacy_targets: Vec::new(),
            registry_hash: hash(0),
            proof_evidence: false,
        };
        registry.refresh_hash().unwrap();
        registry
    }

    fn projection(version: &str, seed: u8) -> CatalogTargetProjection {
        CatalogTargetProjection {
            package: PackageId::new("npa-mathlib"),
            version: PackageVersion::new(version),
            manifest_file_hash: hash(seed),
            package_lock_file_hash: hash(seed + 1),
            axiom_report_file_hash: hash(seed + 2),
            theorem_index_file_hash: hash(seed + 3),
            export_summary_file_hash: hash(seed + 4),
            publish_plan_file_hash: hash(seed + 5),
        }
    }

    fn append_empty_event(
        registry: &PromotionOriginRegistryV3,
        input_file_hash: PackageHash,
        previous: CatalogTargetProjection,
        target: CatalogTargetProjection,
    ) -> PromotionOriginRegistryV3 {
        let mut event = CatalogChangeEvent {
            event_id: hash(0),
            kind: "catalog_registry_sync_v1".to_owned(),
            input_registry_hash: input_file_hash,
            change_set_hash: hash(0),
            previous_target: previous,
            target,
            audit: CatalogGovernanceFileRef {
                path: PackagePath::new("docs/promotion/audit.md"),
                file_hash: hash(20),
            },
            request: None,
            attestation: CatalogAttestationRef {
                path: PackagePath::new("docs/promotion/sync.json"),
                payload_hash: hash(21),
            },
            revised_routes: Vec::new(),
            added_targets: Vec::new(),
            lifecycle_changes: Vec::new(),
        };
        event.change_set_hash = catalog_change_set_hash(&event).unwrap();
        event.event_id = catalog_change_event_id(&event).unwrap();
        let mut next = registry.clone();
        next.generation += 1;
        next.catalog_change_events.push(event);
        next.refresh_hash().unwrap();
        next
    }

    #[test]
    fn canonical_v3_round_trip_and_self_hash() {
        let v3 = migrate_promotion_origin_registry_v2_to_v3(&empty_v2()).unwrap();
        let json = v3.canonical_json().unwrap();
        assert_eq!(parse_promotion_origin_registry_v3_json(&json).unwrap(), v3);
        assert_eq!(
            promotion_origin_registry_v3_hash(&v3).unwrap(),
            v3.registry_hash
        );
    }

    #[test]
    fn accepts_skipped_version_reconciliation_and_repeated_later_sync() {
        let v2 = empty_v2();
        let migrated = migrate_promotion_origin_registry_v2_to_v3(&v2).unwrap();
        let first = append_empty_event(
            &migrated,
            package_file_hash(v2.canonical_json().unwrap().as_bytes()),
            projection("0.2.1", 1),
            projection("0.2.4", 8),
        );
        validate_promotion_origin_registry_v2_to_v3_reconciliation(&v2, &first).unwrap();
        let second = append_empty_event(
            &first,
            package_file_hash(first.canonical_json().unwrap().as_bytes()),
            projection("0.2.4", 8),
            projection("0.3.0", 30),
        );
        validate_promotion_origin_registry_v3_transition(&first, &second).unwrap();
    }

    #[test]
    fn rejects_mutated_history_and_unknown_fields() {
        let v2 = empty_v2();
        let migrated = migrate_promotion_origin_registry_v2_to_v3(&v2).unwrap();
        let first = append_empty_event(
            &migrated,
            package_file_hash(v2.canonical_json().unwrap().as_bytes()),
            projection("0.2.1", 1),
            projection("0.2.4", 8),
        );
        let mut mutated = first.clone();
        mutated.catalog_change_events[0].audit.file_hash = hash(99);
        mutated.refresh_hash().unwrap_err();
        let mut wrong_input = first.clone();
        wrong_input.catalog_change_events[0].input_registry_hash = hash(99);
        wrong_input.catalog_change_events[0].change_set_hash =
            catalog_change_set_hash(&wrong_input.catalog_change_events[0]).unwrap();
        wrong_input.catalog_change_events[0].event_id =
            catalog_change_event_id(&wrong_input.catalog_change_events[0]).unwrap();
        wrong_input.refresh_hash().unwrap();
        assert!(
            validate_promotion_origin_registry_v2_to_v3_reconciliation(&v2, &wrong_input).is_err()
        );
        let json = first.canonical_json().unwrap().replacen(
            "\"registry_id\":",
            "\"unknown\":false,\"registry_id\":",
            1,
        );
        assert!(parse_promotion_origin_registry_v3_json(&json).is_err());
    }

    #[test]
    fn legacy_previous_hash_requires_explicit_previous_package_context() {
        let target_module = Name::from_dotted("Mathlib.Legacy");
        let legacy_revision = PromotionTargetRevision::<PromotionReservedTheorem> {
            target_version: PackageVersion::new("0.2.1"),
            target_source_file_hash: hash(30),
            target_certificate_file_hash: hash(31),
            target_certificate_hash: hash(32),
            target_export_hash: hash(33),
            target_axiom_report_hash: hash(34),
            theorems: Vec::new(),
        };
        let mut previous = PromotionOriginRegistry {
            schema: crate::MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 1,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries: Vec::new(),
            unresolved_legacy_targets: vec![PromotionLegacyTargetReservation {
                reservation_id: promotion_legacy_target_reservation_id(
                    &target_module,
                    &legacy_revision,
                )
                .unwrap(),
                lifecycle: PromotionLifecycle::Active,
                target_module: target_module.clone(),
                target_revisions: vec![legacy_revision.clone()],
                evidence: PromotionEvidence::LegacyAudit {
                    audit_location: PromotionAuditLocation {
                        repository: "npa-mathlib".to_owned(),
                        path: PackagePath::new("docs/promotion/legacy.md"),
                    },
                    audit_file_hash: hash(35),
                },
            }],
            registry_hash: hash(0),
            proof_evidence: false,
        };
        previous.refresh_hash().unwrap();
        let migrated = migrate_promotion_origin_registry_v1_to_v3(&previous).unwrap();
        let mut completed = unify_v1_revision(&legacy_revision);
        completed.target_meta_file_hash = hash(36);
        completed.target_replay_file_hash = hash(37);
        let completed_hash = catalog_target_revision_hash(&completed).unwrap();
        let mut event = CatalogChangeEvent {
            event_id: hash(0),
            kind: "catalog_registry_sync_v1".to_owned(),
            input_registry_hash: package_file_hash(previous.canonical_json().unwrap().as_bytes()),
            change_set_hash: hash(0),
            previous_target: projection("0.2.1", 1),
            target: projection("0.2.2", 8),
            audit: CatalogGovernanceFileRef {
                path: PackagePath::new("docs/promotion/audit.md"),
                file_hash: hash(38),
            },
            request: None,
            attestation: CatalogAttestationRef {
                path: PackagePath::new("docs/promotion/sync.json"),
                payload_hash: hash(39),
            },
            revised_routes: vec![CatalogRevisedRoute {
                owner_kind: "legacy_reservation".to_owned(),
                owner_id: previous.unresolved_legacy_targets[0].reservation_id,
                target_module: target_module.clone(),
                previous_revision_hash: completed_hash,
                target_revision: PromotionDeclarationTargetRevision {
                    target_version: PackageVersion::new("0.2.2"),
                    ..completed
                },
            }],
            added_targets: Vec::new(),
            lifecycle_changes: Vec::new(),
        };
        event.change_set_hash = catalog_change_set_hash(&event).unwrap();
        event.event_id = catalog_change_event_id(&event).unwrap();
        let mut next = migrated;
        next.generation += 1;
        next.catalog_change_events.push(event);
        next.refresh_hash().unwrap();

        assert!(
            validate_promotion_origin_registry_v1_to_v3_reconciliation(&previous, &next).is_err()
        );
        let context = BTreeMap::from([(target_module.as_dotted(), completed_hash)]);
        validate_promotion_origin_registry_v1_to_v3_reconciliation_with_previous_hashes(
            &previous, &next, &context,
        )
        .unwrap();
        assert!(
            validate_promotion_origin_registry_v1_to_v3_reconciliation_with_previous_hashes(
                &previous,
                &next,
                &BTreeMap::from([(target_module.as_dotted(), hash(99))]),
            )
            .is_err()
        );
    }
}

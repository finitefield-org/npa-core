//! Canonical machine-readable mathlib promotion-origin registry.
//!
//! Registry data is governance metadata, not proof evidence. It prevents
//! duplicate source routes and target collisions while preserving historical
//! namespace transport identities.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_path, required_string, required_u64, required_value,
        validate_declaration_name, validate_module_name, validate_package_identity,
        validate_plain_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    schema::MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA,
};

const REGISTRY_FIELDS: &[&str] = &[
    "schema",
    "registry_id",
    "registry_version",
    "generation",
    "target_package",
    "entries",
    "unresolved_legacy_targets",
    "registry_hash",
    "proof_evidence",
];
const ENTRY_FIELDS: &[&str] = &[
    "promotion_id",
    "lifecycle",
    "introduced_version",
    "canonical_source",
    "equivalent_sources",
    "module_routes",
    "evidence",
];
const SOURCE_FIELDS: &[&str] = &["package", "version", "modules"];
const SOURCE_MODULE_FIELDS: &[&str] = &[
    "module",
    "source_file_hash",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
];
const ROUTE_FIELDS: &[&str] = &[
    "source_module",
    "target_module",
    "declaration_mapping",
    "renames",
    "target_revisions",
];
const RENAME_FIELDS: &[&str] = &["source", "target"];
const REVISION_FIELDS: &[&str] = &[
    "target_version",
    "target_source_file_hash",
    "target_certificate_file_hash",
    "target_certificate_hash",
    "target_export_hash",
    "target_axiom_report_hash",
    "theorems",
];
const ROUTE_THEOREM_FIELDS: &[&str] = &[
    "source_name",
    "source_statement_hash",
    "target_name",
    "target_statement_hash",
];
const RESERVATION_THEOREM_FIELDS: &[&str] = &["target_name", "target_statement_hash"];
const ACTIVE_FIELDS: &[&str] = &["kind"];
const RETIRED_FIELDS: &[&str] = &[
    "kind",
    "retired_version",
    "audit_location",
    "audit_file_hash",
];
const AUDIT_LOCATION_FIELDS: &[&str] = &["repository", "path"];
const NAMESPACE_EVIDENCE_FIELDS: &[&str] = &[
    "kind",
    "plan_schema",
    "plan_path",
    "plan_file_hash",
    "acceptance",
    "transport",
];
const LEGACY_EVIDENCE_FIELDS: &[&str] = &["kind", "audit_location", "audit_file_hash"];
const ACCEPTANCE_EVIDENCE_FIELDS: &[&str] = &[
    "policy_id",
    "policy_version",
    "policy_file_hash",
    "source_ledger_schema",
    "source_ledger_path",
    "source_ledger_file_hash",
];
const TRANSPORT_EVIDENCE_FIELDS: &[&str] = &[
    "policy_id",
    "policy_version",
    "policy_file_hash",
    "mapping_request_schema",
    "mapping_request_path",
    "mapping_request_file_hash",
    "attestation_schema",
    "attestation_path",
    "attestation_file_hash",
    "normalized_closure_hash",
];
const RESERVATION_FIELDS: &[&str] = &[
    "reservation_id",
    "lifecycle",
    "target_module",
    "target_revisions",
    "evidence",
];

const REGISTRY_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-ORIGIN-REGISTRY-v1\0";
const LEGACY_TARGET_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-LEGACY-TARGET-v1\0";

/// Stable registry identifier required by v1.
pub const MATHLIB_PROMOTION_REGISTRY_ID: &str = "finitefield-org.npa-mathlib.promotion-origins";
/// Canonical registry location relative to npa-mathlib.
pub const MATHLIB_PROMOTION_REGISTRY_PATH: &str = "promotion-origins.json";

/// Exact source module artifact identity.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionSourceModule {
    /// Source module name.
    pub module: Name,
    /// Source bytes hash.
    pub source_file_hash: PackageHash,
    /// Certificate file bytes hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical export hash.
    pub export_hash: PackageHash,
}

/// One canonical or artifact-identical source package origin.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionSourceOrigin {
    /// Source package ID.
    pub package: PackageId,
    /// Source package version.
    pub version: PackageVersion,
    /// Complete selected-module artifact inventory.
    pub modules: Vec<PromotionSourceModule>,
}

/// One explicit declaration rename retained from transport mapping.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionDeclarationRename {
    /// Source declaration.
    pub source: Name,
    /// Public target declaration.
    pub target: Name,
}

/// One theorem identity across a sourced route.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionRouteTheorem {
    /// Source theorem name.
    pub source_name: Name,
    /// Source statement hash.
    pub source_statement_hash: PackageHash,
    /// Target theorem name.
    pub target_name: Name,
    /// Target statement hash.
    pub target_statement_hash: PackageHash,
}

/// One target-only theorem identity in an unresolved reservation.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionReservedTheorem {
    /// Target theorem name.
    pub target_name: Name,
    /// Target statement hash.
    pub target_statement_hash: PackageHash,
}

/// Exact target artifact identity at one package version.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTargetRevision<T> {
    /// Target release version that introduced this revision.
    pub target_version: PackageVersion,
    /// Public source bytes hash.
    pub target_source_file_hash: PackageHash,
    /// Public certificate file hash.
    pub target_certificate_file_hash: PackageHash,
    /// Public canonical certificate hash.
    pub target_certificate_hash: PackageHash,
    /// Public export hash.
    pub target_export_hash: PackageHash,
    /// Public axiom-report hash.
    pub target_axiom_report_hash: PackageHash,
    /// Theorem identities for this revision.
    pub theorems: Vec<T>,
}

/// One source-to-public module route.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionModuleRoute {
    /// Source module.
    pub source_module: Name,
    /// Public target module.
    pub target_module: Name,
    /// Mapping mode, always `same-name-except-explicit` in v1.
    pub declaration_mapping: String,
    /// Explicit renames, empty for generic materializer-v1 entries.
    pub renames: Vec<PromotionDeclarationRename>,
    /// Immutable target revision history.
    pub target_revisions: Vec<PromotionTargetRevision<PromotionRouteTheorem>>,
}

/// Logical repository-relative audit location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionAuditLocation {
    /// Logical repository identifier, never a host path.
    pub repository: String,
    /// Repository-relative normalized path.
    pub path: PackagePath,
}

/// Target lifecycle, independent of evidence provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PromotionLifecycle {
    /// Target is present in the current package.
    Active,
    /// Target was intentionally removed while its route stays reserved.
    Retired {
        /// Release that retired the target.
        retired_version: PackageVersion,
        /// Retirement audit location.
        audit_location: PromotionAuditLocation,
        /// Exact retirement audit bytes hash.
        audit_file_hash: PackageHash,
    },
}

/// Hash-bound L2 acceptance evidence references.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionAcceptanceEvidence {
    /// Acceptance policy ID.
    pub policy_id: String,
    /// Acceptance policy version.
    pub policy_version: u64,
    /// Acceptance policy bytes hash.
    pub policy_file_hash: PackageHash,
    /// Acceptance ledger schema.
    pub source_ledger_schema: String,
    /// Source-root-relative ledger path.
    pub source_ledger_path: PackagePath,
    /// Acceptance ledger bytes hash.
    pub source_ledger_file_hash: PackageHash,
}

/// Hash-bound namespace-transport evidence references.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTransportEvidence {
    /// Transport policy ID.
    pub policy_id: String,
    /// Transport policy version.
    pub policy_version: u64,
    /// Transport policy bytes hash.
    pub policy_file_hash: PackageHash,
    /// Mapping request schema.
    pub mapping_request_schema: String,
    /// Source-root-relative mapping path.
    pub mapping_request_path: PackagePath,
    /// Mapping request bytes hash.
    pub mapping_request_file_hash: PackageHash,
    /// Transport attestation schema.
    pub attestation_schema: String,
    /// Source-root-relative attestation path.
    pub attestation_path: PackagePath,
    /// Transport attestation bytes hash.
    pub attestation_file_hash: PackageHash,
    /// Normalized closure hash.
    pub normalized_closure_hash: PackageHash,
}

/// Evidence provenance for a promotion entry or reservation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PromotionEvidence {
    /// Current v2 namespace transport evidence.
    NamespaceTransportV2 {
        /// Canonical plan schema.
        plan_schema: String,
        /// Source-root-relative plan path.
        plan_path: PackagePath,
        /// Plan bytes hash.
        plan_file_hash: PackageHash,
        /// L2 acceptance evidence.
        acceptance: Box<PromotionAcceptanceEvidence>,
        /// Namespace transport evidence.
        transport: Box<PromotionTransportEvidence>,
    },
    /// Historical audited evidence predating current schemas.
    LegacyAudit {
        /// Audit location.
        audit_location: PromotionAuditLocation,
        /// Audit bytes hash.
        audit_file_hash: PackageHash,
    },
}

/// One sourced promotion closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionOriginEntry {
    /// Stable route ID.
    pub promotion_id: PackageHash,
    /// Current lifecycle.
    pub lifecycle: PromotionLifecycle,
    /// First target release version.
    pub introduced_version: PackageVersion,
    /// Canonical source package.
    pub canonical_source: PromotionSourceOrigin,
    /// Artifact-identical source aliases.
    pub equivalent_sources: Vec<PromotionSourceOrigin>,
    /// Complete one-to-one module routes.
    pub module_routes: Vec<PromotionModuleRoute>,
    /// Governance evidence provenance.
    pub evidence: PromotionEvidence,
}

/// One target-only legacy reservation with unknown source provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionLegacyTargetReservation {
    /// Stable target reservation ID.
    pub reservation_id: PackageHash,
    /// Current lifecycle.
    pub lifecycle: PromotionLifecycle,
    /// Reserved public target module.
    pub target_module: Name,
    /// Immutable target-only revision history.
    pub target_revisions: Vec<PromotionTargetRevision<PromotionReservedTheorem>>,
    /// Always legacy audit evidence in v1.
    pub evidence: PromotionEvidence,
}

/// Canonical mathlib promotion-origin registry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionOriginRegistry {
    /// Schema identifier.
    pub schema: String,
    /// Stable registry ID.
    pub registry_id: String,
    /// Registry format version.
    pub registry_version: u64,
    /// Monotonic content generation.
    pub generation: u64,
    /// Public target package.
    pub target_package: PackageId,
    /// Sourced promotion entries.
    pub entries: Vec<PromotionOriginEntry>,
    /// Target-only historical reservations.
    pub unresolved_legacy_targets: Vec<PromotionLegacyTargetReservation>,
    /// Domain-separated self-hash.
    pub registry_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl PromotionOriginRegistry {
    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_promotion_origin_registry(self)?;
        Ok(format!("{}\n", registry_json(self)))
    }

    /// Recompute and store the registry self-hash.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.registry_hash = promotion_origin_registry_hash(self)?;
        Ok(())
    }
}

/// Registry lookup result used by discovery and planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PromotionOriginLookup {
    /// Exact package/version/module/artifact route exists.
    ExactOriginAlreadyPromoted,
    /// Artifact identity exists under another package origin.
    ArtifactAliasAlreadyPromoted,
    /// Public target module is already reserved.
    TargetModuleCollision,
    /// Target certificate/export identity belongs to another route.
    TargetArtifactCollision,
    /// No registry key matched.
    NoRegistryMatch,
}

/// Lookup one candidate against registry indexes in deterministic priority order.
pub fn lookup_promotion_origin(
    registry: &PromotionOriginRegistry,
    source: &PromotionSourceOrigin,
    target_modules: &[Name],
    target_artifacts: &[(PackageHash, PackageHash)],
) -> PromotionOriginLookup {
    for entry in &registry.entries {
        for origin in std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources) {
            if origin == source {
                return PromotionOriginLookup::ExactOriginAlreadyPromoted;
            }
            if origin.modules.len() == source.modules.len()
                && origin
                    .modules
                    .iter()
                    .zip(&source.modules)
                    .all(|(left, right)| source_module_hashes(left) == source_module_hashes(right))
            {
                return PromotionOriginLookup::ArtifactAliasAlreadyPromoted;
            }
        }
    }
    if registry_target_modules(registry)
        .iter()
        .any(|module| target_modules.contains(module))
    {
        return PromotionOriginLookup::TargetModuleCollision;
    }
    if registry_target_artifacts(registry)
        .iter()
        .any(|identity| target_artifacts.contains(identity))
    {
        return PromotionOriginLookup::TargetArtifactCollision;
    }
    PromotionOriginLookup::NoRegistryMatch
}

/// Parse and validate canonical promotion-origin registry JSON.
pub fn parse_promotion_origin_registry_json(
    source: &str,
) -> PackageArtifactResult<PromotionOriginRegistry> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, REGISTRY_FIELDS)?;
    let registry = PromotionOriginRegistry {
        schema: required_string(members, "$", "schema")?,
        registry_id: required_string(members, "$", "registry_id")?,
        registry_version: required_u64(members, "$", "registry_version")?,
        generation: required_u64(members, "$", "generation")?,
        target_package: PackageId::new(required_string(members, "$", "target_package")?),
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        unresolved_legacy_targets: required_array(members, "$", "unresolved_legacy_targets")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_reservation(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        registry_hash: required_hash(members, "$", "registry_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_promotion_origin_registry(&registry)?;
    if source != registry.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "promotion-origin registry JSON bytes",
        ));
    }
    Ok(registry)
}

/// Compute the registry self-hash.
pub fn promotion_origin_registry_hash(
    registry: &PromotionOriginRegistry,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = registry.clone();
    copy.registry_hash = zero_hash();
    validate_registry_shape(&copy, false)?;
    let json = registry_json(&copy);
    let mut bytes = Vec::with_capacity(REGISTRY_DOMAIN.len() + json.len());
    bytes.extend_from_slice(REGISTRY_DOMAIN);
    bytes.extend_from_slice(json.as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Compute a stable unresolved-target reservation ID from its first revision.
pub fn promotion_legacy_target_reservation_id(
    target_module: &Name,
    revision: &PromotionTargetRevision<PromotionReservedTheorem>,
) -> PackageArtifactResult<PackageHash> {
    validate_module_name(target_module, "target_module")?;
    let identity = json_object_in_order(vec![
        ("target_module", json_string(&target_module.as_dotted())),
        (
            "target_source_file_hash",
            hash_json(revision.target_source_file_hash),
        ),
        (
            "target_certificate_file_hash",
            hash_json(revision.target_certificate_file_hash),
        ),
        (
            "target_certificate_hash",
            hash_json(revision.target_certificate_hash),
        ),
        ("target_export_hash", hash_json(revision.target_export_hash)),
        (
            "target_axiom_report_hash",
            hash_json(revision.target_axiom_report_hash),
        ),
    ]);
    let mut bytes = Vec::with_capacity(LEGACY_TARGET_DOMAIN.len() + identity.len());
    bytes.extend_from_slice(LEGACY_TARGET_DOMAIN);
    bytes.extend_from_slice(identity.as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Validate all registry shape, ordering, uniqueness, and self-hash invariants.
pub fn validate_promotion_origin_registry(
    registry: &PromotionOriginRegistry,
) -> PackageArtifactResult<()> {
    validate_registry_shape(registry, true)
}

/// Validate a permitted append-only v1 registry transition.
pub fn validate_promotion_origin_registry_transition(
    previous: &PromotionOriginRegistry,
    next: &PromotionOriginRegistry,
) -> PackageArtifactResult<()> {
    validate_promotion_origin_registry(previous)?;
    validate_promotion_origin_registry(next)?;
    let expected_generation = previous.generation.checked_add(1).ok_or_else(|| {
        PackageArtifactError::invalid_enum_value(
            "$",
            "registry_transition",
            "same registry identity and next generation",
            "generation overflow",
        )
    })?;
    if previous.schema != next.schema
        || previous.registry_id != next.registry_id
        || previous.registry_version != next.registry_version
        || previous.target_package != next.target_package
        || next.generation != expected_generation
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "registry_transition",
            "same registry identity and next generation",
            "mismatch",
        ));
    }
    let next_entries = next
        .entries
        .iter()
        .map(|entry| (entry.promotion_id, entry))
        .collect::<BTreeMap<_, _>>();
    for old in &previous.entries {
        let Some(new) = next_entries.get(&old.promotion_id) else {
            return Err(transition_error());
        };
        if old.lifecycle != new.lifecycle
            || old.introduced_version != new.introduced_version
            || old.canonical_source != new.canonical_source
            || old.module_routes != new.module_routes
            || old.evidence != new.evidence
            || old
                .equivalent_sources
                .iter()
                .any(|origin| !new.equivalent_sources.contains(origin))
        {
            return Err(transition_error());
        }
    }
    let next_reservations = next
        .unresolved_legacy_targets
        .iter()
        .map(|entry| (entry.reservation_id, entry))
        .collect::<BTreeMap<_, _>>();
    if previous.unresolved_legacy_targets.iter().any(|old| {
        next_reservations
            .get(&old.reservation_id)
            .is_none_or(|new| *new != old)
    }) {
        return Err(transition_error());
    }
    Ok(())
}

fn validate_registry_shape(
    registry: &PromotionOriginRegistry,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    if registry.schema != MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA,
            &registry.schema,
        ));
    }
    if registry.registry_id != MATHLIB_PROMOTION_REGISTRY_ID
        || registry.registry_version != 1
        || registry.generation == 0
        || registry.target_package.as_str() != "npa-mathlib"
        || registry.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "registry",
            "strict npa-mathlib registry v1",
            "mismatch",
        ));
    }
    let mut previous_id = None;
    let mut origin_routes = BTreeSet::new();
    let mut target_modules = BTreeSet::new();
    let mut target_artifacts = BTreeMap::new();
    let mut target_theorems = BTreeSet::new();
    for (index, entry) in registry.entries.iter().enumerate() {
        if previous_id.is_some_and(|old| old >= entry.promotion_id) {
            return Err(PackageArtifactError::non_canonical(
                "entries",
                "strict promotion_id order",
            ));
        }
        previous_id = Some(entry.promotion_id);
        validate_entry(entry, index)?;
        for origin in std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources) {
            for module in &origin.modules {
                let route = (
                    origin.package.as_str().to_owned(),
                    origin.version.as_str().to_owned(),
                    module.module.clone(),
                );
                if !origin_routes.insert(route) {
                    return Err(duplicate_error("entries", "origin route"));
                }
            }
        }
        for route in &entry.module_routes {
            record_target_route(
                &route.target_module,
                &route.target_revisions,
                &mut target_modules,
                &mut target_artifacts,
                &mut target_theorems,
            )?;
        }
    }
    let mut previous_reservation = None;
    for (index, reservation) in registry.unresolved_legacy_targets.iter().enumerate() {
        if previous_reservation.is_some_and(|old| old >= reservation.reservation_id) {
            return Err(PackageArtifactError::non_canonical(
                "unresolved_legacy_targets",
                "strict reservation_id order",
            ));
        }
        previous_reservation = Some(reservation.reservation_id);
        validate_reservation(reservation, index)?;
        record_reserved_target(
            reservation,
            &mut target_modules,
            &mut target_artifacts,
            &mut target_theorems,
        )?;
    }
    if check_hash && registry.registry_hash != promotion_origin_registry_hash(registry)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "registry_hash",
            "registry_hash",
            "matching promotion-origin registry self-hash",
            "mismatch",
        ));
    }
    Ok(())
}

pub(crate) fn validate_entry(
    entry: &PromotionOriginEntry,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("entries[{index}]");
    validate_source(&entry.canonical_source, &format!("{path}.canonical_source"))?;
    validate_version(
        &entry.introduced_version,
        &format!("{path}.introduced_version"),
    )?;
    validate_lifecycle(&entry.lifecycle, &path)?;
    validate_evidence(&entry.evidence, &format!("{path}.evidence"), false)?;
    if entry.module_routes.is_empty()
        || entry.module_routes.len() != entry.canonical_source.modules.len()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "module_routes",
            "one route per canonical source module",
            "mismatch",
        ));
    }
    let canonical_hashes = entry
        .canonical_source
        .modules
        .iter()
        .map(source_module_hashes)
        .collect::<Vec<_>>();
    let mut previous_source = None::<(String, String)>;
    for (alias_index, source) in entry.equivalent_sources.iter().enumerate() {
        validate_source(source, &format!("{path}.equivalent_sources[{alias_index}]"))?;
        let key = (
            source.package.as_str().to_owned(),
            source.version.as_str().to_owned(),
        );
        if key
            == (
                entry.canonical_source.package.as_str().to_owned(),
                entry.canonical_source.version.as_str().to_owned(),
            )
            || previous_source.as_ref().is_some_and(|old| old >= &key)
            || source.modules.len() != canonical_hashes.len()
            || source.modules.iter().map(|module| &module.module).ne(entry
                .canonical_source
                .modules
                .iter()
                .map(|module| &module.module))
            || source
                .modules
                .iter()
                .map(source_module_hashes)
                .ne(canonical_hashes.iter().copied())
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.equivalent_sources"),
                "sorted complete artifact-identical aliases",
            ));
        }
        previous_source = Some(key);
    }
    let mut previous_route = None;
    let mut routed_sources = BTreeSet::new();
    for (route_index, route) in entry.module_routes.iter().enumerate() {
        let key = (
            route.source_module.as_dotted(),
            route.target_module.as_dotted(),
        );
        if previous_route.as_ref().is_some_and(|old| old >= &key) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.module_routes"),
                "sorted module routes",
            ));
        }
        previous_route = Some(key);
        if !routed_sources.insert(route.source_module.clone()) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.module_routes"),
                "one route per source module",
            ));
        }
        validate_route(route, &format!("{path}.module_routes[{route_index}]"))?;
        if route.target_revisions[0].target_version != entry.introduced_version
            || !entry
                .canonical_source
                .modules
                .iter()
                .any(|module| module.module == route.source_module)
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.module_routes[{route_index}]"),
                "route",
                "canonical source route with introduced revision",
                "mismatch",
            ));
        }
        validate_retirement_after(
            &entry.lifecycle,
            route.target_revisions.last().unwrap(),
            &path,
        )?;
    }
    Ok(())
}

fn validate_source(source: &PromotionSourceOrigin, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&source.package, &source.version)?;
    if source.modules.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "modules",
            "nonempty selected module inventory",
            "empty",
        ));
    }
    let mut previous = None;
    for (index, module) in source.modules.iter().enumerate() {
        validate_module_name(&module.module, format!("{path}.modules[{index}].module"))?;
        if previous.as_ref().is_some_and(|old| old >= module) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.modules"),
                "strict module/artifact order",
            ));
        }
        previous = Some(module.clone());
    }
    Ok(())
}

fn validate_route(route: &PromotionModuleRoute, path: &str) -> PackageArtifactResult<()> {
    validate_module_name(&route.source_module, format!("{path}.source_module"))?;
    validate_module_name(&route.target_module, format!("{path}.target_module"))?;
    if route.declaration_mapping != "same-name-except-explicit" || route.target_revisions.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "route",
            "same-name-except-explicit with revisions",
            "mismatch",
        ));
    }
    let mut previous_rename = None;
    for rename in &route.renames {
        validate_declaration_name(&rename.source, format!("{path}.renames.source"))?;
        validate_declaration_name(&rename.target, format!("{path}.renames.target"))?;
        if previous_rename.as_ref().is_some_and(|old| old >= rename) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.renames"),
                "strict rename order",
            ));
        }
        previous_rename = Some(rename.clone());
    }
    validate_revisions(&route.target_revisions, path, |theorem, theorem_path| {
        validate_declaration_name(&theorem.source_name, format!("{theorem_path}.source_name"))?;
        validate_declaration_name(&theorem.target_name, format!("{theorem_path}.target_name"))?;
        Ok((
            theorem.source_name.as_dotted(),
            theorem.target_name.as_dotted(),
        ))
    })
}

pub(crate) fn validate_reservation(
    reservation: &PromotionLegacyTargetReservation,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("unresolved_legacy_targets[{index}]");
    validate_module_name(&reservation.target_module, format!("{path}.target_module"))?;
    validate_lifecycle(&reservation.lifecycle, &path)?;
    validate_evidence(&reservation.evidence, &format!("{path}.evidence"), true)?;
    if reservation.target_revisions.is_empty()
        || reservation.reservation_id
            != promotion_legacy_target_reservation_id(
                &reservation.target_module,
                &reservation.target_revisions[0],
            )?
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "reservation_id",
            "derived nonempty legacy reservation",
            "mismatch",
        ));
    }
    validate_revisions(
        &reservation.target_revisions,
        &path,
        |theorem, theorem_path| {
            validate_declaration_name(&theorem.target_name, format!("{theorem_path}.target_name"))?;
            Ok(theorem.target_name.as_dotted())
        },
    )?;
    validate_retirement_after(
        &reservation.lifecycle,
        reservation.target_revisions.last().unwrap(),
        &path,
    )
}

fn validate_retirement_after<T>(
    lifecycle: &PromotionLifecycle,
    latest: &PromotionTargetRevision<T>,
    path: &str,
) -> PackageArtifactResult<()> {
    if let PromotionLifecycle::Retired {
        retired_version, ..
    } = lifecycle
    {
        if version_tuple(retired_version)? <= version_tuple(&latest.target_version)? {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.lifecycle.retired_version"),
                "retired_version",
                "version later than latest target revision",
                retired_version.as_str(),
            ));
        }
    }
    Ok(())
}

fn validate_revisions<T, K: Ord, F>(
    revisions: &[PromotionTargetRevision<T>],
    path: &str,
    mut theorem_key: F,
) -> PackageArtifactResult<()>
where
    F: FnMut(&T, &str) -> PackageArtifactResult<K>,
{
    let mut previous_version = None;
    for (index, revision) in revisions.iter().enumerate() {
        validate_version(
            &revision.target_version,
            &format!("{path}.target_revisions[{index}].target_version"),
        )?;
        let version = version_tuple(&revision.target_version)?;
        if previous_version.is_some_and(|old| old >= version) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.target_revisions"),
                "strict numeric version order",
            ));
        }
        previous_version = Some(version);
        let mut previous_theorem = None;
        for (theorem_index, theorem) in revision.theorems.iter().enumerate() {
            let theorem_path =
                format!("{path}.target_revisions[{index}].theorems[{theorem_index}]");
            let key = theorem_key(theorem, &theorem_path)?;
            if previous_theorem.as_ref().is_some_and(|old| old >= &key) {
                return Err(PackageArtifactError::non_canonical(
                    format!("{path}.target_revisions[{index}].theorems"),
                    "strict theorem order",
                ));
            }
            previous_theorem = Some(key);
        }
    }
    Ok(())
}

fn validate_lifecycle(lifecycle: &PromotionLifecycle, path: &str) -> PackageArtifactResult<()> {
    if let PromotionLifecycle::Retired {
        retired_version,
        audit_location,
        ..
    } = lifecycle
    {
        validate_version(
            retired_version,
            &format!("{path}.lifecycle.retired_version"),
        )?;
        validate_audit_location(audit_location, &format!("{path}.lifecycle.audit_location"))?;
    }
    Ok(())
}

fn validate_evidence(
    evidence: &PromotionEvidence,
    path: &str,
    require_legacy: bool,
) -> PackageArtifactResult<()> {
    match evidence {
        PromotionEvidence::NamespaceTransportV2 {
            plan_schema,
            plan_path,
            acceptance,
            transport,
            ..
        } if !require_legacy => {
            if plan_schema != "npa.mathlib.promotion_plan.v1"
                || acceptance.source_ledger_schema != "npa.l2_acceptance.v2"
                || transport.mapping_request_schema != "npa.l2_namespace_transport_request.v1"
                || transport.attestation_schema != "npa.l2_namespace_transport_attestation.v2"
                || acceptance.policy_version == 0
                || transport.policy_version == 0
            {
                return Err(PackageArtifactError::invalid_enum_value(
                    path,
                    "evidence",
                    "current namespace transport schemas",
                    "mismatch",
                ));
            }
            validate_plain_string(
                &acceptance.policy_id,
                format!("{path}.acceptance.policy_id"),
            )?;
            validate_plain_string(&transport.policy_id, format!("{path}.transport.policy_id"))?;
            validate_package_path(plan_path, format!("{path}.plan_path"))
                .map_err(|_| PackageArtifactError::invalid_path(path, plan_path.as_str()))?;
            for (value, field) in [
                (&acceptance.source_ledger_path, "source_ledger_path"),
                (&transport.mapping_request_path, "mapping_request_path"),
                (&transport.attestation_path, "attestation_path"),
            ] {
                validate_package_path(value, format!("{path}.{field}"))
                    .map_err(|_| PackageArtifactError::invalid_path(path, value.as_str()))?;
            }
            Ok(())
        }
        PromotionEvidence::LegacyAudit { audit_location, .. } => {
            validate_audit_location(audit_location, &format!("{path}.audit_location"))
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            path,
            "evidence",
            "legacy_audit evidence",
            "namespace_transport_v2",
        )),
    }
}

fn validate_audit_location(
    location: &PromotionAuditLocation,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_plain_string(&location.repository, format!("{path}.repository"))?;
    validate_package_path(&location.path, format!("{path}.path"))
        .map_err(|_| PackageArtifactError::invalid_path(path, location.path.as_str()))
}

fn record_target_route<T>(
    module: &Name,
    revisions: &[PromotionTargetRevision<T>],
    modules: &mut BTreeSet<Name>,
    artifacts: &mut BTreeMap<(PackageHash, PackageHash), Name>,
    theorems: &mut BTreeSet<(Name, String)>,
) -> PackageArtifactResult<()>
where
    T: TargetTheoremName,
{
    if !modules.insert(module.clone()) {
        return Err(duplicate_error("module_routes", "target module"));
    }
    for revision in revisions {
        if let Some(existing) = artifacts.insert(
            (
                revision.target_certificate_hash,
                revision.target_export_hash,
            ),
            module.clone(),
        ) {
            if existing != *module {
                return Err(duplicate_error("target_revisions", "target artifact"));
            }
        }
        for theorem in &revision.theorems {
            let name = theorem.target_name_string();
            theorems.insert((module.clone(), name));
        }
    }
    Ok(())
}

trait TargetTheoremName {
    fn target_name_string(&self) -> String;
}
impl TargetTheoremName for PromotionRouteTheorem {
    fn target_name_string(&self) -> String {
        self.target_name.as_dotted()
    }
}
impl TargetTheoremName for PromotionReservedTheorem {
    fn target_name_string(&self) -> String {
        self.target_name.as_dotted()
    }
}

fn record_reserved_target(
    reservation: &PromotionLegacyTargetReservation,
    modules: &mut BTreeSet<Name>,
    artifacts: &mut BTreeMap<(PackageHash, PackageHash), Name>,
    theorems: &mut BTreeSet<(Name, String)>,
) -> PackageArtifactResult<()> {
    record_target_route(
        &reservation.target_module,
        &reservation.target_revisions,
        modules,
        artifacts,
        theorems,
    )
}

fn registry_target_modules(registry: &PromotionOriginRegistry) -> Vec<Name> {
    registry
        .entries
        .iter()
        .flat_map(|entry| {
            entry
                .module_routes
                .iter()
                .map(|route| route.target_module.clone())
        })
        .chain(
            registry
                .unresolved_legacy_targets
                .iter()
                .map(|entry| entry.target_module.clone()),
        )
        .collect()
}

fn registry_target_artifacts(
    registry: &PromotionOriginRegistry,
) -> Vec<(PackageHash, PackageHash)> {
    registry
        .entries
        .iter()
        .flat_map(|entry| &entry.module_routes)
        .flat_map(|route| &route.target_revisions)
        .map(|revision| {
            (
                revision.target_certificate_hash,
                revision.target_export_hash,
            )
        })
        .chain(
            registry
                .unresolved_legacy_targets
                .iter()
                .flat_map(|entry| &entry.target_revisions)
                .map(|revision| {
                    (
                        revision.target_certificate_hash,
                        revision.target_export_hash,
                    )
                }),
        )
        .collect()
}

fn source_module_hashes(
    module: &PromotionSourceModule,
) -> (PackageHash, PackageHash, PackageHash, PackageHash) {
    (
        module.source_file_hash,
        module.certificate_file_hash,
        module.certificate_hash,
        module.export_hash,
    )
}

fn validate_version(version: &PackageVersion, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&PackageId::new("version-check"), version)
        .map_err(|_| PackageArtifactError::invalid_version(path, version.as_str()))
}

fn version_tuple(version: &PackageVersion) -> PackageArtifactResult<(u64, u64, u64)> {
    let values = version
        .as_str()
        .split('.')
        .map(str::parse::<u64>)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| PackageArtifactError::invalid_version("version", version.as_str()))?;
    if values.len() != 3 {
        return Err(PackageArtifactError::invalid_version(
            "version",
            version.as_str(),
        ));
    }
    Ok((values[0], values[1], values[2]))
}

fn transition_error() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "registry_transition",
        "append-only v1 transition",
        "mutation",
    )
}

fn duplicate_error(path: &str, actual: &str) -> PackageArtifactError {
    PackageArtifactError::non_canonical(path, actual)
}

pub(crate) fn parse_entry(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<PromotionOriginEntry> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    Ok(PromotionOriginEntry {
        promotion_id: required_hash(members, &path, "promotion_id")?,
        lifecycle: parse_lifecycle(required_value(members, &path, "lifecycle")?, &path)?,
        introduced_version: PackageVersion::new(required_string(
            members,
            &path,
            "introduced_version",
        )?),
        canonical_source: parse_source(
            required_value(members, &path, "canonical_source")?,
            &format!("{path}.canonical_source"),
        )?,
        equivalent_sources: required_array(members, &path, "equivalent_sources")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_source(value, &format!("{path}.equivalent_sources[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        module_routes: required_array(members, &path, "module_routes")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_route(value, &format!("{path}.module_routes[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        evidence: parse_evidence(
            required_value(members, &path, "evidence")?,
            &format!("{path}.evidence"),
        )?,
    })
}

fn parse_source(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionSourceOrigin> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_FIELDS)?;
    Ok(PromotionSourceOrigin {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        modules: required_array(members, path, "modules")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_source_module(value, &format!("{path}.modules[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_source_module(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionSourceModule> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_MODULE_FIELDS)?;
    Ok(PromotionSourceModule {
        module: required_name(members, path, "module")?,
        source_file_hash: required_hash(members, path, "source_file_hash")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
    })
}

fn parse_route(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionModuleRoute> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ROUTE_FIELDS)?;
    Ok(PromotionModuleRoute {
        source_module: required_name(members, path, "source_module")?,
        target_module: required_name(members, path, "target_module")?,
        declaration_mapping: required_string(members, path, "declaration_mapping")?,
        renames: required_array(members, path, "renames")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_rename(value, &format!("{path}.renames[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        target_revisions: required_array(members, path, "target_revisions")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_revision(
                    value,
                    &format!("{path}.target_revisions[{index}]"),
                    parse_route_theorem,
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_rename(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionDeclarationRename> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, RENAME_FIELDS)?;
    Ok(PromotionDeclarationRename {
        source: required_name(members, path, "source")?,
        target: required_name(members, path, "target")?,
    })
}

fn parse_revision<T, F>(
    value: &JsonValue,
    path: &str,
    mut parse_theorem: F,
) -> PackageArtifactResult<PromotionTargetRevision<T>>
where
    F: FnMut(&JsonValue, &str) -> PackageArtifactResult<T>,
{
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REVISION_FIELDS)?;
    Ok(PromotionTargetRevision {
        target_version: PackageVersion::new(required_string(members, path, "target_version")?),
        target_source_file_hash: required_hash(members, path, "target_source_file_hash")?,
        target_certificate_file_hash: required_hash(members, path, "target_certificate_file_hash")?,
        target_certificate_hash: required_hash(members, path, "target_certificate_hash")?,
        target_export_hash: required_hash(members, path, "target_export_hash")?,
        target_axiom_report_hash: required_hash(members, path, "target_axiom_report_hash")?,
        theorems: required_array(members, path, "theorems")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_theorem(value, &format!("{path}.theorems[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_route_theorem(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionRouteTheorem> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ROUTE_THEOREM_FIELDS)?;
    Ok(PromotionRouteTheorem {
        source_name: required_name(members, path, "source_name")?,
        source_statement_hash: required_hash(members, path, "source_statement_hash")?,
        target_name: required_name(members, path, "target_name")?,
        target_statement_hash: required_hash(members, path, "target_statement_hash")?,
    })
}

fn parse_reserved_theorem(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionReservedTheorem> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, RESERVATION_THEOREM_FIELDS)?;
    Ok(PromotionReservedTheorem {
        target_name: required_name(members, path, "target_name")?,
        target_statement_hash: required_hash(members, path, "target_statement_hash")?,
    })
}

fn parse_lifecycle(value: &JsonValue, parent: &str) -> PackageArtifactResult<PromotionLifecycle> {
    let path = format!("{parent}.lifecycle");
    let members = expect_object(value, &path)?;
    let kind = required_string(members, &path, "kind")?;
    match kind.as_str() {
        "active" => {
            reject_unknown_fields(&path, members, ACTIVE_FIELDS)?;
            Ok(PromotionLifecycle::Active)
        }
        "retired" => {
            reject_unknown_fields(&path, members, RETIRED_FIELDS)?;
            Ok(PromotionLifecycle::Retired {
                retired_version: PackageVersion::new(required_string(
                    members,
                    &path,
                    "retired_version",
                )?),
                audit_location: parse_audit_location(
                    required_value(members, &path, "audit_location")?,
                    &format!("{path}.audit_location"),
                )?,
                audit_file_hash: required_hash(members, &path, "audit_file_hash")?,
            })
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            &path,
            "kind",
            "active or retired",
            kind,
        )),
    }
}

fn parse_audit_location(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionAuditLocation> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, AUDIT_LOCATION_FIELDS)?;
    Ok(PromotionAuditLocation {
        repository: required_string(members, path, "repository")?,
        path: required_path(members, path, "path")?,
    })
}

fn parse_evidence(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionEvidence> {
    let members = expect_object(value, path)?;
    let kind = required_string(members, path, "kind")?;
    match kind.as_str() {
        "namespace_transport_v2" => {
            reject_unknown_fields(path, members, NAMESPACE_EVIDENCE_FIELDS)?;
            Ok(PromotionEvidence::NamespaceTransportV2 {
                plan_schema: required_string(members, path, "plan_schema")?,
                plan_path: required_path(members, path, "plan_path")?,
                plan_file_hash: required_hash(members, path, "plan_file_hash")?,
                acceptance: Box::new(parse_acceptance_evidence(
                    required_value(members, path, "acceptance")?,
                    &format!("{path}.acceptance"),
                )?),
                transport: Box::new(parse_transport_evidence(
                    required_value(members, path, "transport")?,
                    &format!("{path}.transport"),
                )?),
            })
        }
        "legacy_audit" => {
            reject_unknown_fields(path, members, LEGACY_EVIDENCE_FIELDS)?;
            Ok(PromotionEvidence::LegacyAudit {
                audit_location: parse_audit_location(
                    required_value(members, path, "audit_location")?,
                    &format!("{path}.audit_location"),
                )?,
                audit_file_hash: required_hash(members, path, "audit_file_hash")?,
            })
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            path,
            "kind",
            "namespace_transport_v2 or legacy_audit",
            kind,
        )),
    }
}

fn parse_acceptance_evidence(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionAcceptanceEvidence> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ACCEPTANCE_EVIDENCE_FIELDS)?;
    Ok(PromotionAcceptanceEvidence {
        policy_id: required_string(members, path, "policy_id")?,
        policy_version: required_u64(members, path, "policy_version")?,
        policy_file_hash: required_hash(members, path, "policy_file_hash")?,
        source_ledger_schema: required_string(members, path, "source_ledger_schema")?,
        source_ledger_path: required_path(members, path, "source_ledger_path")?,
        source_ledger_file_hash: required_hash(members, path, "source_ledger_file_hash")?,
    })
}

fn parse_transport_evidence(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionTransportEvidence> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TRANSPORT_EVIDENCE_FIELDS)?;
    Ok(PromotionTransportEvidence {
        policy_id: required_string(members, path, "policy_id")?,
        policy_version: required_u64(members, path, "policy_version")?,
        policy_file_hash: required_hash(members, path, "policy_file_hash")?,
        mapping_request_schema: required_string(members, path, "mapping_request_schema")?,
        mapping_request_path: required_path(members, path, "mapping_request_path")?,
        mapping_request_file_hash: required_hash(members, path, "mapping_request_file_hash")?,
        attestation_schema: required_string(members, path, "attestation_schema")?,
        attestation_path: required_path(members, path, "attestation_path")?,
        attestation_file_hash: required_hash(members, path, "attestation_file_hash")?,
        normalized_closure_hash: required_hash(members, path, "normalized_closure_hash")?,
    })
}

pub(crate) fn parse_reservation(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<PromotionLegacyTargetReservation> {
    let path = format!("unresolved_legacy_targets[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, RESERVATION_FIELDS)?;
    Ok(PromotionLegacyTargetReservation {
        reservation_id: required_hash(members, &path, "reservation_id")?,
        lifecycle: parse_lifecycle(required_value(members, &path, "lifecycle")?, &path)?,
        target_module: required_name(members, &path, "target_module")?,
        target_revisions: required_array(members, &path, "target_revisions")?
            .iter()
            .enumerate()
            .map(|(i, value)| {
                parse_revision(
                    value,
                    &format!("{path}.target_revisions[{i}]"),
                    parse_reserved_theorem,
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        evidence: parse_evidence(
            required_value(members, &path, "evidence")?,
            &format!("{path}.evidence"),
        )?,
    })
}

fn registry_json(registry: &PromotionOriginRegistry) -> String {
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
                    .map(reservation_json)
                    .collect(),
            ),
        ),
        ("registry_hash", hash_json(registry.registry_hash)),
        ("proof_evidence", json_bool(registry.proof_evidence)),
    ])
}

pub(crate) fn entry_json(entry: &PromotionOriginEntry) -> String {
    json_object_in_order(vec![
        ("promotion_id", hash_json(entry.promotion_id)),
        ("lifecycle", lifecycle_json(&entry.lifecycle)),
        (
            "introduced_version",
            json_string(entry.introduced_version.as_str()),
        ),
        ("canonical_source", source_json(&entry.canonical_source)),
        (
            "equivalent_sources",
            json_array(entry.equivalent_sources.iter().map(source_json).collect()),
        ),
        (
            "module_routes",
            json_array(entry.module_routes.iter().map(route_json).collect()),
        ),
        ("evidence", evidence_json(&entry.evidence)),
    ])
}

fn source_json(source: &PromotionSourceOrigin) -> String {
    json_object_in_order(vec![
        ("package", json_string(source.package.as_str())),
        ("version", json_string(source.version.as_str())),
        (
            "modules",
            json_array(source.modules.iter().map(source_module_json).collect()),
        ),
    ])
}

fn source_module_json(module: &PromotionSourceModule) -> String {
    json_object_in_order(vec![
        ("module", json_string(&module.module.as_dotted())),
        ("source_file_hash", hash_json(module.source_file_hash)),
        (
            "certificate_file_hash",
            hash_json(module.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(module.certificate_hash)),
        ("export_hash", hash_json(module.export_hash)),
    ])
}

fn route_json(route: &PromotionModuleRoute) -> String {
    json_object_in_order(vec![
        (
            "source_module",
            json_string(&route.source_module.as_dotted()),
        ),
        (
            "target_module",
            json_string(&route.target_module.as_dotted()),
        ),
        (
            "declaration_mapping",
            json_string(&route.declaration_mapping),
        ),
        (
            "renames",
            json_array(route.renames.iter().map(rename_json).collect()),
        ),
        (
            "target_revisions",
            json_array(
                route
                    .target_revisions
                    .iter()
                    .map(|revision| revision_json(revision, route_theorem_json))
                    .collect(),
            ),
        ),
    ])
}

fn rename_json(rename: &PromotionDeclarationRename) -> String {
    json_object_in_order(vec![
        ("source", json_string(&rename.source.as_dotted())),
        ("target", json_string(&rename.target.as_dotted())),
    ])
}

fn revision_json<T, F>(revision: &PromotionTargetRevision<T>, theorem_json: F) -> String
where
    F: Fn(&T) -> String,
{
    json_object_in_order(vec![
        (
            "target_version",
            json_string(revision.target_version.as_str()),
        ),
        (
            "target_source_file_hash",
            hash_json(revision.target_source_file_hash),
        ),
        (
            "target_certificate_file_hash",
            hash_json(revision.target_certificate_file_hash),
        ),
        (
            "target_certificate_hash",
            hash_json(revision.target_certificate_hash),
        ),
        ("target_export_hash", hash_json(revision.target_export_hash)),
        (
            "target_axiom_report_hash",
            hash_json(revision.target_axiom_report_hash),
        ),
        (
            "theorems",
            json_array(revision.theorems.iter().map(theorem_json).collect()),
        ),
    ])
}

fn route_theorem_json(theorem: &PromotionRouteTheorem) -> String {
    json_object_in_order(vec![
        ("source_name", json_string(&theorem.source_name.as_dotted())),
        (
            "source_statement_hash",
            hash_json(theorem.source_statement_hash),
        ),
        ("target_name", json_string(&theorem.target_name.as_dotted())),
        (
            "target_statement_hash",
            hash_json(theorem.target_statement_hash),
        ),
    ])
}

fn reserved_theorem_json(theorem: &PromotionReservedTheorem) -> String {
    json_object_in_order(vec![
        ("target_name", json_string(&theorem.target_name.as_dotted())),
        (
            "target_statement_hash",
            hash_json(theorem.target_statement_hash),
        ),
    ])
}

fn lifecycle_json(lifecycle: &PromotionLifecycle) -> String {
    match lifecycle {
        PromotionLifecycle::Active => json_object_in_order(vec![("kind", json_string("active"))]),
        PromotionLifecycle::Retired {
            retired_version,
            audit_location,
            audit_file_hash,
        } => json_object_in_order(vec![
            ("kind", json_string("retired")),
            ("retired_version", json_string(retired_version.as_str())),
            ("audit_location", audit_location_json(audit_location)),
            ("audit_file_hash", hash_json(*audit_file_hash)),
        ]),
    }
}

fn audit_location_json(location: &PromotionAuditLocation) -> String {
    json_object_in_order(vec![
        ("repository", json_string(&location.repository)),
        ("path", json_string(location.path.as_str())),
    ])
}

fn evidence_json(evidence: &PromotionEvidence) -> String {
    match evidence {
        PromotionEvidence::NamespaceTransportV2 {
            plan_schema,
            plan_path,
            plan_file_hash,
            acceptance,
            transport,
        } => json_object_in_order(vec![
            ("kind", json_string("namespace_transport_v2")),
            ("plan_schema", json_string(plan_schema)),
            ("plan_path", json_string(plan_path.as_str())),
            ("plan_file_hash", hash_json(*plan_file_hash)),
            ("acceptance", acceptance_evidence_json(acceptance)),
            ("transport", transport_evidence_json(transport)),
        ]),
        PromotionEvidence::LegacyAudit {
            audit_location,
            audit_file_hash,
        } => json_object_in_order(vec![
            ("kind", json_string("legacy_audit")),
            ("audit_location", audit_location_json(audit_location)),
            ("audit_file_hash", hash_json(*audit_file_hash)),
        ]),
    }
}

fn acceptance_evidence_json(value: &PromotionAcceptanceEvidence) -> String {
    json_object_in_order(vec![
        ("policy_id", json_string(&value.policy_id)),
        ("policy_version", json_u64(value.policy_version)),
        ("policy_file_hash", hash_json(value.policy_file_hash)),
        (
            "source_ledger_schema",
            json_string(&value.source_ledger_schema),
        ),
        (
            "source_ledger_path",
            json_string(value.source_ledger_path.as_str()),
        ),
        (
            "source_ledger_file_hash",
            hash_json(value.source_ledger_file_hash),
        ),
    ])
}

fn transport_evidence_json(value: &PromotionTransportEvidence) -> String {
    json_object_in_order(vec![
        ("policy_id", json_string(&value.policy_id)),
        ("policy_version", json_u64(value.policy_version)),
        ("policy_file_hash", hash_json(value.policy_file_hash)),
        (
            "mapping_request_schema",
            json_string(&value.mapping_request_schema),
        ),
        (
            "mapping_request_path",
            json_string(value.mapping_request_path.as_str()),
        ),
        (
            "mapping_request_file_hash",
            hash_json(value.mapping_request_file_hash),
        ),
        ("attestation_schema", json_string(&value.attestation_schema)),
        (
            "attestation_path",
            json_string(value.attestation_path.as_str()),
        ),
        (
            "attestation_file_hash",
            hash_json(value.attestation_file_hash),
        ),
        (
            "normalized_closure_hash",
            hash_json(value.normalized_closure_hash),
        ),
    ])
}

pub(crate) fn reservation_json(reservation: &PromotionLegacyTargetReservation) -> String {
    json_object_in_order(vec![
        ("reservation_id", hash_json(reservation.reservation_id)),
        ("lifecycle", lifecycle_json(&reservation.lifecycle)),
        (
            "target_module",
            json_string(&reservation.target_module.as_dotted()),
        ),
        (
            "target_revisions",
            json_array(
                reservation
                    .target_revisions
                    .iter()
                    .map(|revision| revision_json(revision, reserved_theorem_json))
                    .collect(),
            ),
        ),
        ("evidence", evidence_json(&reservation.evidence)),
    ])
}

const fn zero_hash() -> PackageHash {
    PackageHash::new([0; 32])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_registry_round_trips_and_hashes() {
        let mut registry = PromotionOriginRegistry {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 1,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries: Vec::new(),
            unresolved_legacy_targets: Vec::new(),
            registry_hash: zero_hash(),
            proof_evidence: false,
        };
        registry.refresh_hash().unwrap();
        assert_eq!(
            crate::format_package_hash(&registry.registry_hash),
            "sha256:675bc234852868bf174d73536ec045ea39eb9e68b658ebebbdf84ff50fa1d471"
        );
        let json = registry.canonical_json().unwrap();
        assert_eq!(
            parse_promotion_origin_registry_json(&json).unwrap(),
            registry
        );
    }

    #[test]
    fn transition_rejects_generation_overflow_without_panicking() {
        let mut previous = PromotionOriginRegistry {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 1,
            generation: u64::MAX,
            target_package: PackageId::new("npa-mathlib"),
            entries: Vec::new(),
            unresolved_legacy_targets: Vec::new(),
            registry_hash: zero_hash(),
            proof_evidence: false,
        };
        previous.refresh_hash().unwrap();
        let next = previous.clone();

        assert!(validate_promotion_origin_registry_transition(&previous, &next).is_err());
    }
}

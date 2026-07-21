//! Declaration-aware mathlib promotion-origin registry v2.
//!
//! Registry v2 losslessly wraps every historical v1 sourced entry and keeps
//! legacy target reservations at the top level. New declaration routes bind
//! verified materialization evidence and exact selected closure identities.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_path, required_string, required_u64, required_value,
        validate_declaration_name, validate_module_name, validate_package_identity,
        PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    promotion_materialization_attestation::{
        validate_verified_materialization_attestation, VerifiedMaterializationAttestation,
    },
    promotion_plan_v2::{
        declaration_json, equivalent_json, mapping_json, mathlib_declaration_promotion_route_id_v2,
        parse_declaration, parse_equivalent, parse_mapping, parse_root,
        promotion_plan_v2_dependency_edge_hash, root_json,
        validate_declaration_promotion_resource_count,
        validate_declaration_promotion_resource_limits, validate_mathlib_promotion_plan_v2,
        validate_promotion_plan_v2_closure_relationships, validate_promotion_plan_v2_declaration,
        validate_promotion_plan_v2_mapping, validate_promotion_plan_v2_root,
        MathlibPromotionPlanV2, PromotionPlanV2Declaration, PromotionPlanV2DependencyMapping,
        PromotionPlanV2EquivalentSource, PromotionPlanV2Root,
        DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
        DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES,
        DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
        DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
        DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS,
    },
    promotion_registry::{
        entry_json as v1_entry_json, parse_entry as parse_v1_entry,
        parse_reservation as parse_v1_reservation, reservation_json as v1_reservation_json,
        validate_entry as validate_v1_entry, validate_promotion_origin_registry,
        validate_reservation as validate_v1_reservation, PromotionLegacyTargetReservation,
        PromotionOriginEntry, PromotionOriginLookup, PromotionOriginRegistry,
        PromotionSourceModule, PromotionSourceOrigin, MATHLIB_PROMOTION_REGISTRY_ID,
    },
    schema::{
        MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA, MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA,
        MATHLIB_PROMOTION_PLAN_V2_SCHEMA, MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA,
    },
};

const REGISTRY_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-ORIGIN-REGISTRY-v2\0";
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
const WRAPPER_FIELDS: &[&str] = &["kind", "v1_entry"];
const DECLARATION_FIELDS: &[&str] = &[
    "kind",
    "promotion_id",
    "lifecycle",
    "introduced_version",
    "canonical_source",
    "equivalent_sources",
    "source_module",
    "target_module",
    "roots",
    "closure",
    "dependency_mappings",
    "target_revisions",
    "evidence",
    "maturity_events",
];
const REVISION_FIELDS: &[&str] = &[
    "target_version",
    "target_source_file_hash",
    "target_meta_file_hash",
    "target_replay_file_hash",
    "target_certificate_file_hash",
    "target_certificate_hash",
    "target_export_hash",
    "target_axiom_report_hash",
    "theorems",
];
const THEOREM_FIELDS: &[&str] = &["target_name", "statement_hash"];
const EVIDENCE_FIELDS: &[&str] = &[
    "kind",
    "plan_schema",
    "plan_path",
    "plan_file_hash",
    "attestation_schema",
    "attestation_path",
    "attestation_file_hash",
    "declaration_closure_hash",
    "normalized_closure_hash",
    "catalog_policy_file_hash",
    "namespace_policy_file_hash",
];
const MATURITY_FIELDS: &[&str] = &["kind", "target_version", "evidence_file_hash"];
const MAX_TARGET_REVISIONS: usize = 1;
const MAX_MATURITY_EVENTS: usize = 0;
// A target theorem is either materialized directly or emitted by one.
const MAX_TARGET_THEOREMS: usize = DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS
    + DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS;

/// Immutable target theorem identity in a declaration route revision.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionDeclarationTargetTheorem {
    /// Public theorem name.
    pub target_name: Name,
    /// Checked statement hash.
    pub statement_hash: PackageHash,
}

/// Immutable target artifact identity for one declaration route version.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionDeclarationTargetRevision {
    /// Target release version.
    pub target_version: PackageVersion,
    /// Target source bytes hash.
    pub target_source_file_hash: PackageHash,
    /// Target metadata bytes hash.
    pub target_meta_file_hash: PackageHash,
    /// Target replay bytes hash.
    pub target_replay_file_hash: PackageHash,
    /// Target certificate bytes hash.
    pub target_certificate_file_hash: PackageHash,
    /// Canonical target certificate hash.
    pub target_certificate_hash: PackageHash,
    /// Canonical target export hash.
    pub target_export_hash: PackageHash,
    /// Canonical target axiom-report hash.
    pub target_axiom_report_hash: PackageHash,
    /// Public theorem identities in the selected closure.
    pub theorems: Vec<PromotionDeclarationTargetTheorem>,
}

/// Hash-bound verified declaration materialization evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionDeclarationEvidence {
    /// Exactly `verified_declaration_materialization_v1`.
    pub kind: String,
    /// Exact plan schema.
    pub plan_schema: String,
    /// Source-root-relative plan path.
    pub plan_path: PackagePath,
    /// Exact plan file hash.
    pub plan_file_hash: PackageHash,
    /// Exact attestation schema.
    pub attestation_schema: String,
    /// Source-root-relative attestation path.
    pub attestation_path: PackagePath,
    /// Exact attestation file hash.
    pub attestation_file_hash: PackageHash,
    /// Selected declaration closure hash.
    pub declaration_closure_hash: PackageHash,
    /// Equal normalized source/target closure hash.
    pub normalized_closure_hash: PackageHash,
    /// Exact catalog policy file hash.
    pub catalog_policy_file_hash: PackageHash,
    /// Exact namespace policy file hash.
    pub namespace_policy_file_hash: PackageHash,
}

/// Append-only exact-target maturity event.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionMaturityEvent {
    /// Versioned maturity event kind.
    pub kind: String,
    /// Target version reviewed by the event.
    pub target_version: PackageVersion,
    /// Exact event evidence file hash.
    pub evidence_file_hash: PackageHash,
}

/// New declaration-closure registry route.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationClosureRegistryEntry {
    /// Stable route ID.
    pub promotion_id: PackageHash,
    /// Exactly `active` in the first implementation.
    pub lifecycle: String,
    /// First target release version.
    pub introduced_version: PackageVersion,
    /// Canonical selected source identity.
    pub canonical_source: PromotionPlanV2EquivalentSource,
    /// Exact artifact-identical source aliases.
    pub equivalent_sources: Vec<PromotionPlanV2EquivalentSource>,
    /// Original source module.
    pub source_module: Name,
    /// New public target module.
    pub target_module: Name,
    /// Requested roots.
    pub roots: Vec<PromotionPlanV2Root>,
    /// Complete materialized declaration closure.
    pub closure: Vec<PromotionPlanV2Declaration>,
    /// Exact used dependency mappings.
    pub dependency_mappings: Vec<PromotionPlanV2DependencyMapping>,
    /// Immutable target revisions.
    pub target_revisions: Vec<PromotionDeclarationTargetRevision>,
    /// Verified admission evidence.
    pub evidence: PromotionDeclarationEvidence,
    /// Append-only later maturity evidence.
    pub maturity_events: Vec<PromotionMaturityEvent>,
}

/// One sourced registry v2 entry variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PromotionOriginEntryV2 {
    /// Lossless historical v1 wrapper.
    WholeModuleV1(Box<PromotionOriginEntry>),
    /// Declaration-level verified materialization route.
    DeclarationClosureV1(Box<DeclarationClosureRegistryEntry>),
}

impl PromotionOriginEntryV2 {
    /// Stable route ID for sorting and lookup.
    pub fn promotion_id(&self) -> PackageHash {
        match self {
            Self::WholeModuleV1(entry) => entry.promotion_id,
            Self::DeclarationClosureV1(entry) => entry.promotion_id,
        }
    }

    /// Stable entry kind discriminator.
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::WholeModuleV1(_) => "whole_module_v1",
            Self::DeclarationClosureV1(_) => "declaration_closure_v1",
        }
    }
}

/// Canonical declaration-aware promotion-origin registry v2.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionOriginRegistryV2 {
    /// Exact schema.
    pub schema: String,
    /// Stable registry ID.
    pub registry_id: String,
    /// Exactly 2.
    pub registry_version: u64,
    /// Monotonic content generation.
    pub generation: u64,
    /// Exactly `npa-mathlib`.
    pub target_package: PackageId,
    /// Sourced route entries.
    pub entries: Vec<PromotionOriginEntryV2>,
    /// Unchanged top-level legacy reservations.
    pub unresolved_legacy_targets: Vec<PromotionLegacyTargetReservation>,
    /// Domain-separated self-hash.
    pub registry_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl PromotionOriginRegistryV2 {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_promotion_origin_registry_v2(self)?;
        Ok(format!("{}\n", registry_json(self)))
    }

    /// Recompute and store the v2 registry self-hash.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.registry_hash = promotion_origin_registry_v2_hash(self)?;
        Ok(())
    }
}

/// Look up a complete-module promotion candidate against registry v2.
pub fn lookup_promotion_origin_v2(
    registry: &PromotionOriginRegistryV2,
    source: &PromotionSourceOrigin,
    target_modules: &[Name],
    target_artifacts: &[(PackageHash, PackageHash)],
) -> PromotionOriginLookup {
    for entry in &registry.entries {
        match entry {
            PromotionOriginEntryV2::WholeModuleV1(entry) => {
                for origin in
                    std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources)
                {
                    if origin == source {
                        return PromotionOriginLookup::ExactOriginAlreadyPromoted;
                    }
                    if origin.modules.len() == source.modules.len()
                        && origin
                            .modules
                            .iter()
                            .zip(&source.modules)
                            .all(|(left, right)| source_module_artifacts_match(left, right))
                    {
                        return PromotionOriginLookup::ArtifactAliasAlreadyPromoted;
                    }
                }
            }
            PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
                for origin in
                    std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources)
                {
                    let Some(module) = source
                        .modules
                        .iter()
                        .find(|module| module.module == origin.source_module)
                    else {
                        continue;
                    };
                    if origin.package == source.package
                        && origin.version == source.version
                        && declaration_source_artifacts_match(origin, module)
                    {
                        return PromotionOriginLookup::ExactOriginAlreadyPromoted;
                    }
                    if declaration_source_artifacts_match(origin, module) {
                        return PromotionOriginLookup::ArtifactAliasAlreadyPromoted;
                    }
                }
            }
        }
    }
    let target_module_collision = registry.entries.iter().any(|entry| match entry {
        PromotionOriginEntryV2::WholeModuleV1(entry) => entry
            .module_routes
            .iter()
            .any(|route| target_modules.contains(&route.target_module)),
        PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
            target_modules.contains(&entry.target_module)
        }
    }) || registry
        .unresolved_legacy_targets
        .iter()
        .any(|entry| target_modules.contains(&entry.target_module));
    if target_module_collision {
        return PromotionOriginLookup::TargetModuleCollision;
    }
    let target_artifact_collision = registry.entries.iter().any(|entry| match entry {
        PromotionOriginEntryV2::WholeModuleV1(entry) => entry.module_routes.iter().any(|route| {
            route.target_revisions.iter().any(|revision| {
                target_artifacts.contains(&(
                    revision.target_certificate_hash,
                    revision.target_export_hash,
                ))
            })
        }),
        PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
            entry.target_revisions.iter().any(|revision| {
                target_artifacts.contains(&(
                    revision.target_certificate_hash,
                    revision.target_export_hash,
                ))
            })
        }
    }) || registry.unresolved_legacy_targets.iter().any(|entry| {
        entry.target_revisions.iter().any(|revision| {
            target_artifacts.contains(&(
                revision.target_certificate_hash,
                revision.target_export_hash,
            ))
        })
    });
    if target_artifact_collision {
        return PromotionOriginLookup::TargetArtifactCollision;
    }
    PromotionOriginLookup::NoRegistryMatch
}

fn source_module_artifacts_match(
    left: &PromotionSourceModule,
    right: &PromotionSourceModule,
) -> bool {
    left.source_file_hash == right.source_file_hash
        && left.certificate_file_hash == right.certificate_file_hash
        && left.certificate_hash == right.certificate_hash
        && left.export_hash == right.export_hash
}

fn declaration_source_artifacts_match(
    left: &PromotionPlanV2EquivalentSource,
    right: &PromotionSourceModule,
) -> bool {
    left.source_file_hash == right.source_file_hash
        && left.certificate_file_hash == right.certificate_file_hash
        && left.certificate_hash == right.certificate_hash
        && left.export_hash == right.export_hash
}

/// Losslessly wrap a valid v1 registry without changing its generation.
pub fn migrate_promotion_origin_registry_v1_to_v2(
    registry: &PromotionOriginRegistry,
) -> PackageArtifactResult<PromotionOriginRegistryV2> {
    validate_promotion_origin_registry(registry)?;
    let mut migrated = PromotionOriginRegistryV2 {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
        registry_id: registry.registry_id.clone(),
        registry_version: 2,
        generation: registry.generation,
        target_package: registry.target_package.clone(),
        entries: registry
            .entries
            .iter()
            .cloned()
            .map(|entry| PromotionOriginEntryV2::WholeModuleV1(Box::new(entry)))
            .collect(),
        unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
        registry_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    migrated.refresh_hash()?;
    Ok(migrated)
}

/// Parse and validate strict canonical registry v2 JSON.
pub fn parse_promotion_origin_registry_v2_json(
    source: &str,
) -> PackageArtifactResult<PromotionOriginRegistryV2> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, REGISTRY_FIELDS)?;
    let registry = PromotionOriginRegistryV2 {
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
            .map(|(index, value)| parse_v1_reservation(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        registry_hash: required_hash(members, "$", "registry_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_promotion_origin_registry_v2(&registry)?;
    if source != registry.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "registry v2 JSON bytes",
        ));
    }
    Ok(registry)
}

/// Compute registry v2 self-hash with its hash field zeroed.
pub fn promotion_origin_registry_v2_hash(
    registry: &PromotionOriginRegistryV2,
) -> PackageArtifactResult<PackageHash> {
    validate_registry_shape(registry, false)?;
    let mut copy = registry.clone();
    copy.registry_hash = PackageHash::new([0; 32]);
    Ok(domain_hash(
        REGISTRY_DOMAIN,
        registry_json(&copy).as_bytes(),
    ))
}

/// Validate registry v2 identity, wrappers, routes, collisions, and self-hash.
pub fn validate_promotion_origin_registry_v2(
    registry: &PromotionOriginRegistryV2,
) -> PackageArtifactResult<()> {
    validate_registry_shape(registry, true)
}

/// Validate that one declaration registry entry is exactly bound to its admission evidence.
pub fn validate_declaration_registry_entry_admission(
    entry: &DeclarationClosureRegistryEntry,
    plan: &MathlibPromotionPlanV2,
    attestation: &VerifiedMaterializationAttestation,
) -> PackageArtifactResult<()> {
    validate_mathlib_promotion_plan_v2(plan)?;
    validate_verified_materialization_attestation(attestation)?;
    validate_declaration_entry(entry, 0, &plan.target_baseline.package)?;
    let plan_file_hash = package_file_hash(plan.canonical_json()?.as_bytes());
    let attestation_file_hash = package_file_hash(attestation.canonical_json()?.as_bytes());
    let edge_hash = promotion_plan_v2_dependency_edge_hash(
        &plan.selection.materialized_declarations,
        &plan.dependency_mappings,
    )?;
    let canonical_source = PromotionPlanV2EquivalentSource {
        package: plan.source.package.clone(),
        version: plan.source.version.clone(),
        source_module: plan.selection.source_module.clone(),
        source_file_hash: plan.selection.source_file_hash,
        certificate_file_hash: plan.selection.certificate_file_hash,
        certificate_hash: plan.selection.certificate_hash,
        export_hash: plan.selection.export_hash,
        declaration_closure_hash: plan.selection.declaration_closure_hash,
        dependency_edge_hash: edge_hash,
    };
    let first_revision = entry.target_revisions.first().ok_or_else(admission_error)?;
    let source_checker = attestation
        .checker_verdicts
        .iter()
        .find(|verdict| verdict.side == "source")
        .ok_or_else(admission_error)?;
    let target_checker = attestation
        .checker_verdicts
        .iter()
        .find(|verdict| verdict.side == "target")
        .ok_or_else(admission_error)?;
    let target_base = plan.selection.target_module.as_dotted().replace('.', "/");
    let target_source_path = PackagePath::new(format!("{target_base}/source.npa"));
    let target_meta_path = PackagePath::new(format!("{target_base}/meta.json"));
    let target_replay_path = PackagePath::new(format!("{target_base}/replay.json"));
    let target_certificate_path = PackagePath::new(format!("{target_base}/certificate.npcert"));
    if entry.promotion_id != plan.promotion_id
        || entry.introduced_version != plan.target_baseline.planned_version
        || entry.canonical_source != canonical_source
        || entry.equivalent_sources != plan.equivalent_sources
        || entry.source_module != plan.selection.source_module
        || entry.target_module != plan.selection.target_module
        || entry.roots != plan.selection.roots
        || entry.closure != plan.selection.materialized_declarations
        || entry.dependency_mappings != plan.dependency_mappings
        || entry.evidence.plan_schema != plan.schema
        || entry.evidence.plan_path != attestation.plan.path
        || entry.evidence.plan_file_hash != plan_file_hash
        || attestation.plan.file_hash != plan_file_hash
        || entry.evidence.attestation_schema != attestation.schema
        || entry.evidence.attestation_file_hash != attestation_file_hash
        || entry.evidence.declaration_closure_hash != plan.selection.declaration_closure_hash
        || entry.evidence.normalized_closure_hash != attestation.normalized_closure_hash
        || entry.evidence.catalog_policy_file_hash != plan.governance.catalog_policy_file_hash
        || entry.evidence.namespace_policy_file_hash != plan.governance.namespace_policy_file_hash
        || attestation.promotion_id != plan.promotion_id
        || attestation.request.path != plan.governance.request_path
        || attestation.request.schema != plan.governance.request_schema
        || attestation.request.file_hash != plan.governance.request_file_hash
        || attestation.request.identity_hash != plan.governance.request_file_hash
        || attestation.plan.schema != plan.schema
        || attestation.plan.identity_hash != plan.plan_hash
        || attestation.source != plan.source
        || attestation.target_baseline != plan.target_baseline
        || attestation.target.source_path != target_source_path
        || attestation.target.meta_path != target_meta_path
        || attestation.target.replay_path != target_replay_path
        || attestation.target.certificate_path != target_certificate_path
        || attestation.source_declaration_closure_hash != plan.selection.declaration_closure_hash
        || attestation.materialized_declarations != plan.selection.materialized_declarations
        || attestation.generated_exports != plan.selection.generated_exports
        || attestation.externalized_dependencies != plan.dependency_mappings
        || attestation
            .replay_omissions
            .iter()
            .any(|row| row.source_replay_file_hash != plan.selection.replay_file_hash)
        || source_checker.certificate_hash != plan.selection.certificate_hash
        || source_checker.export_hash != plan.selection.export_hash
        || target_checker.certificate_hash != attestation.target.certificate_hash
        || target_checker.export_hash != attestation.target.export_hash
        || attestation.target.package != plan.target_baseline.package
        || first_revision.target_version != attestation.target.version
        || first_revision.target_source_file_hash != attestation.target.source_file_hash
        || first_revision.target_meta_file_hash != attestation.target.meta_file_hash
        || first_revision.target_replay_file_hash != attestation.target.replay_file_hash
        || first_revision.target_certificate_file_hash != attestation.target.certificate_file_hash
        || first_revision.target_certificate_hash != attestation.target.certificate_hash
        || first_revision.target_export_hash != attestation.target.export_hash
        || first_revision.target_axiom_report_hash != attestation.target.axiom_report_hash
    {
        return Err(admission_error());
    }
    Ok(())
}

/// Validate an append-only transition between two v2 registries.
pub fn validate_promotion_origin_registry_v2_transition(
    previous: &PromotionOriginRegistryV2,
    next: &PromotionOriginRegistryV2,
) -> PackageArtifactResult<()> {
    validate_promotion_origin_registry_v2(previous)?;
    validate_promotion_origin_registry_v2(next)?;
    let expected_generation = previous
        .generation
        .checked_add(1)
        .ok_or_else(transition_error)?;
    if previous.registry_id != next.registry_id
        || previous.target_package != next.target_package
        || next.generation != expected_generation
        || previous.unresolved_legacy_targets != next.unresolved_legacy_targets
    {
        return Err(transition_error());
    }
    let next_by_id = next
        .entries
        .iter()
        .map(|entry| (entry.promotion_id(), entry))
        .collect::<BTreeMap<_, _>>();
    let mut equivalent_additions = 0_usize;
    for old in &previous.entries {
        let Some(new) = next_by_id.get(&old.promotion_id()) else {
            return Err(transition_error());
        };
        match (old, *new) {
            (
                PromotionOriginEntryV2::WholeModuleV1(old),
                PromotionOriginEntryV2::WholeModuleV1(new),
            ) => {
                if old.promotion_id != new.promotion_id
                    || old.lifecycle != new.lifecycle
                    || old.introduced_version != new.introduced_version
                    || old.canonical_source != new.canonical_source
                    || old.module_routes != new.module_routes
                    || old.evidence != new.evidence
                    || old
                        .equivalent_sources
                        .iter()
                        .any(|origin| !new.equivalent_sources.contains(origin))
                    || new.equivalent_sources.len() < old.equivalent_sources.len()
                    || new.equivalent_sources.len() > old.equivalent_sources.len() + 1
                {
                    return Err(transition_error());
                }
                equivalent_additions += new.equivalent_sources.len() - old.equivalent_sources.len();
            }
            (
                PromotionOriginEntryV2::DeclarationClosureV1(old),
                PromotionOriginEntryV2::DeclarationClosureV1(new),
            ) => {
                if old.promotion_id != new.promotion_id
                    || old.lifecycle != new.lifecycle
                    || old.introduced_version != new.introduced_version
                    || old.canonical_source != new.canonical_source
                    || old.source_module != new.source_module
                    || old.target_module != new.target_module
                    || old.roots != new.roots
                    || old.closure != new.closure
                    || old.dependency_mappings != new.dependency_mappings
                    || old.target_revisions != new.target_revisions
                    || old.evidence != new.evidence
                    || old
                        .equivalent_sources
                        .iter()
                        .any(|origin| !new.equivalent_sources.contains(origin))
                    || new.equivalent_sources.len() < old.equivalent_sources.len()
                    || new.equivalent_sources.len() > old.equivalent_sources.len() + 1
                    || new.maturity_events != old.maturity_events
                {
                    return Err(transition_error());
                }
                equivalent_additions += new.equivalent_sources.len() - old.equivalent_sources.len();
            }
            _ => return Err(transition_error()),
        }
    }
    let new_entries = next
        .entries
        .len()
        .checked_sub(previous.entries.len())
        .ok_or_else(transition_error)?;
    if !matches!((new_entries, equivalent_additions), (1, 0) | (0, 1)) {
        return Err(transition_error());
    }
    Ok(())
}

/// Validate a v1-to-v2 generation transition and lossless wrapper projection.
pub fn validate_promotion_origin_registry_v1_to_v2_transition(
    previous: &PromotionOriginRegistry,
    next: &PromotionOriginRegistryV2,
) -> PackageArtifactResult<()> {
    let migrated = migrate_promotion_origin_registry_v1_to_v2(previous)?;
    validate_promotion_origin_registry_v2_transition(&migrated, next).map_err(|_| {
        PackageArtifactError::invalid_enum_value(
            "$",
            "registry_upgrade",
            "lossless v1 projection and one append-only route or equivalent-origin addition",
            "mismatch",
        )
    })
}

fn validate_registry_shape(
    registry: &PromotionOriginRegistryV2,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    if registry.schema != MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA
        || registry.registry_id != MATHLIB_PROMOTION_REGISTRY_ID
        || registry.registry_version != 2
        || registry.generation == 0
        || registry.target_package.as_str() != "npa-mathlib"
        || registry.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "registry",
            "strict npa-mathlib registry v2",
            "mismatch",
        ));
    }
    let mut previous_id = None;
    let mut target_modules = BTreeSet::new();
    let mut target_artifacts = BTreeMap::new();
    let mut whole_source_modules = BTreeSet::new();
    let mut v1_projection = PromotionOriginRegistry {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
        registry_id: registry.registry_id.clone(),
        registry_version: 1,
        generation: registry.generation,
        target_package: registry.target_package.clone(),
        entries: registry
            .entries
            .iter()
            .filter_map(|entry| match entry {
                PromotionOriginEntryV2::WholeModuleV1(entry) => Some((**entry).clone()),
                PromotionOriginEntryV2::DeclarationClosureV1(_) => None,
            })
            .collect(),
        unresolved_legacy_targets: registry.unresolved_legacy_targets.clone(),
        registry_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    v1_projection.refresh_hash()?;
    for entry in &v1_projection.entries {
        for origin in std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources) {
            whole_source_modules.extend(origin.modules.iter().cloned());
        }
        for route in &entry.module_routes {
            for revision in &route.target_revisions {
                target_artifacts.insert(
                    (
                        revision.target_certificate_hash,
                        revision.target_export_hash,
                    ),
                    route.target_module.clone(),
                );
            }
        }
    }
    for reservation in &v1_projection.unresolved_legacy_targets {
        for revision in &reservation.target_revisions {
            target_artifacts.insert(
                (
                    revision.target_certificate_hash,
                    revision.target_export_hash,
                ),
                reservation.target_module.clone(),
            );
        }
    }
    let mut declaration_sources = BTreeSet::new();
    for (index, entry) in registry.entries.iter().enumerate() {
        let id = entry.promotion_id();
        if previous_id.is_some_and(|previous| previous >= id) {
            return Err(PackageArtifactError::non_canonical(
                "entries",
                "strict promotion_id order",
            ));
        }
        previous_id = Some(id);
        match entry {
            PromotionOriginEntryV2::WholeModuleV1(entry) => {
                validate_v1_entry(entry, index)?;
                for route in &entry.module_routes {
                    if !target_modules.insert(route.target_module.clone()) {
                        return Err(collision_error("target module"));
                    }
                }
            }
            PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
                validate_declaration_entry(entry, index, &registry.target_package)?;
                let source_module = PromotionSourceModule {
                    module: entry.source_module.clone(),
                    source_file_hash: entry.canonical_source.source_file_hash,
                    certificate_file_hash: entry.canonical_source.certificate_file_hash,
                    certificate_hash: entry.canonical_source.certificate_hash,
                    export_hash: entry.canonical_source.export_hash,
                };
                if whole_source_modules.contains(&source_module)
                    || !target_modules.insert(entry.target_module.clone())
                {
                    return Err(collision_error("source or target module"));
                }
                for declaration in &entry.closure {
                    let key = (
                        entry.source_module.clone(),
                        declaration.source_name.clone(),
                        declaration.certificate_kind.clone(),
                        declaration.decl_interface_hash,
                    );
                    if !declaration_sources.insert(key) {
                        return Err(collision_error("source declaration"));
                    }
                }
                for revision in &entry.target_revisions {
                    if target_artifacts
                        .insert(
                            (
                                revision.target_certificate_hash,
                                revision.target_export_hash,
                            ),
                            entry.target_module.clone(),
                        )
                        .is_some()
                    {
                        return Err(collision_error("target artifact"));
                    }
                }
            }
        }
    }
    for (index, reservation) in registry.unresolved_legacy_targets.iter().enumerate() {
        validate_v1_reservation(reservation, index)?;
        if !target_modules.insert(reservation.target_module.clone()) {
            return Err(collision_error("legacy target module"));
        }
    }
    if check_hash && registry.registry_hash != promotion_origin_registry_v2_hash(registry)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "registry_hash",
            "registry_hash",
            "recomputed registry v2 hash",
            crate::format_package_hash(&registry.registry_hash),
        ));
    }
    Ok(())
}

fn validate_declaration_entry(
    entry: &DeclarationClosureRegistryEntry,
    index: usize,
    target_package: &PackageId,
) -> PackageArtifactResult<()> {
    let path = format!("entries[{index}].declaration_closure_v1");
    validate_declaration_promotion_resource_count(
        &path,
        "target_revisions",
        entry.target_revisions.len(),
        MAX_TARGET_REVISIONS,
    )?;
    validate_declaration_promotion_resource_count(
        &path,
        "maturity_events",
        entry.maturity_events.len(),
        MAX_MATURITY_EVENTS,
    )?;
    if entry.lifecycle != "active"
        || entry.closure.is_empty()
        || entry.roots.is_empty()
        || entry.target_revisions.len() != 1
        || entry.evidence.kind != "verified_declaration_materialization_v1"
        || entry.evidence.plan_schema != MATHLIB_PROMOTION_PLAN_V2_SCHEMA
        || entry.evidence.attestation_schema != MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA
        || entry.canonical_source.source_module != entry.source_module
        || entry.canonical_source.declaration_closure_hash
            != entry.evidence.declaration_closure_hash
        || !entry.maturity_events.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "entry",
            "complete active verified declaration route",
            "mismatch",
        ));
    }
    validate_declaration_promotion_resource_limits(
        Some(&entry.source_module),
        Some(&entry.target_module),
        Some(&entry.roots),
        &entry.closure,
        None,
        &entry.dependency_mappings,
        &path,
    )?;
    validate_declaration_promotion_resource_count(
        &path,
        "equivalent_sources",
        entry.equivalent_sources.len(),
        DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES,
    )?;
    for revision in &entry.target_revisions {
        validate_declaration_promotion_resource_count(
            &path,
            "target_revisions.theorems",
            revision.theorems.len(),
            MAX_TARGET_THEOREMS,
        )?;
    }
    validate_package_identity(target_package, &entry.introduced_version)?;
    validate_module_name(&entry.source_module, format!("{path}.source_module"))?;
    validate_module_name(&entry.target_module, format!("{path}.target_module"))?;
    if !entry.target_module.as_dotted().starts_with("Mathlib.") {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "target_module",
            "Mathlib.* module",
            entry.target_module.as_dotted(),
        ));
    }
    validate_package_identity(
        &entry.canonical_source.package,
        &entry.canonical_source.version,
    )?;
    ensure_strict(
        &entry.equivalent_sources,
        &format!("{path}.equivalent_sources"),
    )?;
    ensure_strict(&entry.roots, &format!("{path}.roots"))?;
    ensure_strict(&entry.closure, &format!("{path}.closure"))?;
    ensure_strict(
        &entry.dependency_mappings,
        &format!("{path}.dependency_mappings"),
    )?;
    ensure_strict(&entry.target_revisions, &format!("{path}.target_revisions"))?;
    ensure_strict(&entry.maturity_events, &format!("{path}.maturity_events"))?;
    for root in &entry.roots {
        validate_promotion_plan_v2_root(root, &format!("{path}.roots"))?;
    }
    for declaration in &entry.closure {
        validate_promotion_plan_v2_declaration(declaration, &format!("{path}.closure"))?;
    }
    for mapping in &entry.dependency_mappings {
        validate_promotion_plan_v2_mapping(mapping, &format!("{path}.dependency_mappings"))?;
        if (mapping.source.origin == PackageArtifactOrigin::Local
            && (mapping.source.package != entry.canonical_source.package
                || mapping.source.version != entry.canonical_source.version))
            || (mapping.target.origin == PackageArtifactOrigin::Local
                && (mapping.target.package != *target_package
                    || !version_is_strictly_greater(
                        &entry.introduced_version,
                        &mapping.target.version,
                    )))
            || mapping.target.module == entry.target_module
        {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "dependency_mappings",
                "local canonical-source and earlier target identities distinct from the promoted module",
                "mismatch",
            ));
        }
    }
    for equivalent in &entry.equivalent_sources {
        validate_package_identity(&equivalent.package, &equivalent.version)?;
        if equivalent == &entry.canonical_source
            || equivalent.source_module != entry.canonical_source.source_module
            || equivalent.source_file_hash != entry.canonical_source.source_file_hash
            || equivalent.certificate_file_hash != entry.canonical_source.certificate_file_hash
            || equivalent.certificate_hash != entry.canonical_source.certificate_hash
            || equivalent.export_hash != entry.canonical_source.export_hash
            || equivalent.declaration_closure_hash
                != entry.canonical_source.declaration_closure_hash
            || equivalent.dependency_edge_hash != entry.canonical_source.dependency_edge_hash
        {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "equivalent_sources",
                "a distinct origin with artifact-identical module, certificate, export, selected closure, and edges",
                "mismatch",
            ));
        }
    }
    validate_promotion_plan_v2_closure_relationships(
        &entry.source_module,
        &entry.roots,
        &entry.closure,
        &path,
    )?;
    for revision in &entry.target_revisions {
        validate_package_identity(target_package, &revision.target_version)?;
        ensure_strict(
            &revision.theorems,
            &format!("{path}.target_revisions.theorems"),
        )?;
        for theorem in &revision.theorems {
            validate_declaration_name(
                &theorem.target_name,
                "target_revisions.theorems.target_name",
            )?;
        }
    }
    let first_revision = entry.target_revisions.first().expect("nonempty revisions");
    let route_id = mathlib_declaration_promotion_route_id_v2(
        &entry.canonical_source.package,
        &entry.canonical_source.version,
        &entry.source_module,
        &entry.target_module,
        &entry.roots,
        entry.canonical_source.declaration_closure_hash,
    )?;
    let edge_hash =
        promotion_plan_v2_dependency_edge_hash(&entry.closure, &entry.dependency_mappings)?;
    if entry.promotion_id != route_id
        || entry.introduced_version != first_revision.target_version
        || entry.canonical_source.dependency_edge_hash != edge_hash
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "route_identity",
            "route ID, introduced revision, and dependency-edge identity derived from entry fields",
            "mismatch",
        ));
    }
    for evidence_path in [&entry.evidence.plan_path, &entry.evidence.attestation_path] {
        validate_package_path(evidence_path, "evidence.path").map_err(|_| {
            PackageArtifactError::invalid_path("evidence.path", evidence_path.as_str())
        })?;
    }
    Ok(())
}

fn ensure_strict<T: Ord>(values: &[T], path: &str) -> PackageArtifactResult<()> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        Err(PackageArtifactError::non_canonical(path, "strict order"))
    } else {
        Ok(())
    }
}

fn version_is_strictly_greater(left: &PackageVersion, right: &PackageVersion) -> bool {
    fn parts(version: &PackageVersion) -> Option<(u64, u64, u64)> {
        let values = version
            .as_str()
            .split('.')
            .map(str::parse::<u64>)
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        (values.len() == 3).then(|| (values[0], values[1], values[2]))
    }
    matches!((parts(left), parts(right)), (Some(left), Some(right)) if left > right)
}

fn parse_entry(value: &JsonValue, index: usize) -> PackageArtifactResult<PromotionOriginEntryV2> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    let kind = required_string(members, &path, "kind")?;
    match kind.as_str() {
        "whole_module_v1" => {
            reject_unknown_fields(&path, members, WRAPPER_FIELDS)?;
            Ok(PromotionOriginEntryV2::WholeModuleV1(Box::new(
                parse_v1_entry(required_value(members, &path, "v1_entry")?, index)?,
            )))
        }
        "declaration_closure_v1" => {
            reject_unknown_fields(&path, members, DECLARATION_FIELDS)?;
            Ok(PromotionOriginEntryV2::DeclarationClosureV1(Box::new(
                parse_declaration_entry(members, &path)?,
            )))
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            &path,
            "kind",
            "whole_module_v1 or declaration_closure_v1",
            kind,
        )),
    }
}

fn parse_declaration_entry(
    members: &[crate::json::JsonMember],
    path: &str,
) -> PackageArtifactResult<DeclarationClosureRegistryEntry> {
    Ok(DeclarationClosureRegistryEntry {
        promotion_id: required_hash(members, path, "promotion_id")?,
        lifecycle: required_string(members, path, "lifecycle")?,
        introduced_version: PackageVersion::new(required_string(
            members,
            path,
            "introduced_version",
        )?),
        canonical_source: parse_equivalent(
            required_value(members, path, "canonical_source")?,
            &format!("{path}.canonical_source"),
        )?,
        equivalent_sources: parse_array_bounded(
            members,
            path,
            "equivalent_sources",
            DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES,
            parse_equivalent,
        )?,
        source_module: required_name(members, path, "source_module")?,
        target_module: required_name(members, path, "target_module")?,
        roots: parse_array_bounded(
            members,
            path,
            "roots",
            DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS,
            parse_root,
        )?,
        closure: parse_array_bounded(
            members,
            path,
            "closure",
            DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
            parse_declaration,
        )?,
        dependency_mappings: parse_array_bounded(
            members,
            path,
            "dependency_mappings",
            DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
            parse_mapping,
        )?,
        target_revisions: parse_array_bounded(
            members,
            path,
            "target_revisions",
            MAX_TARGET_REVISIONS,
            parse_revision,
        )?,
        evidence: parse_evidence(
            required_value(members, path, "evidence")?,
            &format!("{path}.evidence"),
        )?,
        maturity_events: parse_array_bounded(
            members,
            path,
            "maturity_events",
            MAX_MATURITY_EVENTS,
            parse_maturity,
        )?,
    })
}

fn parse_array_bounded<T>(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
    maximum: usize,
    parser: fn(&JsonValue, &str) -> PackageArtifactResult<T>,
) -> PackageArtifactResult<Vec<T>> {
    let values = required_array(members, path, field)?;
    validate_declaration_promotion_resource_count(path, field, values.len(), maximum)?;
    values
        .iter()
        .enumerate()
        .map(|(index, value)| parser(value, &format!("{path}.{field}[{index}]")))
        .collect()
}

fn parse_revision(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionDeclarationTargetRevision> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REVISION_FIELDS)?;
    Ok(PromotionDeclarationTargetRevision {
        target_version: PackageVersion::new(required_string(members, path, "target_version")?),
        target_source_file_hash: required_hash(members, path, "target_source_file_hash")?,
        target_meta_file_hash: required_hash(members, path, "target_meta_file_hash")?,
        target_replay_file_hash: required_hash(members, path, "target_replay_file_hash")?,
        target_certificate_file_hash: required_hash(members, path, "target_certificate_file_hash")?,
        target_certificate_hash: required_hash(members, path, "target_certificate_hash")?,
        target_export_hash: required_hash(members, path, "target_export_hash")?,
        target_axiom_report_hash: required_hash(members, path, "target_axiom_report_hash")?,
        theorems: parse_array_bounded(
            members,
            path,
            "theorems",
            MAX_TARGET_THEOREMS,
            parse_theorem,
        )?,
    })
}

fn parse_theorem(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionDeclarationTargetTheorem> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, THEOREM_FIELDS)?;
    Ok(PromotionDeclarationTargetTheorem {
        target_name: required_name(members, path, "target_name")?,
        statement_hash: required_hash(members, path, "statement_hash")?,
    })
}

fn parse_evidence(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionDeclarationEvidence> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, EVIDENCE_FIELDS)?;
    Ok(PromotionDeclarationEvidence {
        kind: required_string(members, path, "kind")?,
        plan_schema: required_string(members, path, "plan_schema")?,
        plan_path: required_path(members, path, "plan_path")?,
        plan_file_hash: required_hash(members, path, "plan_file_hash")?,
        attestation_schema: required_string(members, path, "attestation_schema")?,
        attestation_path: required_path(members, path, "attestation_path")?,
        attestation_file_hash: required_hash(members, path, "attestation_file_hash")?,
        declaration_closure_hash: required_hash(members, path, "declaration_closure_hash")?,
        normalized_closure_hash: required_hash(members, path, "normalized_closure_hash")?,
        catalog_policy_file_hash: required_hash(members, path, "catalog_policy_file_hash")?,
        namespace_policy_file_hash: required_hash(members, path, "namespace_policy_file_hash")?,
    })
}

fn parse_maturity(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionMaturityEvent> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, MATURITY_FIELDS)?;
    Ok(PromotionMaturityEvent {
        kind: required_string(members, path, "kind")?,
        target_version: PackageVersion::new(required_string(members, path, "target_version")?),
        evidence_file_hash: required_hash(members, path, "evidence_file_hash")?,
    })
}

fn registry_json(registry: &PromotionOriginRegistryV2) -> String {
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
        ("registry_hash", hash_json(registry.registry_hash)),
        ("proof_evidence", json_bool(registry.proof_evidence)),
    ])
}

fn entry_json(entry: &PromotionOriginEntryV2) -> String {
    match entry {
        PromotionOriginEntryV2::WholeModuleV1(entry) => json_object_in_order(vec![
            ("kind", json_string("whole_module_v1")),
            ("v1_entry", v1_entry_json(entry)),
        ]),
        PromotionOriginEntryV2::DeclarationClosureV1(entry) => json_object_in_order(vec![
            ("kind", json_string("declaration_closure_v1")),
            ("promotion_id", hash_json(entry.promotion_id)),
            ("lifecycle", json_string(&entry.lifecycle)),
            (
                "introduced_version",
                json_string(entry.introduced_version.as_str()),
            ),
            ("canonical_source", equivalent_json(&entry.canonical_source)),
            (
                "equivalent_sources",
                json_array(
                    entry
                        .equivalent_sources
                        .iter()
                        .map(equivalent_json)
                        .collect(),
                ),
            ),
            (
                "source_module",
                json_string(&entry.source_module.as_dotted()),
            ),
            (
                "target_module",
                json_string(&entry.target_module.as_dotted()),
            ),
            (
                "roots",
                json_array(entry.roots.iter().map(root_json).collect()),
            ),
            (
                "closure",
                json_array(entry.closure.iter().map(declaration_json).collect()),
            ),
            (
                "dependency_mappings",
                json_array(entry.dependency_mappings.iter().map(mapping_json).collect()),
            ),
            (
                "target_revisions",
                json_array(entry.target_revisions.iter().map(revision_json).collect()),
            ),
            ("evidence", evidence_json(&entry.evidence)),
            (
                "maturity_events",
                json_array(entry.maturity_events.iter().map(maturity_json).collect()),
            ),
        ]),
    }
}

fn revision_json(value: &PromotionDeclarationTargetRevision) -> String {
    json_object_in_order(vec![
        ("target_version", json_string(value.target_version.as_str())),
        (
            "target_source_file_hash",
            hash_json(value.target_source_file_hash),
        ),
        (
            "target_meta_file_hash",
            hash_json(value.target_meta_file_hash),
        ),
        (
            "target_replay_file_hash",
            hash_json(value.target_replay_file_hash),
        ),
        (
            "target_certificate_file_hash",
            hash_json(value.target_certificate_file_hash),
        ),
        (
            "target_certificate_hash",
            hash_json(value.target_certificate_hash),
        ),
        ("target_export_hash", hash_json(value.target_export_hash)),
        (
            "target_axiom_report_hash",
            hash_json(value.target_axiom_report_hash),
        ),
        (
            "theorems",
            json_array(value.theorems.iter().map(theorem_json).collect()),
        ),
    ])
}
fn theorem_json(value: &PromotionDeclarationTargetTheorem) -> String {
    json_object_in_order(vec![
        ("target_name", json_string(&value.target_name.as_dotted())),
        ("statement_hash", hash_json(value.statement_hash)),
    ])
}
fn evidence_json(value: &PromotionDeclarationEvidence) -> String {
    json_object_in_order(vec![
        ("kind", json_string(&value.kind)),
        ("plan_schema", json_string(&value.plan_schema)),
        ("plan_path", json_string(value.plan_path.as_str())),
        ("plan_file_hash", hash_json(value.plan_file_hash)),
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
            "declaration_closure_hash",
            hash_json(value.declaration_closure_hash),
        ),
        (
            "normalized_closure_hash",
            hash_json(value.normalized_closure_hash),
        ),
        (
            "catalog_policy_file_hash",
            hash_json(value.catalog_policy_file_hash),
        ),
        (
            "namespace_policy_file_hash",
            hash_json(value.namespace_policy_file_hash),
        ),
    ])
}
fn maturity_json(value: &PromotionMaturityEvent) -> String {
    json_object_in_order(vec![
        ("kind", json_string(&value.kind)),
        ("target_version", json_string(value.target_version.as_str())),
        ("evidence_file_hash", hash_json(value.evidence_file_hash)),
    ])
}

fn domain_hash(domain: &[u8], bytes: &[u8]) -> PackageHash {
    let mut input = Vec::with_capacity(domain.len() + bytes.len());
    input.extend_from_slice(domain);
    input.extend_from_slice(bytes);
    package_file_hash(&input)
}
fn collision_error(actual: &str) -> PackageArtifactError {
    PackageArtifactError::non_canonical(
        "entries",
        format!("promotion registry collision: {actual}"),
    )
}
fn transition_error() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "registry_transition",
        "append-only v2 transition",
        "mutation",
    )
}

fn admission_error() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "declaration_registry_admission",
        "registry entry exactly bound to plan and verified materialization attestation",
        "mismatch",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        promotion_plan_v2::PromotionSourceSpan,
        promotion_registry::{
            PromotionAuditLocation, PromotionEvidence, PromotionLifecycle, PromotionModuleRoute,
            PromotionRouteTheorem, PromotionSourceModule, PromotionSourceOrigin,
            PromotionTargetRevision,
        },
        schema::MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA,
    };

    fn hash(byte: u8) -> PackageHash {
        PackageHash::from([byte; 32])
    }

    fn declaration_entry(seed: u8) -> PromotionOriginEntryV2 {
        let source_module = Name::from_dotted(format!("Proofs.Route{seed}"));
        let target_module = Name::from_dotted(format!("Mathlib.Route{seed}"));
        let declaration = Name::from_dotted(format!("route_{seed}"));
        let closure_hash = hash(seed.wrapping_add(1));
        let mut entry = DeclarationClosureRegistryEntry {
            promotion_id: PackageHash::new([0; 32]),
            lifecycle: "active".to_owned(),
            introduced_version: PackageVersion::new("0.2.0"),
            canonical_source: PromotionPlanV2EquivalentSource {
                package: PackageId::new(format!("source-{seed}")),
                version: PackageVersion::new("0.1.0"),
                source_module: source_module.clone(),
                source_file_hash: hash(seed.wrapping_add(2)),
                certificate_file_hash: hash(seed.wrapping_add(3)),
                certificate_hash: hash(seed.wrapping_add(4)),
                export_hash: hash(seed.wrapping_add(5)),
                declaration_closure_hash: closure_hash,
                dependency_edge_hash: PackageHash::new([0; 32]),
            },
            equivalent_sources: Vec::new(),
            source_module,
            target_module,
            roots: vec![PromotionPlanV2Root {
                requested_name: declaration.clone(),
                owner_name: declaration.clone(),
                kind: "theorem".to_owned(),
            }],
            closure: vec![PromotionPlanV2Declaration {
                role: "root".to_owned(),
                source_name: declaration.clone(),
                target_name: declaration.clone(),
                certificate_kind: "theorem".to_owned(),
                human_kind: "theorem".to_owned(),
                source_decl_index: 0,
                decl_interface_hash: hash(seed.wrapping_add(7)),
                decl_certificate_hash: hash(seed.wrapping_add(8)),
                type_hash: hash(seed.wrapping_add(9)),
                body_hash: None,
                item_span: PromotionSourceSpan { start: 1, end: 2 },
                family_owner: declaration.clone(),
                family_members: vec![declaration.clone()],
                generated_exports: Vec::new(),
                direct_dependencies: Vec::new(),
            }],
            dependency_mappings: Vec::new(),
            target_revisions: vec![PromotionDeclarationTargetRevision {
                target_version: PackageVersion::new("0.2.0"),
                target_source_file_hash: hash(seed.wrapping_add(10)),
                target_meta_file_hash: hash(seed.wrapping_add(11)),
                target_replay_file_hash: hash(seed.wrapping_add(12)),
                target_certificate_file_hash: hash(seed.wrapping_add(13)),
                target_certificate_hash: hash(seed.wrapping_add(14)),
                target_export_hash: hash(seed.wrapping_add(15)),
                target_axiom_report_hash: hash(seed.wrapping_add(16)),
                theorems: vec![PromotionDeclarationTargetTheorem {
                    target_name: declaration,
                    statement_hash: hash(seed.wrapping_add(17)),
                }],
            }],
            evidence: PromotionDeclarationEvidence {
                kind: "verified_declaration_materialization_v1".to_owned(),
                plan_schema: MATHLIB_PROMOTION_PLAN_V2_SCHEMA.to_owned(),
                plan_path: PackagePath::new(format!("promotion/route-{seed}.plan.json")),
                plan_file_hash: hash(seed.wrapping_add(18)),
                attestation_schema: MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA.to_owned(),
                attestation_path: PackagePath::new(format!(
                    "promotion/route-{seed}.attestation.json"
                )),
                attestation_file_hash: hash(seed.wrapping_add(19)),
                declaration_closure_hash: closure_hash,
                normalized_closure_hash: hash(seed.wrapping_add(20)),
                catalog_policy_file_hash: hash(seed.wrapping_add(21)),
                namespace_policy_file_hash: hash(seed.wrapping_add(22)),
            },
            maturity_events: Vec::new(),
        };
        entry.canonical_source.dependency_edge_hash =
            promotion_plan_v2_dependency_edge_hash(&entry.closure, &entry.dependency_mappings)
                .unwrap();
        entry.promotion_id = mathlib_declaration_promotion_route_id_v2(
            &entry.canonical_source.package,
            &entry.canonical_source.version,
            &entry.source_module,
            &entry.target_module,
            &entry.roots,
            entry.canonical_source.declaration_closure_hash,
        )
        .unwrap();
        PromotionOriginEntryV2::DeclarationClosureV1(Box::new(entry))
    }

    fn refresh_declaration_route_identity(entry: &mut PromotionOriginEntryV2) {
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = entry else {
            unreachable!()
        };
        entry.canonical_source.dependency_edge_hash =
            promotion_plan_v2_dependency_edge_hash(&entry.closure, &entry.dependency_mappings)
                .unwrap();
        entry.promotion_id = mathlib_declaration_promotion_route_id_v2(
            &entry.canonical_source.package,
            &entry.canonical_source.version,
            &entry.source_module,
            &entry.target_module,
            &entry.roots,
            entry.canonical_source.declaration_closure_hash,
        )
        .unwrap();
    }

    fn registry(
        generation: u64,
        mut entries: Vec<PromotionOriginEntryV2>,
    ) -> PromotionOriginRegistryV2 {
        entries.sort_by_key(PromotionOriginEntryV2::promotion_id);
        let mut registry = PromotionOriginRegistryV2 {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 2,
            generation,
            target_package: PackageId::new("npa-mathlib"),
            entries,
            unresolved_legacy_targets: Vec::new(),
            registry_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        registry.refresh_hash().unwrap();
        registry
    }

    fn whole_module_v1_registry() -> PromotionOriginRegistry {
        let source_module = Name::from_dotted("Proofs.LegacyRoute");
        let target_module = Name::from_dotted("Mathlib.LegacyRoute");
        let target_version = PackageVersion::new("0.2.0");
        let mut registry = PromotionOriginRegistry {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 1,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries: vec![PromotionOriginEntry {
                promotion_id: hash(1),
                lifecycle: PromotionLifecycle::Active,
                introduced_version: target_version.clone(),
                canonical_source: PromotionSourceOrigin {
                    package: PackageId::new("legacy-source"),
                    version: PackageVersion::new("0.1.0"),
                    modules: vec![PromotionSourceModule {
                        module: source_module.clone(),
                        source_file_hash: hash(2),
                        certificate_file_hash: hash(3),
                        certificate_hash: hash(4),
                        export_hash: hash(5),
                    }],
                },
                equivalent_sources: Vec::new(),
                module_routes: vec![PromotionModuleRoute {
                    source_module,
                    target_module,
                    declaration_mapping: "same-name-except-explicit".to_owned(),
                    renames: Vec::new(),
                    target_revisions: vec![PromotionTargetRevision::<PromotionRouteTheorem> {
                        target_version,
                        target_source_file_hash: hash(6),
                        target_certificate_file_hash: hash(7),
                        target_certificate_hash: hash(8),
                        target_export_hash: hash(9),
                        target_axiom_report_hash: hash(10),
                        theorems: Vec::new(),
                    }],
                }],
                evidence: PromotionEvidence::LegacyAudit {
                    audit_location: PromotionAuditLocation {
                        repository: "legacy-audit".to_owned(),
                        path: PackagePath::new("promotion/legacy-route.md"),
                    },
                    audit_file_hash: hash(11),
                },
            }],
            unresolved_legacy_targets: Vec::new(),
            registry_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        registry.refresh_hash().unwrap();
        registry
    }

    fn equivalent_source(
        entry: &PromotionOriginEntryV2,
        suffix: &str,
    ) -> PromotionPlanV2EquivalentSource {
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = entry else {
            unreachable!()
        };
        PromotionPlanV2EquivalentSource {
            package: PackageId::new(format!("source-alias-{suffix}")),
            ..entry.canonical_source.clone()
        }
    }

    #[test]
    fn empty_v1_migration_is_lossless_and_canonical_v2() {
        let mut v1 = PromotionOriginRegistry {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 1,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries: Vec::new(),
            unresolved_legacy_targets: Vec::new(),
            registry_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        v1.refresh_hash().unwrap();
        let v2 = migrate_promotion_origin_registry_v1_to_v2(&v1).unwrap();
        assert_eq!(v2.generation, v1.generation);
        assert!(v2.entries.is_empty());
        let json = v2.canonical_json().unwrap();
        assert_eq!(parse_promotion_origin_registry_v2_json(&json).unwrap(), v2);
    }

    #[test]
    fn declaration_registry_rejects_unimplemented_maturity_events() {
        let mut registry = registry(1, vec![declaration_entry(1)]);
        let canonical_json = registry.canonical_json().unwrap();
        let event = PromotionMaturityEvent {
            kind: "reviewed_target_l2_v1".to_owned(),
            target_version: PackageVersion::new("0.2.0"),
            evidence_file_hash: hash(90),
        };
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut registry.entries[0] else {
            unreachable!()
        };
        entry.maturity_events.push(event.clone());
        let error = validate_promotion_origin_registry_v2(&registry).unwrap_err();
        assert_eq!(error.field.as_deref(), Some("maturity_events"));

        let encoded_event = maturity_json(&event);
        let source = canonical_json.replace(
            "\"maturity_events\":[]",
            &format!("\"maturity_events\":[{encoded_event}]"),
        );
        let error = parse_promotion_origin_registry_v2_json(&source).unwrap_err();
        assert_eq!(error.field.as_deref(), Some("maturity_events"));
    }

    #[test]
    fn declaration_registry_bounds_auxiliary_arrays_before_typed_conversion() {
        let mut registry = registry(1, vec![declaration_entry(1)]);
        let alias = equivalent_source(&registry.entries[0], "one");
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut registry.entries[0] else {
            unreachable!()
        };
        entry.equivalent_sources.push(alias);
        registry.refresh_hash().unwrap();

        let value = parse_artifact_json(&registry.canonical_json().unwrap()).unwrap();
        let members = expect_object(&value, "$").unwrap();
        let entries = required_array(members, "$", "entries").unwrap();
        let entry_members = expect_object(&entries[0], "entries[0]").unwrap();
        let equivalent_error = parse_array_bounded(
            entry_members,
            "entries[0]",
            "equivalent_sources",
            0,
            parse_equivalent,
        )
        .unwrap_err();
        assert_eq!(
            equivalent_error.field.as_deref(),
            Some("equivalent_sources")
        );
        let revision_error = parse_array_bounded(
            entry_members,
            "entries[0]",
            "target_revisions",
            0,
            parse_revision,
        )
        .unwrap_err();
        assert_eq!(revision_error.field.as_deref(), Some("target_revisions"));

        let revisions = required_array(entry_members, "entries[0]", "target_revisions").unwrap();
        let revision_members =
            expect_object(&revisions[0], "entries[0].target_revisions[0]").unwrap();
        let theorem_error = parse_array_bounded(
            revision_members,
            "entries[0].target_revisions[0]",
            "theorems",
            0,
            parse_theorem,
        )
        .unwrap_err();
        assert_eq!(theorem_error.field.as_deref(), Some("theorems"));
    }

    #[test]
    fn declaration_registry_rejects_underived_route_identity() {
        let mut registry = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut registry.entries[0] else {
            unreachable!()
        };
        entry.promotion_id = hash(99);
        assert!(validate_promotion_origin_registry_v2(&registry).is_err());
    }

    #[test]
    fn declaration_registry_rejects_invalid_embedded_declaration_rows() {
        let mut invalid_declaration = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) =
            &mut invalid_declaration.entries[0]
        else {
            unreachable!()
        };
        entry.closure[0].certificate_kind = "axiom".to_owned();
        assert!(invalid_declaration.refresh_hash().is_err());

        let mut root_kind = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut root_kind.entries[0] else {
            unreachable!()
        };
        entry.roots[0].kind = "definition".to_owned();
        assert!(root_kind.refresh_hash().is_err());
    }

    #[test]
    fn declaration_registry_rejects_cross_route_target_artifact_collisions() {
        let first = declaration_entry(1);
        let mut second = declaration_entry(40);
        let PromotionOriginEntryV2::DeclarationClosureV1(first_entry) = &first else {
            unreachable!()
        };
        let PromotionOriginEntryV2::DeclarationClosureV1(second_entry) = &mut second else {
            unreachable!()
        };
        second_entry.target_revisions[0].target_certificate_hash =
            first_entry.target_revisions[0].target_certificate_hash;
        second_entry.target_revisions[0].target_export_hash =
            first_entry.target_revisions[0].target_export_hash;

        let mut entries = vec![first, second];
        entries.sort_by_key(PromotionOriginEntryV2::promotion_id);
        let mut registry = PromotionOriginRegistryV2 {
            schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
            registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
            registry_version: 2,
            generation: 1,
            target_package: PackageId::new("npa-mathlib"),
            entries,
            unresolved_legacy_targets: Vec::new(),
            registry_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        assert!(registry.refresh_hash().is_err());
    }

    #[test]
    fn declaration_registry_collides_on_exact_declaration_identity_not_names_alone() {
        let first = declaration_entry(1);
        let mut changed = declaration_entry(40);
        let PromotionOriginEntryV2::DeclarationClosureV1(first_entry) = &first else {
            unreachable!()
        };
        let PromotionOriginEntryV2::DeclarationClosureV1(changed_entry) = &mut changed else {
            unreachable!()
        };
        changed_entry.source_module = first_entry.source_module.clone();
        changed_entry.canonical_source.source_module = first_entry.source_module.clone();
        changed_entry.roots[0].requested_name = first_entry.roots[0].requested_name.clone();
        changed_entry.roots[0].owner_name = first_entry.roots[0].owner_name.clone();
        changed_entry.closure[0].source_name = first_entry.closure[0].source_name.clone();
        changed_entry.closure[0].target_name = first_entry.closure[0].target_name.clone();
        changed_entry.closure[0].family_owner = first_entry.closure[0].family_owner.clone();
        changed_entry.closure[0].family_members = first_entry.closure[0].family_members.clone();
        refresh_declaration_route_identity(&mut changed);

        let valid = registry(1, vec![first.clone(), changed.clone()]);
        validate_promotion_origin_registry_v2(&valid).unwrap();

        let PromotionOriginEntryV2::DeclarationClosureV1(changed_entry) = &mut changed else {
            unreachable!()
        };
        changed_entry.closure[0].decl_interface_hash = first_entry.closure[0].decl_interface_hash;
        refresh_declaration_route_identity(&mut changed);
        let mut collision = registry(1, vec![first]);
        collision.entries.push(changed);
        collision
            .entries
            .sort_by_key(PromotionOriginEntryV2::promotion_id);
        assert!(collision.refresh_hash().is_err());
    }

    #[test]
    fn whole_module_reservation_uses_exact_source_artifact_identity() {
        let mut previous = whole_module_v1_registry();
        let whole_source = previous.entries[0].canonical_source.modules[0].clone();
        previous.refresh_hash().unwrap();
        let mut migrated = migrate_promotion_origin_registry_v1_to_v2(&previous).unwrap();
        let mut changed = declaration_entry(40);
        let PromotionOriginEntryV2::DeclarationClosureV1(changed_entry) = &mut changed else {
            unreachable!()
        };
        changed_entry.source_module = whole_source.module.clone();
        changed_entry.canonical_source.source_module = whole_source.module.clone();
        refresh_declaration_route_identity(&mut changed);
        migrated.entries.push(changed.clone());
        migrated
            .entries
            .sort_by_key(PromotionOriginEntryV2::promotion_id);
        migrated.generation += 1;
        migrated.refresh_hash().unwrap();

        let PromotionOriginEntryV2::DeclarationClosureV1(changed_entry) = &mut changed else {
            unreachable!()
        };
        changed_entry.canonical_source.source_file_hash = whole_source.source_file_hash;
        changed_entry.canonical_source.certificate_file_hash = whole_source.certificate_file_hash;
        changed_entry.canonical_source.certificate_hash = whole_source.certificate_hash;
        changed_entry.canonical_source.export_hash = whole_source.export_hash;
        let mut collision = migrate_promotion_origin_registry_v1_to_v2(&previous).unwrap();
        collision.entries.push(changed);
        collision
            .entries
            .sort_by_key(PromotionOriginEntryV2::promotion_id);
        collision.generation += 1;
        assert!(collision.refresh_hash().is_err());
    }

    #[test]
    fn declaration_registry_rejects_mismatched_introduced_revision_and_edges() {
        let mut introduced = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut introduced.entries[0] else {
            unreachable!()
        };
        entry.introduced_version = PackageVersion::new("0.3.0");
        assert!(validate_promotion_origin_registry_v2(&introduced).is_err());

        let mut edges = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut edges.entries[0] else {
            unreachable!()
        };
        entry.canonical_source.dependency_edge_hash = hash(99);
        assert!(validate_promotion_origin_registry_v2(&edges).is_err());

        let mut revisions = registry(1, vec![declaration_entry(1)]);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut revisions.entries[0] else {
            unreachable!()
        };
        let mut second = entry.target_revisions[0].clone();
        second.target_version = PackageVersion::new("0.3.0");
        entry.target_revisions.push(second);
        assert!(validate_promotion_origin_registry_v2(&revisions).is_err());
    }

    #[test]
    fn declaration_registry_rejects_nonhistorical_local_mapping_endpoints() {
        let mut route = declaration_entry(1);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut route else {
            unreachable!()
        };
        entry
            .dependency_mappings
            .push(PromotionPlanV2DependencyMapping {
                source: crate::promotion_plan::PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: entry.canonical_source.package.clone(),
                    version: entry.canonical_source.version.clone(),
                    module: Name::from_dotted("Proofs.Dependency"),
                },
                target: crate::promotion_plan::PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: PackageId::new("npa-mathlib"),
                    version: PackageVersion::new("0.1.0"),
                    module: Name::from_dotted("Mathlib.Dependency"),
                },
                declaration_name: Name::from_dotted("helper"),
                source_decl_interface_hash: hash(80),
                target_decl_interface_hash: hash(80),
                target_certificate_file_hash: hash(81),
                target_certificate_hash: hash(82),
                target_export_hash: hash(83),
            });
        refresh_declaration_route_identity(&mut route);
        let target_package = PackageId::new("npa-mathlib");
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &route else {
            unreachable!()
        };
        validate_declaration_entry(entry, 0, &target_package).unwrap();

        let mut wrong_source = route.clone();
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut wrong_source else {
            unreachable!()
        };
        entry.dependency_mappings[0].source.version = PackageVersion::new("0.1.1");
        refresh_declaration_route_identity(&mut wrong_source);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &wrong_source else {
            unreachable!()
        };
        assert!(validate_declaration_entry(entry, 0, &target_package).is_err());

        let mut future_target = route.clone();
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut future_target else {
            unreachable!()
        };
        entry.dependency_mappings[0].target.version = entry.introduced_version.clone();
        refresh_declaration_route_identity(&mut future_target);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &future_target else {
            unreachable!()
        };
        assert!(validate_declaration_entry(entry, 0, &target_package).is_err());

        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut route else {
            unreachable!()
        };
        entry.dependency_mappings[0].target.module = entry.target_module.clone();
        refresh_declaration_route_identity(&mut route);
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &route else {
            unreachable!()
        };
        assert!(validate_declaration_entry(entry, 0, &target_package).is_err());
    }

    #[test]
    fn v2_transition_accepts_exactly_one_route_or_one_equivalent_origin() {
        let previous = registry(1, vec![declaration_entry(1)]);

        let next_route = registry(2, vec![declaration_entry(1), declaration_entry(40)]);
        validate_promotion_origin_registry_v2_transition(&previous, &next_route).unwrap();

        let mut next_alias = previous.clone();
        next_alias.generation += 1;
        let alias = equivalent_source(&next_alias.entries[0], "one");
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut next_alias.entries[0] else {
            unreachable!()
        };
        entry.equivalent_sources.push(alias);
        next_alias.refresh_hash().unwrap();
        validate_promotion_origin_registry_v2_transition(&previous, &next_alias).unwrap();

        let batch_routes = registry(
            2,
            vec![
                declaration_entry(1),
                declaration_entry(40),
                declaration_entry(80),
            ],
        );
        assert!(
            validate_promotion_origin_registry_v2_transition(&previous, &batch_routes).is_err()
        );

        let mut batch_aliases = previous.clone();
        batch_aliases.generation += 1;
        let aliases = [
            equivalent_source(&batch_aliases.entries[0], "one"),
            equivalent_source(&batch_aliases.entries[0], "two"),
        ];
        let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut batch_aliases.entries[0]
        else {
            unreachable!()
        };
        entry.equivalent_sources.extend(aliases);
        entry.equivalent_sources.sort();
        batch_aliases.refresh_hash().unwrap();
        assert!(
            validate_promotion_origin_registry_v2_transition(&previous, &batch_aliases).is_err()
        );
    }

    #[test]
    fn v2_transition_rejects_generation_overflow_without_panicking() {
        let previous = registry(u64::MAX, vec![declaration_entry(1)]);
        let next = previous.clone();

        assert!(validate_promotion_origin_registry_v2_transition(&previous, &next).is_err());
    }

    #[test]
    fn v1_to_v2_transition_accepts_one_equivalent_origin() {
        let previous = whole_module_v1_registry();
        let mut next = migrate_promotion_origin_registry_v1_to_v2(&previous).unwrap();
        next.generation += 1;
        let PromotionOriginEntryV2::WholeModuleV1(entry) = &mut next.entries[0] else {
            unreachable!()
        };
        let mut alias = entry.canonical_source.clone();
        alias.package = PackageId::new("legacy-source-alias");
        entry.equivalent_sources.push(alias);
        next.refresh_hash().unwrap();

        validate_promotion_origin_registry_v1_to_v2_transition(&previous, &next).unwrap();
    }

    #[test]
    fn v2_lookup_blocks_complete_module_overlap_with_declaration_routes() {
        let entry = declaration_entry(1);
        let PromotionOriginEntryV2::DeclarationClosureV1(declaration) = &entry else {
            unreachable!()
        };
        let exact = PromotionSourceOrigin {
            package: declaration.canonical_source.package.clone(),
            version: declaration.canonical_source.version.clone(),
            modules: vec![PromotionSourceModule {
                module: declaration.source_module.clone(),
                source_file_hash: declaration.canonical_source.source_file_hash,
                certificate_file_hash: declaration.canonical_source.certificate_file_hash,
                certificate_hash: declaration.canonical_source.certificate_hash,
                export_hash: declaration.canonical_source.export_hash,
            }],
        };
        let target_module = declaration.target_module.clone();
        let target_artifact = (
            declaration.target_revisions[0].target_certificate_hash,
            declaration.target_revisions[0].target_export_hash,
        );
        let registry = registry(1, vec![entry]);

        assert_eq!(
            lookup_promotion_origin_v2(&registry, &exact, &[], &[]),
            PromotionOriginLookup::ExactOriginAlreadyPromoted
        );

        let mut alias = exact.clone();
        alias.package = PackageId::new("source-artifact-alias");
        assert_eq!(
            lookup_promotion_origin_v2(&registry, &alias, &[], &[]),
            PromotionOriginLookup::ArtifactAliasAlreadyPromoted
        );

        let mut changed = exact.clone();
        changed.modules[0].source_file_hash = hash(89);
        assert_eq!(
            lookup_promotion_origin_v2(&registry, &changed, &[], &[]),
            PromotionOriginLookup::NoRegistryMatch
        );

        let unrelated = PromotionSourceOrigin {
            package: PackageId::new("unrelated-source"),
            version: PackageVersion::new("0.1.0"),
            modules: vec![PromotionSourceModule {
                module: Name::from_dotted("Proofs.Unrelated"),
                source_file_hash: hash(90),
                certificate_file_hash: hash(91),
                certificate_hash: hash(92),
                export_hash: hash(93),
            }],
        };
        assert_eq!(
            lookup_promotion_origin_v2(&registry, &unrelated, &[target_module], &[]),
            PromotionOriginLookup::TargetModuleCollision
        );
        assert_eq!(
            lookup_promotion_origin_v2(&registry, &unrelated, &[], &[target_artifact]),
            PromotionOriginLookup::TargetArtifactCollision
        );
    }
}

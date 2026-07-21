//! Canonical declaration-level mathlib promotion plan v2.
//!
//! The plan binds verified package snapshots and a selected declaration
//! closure. It is deterministic workflow input, not proof evidence.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{Name, DECLARATION_CLOSURE_LIMITS_V1};

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_path, required_string, required_u64, required_value,
        validate_declaration_name, validate_module_name, validate_package_identity,
        PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, parse_package_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    promotion_plan::{PromotionPackageSnapshot, PromotionPlanEndpoint},
    schema::{MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA, MATHLIB_PROMOTION_PLAN_V2_SCHEMA},
};

const PLAN_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-PLAN-v2\0";
const ROUTE_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-ROUTE-v2\0";
const EDGE_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-PLAN-EDGES-v2\0";
pub(crate) const DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS: usize =
    DECLARATION_CLOSURE_LIMITS_V1.requested_roots;
pub(crate) const DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES: usize =
    DECLARATION_CLOSURE_LIMITS_V1.loaded_modules;
// Each equivalent origin requires an independently validated source snapshot.
pub(crate) const DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES: usize =
    DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES;
pub(crate) const DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS: usize =
    DECLARATION_CLOSURE_LIMITS_V1.materialized_declarations;
pub(crate) const DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS: usize =
    DECLARATION_CLOSURE_LIMITS_V1.generated_exports;
pub(crate) const DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES: usize =
    DECLARATION_CLOSURE_LIMITS_V1.dependency_edges;
const DECLARATION_PROMOTION_V1_MAX_FAMILY_MEMBERS: usize =
    DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS
        + DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS;
const PLAN_FIELDS: &[&str] = &[
    "schema",
    "promotion_id",
    "source",
    "target_baseline",
    "governance",
    "selection",
    "dependency_mappings",
    "equivalent_sources",
    "requested_maturity",
    "plan_hash",
    "proof_evidence",
];
const SOURCE_FIELDS: &[&str] = &[
    "package",
    "version",
    "manifest_file_hash",
    "lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
];
const TARGET_FIELDS: &[&str] = &[
    "package",
    "version",
    "planned_version",
    "manifest_file_hash",
    "lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
    "verified_export_summary_file_hash",
    "publish_plan_file_hash",
    "registry_file_hash",
];
const GOVERNANCE_FIELDS: &[&str] = &[
    "request_path",
    "request_schema",
    "request_file_hash",
    "catalog_policy_file_hash",
    "namespace_policy_file_hash",
];
const SELECTION_FIELDS: &[&str] = &[
    "source_module",
    "target_module",
    "source_path",
    "source_file_hash",
    "meta_path",
    "meta_file_hash",
    "replay_path",
    "replay_file_hash",
    "certificate_path",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
    "axiom_report_hash",
    "roots",
    "materialized_declarations",
    "generated_exports",
    "declaration_closure_hash",
];
const ROOT_FIELDS: &[&str] = &["requested_name", "owner_name", "kind"];
const DECL_FIELDS: &[&str] = &[
    "role",
    "source_name",
    "target_name",
    "certificate_kind",
    "human_kind",
    "source_decl_index",
    "decl_interface_hash",
    "decl_certificate_hash",
    "type_hash",
    "body_hash",
    "item_span",
    "family_owner",
    "family_members",
    "generated_exports",
    "direct_dependencies",
];
const SPAN_FIELDS: &[&str] = &["start", "end"];
const IDENTITY_FIELDS: &[&str] = &["module", "name", "kind", "decl_interface_hash"];
const MAPPING_FIELDS: &[&str] = &[
    "source",
    "target",
    "declaration_name",
    "source_decl_interface_hash",
    "target_decl_interface_hash",
    "target_certificate_file_hash",
    "target_certificate_hash",
    "target_export_hash",
];
const ENDPOINT_FIELDS: &[&str] = &["origin", "package", "version", "module"];
const EQUIVALENT_FIELDS: &[&str] = &[
    "package",
    "version",
    "source_module",
    "source_file_hash",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
    "declaration_closure_hash",
    "dependency_edge_hash",
];

/// Clean target snapshot plus declaration-promotion governance projections.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTargetSnapshotV2 {
    /// Target package ID.
    pub package: PackageId,
    /// Baseline version.
    pub version: PackageVersion,
    /// Planned version.
    pub planned_version: PackageVersion,
    /// Exact manifest file hash.
    pub manifest_file_hash: PackageHash,
    /// Exact checked package-lock file hash.
    pub lock_file_hash: PackageHash,
    /// Exact axiom-report file hash.
    pub axiom_report_file_hash: PackageHash,
    /// Exact theorem-index file hash.
    pub theorem_index_file_hash: PackageHash,
    /// Exact verified-export-summary file hash.
    pub verified_export_summary_file_hash: PackageHash,
    /// Exact publish-plan file hash.
    pub publish_plan_file_hash: PackageHash,
    /// Exact promotion registry file hash.
    pub registry_file_hash: PackageHash,
}

/// Fixed governance inputs bound by declaration plan v2.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionGovernanceV2 {
    /// Source-root-relative request path.
    pub request_path: PackagePath,
    /// Exact request schema.
    pub request_schema: String,
    /// Exact request bytes hash.
    pub request_file_hash: PackageHash,
    /// Baseline catalog policy bytes hash.
    pub catalog_policy_file_hash: PackageHash,
    /// Baseline namespace policy bytes hash.
    pub namespace_policy_file_hash: PackageHash,
}

/// Requested name and normalized owner name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionPlanV2Root {
    /// Exact requested export name.
    pub requested_name: Name,
    /// Certificate/source-family owner name.
    pub owner_name: Name,
    /// Human request kind.
    pub kind: String,
}

/// Byte span in the selected source file.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionSourceSpan {
    /// Inclusive UTF-8 byte start.
    pub start: u64,
    /// Exclusive UTF-8 byte end.
    pub end: u64,
}

/// Exact resolved declaration identity used by closure rows and edges.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionPlanV2Identity {
    /// Provider module.
    pub module: Name,
    /// Declaration name.
    pub name: Name,
    /// Stable certificate kind.
    pub kind: String,
    /// Verified interface hash.
    pub decl_interface_hash: PackageHash,
}

/// One materialized declaration certificate in the selected closure.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionPlanV2Declaration {
    /// `root` or `support`.
    pub role: String,
    /// Source declaration name.
    pub source_name: Name,
    /// Target declaration name, equal in v1 request semantics.
    pub target_name: Name,
    /// Certificate kind.
    pub certificate_kind: String,
    /// Human/source kind.
    pub human_kind: String,
    /// Verified source declaration-table index.
    pub source_decl_index: u64,
    /// Public interface hash.
    pub decl_interface_hash: PackageHash,
    /// Full declaration certificate hash.
    pub decl_certificate_hash: PackageHash,
    /// Export type hash.
    pub type_hash: PackageHash,
    /// Export body hash when exported.
    pub body_hash: Option<PackageHash>,
    /// Owning top-level Human item span.
    pub item_span: PromotionSourceSpan,
    /// Stable source-family owner.
    pub family_owner: Name,
    /// Complete family membership.
    pub family_members: Vec<Name>,
    /// Generated exports owned by this declaration.
    pub generated_exports: Vec<PromotionPlanV2Identity>,
    /// Sorted exact direct dependencies.
    pub direct_dependencies: Vec<PromotionPlanV2Identity>,
}

/// Selected source sidecars and complete declaration closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionSelectionV2 {
    /// Source module.
    pub source_module: Name,
    /// New target module.
    pub target_module: Name,
    /// Source path.
    pub source_path: PackagePath,
    /// Source bytes hash.
    pub source_file_hash: PackageHash,
    /// Metadata sidecar path.
    pub meta_path: PackagePath,
    /// Metadata sidecar bytes hash.
    pub meta_file_hash: PackageHash,
    /// Replay sidecar path.
    pub replay_path: PackagePath,
    /// Replay sidecar bytes hash.
    pub replay_file_hash: PackageHash,
    /// Certificate path.
    pub certificate_path: PackagePath,
    /// Certificate file bytes hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical export hash.
    pub export_hash: PackageHash,
    /// Canonical axiom-report hash.
    pub axiom_report_hash: PackageHash,
    /// Requested roots.
    pub roots: Vec<PromotionPlanV2Root>,
    /// Complete materialized declaration closure.
    pub materialized_declarations: Vec<PromotionPlanV2Declaration>,
    /// Complete generated export inventory.
    pub generated_exports: Vec<PromotionPlanV2Identity>,
    /// Domain-separated declaration closure hash.
    pub declaration_closure_hash: PackageHash,
}

/// One reached and validated externalized declaration mapping.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionPlanV2DependencyMapping {
    /// Exact source endpoint.
    pub source: PromotionPlanEndpoint,
    /// Exact target endpoint.
    pub target: PromotionPlanEndpoint,
    /// Same declaration name at both endpoints.
    pub declaration_name: Name,
    /// Source interface hash.
    pub source_decl_interface_hash: PackageHash,
    /// Target interface hash.
    pub target_decl_interface_hash: PackageHash,
    /// Target certificate file hash.
    pub target_certificate_file_hash: PackageHash,
    /// Target canonical certificate hash.
    pub target_certificate_hash: PackageHash,
    /// Target export hash.
    pub target_export_hash: PackageHash,
}

/// Artifact-identical equivalent source origin for the selected closure.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionPlanV2EquivalentSource {
    /// Equivalent package ID.
    pub package: PackageId,
    /// Equivalent package version.
    pub version: PackageVersion,
    /// Equivalent source module.
    pub source_module: Name,
    /// Source bytes hash.
    pub source_file_hash: PackageHash,
    /// Certificate bytes hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical export hash.
    pub export_hash: PackageHash,
    /// Exact selected closure hash.
    pub declaration_closure_hash: PackageHash,
    /// Exact selected edge projection hash.
    pub dependency_edge_hash: PackageHash,
}

/// Canonical declaration-level mathlib promotion plan v2.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MathlibPromotionPlanV2 {
    /// Exact v2 schema.
    pub schema: String,
    /// Stable route ID.
    pub promotion_id: PackageHash,
    /// Source generated-artifact snapshot.
    pub source: PromotionPackageSnapshot,
    /// Target baseline snapshot.
    pub target_baseline: PromotionTargetSnapshotV2,
    /// Governance inputs.
    pub governance: PromotionGovernanceV2,
    /// Selected declaration closure.
    pub selection: PromotionSelectionV2,
    /// Used externalized dependency mappings.
    pub dependency_mappings: Vec<PromotionPlanV2DependencyMapping>,
    /// Artifact-identical source origins.
    pub equivalent_sources: Vec<PromotionPlanV2EquivalentSource>,
    /// Exactly `verified`.
    pub requested_maturity: String,
    /// Domain-separated self-hash.
    pub plan_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl MathlibPromotionPlanV2 {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_mathlib_promotion_plan_v2(self)?;
        Ok(format!("{}\n", plan_json(self)))
    }

    /// Recompute the stable route ID and plan self-hash.
    pub fn finalize(&mut self) -> PackageArtifactResult<()> {
        self.promotion_id = mathlib_promotion_route_id_v2(self)?;
        self.plan_hash = mathlib_promotion_plan_hash_v2(self)?;
        Ok(())
    }
}

/// Parse and validate strict canonical plan v2 JSON.
pub fn parse_mathlib_promotion_plan_v2_json(
    source: &str,
) -> PackageArtifactResult<MathlibPromotionPlanV2> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, PLAN_FIELDS)?;
    let plan = MathlibPromotionPlanV2 {
        schema: required_string(members, "$", "schema")?,
        promotion_id: required_hash(members, "$", "promotion_id")?,
        source: parse_source(required_value(members, "$", "source")?, "source")?,
        target_baseline: parse_target(
            required_value(members, "$", "target_baseline")?,
            "target_baseline",
        )?,
        governance: parse_governance(required_value(members, "$", "governance")?, "governance")?,
        selection: parse_selection(required_value(members, "$", "selection")?, "selection")?,
        dependency_mappings: parse_array_bounded(
            members,
            "$",
            "dependency_mappings",
            DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
            parse_mapping,
        )?,
        equivalent_sources: parse_array_bounded(
            members,
            "$",
            "equivalent_sources",
            DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES,
            parse_equivalent,
        )?,
        requested_maturity: required_string(members, "$", "requested_maturity")?,
        plan_hash: required_hash(members, "$", "plan_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_mathlib_promotion_plan_v2(&plan)?;
    if source != plan.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "promotion plan v2 JSON bytes",
        ));
    }
    Ok(plan)
}

/// Compute plan v2 self-hash with its hash field zeroed.
pub fn mathlib_promotion_plan_hash_v2(
    plan: &MathlibPromotionPlanV2,
) -> PackageArtifactResult<PackageHash> {
    validate_plan_shape(plan, false, true)?;
    let mut copy = plan.clone();
    copy.plan_hash = PackageHash::new([0; 32]);
    Ok(domain_hash(PLAN_DOMAIN, plan_json(&copy).as_bytes()))
}

/// Compute stable route ID excluding planned target version.
pub fn mathlib_promotion_route_id_v2(
    plan: &MathlibPromotionPlanV2,
) -> PackageArtifactResult<PackageHash> {
    validate_plan_shape(plan, false, false)?;
    mathlib_declaration_promotion_route_id_v2(
        &plan.source.package,
        &plan.source.version,
        &plan.selection.source_module,
        &plan.selection.target_module,
        &plan.selection.roots,
        plan.selection.declaration_closure_hash,
    )
}

/// Compute a declaration route ID from the exact fields retained by registry v2.
pub fn mathlib_declaration_promotion_route_id_v2(
    source_package: &PackageId,
    source_version: &PackageVersion,
    source_module: &Name,
    target_module: &Name,
    roots: &[PromotionPlanV2Root],
    declaration_closure_hash: PackageHash,
) -> PackageArtifactResult<PackageHash> {
    validate_package_identity(source_package, source_version)?;
    validate_module_name(source_module, "source_module")?;
    validate_module_name(target_module, "target_module")?;
    if !target_module.as_dotted().starts_with("Mathlib.") {
        return Err(PackageArtifactError::invalid_enum_value(
            "target_module",
            "target_module",
            "Mathlib.* module",
            target_module.as_dotted(),
        ));
    }
    if roots.is_empty() {
        return Err(PackageArtifactError::non_canonical(
            "roots",
            "nonempty declaration roots",
        ));
    }
    validate_declaration_promotion_resource_count(
        "$",
        "roots",
        roots.len(),
        DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS,
    )?;
    ensure_strict(roots, "roots")?;
    for root in roots {
        validate_promotion_plan_v2_root(root, "roots")?;
    }
    let route = json_object_in_order(vec![
        ("source_package", json_string(source_package.as_str())),
        ("source_version", json_string(source_version.as_str())),
        ("source_module", json_string(&source_module.as_dotted())),
        ("target_module", json_string(&target_module.as_dotted())),
        ("roots", json_array(roots.iter().map(root_json).collect())),
        (
            "declaration_closure_hash",
            hash_json(declaration_closure_hash),
        ),
    ]);
    Ok(domain_hash(ROUTE_DOMAIN, route.as_bytes()))
}

/// Compute the stable selected-edge identity used by equivalent source rows.
pub fn promotion_plan_v2_dependency_edge_hash(
    declarations: &[PromotionPlanV2Declaration],
    mappings: &[PromotionPlanV2DependencyMapping],
) -> PackageArtifactResult<PackageHash> {
    validate_declaration_promotion_resource_limits(
        None,
        None,
        None,
        declarations,
        None,
        mappings,
        "$",
    )?;
    ensure_strict(declarations, "materialized_declarations")?;
    ensure_strict(mappings, "dependency_mappings")?;
    let value = json_object_in_order(vec![
        (
            "declarations",
            json_array(
                declarations
                    .iter()
                    .map(|row| {
                        json_object_in_order(vec![
                            (
                                "source",
                                identity_json(&PromotionPlanV2Identity {
                                    module: Name::from_dotted("$selected"),
                                    name: row.source_name.clone(),
                                    kind: row.certificate_kind.clone(),
                                    decl_interface_hash: row.decl_interface_hash,
                                }),
                            ),
                            (
                                "direct_dependencies",
                                json_array(
                                    row.direct_dependencies.iter().map(identity_json).collect(),
                                ),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "externalized",
            json_array(mappings.iter().map(mapping_json).collect()),
        ),
    ]);
    Ok(domain_hash(EDGE_DOMAIN, value.as_bytes()))
}

/// Validate plan v2 schema, canonical order, identities, route ID, and self-hash.
pub fn validate_mathlib_promotion_plan_v2(
    plan: &MathlibPromotionPlanV2,
) -> PackageArtifactResult<()> {
    validate_plan_shape(plan, true, true)
}

fn validate_plan_shape(
    plan: &MathlibPromotionPlanV2,
    check_hash: bool,
    check_route: bool,
) -> PackageArtifactResult<()> {
    if plan.schema != MATHLIB_PROMOTION_PLAN_V2_SCHEMA
        || plan.requested_maturity != "verified"
        || plan.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "fixed_values",
            "plan v2, verified, false",
            "mismatch",
        ));
    }
    validate_package_identity(&plan.source.package, &plan.source.version)?;
    validate_promotion_target_snapshot_v2(&plan.target_baseline, "target_baseline")?;
    if plan.governance.request_schema != MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA
        || plan.selection.roots.is_empty()
        || plan.selection.materialized_declarations.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "identity",
            "valid declaration promotion identity",
            "mismatch",
        ));
    }
    validate_declaration_promotion_resource_limits(
        Some(&plan.selection.source_module),
        Some(&plan.selection.target_module),
        Some(&plan.selection.roots),
        &plan.selection.materialized_declarations,
        Some(&plan.selection.generated_exports),
        &plan.dependency_mappings,
        "selection",
    )?;
    validate_declaration_promotion_resource_count(
        "$",
        "equivalent_sources",
        plan.equivalent_sources.len(),
        DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES,
    )?;
    validate_package_path(&plan.governance.request_path, "governance.request_path").map_err(
        |_| {
            PackageArtifactError::invalid_path(
                "governance.request_path",
                plan.governance.request_path.as_str(),
            )
        },
    )?;
    validate_module_name(&plan.selection.source_module, "selection.source_module")?;
    validate_module_name(&plan.selection.target_module, "selection.target_module")?;
    if !plan
        .selection
        .target_module
        .as_dotted()
        .starts_with("Mathlib.")
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "selection.target_module",
            "target_module",
            "Mathlib.* module",
            plan.selection.target_module.as_dotted(),
        ));
    }
    for (path, value) in [
        ("source_path", &plan.selection.source_path),
        ("meta_path", &plan.selection.meta_path),
        ("replay_path", &plan.selection.replay_path),
        ("certificate_path", &plan.selection.certificate_path),
    ] {
        validate_package_path(value, path)
            .map_err(|_| PackageArtifactError::invalid_path(path, value.as_str()))?;
    }
    ensure_strict(&plan.selection.roots, "selection.roots")?;
    ensure_strict(
        &plan.selection.materialized_declarations,
        "selection.materialized_declarations",
    )?;
    ensure_strict(
        &plan.selection.generated_exports,
        "selection.generated_exports",
    )?;
    ensure_strict(&plan.dependency_mappings, "dependency_mappings")?;
    ensure_strict(&plan.equivalent_sources, "equivalent_sources")?;
    let mut declaration_names = BTreeSet::new();
    for root in &plan.selection.roots {
        validate_promotion_plan_v2_root(root, "selection.roots")?;
    }
    for declaration in &plan.selection.materialized_declarations {
        validate_promotion_plan_v2_declaration(declaration, "selection.materialized_declarations")?;
        if !declaration_names.insert(declaration.source_name.clone()) {
            return Err(PackageArtifactError::non_canonical(
                "selection.materialized_declarations",
                "unique declaration names",
            ));
        }
    }
    validate_promotion_plan_v2_closure_relationships(
        &plan.selection.source_module,
        &plan.selection.roots,
        &plan.selection.materialized_declarations,
        "selection",
    )?;
    let generated = plan
        .selection
        .materialized_declarations
        .iter()
        .flat_map(|row| row.generated_exports.iter().cloned())
        .collect::<BTreeSet<_>>();
    if generated != plan.selection.generated_exports.iter().cloned().collect() {
        return Err(PackageArtifactError::non_canonical(
            "selection.generated_exports",
            "complete generated export union",
        ));
    }
    for identity in &plan.selection.generated_exports {
        validate_promotion_plan_v2_identity(identity, "selection.generated_exports")?;
    }
    let source_axiom_dependencies = plan
        .selection
        .materialized_declarations
        .iter()
        .flat_map(|declaration| &declaration.direct_dependencies)
        .filter(|dependency| dependency.kind == "axiom")
        .map(|dependency| (&dependency.module, &dependency.name))
        .collect::<BTreeSet<_>>();
    for mapping in &plan.dependency_mappings {
        validate_promotion_plan_v2_mapping(mapping, "dependency_mappings")?;
        if (mapping.source.origin == PackageArtifactOrigin::Local
            && (mapping.source.package != plan.source.package
                || mapping.source.version != plan.source.version))
            || (mapping.target.origin == PackageArtifactOrigin::Local
                && (mapping.target.package != plan.target_baseline.package
                    || mapping.target.version != plan.target_baseline.version))
            || mapping.target.module == plan.selection.target_module
        {
            return Err(PackageArtifactError::invalid_enum_value(
                "dependency_mappings",
                "endpoint_identity",
                "local source and target-baseline identities distinct from the new target module",
                "mismatch",
            ));
        }
        if mapping.source.origin == PackageArtifactOrigin::Local
            && source_axiom_dependencies
                .contains(&(&mapping.source.module, &mapping.declaration_name))
        {
            return Err(PackageArtifactError::invalid_enum_value(
                "dependency_mappings",
                "source_axiom",
                "source-local axioms cannot be externalized",
                mapping.declaration_name.as_dotted(),
            ));
        }
    }
    let dependency_edge_hash = promotion_plan_v2_dependency_edge_hash(
        &plan.selection.materialized_declarations,
        &plan.dependency_mappings,
    )?;
    for equivalent in &plan.equivalent_sources {
        validate_package_identity(&equivalent.package, &equivalent.version)?;
        validate_module_name(
            &equivalent.source_module,
            "equivalent_sources.source_module",
        )?;
        if equivalent.source_module != plan.selection.source_module
            || equivalent.source_file_hash != plan.selection.source_file_hash
            || equivalent.certificate_file_hash != plan.selection.certificate_file_hash
            || equivalent.certificate_hash != plan.selection.certificate_hash
            || equivalent.export_hash != plan.selection.export_hash
            || equivalent.declaration_closure_hash != plan.selection.declaration_closure_hash
            || equivalent.dependency_edge_hash != dependency_edge_hash
            || (equivalent.package == plan.source.package
                && equivalent.version == plan.source.version)
        {
            return Err(PackageArtifactError::invalid_enum_value(
                "equivalent_sources",
                "artifact_identity",
                "distinct artifact-identical source origin with selected closure and edges",
                "mismatch",
            ));
        }
    }
    if check_route && plan.promotion_id != mathlib_promotion_route_id_v2(plan)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "promotion_id",
            "promotion_id",
            "recomputed route ID",
            crate::format_package_hash(&plan.promotion_id),
        ));
    }
    if check_hash && plan.plan_hash != mathlib_promotion_plan_hash_v2(plan)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "plan_hash",
            "plan_hash",
            "recomputed plan hash",
            crate::format_package_hash(&plan.plan_hash),
        ));
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_root(
    root: &PromotionPlanV2Root,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_declaration_name(&root.requested_name, format!("{path}.requested_name"))?;
    validate_declaration_name(&root.owner_name, format!("{path}.owner_name"))?;
    if !matches!(
        root.kind.as_str(),
        "theorem" | "definition" | "inductive" | "class" | "instance"
    ) {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "kind",
            "theorem, definition, inductive, class, or instance",
            &root.kind,
        ));
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_identity(
    identity: &PromotionPlanV2Identity,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_module_name(&identity.module, format!("{path}.module"))?;
    validate_declaration_name(&identity.name, format!("{path}.name"))?;
    if !matches!(
        identity.kind.as_str(),
        "axiom" | "definition" | "theorem" | "inductive" | "constructor" | "recursor"
    ) {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "kind",
            "axiom, definition, theorem, inductive, constructor, or recursor",
            &identity.kind,
        ));
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_declaration(
    declaration: &PromotionPlanV2Declaration,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_declaration_name(&declaration.source_name, format!("{path}.source_name"))?;
    validate_declaration_name(&declaration.target_name, format!("{path}.target_name"))?;
    validate_declaration_name(&declaration.family_owner, format!("{path}.family_owner"))?;
    if declaration.source_name != declaration.target_name
        || !matches!(declaration.role.as_str(), "root" | "support")
        || !matches!(
            declaration.certificate_kind.as_str(),
            "theorem" | "definition" | "inductive"
        )
        || !matches!(
            declaration.human_kind.as_str(),
            "theorem" | "definition" | "inductive" | "class" | "class_field" | "instance"
        )
        || declaration.item_span.start >= declaration.item_span.end
    {
        return Err(PackageArtifactError::non_canonical(
            path,
            "valid same-name declaration row",
        ));
    }
    validate_declaration_promotion_resource_count(
        path,
        "family_members",
        declaration.family_members.len(),
        DECLARATION_PROMOTION_V1_MAX_FAMILY_MEMBERS,
    )?;
    validate_declaration_promotion_resource_count(
        path,
        "generated_exports",
        declaration.generated_exports.len(),
        DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
    )?;
    validate_declaration_promotion_resource_count(
        path,
        "direct_dependencies",
        declaration.direct_dependencies.len(),
        DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
    )?;
    ensure_strict(
        &declaration.family_members,
        &format!("{path}.family_members"),
    )?;
    ensure_strict(
        &declaration.generated_exports,
        &format!("{path}.generated_exports"),
    )?;
    ensure_strict(
        &declaration.direct_dependencies,
        &format!("{path}.direct_dependencies"),
    )?;
    for member in &declaration.family_members {
        validate_declaration_name(member, format!("{path}.family_members"))?;
    }
    for identity in &declaration.generated_exports {
        validate_promotion_plan_v2_identity(identity, &format!("{path}.generated_exports"))?;
    }
    for identity in &declaration.direct_dependencies {
        validate_promotion_plan_v2_identity(identity, &format!("{path}.direct_dependencies"))?;
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_mapping(
    mapping: &PromotionPlanV2DependencyMapping,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_endpoint(&mapping.source, &format!("{path}.source"))?;
    validate_endpoint(&mapping.target, &format!("{path}.target"))?;
    validate_declaration_name(
        &mapping.declaration_name,
        format!("{path}.declaration_name"),
    )?;
    if mapping.source_decl_interface_hash != mapping.target_decl_interface_hash {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "decl_interface_hash",
            "equal source and target interface hash",
            "mismatch",
        ));
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_closure_relationships(
    source_module: &Name,
    roots: &[PromotionPlanV2Root],
    declarations: &[PromotionPlanV2Declaration],
    path: &str,
) -> PackageArtifactResult<()> {
    validate_promotion_plan_v2_generated_export_ownership(
        declarations,
        &format!("{path}.materialized_declarations"),
    )?;
    let mut by_name = BTreeMap::new();
    for declaration in declarations {
        if by_name
            .insert(declaration.source_name.clone(), declaration)
            .is_some()
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.materialized_declarations"),
                "unique declaration names",
            ));
        }
    }
    let root_owners = roots
        .iter()
        .map(|root| root.owner_name.clone())
        .collect::<BTreeSet<_>>();
    for root in roots {
        let Some(owner) = by_name.get(&root.owner_name) else {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.roots"),
                "owner_name",
                "materialized root owner",
                root.owner_name.as_dotted(),
            ));
        };
        if owner.role != "root"
            || owner.human_kind != root.kind
            || !owner.family_members.contains(&root.requested_name)
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.roots"),
                "root_identity",
                "requested family member with matching materialized owner kind",
                root.requested_name.as_dotted(),
            ));
        }
    }
    let mut family_shapes = BTreeMap::new();
    let mut family_actual = BTreeMap::<Name, BTreeSet<Name>>::new();
    for declaration in declarations {
        if (declaration.role == "root") != root_owners.contains(&declaration.family_owner)
            || !declaration
                .family_members
                .contains(&declaration.family_owner)
            || !declaration
                .family_members
                .contains(&declaration.source_name)
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.materialized_declarations"),
                "family",
                "complete family with role matching its root owner",
                declaration.source_name.as_dotted(),
            ));
        }
        let shape = (&declaration.family_members, declaration.item_span);
        if family_shapes
            .insert(declaration.family_owner.clone(), shape)
            .is_some_and(|old| old != shape)
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.materialized_declarations"),
                "one member inventory and item span per source family",
            ));
        }
        let actual = family_actual
            .entry(declaration.family_owner.clone())
            .or_default();
        actual.insert(declaration.source_name.clone());
        for generated in &declaration.generated_exports {
            if generated.module != *source_module
                || !declaration.family_members.contains(&generated.name)
            {
                return Err(PackageArtifactError::invalid_enum_value(
                    format!("{path}.materialized_declarations.generated_exports"),
                    "family",
                    "source-module export owned by the declaration family",
                    generated.name.as_dotted(),
                ));
            }
            actual.insert(generated.name.clone());
        }
    }
    for (owner, (members, _)) in family_shapes {
        if family_actual
            .get(&owner)
            .is_none_or(|actual| actual != &members.iter().cloned().collect::<BTreeSet<_>>())
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.materialized_declarations"),
                "complete source-family member inventory",
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_promotion_plan_v2_generated_export_ownership(
    declarations: &[PromotionPlanV2Declaration],
    path: &str,
) -> PackageArtifactResult<()> {
    let mut owned_generated_exports = BTreeSet::new();
    for generated in declarations
        .iter()
        .flat_map(|declaration| &declaration.generated_exports)
    {
        if !owned_generated_exports.insert((generated.module.clone(), generated.name.clone())) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.generated_exports"),
                "one declaration owner per generated export",
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_declaration_promotion_resource_count(
    path: &str,
    field: &str,
    actual: usize,
    maximum: usize,
) -> PackageArtifactResult<()> {
    if actual > maximum {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            field,
            format!("at most {maximum}"),
            actual.to_string(),
        ));
    }
    Ok(())
}

pub(crate) fn validate_declaration_promotion_resource_limits(
    source_module: Option<&Name>,
    target_module: Option<&Name>,
    roots: Option<&[PromotionPlanV2Root]>,
    declarations: &[PromotionPlanV2Declaration],
    generated_exports: Option<&[PromotionPlanV2Identity]>,
    dependency_mappings: &[PromotionPlanV2DependencyMapping],
    path: &str,
) -> PackageArtifactResult<()> {
    if let Some(roots) = roots {
        validate_declaration_promotion_resource_count(
            path,
            "roots",
            roots.len(),
            DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS,
        )?;
    }
    validate_declaration_promotion_resource_count(
        path,
        "materialized_declarations",
        declarations.len(),
        DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
    )?;
    if let Some(generated_exports) = generated_exports {
        validate_declaration_promotion_resource_count(
            path,
            "generated_exports",
            generated_exports.len(),
            DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
        )?;
    }
    validate_declaration_promotion_resource_count(
        path,
        "dependency_mappings",
        dependency_mappings.len(),
        DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
    )?;

    let mut source_loaded_modules = BTreeSet::new();
    if let Some(source_module) = source_module {
        source_loaded_modules.insert(source_module);
    }
    let mut target_loaded_modules = BTreeSet::new();
    if let Some(target_module) = target_module {
        target_loaded_modules.insert(target_module);
    }
    if let Some(generated_exports) = generated_exports {
        for generated in generated_exports {
            source_loaded_modules.insert(&generated.module);
            validate_declaration_promotion_resource_count(
                path,
                "loaded_modules",
                source_loaded_modules.len(),
                DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES,
            )?;
        }
    }
    let mut owned_generated_exports = 0usize;
    let mut dependency_edges = 0usize;
    for declaration in declarations {
        owned_generated_exports =
            owned_generated_exports.saturating_add(declaration.generated_exports.len());
        validate_declaration_promotion_resource_count(
            path,
            "generated_exports",
            owned_generated_exports,
            DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
        )?;
        for generated in &declaration.generated_exports {
            source_loaded_modules.insert(&generated.module);
            validate_declaration_promotion_resource_count(
                path,
                "loaded_modules",
                source_loaded_modules.len(),
                DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES,
            )?;
        }
        dependency_edges = dependency_edges.saturating_add(declaration.direct_dependencies.len());
        validate_declaration_promotion_resource_count(
            path,
            "dependency_edges",
            dependency_edges,
            DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
        )?;
        for dependency in &declaration.direct_dependencies {
            source_loaded_modules.insert(&dependency.module);
            validate_declaration_promotion_resource_count(
                path,
                "loaded_modules",
                source_loaded_modules.len(),
                DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES,
            )?;
        }
    }
    for mapping in dependency_mappings {
        source_loaded_modules.insert(&mapping.source.module);
        validate_declaration_promotion_resource_count(
            path,
            "loaded_modules",
            source_loaded_modules.len(),
            DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES,
        )?;
        target_loaded_modules.insert(&mapping.target.module);
        validate_declaration_promotion_resource_count(
            path,
            "loaded_modules",
            target_loaded_modules.len(),
            DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES,
        )?;
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

fn validate_endpoint(endpoint: &PromotionPlanEndpoint, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&endpoint.package, &endpoint.version)?;
    validate_module_name(&endpoint.module, format!("{path}.module"))
}

pub(crate) fn validate_promotion_target_snapshot_v2(
    target: &PromotionTargetSnapshotV2,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_package_identity(&target.package, &target.version)?;
    validate_package_identity(&target.package, &target.planned_version)?;
    if target.package.as_str() != "npa-mathlib"
        || !version_is_strictly_greater(&target.planned_version, &target.version)
    {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "identity",
            "npa-mathlib with strictly greater planned version",
            target.planned_version.as_str(),
        ));
    }
    Ok(())
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
        .map(|(index, value)| parser(value, &format!("{field}[{index}]")))
        .collect()
}

pub(crate) fn parse_source(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPackageSnapshot> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_FIELDS)?;
    Ok(PromotionPackageSnapshot {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        lock_file_hash: required_hash(members, path, "lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
    })
}

pub(crate) fn parse_target(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionTargetSnapshotV2> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TARGET_FIELDS)?;
    Ok(PromotionTargetSnapshotV2 {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        planned_version: PackageVersion::new(required_string(members, path, "planned_version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        lock_file_hash: required_hash(members, path, "lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
        verified_export_summary_file_hash: required_hash(
            members,
            path,
            "verified_export_summary_file_hash",
        )?,
        publish_plan_file_hash: required_hash(members, path, "publish_plan_file_hash")?,
        registry_file_hash: required_hash(members, path, "registry_file_hash")?,
    })
}

fn parse_governance(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionGovernanceV2> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GOVERNANCE_FIELDS)?;
    Ok(PromotionGovernanceV2 {
        request_path: required_path(members, path, "request_path")?,
        request_schema: required_string(members, path, "request_schema")?,
        request_file_hash: required_hash(members, path, "request_file_hash")?,
        catalog_policy_file_hash: required_hash(members, path, "catalog_policy_file_hash")?,
        namespace_policy_file_hash: required_hash(members, path, "namespace_policy_file_hash")?,
    })
}

fn parse_selection(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionSelectionV2> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SELECTION_FIELDS)?;
    Ok(PromotionSelectionV2 {
        source_module: required_name(members, path, "source_module")?,
        target_module: required_name(members, path, "target_module")?,
        source_path: required_path(members, path, "source_path")?,
        source_file_hash: required_hash(members, path, "source_file_hash")?,
        meta_path: required_path(members, path, "meta_path")?,
        meta_file_hash: required_hash(members, path, "meta_file_hash")?,
        replay_path: required_path(members, path, "replay_path")?,
        replay_file_hash: required_hash(members, path, "replay_file_hash")?,
        certificate_path: required_path(members, path, "certificate_path")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        roots: parse_array_bounded(
            members,
            path,
            "roots",
            DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS,
            parse_root,
        )?,
        materialized_declarations: parse_array_bounded(
            members,
            path,
            "materialized_declarations",
            DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
            parse_declaration,
        )?,
        generated_exports: parse_array_bounded(
            members,
            path,
            "generated_exports",
            DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
            parse_identity,
        )?,
        declaration_closure_hash: required_hash(members, path, "declaration_closure_hash")?,
    })
}

pub(crate) fn parse_root(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPlanV2Root> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ROOT_FIELDS)?;
    Ok(PromotionPlanV2Root {
        requested_name: required_name(members, path, "requested_name")?,
        owner_name: required_name(members, path, "owner_name")?,
        kind: required_string(members, path, "kind")?,
    })
}

pub(crate) fn parse_declaration(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPlanV2Declaration> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, DECL_FIELDS)?;
    Ok(PromotionPlanV2Declaration {
        role: required_string(members, path, "role")?,
        source_name: required_name(members, path, "source_name")?,
        target_name: required_name(members, path, "target_name")?,
        certificate_kind: required_string(members, path, "certificate_kind")?,
        human_kind: required_string(members, path, "human_kind")?,
        source_decl_index: required_u64(members, path, "source_decl_index")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
        decl_certificate_hash: required_hash(members, path, "decl_certificate_hash")?,
        type_hash: required_hash(members, path, "type_hash")?,
        body_hash: parse_optional_hash(
            required_value(members, path, "body_hash")?,
            &format!("{path}.body_hash"),
        )?,
        item_span: parse_span(
            required_value(members, path, "item_span")?,
            &format!("{path}.item_span"),
        )?,
        family_owner: required_name(members, path, "family_owner")?,
        family_members: parse_name_array(members, path, "family_members")?,
        generated_exports: parse_array_bounded(
            members,
            path,
            "generated_exports",
            DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
            parse_identity,
        )?,
        direct_dependencies: parse_array_bounded(
            members,
            path,
            "direct_dependencies",
            DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
            parse_identity,
        )?,
    })
}

fn parse_span(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionSourceSpan> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SPAN_FIELDS)?;
    Ok(PromotionSourceSpan {
        start: required_u64(members, path, "start")?,
        end: required_u64(members, path, "end")?,
    })
}

pub(crate) fn parse_identity(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPlanV2Identity> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, IDENTITY_FIELDS)?;
    Ok(PromotionPlanV2Identity {
        module: required_name(members, path, "module")?,
        name: required_name(members, path, "name")?,
        kind: required_string(members, path, "kind")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
    })
}

pub(crate) fn parse_mapping(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPlanV2DependencyMapping> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, MAPPING_FIELDS)?;
    Ok(PromotionPlanV2DependencyMapping {
        source: parse_endpoint(
            required_value(members, path, "source")?,
            &format!("{path}.source"),
        )?,
        target: parse_endpoint(
            required_value(members, path, "target")?,
            &format!("{path}.target"),
        )?,
        declaration_name: required_name(members, path, "declaration_name")?,
        source_decl_interface_hash: required_hash(members, path, "source_decl_interface_hash")?,
        target_decl_interface_hash: required_hash(members, path, "target_decl_interface_hash")?,
        target_certificate_file_hash: required_hash(members, path, "target_certificate_file_hash")?,
        target_certificate_hash: required_hash(members, path, "target_certificate_hash")?,
        target_export_hash: required_hash(members, path, "target_export_hash")?,
    })
}

fn parse_endpoint(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionPlanEndpoint> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ENDPOINT_FIELDS)?;
    Ok(PromotionPlanEndpoint {
        origin: PackageArtifactOrigin::parse(&required_string(members, path, "origin")?, path)?,
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        module: required_name(members, path, "module")?,
    })
}

pub(crate) fn parse_equivalent(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPlanV2EquivalentSource> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, EQUIVALENT_FIELDS)?;
    Ok(PromotionPlanV2EquivalentSource {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        source_module: required_name(members, path, "source_module")?,
        source_file_hash: required_hash(members, path, "source_file_hash")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        declaration_closure_hash: required_hash(members, path, "declaration_closure_hash")?,
        dependency_edge_hash: required_hash(members, path, "dependency_edge_hash")?,
    })
}

fn parse_name_array(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<Name>> {
    let values = required_array(members, path, field)?;
    validate_declaration_promotion_resource_count(
        path,
        field,
        values.len(),
        DECLARATION_PROMOTION_V1_MAX_FAMILY_MEMBERS,
    )?;
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(Name::from_dotted).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    None,
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn parse_optional_hash(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<Option<PackageHash>> {
    match value {
        JsonValue::Null => Ok(None),
        JsonValue::String(value) => parse_package_hash(value, path)
            .map(Some)
            .map_err(|_| PackageArtifactError::invalid_hash_format(path, value)),
        _ => Err(PackageArtifactError::wrong_type(
            path,
            None,
            "string or null",
            value.kind().as_str(),
        )),
    }
}

fn plan_json(plan: &MathlibPromotionPlanV2) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&plan.schema)),
        ("promotion_id", hash_json(plan.promotion_id)),
        ("source", source_json(&plan.source)),
        ("target_baseline", target_json(&plan.target_baseline)),
        ("governance", governance_json(&plan.governance)),
        ("selection", selection_json(&plan.selection)),
        (
            "dependency_mappings",
            json_array(plan.dependency_mappings.iter().map(mapping_json).collect()),
        ),
        (
            "equivalent_sources",
            json_array(
                plan.equivalent_sources
                    .iter()
                    .map(equivalent_json)
                    .collect(),
            ),
        ),
        ("requested_maturity", json_string(&plan.requested_maturity)),
        ("plan_hash", hash_json(plan.plan_hash)),
        ("proof_evidence", json_bool(plan.proof_evidence)),
    ])
}

pub(crate) fn source_json(value: &PromotionPackageSnapshot) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        ("manifest_file_hash", hash_json(value.manifest_file_hash)),
        ("lock_file_hash", hash_json(value.lock_file_hash)),
        (
            "axiom_report_file_hash",
            hash_json(value.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(value.theorem_index_file_hash),
        ),
    ])
}
pub(crate) fn target_json(value: &PromotionTargetSnapshotV2) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        (
            "planned_version",
            json_string(value.planned_version.as_str()),
        ),
        ("manifest_file_hash", hash_json(value.manifest_file_hash)),
        ("lock_file_hash", hash_json(value.lock_file_hash)),
        (
            "axiom_report_file_hash",
            hash_json(value.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(value.theorem_index_file_hash),
        ),
        (
            "verified_export_summary_file_hash",
            hash_json(value.verified_export_summary_file_hash),
        ),
        (
            "publish_plan_file_hash",
            hash_json(value.publish_plan_file_hash),
        ),
        ("registry_file_hash", hash_json(value.registry_file_hash)),
    ])
}
fn governance_json(value: &PromotionGovernanceV2) -> String {
    json_object_in_order(vec![
        ("request_path", json_string(value.request_path.as_str())),
        ("request_schema", json_string(&value.request_schema)),
        ("request_file_hash", hash_json(value.request_file_hash)),
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
fn selection_json(value: &PromotionSelectionV2) -> String {
    json_object_in_order(vec![
        (
            "source_module",
            json_string(&value.source_module.as_dotted()),
        ),
        (
            "target_module",
            json_string(&value.target_module.as_dotted()),
        ),
        ("source_path", json_string(value.source_path.as_str())),
        ("source_file_hash", hash_json(value.source_file_hash)),
        ("meta_path", json_string(value.meta_path.as_str())),
        ("meta_file_hash", hash_json(value.meta_file_hash)),
        ("replay_path", json_string(value.replay_path.as_str())),
        ("replay_file_hash", hash_json(value.replay_file_hash)),
        (
            "certificate_path",
            json_string(value.certificate_path.as_str()),
        ),
        (
            "certificate_file_hash",
            hash_json(value.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
        ("axiom_report_hash", hash_json(value.axiom_report_hash)),
        (
            "roots",
            json_array(value.roots.iter().map(root_json).collect()),
        ),
        (
            "materialized_declarations",
            json_array(
                value
                    .materialized_declarations
                    .iter()
                    .map(declaration_json)
                    .collect(),
            ),
        ),
        (
            "generated_exports",
            json_array(value.generated_exports.iter().map(identity_json).collect()),
        ),
        (
            "declaration_closure_hash",
            hash_json(value.declaration_closure_hash),
        ),
    ])
}
pub(crate) fn root_json(value: &PromotionPlanV2Root) -> String {
    json_object_in_order(vec![
        (
            "requested_name",
            json_string(&value.requested_name.as_dotted()),
        ),
        ("owner_name", json_string(&value.owner_name.as_dotted())),
        ("kind", json_string(&value.kind)),
    ])
}
pub(crate) fn declaration_json(value: &PromotionPlanV2Declaration) -> String {
    json_object_in_order(vec![
        ("role", json_string(&value.role)),
        ("source_name", json_string(&value.source_name.as_dotted())),
        ("target_name", json_string(&value.target_name.as_dotted())),
        ("certificate_kind", json_string(&value.certificate_kind)),
        ("human_kind", json_string(&value.human_kind)),
        ("source_decl_index", json_u64(value.source_decl_index)),
        ("decl_interface_hash", hash_json(value.decl_interface_hash)),
        (
            "decl_certificate_hash",
            hash_json(value.decl_certificate_hash),
        ),
        ("type_hash", hash_json(value.type_hash)),
        (
            "body_hash",
            value.body_hash.map_or_else(|| "null".to_owned(), hash_json),
        ),
        ("item_span", span_json(value.item_span)),
        ("family_owner", json_string(&value.family_owner.as_dotted())),
        (
            "family_members",
            json_array(
                value
                    .family_members
                    .iter()
                    .map(|name| json_string(&name.as_dotted()))
                    .collect(),
            ),
        ),
        (
            "generated_exports",
            json_array(value.generated_exports.iter().map(identity_json).collect()),
        ),
        (
            "direct_dependencies",
            json_array(
                value
                    .direct_dependencies
                    .iter()
                    .map(identity_json)
                    .collect(),
            ),
        ),
    ])
}
fn span_json(value: PromotionSourceSpan) -> String {
    json_object_in_order(vec![
        ("start", json_u64(value.start)),
        ("end", json_u64(value.end)),
    ])
}
pub(crate) fn identity_json(value: &PromotionPlanV2Identity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&value.module.as_dotted())),
        ("name", json_string(&value.name.as_dotted())),
        ("kind", json_string(&value.kind)),
        ("decl_interface_hash", hash_json(value.decl_interface_hash)),
    ])
}
pub(crate) fn mapping_json(value: &PromotionPlanV2DependencyMapping) -> String {
    json_object_in_order(vec![
        ("source", endpoint_json(&value.source)),
        ("target", endpoint_json(&value.target)),
        (
            "declaration_name",
            json_string(&value.declaration_name.as_dotted()),
        ),
        (
            "source_decl_interface_hash",
            hash_json(value.source_decl_interface_hash),
        ),
        (
            "target_decl_interface_hash",
            hash_json(value.target_decl_interface_hash),
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
    ])
}
fn endpoint_json(value: &PromotionPlanEndpoint) -> String {
    json_object_in_order(vec![
        ("origin", json_string(value.origin.as_str())),
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        ("module", json_string(&value.module.as_dotted())),
    ])
}
pub(crate) fn equivalent_json(value: &PromotionPlanV2EquivalentSource) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        (
            "source_module",
            json_string(&value.source_module.as_dotted()),
        ),
        ("source_file_hash", hash_json(value.source_file_hash)),
        (
            "certificate_file_hash",
            hash_json(value.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
        (
            "declaration_closure_hash",
            hash_json(value.declaration_closure_hash),
        ),
        (
            "dependency_edge_hash",
            hash_json(value.dependency_edge_hash),
        ),
    ])
}

fn domain_hash(domain: &[u8], bytes: &[u8]) -> PackageHash {
    let mut input = Vec::with_capacity(domain.len() + bytes.len());
    input.extend_from_slice(domain);
    input.extend_from_slice(bytes);
    package_file_hash(&input)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(byte: u8) -> PackageHash {
        PackageHash::from([byte; 32])
    }
    fn fixture() -> MathlibPromotionPlanV2 {
        let identity = PromotionPlanV2Identity {
            module: Name::from_dotted("Proofs.Big"),
            name: Name::from_dotted("chosen"),
            kind: "theorem".to_owned(),
            decl_interface_hash: hash(20),
        };
        let mut plan = MathlibPromotionPlanV2 {
            schema: MATHLIB_PROMOTION_PLAN_V2_SCHEMA.to_owned(),
            promotion_id: PackageHash::new([0; 32]),
            source: PromotionPackageSnapshot {
                package: PackageId::new("npa-project-fixture"),
                version: PackageVersion::new("0.1.0"),
                manifest_file_hash: hash(1),
                lock_file_hash: hash(2),
                axiom_report_file_hash: hash(3),
                theorem_index_file_hash: hash(4),
            },
            target_baseline: PromotionTargetSnapshotV2 {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.0"),
                planned_version: PackageVersion::new("0.3.0"),
                manifest_file_hash: hash(5),
                lock_file_hash: hash(6),
                axiom_report_file_hash: hash(7),
                theorem_index_file_hash: hash(8),
                verified_export_summary_file_hash: hash(9),
                publish_plan_file_hash: hash(10),
                registry_file_hash: hash(11),
            },
            governance: PromotionGovernanceV2 {
                request_path: PackagePath::new("promotion/fixture.selection.json"),
                request_schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
                request_file_hash: hash(12),
                catalog_policy_file_hash: hash(13),
                namespace_policy_file_hash: hash(14),
            },
            selection: PromotionSelectionV2 {
                source_module: Name::from_dotted("Proofs.Big"),
                target_module: Name::from_dotted("Mathlib.Small"),
                source_path: PackagePath::new("Proofs/Big/source.npa"),
                source_file_hash: hash(15),
                meta_path: PackagePath::new("Proofs/Big/meta.json"),
                meta_file_hash: hash(16),
                replay_path: PackagePath::new("Proofs/Big/proof-replay.json"),
                replay_file_hash: hash(17),
                certificate_path: PackagePath::new("Proofs/Big/certificate.npcert"),
                certificate_file_hash: hash(18),
                certificate_hash: hash(19),
                export_hash: hash(21),
                axiom_report_hash: hash(22),
                roots: vec![PromotionPlanV2Root {
                    requested_name: Name::from_dotted("chosen"),
                    owner_name: Name::from_dotted("chosen"),
                    kind: "theorem".to_owned(),
                }],
                materialized_declarations: vec![PromotionPlanV2Declaration {
                    role: "root".to_owned(),
                    source_name: Name::from_dotted("chosen"),
                    target_name: Name::from_dotted("chosen"),
                    certificate_kind: "theorem".to_owned(),
                    human_kind: "theorem".to_owned(),
                    source_decl_index: 0,
                    decl_interface_hash: hash(20),
                    decl_certificate_hash: hash(23),
                    type_hash: hash(24),
                    body_hash: None,
                    item_span: PromotionSourceSpan { start: 1, end: 10 },
                    family_owner: Name::from_dotted("chosen"),
                    family_members: vec![Name::from_dotted("chosen")],
                    generated_exports: Vec::new(),
                    direct_dependencies: Vec::new(),
                }],
                generated_exports: Vec::new(),
                declaration_closure_hash: hash(25),
            },
            dependency_mappings: Vec::new(),
            equivalent_sources: Vec::new(),
            requested_maturity: "verified".to_owned(),
            plan_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        let _ = identity;
        plan.finalize().unwrap();
        plan
    }

    #[test]
    fn plan_v2_round_trips_and_detects_hash_tampering() {
        let plan = fixture();
        let json = plan.canonical_json().unwrap();
        assert_eq!(parse_mathlib_promotion_plan_v2_json(&json).unwrap(), plan);
        let tampered = json.replace(
            &crate::format_package_hash(&plan.plan_hash),
            &crate::format_package_hash(&hash(99)),
        );
        assert!(parse_mathlib_promotion_plan_v2_json(&tampered).is_err());
    }

    #[test]
    fn plan_v2_rejects_invalid_embedded_kinds_names_and_target_namespace() {
        let mut root_kind = fixture();
        root_kind.selection.roots[0].kind = "lemma".to_owned();
        assert!(root_kind.finalize().is_err());

        let mut owner_kind = fixture();
        owner_kind.selection.roots[0].kind = "definition".to_owned();
        assert!(owner_kind.finalize().is_err());

        let mut requested_member = fixture();
        requested_member.selection.roots[0].requested_name = Name::from_dotted("not_a_member");
        assert!(requested_member.finalize().is_err());

        let mut dependency_kind = fixture();
        dependency_kind.selection.materialized_declarations[0]
            .direct_dependencies
            .push(PromotionPlanV2Identity {
                module: Name::from_dotted("Proofs.Dependency"),
                name: Name::from_dotted("helper"),
                kind: "opaque-proof".to_owned(),
                decl_interface_hash: hash(30),
            });
        assert!(dependency_kind.finalize().is_err());

        let mut family_name = fixture();
        family_name.selection.materialized_declarations[0].family_members =
            vec![Name::from_dotted("not..canonical")];
        assert!(family_name.finalize().is_err());

        let mut family_inventory = fixture();
        family_inventory.selection.materialized_declarations[0].family_members =
            vec![Name::from_dotted("unrelated")];
        assert!(family_inventory.finalize().is_err());

        let mut target_namespace = fixture();
        target_namespace.selection.target_module = Name::from_dotted("Private.Small");
        assert!(target_namespace.finalize().is_err());

        let mut equivalent_edge = fixture();
        equivalent_edge
            .equivalent_sources
            .push(PromotionPlanV2EquivalentSource {
                package: PackageId::new("source-alias"),
                version: equivalent_edge.source.version.clone(),
                source_module: equivalent_edge.selection.source_module.clone(),
                source_file_hash: equivalent_edge.selection.source_file_hash,
                certificate_file_hash: equivalent_edge.selection.certificate_file_hash,
                certificate_hash: equivalent_edge.selection.certificate_hash,
                export_hash: equivalent_edge.selection.export_hash,
                declaration_closure_hash: equivalent_edge.selection.declaration_closure_hash,
                dependency_edge_hash: hash(99),
            });
        assert!(equivalent_edge.finalize().is_err());
    }

    #[test]
    fn plan_v2_binds_local_mapping_endpoints_to_snapshots() {
        let mut plan = fixture();
        plan.dependency_mappings
            .push(PromotionPlanV2DependencyMapping {
                source: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: plan.source.package.clone(),
                    version: plan.source.version.clone(),
                    module: Name::from_dotted("Proofs.Dependency"),
                },
                target: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: plan.target_baseline.package.clone(),
                    version: plan.target_baseline.version.clone(),
                    module: Name::from_dotted("Mathlib.Dependency"),
                },
                declaration_name: Name::from_dotted("helper"),
                source_decl_interface_hash: hash(30),
                target_decl_interface_hash: hash(30),
                target_certificate_file_hash: hash(31),
                target_certificate_hash: hash(32),
                target_export_hash: hash(33),
            });
        assert!(plan.finalize().is_ok());

        let mut wrong_source = plan.clone();
        wrong_source.dependency_mappings[0].source.version = PackageVersion::new("0.1.1");
        assert!(wrong_source.finalize().is_err());

        let mut future_target = plan.clone();
        future_target.dependency_mappings[0].target.version =
            future_target.target_baseline.planned_version.clone();
        assert!(future_target.finalize().is_err());

        let mut new_target = plan;
        new_target.dependency_mappings[0].target.module =
            new_target.selection.target_module.clone();
        assert!(new_target.finalize().is_err());
    }

    #[test]
    fn plan_v2_rejects_source_local_axiom_externalization() {
        let mut plan = fixture();
        let source_module = Name::from_dotted("Proofs.LocalAxioms");
        let declaration_name = Name::from_dotted("choice");
        plan.selection.materialized_declarations[0]
            .direct_dependencies
            .push(PromotionPlanV2Identity {
                module: source_module.clone(),
                name: declaration_name.clone(),
                kind: "axiom".to_owned(),
                decl_interface_hash: hash(30),
            });
        plan.dependency_mappings
            .push(PromotionPlanV2DependencyMapping {
                source: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: plan.source.package.clone(),
                    version: plan.source.version.clone(),
                    module: source_module,
                },
                target: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: PackageId::new("npa-std"),
                    version: PackageVersion::new("0.1.0"),
                    module: Name::from_dotted("Std.Logic.Classical"),
                },
                declaration_name,
                source_decl_interface_hash: hash(30),
                target_decl_interface_hash: hash(30),
                target_certificate_file_hash: hash(31),
                target_certificate_hash: hash(32),
                target_export_hash: hash(33),
            });

        let error = plan.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("source_axiom"));
        assert_eq!(error.actual_value.as_deref(), Some("choice"));

        plan.dependency_mappings[0].source.origin = PackageArtifactOrigin::External;
        plan.dependency_mappings[0].source.package = PackageId::new("source-external");
        assert!(plan.finalize().is_ok());
    }

    #[test]
    fn plan_v2_enforces_closure_resource_limits_before_canonicalization() {
        let mut plan = fixture();
        plan.selection.roots =
            vec![plan.selection.roots[0].clone(); DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS + 1];

        let route_error = mathlib_declaration_promotion_route_id_v2(
            &plan.source.package,
            &plan.source.version,
            &plan.selection.source_module,
            &plan.selection.target_module,
            &plan.selection.roots,
            plan.selection.declaration_closure_hash,
        )
        .unwrap_err();
        assert_eq!(route_error.field.as_deref(), Some("roots"));

        let error = plan.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("roots"));
        let actual = (DECLARATION_PROMOTION_V1_MAX_REQUESTED_ROOTS + 1).to_string();
        assert_eq!(error.actual_value.as_deref(), Some(actual.as_str()));

        let mut plan = fixture();
        let equivalent = PromotionPlanV2EquivalentSource {
            package: PackageId::new("source-alias"),
            version: plan.source.version.clone(),
            source_module: plan.selection.source_module.clone(),
            source_file_hash: plan.selection.source_file_hash,
            certificate_file_hash: plan.selection.certificate_file_hash,
            certificate_hash: plan.selection.certificate_hash,
            export_hash: plan.selection.export_hash,
            declaration_closure_hash: plan.selection.declaration_closure_hash,
            dependency_edge_hash: promotion_plan_v2_dependency_edge_hash(
                &plan.selection.materialized_declarations,
                &plan.dependency_mappings,
            )
            .unwrap(),
        };
        plan.equivalent_sources =
            vec![equivalent; DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES + 1];
        let error = plan.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("equivalent_sources"));
        let actual = (DECLARATION_PROMOTION_V1_MAX_EQUIVALENT_SOURCES + 1).to_string();
        assert_eq!(error.actual_value.as_deref(), Some(actual.as_str()));
    }

    #[test]
    fn plan_v2_bounds_equivalent_sources_before_typed_conversion() {
        let mut plan = fixture();
        plan.equivalent_sources
            .push(PromotionPlanV2EquivalentSource {
                package: PackageId::new("source-alias"),
                version: plan.source.version.clone(),
                source_module: plan.selection.source_module.clone(),
                source_file_hash: plan.selection.source_file_hash,
                certificate_file_hash: plan.selection.certificate_file_hash,
                certificate_hash: plan.selection.certificate_hash,
                export_hash: plan.selection.export_hash,
                declaration_closure_hash: plan.selection.declaration_closure_hash,
                dependency_edge_hash: promotion_plan_v2_dependency_edge_hash(
                    &plan.selection.materialized_declarations,
                    &plan.dependency_mappings,
                )
                .unwrap(),
            });
        plan.finalize().unwrap();
        let value = parse_artifact_json(&plan.canonical_json().unwrap()).unwrap();
        let members = expect_object(&value, "$").unwrap();
        let error = parse_array_bounded(members, "$", "equivalent_sources", 0, parse_equivalent)
            .unwrap_err();
        assert_eq!(error.field.as_deref(), Some("equivalent_sources"));
        assert_eq!(error.actual_value.as_deref(), Some("1"));
    }

    #[test]
    fn promotion_artifacts_bound_distinct_loaded_source_modules() {
        let plan = fixture();
        let mut declaration = plan.selection.materialized_declarations[0].clone();
        declaration.direct_dependencies = (0..DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES - 1)
            .map(|index| PromotionPlanV2Identity {
                module: Name::from_dotted(format!("Proofs.Dependency{index:04}")),
                name: Name::from_dotted("helper"),
                kind: "theorem".to_owned(),
                decl_interface_hash: hash(30),
            })
            .collect();
        validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            std::slice::from_ref(&declaration),
            Some(&plan.selection.generated_exports),
            &plan.dependency_mappings,
            "selection",
        )
        .unwrap();

        declaration
            .direct_dependencies
            .push(PromotionPlanV2Identity {
                module: Name::from_dotted("Proofs.Dependency4095"),
                name: Name::from_dotted("helper"),
                kind: "theorem".to_owned(),
                decl_interface_hash: hash(30),
            });
        let error = validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            std::slice::from_ref(&declaration),
            Some(&plan.selection.generated_exports),
            &plan.dependency_mappings,
            "selection",
        )
        .unwrap_err();
        assert_eq!(error.field.as_deref(), Some("loaded_modules"));
        let actual = (DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES + 1).to_string();
        assert_eq!(error.actual_value.as_deref(), Some(actual.as_str()));

        let mut generated_exports = (0..DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES - 1)
            .map(|index| PromotionPlanV2Identity {
                module: Name::from_dotted(format!("Proofs.Generated{index:04}")),
                name: Name::from_dotted("generated"),
                kind: "constructor".to_owned(),
                decl_interface_hash: hash(31),
            })
            .collect::<Vec<_>>();
        validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            &plan.selection.materialized_declarations,
            Some(&generated_exports),
            &plan.dependency_mappings,
            "selection",
        )
        .unwrap();

        generated_exports.push(PromotionPlanV2Identity {
            module: Name::from_dotted("Proofs.Generated4095"),
            name: Name::from_dotted("generated"),
            kind: "constructor".to_owned(),
            decl_interface_hash: hash(31),
        });
        let error = validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            &plan.selection.materialized_declarations,
            Some(&generated_exports),
            &plan.dependency_mappings,
            "selection",
        )
        .unwrap_err();
        assert_eq!(error.field.as_deref(), Some("loaded_modules"));
        assert_eq!(error.actual_value.as_deref(), Some(actual.as_str()));
    }

    #[test]
    fn promotion_artifacts_bound_distinct_loaded_target_modules() {
        let plan = fixture();
        let mut mappings = (0..DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES - 1)
            .map(|index| PromotionPlanV2DependencyMapping {
                source: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: plan.source.package.clone(),
                    version: plan.source.version.clone(),
                    module: plan.selection.source_module.clone(),
                },
                target: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: plan.target_baseline.package.clone(),
                    version: plan.target_baseline.version.clone(),
                    module: Name::from_dotted(format!("Mathlib.Dependency{index:04}")),
                },
                declaration_name: Name::from_dotted("helper"),
                source_decl_interface_hash: hash(30),
                target_decl_interface_hash: hash(30),
                target_certificate_file_hash: hash(31),
                target_certificate_hash: hash(32),
                target_export_hash: hash(33),
            })
            .collect::<Vec<_>>();
        validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            &plan.selection.materialized_declarations,
            Some(&plan.selection.generated_exports),
            &mappings,
            "selection",
        )
        .unwrap();

        mappings.push(PromotionPlanV2DependencyMapping {
            source: PromotionPlanEndpoint {
                origin: PackageArtifactOrigin::Local,
                package: plan.source.package.clone(),
                version: plan.source.version.clone(),
                module: plan.selection.source_module.clone(),
            },
            target: PromotionPlanEndpoint {
                origin: PackageArtifactOrigin::External,
                package: plan.target_baseline.package.clone(),
                version: plan.target_baseline.version.clone(),
                module: Name::from_dotted("Mathlib.Dependency4095"),
            },
            declaration_name: Name::from_dotted("helper"),
            source_decl_interface_hash: hash(30),
            target_decl_interface_hash: hash(30),
            target_certificate_file_hash: hash(31),
            target_certificate_hash: hash(32),
            target_export_hash: hash(33),
        });
        let error = validate_declaration_promotion_resource_limits(
            Some(&plan.selection.source_module),
            Some(&plan.selection.target_module),
            Some(&plan.selection.roots),
            &plan.selection.materialized_declarations,
            Some(&plan.selection.generated_exports),
            &mappings,
            "selection",
        )
        .unwrap_err();
        assert_eq!(error.field.as_deref(), Some("loaded_modules"));
        let actual = (DECLARATION_PROMOTION_V1_MAX_LOADED_MODULES + 1).to_string();
        assert_eq!(error.actual_value.as_deref(), Some(actual.as_str()));
    }

    #[test]
    fn closure_relationships_reject_ambiguous_generated_export_ownership() {
        let plan = fixture();
        let generated = PromotionPlanV2Identity {
            module: plan.selection.source_module.clone(),
            name: Name::from_dotted("generated"),
            kind: "constructor".to_owned(),
            decl_interface_hash: hash(30),
        };
        let family_members = vec![
            Name::from_dotted("chosen"),
            generated.name.clone(),
            Name::from_dotted("helper"),
        ];
        let mut owner = plan.selection.materialized_declarations[0].clone();
        owner.family_members.clone_from(&family_members);
        owner.generated_exports = vec![generated.clone()];
        let mut second_owner = owner.clone();
        second_owner.source_name = Name::from_dotted("helper");
        second_owner.target_name = second_owner.source_name.clone();
        second_owner.source_decl_index = 1;

        let error = validate_promotion_plan_v2_closure_relationships(
            &plan.selection.source_module,
            &plan.selection.roots,
            &[owner, second_owner],
            "selection",
        )
        .unwrap_err();
        assert_eq!(
            error.actual_value.as_deref(),
            Some("one declaration owner per generated export")
        );
    }
}

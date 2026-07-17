//! Canonical package-generic plan for namespace-only promotion to npa-mathlib.
//!
//! A plan binds validated package and governance snapshots. It is deterministic
//! workflow input and explicitly not proof evidence.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        parse_artifact_json, reject_unknown_fields, required_array, required_bool, required_hash,
        required_name, required_path, required_string, required_u64, required_value,
        validate_declaration_name, validate_module_name, validate_package_identity,
        PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    promotion_registry::{PromotionSourceModule, PromotionSourceOrigin},
    schema::MATHLIB_PROMOTION_PLAN_SCHEMA,
};

const PLAN_FIELDS: &[&str] = &[
    "schema",
    "promotion_id",
    "source",
    "target_baseline",
    "governance",
    "selected_modules",
    "dependency_mappings",
    "equivalent_sources",
    "compatibility_alias",
    "plan_hash",
    "proof_evidence",
];
const SNAPSHOT_FIELDS: &[&str] = &[
    "package",
    "version",
    "manifest_file_hash",
    "lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
];
const TARGET_SNAPSHOT_FIELDS: &[&str] = &[
    "package",
    "version",
    "planned_version",
    "manifest_file_hash",
    "lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
];
const GOVERNANCE_FIELDS: &[&str] = &[
    "acceptance_policy_id",
    "acceptance_policy_version",
    "acceptance_policy_file_hash",
    "source_acceptance_path",
    "source_acceptance_schema",
    "source_acceptance_file_hash",
    "transport_policy_id",
    "transport_policy_version",
    "transport_policy_file_hash",
    "mapping_path",
    "mapping_schema",
    "mapping_file_hash",
    "registry_file_hash",
];
const SELECTED_FIELDS: &[&str] = &[
    "source_module",
    "target_module",
    "source_path",
    "source_file_hash",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
    "axiom_report_hash",
    "imports",
    "exports",
    "theorems",
];
const EXPORT_FIELDS: &[&str] = &["kind", "source_name", "target_name", "decl_interface_hash"];
const THEOREM_FIELDS: &[&str] = &["source_name", "target_name", "statement_hash"];
const DEPENDENCY_FIELDS: &[&str] = &[
    "role",
    "source",
    "target",
    "declaration_mapping",
    "renames",
    "target_certificate_file_hash",
    "target_certificate_hash",
    "target_export_hash",
];
const ENDPOINT_FIELDS: &[&str] = &["origin", "package", "version", "module"];
const RENAME_FIELDS: &[&str] = &["source", "target"];
const SOURCE_FIELDS: &[&str] = &["package", "version", "modules"];
const SOURCE_MODULE_FIELDS: &[&str] = &[
    "module",
    "source_file_hash",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
];

const PLAN_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-PLAN-v1\0";
const ROUTE_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-ROUTE-v1\0";

/// Exact source generated-artifact snapshot bound by a plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionPackageSnapshot {
    /// Package ID.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Manifest bytes hash.
    pub manifest_file_hash: PackageHash,
    /// Checked package-lock bytes hash.
    pub lock_file_hash: PackageHash,
    /// Checked axiom-report bytes hash.
    pub axiom_report_file_hash: PackageHash,
    /// Checked theorem-index bytes hash.
    pub theorem_index_file_hash: PackageHash,
}

/// Clean target snapshot plus the explicitly planned release version.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTargetSnapshot {
    /// Target package ID.
    pub package: PackageId,
    /// Baseline package version.
    pub version: PackageVersion,
    /// Planned target version.
    pub planned_version: PackageVersion,
    /// Manifest bytes hash.
    pub manifest_file_hash: PackageHash,
    /// Checked package-lock bytes hash.
    pub lock_file_hash: PackageHash,
    /// Checked axiom-report bytes hash.
    pub axiom_report_file_hash: PackageHash,
    /// Checked theorem-index bytes hash.
    pub theorem_index_file_hash: PackageHash,
}

/// Governance files and schemas bound by the plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionGovernance {
    /// L2 acceptance policy ID.
    pub acceptance_policy_id: String,
    /// L2 acceptance policy version.
    pub acceptance_policy_version: u64,
    /// L2 acceptance policy file hash.
    pub acceptance_policy_file_hash: PackageHash,
    /// Source-root-relative acceptance ledger path.
    pub source_acceptance_path: PackagePath,
    /// Acceptance ledger schema.
    pub source_acceptance_schema: String,
    /// Acceptance ledger file hash.
    pub source_acceptance_file_hash: PackageHash,
    /// Transport policy ID.
    pub transport_policy_id: String,
    /// Transport policy version.
    pub transport_policy_version: u64,
    /// Transport policy file hash.
    pub transport_policy_file_hash: PackageHash,
    /// Source-root-relative mapping path.
    pub mapping_path: PackagePath,
    /// Mapping request schema.
    pub mapping_schema: String,
    /// Mapping request file hash.
    pub mapping_file_hash: PackageHash,
    /// Clean-baseline registry file hash.
    pub registry_file_hash: PackageHash,
}

/// One complete exported global identity.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionPlanExport {
    /// Stable export kind.
    pub kind: String,
    /// Source global name.
    pub source_name: Name,
    /// Target global name.
    pub target_name: Name,
    /// Decoded certificate declaration-interface hash.
    pub decl_interface_hash: PackageHash,
}

/// One selected theorem statement identity.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionPlanTheorem {
    /// Source theorem name.
    pub source_name: Name,
    /// Target theorem name.
    pub target_name: Name,
    /// Checked statement hash.
    pub statement_hash: PackageHash,
}

/// One selected module and its source artifact inventory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionPlanSelectedModule {
    /// Source module.
    pub source_module: Name,
    /// Public target module.
    pub target_module: Name,
    /// Source package-relative source path.
    pub source_path: PackagePath,
    /// Source bytes hash.
    pub source_file_hash: PackageHash,
    /// Certificate file bytes hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical export hash.
    pub export_hash: PackageHash,
    /// Canonical axiom-report hash.
    pub axiom_report_hash: PackageHash,
    /// Direct imports.
    pub imports: Vec<Name>,
    /// Complete exported-global inventory.
    pub exports: Vec<PromotionPlanExport>,
    /// Checked theorem statement inventory.
    pub theorems: Vec<PromotionPlanTheorem>,
}

/// Complete module endpoint retained from a transport request.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionPlanEndpoint {
    /// Local or external origin.
    pub origin: PackageArtifactOrigin,
    /// Package ID.
    pub package: PackageId,
    /// Package version.
    pub version: PackageVersion,
    /// Module name.
    pub module: Name,
}

/// One explicit dependency declaration rename.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PromotionPlanRename {
    /// Source global.
    pub source: Name,
    /// Target global.
    pub target: Name,
}

/// One existing-target dependency mapping.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionPlanDependencyMapping {
    /// Always `dependency`.
    pub role: String,
    /// Complete source endpoint.
    pub source: PromotionPlanEndpoint,
    /// Complete target endpoint.
    pub target: PromotionPlanEndpoint,
    /// Always `same-name-except-explicit`.
    pub declaration_mapping: String,
    /// Empty in materializer v1.
    pub renames: Vec<PromotionPlanRename>,
    /// Baseline target certificate file hash.
    pub target_certificate_file_hash: PackageHash,
    /// Baseline target certificate hash.
    pub target_certificate_hash: PackageHash,
    /// Baseline target export hash.
    pub target_export_hash: PackageHash,
}

/// Canonical generic mathlib promotion plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MathlibPromotionPlan {
    /// Schema identifier.
    pub schema: String,
    /// Stable route ID, independent of planned release version.
    pub promotion_id: PackageHash,
    /// Source package snapshot.
    pub source: PromotionPackageSnapshot,
    /// Clean target snapshot and planned version.
    pub target_baseline: PromotionTargetSnapshot,
    /// Governance identities.
    pub governance: PromotionGovernance,
    /// Complete selected closure.
    pub selected_modules: Vec<PromotionPlanSelectedModule>,
    /// Existing target dependency mappings.
    pub dependency_mappings: Vec<PromotionPlanDependencyMapping>,
    /// Artifact-identical source aliases.
    pub equivalent_sources: Vec<PromotionSourceOrigin>,
    /// Always `none` in v1.
    pub compatibility_alias: String,
    /// Domain-separated plan self-hash.
    pub plan_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl MathlibPromotionPlan {
    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_mathlib_promotion_plan(self)?;
        Ok(format!("{}\n", plan_json(self)))
    }

    /// Recompute stable route ID and plan self-hash after construction.
    pub fn finalize(&mut self) -> PackageArtifactResult<()> {
        self.promotion_id = mathlib_promotion_route_id(self)?;
        self.plan_hash = mathlib_promotion_plan_hash(self)?;
        Ok(())
    }
}

/// Parse and validate strict canonical promotion-plan JSON.
pub fn parse_mathlib_promotion_plan_json(
    source: &str,
) -> PackageArtifactResult<MathlibPromotionPlan> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, PLAN_FIELDS)?;
    let plan = MathlibPromotionPlan {
        schema: required_string(members, "$", "schema")?,
        promotion_id: required_hash(members, "$", "promotion_id")?,
        source: parse_snapshot(required_value(members, "$", "source")?, "source")?,
        target_baseline: parse_target_snapshot(
            required_value(members, "$", "target_baseline")?,
            "target_baseline",
        )?,
        governance: parse_governance(required_value(members, "$", "governance")?, "governance")?,
        selected_modules: required_array(members, "$", "selected_modules")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_selected(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        dependency_mappings: required_array(members, "$", "dependency_mappings")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_dependency(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        equivalent_sources: required_array(members, "$", "equivalent_sources")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_source(value, &format!("equivalent_sources[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        compatibility_alias: required_string(members, "$", "compatibility_alias")?,
        plan_hash: required_hash(members, "$", "plan_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_mathlib_promotion_plan(&plan)?;
    if source != plan.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "mathlib promotion plan JSON bytes",
        ));
    }
    Ok(plan)
}

/// Compute the plan self-hash.
pub fn mathlib_promotion_plan_hash(
    plan: &MathlibPromotionPlan,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = plan.clone();
    copy.plan_hash = zero_hash();
    validate_plan_shape(&copy, false, true)?;
    domain_hash(PLAN_DOMAIN, plan_json(&copy).as_bytes())
}

/// Compute the stable route ID while excluding the planned target version.
pub fn mathlib_promotion_route_id(
    plan: &MathlibPromotionPlan,
) -> PackageArtifactResult<PackageHash> {
    validate_plan_shape(plan, false, false)?;
    let route = json_object_in_order(vec![
        ("source_package", json_string(plan.source.package.as_str())),
        ("source_version", json_string(plan.source.version.as_str())),
        (
            "target_package",
            json_string(plan.target_baseline.package.as_str()),
        ),
        (
            "selected_modules",
            json_array(
                plan.selected_modules
                    .iter()
                    .map(|module| {
                        json_object_in_order(vec![
                            (
                                "source_module",
                                json_string(&module.source_module.as_dotted()),
                            ),
                            (
                                "target_module",
                                json_string(&module.target_module.as_dotted()),
                            ),
                            ("source_file_hash", hash_json(module.source_file_hash)),
                            (
                                "certificate_file_hash",
                                hash_json(module.certificate_file_hash),
                            ),
                            ("certificate_hash", hash_json(module.certificate_hash)),
                            ("export_hash", hash_json(module.export_hash)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ]);
    domain_hash(ROUTE_DOMAIN, route.as_bytes())
}

/// Validate all plan shape, ordering, route ID, and self-hash invariants.
pub fn validate_mathlib_promotion_plan(plan: &MathlibPromotionPlan) -> PackageArtifactResult<()> {
    validate_plan_shape(plan, true, true)
}

fn validate_plan_shape(
    plan: &MathlibPromotionPlan,
    check_hash: bool,
    check_id: bool,
) -> PackageArtifactResult<()> {
    if plan.schema != MATHLIB_PROMOTION_PLAN_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            MATHLIB_PROMOTION_PLAN_SCHEMA,
            &plan.schema,
        ));
    }
    validate_package_identity(&plan.source.package, &plan.source.version)?;
    validate_package_identity(&plan.target_baseline.package, &plan.target_baseline.version)?;
    validate_package_identity(
        &plan.target_baseline.package,
        &plan.target_baseline.planned_version,
    )?;
    if plan.target_baseline.package.as_str() != "npa-mathlib"
        || version_tuple(&plan.target_baseline.planned_version)?
            <= version_tuple(&plan.target_baseline.version)?
        || plan.selected_modules.is_empty()
        || plan.compatibility_alias != "none"
        || plan.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "promotion_plan",
            "strict v1 plan with increasing npa-mathlib target",
            "mismatch",
        ));
    }
    validate_governance(&plan.governance)?;
    let mut previous_selected = None;
    let mut source_names = BTreeSet::new();
    let mut target_names = BTreeSet::new();
    for (index, module) in plan.selected_modules.iter().enumerate() {
        validate_selected(module, index)?;
        let key = (
            module.source_module.as_dotted(),
            module.target_module.as_dotted(),
        );
        if previous_selected.as_ref().is_some_and(|old| old >= &key)
            || !source_names.insert(module.source_module.clone())
            || !target_names.insert(module.target_module.clone())
        {
            return Err(PackageArtifactError::non_canonical(
                "selected_modules",
                "strict one-to-one selected module order",
            ));
        }
        previous_selected = Some(key);
    }
    let mut previous_dependency = None;
    for (index, mapping) in plan.dependency_mappings.iter().enumerate() {
        validate_dependency(mapping, index)?;
        if mapping.target.package != plan.target_baseline.package
            || mapping.target.version != plan.target_baseline.planned_version
        {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("dependency_mappings[{index}].target"),
                "target",
                "planned target package and version",
                "mismatch",
            ));
        }
        let key = (&mapping.source, &mapping.target);
        if previous_dependency.is_some_and(|old| old >= key) {
            return Err(PackageArtifactError::non_canonical(
                "dependency_mappings",
                "strict endpoint order",
            ));
        }
        previous_dependency = Some(key);
    }
    let selected_hashes = plan
        .selected_modules
        .iter()
        .map(|module| {
            (
                module.source_file_hash,
                module.certificate_file_hash,
                module.certificate_hash,
                module.export_hash,
            )
        })
        .collect::<Vec<_>>();
    let mut previous_alias = None;
    for (index, alias) in plan.equivalent_sources.iter().enumerate() {
        validate_source(alias, &format!("equivalent_sources[{index}]"))?;
        let key = (
            alias.package.as_str().to_owned(),
            alias.version.as_str().to_owned(),
        );
        if key
            == (
                plan.source.package.as_str().to_owned(),
                plan.source.version.as_str().to_owned(),
            )
            || previous_alias.as_ref().is_some_and(|old| old >= &key)
            || alias.modules.len() != selected_hashes.len()
            || alias.modules.iter().map(|module| &module.module).ne(plan
                .selected_modules
                .iter()
                .map(|module| &module.source_module))
            || alias
                .modules
                .iter()
                .map(source_module_hashes)
                .ne(selected_hashes.iter().copied())
        {
            return Err(PackageArtifactError::non_canonical(
                "equivalent_sources",
                "sorted complete artifact-identical aliases",
            ));
        }
        previous_alias = Some(key);
    }
    if check_id && plan.promotion_id != mathlib_promotion_route_id(plan)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "promotion_id",
            "promotion_id",
            "derived stable promotion route ID",
            "mismatch",
        ));
    }
    if check_hash && plan.plan_hash != mathlib_promotion_plan_hash(plan)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "plan_hash",
            "plan_hash",
            "matching promotion plan self-hash",
            "mismatch",
        ));
    }
    Ok(())
}

fn validate_governance(value: &PromotionGovernance) -> PackageArtifactResult<()> {
    if value.acceptance_policy_version == 0
        || value.transport_policy_version == 0
        || value.source_acceptance_schema != "npa.l2_acceptance.v2"
        || value.mapping_schema != "npa.l2_namespace_transport_request.v1"
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "governance",
            "schemas",
            "current L2 acceptance and transport request schemas",
            "mismatch",
        ));
    }
    for (path, field) in [
        (&value.source_acceptance_path, "source_acceptance_path"),
        (&value.mapping_path, "mapping_path"),
    ] {
        validate_package_path(path, field)
            .map_err(|_| PackageArtifactError::invalid_path(field, path.as_str()))?;
    }
    Ok(())
}

fn validate_selected(
    module: &PromotionPlanSelectedModule,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("selected_modules[{index}]");
    validate_module_name(&module.source_module, format!("{path}.source_module"))?;
    validate_module_name(&module.target_module, format!("{path}.target_module"))?;
    validate_package_path(&module.source_path, format!("{path}.source_path"))
        .map_err(|_| PackageArtifactError::invalid_path(&path, module.source_path.as_str()))?;
    let mut previous_import = None;
    for import in &module.imports {
        validate_module_name(import, format!("{path}.imports"))?;
        if previous_import.as_ref().is_some_and(|old| old >= import) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.imports"),
                "strict import order",
            ));
        }
        previous_import = Some(import.clone());
    }
    let mut previous_export = None;
    let mut export_names = BTreeSet::new();
    let mut theorem_export_names = BTreeSet::new();
    for export in &module.exports {
        validate_declaration_name(&export.source_name, format!("{path}.exports.source_name"))?;
        validate_declaration_name(&export.target_name, format!("{path}.exports.target_name"))?;
        if !matches!(
            export.kind.as_str(),
            "axiom" | "definition" | "theorem" | "inductive" | "constructor" | "recursor"
        ) || export.source_name != export.target_name
            || !export_names.insert(export.source_name.clone())
            || previous_export.as_ref().is_some_and(|old| old >= export)
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.exports"),
                "same-name strict export order",
            ));
        }
        if export.kind == "theorem" {
            theorem_export_names.insert(export.source_name.clone());
        }
        previous_export = Some(export.clone());
    }
    let mut previous_theorem = None;
    for theorem in &module.theorems {
        validate_declaration_name(&theorem.source_name, format!("{path}.theorems.source_name"))?;
        validate_declaration_name(&theorem.target_name, format!("{path}.theorems.target_name"))?;
        if theorem.source_name != theorem.target_name
            || previous_theorem.as_ref().is_some_and(|old| old >= theorem)
        {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.theorems"),
                "same-name strict theorem order",
            ));
        }
        previous_theorem = Some(theorem.clone());
    }
    if theorem_export_names
        != module
            .theorems
            .iter()
            .map(|theorem| theorem.source_name.clone())
            .collect()
    {
        return Err(PackageArtifactError::non_canonical(
            format!("{path}.theorems"),
            "complete theorem export inventory",
        ));
    }
    Ok(())
}

fn validate_dependency(
    mapping: &PromotionPlanDependencyMapping,
    index: usize,
) -> PackageArtifactResult<()> {
    let path = format!("dependency_mappings[{index}]");
    validate_endpoint(&mapping.source, &format!("{path}.source"))?;
    validate_endpoint(&mapping.target, &format!("{path}.target"))?;
    if mapping.role != "dependency"
        || mapping.target.origin != PackageArtifactOrigin::Local
        || mapping.declaration_mapping != "same-name-except-explicit"
        || !mapping.renames.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            &path,
            "mapping",
            "dependency same-name mapping with empty renames",
            "mismatch",
        ));
    }
    Ok(())
}

fn validate_endpoint(endpoint: &PromotionPlanEndpoint, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&endpoint.package, &endpoint.version)?;
    validate_module_name(&endpoint.module, format!("{path}.module"))
}

fn parse_snapshot(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionPackageSnapshot> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SNAPSHOT_FIELDS)?;
    Ok(PromotionPackageSnapshot {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        lock_file_hash: required_hash(members, path, "lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
    })
}

fn parse_target_snapshot(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionTargetSnapshot> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TARGET_SNAPSHOT_FIELDS)?;
    Ok(PromotionTargetSnapshot {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        planned_version: PackageVersion::new(required_string(members, path, "planned_version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        lock_file_hash: required_hash(members, path, "lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
    })
}

fn parse_governance(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionGovernance> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GOVERNANCE_FIELDS)?;
    Ok(PromotionGovernance {
        acceptance_policy_id: required_string(members, path, "acceptance_policy_id")?,
        acceptance_policy_version: required_u64(members, path, "acceptance_policy_version")?,
        acceptance_policy_file_hash: required_hash(members, path, "acceptance_policy_file_hash")?,
        source_acceptance_path: required_path(members, path, "source_acceptance_path")?,
        source_acceptance_schema: required_string(members, path, "source_acceptance_schema")?,
        source_acceptance_file_hash: required_hash(members, path, "source_acceptance_file_hash")?,
        transport_policy_id: required_string(members, path, "transport_policy_id")?,
        transport_policy_version: required_u64(members, path, "transport_policy_version")?,
        transport_policy_file_hash: required_hash(members, path, "transport_policy_file_hash")?,
        mapping_path: required_path(members, path, "mapping_path")?,
        mapping_schema: required_string(members, path, "mapping_schema")?,
        mapping_file_hash: required_hash(members, path, "mapping_file_hash")?,
        registry_file_hash: required_hash(members, path, "registry_file_hash")?,
    })
}

fn parse_selected(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<PromotionPlanSelectedModule> {
    let path = format!("selected_modules[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, SELECTED_FIELDS)?;
    Ok(PromotionPlanSelectedModule {
        source_module: required_name(members, &path, "source_module")?,
        target_module: required_name(members, &path, "target_module")?,
        source_path: required_path(members, &path, "source_path")?,
        source_file_hash: required_hash(members, &path, "source_file_hash")?,
        certificate_file_hash: required_hash(members, &path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        axiom_report_hash: required_hash(members, &path, "axiom_report_hash")?,
        imports: required_array(members, &path, "imports")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_name_value(value, &format!("{path}.imports[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        exports: required_array(members, &path, "exports")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_export(value, &format!("{path}.exports[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        theorems: required_array(members, &path, "theorems")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_theorem(value, &format!("{path}.theorems[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_name_value(value: &JsonValue, path: &str) -> PackageArtifactResult<Name> {
    value.string_value().map(Name::from_dotted).ok_or_else(|| {
        PackageArtifactError::wrong_type(path, None, "string", value.kind().as_str())
    })
}

fn parse_export(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionPlanExport> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, EXPORT_FIELDS)?;
    Ok(PromotionPlanExport {
        kind: required_string(members, path, "kind")?,
        source_name: required_name(members, path, "source_name")?,
        target_name: required_name(members, path, "target_name")?,
        decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
    })
}

fn parse_theorem(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionPlanTheorem> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, THEOREM_FIELDS)?;
    Ok(PromotionPlanTheorem {
        source_name: required_name(members, path, "source_name")?,
        target_name: required_name(members, path, "target_name")?,
        statement_hash: required_hash(members, path, "statement_hash")?,
    })
}

fn parse_dependency(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<PromotionPlanDependencyMapping> {
    let path = format!("dependency_mappings[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, DEPENDENCY_FIELDS)?;
    Ok(PromotionPlanDependencyMapping {
        role: required_string(members, &path, "role")?,
        source: parse_endpoint(
            required_value(members, &path, "source")?,
            &format!("{path}.source"),
        )?,
        target: parse_endpoint(
            required_value(members, &path, "target")?,
            &format!("{path}.target"),
        )?,
        declaration_mapping: required_string(members, &path, "declaration_mapping")?,
        renames: required_array(members, &path, "renames")?
            .iter()
            .enumerate()
            .map(|(i, value)| parse_rename(value, &format!("{path}.renames[{i}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        target_certificate_file_hash: required_hash(
            members,
            &path,
            "target_certificate_file_hash",
        )?,
        target_certificate_hash: required_hash(members, &path, "target_certificate_hash")?,
        target_export_hash: required_hash(members, &path, "target_export_hash")?,
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

fn parse_rename(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionPlanRename> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, RENAME_FIELDS)?;
    Ok(PromotionPlanRename {
        source: required_name(members, path, "source")?,
        target: required_name(members, path, "target")?,
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
            .map(|(i, value)| parse_source_module(value, &format!("{path}.modules[{i}]")))
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

fn plan_json(plan: &MathlibPromotionPlan) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&plan.schema)),
        ("promotion_id", hash_json(plan.promotion_id)),
        ("source", snapshot_json(&plan.source)),
        (
            "target_baseline",
            target_snapshot_json(&plan.target_baseline),
        ),
        ("governance", governance_json(&plan.governance)),
        (
            "selected_modules",
            json_array(plan.selected_modules.iter().map(selected_json).collect()),
        ),
        (
            "dependency_mappings",
            json_array(
                plan.dependency_mappings
                    .iter()
                    .map(dependency_json)
                    .collect(),
            ),
        ),
        (
            "equivalent_sources",
            json_array(plan.equivalent_sources.iter().map(source_json).collect()),
        ),
        (
            "compatibility_alias",
            json_string(&plan.compatibility_alias),
        ),
        ("plan_hash", hash_json(plan.plan_hash)),
        ("proof_evidence", json_bool(plan.proof_evidence)),
    ])
}

fn snapshot_json(value: &PromotionPackageSnapshot) -> String {
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

fn target_snapshot_json(value: &PromotionTargetSnapshot) -> String {
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
    ])
}

fn governance_json(value: &PromotionGovernance) -> String {
    json_object_in_order(vec![
        (
            "acceptance_policy_id",
            json_string(&value.acceptance_policy_id),
        ),
        (
            "acceptance_policy_version",
            value.acceptance_policy_version.to_string(),
        ),
        (
            "acceptance_policy_file_hash",
            hash_json(value.acceptance_policy_file_hash),
        ),
        (
            "source_acceptance_path",
            json_string(value.source_acceptance_path.as_str()),
        ),
        (
            "source_acceptance_schema",
            json_string(&value.source_acceptance_schema),
        ),
        (
            "source_acceptance_file_hash",
            hash_json(value.source_acceptance_file_hash),
        ),
        (
            "transport_policy_id",
            json_string(&value.transport_policy_id),
        ),
        (
            "transport_policy_version",
            value.transport_policy_version.to_string(),
        ),
        (
            "transport_policy_file_hash",
            hash_json(value.transport_policy_file_hash),
        ),
        ("mapping_path", json_string(value.mapping_path.as_str())),
        ("mapping_schema", json_string(&value.mapping_schema)),
        ("mapping_file_hash", hash_json(value.mapping_file_hash)),
        ("registry_file_hash", hash_json(value.registry_file_hash)),
    ])
}

fn selected_json(value: &PromotionPlanSelectedModule) -> String {
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
        (
            "certificate_file_hash",
            hash_json(value.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
        ("axiom_report_hash", hash_json(value.axiom_report_hash)),
        (
            "imports",
            json_array(
                value
                    .imports
                    .iter()
                    .map(|name| json_string(&name.as_dotted()))
                    .collect(),
            ),
        ),
        (
            "exports",
            json_array(value.exports.iter().map(export_json).collect()),
        ),
        (
            "theorems",
            json_array(value.theorems.iter().map(theorem_json).collect()),
        ),
    ])
}

fn export_json(value: &PromotionPlanExport) -> String {
    json_object_in_order(vec![
        ("kind", json_string(&value.kind)),
        ("source_name", json_string(&value.source_name.as_dotted())),
        ("target_name", json_string(&value.target_name.as_dotted())),
        ("decl_interface_hash", hash_json(value.decl_interface_hash)),
    ])
}

fn theorem_json(value: &PromotionPlanTheorem) -> String {
    json_object_in_order(vec![
        ("source_name", json_string(&value.source_name.as_dotted())),
        ("target_name", json_string(&value.target_name.as_dotted())),
        ("statement_hash", hash_json(value.statement_hash)),
    ])
}

fn dependency_json(value: &PromotionPlanDependencyMapping) -> String {
    json_object_in_order(vec![
        ("role", json_string(&value.role)),
        ("source", endpoint_json(&value.source)),
        ("target", endpoint_json(&value.target)),
        (
            "declaration_mapping",
            json_string(&value.declaration_mapping),
        ),
        (
            "renames",
            json_array(value.renames.iter().map(rename_json).collect()),
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

fn rename_json(value: &PromotionPlanRename) -> String {
    json_object_in_order(vec![
        ("source", json_string(&value.source.as_dotted())),
        ("target", json_string(&value.target.as_dotted())),
    ])
}

fn source_json(value: &PromotionSourceOrigin) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        (
            "modules",
            json_array(value.modules.iter().map(source_module_json).collect()),
        ),
    ])
}

fn source_module_json(value: &PromotionSourceModule) -> String {
    json_object_in_order(vec![
        ("module", json_string(&value.module.as_dotted())),
        ("source_file_hash", hash_json(value.source_file_hash)),
        (
            "certificate_file_hash",
            hash_json(value.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
    ])
}

fn validate_source(source: &PromotionSourceOrigin, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&source.package, &source.version)?;
    if source.modules.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "modules",
            "nonempty modules",
            "empty",
        ));
    }
    let mut previous = None;
    for module in &source.modules {
        validate_module_name(&module.module, format!("{path}.modules.module"))?;
        if previous.as_ref().is_some_and(|old| old >= module) {
            return Err(PackageArtifactError::non_canonical(
                format!("{path}.modules"),
                "strict module order",
            ));
        }
        previous = Some(module.clone());
    }
    Ok(())
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

fn domain_hash(domain: &[u8], payload: &[u8]) -> PackageArtifactResult<PackageHash> {
    let mut bytes = Vec::with_capacity(domain.len() + payload.len());
    bytes.extend_from_slice(domain);
    bytes.extend_from_slice(payload);
    Ok(package_file_hash(&bytes))
}

const fn zero_hash() -> PackageHash {
    PackageHash::new([0; 32])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_plan() -> MathlibPromotionPlan {
        let hash = |value: &str| package_file_hash(value.as_bytes());
        MathlibPromotionPlan {
            schema: MATHLIB_PROMOTION_PLAN_SCHEMA.to_owned(),
            promotion_id: zero_hash(),
            source: PromotionPackageSnapshot {
                package: PackageId::new("npa-project-example-proofs"),
                version: PackageVersion::new("0.1.0"),
                manifest_file_hash: hash("source-manifest"),
                lock_file_hash: hash("source-lock"),
                axiom_report_file_hash: hash("source-axioms"),
                theorem_index_file_hash: hash("source-index"),
            },
            target_baseline: PromotionTargetSnapshot {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.1"),
                planned_version: PackageVersion::new("0.2.2"),
                manifest_file_hash: hash("target-manifest"),
                lock_file_hash: hash("target-lock"),
                axiom_report_file_hash: hash("target-axioms"),
                theorem_index_file_hash: hash("target-index"),
            },
            governance: PromotionGovernance {
                acceptance_policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
                acceptance_policy_version: 2,
                acceptance_policy_file_hash: hash("acceptance-policy"),
                source_acceptance_path: PackagePath::new("l2-acceptance.json"),
                source_acceptance_schema: "npa.l2_acceptance.v2".to_owned(),
                source_acceptance_file_hash: hash("acceptance"),
                transport_policy_id: "finitefield-org.npa-mathlib.l2-namespace-transport"
                    .to_owned(),
                transport_policy_version: 1,
                transport_policy_file_hash: hash("transport-policy"),
                mapping_path: PackagePath::new("promotion/example/mapping.json"),
                mapping_schema: "npa.l2_namespace_transport_request.v1".to_owned(),
                mapping_file_hash: hash("mapping"),
                registry_file_hash: hash("registry"),
            },
            selected_modules: vec![PromotionPlanSelectedModule {
                source_module: Name::from_dotted("Proofs.Ai.Example.Basic"),
                target_module: Name::from_dotted("Mathlib.Example.Basic"),
                source_path: PackagePath::new("Proofs/Ai/Example/Basic/source.npa"),
                source_file_hash: hash("source"),
                certificate_file_hash: hash("cert-file"),
                certificate_hash: hash("cert"),
                export_hash: hash("export"),
                axiom_report_hash: hash("axioms"),
                imports: Vec::new(),
                exports: Vec::new(),
                theorems: Vec::new(),
            }],
            dependency_mappings: Vec::new(),
            equivalent_sources: Vec::new(),
            compatibility_alias: "none".to_owned(),
            plan_hash: zero_hash(),
            proof_evidence: false,
        }
    }

    #[test]
    fn plan_round_trips_and_route_ignores_planned_release_version() {
        let mut plan = sample_plan();
        plan.finalize().unwrap();
        assert_eq!(
            crate::format_package_hash(&plan.promotion_id),
            "sha256:4db4b008060e7161b5fc7cdd204f20c47000d6a101a540717a80000edc3ef752"
        );
        assert_eq!(
            crate::format_package_hash(&plan.plan_hash),
            "sha256:d4dbf3a47122bfaffa7c07aed6c4728041ac4886e5508c3c9ce0088ba488cae6"
        );
        let promotion_id = plan.promotion_id;
        let json = plan.canonical_json().unwrap();
        assert_eq!(parse_mathlib_promotion_plan_json(&json).unwrap(), plan);

        plan.target_baseline.planned_version = PackageVersion::new("0.2.3");
        plan.finalize().unwrap();
        assert_eq!(plan.promotion_id, promotion_id);
    }
}

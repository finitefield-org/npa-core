//! Canonical operator intent for declaration-level mathlib promotion.
//!
//! A request is source-owned governance metadata and never proof evidence.

use std::collections::BTreeSet;

use npa_cert::{DeclarationClosureLimits, Name, DECLARATION_CLOSURE_LIMITS_V1};

use crate::{
    artifacts::{
        expect_object, json_array, json_bool, json_object_in_order, json_string,
        parse_artifact_json, reject_unknown_fields, required_array, required_bool, required_name,
        required_string, required_value, validate_declaration_name, validate_module_name,
        validate_package_identity, PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    promotion_plan::PromotionPlanEndpoint,
    schema::MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA,
};

const REQUEST_FIELDS: &[&str] = &[
    "schema",
    "source",
    "target",
    "source_module",
    "target_module",
    "roots",
    "dependency_mappings",
    "requested_maturity",
    "proof_evidence",
];
const SOURCE_FIELDS: &[&str] = &["package", "version"];
const TARGET_FIELDS: &[&str] = &["package", "baseline_version", "planned_version"];
const ROOT_FIELDS: &[&str] = &["source_name", "target_name", "kind"];
const MAPPING_FIELDS: &[&str] = &["source", "target", "declaration_mapping"];
const ENDPOINT_FIELDS: &[&str] = &["origin", "package", "version", "module"];

/// Source package identity named by a declaration request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationPromotionSource {
    /// Exact source package ID.
    pub package: PackageId,
    /// Exact source package version.
    pub version: PackageVersion,
}

/// Target baseline and planned release identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationPromotionTarget {
    /// Target package ID, exactly `npa-mathlib` in v1.
    pub package: PackageId,
    /// Clean target baseline version.
    pub baseline_version: PackageVersion,
    /// Strictly greater planned target version.
    pub planned_version: PackageVersion,
}

/// Operator-facing requested root kind.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeclarationPromotionRootKind {
    /// Opaque theorem root.
    Theorem,
    /// Definition root.
    Definition,
    /// Inductive root.
    Inductive,
    /// Typeclass root.
    Class,
    /// Typeclass instance root.
    Instance,
}

impl DeclarationPromotionRootKind {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Theorem => "theorem",
            Self::Definition => "definition",
            Self::Inductive => "inductive",
            Self::Class => "class",
            Self::Instance => "instance",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "theorem" => Ok(Self::Theorem),
            "definition" => Ok(Self::Definition),
            "inductive" => Ok(Self::Inductive),
            "class" => Ok(Self::Class),
            "instance" => Ok(Self::Instance),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "kind",
                "theorem, definition, inductive, class, or instance",
                value,
            )),
        }
    }
}

/// One exact requested declaration root.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DeclarationPromotionRoot {
    /// Source declaration or generated export name.
    pub source_name: Name,
    /// Target declaration name, equal to source in v1.
    pub target_name: Name,
    /// Expected Human owner kind.
    pub kind: DeclarationPromotionRootKind,
}

/// One explicit module endpoint mapping used at declaration granularity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationPromotionDependencyMapping {
    /// Exact source endpoint.
    pub source: PromotionPlanEndpoint,
    /// Exact target endpoint.
    pub target: PromotionPlanEndpoint,
    /// Exactly `same-name` in v1.
    pub declaration_mapping: String,
}

/// Canonical declaration-level selection request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationPromotionRequest {
    /// Exact schema identifier.
    pub schema: String,
    /// Source package identity.
    pub source: DeclarationPromotionSource,
    /// Target package versions.
    pub target: DeclarationPromotionTarget,
    /// One local source module.
    pub source_module: Name,
    /// One new public target module.
    pub target_module: Name,
    /// Strictly sorted unique requested roots.
    pub roots: Vec<DeclarationPromotionRoot>,
    /// Strictly sorted unique dependency mappings.
    pub dependency_mappings: Vec<DeclarationPromotionDependencyMapping>,
    /// Exactly `verified`.
    pub requested_maturity: String,
    /// Always false.
    pub proof_evidence: bool,
}

impl DeclarationPromotionRequest {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_declaration_promotion_request(self)?;
        Ok(format!("{}\n", request_json(self)))
    }
}

/// Parse and validate strict canonical declaration request JSON.
pub fn parse_declaration_promotion_request_json(
    source: &str,
) -> PackageArtifactResult<DeclarationPromotionRequest> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, REQUEST_FIELDS)?;
    let roots = required_array_bounded(
        members,
        "$",
        "roots",
        DECLARATION_CLOSURE_LIMITS_V1.requested_roots,
    )?;
    let dependency_mappings = required_array_bounded(
        members,
        "$",
        "dependency_mappings",
        DECLARATION_CLOSURE_LIMITS_V1.dependency_edges,
    )?;
    let request = DeclarationPromotionRequest {
        schema: required_string(members, "$", "schema")?,
        source: parse_source(required_value(members, "$", "source")?, "source")?,
        target: parse_target(required_value(members, "$", "target")?, "target")?,
        source_module: required_name(members, "$", "source_module")?,
        target_module: required_name(members, "$", "target_module")?,
        roots: roots
            .iter()
            .enumerate()
            .map(|(index, value)| parse_root(value, &format!("roots[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        dependency_mappings: dependency_mappings
            .iter()
            .enumerate()
            .map(|(index, value)| parse_mapping(value, &format!("dependency_mappings[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        requested_maturity: required_string(members, "$", "requested_maturity")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_declaration_promotion_request(&request)?;
    if source != request.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "declaration promotion request JSON bytes",
        ));
    }
    Ok(request)
}

/// Validate request schema, ordering, names, versions, and fixed v1 values.
pub fn validate_declaration_promotion_request(
    request: &DeclarationPromotionRequest,
) -> PackageArtifactResult<()> {
    if request.schema != MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA
        || request.requested_maturity != "verified"
        || request.proof_evidence
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "schema_or_fixed_value",
            "declaration request v1, verified, proof_evidence false",
            "mismatch",
        ));
    }
    validate_package_identity(&request.source.package, &request.source.version)?;
    validate_package_identity(&request.target.package, &request.target.baseline_version)?;
    validate_package_identity(&request.target.package, &request.target.planned_version)?;
    if request.target.package.as_str() != "npa-mathlib"
        || !version_is_strictly_greater(
            &request.target.planned_version,
            &request.target.baseline_version,
        )
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "target",
            "version",
            "npa-mathlib and strictly greater planned version",
            request.target.planned_version.as_str(),
        ));
    }
    validate_module_name(&request.source_module, "source_module")?;
    validate_module_name(&request.target_module, "target_module")?;
    if !request.target_module.as_dotted().starts_with("Mathlib.") {
        return Err(PackageArtifactError::invalid_enum_value(
            "target_module",
            "module",
            "new Mathlib.* module",
            request.target_module.as_dotted(),
        ));
    }
    validate_request_resource_limits(request, DECLARATION_CLOSURE_LIMITS_V1)?;
    if request.roots.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "roots",
            "length",
            "1..=4096",
            request.roots.len().to_string(),
        ));
    }
    let mut previous_root: Option<&DeclarationPromotionRoot> = None;
    for root in &request.roots {
        validate_declaration_name(&root.source_name, "roots.source_name")?;
        validate_declaration_name(&root.target_name, "roots.target_name")?;
        if root.source_name != root.target_name || previous_root.is_some_and(|old| old >= root) {
            return Err(PackageArtifactError::non_canonical(
                "roots",
                "strictly sorted unique same-name roots",
            ));
        }
        previous_root = Some(root);
    }
    let mut previous_mapping: Option<&DeclarationPromotionDependencyMapping> = None;
    let mut unique = BTreeSet::new();
    for mapping in &request.dependency_mappings {
        validate_endpoint(&mapping.source, "dependency_mappings.source")?;
        validate_endpoint(&mapping.target, "dependency_mappings.target")?;
        if mapping.declaration_mapping != "same-name"
            || (mapping.source.origin == PackageArtifactOrigin::Local
                && (mapping.source.package != request.source.package
                    || mapping.source.version != request.source.version))
            || (mapping.target.origin == PackageArtifactOrigin::Local
                && (mapping.target.package != request.target.package
                    || mapping.target.version != request.target.baseline_version))
            || mapping.target.module == request.target_module
            || !unique.insert((&mapping.source, &mapping.target))
            || previous_mapping
                .is_some_and(|old| mapping_sort_key(old) >= mapping_sort_key(mapping))
        {
            return Err(PackageArtifactError::non_canonical(
                "dependency_mappings",
                "strict endpoint order with same-name mapping",
            ));
        }
        previous_mapping = Some(mapping);
    }
    Ok(())
}

fn validate_request_resource_limits(
    request: &DeclarationPromotionRequest,
    limits: DeclarationClosureLimits,
) -> PackageArtifactResult<()> {
    validate_resource_count("$", "roots", request.roots.len(), limits.requested_roots)?;
    validate_resource_count(
        "$",
        "dependency_mappings",
        request.dependency_mappings.len(),
        limits.dependency_edges,
    )?;

    let mut source_modules = BTreeSet::from([&request.source_module]);
    let mut target_modules = BTreeSet::from([&request.target_module]);
    for mapping in &request.dependency_mappings {
        source_modules.insert(&mapping.source.module);
        validate_resource_count(
            "$",
            "loaded_modules",
            source_modules.len(),
            limits.loaded_modules,
        )?;
        target_modules.insert(&mapping.target.module);
        validate_resource_count(
            "$",
            "loaded_modules",
            target_modules.len(),
            limits.loaded_modules,
        )?;
    }
    Ok(())
}

fn required_array_bounded<'a>(
    members: &'a [crate::json::JsonMember],
    path: &str,
    field: &str,
    maximum: usize,
) -> PackageArtifactResult<&'a [JsonValue]> {
    let values = required_array(members, path, field)?;
    validate_resource_count(path, field, values.len(), maximum)?;
    Ok(values)
}

fn validate_resource_count(
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

fn validate_endpoint(endpoint: &PromotionPlanEndpoint, path: &str) -> PackageArtifactResult<()> {
    validate_package_identity(&endpoint.package, &endpoint.version)?;
    validate_module_name(&endpoint.module, format!("{path}.module"))
}

fn mapping_sort_key(
    mapping: &DeclarationPromotionDependencyMapping,
) -> (&PromotionPlanEndpoint, &PromotionPlanEndpoint) {
    (&mapping.source, &mapping.target)
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

fn parse_source(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<DeclarationPromotionSource> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_FIELDS)?;
    Ok(DeclarationPromotionSource {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
    })
}

fn parse_target(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<DeclarationPromotionTarget> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TARGET_FIELDS)?;
    Ok(DeclarationPromotionTarget {
        package: PackageId::new(required_string(members, path, "package")?),
        baseline_version: PackageVersion::new(required_string(members, path, "baseline_version")?),
        planned_version: PackageVersion::new(required_string(members, path, "planned_version")?),
    })
}

fn parse_root(value: &JsonValue, path: &str) -> PackageArtifactResult<DeclarationPromotionRoot> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ROOT_FIELDS)?;
    Ok(DeclarationPromotionRoot {
        source_name: required_name(members, path, "source_name")?,
        target_name: required_name(members, path, "target_name")?,
        kind: DeclarationPromotionRootKind::parse(&required_string(members, path, "kind")?, path)?,
    })
}

fn parse_mapping(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<DeclarationPromotionDependencyMapping> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, MAPPING_FIELDS)?;
    Ok(DeclarationPromotionDependencyMapping {
        source: parse_endpoint(
            required_value(members, path, "source")?,
            &format!("{path}.source"),
        )?,
        target: parse_endpoint(
            required_value(members, path, "target")?,
            &format!("{path}.target"),
        )?,
        declaration_mapping: required_string(members, path, "declaration_mapping")?,
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

fn request_json(request: &DeclarationPromotionRequest) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&request.schema)),
        ("source", source_json(&request.source)),
        ("target", target_json(&request.target)),
        (
            "source_module",
            json_string(&request.source_module.as_dotted()),
        ),
        (
            "target_module",
            json_string(&request.target_module.as_dotted()),
        ),
        (
            "roots",
            json_array(request.roots.iter().map(root_json).collect()),
        ),
        (
            "dependency_mappings",
            json_array(
                request
                    .dependency_mappings
                    .iter()
                    .map(mapping_json)
                    .collect(),
            ),
        ),
        (
            "requested_maturity",
            json_string(&request.requested_maturity),
        ),
        ("proof_evidence", json_bool(request.proof_evidence)),
    ])
}

fn source_json(source: &DeclarationPromotionSource) -> String {
    json_object_in_order(vec![
        ("package", json_string(source.package.as_str())),
        ("version", json_string(source.version.as_str())),
    ])
}

fn target_json(target: &DeclarationPromotionTarget) -> String {
    json_object_in_order(vec![
        ("package", json_string(target.package.as_str())),
        (
            "baseline_version",
            json_string(target.baseline_version.as_str()),
        ),
        (
            "planned_version",
            json_string(target.planned_version.as_str()),
        ),
    ])
}

fn root_json(root: &DeclarationPromotionRoot) -> String {
    json_object_in_order(vec![
        ("source_name", json_string(&root.source_name.as_dotted())),
        ("target_name", json_string(&root.target_name.as_dotted())),
        ("kind", json_string(root.kind.as_str())),
    ])
}

fn mapping_json(mapping: &DeclarationPromotionDependencyMapping) -> String {
    json_object_in_order(vec![
        ("source", endpoint_json(&mapping.source)),
        ("target", endpoint_json(&mapping.target)),
        (
            "declaration_mapping",
            json_string(&mapping.declaration_mapping),
        ),
    ])
}

fn endpoint_json(endpoint: &PromotionPlanEndpoint) -> String {
    json_object_in_order(vec![
        ("origin", json_string(endpoint.origin.as_str())),
        ("package", json_string(endpoint.package.as_str())),
        ("version", json_string(endpoint.version.as_str())),
        ("module", json_string(&endpoint.module.as_dotted())),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request() -> DeclarationPromotionRequest {
        DeclarationPromotionRequest {
            schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
            source: DeclarationPromotionSource {
                package: PackageId::new("npa-project-fixture"),
                version: PackageVersion::new("0.1.0"),
            },
            target: DeclarationPromotionTarget {
                package: PackageId::new("npa-mathlib"),
                baseline_version: PackageVersion::new("0.2.9"),
                planned_version: PackageVersion::new("0.2.10"),
            },
            source_module: Name::from_dotted("Proofs.Large"),
            target_module: Name::from_dotted("Mathlib.Small"),
            roots: vec![
                DeclarationPromotionRoot {
                    source_name: Name::from_dotted("first"),
                    target_name: Name::from_dotted("first"),
                    kind: DeclarationPromotionRootKind::Theorem,
                },
                DeclarationPromotionRoot {
                    source_name: Name::from_dotted("second"),
                    target_name: Name::from_dotted("second"),
                    kind: DeclarationPromotionRootKind::Definition,
                },
            ],
            dependency_mappings: Vec::new(),
            requested_maturity: "verified".to_owned(),
            proof_evidence: false,
        }
    }

    #[test]
    fn request_round_trips_and_uses_numeric_version_order() {
        let request = request();
        let json = request.canonical_json().unwrap();
        assert_eq!(
            parse_declaration_promotion_request_json(&json).unwrap(),
            request
        );
        assert!(json.contains("\"planned_version\":\"0.2.10\""));
    }

    #[test]
    fn request_rejects_unknown_fields_unsorted_roots_and_noncanonical_bytes() {
        let request = request();
        let json = request.canonical_json().unwrap();
        assert!(parse_declaration_promotion_request_json(&json.replace(
            "\"proof_evidence\":false",
            "\"unknown\":0,\"proof_evidence\":false"
        ))
        .is_err());
        let mut unsorted = request.clone();
        unsorted.roots.reverse();
        assert!(unsorted.canonical_json().is_err());
        assert!(parse_declaration_promotion_request_json(&format!(" {json}")).is_err());
    }

    #[test]
    fn request_resource_limits_precede_typed_array_conversion() {
        let request = request();
        let value = parse_artifact_json(&request_json(&request)).unwrap();
        let members = expect_object(&value, "$").unwrap();
        let error = required_array_bounded(members, "$", "roots", 1).unwrap_err();
        assert_eq!(error.field.as_deref(), Some("roots"));
        assert_eq!(error.actual_value.as_deref(), Some("2"));

        let mut over_roots = request.clone();
        over_roots.roots =
            vec![over_roots.roots[0].clone(); DECLARATION_CLOSURE_LIMITS_V1.requested_roots + 1];
        let error = validate_declaration_promotion_request(&over_roots).unwrap_err();
        assert_eq!(error.field.as_deref(), Some("roots"));
    }

    #[test]
    fn request_bounds_mapping_edges_and_loaded_modules() {
        let mut request = request();
        request
            .dependency_mappings
            .push(DeclarationPromotionDependencyMapping {
                source: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: request.source.package.clone(),
                    version: request.source.version.clone(),
                    module: Name::from_dotted("Proofs.Dependency"),
                },
                target: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: PackageId::new("npa-std"),
                    version: PackageVersion::new("0.2.0"),
                    module: Name::from_dotted("Std.Dependency"),
                },
                declaration_mapping: "same-name".to_owned(),
            });

        let edge_error = validate_request_resource_limits(
            &request,
            DeclarationClosureLimits {
                dependency_edges: 0,
                ..DeclarationClosureLimits::default()
            },
        )
        .unwrap_err();
        assert_eq!(edge_error.field.as_deref(), Some("dependency_mappings"));

        let module_error = validate_request_resource_limits(
            &request,
            DeclarationClosureLimits {
                loaded_modules: 1,
                ..DeclarationClosureLimits::default()
            },
        )
        .unwrap_err();
        assert_eq!(module_error.field.as_deref(), Some("loaded_modules"));
        assert_eq!(module_error.actual_value.as_deref(), Some("2"));
    }

    #[test]
    fn request_binds_local_mapping_endpoints_to_named_snapshots() {
        let mut request = request();
        request
            .dependency_mappings
            .push(DeclarationPromotionDependencyMapping {
                source: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: request.source.package.clone(),
                    version: request.source.version.clone(),
                    module: Name::from_dotted("Proofs.Dependency"),
                },
                target: PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: request.target.package.clone(),
                    version: request.target.baseline_version.clone(),
                    module: Name::from_dotted("Mathlib.Dependency"),
                },
                declaration_mapping: "same-name".to_owned(),
            });
        assert!(validate_declaration_promotion_request(&request).is_ok());

        let mut wrong_source = request.clone();
        wrong_source.dependency_mappings[0].source.version = PackageVersion::new("0.1.1");
        assert!(validate_declaration_promotion_request(&wrong_source).is_err());

        let mut future_target = request.clone();
        future_target.dependency_mappings[0].target.version =
            future_target.target.planned_version.clone();
        assert!(validate_declaration_promotion_request(&future_target).is_err());

        let mut new_target = request;
        new_target.dependency_mappings[0].target.module = new_target.target_module.clone();
        assert!(validate_declaration_promotion_request(&new_target).is_err());
    }
}

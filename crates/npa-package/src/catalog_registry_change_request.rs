//! Canonical operator request for catalog lifecycle changes.

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        parse_artifact_json, reject_unknown_fields, required_array, required_bool, required_hash,
        required_path, required_string, validate_module_name,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::{JsonMember, JsonValue},
    manifest::PackageVersion,
    path::{validate_package_path, PackagePath},
    schema::MATHLIB_CATALOG_REGISTRY_CHANGE_REQUEST_SCHEMA,
};

const DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-REGISTRY-CHANGE-REQUEST-v1\0";
const REQUEST_FIELDS: &[&str] = &[
    "schema",
    "previous_version",
    "target_version",
    "changes",
    "audit",
    "request_hash",
    "proof_evidence",
];
const CHANGE_FIELDS: &[&str] = &["kind", "old_modules", "new_modules", "explanation"];
const AUDIT_FIELDS: &[&str] = &["path", "file_hash"];
const MAX_CHANGES: usize = 4096;
const MAX_MODULES_PER_CHANGE: usize = 4096;

/// One requested rename, replacement, split, merge, or retirement.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CatalogRegistryRequestedChange {
    /// Lifecycle relation kind.
    pub kind: String,
    /// Existing modules retired by the relation.
    pub old_modules: Vec<Name>,
    /// New modules introduced by the relation.
    pub new_modules: Vec<Name>,
    /// Nonempty operator rationale.
    pub explanation: String,
}

/// Canonical catalog lifecycle change request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogRegistryChangeRequest {
    /// Exact schema identifier.
    pub schema: String,
    /// Older target version.
    pub previous_version: PackageVersion,
    /// Strictly newer target version.
    pub target_version: PackageVersion,
    /// Strictly sorted lifecycle relations.
    pub changes: Vec<CatalogRegistryRequestedChange>,
    /// Audit path.
    pub audit_path: PackagePath,
    /// Audit file hash.
    pub audit_file_hash: PackageHash,
    /// Domain-separated self-hash.
    pub request_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl CatalogRegistryChangeRequest {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_catalog_registry_change_request(self)?;
        Ok(format!("{}\n", request_json(self)))
    }

    /// Recompute the canonical request self-hash.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.request_hash = catalog_registry_change_request_hash(self)?;
        Ok(())
    }
}

/// Parse and validate one strict canonical request.
pub fn parse_catalog_registry_change_request_json(
    source: &str,
) -> PackageArtifactResult<CatalogRegistryChangeRequest> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, REQUEST_FIELDS)?;
    let audit = expect_object(required_value(members, "$", "audit")?, "$.audit")?;
    reject_unknown_fields("$.audit", audit, AUDIT_FIELDS)?;
    let change_values = required_array(members, "$", "changes")?;
    if change_values.len() > MAX_CHANGES {
        return Err(invalid());
    }
    let request = CatalogRegistryChangeRequest {
        schema: required_string(members, "$", "schema")?,
        previous_version: PackageVersion::new(required_string(members, "$", "previous_version")?),
        target_version: PackageVersion::new(required_string(members, "$", "target_version")?),
        changes: change_values
            .iter()
            .enumerate()
            .map(|(index, value)| parse_change(value, &format!("$.changes[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        audit_path: required_path(audit, "$.audit", "path")?,
        audit_file_hash: required_hash(audit, "$.audit", "file_hash")?,
        request_hash: required_hash(members, "$", "request_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_catalog_registry_change_request(&request)?;
    if request.canonical_json()?.as_bytes() != source.as_bytes() {
        return Err(PackageArtifactError::non_canonical("$", "canonical JSON"));
    }
    Ok(request)
}

/// Compute the request self-hash with its hash field zeroed.
pub fn catalog_registry_change_request_hash(
    request: &CatalogRegistryChangeRequest,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = request.clone();
    copy.request_hash = PackageHash::new([0; 32]);
    validate_shape(&copy, false)?;
    let mut bytes = DOMAIN.to_vec();
    bytes.extend_from_slice(request_json(&copy).as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Validate request shape, cardinalities, ordering, paths, and self-hash.
pub fn validate_catalog_registry_change_request(
    request: &CatalogRegistryChangeRequest,
) -> PackageArtifactResult<()> {
    validate_shape(request, true)
}

fn validate_shape(
    request: &CatalogRegistryChangeRequest,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    validate_package_path(&request.audit_path, "$.audit.path").map_err(|_| {
        PackageArtifactError::invalid_path("$.audit.path", request.audit_path.as_str())
    })?;
    if request.schema != MATHLIB_CATALOG_REGISTRY_CHANGE_REQUEST_SCHEMA
        || request.proof_evidence
        || request.changes.is_empty()
        || request.changes.len() > MAX_CHANGES
        || request.changes.windows(2).any(|pair| {
            (&pair[0].kind, &pair[0].old_modules, &pair[0].new_modules)
                >= (&pair[1].kind, &pair[1].old_modules, &pair[1].new_modules)
        })
        || !version_greater(&request.target_version, &request.previous_version)
    {
        return Err(invalid());
    }
    for change in &request.changes {
        if change.explanation.trim().is_empty()
            || change.old_modules.is_empty()
            || change.old_modules.len() > MAX_MODULES_PER_CHANGE
            || change.new_modules.len() > MAX_MODULES_PER_CHANGE
            || !strict(&change.old_modules)
            || !strict(&change.new_modules)
        {
            return Err(invalid());
        }
        let valid = match change.kind.as_str() {
            "rename" | "replacement" => {
                change.old_modules.len() == 1 && change.new_modules.len() == 1
            }
            "split" => change.old_modules.len() == 1 && change.new_modules.len() >= 2,
            "merge" => change.old_modules.len() >= 2 && change.new_modules.len() == 1,
            "retirement" => change.new_modules.is_empty(),
            _ => false,
        };
        if !valid {
            return Err(invalid());
        }
    }
    if check_hash && request.request_hash != catalog_registry_change_request_hash(request)? {
        return Err(invalid());
    }
    Ok(())
}

fn parse_change(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<CatalogRegistryRequestedChange> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CHANGE_FIELDS)?;
    Ok(CatalogRegistryRequestedChange {
        kind: required_string(members, path, "kind")?,
        old_modules: names(members, path, "old_modules")?,
        new_modules: names(members, path, "new_modules")?,
        explanation: required_string(members, path, "explanation")?,
    })
}

fn names(members: &[JsonMember], path: &str, field: &str) -> PackageArtifactResult<Vec<Name>> {
    let values = required_array(members, path, field)?;
    if values.len() > MAX_MODULES_PER_CHANGE {
        return Err(invalid());
    }
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let row_path = format!("{path}.{field}[{index}]");
            let value = value.string_value().ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    &row_path,
                    Some(field.to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })?;
            let name = Name::from_dotted(value);
            validate_module_name(&name, &row_path)?;
            Ok(name)
        })
        .collect()
}

fn request_json(request: &CatalogRegistryChangeRequest) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&request.schema)),
        (
            "previous_version",
            json_string(request.previous_version.as_str()),
        ),
        (
            "target_version",
            json_string(request.target_version.as_str()),
        ),
        (
            "changes",
            json_array(request.changes.iter().map(change_json).collect()),
        ),
        (
            "audit",
            json_object_in_order(vec![
                ("path", json_string(request.audit_path.as_str())),
                ("file_hash", hash_json(request.audit_file_hash)),
            ]),
        ),
        ("request_hash", hash_json(request.request_hash)),
        ("proof_evidence", json_bool(request.proof_evidence)),
    ])
}

fn change_json(change: &CatalogRegistryRequestedChange) -> String {
    json_object_in_order(vec![
        ("kind", json_string(&change.kind)),
        (
            "old_modules",
            json_array(
                change
                    .old_modules
                    .iter()
                    .map(|name| json_string(&name.as_dotted()))
                    .collect(),
            ),
        ),
        (
            "new_modules",
            json_array(
                change
                    .new_modules
                    .iter()
                    .map(|name| json_string(&name.as_dotted()))
                    .collect(),
            ),
        ),
        ("explanation", json_string(&change.explanation)),
    ])
}

fn required_value<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<&'a JsonValue> {
    crate::artifacts::required_value(members, path, field)
}

fn strict<T: Ord>(values: &[T]) -> bool {
    !values.windows(2).any(|pair| pair[0] >= pair[1])
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

fn invalid() -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(
        "$",
        "catalog_registry_change_request",
        "canonical valid lifecycle request",
        "mismatch",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_round_trip_and_hash() {
        let mut request = CatalogRegistryChangeRequest {
            schema: MATHLIB_CATALOG_REGISTRY_CHANGE_REQUEST_SCHEMA.to_owned(),
            previous_version: PackageVersion::new("0.2.4"),
            target_version: PackageVersion::new("0.4.0"),
            changes: vec![CatalogRegistryRequestedChange {
                kind: "replacement".to_owned(),
                old_modules: vec![Name::from_dotted("Mathlib.Old")],
                new_modules: vec![Name::from_dotted("Mathlib.New")],
                explanation: "Use the meaning-first replacement.".to_owned(),
            }],
            audit_path: PackagePath::new("docs/promotion/catalog.md"),
            audit_file_hash: PackageHash::new([1; 32]),
            request_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        request.refresh_hash().unwrap();
        let json = request.canonical_json().unwrap();
        assert_eq!(
            parse_catalog_registry_change_request_json(&json).unwrap(),
            request
        );
    }

    #[test]
    fn parser_rejects_oversized_arrays_before_typed_collection() {
        let change = r#"{"kind":"retirement","old_modules":["Mathlib.Old"],"new_modules":[],"explanation":"retire"}"#;
        let changes = std::iter::repeat_n(change, MAX_CHANGES + 1)
            .collect::<Vec<_>>()
            .join(",");
        let source = format!(
            "{{\"schema\":\"{}\",\"previous_version\":\"0.2.1\",\"target_version\":\"0.2.4\",\"changes\":[{}],\"audit\":{{\"path\":\"docs/promotion/audit.md\",\"file_hash\":\"sha256:{}\"}},\"request_hash\":\"sha256:{}\",\"proof_evidence\":false}}\n",
            MATHLIB_CATALOG_REGISTRY_CHANGE_REQUEST_SCHEMA,
            changes,
            "00".repeat(32),
            "00".repeat(32),
        );
        assert!(parse_catalog_registry_change_request_json(&source).is_err());

        let names = std::iter::repeat_n("\"Mathlib.Old\"", MAX_MODULES_PER_CHANGE + 1)
            .collect::<Vec<_>>()
            .join(",");
        let oversized_names = format!(
            "{{\"kind\":\"merge\",\"old_modules\":[{names}],\"new_modules\":[\"Mathlib.New\"],\"explanation\":\"merge\"}}"
        );
        assert!(parse_change(
            &parse_artifact_json(&oversized_names).unwrap(),
            "$.changes[0]"
        )
        .is_err());
    }
}

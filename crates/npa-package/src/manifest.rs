//! Package manifest parsing entry points and raw accepted input types.

use toml::{Table, Value};

use npa_cert::Name;

use crate::{
    error::{PackageManifestError, PackageManifestResult},
    hash::{parse_package_hash, PackageHash},
    name::PackageId,
    path::PackagePath,
};

/// Exact package version string accepted by `npa.package.v0.1`.
///
/// The grammar is fixed by CLR-01 validation: `MAJOR.MINOR.PATCH`, no leading
/// zeroes except the single digit `0`, and no pre-release or build metadata.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageVersion(pub String);

impl PackageVersion {
    /// Build a package version wrapper from a version string.
    pub fn new(version: impl Into<String>) -> Self {
        Self(version.into())
    }

    /// Return the version string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Accepted `npa.package.v0.1` manifest input shape.
///
/// This is package metadata, not proof evidence. The struct intentionally
/// contains only accepted manifest fields; generated checker verdicts,
/// registry lookups, implicit version resolution, and status fields are not
/// accepted manifest inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageManifest {
    /// Manifest schema string; must equal [`crate::schema::PACKAGE_MANIFEST_SCHEMA`].
    pub schema: String,
    /// Package identity.
    pub package: PackageId,
    /// Exact package version.
    pub version: PackageVersion,
    /// Core spec profile, for example `npa.core.v0.1`.
    pub core_spec: String,
    /// Kernel compatibility profile, for example `npa.kernel.v0.1`.
    pub kernel_profile: String,
    /// Certificate format profile, for example `npa.certificate.canonical.v0.1`.
    pub certificate_format: String,
    /// Required checker profile, for example `npa.checker.reference.v0.1`.
    pub checker_profile: String,
    /// Package axiom policy.
    pub policy: PackagePolicy,
    /// Local modules declared by this package.
    pub modules: Vec<PackageModule>,
    /// Optional package license expression.
    pub license: Option<String>,
    /// Optional informational source repository URL.
    pub repository: Option<String>,
    /// Optional informational package description.
    pub description: Option<String>,
    /// Optional hash-pinned external module imports.
    pub imports: Option<Vec<PackageExternalImport>>,
}

/// Package-level axiom policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackagePolicy {
    /// Whether axioms outside [`Self::allowed_axioms`] may appear.
    pub allow_custom_axioms: bool,
    /// Exact axiom names permitted by package policy.
    pub allowed_axioms: Vec<Name>,
}

/// Hash-pinned top-level external package/module import.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageExternalImport {
    /// External module name.
    pub module: Name,
    /// External package identity.
    pub package: PackageId,
    /// Exact external package version.
    pub version: PackageVersion,
    /// Package-relative path to the vendored external certificate.
    pub certificate: PackagePath,
    /// Exact canonical export hash for the external module.
    pub export_hash: PackageHash,
    /// Exact canonical certificate hash for high-trust identity.
    pub certificate_hash: PackageHash,
}

/// Local module entry in an `npa.package.v0.1` manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageModule {
    /// Local module name.
    pub module: Name,
    /// Package-relative source path.
    pub source: PackagePath,
    /// Package-relative certificate path.
    pub certificate: PackagePath,
    /// Direct module imports, resolved by package graph validation.
    pub imports: Vec<Name>,
    /// Expected SHA-256 hash of source file bytes.
    pub expected_source_hash: PackageHash,
    /// Expected SHA-256 hash of certificate file bytes.
    pub expected_certificate_file_hash: PackageHash,
    /// Expected canonical export hash from the certificate.
    pub expected_export_hash: PackageHash,
    /// Expected canonical axiom report hash from the certificate.
    pub expected_axiom_report_hash: PackageHash,
    /// Expected canonical certificate hash from the certificate.
    pub expected_certificate_hash: PackageHash,
    /// Optional untrusted metadata path.
    pub meta: Option<PackagePath>,
    /// Optional untrusted replay path.
    pub replay: Option<PackagePath>,
    /// Optional producer profile metadata.
    pub producer_profile: Option<String>,
    /// Optional inductive declaration summary.
    pub inductives: Option<Vec<Name>>,
    /// Optional definition declaration summary.
    pub definitions: Option<Vec<Name>>,
    /// Optional theorem declaration summary.
    pub theorems: Option<Vec<Name>>,
    /// Optional axiom declaration summary checked against package policy.
    pub axioms: Option<Vec<Name>>,
    /// Optional search/docs metadata tags.
    pub tags: Option<Vec<String>>,
}

/// Parse package manifest TOML into a structured value without reading files.
pub fn parse_toml_value(source: &str) -> Result<toml::Value, toml::de::Error> {
    source.parse()
}

/// Parse an `npa-package.toml` string into accepted manifest input fields.
///
/// This function performs structured TOML parsing, duplicate-key rejection as
/// reported by the TOML parser, closed-object unknown-field checks, required
/// field checks, and TOML type checks. It does not read files, resolve imports,
/// build certificates, query registries, or execute checkers.
pub fn parse_manifest_str(source: &str) -> PackageManifestResult<PackageManifest> {
    let value = parse_toml_value(source).map_err(package_toml_parse_error)?;
    let root = value.as_table().ok_or_else(|| {
        PackageManifestError::wrong_type("$", None, "table", value_type_name(&value))
    })?;

    reject_unknown_fields("$", root, TOP_LEVEL_FIELDS)?;

    Ok(PackageManifest {
        schema: required_string(root, "$", "schema")?,
        package: PackageId::new(required_string(root, "$", "package")?),
        version: PackageVersion::new(required_string(root, "$", "version")?),
        core_spec: required_string(root, "$", "core_spec")?,
        kernel_profile: required_string(root, "$", "kernel_profile")?,
        certificate_format: required_string(root, "$", "certificate_format")?,
        checker_profile: required_string(root, "$", "checker_profile")?,
        policy: parse_policy(required_table(root, "$", "policy")?)?,
        modules: required_table_array(root, "$", "modules")?
            .into_iter()
            .enumerate()
            .map(|(index, module)| parse_module(index, module))
            .collect::<PackageManifestResult<Vec<_>>>()?,
        license: optional_string(root, "$", "license")?,
        repository: optional_string(root, "$", "repository")?,
        description: optional_string(root, "$", "description")?,
        imports: optional_table_array(root, "$", "imports")?
            .map(|imports| {
                imports
                    .into_iter()
                    .enumerate()
                    .map(|(index, import)| parse_external_import(index, import))
                    .collect::<PackageManifestResult<Vec<_>>>()
            })
            .transpose()?,
    })
}

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "core_spec",
    "kernel_profile",
    "certificate_format",
    "checker_profile",
    "policy",
    "modules",
    "license",
    "repository",
    "description",
    "imports",
];

const POLICY_FIELDS: &[&str] = &["allow_custom_axioms", "allowed_axioms"];

const IMPORT_FIELDS: &[&str] = &[
    "module",
    "package",
    "version",
    "certificate",
    "export_hash",
    "certificate_hash",
];

const MODULE_FIELDS: &[&str] = &[
    "module",
    "source",
    "certificate",
    "imports",
    "expected_source_hash",
    "expected_certificate_file_hash",
    "expected_export_hash",
    "expected_axiom_report_hash",
    "expected_certificate_hash",
    "meta",
    "replay",
    "producer_profile",
    "inductives",
    "definitions",
    "theorems",
    "axioms",
    "tags",
];

fn package_toml_parse_error(error: toml::de::Error) -> PackageManifestError {
    let message = error.message().to_owned();
    if message.contains("duplicate key") {
        PackageManifestError::duplicate_field(message)
    } else {
        PackageManifestError::invalid_toml(message)
    }
}

fn parse_policy(table: &Table) -> PackageManifestResult<PackagePolicy> {
    reject_unknown_fields("policy", table, POLICY_FIELDS)?;
    Ok(PackagePolicy {
        allow_custom_axioms: required_bool(table, "policy", "allow_custom_axioms")?,
        allowed_axioms: required_name_array(table, "policy", "allowed_axioms")?,
    })
}

fn parse_external_import(
    index: usize,
    table: &Table,
) -> PackageManifestResult<PackageExternalImport> {
    let path = format!("imports[{index}]");
    reject_unknown_fields(&path, table, IMPORT_FIELDS)?;
    Ok(PackageExternalImport {
        module: Name::from_dotted(required_string(table, &path, "module")?),
        package: PackageId::new(required_string(table, &path, "package")?),
        version: PackageVersion::new(required_string(table, &path, "version")?),
        certificate: PackagePath::new(required_string(table, &path, "certificate")?),
        export_hash: required_hash(table, &path, "export_hash")?,
        certificate_hash: required_hash(table, &path, "certificate_hash")?,
    })
}

fn parse_module(index: usize, table: &Table) -> PackageManifestResult<PackageModule> {
    let path = format!("modules[{index}]");
    reject_unknown_fields(&path, table, MODULE_FIELDS)?;
    Ok(PackageModule {
        module: Name::from_dotted(required_string(table, &path, "module")?),
        source: PackagePath::new(required_string(table, &path, "source")?),
        certificate: PackagePath::new(required_string(table, &path, "certificate")?),
        imports: required_name_array(table, &path, "imports")?,
        expected_source_hash: required_hash(table, &path, "expected_source_hash")?,
        expected_certificate_file_hash: required_hash(
            table,
            &path,
            "expected_certificate_file_hash",
        )?,
        expected_export_hash: required_hash(table, &path, "expected_export_hash")?,
        expected_axiom_report_hash: required_hash(table, &path, "expected_axiom_report_hash")?,
        expected_certificate_hash: required_hash(table, &path, "expected_certificate_hash")?,
        meta: optional_path(table, &path, "meta")?,
        replay: optional_path(table, &path, "replay")?,
        producer_profile: optional_string(table, &path, "producer_profile")?,
        inductives: optional_name_array(table, &path, "inductives")?,
        definitions: optional_name_array(table, &path, "definitions")?,
        theorems: optional_name_array(table, &path, "theorems")?,
        axioms: optional_name_array(table, &path, "axioms")?,
        tags: optional_string_array(table, &path, "tags")?,
    })
}

fn reject_unknown_fields(path: &str, table: &Table, allowed: &[&str]) -> PackageManifestResult<()> {
    for key in table.keys() {
        if !allowed.iter().any(|allowed_key| allowed_key == key) {
            return Err(PackageManifestError::unknown_field(path, key.clone()));
        }
    }
    Ok(())
}

fn required_value<'a>(
    table: &'a Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<&'a Value> {
    table
        .get(field)
        .ok_or_else(|| PackageManifestError::missing_field(path, field))
}

fn required_string(table: &Table, path: &str, field: &str) -> PackageManifestResult<String> {
    let value = required_value(table, path, field)?;
    value.as_str().map(ToOwned::to_owned).ok_or_else(|| {
        PackageManifestError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "string",
            value_type_name(value),
        )
    })
}

fn optional_string(
    table: &Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Option<String>> {
    table
        .get(field)
        .map(|value| {
            value.as_str().map(ToOwned::to_owned).ok_or_else(|| {
                PackageManifestError::wrong_type(
                    field_path(path, field),
                    Some(field.to_owned()),
                    "string",
                    value_type_name(value),
                )
            })
        })
        .transpose()
}

fn required_bool(table: &Table, path: &str, field: &str) -> PackageManifestResult<bool> {
    let value = required_value(table, path, field)?;
    value.as_bool().ok_or_else(|| {
        PackageManifestError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "bool",
            value_type_name(value),
        )
    })
}

fn required_table<'a>(
    table: &'a Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<&'a Table> {
    let value = required_value(table, path, field)?;
    value.as_table().ok_or_else(|| {
        PackageManifestError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "table",
            value_type_name(value),
        )
    })
}

fn required_table_array<'a>(
    table: &'a Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Vec<&'a Table>> {
    let value = required_value(table, path, field)?;
    table_array_from_value(value, &field_path(path, field), Some(field.to_owned()))
}

fn optional_table_array<'a>(
    table: &'a Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Option<Vec<&'a Table>>> {
    table
        .get(field)
        .map(|value| {
            table_array_from_value(value, &field_path(path, field), Some(field.to_owned()))
        })
        .transpose()
}

fn table_array_from_value<'a>(
    value: &'a Value,
    path: &str,
    field: Option<String>,
) -> PackageManifestResult<Vec<&'a Table>> {
    let array = value.as_array().ok_or_else(|| {
        PackageManifestError::wrong_type(
            path.to_owned(),
            field.clone(),
            "array",
            value_type_name(value),
        )
    })?;
    array
        .iter()
        .enumerate()
        .map(|(index, item)| {
            item.as_table().ok_or_else(|| {
                PackageManifestError::wrong_type(
                    format!("{path}[{index}]"),
                    None,
                    "table",
                    value_type_name(item),
                )
            })
        })
        .collect()
}

fn required_name_array(table: &Table, path: &str, field: &str) -> PackageManifestResult<Vec<Name>> {
    Ok(required_string_array(table, path, field)?
        .into_iter()
        .map(Name::from_dotted)
        .collect())
}

fn optional_name_array(
    table: &Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Option<Vec<Name>>> {
    optional_string_array(table, path, field).map(|value| {
        value.map(|items| items.into_iter().map(Name::from_dotted).collect::<Vec<_>>())
    })
}

fn required_string_array(
    table: &Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Vec<String>> {
    let value = required_value(table, path, field)?;
    string_array_from_value(value, &field_path(path, field), Some(field.to_owned()))
}

fn optional_string_array(
    table: &Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Option<Vec<String>>> {
    table
        .get(field)
        .map(|value| {
            string_array_from_value(value, &field_path(path, field), Some(field.to_owned()))
        })
        .transpose()
}

fn string_array_from_value(
    value: &Value,
    path: &str,
    field: Option<String>,
) -> PackageManifestResult<Vec<String>> {
    let array = value.as_array().ok_or_else(|| {
        PackageManifestError::wrong_type(
            path.to_owned(),
            field.clone(),
            "array",
            value_type_name(value),
        )
    })?;
    array
        .iter()
        .enumerate()
        .map(|(index, item)| {
            item.as_str().map(ToOwned::to_owned).ok_or_else(|| {
                PackageManifestError::wrong_type(
                    format!("{path}[{index}]"),
                    None,
                    "string",
                    value_type_name(item),
                )
            })
        })
        .collect()
}

fn optional_path(
    table: &Table,
    path: &str,
    field: &str,
) -> PackageManifestResult<Option<PackagePath>> {
    optional_string(table, path, field).map(|value| value.map(PackagePath::new))
}

fn required_hash(table: &Table, path: &str, field: &str) -> PackageManifestResult<PackageHash> {
    let value = required_string(table, path, field)?;
    parse_package_hash(&value, field_path(path, field))
}

fn field_path(path: &str, field: &str) -> String {
    if path == "$" {
        field.to_owned()
    } else {
        format!("{path}.{field}")
    }
}

fn value_type_name(value: &Value) -> &'static str {
    match value {
        Value::String(_) => "string",
        Value::Integer(_) => "integer",
        Value::Float(_) => "float",
        Value::Boolean(_) => "bool",
        Value::Datetime(_) => "datetime",
        Value::Array(_) => "array",
        Value::Table(_) => "table",
    }
}

#[cfg(test)]
mod tests {
    use npa_cert::Name;

    use super::{
        parse_toml_value, PackageExternalImport, PackageManifest, PackageModule, PackagePolicy,
        PackageVersion,
    };
    use crate::{PackageHash, PackageId, PackagePath, PACKAGE_MANIFEST_SCHEMA};

    #[test]
    fn package_manifest_skeleton_uses_structured_toml_parser() {
        let parsed = parse_toml_value("schema = \"npa.package.v0.1\"").unwrap();
        assert_eq!(parsed["schema"].as_str(), Some("npa.package.v0.1"));
    }

    #[test]
    fn package_manifest_schema_types_model_allowed_fields() {
        let zero_hash = PackageHash::new([0; 32]);
        let module = PackageModule {
            module: Name::from_dotted("Proofs.Ai.Basic"),
            source: PackagePath::new("Proofs/Ai/Basic/source.npa"),
            certificate: PackagePath::new("Proofs/Ai/Basic/certificate.npcert"),
            imports: vec![Name::from_dotted("Std.Logic.Eq")],
            expected_source_hash: zero_hash,
            expected_certificate_file_hash: zero_hash,
            expected_export_hash: zero_hash,
            expected_axiom_report_hash: zero_hash,
            expected_certificate_hash: zero_hash,
            meta: Some(PackagePath::new("Proofs/Ai/Basic/meta.json")),
            replay: Some(PackagePath::new("Proofs/Ai/Basic/replay.json")),
            producer_profile: Some("human-surface-explicit-term".to_owned()),
            inductives: Some(Vec::new()),
            definitions: Some(Vec::new()),
            theorems: Some(vec![Name::from_dotted("id")]),
            axioms: Some(Vec::new()),
            tags: Some(vec!["basic".to_owned()]),
        };
        let import = PackageExternalImport {
            module: Name::from_dotted("Std.Logic.Eq"),
            package: PackageId::new("npa-std"),
            version: PackageVersion::new("0.1.0"),
            certificate: PackagePath::new("vendor/npa-std/Std/Logic/Eq/certificate.npcert"),
            export_hash: zero_hash,
            certificate_hash: zero_hash,
        };
        let manifest = PackageManifest {
            schema: PACKAGE_MANIFEST_SCHEMA.to_owned(),
            package: PackageId::new("npa-proof-corpus"),
            version: PackageVersion::new("0.1.0"),
            core_spec: "npa.core.v0.1".to_owned(),
            kernel_profile: "npa.kernel.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_profile: "npa.checker.reference.v0.1".to_owned(),
            policy: PackagePolicy {
                allow_custom_axioms: false,
                allowed_axioms: vec![Name::from_dotted("Eq.rec")],
            },
            modules: vec![module],
            license: Some("Apache-2.0".to_owned()),
            repository: Some("https://github.com/finitefield-org/npa-core".to_owned()),
            description: Some("proof corpus fixture".to_owned()),
            imports: Some(vec![import]),
        };

        assert_eq!(manifest.schema, PACKAGE_MANIFEST_SCHEMA);
        assert_eq!(manifest.modules[0].expected_export_hash, zero_hash);
        assert_eq!(
            manifest.imports.as_ref().unwrap()[0].certificate_hash,
            zero_hash
        );
    }
}

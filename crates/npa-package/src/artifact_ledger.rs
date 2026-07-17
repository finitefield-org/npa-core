//! Typed parsing for the untrusted package artifact-ledger metadata sidecar.
//!
//! Successful parsing recognizes the `npa-ai-proof-meta-v0.1` metadata shape.
//! It does not validate certificate content, execute a checker, or confer proof
//! trust on the sidecar or any value recorded in it.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use npa_cert::Name;

use crate::{
    json::{parse_json, JsonMember, JsonValue},
    parse_package_hash, validate_canonical_module_name, validate_package_path, PackageHash,
    PackagePath,
};

/// Exact metadata schema recognized by the artifact-ledger audit.
pub const PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA: &str = "npa-ai-proof-meta-v0.1";

const DUPLICATE_KEY_FIELD: &str = "duplicate_key";
const UNSUPPORTED_SCHEMA_VALUE: &str = "unsupported schema";
const INVALID_NAME_VALUE: &str = "invalid name";
const INVALID_HASH_VALUE: &str = "invalid hash";

/// Parsed, untrusted metadata ledger values used for comparison.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerMetadata {
    /// Module identity recorded by the metadata ledger.
    pub module: Name,
    /// Package-relative source path recorded by the metadata ledger.
    pub source: PackagePath,
    /// Package-relative certificate path recorded by the metadata ledger.
    pub certificate: PackagePath,
    /// Producer profile recorded by the metadata ledger.
    pub producer_profile: String,
    /// Exact source-file hash recorded by the metadata ledger.
    pub source_sha256: PackageHash,
    /// Exact certificate-file hash recorded by the metadata ledger.
    pub certificate_file_sha256: PackageHash,
    /// Canonical export hash recorded by the metadata ledger.
    pub export_hash: PackageHash,
    /// Canonical axiom-report hash recorded by the metadata ledger.
    pub axiom_report_hash: PackageHash,
    /// Canonical certificate hash recorded by the metadata ledger.
    pub certificate_hash: PackageHash,
    /// Canonical, sorted, duplicate-free import names.
    pub imports: Vec<Name>,
    /// Canonical, sorted, duplicate-free axiom names.
    pub axioms: Vec<Name>,
}

/// Source declaration kind rendered into refreshed artifact-ledger metadata.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageArtifactLedgerDeclarationKind {
    /// Explicit source axiom.
    Axiom,
    /// Explicit source definition.
    Definition,
    /// Explicit source theorem.
    Theorem,
    /// Explicit source inductive declaration or mutual block.
    Inductive,
}

impl PackageArtifactLedgerDeclarationKind {
    /// Stable metadata spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Definition => "def",
            Self::Theorem => "theorem",
            Self::Inductive => "inductive",
        }
    }
}

/// Explicit source declaration rendered into refreshed metadata.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerDeclaration {
    /// Canonical declaration name relative to the module.
    pub name: Name,
    /// Source declaration kind.
    pub kind: PackageArtifactLedgerDeclarationKind,
}

impl PackageArtifactLedgerDeclaration {
    /// Build an explicit metadata declaration.
    pub fn new(name: Name, kind: PackageArtifactLedgerDeclarationKind) -> Self {
        Self { name, kind }
    }
}

/// Checked values used to render one canonical metadata sidecar.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerMetadataRefreshInput {
    /// Local module identity.
    pub module: Name,
    /// Validated package-relative source path.
    pub source: PackagePath,
    /// Validated package-relative certificate path.
    pub certificate: PackagePath,
    /// Nonempty producer profile from the manifest.
    pub producer_profile: String,
    /// Hash of exact source bytes used by the build.
    pub source_sha256: PackageHash,
    /// Hash of freshly encoded canonical certificate bytes.
    pub certificate_file_sha256: PackageHash,
    /// Verified export hash.
    pub export_hash: PackageHash,
    /// Verified axiom-report hash.
    pub axiom_report_hash: PackageHash,
    /// Verified certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical direct package-module imports.
    pub imports: Vec<Name>,
    /// Canonical verified axiom-report union.
    pub axioms: Vec<Name>,
    /// Explicit parsed source declarations.
    pub declarations: Vec<PackageArtifactLedgerDeclaration>,
}

impl PackageArtifactLedgerMetadataRefreshInput {
    /// Build a complete checked metadata refresh input.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        module: Name,
        source: PackagePath,
        certificate: PackagePath,
        producer_profile: String,
        source_sha256: PackageHash,
        certificate_file_sha256: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
        imports: Vec<Name>,
        axioms: Vec<Name>,
        declarations: Vec<PackageArtifactLedgerDeclaration>,
    ) -> Self {
        Self {
            module,
            source,
            certificate,
            producer_profile,
            source_sha256,
            certificate_file_sha256,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            imports,
            axioms,
            declarations,
        }
    }
}

/// Typed failure while parsing an artifact-ledger metadata document.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerMetadataError {
    /// Stable machine-readable failure reason.
    pub reason_code: PackageArtifactLedgerMetadataErrorReason,
    /// JSON field associated with the failure, when available.
    pub field: Option<String>,
    /// Expected scalar value or type, when useful.
    pub expected_value: Option<String>,
    /// Actual scalar value or type, when useful.
    pub actual_value: Option<String>,
}

/// Stable artifact-ledger metadata parser failure reasons.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageArtifactLedgerMetadataErrorReason {
    /// JSON is malformed or contains a duplicate object key.
    InvalidJson,
    /// The root or a required field has the wrong JSON type.
    WrongType,
    /// A required field is absent.
    MissingField,
    /// The metadata schema is not supported.
    UnsupportedSchema,
    /// A required hash does not use canonical lowercase SHA-256 spelling.
    InvalidHash,
    /// A module, import, or axiom name is not canonical.
    InvalidName,
    /// A source or certificate path is not a lexical package-relative path.
    InvalidPath,
    /// An import or axiom name occurs more than once.
    DuplicateName,
}

impl PackageArtifactLedgerMetadataErrorReason {
    /// Return the stable diagnostic reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidJson => "artifact_ledger_meta_invalid_json",
            Self::WrongType => "artifact_ledger_meta_wrong_type",
            Self::MissingField => "artifact_ledger_meta_missing_field",
            Self::UnsupportedSchema => "artifact_ledger_meta_unsupported_schema",
            Self::InvalidHash => "artifact_ledger_meta_invalid_hash",
            Self::InvalidName => "artifact_ledger_meta_invalid_name",
            Self::InvalidPath => "artifact_ledger_meta_invalid_path",
            Self::DuplicateName => "artifact_ledger_meta_duplicate_name",
        }
    }
}

impl PackageArtifactLedgerMetadataError {
    fn new(reason_code: PackageArtifactLedgerMetadataErrorReason) -> Self {
        Self {
            reason_code,
            field: None,
            expected_value: None,
            actual_value: None,
        }
    }

    fn field(mut self, field: impl Into<String>) -> Self {
        self.field = Some(field.into());
        self
    }

    fn values(mut self, expected: impl Into<String>, actual: impl Into<String>) -> Self {
        self.expected_value = Some(expected.into());
        self.actual_value = Some(actual.into());
        self
    }
}

/// Parse and validate an untrusted `npa-ai-proof-meta-v0.1` document.
///
/// Unknown top-level fields are tolerated, but duplicate keys are rejected
/// recursively, including duplicates inside ignored extension objects.
pub fn parse_package_artifact_ledger_metadata(
    source: &str,
) -> Result<PackageArtifactLedgerMetadata, PackageArtifactLedgerMetadataError> {
    let value = parse_json(source).map_err(|_| {
        PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::InvalidJson,
        )
    })?;
    reject_duplicate_keys(&value)?;
    let members = value.object_members().ok_or_else(|| {
        PackageArtifactLedgerMetadataError::new(PackageArtifactLedgerMetadataErrorReason::WrongType)
            .values("object", value.kind().as_str())
    })?;

    let schema = required_string(members, "schema")?;
    if schema != PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA {
        return Err(PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::UnsupportedSchema,
        )
        .field("schema")
        .values(
            PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA,
            UNSUPPORTED_SCHEMA_VALUE,
        ));
    }

    let module = required_name(members, "module")?;
    let source_path = required_path(members, "source")?;
    let certificate = required_path(members, "certificate")?;
    let producer_profile = required_string(members, "producer_profile")?.to_owned();
    if producer_profile.is_empty() {
        return Err(PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::WrongType,
        )
        .field("producer_profile")
        .values("non-empty string", "empty string"));
    }

    Ok(PackageArtifactLedgerMetadata {
        module,
        source: source_path,
        certificate,
        producer_profile,
        source_sha256: required_hash(members, "source_sha256")?,
        certificate_file_sha256: required_hash(members, "certificate_file_sha256")?,
        export_hash: required_hash(members, "export_hash")?,
        axiom_report_hash: required_hash(members, "axiom_report_hash")?,
        certificate_hash: required_hash(members, "certificate_hash")?,
        imports: required_name_array(members, "imports")?,
        axioms: required_name_array(members, "axioms")?,
    })
}

const STANDARD_METADATA_FIELDS: &[&str] = &[
    "schema",
    "module",
    "source",
    "certificate",
    "producer_profile",
    "trusted_status",
    "source_sha256",
    "certificate_file_sha256",
    "export_hash",
    "axiom_report_hash",
    "certificate_hash",
    "imports",
    "axioms",
    "declarations",
    "trust_boundary",
];

/// Render canonical refreshed metadata while preserving valid unknown members.
pub fn refresh_package_artifact_ledger_metadata(
    existing: Option<&str>,
    input: &PackageArtifactLedgerMetadataRefreshInput,
) -> Result<String, PackageArtifactLedgerMetadataError> {
    if input.producer_profile.is_empty() {
        return Err(PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::WrongType,
        )
        .field("producer_profile")
        .values("non-empty string", "empty string"));
    }
    let mut extensions = BTreeMap::<String, JsonValue>::new();
    if let Some(existing) = existing {
        let value = parse_json(existing).map_err(|_| {
            PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::InvalidJson,
            )
        })?;
        reject_duplicate_keys(&value)?;
        let members = value.object_members().ok_or_else(|| {
            PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::WrongType,
            )
            .values("object", value.kind().as_str())
        })?;
        if let Some(schema) = members.iter().find(|member| member.key() == "schema") {
            if schema.value().string_value() != Some(PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA) {
                return Err(PackageArtifactLedgerMetadataError::new(
                    PackageArtifactLedgerMetadataErrorReason::UnsupportedSchema,
                )
                .field("schema")
                .values(
                    PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA,
                    UNSUPPORTED_SCHEMA_VALUE,
                ));
            }
        }
        for member in members {
            if !STANDARD_METADATA_FIELDS.contains(&member.key()) {
                extensions.insert(member.key().to_owned(), member.value().clone());
            }
        }
    }

    let mut imports = input.imports.clone();
    imports.sort();
    imports.dedup();
    let mut axioms = input.axioms.clone();
    axioms.sort();
    axioms.dedup();
    let mut output = String::from("{\n");
    let standard = [
        ("schema", PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA.to_owned()),
        ("module", input.module.as_dotted().to_owned()),
        ("source", input.source.as_str().to_owned()),
        ("certificate", input.certificate.as_str().to_owned()),
        ("producer_profile", input.producer_profile.clone()),
        ("trusted_status", "verified_by_certificate".to_owned()),
        (
            "source_sha256",
            crate::format_package_hash(&input.source_sha256),
        ),
        (
            "certificate_file_sha256",
            crate::format_package_hash(&input.certificate_file_sha256),
        ),
        (
            "export_hash",
            crate::format_package_hash(&input.export_hash),
        ),
        (
            "axiom_report_hash",
            crate::format_package_hash(&input.axiom_report_hash),
        ),
        (
            "certificate_hash",
            crate::format_package_hash(&input.certificate_hash),
        ),
    ];
    let mut first = true;
    for (key, value) in standard {
        push_pretty_member_prefix(&mut output, &mut first, key);
        push_json_string(&mut output, &value);
    }
    push_name_array_member(&mut output, &mut first, "imports", &imports);
    push_name_array_member(&mut output, &mut first, "axioms", &axioms);
    push_pretty_member_prefix(&mut output, &mut first, "declarations");
    output.push('[');
    for (index, declaration) in input.declarations.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push_str("{\"name\":");
        push_json_string(&mut output, &declaration.name.as_dotted());
        output.push_str(",\"kind\":");
        push_json_string(&mut output, declaration.kind.as_str());
        output.push('}');
    }
    output.push(']');
    push_pretty_member_prefix(&mut output, &mut first, "trust_boundary");
    push_json_string(
        &mut output,
        "source, replay, and metadata are non-trusted sidecars; only the canonical certificate verified by npa-cert is accepted",
    );
    for (key, value) in extensions {
        push_pretty_member_prefix(&mut output, &mut first, &key);
        push_json_value(&mut output, &value);
    }
    output.push_str("\n}\n");
    Ok(output)
}

fn push_pretty_member_prefix(output: &mut String, first: &mut bool, key: &str) {
    if !*first {
        output.push_str(",\n");
    }
    *first = false;
    output.push_str("  ");
    push_json_string(output, key);
    output.push_str(": ");
}

fn push_name_array_member(output: &mut String, first: &mut bool, key: &str, names: &[Name]) {
    push_pretty_member_prefix(output, first, key);
    output.push('[');
    for (index, name) in names.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        push_json_string(output, &name.as_dotted());
    }
    output.push(']');
}

fn push_json_string(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                write!(output, "\\u{:04x}", character as u32).expect("write to String cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
}

fn push_json_value(output: &mut String, value: &JsonValue) {
    match value {
        JsonValue::Null => output.push_str("null"),
        JsonValue::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        JsonValue::Number(value) => output.push_str(value),
        JsonValue::String(value) => push_json_string(output, value),
        JsonValue::Array(values) => {
            output.push('[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    output.push(',');
                }
                push_json_value(output, value);
            }
            output.push(']');
        }
        JsonValue::Object(members) => {
            output.push('{');
            for (index, member) in members.iter().enumerate() {
                if index > 0 {
                    output.push(',');
                }
                push_json_string(output, member.key());
                output.push(':');
                push_json_value(output, member.value());
            }
            output.push('}');
        }
    }
}

fn reject_duplicate_keys(value: &JsonValue) -> Result<(), PackageArtifactLedgerMetadataError> {
    match value {
        JsonValue::Object(members) => {
            let mut keys = BTreeSet::new();
            for member in members {
                if !keys.insert(member.key()) {
                    return Err(PackageArtifactLedgerMetadataError::new(
                        PackageArtifactLedgerMetadataErrorReason::InvalidJson,
                    )
                    .field(DUPLICATE_KEY_FIELD));
                }
                reject_duplicate_keys(member.value())?;
            }
        }
        JsonValue::Array(values) => {
            for value in values {
                reject_duplicate_keys(value)?;
            }
        }
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {}
    }
    Ok(())
}

fn required_value<'a>(
    members: &'a [JsonMember],
    field: &str,
) -> Result<&'a JsonValue, PackageArtifactLedgerMetadataError> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| {
            PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::MissingField,
            )
            .field(field)
        })
}

fn required_string<'a>(
    members: &'a [JsonMember],
    field: &str,
) -> Result<&'a str, PackageArtifactLedgerMetadataError> {
    let value = required_value(members, field)?;
    value.string_value().ok_or_else(|| {
        PackageArtifactLedgerMetadataError::new(PackageArtifactLedgerMetadataErrorReason::WrongType)
            .field(field)
            .values("string", value.kind().as_str())
    })
}

fn required_name(
    members: &[JsonMember],
    field: &str,
) -> Result<Name, PackageArtifactLedgerMetadataError> {
    let value = required_string(members, field)?;
    let name = Name::from_dotted(value);
    validate_canonical_module_name(&name, field).map_err(|_| {
        PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::InvalidName,
        )
        .field(field)
        .values("canonical dotted name", INVALID_NAME_VALUE)
    })?;
    Ok(name)
}

fn required_path(
    members: &[JsonMember],
    field: &str,
) -> Result<PackagePath, PackageArtifactLedgerMetadataError> {
    let value = required_string(members, field)?;
    let path = PackagePath::new(value);
    validate_package_path(&path, field).map_err(|_| {
        PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::InvalidPath,
        )
        .field(field)
        .values("package-relative path", "invalid path")
    })?;
    Ok(path)
}

fn required_hash(
    members: &[JsonMember],
    field: &str,
) -> Result<PackageHash, PackageArtifactLedgerMetadataError> {
    let value = required_string(members, field)?;
    parse_package_hash(value, field).map_err(|_| {
        PackageArtifactLedgerMetadataError::new(
            PackageArtifactLedgerMetadataErrorReason::InvalidHash,
        )
        .field(field)
        .values("sha256:<64 lowercase hex>", INVALID_HASH_VALUE)
    })
}

fn required_name_array(
    members: &[JsonMember],
    field: &str,
) -> Result<Vec<Name>, PackageArtifactLedgerMetadataError> {
    let value = required_value(members, field)?;
    let values = value.array_elements().ok_or_else(|| {
        PackageArtifactLedgerMetadataError::new(PackageArtifactLedgerMetadataErrorReason::WrongType)
            .field(field)
            .values("array", value.kind().as_str())
    })?;
    let mut names = Vec::with_capacity(values.len());
    let mut seen = BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        let item_field = format!("{field}[{index}]");
        let string = value.string_value().ok_or_else(|| {
            PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::WrongType,
            )
            .field(&item_field)
            .values("string", value.kind().as_str())
        })?;
        let name = Name::from_dotted(string);
        validate_canonical_module_name(&name, &item_field).map_err(|_| {
            PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::InvalidName,
            )
            .field(&item_field)
            .values("canonical dotted name", INVALID_NAME_VALUE)
        })?;
        if !seen.insert(name.clone()) {
            return Err(PackageArtifactLedgerMetadataError::new(
                PackageArtifactLedgerMetadataErrorReason::DuplicateName,
            )
            .field(field)
            .values("unique canonical names", string));
        }
        names.push(name);
    }
    names.sort();
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;

    const HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    fn metadata(extra: &str) -> String {
        format!(
            r#"{{
  "schema":"npa-ai-proof-meta-v0.1",
  "module":"Example.Module",
  "source":"Example/Module/source.npa",
  "certificate":"Example/Module/certificate.npcert",
  "producer_profile":"fixture",
  "source_sha256":"{HASH}",
  "certificate_file_sha256":"{HASH}",
  "export_hash":"{HASH}",
  "axiom_report_hash":"{HASH}",
  "certificate_hash":"{HASH}",
  "imports":["Example.Z","Example.A"],
  "axioms":[]{extra}
}}"#
        )
    }

    #[test]
    fn artifact_ledger_metadata_parses_and_sorts_names() {
        let parsed = parse_package_artifact_ledger_metadata(&metadata("")).unwrap();
        assert_eq!(
            parsed
                .imports
                .iter()
                .map(Name::as_dotted)
                .collect::<Vec<_>>(),
            vec!["Example.A", "Example.Z"]
        );
    }

    #[test]
    fn artifact_ledger_metadata_tolerates_unknown_fields() {
        parse_package_artifact_ledger_metadata(&metadata(
            r#", "description":{"future":[1,true,null]}"#,
        ))
        .unwrap();
    }

    #[test]
    fn artifact_ledger_metadata_rejects_nested_duplicate_keys() {
        let private_key = "/Users/private/metadata-key";
        let error = parse_package_artifact_ledger_metadata(&metadata(&format!(
            r#", "description":{{"{private_key}":1,"{private_key}":2}}"#,
        )))
        .unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidJson
        );
        assert_eq!(error.field.as_deref(), Some(DUPLICATE_KEY_FIELD));
        assert!(!format!("{error:?}").contains(private_key));
    }

    #[test]
    fn artifact_ledger_metadata_rejects_duplicate_names() {
        let source = metadata("").replace(
            r#"["Example.Z","Example.A"]"#,
            r#"["Example.A","Example.A"]"#,
        );
        let error = parse_package_artifact_ledger_metadata(&source).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::DuplicateName
        );
    }

    #[test]
    fn artifact_ledger_metadata_rejects_noncanonical_hash_and_path() {
        let bad_hash = metadata("").replace(HASH, "sha256:ABC");
        assert_eq!(
            parse_package_artifact_ledger_metadata(&bad_hash)
                .unwrap_err()
                .reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidHash
        );
        let bad_path = metadata("").replace("Example/Module/source.npa", "../source.npa");
        let error = parse_package_artifact_ledger_metadata(&bad_path).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidPath
        );
        assert_eq!(
            error.expected_value.as_deref(),
            Some("package-relative path")
        );
        assert_eq!(error.actual_value.as_deref(), Some("invalid path"));
        assert!(!format!("{error:?}").contains("../source.npa"));
    }

    #[test]
    fn artifact_ledger_metadata_rejects_malformed_and_top_level_duplicate_json() {
        assert_eq!(
            parse_package_artifact_ledger_metadata("{")
                .unwrap_err()
                .reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidJson
        );
        let duplicate = metadata("").replace(
            r#""schema":"npa-ai-proof-meta-v0.1","#,
            r#""schema":"npa-ai-proof-meta-v0.1","schema":"other","#,
        );
        let error = parse_package_artifact_ledger_metadata(&duplicate).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidJson
        );
        assert_eq!(error.field.as_deref(), Some(DUPLICATE_KEY_FIELD));
    }

    #[test]
    fn artifact_ledger_metadata_distinguishes_missing_wrong_type_and_schema() {
        let missing = metadata("").replace(
            &format!(
                r#"  "source_sha256":"{HASH}",
"#
            ),
            "",
        );
        let error = parse_package_artifact_ledger_metadata(&missing).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::MissingField
        );
        assert_eq!(error.field.as_deref(), Some("source_sha256"));

        let wrong_type =
            metadata("").replace(r#""imports":["Example.Z","Example.A"]"#, r#""imports":{}"#);
        assert_eq!(
            parse_package_artifact_ledger_metadata(&wrong_type)
                .unwrap_err()
                .reason_code,
            PackageArtifactLedgerMetadataErrorReason::WrongType
        );

        let unsupported_value = "/Users/private/future-schema";
        let unsupported = metadata("").replace("npa-ai-proof-meta-v0.1", unsupported_value);
        let error = parse_package_artifact_ledger_metadata(&unsupported).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactLedgerMetadataErrorReason::UnsupportedSchema
        );
        assert_eq!(
            error.actual_value.as_deref(),
            Some(UNSUPPORTED_SCHEMA_VALUE)
        );
        assert!(!format!("{error:?}").contains(unsupported_value));
    }

    #[test]
    fn artifact_ledger_metadata_rejects_every_noncanonical_hash_shape() {
        for replacement in [
            "sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
            "sha256:0",
            "sha256:00000000000000000000000000000000000000000000000000000000000000000",
            "sha256:gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg",
        ] {
            let source = metadata("").replacen(HASH, replacement, 1);
            let error = parse_package_artifact_ledger_metadata(&source).unwrap_err();
            assert_eq!(
                error.reason_code,
                PackageArtifactLedgerMetadataErrorReason::InvalidHash,
                "replacement={replacement}"
            );
            assert_eq!(error.actual_value.as_deref(), Some(INVALID_HASH_VALUE));
            assert!(!format!("{error:?}").contains(replacement));
        }
    }

    #[test]
    fn artifact_ledger_metadata_rejects_noncanonical_names_and_certificate_paths() {
        for (source, invalid_name) in [
            (
                metadata("").replace("Example.Module", "Example..Module"),
                "Example..Module",
            ),
            (
                metadata("").replace("Example.Z", "Example..Z"),
                "Example..Z",
            ),
            (
                metadata("").replace(r#""axioms":[]"#, r#""axioms":["Example..Axiom"]"#),
                "Example..Axiom",
            ),
        ] {
            let error = parse_package_artifact_ledger_metadata(&source).unwrap_err();
            assert_eq!(
                error.reason_code,
                PackageArtifactLedgerMetadataErrorReason::InvalidName
            );
            assert_eq!(error.actual_value.as_deref(), Some(INVALID_NAME_VALUE));
            assert!(!format!("{error:?}").contains(invalid_name));
        }
        for path in [
            "/absolute/certificate.npcert",
            "Example//certificate.npcert",
        ] {
            let source = metadata("").replace("Example/Module/certificate.npcert", path);
            assert_eq!(
                parse_package_artifact_ledger_metadata(&source)
                    .unwrap_err()
                    .reason_code,
                PackageArtifactLedgerMetadataErrorReason::InvalidPath
            );
        }
    }

    #[test]
    fn artifact_ledger_metadata_sorts_axioms_independently_of_input_order() {
        let first = metadata("").replace(r#""axioms":[]"#, r#""axioms":["Example.Z","Example.A"]"#);
        let second =
            metadata("").replace(r#""axioms":[]"#, r#""axioms":["Example.A","Example.Z"]"#);
        let first = parse_package_artifact_ledger_metadata(&first).unwrap();
        let second = parse_package_artifact_ledger_metadata(&second).unwrap();
        assert_eq!(first.imports, second.imports);
        assert_eq!(first.axioms, second.axioms);

        let duplicate =
            metadata("").replace(r#""axioms":[]"#, r#""axioms":["Example.A","Example.A"]"#);
        assert_eq!(
            parse_package_artifact_ledger_metadata(&duplicate)
                .unwrap_err()
                .reason_code,
            PackageArtifactLedgerMetadataErrorReason::DuplicateName
        );
    }

    #[test]
    fn artifact_ledger_metadata_refresh_canonicalizes_direct_imports_and_preserves_extensions() {
        let input = PackageArtifactLedgerMetadataRefreshInput {
            module: Name::from_dotted("Example.Module"),
            source: PackagePath::new("Example/Module/source.npa"),
            certificate: PackagePath::new("Example/Module/certificate.npcert"),
            producer_profile: "human-surface-explicit-term".to_owned(),
            source_sha256: PackageHash::new([1; 32]),
            certificate_file_sha256: PackageHash::new([2; 32]),
            export_hash: PackageHash::new([3; 32]),
            axiom_report_hash: PackageHash::new([4; 32]),
            certificate_hash: PackageHash::new([5; 32]),
            imports: vec![
                Name::from_dotted("Example.Z"),
                Name::from_dotted("Example.A"),
            ],
            axioms: vec![Name::from_dotted("Classical.choice")],
            declarations: vec![PackageArtifactLedgerDeclaration {
                name: Name::from_dotted("theorem_name"),
                kind: PackageArtifactLedgerDeclarationKind::Theorem,
            }],
        };
        let existing = metadata(r#", "z_extension":{"b":2,"a":1}, "a_extension":true"#);
        let refreshed = refresh_package_artifact_ledger_metadata(Some(&existing), &input).unwrap();
        assert_eq!(
            refresh_package_artifact_ledger_metadata(Some(&refreshed), &input).unwrap(),
            refreshed
        );
        assert!(refreshed.contains("\"a_extension\": true"));
        assert!(refreshed.contains("\"z_extension\": {\"b\":2,\"a\":1}"));
        assert!(refreshed.find("a_extension").unwrap() < refreshed.find("z_extension").unwrap());
        assert!(refreshed.ends_with("\n"));
        let parsed = parse_package_artifact_ledger_metadata(&refreshed).unwrap();
        assert_eq!(
            parsed.imports,
            vec![
                Name::from_dotted("Example.A"),
                Name::from_dotted("Example.Z")
            ]
        );
    }

    #[test]
    fn artifact_ledger_metadata_refresh_rejects_duplicates_and_other_schema() {
        let input = PackageArtifactLedgerMetadataRefreshInput {
            module: Name::from_dotted("Example.Module"),
            source: PackagePath::new("source.npa"),
            certificate: PackagePath::new("certificate.npcert"),
            producer_profile: "fixture".to_owned(),
            source_sha256: PackageHash::new([0; 32]),
            certificate_file_sha256: PackageHash::new([0; 32]),
            export_hash: PackageHash::new([0; 32]),
            axiom_report_hash: PackageHash::new([0; 32]),
            certificate_hash: PackageHash::new([0; 32]),
            imports: vec![],
            axioms: vec![],
            declarations: vec![],
        };
        assert_eq!(
            refresh_package_artifact_ledger_metadata(
                Some("{\"schema\":\"npa-ai-proof-meta-v0.1\",\"x\":1,\"x\":2}"),
                &input,
            )
            .unwrap_err()
            .reason_code,
            PackageArtifactLedgerMetadataErrorReason::InvalidJson
        );
        assert_eq!(
            refresh_package_artifact_ledger_metadata(Some("{\"schema\":\"future\"}"), &input)
                .unwrap_err()
                .reason_code,
            PackageArtifactLedgerMetadataErrorReason::UnsupportedSchema
        );
    }
}

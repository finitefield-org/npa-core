//! Offline generated-artifact release-manifest validation.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use npa_api::{JsonDocument, JsonValue, JsonValueKind};

const V0_1_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.1";
const V0_2_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.2";
const VALIDATION_SCHEMA: &str = "npa.generated_artifact_release_manifest.validation.v0.1";
const COMMAND_RESULT_SCHEMA_V0_1: &str = "npa.package.command_result.v0.1";
const COMMAND_RESULT_SCHEMA_V0_2: &str = "npa.package.command_result.v0.2";
const COMMAND_RESULT_SCHEMA_V0_3: &str = "npa.package.command_result.v0.3";
const TIMINGS_SCHEMA: &str = "npa.package.timings.v0.1";
const PACKAGE_LOCK_RELATIVE_PATH: &str = "generated/package-lock.json";

const BASE_FIELDS: &[&str] = &[
    "schema",
    "package",
    "package_root",
    "source_commit",
    "tag",
    "npa_core_ref",
    "generated_at_utc",
    "generator_commands",
    "check_commands",
    "generated_files",
    "omitted_files",
    "archive",
];
const VERIFICATION_FIELDS: &[&str] = &[
    "package_lock_mode",
    "package_lock_path",
    "package_lock_sha256",
    "command",
    "command_result",
    "checker_mode",
    "verdict_source",
    "npa_core_source_kind",
    "npa_core_checkout_revision",
    "npa_core_tree_hash",
    "npa_cli_crate_version",
    "cargo_manifest_path",
    "cargo_lock_path",
    "cargo_lock_sha256",
    "rust_toolchain",
    "rust_target",
    "cargo_profile",
    "host_executable_name",
    "host_executable_sha256",
    "external_checker",
];
const EXTERNAL_FIELDS: &[&str] = &[
    "runner_policy_path",
    "runner_policy_sha256",
    "checker_registry_path",
    "checker_registry_sha256",
    "checker_id",
    "checker_version",
    "checker_binary_sha256",
    "checker_build_hash",
];
const DIAGNOSTIC_REQUIRED_FIELDS: &[&str] = &["kind", "reason_code", "severity"];
const DIAGNOSTIC_OPTIONAL_FIELDS_V0_1: &[&str] = &[
    "module",
    "path",
    "field",
    "expected_hash",
    "actual_hash",
    "expected_value",
    "actual_value",
    "checker",
];
const DIAGNOSTIC_OPTIONAL_FIELDS_V0_2: &[&str] = &[
    "module",
    "path",
    "field",
    "expected_hash",
    "actual_hash",
    "expected_value",
    "actual_value",
    "checker",
    "source",
];
const DIAGNOSTIC_OPTIONAL_FIELDS_V0_3: &[&str] = &[
    "module",
    "path",
    "field",
    "expected_hash",
    "actual_hash",
    "expected_value",
    "actual_value",
    "checker",
    "source",
    "conversion",
];

type Object<'value, 'source> = BTreeMap<&'value str, &'value JsonValue<'source>>;

/// Deterministic release-manifest validation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseManifestValidationError {
    message: String,
}

impl ReleaseManifestValidationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ReleaseManifestValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for ReleaseManifestValidationError {}

/// Successful input schema and evidence classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReleaseManifestValidation {
    input_schema: &'static str,
    evidence_classification: &'static str,
}

impl ReleaseManifestValidation {
    /// Validated input manifest schema.
    pub const fn input_schema(self) -> &'static str {
        self.input_schema
    }

    /// Evidence classification assigned by the validator.
    pub const fn evidence_classification(self) -> &'static str {
        self.evidence_classification
    }

    /// Render the stable compact success JSON without a trailing newline.
    pub fn render_json(self) -> String {
        format!(
            "{{\"schema\":\"{VALIDATION_SCHEMA}\",\"status\":\"valid\",\"input_schema\":\"{}\",\"evidence_classification\":\"{}\"}}",
            self.input_schema, self.evidence_classification
        )
    }
}

/// Validate one UTF-8 generated-artifact release-manifest document.
///
/// This function performs no filesystem, network, process, or asset I/O.
pub fn validate_release_manifest(
    source: &str,
    require_v0_2: bool,
) -> Result<ReleaseManifestValidation, ReleaseManifestValidationError> {
    let document = JsonDocument::parse(source).map_err(|error| {
        ReleaseManifestValidationError::new(format!(
            "invalid JSON at byte {}: {:?}",
            error.offset, error.kind
        ))
    })?;
    reject_duplicate_fields(document.root())?;
    validate_manifest(document.root(), require_v0_2)
}

fn reject_duplicate_fields(value: &JsonValue<'_>) -> Result<(), ReleaseManifestValidationError> {
    match value.kind() {
        JsonValueKind::Array => {
            for item in value
                .array_elements()
                .expect("JSON array kind has elements")
            {
                reject_duplicate_fields(item)?;
            }
        }
        JsonValueKind::Object => {
            let members = value
                .object_members()
                .expect("JSON object kind has members");
            for member in members {
                reject_duplicate_fields(member.value())?;
            }
            let mut fields = BTreeSet::new();
            for member in members {
                if !fields.insert(member.key()) {
                    return Err(ReleaseManifestValidationError::new(format!(
                        "duplicate JSON field '{}'",
                        member.key()
                    )));
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn require_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
) -> Result<Object<'value, 'source>, ReleaseManifestValidationError> {
    let members = value.object_members().ok_or_else(|| {
        ReleaseManifestValidationError::new(format!("{where_} must be an object"))
    })?;
    Ok(members
        .iter()
        .map(|member| (member.key(), member.value()))
        .collect())
}

fn require_fields(
    object: &Object<'_, '_>,
    required: &[&str],
    where_: &str,
    optional: &[&str],
) -> Result<(), ReleaseManifestValidationError> {
    let mut missing = required
        .iter()
        .copied()
        .filter(|field| !object.contains_key(field))
        .collect::<Vec<_>>();
    missing.sort_unstable();
    if let Some(field) = missing.first() {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} missing field '{field}'"
        )));
    }

    let mut unknown = object
        .keys()
        .copied()
        .filter(|field| !required.contains(field) && !optional.contains(field))
        .collect::<Vec<_>>();
    unknown.sort_unstable();
    if let Some(field) = unknown.first() {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} has unknown field '{field}'"
        )));
    }
    Ok(())
}

fn value<'value, 'source>(
    object: &Object<'value, 'source>,
    field: &str,
) -> &'value JsonValue<'source> {
    object
        .get(field)
        .copied()
        .expect("required field was checked before access")
}

fn require_text<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let text = value.string_value().ok_or_else(|| {
        ReleaseManifestValidationError::new(format!("{where_} must be a nonempty canonical string"))
    })?;
    if text.is_empty() || text.trim() != text {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be a nonempty canonical string"
        )));
    }
    if text.chars().any(|character| (character as u32) < 0x20) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} contains a control character"
        )));
    }
    Ok(text)
}

fn require_nonempty_text<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let text = value.string_value().ok_or_else(|| {
        ReleaseManifestValidationError::new(format!("{where_} must be a nonempty string"))
    })?;
    if text.is_empty() {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be a nonempty string"
        )));
    }
    if text.chars().any(|character| (character as u32) < 0x20) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} contains a control character"
        )));
    }
    Ok(text)
}

fn require_array<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
) -> Result<&'value [JsonValue<'source>], ReleaseManifestValidationError> {
    value
        .array_elements()
        .ok_or_else(|| ReleaseManifestValidationError::new(format!("{where_} must be an array")))
}

fn require_bool(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<bool, ReleaseManifestValidationError> {
    value
        .bool_value()
        .ok_or_else(|| ReleaseManifestValidationError::new(format!("{where_} must be a boolean")))
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct DecimalNat(String);

impl DecimalNat {
    fn parse(value: &JsonValue<'_>, where_: &str) -> Result<Self, ReleaseManifestValidationError> {
        let raw = value.number_raw().ok_or_else(|| {
            ReleaseManifestValidationError::new(format!("{where_} must be a nonnegative integer"))
        })?;
        let digits = if raw == "-0" { "0" } else { raw };
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_} must be a nonnegative integer"
            )));
        }
        let normalized = digits.trim_start_matches('0');
        Ok(Self(if normalized.is_empty() {
            "0".to_owned()
        } else {
            normalized.to_owned()
        }))
    }

    fn greater_than(&self, other: &Self) -> bool {
        self.0.len() > other.0.len()
            || (self.0.len() == other.0.len() && self.0.as_bytes() > other.0.as_bytes())
    }

    fn is_zero(&self) -> bool {
        self.0 == "0"
    }
}

fn require_locator<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let path = require_text(value, where_)?;
    if path.starts_with('/') || path.starts_with('\\') || path.contains('\\') {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be a relative slash-separated path"
        )));
    }
    let bytes = path.as_bytes();
    if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must not be an absolute Windows path"
        )));
    }
    if path
        .split('/')
        .any(|segment| segment.is_empty() || segment == "." || segment == "..")
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must not contain empty, '.' or '..' segments"
        )));
    }
    Ok(path)
}

fn require_lower_hex(text: &str, length: usize) -> bool {
    text.len() == length
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn verification_hash<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let text = require_text(value, where_)?;
    let Some(digest) = text.strip_prefix("sha256:") else {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be sha256:<64-lowercase-hex>"
        )));
    };
    if !require_lower_hex(digest, 64) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be sha256:<64-lowercase-hex>"
        )));
    }
    Ok(digest)
}

fn retained_hash<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let text = require_text(value, where_)?;
    if !require_lower_hex(text, 64) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must contain a lowercase SHA-256 digest"
        )));
    }
    Ok(text)
}

fn validate_timestamp(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    let text = require_text(value, where_)?;
    let bytes = text.as_bytes();
    let shape = bytes.len() == 20
        && matches!(bytes[4], b'-')
        && matches!(bytes[7], b'-')
        && matches!(bytes[10], b'T')
        && matches!(bytes[13], b':')
        && matches!(bytes[16], b':')
        && matches!(bytes[19], b'Z')
        && bytes.iter().enumerate().all(|(index, byte)| {
            matches!(index, 4 | 7 | 10 | 13 | 16 | 19) || byte.is_ascii_digit()
        });
    if !shape {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must use YYYY-MM-DDTHH:MM:SSZ"
        )));
    }
    let number = |start: usize, end: usize| -> u32 {
        text[start..end]
            .parse()
            .expect("timestamp digit slices parse")
    };
    let year = number(0, 4);
    let month = number(5, 7);
    let day = number(8, 10);
    let hour = number(11, 13);
    let minute = number(14, 16);
    let second = number(17, 19);
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => 0,
    };
    if year == 0 || day == 0 || day > days || hour > 23 || minute > 59 || second > 59 {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must use YYYY-MM-DDTHH:MM:SSZ"
        )));
    }
    Ok(())
}

fn validate_string_array(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    for (index, item) in require_array(value, where_)?.iter().enumerate() {
        require_text(item, &format!("{where_}[{index}]"))?;
    }
    Ok(())
}

fn package_name_is_valid(text: &str) -> bool {
    text.as_bytes()
        .first()
        .is_some_and(u8::is_ascii_alphanumeric)
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
}

fn profile_is_valid(text: &str) -> bool {
    package_name_is_valid(text)
}

fn rust_target_is_valid(text: &str) -> bool {
    let segments = text.split('-').collect::<Vec<_>>();
    segments.len() >= 3
        && segments.iter().enumerate().all(|(index, segment)| {
            !segment.is_empty()
                && segment.bytes().all(|byte| {
                    byte.is_ascii_alphanumeric() || byte == b'_' || (index > 0 && byte == b'.')
                })
        })
}

fn cli_version_is_valid(text: &str) -> bool {
    let fields = text.split('.').collect::<Vec<_>>();
    fields.len() == 3
        && fields[0] == "0"
        && matches!(fields[1], "3" | "4" | "5" | "6" | "7")
        && !fields[2].is_empty()
        && fields[2].bytes().all(|byte| byte.is_ascii_digit())
        && (fields[2] == "0" || !fields[2].starts_with('0'))
}

fn require_matching_text<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
    predicate: impl FnOnce(&str) -> bool,
) -> Result<&'value str, ReleaseManifestValidationError> {
    let text = require_text(value, where_)?;
    if !predicate(text) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} has an invalid value"
        )));
    }
    Ok(text)
}

fn validate_retained_manifest(
    manifest: &Object<'_, '_>,
) -> Result<BTreeMap<String, String>, ReleaseManifestValidationError> {
    require_matching_text(value(manifest, "package"), "package", package_name_is_valid)?;
    require_locator(value(manifest, "package_root"), "package_root")?;
    require_matching_text(value(manifest, "source_commit"), "source_commit", |text| {
        require_lower_hex(text, 40)
    })?;
    require_text(value(manifest, "tag"), "tag")?;
    require_text(value(manifest, "npa_core_ref"), "npa_core_ref")?;
    validate_timestamp(value(manifest, "generated_at_utc"), "generated_at_utc")?;
    validate_string_array(value(manifest, "generator_commands"), "generator_commands")?;
    validate_string_array(value(manifest, "check_commands"), "check_commands")?;

    let generated = require_array(value(manifest, "generated_files"), "generated_files")?;
    if generated.is_empty() {
        return Err(ReleaseManifestValidationError::new(
            "generated_files must not be empty",
        ));
    }
    let mut generated_hashes = BTreeMap::new();
    for (index, raw_entry) in generated.iter().enumerate() {
        let where_ = format!("generated_files[{index}]");
        let entry = require_object(raw_entry, &where_)?;
        require_fields(&entry, &["path", "sha256"], &where_, &[])?;
        let path = require_locator(value(&entry, "path"), &format!("{where_}.path"))?;
        if generated_hashes.contains_key(path) {
            return Err(ReleaseManifestValidationError::new(format!(
                "generated_files contains duplicate path '{path}'"
            )));
        }
        let digest = retained_hash(value(&entry, "sha256"), &format!("{where_}.sha256"))?;
        generated_hashes.insert(path.to_owned(), digest.to_owned());
    }

    let mut omitted_paths = BTreeSet::new();
    for (index, raw_entry) in require_array(value(manifest, "omitted_files"), "omitted_files")?
        .iter()
        .enumerate()
    {
        let where_ = format!("omitted_files[{index}]");
        let entry = require_object(raw_entry, &where_)?;
        require_fields(&entry, &["path", "reason"], &where_, &[])?;
        let path = require_locator(value(&entry, "path"), &format!("{where_}.path"))?;
        require_text(value(&entry, "reason"), &format!("{where_}.reason"))?;
        if generated_hashes.contains_key(path) || !omitted_paths.insert(path) {
            return Err(ReleaseManifestValidationError::new(format!(
                "omitted_files contains duplicate or generated path '{path}'"
            )));
        }
    }

    let archive = require_object(value(manifest, "archive"), "archive")?;
    require_fields(&archive, &["path", "sha256"], "archive", &[])?;
    require_locator(value(&archive, "path"), "archive.path")?;
    retained_hash(value(&archive, "sha256"), "archive.sha256")?;
    Ok(generated_hashes)
}

fn command_result_schema_for_cli(version: &str) -> &'static str {
    if version.starts_with("0.6.") || version.starts_with("0.7.") {
        COMMAND_RESULT_SCHEMA_V0_3
    } else if version.starts_with("0.5.") {
        COMMAND_RESULT_SCHEMA_V0_2
    } else {
        COMMAND_RESULT_SCHEMA_V0_1
    }
}

fn validate_diagnostic_source(
    value_: &JsonValue<'_>,
    where_: &str,
    schema: &str,
) -> Result<(), ReleaseManifestValidationError> {
    let source = require_object(value_, where_)?;
    require_fields(
        &source,
        &["path", "start_byte", "end_byte"],
        where_,
        if schema == COMMAND_RESULT_SCHEMA_V0_3 {
            &["declaration", "line", "column", "token"]
        } else {
            &["declaration"]
        },
    )?;
    require_locator(value(&source, "path"), &format!("{where_}.path"))?;
    let start = DecimalNat::parse(
        value(&source, "start_byte"),
        &format!("{where_}.start_byte"),
    )?;
    let end = DecimalNat::parse(value(&source, "end_byte"), &format!("{where_}.end_byte"))?;
    if start.greater_than(&end) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} has reversed byte offsets"
        )));
    }
    if source.contains_key("declaration") {
        require_nonempty_text(
            value(&source, "declaration"),
            &format!("{where_}.declaration"),
        )?;
    }
    let has_line = source.contains_key("line");
    let has_column = source.contains_key("column");
    if has_line != has_column {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.line and column must appear together"
        )));
    }
    if has_line {
        let line = DecimalNat::parse(value(&source, "line"), &format!("{where_}.line"))?;
        let column = DecimalNat::parse(value(&source, "column"), &format!("{where_}.column"))?;
        if line.is_zero() || column.is_zero() {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.line and column must be positive"
            )));
        }
    }
    if source.contains_key("token") {
        let token = require_nonempty_text(value(&source, "token"), &format!("{where_}.token"))?;
        if token.len() > 64 || token.chars().any(char::is_control) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.token is not a bounded token"
            )));
        }
    }
    Ok(())
}

fn validate_diagnostic_conversion(
    value_: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    let conversion = require_object(value_, where_)?;
    require_fields(
        &conversion,
        &["phase", "outcome", "lhs_head", "rhs_head", "depth"],
        where_,
        &[],
    )?;
    let phase = require_text(value(&conversion, "phase"), &format!("{where_}.phase"))?;
    if !matches!(
        phase,
        "term_check"
            | "declaration_type"
            | "declaration_value"
            | "inductive_constructor"
            | "inductive_recursor"
            | "definitional_equality"
    ) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.phase is unsupported"
        )));
    }
    let outcome = require_text(value(&conversion, "outcome"), &format!("{where_}.outcome"))?;
    if !matches!(outcome, "not_defeq" | "fuel_exhausted") {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.outcome is unsupported"
        )));
    }
    for field in ["lhs_head", "rhs_head"] {
        let head = require_text(value(&conversion, field), &format!("{where_}.{field}"))?;
        let valid = matches!(
            head,
            "sort" | "bound_variable" | "application" | "lambda" | "pi" | "let" | "unknown"
        ) || head.strip_prefix("constant:").is_some_and(|name| {
            !name.is_empty() && name.len() <= 256 && !name.chars().any(char::is_control)
        });
        if !valid {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.{field} is not a bounded expression head"
            )));
        }
    }
    DecimalNat::parse(value(&conversion, "depth"), &format!("{where_}.depth"))?;
    Ok(())
}

fn validate_command_result_shape<'value, 'source>(
    value_: &'value JsonValue<'source>,
    npa_cli_version: &str,
) -> Result<Object<'value, 'source>, ReleaseManifestValidationError> {
    let result = require_object(value_, "verification.command_result")?;
    require_fields(
        &result,
        &[
            "schema",
            "command",
            "root",
            "status",
            "diagnostics",
            "artifacts",
        ],
        "verification.command_result",
        &["timings"],
    )?;
    let schema = value(&result, "schema").string_value();
    if !matches!(
        schema,
        Some(COMMAND_RESULT_SCHEMA_V0_1 | COMMAND_RESULT_SCHEMA_V0_2 | COMMAND_RESULT_SCHEMA_V0_3)
    ) {
        return Err(ReleaseManifestValidationError::new(
            "verification.command_result.schema is unsupported",
        ));
    }
    if schema.expect("supported schema") != command_result_schema_for_cli(npa_cli_version) {
        return Err(ReleaseManifestValidationError::new(
            "verification.command_result.schema does not match verification.npa_cli_crate_version",
        ));
    }
    if value(&result, "command").string_value() != Some("package verify-certs") {
        return Err(ReleaseManifestValidationError::new(
            "verification.command_result.command must be 'package verify-certs'",
        ));
    }
    require_text(value(&result, "root"), "verification.command_result.root")?;
    if value(&result, "status").string_value() != Some("passed") {
        return Err(ReleaseManifestValidationError::new(
            "verification.command_result.status must be 'passed'",
        ));
    }

    let diagnostics = require_array(
        value(&result, "diagnostics"),
        "verification.command_result.diagnostics",
    )?;
    if diagnostics.is_empty() {
        return Err(ReleaseManifestValidationError::new(
            "verification.command_result.diagnostics must not be empty",
        ));
    }
    let optional = match schema {
        Some(COMMAND_RESULT_SCHEMA_V0_1) => DIAGNOSTIC_OPTIONAL_FIELDS_V0_1,
        Some(COMMAND_RESULT_SCHEMA_V0_2) => DIAGNOSTIC_OPTIONAL_FIELDS_V0_2,
        _ => DIAGNOSTIC_OPTIONAL_FIELDS_V0_3,
    };
    for (index, raw_diagnostic) in diagnostics.iter().enumerate() {
        let where_ = format!("verification.command_result.diagnostics[{index}]");
        let diagnostic = require_object(raw_diagnostic, &where_)?;
        require_fields(&diagnostic, DIAGNOSTIC_REQUIRED_FIELDS, &where_, optional)?;
        require_text(value(&diagnostic, "kind"), &format!("{where_}.kind"))?;
        require_text(
            value(&diagnostic, "reason_code"),
            &format!("{where_}.reason_code"),
        )?;
        if value(&diagnostic, "severity").string_value() != Some("info") {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.severity must be 'info' for a passed result"
            )));
        }
        let mut text_fields = DIAGNOSTIC_OPTIONAL_FIELDS_V0_1
            .iter()
            .copied()
            .filter(|field| diagnostic.contains_key(field))
            .collect::<Vec<_>>();
        text_fields.sort_unstable();
        for field in text_fields {
            require_text(value(&diagnostic, field), &format!("{where_}.{field}"))?;
        }
        if diagnostic.contains_key("source") {
            validate_diagnostic_source(
                value(&diagnostic, "source"),
                &format!("{where_}.source"),
                schema.expect("supported schema"),
            )?;
        }
        if diagnostic.contains_key("conversion") {
            validate_diagnostic_conversion(
                value(&diagnostic, "conversion"),
                &format!("{where_}.conversion"),
            )?;
        }
    }

    for (index, raw_artifact) in require_array(
        value(&result, "artifacts"),
        "verification.command_result.artifacts",
    )?
    .iter()
    .enumerate()
    {
        let where_ = format!("verification.command_result.artifacts[{index}]");
        let artifact = require_object(raw_artifact, &where_)?;
        require_fields(&artifact, &["kind", "path"], &where_, &[])?;
        require_text(value(&artifact, "kind"), &format!("{where_}.kind"))?;
        require_locator(value(&artifact, "path"), &format!("{where_}.path"))?;
    }

    if result.contains_key("timings") {
        let timings = require_object(
            value(&result, "timings"),
            "verification.command_result.timings",
        )?;
        let required = &["schema", "mode", "unit", "proof_evidence", "build_evidence"];
        let mut missing = required
            .iter()
            .copied()
            .filter(|field| !timings.contains_key(field))
            .collect::<Vec<_>>();
        missing.sort_unstable();
        if let Some(field) = missing.first() {
            return Err(ReleaseManifestValidationError::new(format!(
                "verification.command_result.timings missing field '{field}'"
            )));
        }
        if value(&timings, "schema").string_value() != Some(TIMINGS_SCHEMA)
            || value(&timings, "unit").string_value() != Some("ms")
        {
            return Err(ReleaseManifestValidationError::new(
                "verification.command_result.timings has an invalid schema or unit",
            ));
        }
        require_text(
            value(&timings, "mode"),
            "verification.command_result.timings.mode",
        )?;
        if require_bool(
            value(&timings, "proof_evidence"),
            "verification.command_result.timings.proof_evidence",
        )? {
            return Err(ReleaseManifestValidationError::new(
                "timings must not be proof evidence",
            ));
        }
        if require_bool(
            value(&timings, "build_evidence"),
            "verification.command_result.timings.build_evidence",
        )? {
            return Err(ReleaseManifestValidationError::new(
                "timings must not be build evidence",
            ));
        }
        for (field, item) in &timings {
            if required.contains(field) {
                continue;
            }
            if !field.ends_with("_ms") {
                return Err(ReleaseManifestValidationError::new(format!(
                    "verification.command_result.timings has unknown field '{field}'"
                )));
            }
            DecimalNat::parse(
                item,
                &format!("verification.command_result.timings.{field}"),
            )?;
        }
    }
    Ok(result)
}

fn validate_external_identity<'value, 'source>(
    value_: &'value JsonValue<'source>,
    checker_mode: &str,
) -> Result<Option<Object<'value, 'source>>, ReleaseManifestValidationError> {
    if checker_mode != "external" {
        if value_.kind() != JsonValueKind::Null {
            return Err(ReleaseManifestValidationError::new(
                "verification.external_checker must be null for in-process modes",
            ));
        }
        return Ok(None);
    }
    let external = require_object(value_, "verification.external_checker")?;
    require_fields(
        &external,
        EXTERNAL_FIELDS,
        "verification.external_checker",
        &[],
    )?;
    require_locator(
        value(&external, "runner_policy_path"),
        "verification.external_checker.runner_policy_path",
    )?;
    verification_hash(
        value(&external, "runner_policy_sha256"),
        "verification.external_checker.runner_policy_sha256",
    )?;
    require_locator(
        value(&external, "checker_registry_path"),
        "verification.external_checker.checker_registry_path",
    )?;
    verification_hash(
        value(&external, "checker_registry_sha256"),
        "verification.external_checker.checker_registry_sha256",
    )?;
    require_text(
        value(&external, "checker_id"),
        "verification.external_checker.checker_id",
    )?;
    require_text(
        value(&external, "checker_version"),
        "verification.external_checker.checker_version",
    )?;
    verification_hash(
        value(&external, "checker_binary_sha256"),
        "verification.external_checker.checker_binary_sha256",
    )?;
    verification_hash(
        value(&external, "checker_build_hash"),
        "verification.external_checker.checker_build_hash",
    )?;
    Ok(Some(external))
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum OptionValue {
    Boolean,
    Text(String),
}

type ParsedOptions = BTreeMap<&'static str, Vec<OptionValue>>;

fn parse_flag_options(
    tokens: &[String],
    value_flags: &[(&'static str, &'static str)],
    boolean_flags: &[(&'static str, &'static str)],
    where_: &str,
) -> Result<ParsedOptions, ReleaseManifestValidationError> {
    let mut parsed = BTreeMap::new();
    let mut index = 0;
    while index < tokens.len() {
        let token = &tokens[index];
        let (flag, mut inline_value) = match token.split_once('=') {
            Some((flag, value)) => (flag, Some(value.to_owned())),
            None => (token.as_str(), None),
        };
        let (key, option_value) = if let Some((_, key)) = boolean_flags
            .iter()
            .find(|(candidate, _)| *candidate == flag)
        {
            if inline_value.is_some() {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{where_} flag '{flag}' does not take a value"
                )));
            }
            (*key, OptionValue::Boolean)
        } else if let Some((_, key)) = value_flags.iter().find(|(candidate, _)| *candidate == flag)
        {
            if inline_value.is_none() {
                index += 1;
                if index >= tokens.len() || tokens[index].starts_with('-') {
                    return Err(ReleaseManifestValidationError::new(format!(
                        "{where_} flag '{flag}' requires a value"
                    )));
                }
                inline_value = Some(tokens[index].clone());
            }
            let text = inline_value.expect("value option has value");
            if text.is_empty() {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{where_} flag '{flag}' requires a value"
                )));
            }
            (*key, OptionValue::Text(text))
        } else {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_} has unsupported token '{token}'"
            )));
        };
        if parsed.contains_key(key) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_} repeats flag '{flag}'"
            )));
        }
        parsed
            .entry(key)
            .or_insert_with(Vec::new)
            .push(option_value);
        index += 1;
    }
    Ok(parsed)
}

fn one_option<'options>(
    options: &'options ParsedOptions,
    key: &str,
    where_: &str,
) -> Result<&'options str, ReleaseManifestValidationError> {
    match options.get(key).map(Vec::as_slice) {
        Some([OptionValue::Text(value)]) => Ok(value),
        _ => Err(ReleaseManifestValidationError::new(format!(
            "{where_} must select '{key}' exactly once"
        ))),
    }
}

fn require_boolean_option(
    options: &ParsedOptions,
    key: &str,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    if matches!(
        options.get(key).map(Vec::as_slice),
        Some([OptionValue::Boolean])
    ) {
        Ok(())
    } else {
        Err(ReleaseManifestValidationError::new(format!(
            "{where_} must select '{key}' exactly once"
        )))
    }
}

fn command_manifest_matches(recorded: &str, command_value: &str) -> bool {
    if command_value == recorded {
        return true;
    }
    let mut relative = command_value;
    while let Some(rest) = relative.strip_prefix("../") {
        relative = rest;
    }
    if let Some(rest) = relative.strip_prefix("./") {
        relative = rest;
    }
    relative == recorded
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ShellQuote {
    None,
    Single,
    Double,
}

fn shell_words(command: &str) -> Result<Vec<String>, ReleaseManifestValidationError> {
    let mut words = Vec::new();
    let mut current = String::new();
    let mut quote = ShellQuote::None;
    let mut started = false;
    let mut characters = command.chars();
    while let Some(character) = characters.next() {
        match quote {
            ShellQuote::None => match character {
                ' ' | '\t' | '\r' | '\n' => {
                    if started {
                        words.push(std::mem::take(&mut current));
                        started = false;
                    }
                }
                '\'' => {
                    quote = ShellQuote::Single;
                    started = true;
                }
                '"' => {
                    quote = ShellQuote::Double;
                    started = true;
                }
                '\\' => {
                    let escaped = characters.next().ok_or_else(|| {
                        ReleaseManifestValidationError::new(
                            "verification.command is not valid shell tokenization",
                        )
                    })?;
                    current.push(escaped);
                    started = true;
                }
                _ => {
                    current.push(character);
                    started = true;
                }
            },
            ShellQuote::Single => {
                if character == '\'' {
                    quote = ShellQuote::None;
                } else {
                    current.push(character);
                }
            }
            ShellQuote::Double => match character {
                '"' => quote = ShellQuote::None,
                '\\' => {
                    let escaped = characters.next().ok_or_else(|| {
                        ReleaseManifestValidationError::new(
                            "verification.command is not valid shell tokenization",
                        )
                    })?;
                    if matches!(escaped, '"' | '\\') {
                        current.push(escaped);
                    } else {
                        current.push('\\');
                        current.push(escaped);
                    }
                }
                _ => current.push(character),
            },
        }
    }
    if quote != ShellQuote::None {
        return Err(ReleaseManifestValidationError::new(
            "verification.command is not valid shell tokenization",
        ));
    }
    if started {
        words.push(current);
    }
    Ok(words)
}

fn validate_recorded_command(
    verification: &Object<'_, '_>,
    result: &Object<'_, '_>,
    external: Option<&Object<'_, '_>>,
) -> Result<(), ReleaseManifestValidationError> {
    let command = require_text(value(verification, "command"), "verification.command")?;
    let tokens = shell_words(command)?;
    if tokens.first().map(String::as_str) != Some("cargo")
        || tokens.get(1).map(String::as_str) != Some("run")
        || tokens.iter().filter(|token| token.as_str() == "--").count() != 1
    {
        return Err(ReleaseManifestValidationError::new(
            "verification.command must be one cargo run invocation",
        ));
    }
    let separator = tokens
        .iter()
        .position(|token| token == "--")
        .expect("one separator exists");
    let cargo_options = parse_flag_options(
        &tokens[2..separator],
        &[
            ("--manifest-path", "manifest_path"),
            ("--package", "package"),
            ("-p", "package"),
            ("--profile", "profile"),
            ("--target", "target"),
        ],
        &[
            ("--locked", "locked"),
            ("--offline", "offline"),
            ("--quiet", "quiet"),
            ("-q", "quiet"),
            ("--release", "release"),
        ],
        "verification.command cargo prefix",
    )?;
    require_boolean_option(&cargo_options, "locked", "verification.command")?;
    let manifest_path = require_text(
        value(verification, "cargo_manifest_path"),
        "verification.cargo_manifest_path",
    )?;
    if cargo_options.contains_key("manifest_path")
        && !command_manifest_matches(
            manifest_path,
            one_option(&cargo_options, "manifest_path", "verification.command")?,
        )
    {
        return Err(ReleaseManifestValidationError::new(
            "verification.command manifest path disagrees with cargo_manifest_path",
        ));
    }
    if cargo_options.contains_key("release") && cargo_options.contains_key("profile") {
        return Err(ReleaseManifestValidationError::new(
            "verification.command selects two Cargo profiles",
        ));
    }
    let command_profile = if cargo_options.contains_key("release") {
        "release"
    } else if cargo_options.contains_key("profile") {
        one_option(&cargo_options, "profile", "verification.command")?
    } else {
        "dev"
    };
    if require_text(
        value(verification, "cargo_profile"),
        "verification.cargo_profile",
    )? != command_profile
    {
        return Err(ReleaseManifestValidationError::new(
            "verification.command profile disagrees with cargo_profile",
        ));
    }
    if cargo_options.contains_key("target")
        && one_option(&cargo_options, "target", "verification.command")?
            != require_text(
                value(verification, "rust_target"),
                "verification.rust_target",
            )?
    {
        return Err(ReleaseManifestValidationError::new(
            "verification.command target disagrees with rust_target",
        ));
    }
    if one_option(&cargo_options, "package", "verification.command")? != "npa-cli" {
        return Err(ReleaseManifestValidationError::new(
            "verification.command Cargo package disagrees with host_executable_name",
        ));
    }

    let application_tokens = &tokens[separator + 1..];
    if application_tokens.first().map(String::as_str) != Some("package")
        || application_tokens.get(1).map(String::as_str) != Some("verify-certs")
    {
        return Err(ReleaseManifestValidationError::new(
            "direct verification command must invoke package verify-certs",
        ));
    }
    let options = parse_flag_options(
        application_tokens.get(2..).unwrap_or_default(),
        &[
            ("--root", "root"),
            ("--package-lock", "package_lock"),
            ("--checker", "checker"),
            ("--audit-cache", "audit_cache"),
            ("--verifier-memo", "verifier_memo"),
            ("--jobs", "jobs"),
            ("--timings", "timings"),
            ("--runner-policy", "runner_policy"),
            ("--runner-policy-hash", "runner_policy_hash"),
            ("--checker-registry", "checker_registry"),
        ],
        &[("--json", "json")],
        "verification.command package invocation",
    )?;
    let root = one_option(&options, "root", "verification.command")?;
    validate_locator_text(root, "verification.command --root")?;
    if root != require_text(value(result, "root"), "verification.command_result.root")? {
        return Err(ReleaseManifestValidationError::new(
            "verification.command root disagrees with command_result.root",
        ));
    }
    if one_option(&options, "audit_cache", "verification.command")? != "off" {
        return Err(ReleaseManifestValidationError::new(
            "direct verification command must select --audit-cache off",
        ));
    }
    if one_option(&options, "verifier_memo", "verification.command")? != "off" {
        return Err(ReleaseManifestValidationError::new(
            "direct verification command must select --verifier-memo off",
        ));
    }
    if let Some(external) = external {
        if one_option(&options, "runner_policy", "verification.command")?
            != require_text(
                value(external, "runner_policy_path"),
                "verification.external_checker.runner_policy_path",
            )?
        {
            return Err(ReleaseManifestValidationError::new(
                "runner policy path disagrees with the recorded command",
            ));
        }
        if one_option(&options, "runner_policy_hash", "verification.command")?
            != require_text(
                value(external, "runner_policy_sha256"),
                "verification.external_checker.runner_policy_sha256",
            )?
        {
            return Err(ReleaseManifestValidationError::new(
                "runner policy hash disagrees with the recorded command",
            ));
        }
        if one_option(&options, "checker_registry", "verification.command")?
            != require_text(
                value(external, "checker_registry_path"),
                "verification.external_checker.checker_registry_path",
            )?
        {
            return Err(ReleaseManifestValidationError::new(
                "checker registry path disagrees with the recorded command",
            ));
        }
    } else if ["runner_policy", "runner_policy_hash", "checker_registry"]
        .iter()
        .any(|key| options.contains_key(key))
    {
        return Err(ReleaseManifestValidationError::new(
            "in-process verification command has external checker flags",
        ));
    }
    if one_option(&options, "package_lock", "verification.command")? != "checked" {
        return Err(ReleaseManifestValidationError::new(
            "verification.command must explicitly select --package-lock checked",
        ));
    }
    let checker_mode = require_text(
        value(verification, "checker_mode"),
        "verification.checker_mode",
    )?;
    if one_option(&options, "checker", "verification.command")? != checker_mode {
        return Err(ReleaseManifestValidationError::new(
            "verification.command checker disagrees with checker_mode",
        ));
    }
    require_boolean_option(&options, "json", "verification.command")?;
    if options.contains_key("jobs") {
        let jobs = one_option(&options, "jobs", "verification.command")?;
        let positive = !jobs.is_empty()
            && jobs.bytes().all(|byte| byte.is_ascii_digit())
            && jobs.bytes().any(|byte| byte != b'0');
        if !positive {
            return Err(ReleaseManifestValidationError::new(
                "verification.command --jobs must be a positive integer",
            ));
        }
        let normalized = jobs.trim_start_matches('0');
        let normalized = if normalized.is_empty() {
            "0"
        } else {
            normalized
        };
        if checker_mode == "reference" && normalized != "1" {
            return Err(ReleaseManifestValidationError::new(
                "reference verification command must use one job",
            ));
        }
        if external.is_some() && jobs != "1" {
            return Err(ReleaseManifestValidationError::new(
                "external verification command must use one job",
            ));
        }
    }
    let timing_mode = if options.contains_key("timings") {
        one_option(&options, "timings", "verification.command")?
    } else {
        "off"
    };
    if !matches!(timing_mode, "off" | "summary" | "detailed") {
        return Err(ReleaseManifestValidationError::new(
            "verification.command has an unsupported timing mode",
        ));
    }
    if result.contains_key("timings") {
        let timings = require_object(
            value(result, "timings"),
            "verification.command_result.timings",
        )?;
        if timing_mode == "off" || value(&timings, "mode").string_value() != Some(timing_mode) {
            return Err(ReleaseManifestValidationError::new(
                "verification.command timings disagree with command_result",
            ));
        }
    } else if timing_mode != "off" {
        return Err(ReleaseManifestValidationError::new(
            "verification.command timings are missing from command_result",
        ));
    }
    Ok(())
}

fn validate_locator_text(path: &str, where_: &str) -> Result<(), ReleaseManifestValidationError> {
    if path.is_empty()
        || path.trim() != path
        || path.chars().any(|character| (character as u32) < 0x20)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be a nonempty canonical string"
        )));
    }
    if path.starts_with('/') || path.starts_with('\\') || path.contains('\\') {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be a relative slash-separated path"
        )));
    }
    let bytes = path.as_bytes();
    if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must not be an absolute Windows path"
        )));
    }
    if path
        .split('/')
        .any(|segment| segment.is_empty() || matches!(segment, "." | ".."))
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must not contain empty, '.' or '..' segments"
        )));
    }
    Ok(())
}

fn exact_fields(object: &Object<'_, '_>, fields: &[&str]) -> bool {
    object.len() == fields.len() && fields.iter().all(|field| object.contains_key(field))
}

fn counter_segment(segment: &str, key: &str) -> bool {
    segment
        .strip_prefix(key)
        .and_then(|rest| rest.strip_prefix('='))
        .is_some_and(|value| !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()))
}

fn process_memo_telemetry_is_valid(text: &str) -> bool {
    let fields = text.split(';').collect::<Vec<_>>();
    fields.len() == 5
        && fields[0] == "mode=process-local"
        && counter_segment(fields[1], "hits")
        && counter_segment(fields[2], "misses")
        && counter_segment(fields[3], "inserted")
        && fields[4] == "trusted=false"
}

fn decode_cache_telemetry_is_valid(text: &str) -> bool {
    let fields = text.split(';').collect::<Vec<_>>();
    let counters = [
        "certificate_hits",
        "certificate_misses",
        "certificate_inserted",
        "import_context_hits",
        "import_context_misses",
        "import_context_inserted",
        "import_context_disk_hits",
        "import_context_disk_misses",
        "import_context_disk_stale",
        "import_context_disk_schema_misses",
        "import_context_disk_inserted",
    ];
    fields.len() == 14
        && fields[0] == "mode=process-local"
        && counters
            .iter()
            .enumerate()
            .all(|(index, key)| counter_segment(fields[index + 1], key))
        && fields[12] == "trusted=false"
        && fields[13] == "proof_evidence=false"
}

fn validate_result_agreement(
    verification: &Object<'_, '_>,
    result: &Object<'_, '_>,
    external: Option<&Object<'_, '_>>,
) -> Result<(), ReleaseManifestValidationError> {
    let checker_mode = require_text(
        value(verification, "checker_mode"),
        "verification.checker_mode",
    )?;
    let (kind, result_mode, checker, reference_verdict) = match checker_mode {
        "reference" => ("ReferenceVerifier", "reference", "npa-checker-ref", "true"),
        "fast" => (
            "FastVerifier",
            "fast-kernel",
            "fast-kernel-certificate-verifier",
            "false",
        ),
        "external" => ("ExternalVerifier", "external", "npa-checker-ext", "false"),
        _ => unreachable!("checker mode validated before result agreement"),
    };
    if require_text(
        value(verification, "verdict_source"),
        "verification.verdict_source",
    )? != checker
    {
        return Err(ReleaseManifestValidationError::new(
            "verification.verdict_source disagrees with checker_mode",
        ));
    }
    if let Some(external) = external {
        if require_text(
            value(external, "checker_id"),
            "verification.external_checker.checker_id",
        )? != checker
        {
            return Err(ReleaseManifestValidationError::new(
                "external checker_id disagrees with checker_mode",
            ));
        }
    }

    let diagnostics = require_array(
        value(result, "diagnostics"),
        "verification.command_result.diagnostics",
    )?;
    let mut diagnostic_objects = Vec::with_capacity(diagnostics.len());
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        diagnostic_objects.push(require_object(
            diagnostic,
            &format!("verification.command_result.diagnostics[{index}]"),
        )?);
    }
    let allowed_reasons = [
        "package_verified",
        "package_lock_checked",
        "module_verified",
        "process_memo_summary",
        "decode_cache_summary",
    ];
    if diagnostic_objects.iter().any(|diagnostic| {
        !value(diagnostic, "reason_code")
            .string_value()
            .is_some_and(|reason| allowed_reasons.contains(&reason))
    }) {
        return Err(ReleaseManifestValidationError::new(
            "command_result contains a non-live verification diagnostic",
        ));
    }
    let selected = |reason: &str| {
        diagnostic_objects
            .iter()
            .filter(|diagnostic| value(diagnostic, "reason_code").string_value() == Some(reason))
            .collect::<Vec<_>>()
    };
    let aggregates = selected("package_verified");
    let locks = selected("package_lock_checked");
    let modules = selected("module_verified");
    let process_memo = selected("process_memo_summary");
    let decode_cache = selected("decode_cache_summary");
    if aggregates.len() != 1 {
        return Err(ReleaseManifestValidationError::new(
            "command_result must contain one package_verified diagnostic",
        ));
    }
    if locks.len() != 1 {
        return Err(ReleaseManifestValidationError::new(
            "command_result must contain one package_lock_checked diagnostic",
        ));
    }

    let aggregate = aggregates[0];
    let mut aggregate_fields = vec![
        "kind",
        "reason_code",
        "severity",
        "field",
        "actual_value",
        "checker",
    ];
    if external.is_some() {
        aggregate_fields.push("path");
    }
    if !exact_fields(aggregate, &aggregate_fields) {
        return Err(ReleaseManifestValidationError::new(
            "package_verified diagnostic has an unexpected shape",
        ));
    }
    if value(aggregate, "kind").string_value() != Some(kind)
        || value(aggregate, "field").string_value() != Some("verdict_source")
        || value(aggregate, "checker").string_value() != Some(checker)
    {
        return Err(ReleaseManifestValidationError::new(
            "package_verified diagnostic disagrees with checker identity",
        ));
    }
    if let Some(external) = external {
        if value(aggregate, "path").string_value()
            != value(external, "runner_policy_path").string_value()
        {
            return Err(ReleaseManifestValidationError::new(
                "external aggregate path disagrees with runner policy path",
            ));
        }
    }
    let local_fragment = if external.is_some() {
        ""
    } else {
        ";locally_accelerated=false"
    };
    let prefix = format!(
        "mode={result_mode};verdict_source={checker};reference_checker_verdict={reference_verdict}{local_fragment};modules="
    );
    let actual_value = require_text(
        value(aggregate, "actual_value"),
        "package_verified.actual_value",
    )?;
    let Some(module_count_text) = actual_value.strip_prefix(&prefix) else {
        return Err(ReleaseManifestValidationError::new(
            "package_verified diagnostic has invalid aggregate evidence",
        ));
    };
    if module_count_text.is_empty() || !module_count_text.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(ReleaseManifestValidationError::new(
            "package_verified diagnostic has invalid aggregate evidence",
        ));
    }
    let normalized = module_count_text.trim_start_matches('0');
    let normalized = if normalized.is_empty() {
        "0"
    } else {
        normalized
    };
    if normalized == "0" || normalized != modules.len().to_string() {
        return Err(ReleaseManifestValidationError::new(
            "package_verified module count disagrees with module diagnostics",
        ));
    }

    let lock = locks[0];
    if !exact_fields(
        lock,
        &["kind", "reason_code", "severity", "field", "actual_value"],
    ) {
        return Err(ReleaseManifestValidationError::new(
            "package_lock_checked diagnostic has an unexpected shape",
        ));
    }
    if value(lock, "kind").string_value() != Some("PackageLock")
        || value(lock, "field").string_value() != Some("package_lock")
    {
        return Err(ReleaseManifestValidationError::new(
            "package_lock_checked diagnostic has invalid identity",
        ));
    }
    let expected_provenance = format!(
        "mode=checked;hash={}",
        require_text(
            value(verification, "package_lock_sha256"),
            "verification.package_lock_sha256",
        )?
    );
    if value(lock, "actual_value").string_value() != Some(expected_provenance.as_str()) {
        return Err(ReleaseManifestValidationError::new(
            "package_lock_checked hash disagrees with package_lock_sha256",
        ));
    }

    let mut module_names = BTreeSet::new();
    let mut module_paths = BTreeSet::new();
    for module in &modules {
        if !exact_fields(
            module,
            &[
                "kind",
                "reason_code",
                "severity",
                "module",
                "path",
                "field",
                "expected_value",
                "actual_value",
                "checker",
            ],
        ) {
            return Err(ReleaseManifestValidationError::new(
                "module_verified diagnostic has an unexpected shape",
            ));
        }
        let module_name = require_text(value(module, "module"), "module_verified.module")?;
        let module_path = require_locator(value(module, "path"), "module_verified.path")?;
        if !module_names.insert(module_name) || !module_paths.insert(module_path) {
            return Err(ReleaseManifestValidationError::new(
                "command_result contains duplicate module verification evidence",
            ));
        }
        let expected_value = if external.is_some() {
            "checked"
        } else {
            "passed"
        };
        let actual_value = if external.is_some() {
            "checked"
        } else {
            "status=passed;evidence=live-checker;proof_evidence=true"
        };
        if value(module, "kind").string_value() != Some(kind)
            || value(module, "field").string_value() != Some("status")
            || value(module, "expected_value").string_value() != Some(expected_value)
            || value(module, "actual_value").string_value() != Some(actual_value)
            || value(module, "checker").string_value() != Some(checker)
        {
            return Err(ReleaseManifestValidationError::new(
                "module_verified diagnostic is not live checker evidence",
            ));
        }
    }

    let expected_telemetry_count =
        usize::from(result.contains_key("timings") && external.is_none());
    if process_memo.len() != expected_telemetry_count {
        return Err(ReleaseManifestValidationError::new(
            "command_result process_memo_summary diagnostics disagree with timing mode",
        ));
    }
    if decode_cache.len() != expected_telemetry_count {
        return Err(ReleaseManifestValidationError::new(
            "command_result decode_cache_summary diagnostics disagree with timing mode",
        ));
    }
    if let Some(diagnostic) = process_memo.first() {
        if !exact_fields(
            diagnostic,
            &["kind", "reason_code", "severity", "field", "actual_value"],
        ) {
            return Err(ReleaseManifestValidationError::new(
                "process_memo_summary diagnostic has an unexpected shape",
            ));
        }
        if value(diagnostic, "kind").string_value() != Some("GeneratedArtifact")
            || value(diagnostic, "field").string_value() != Some("process_memo")
            || !value(diagnostic, "actual_value")
                .string_value()
                .is_some_and(process_memo_telemetry_is_valid)
        {
            return Err(ReleaseManifestValidationError::new(
                "process_memo_summary diagnostic is invalid telemetry",
            ));
        }
    }
    if let Some(diagnostic) = decode_cache.first() {
        if !exact_fields(
            diagnostic,
            &["kind", "reason_code", "severity", "field", "actual_value"],
        ) {
            return Err(ReleaseManifestValidationError::new(
                "decode_cache_summary diagnostic has an unexpected shape",
            ));
        }
        if value(diagnostic, "kind").string_value() != Some("GeneratedArtifact")
            || value(diagnostic, "field").string_value() != Some("decode_cache")
            || !value(diagnostic, "actual_value")
                .string_value()
                .is_some_and(decode_cache_telemetry_is_valid)
        {
            return Err(ReleaseManifestValidationError::new(
                "decode_cache_summary diagnostic is invalid telemetry",
            ));
        }
    }

    let artifacts = require_array(
        value(result, "artifacts"),
        "verification.command_result.artifacts",
    )?;
    if external.is_none() {
        if !artifacts.is_empty() {
            return Err(ReleaseManifestValidationError::new(
                "in-process command_result must not contain checker artifacts",
            ));
        }
    } else {
        let mut paths = BTreeSet::new();
        if artifacts.len() != modules.len() {
            return Err(ReleaseManifestValidationError::new(
                "external command_result checker artifacts disagree with modules",
            ));
        }
        for (index, artifact) in artifacts.iter().enumerate() {
            let object = require_object(
                artifact,
                &format!("verification.command_result.artifacts[{index}]"),
            )?;
            if value(&object, "kind").string_value() != Some("machine_check_result") {
                return Err(ReleaseManifestValidationError::new(
                    "external command_result checker artifacts disagree with modules",
                ));
            }
            let path = require_text(value(&object, "path"), "artifact.path")?;
            if !paths.insert(path) {
                return Err(ReleaseManifestValidationError::new(
                    "external command_result contains duplicate checker artifacts",
                ));
            }
        }
    }
    Ok(())
}

fn validate_verification(
    value_: &JsonValue<'_>,
    generated_hashes: &BTreeMap<String, String>,
    package_root: &str,
) -> Result<(), ReleaseManifestValidationError> {
    let verification = require_object(value_, "verification")?;
    require_fields(&verification, VERIFICATION_FIELDS, "verification", &[])?;
    if value(&verification, "package_lock_mode").string_value() != Some("checked") {
        return Err(ReleaseManifestValidationError::new(
            "verification.package_lock_mode must be 'checked'",
        ));
    }
    let package_lock_path = require_locator(
        value(&verification, "package_lock_path"),
        "verification.package_lock_path",
    )?;
    let expected_lock_path = format!("{package_root}/{PACKAGE_LOCK_RELATIVE_PATH}");
    if package_lock_path != expected_lock_path {
        return Err(ReleaseManifestValidationError::new(format!(
            "verification.package_lock_path must be derived from package_root: '{expected_lock_path}'"
        )));
    }
    let lock_digest = verification_hash(
        value(&verification, "package_lock_sha256"),
        "verification.package_lock_sha256",
    )?;
    if generated_hashes
        .get(&expected_lock_path)
        .map(String::as_str)
        != Some(lock_digest)
    {
        return Err(ReleaseManifestValidationError::new(
            "package lock hash disagrees with generated_files",
        ));
    }

    let checker_mode = value(&verification, "checker_mode")
        .string_value()
        .unwrap_or_default();
    if !matches!(checker_mode, "reference" | "fast" | "external") {
        return Err(ReleaseManifestValidationError::new(
            "verification.checker_mode is unsupported",
        ));
    }
    require_text(
        value(&verification, "verdict_source"),
        "verification.verdict_source",
    )?;
    if !matches!(
        value(&verification, "npa_core_source_kind").string_value(),
        Some("aggregate" | "standalone")
    ) {
        return Err(ReleaseManifestValidationError::new(
            "verification.npa_core_source_kind is unsupported",
        ));
    }
    require_matching_text(
        value(&verification, "npa_core_checkout_revision"),
        "verification.npa_core_checkout_revision",
        |text| require_lower_hex(text, 40),
    )?;
    require_matching_text(
        value(&verification, "npa_core_tree_hash"),
        "verification.npa_core_tree_hash",
        |text| require_lower_hex(text, 40) || require_lower_hex(text, 64),
    )?;
    let npa_cli_version = require_matching_text(
        value(&verification, "npa_cli_crate_version"),
        "verification.npa_cli_crate_version",
        cli_version_is_valid,
    )?;
    let cargo_manifest_path = require_locator(
        value(&verification, "cargo_manifest_path"),
        "verification.cargo_manifest_path",
    )?;
    if cargo_manifest_path.rsplit('/').next() != Some("Cargo.toml") {
        return Err(ReleaseManifestValidationError::new(
            "verification.cargo_manifest_path must name Cargo.toml",
        ));
    }
    let cargo_lock_path = require_locator(
        value(&verification, "cargo_lock_path"),
        "verification.cargo_lock_path",
    )?;
    if cargo_lock_path.rsplit('/').next() != Some("Cargo.lock") {
        return Err(ReleaseManifestValidationError::new(
            "verification.cargo_lock_path must name Cargo.lock",
        ));
    }
    verification_hash(
        value(&verification, "cargo_lock_sha256"),
        "verification.cargo_lock_sha256",
    )?;
    require_text(
        value(&verification, "rust_toolchain"),
        "verification.rust_toolchain",
    )?;
    require_matching_text(
        value(&verification, "rust_target"),
        "verification.rust_target",
        rust_target_is_valid,
    )?;
    require_matching_text(
        value(&verification, "cargo_profile"),
        "verification.cargo_profile",
        profile_is_valid,
    )?;
    if value(&verification, "host_executable_name").string_value() != Some("npa") {
        return Err(ReleaseManifestValidationError::new(
            "verification.host_executable_name is unsupported",
        ));
    }
    verification_hash(
        value(&verification, "host_executable_sha256"),
        "verification.host_executable_sha256",
    )?;

    let external =
        validate_external_identity(value(&verification, "external_checker"), checker_mode)?;
    let result =
        validate_command_result_shape(value(&verification, "command_result"), npa_cli_version)?;
    validate_result_agreement(&verification, &result, external.as_ref())?;
    validate_recorded_command(&verification, &result, external.as_ref())
}

fn validate_manifest(
    value_: &JsonValue<'_>,
    require_v0_2: bool,
) -> Result<ReleaseManifestValidation, ReleaseManifestValidationError> {
    let root = require_object(value_, "manifest")?;
    match root.get("schema").and_then(|value| value.string_value()) {
        Some(V0_1_SCHEMA) => {
            require_fields(&root, BASE_FIELDS, "manifest", &[])?;
            validate_retained_manifest(&root)?;
            if require_v0_2 {
                return Err(ReleaseManifestValidationError::new(
                    "historical v0.1 evidence does not satisfy --require-v0.2",
                ));
            }
            Ok(ReleaseManifestValidation {
                input_schema: V0_1_SCHEMA,
                evidence_classification: "historical-v0.1",
            })
        }
        Some(V0_2_SCHEMA) => {
            let mut required = BASE_FIELDS.to_vec();
            required.push("verification");
            require_fields(&root, &required, "manifest", &[])?;
            let generated_hashes = validate_retained_manifest(&root)?;
            let package_root = require_text(value(&root, "package_root"), "package_root")?;
            validate_verification(
                value(&root, "verification"),
                &generated_hashes,
                package_root,
            )?;
            Ok(ReleaseManifestValidation {
                input_schema: V0_2_SCHEMA,
                evidence_classification: "checked-v0.2",
            })
        }
        _ => Err(ReleaseManifestValidationError::new(
            "manifest.schema is unsupported",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::{shell_words, validate_timestamp, JsonDocument};

    #[test]
    fn shell_words_support_quotes_and_escapes_without_evaluation() {
        assert_eq!(
            shell_words("cargo run --manifest-path 'core path/Cargo.toml' -- --root proof\\ root")
                .expect("shell words"),
            [
                "cargo",
                "run",
                "--manifest-path",
                "core path/Cargo.toml",
                "--",
                "--root",
                "proof root",
            ]
        );
        assert_eq!(
            shell_words(r#"cargo "proofs\q""#).expect("double-quoted backslash"),
            ["cargo", r"proofs\q"]
        );
    }

    #[test]
    fn timestamp_validation_checks_calendar_dates() {
        let valid = JsonDocument::parse("\"2024-02-29T23:59:59Z\"").expect("valid JSON");
        validate_timestamp(valid.root(), "timestamp").expect("valid leap-day timestamp");
        let invalid = JsonDocument::parse("\"2023-02-29T00:00:00Z\"").expect("valid JSON");
        assert!(validate_timestamp(invalid.root(), "timestamp").is_err());
    }
}

//! Offline generated-artifact release-manifest validation.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use npa_api::{
    JsonDocument, JsonValue, JsonValueKind, PerformanceMeasurementLabel,
    PERFORMANCE_CANDIDATE_DETAIL_LIMIT, PERFORMANCE_DECLARATION_DETAIL_LIMIT,
    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2,
    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3, PERFORMANCE_MODULE_DETAIL_LIMIT,
    PERFORMANCE_WORKER_DETAIL_LIMIT,
};

const V0_1_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.1";
const V0_2_SCHEMA: &str = "npa.generated_artifact_release_manifest.v0.2";
const VALIDATION_SCHEMA: &str = "npa.generated_artifact_release_manifest.validation.v0.1";
const COMMAND_RESULT_SCHEMA_V0_1: &str = "npa.package.command_result.v0.1";
const COMMAND_RESULT_SCHEMA_V0_2: &str = "npa.package.command_result.v0.2";
const COMMAND_RESULT_SCHEMA_V0_3: &str = "npa.package.command_result.v0.3";
const COMMAND_RESULT_SCHEMA_V0_4: &str = "npa.package.command_result.v0.4";
const KERNEL_FUEL_DIAGNOSTIC_SCHEMA_V0_1: &str = "npa.kernel-fuel-diagnostic.v0.1";
const TIMINGS_SCHEMA_V0_1: &str = "npa.package.timings.v0.1";
const TIMINGS_SCHEMA_V0_2: &str = "npa.package.timings.v0.2";
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
const DIAGNOSTIC_OPTIONAL_FIELDS_V0_4: &[&str] = &[
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
    "kernel_fuel",
];

const KERNEL_WORK_FIELDS: &[&str; 10] = &[
    "check_calls",
    "infer_calls",
    "whnf_calls",
    "defeq_calls",
    "quick_equality_hits",
    "beta_steps",
    "delta_steps",
    "iota_steps",
    "zeta_steps",
    "physical_reductions",
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
        && matches!(fields[1], "3" | "4" | "5" | "6" | "7" | "8")
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
    if version.starts_with("0.8.") {
        COMMAND_RESULT_SCHEMA_V0_4
    } else if version.starts_with("0.6.") || version.starts_with("0.7.") {
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
        if matches!(
            schema,
            COMMAND_RESULT_SCHEMA_V0_3 | COMMAND_RESULT_SCHEMA_V0_4
        ) {
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

#[derive(Clone, Copy)]
struct ValidatedKernelOperationFuel {
    spent: u64,
    overflowed: bool,
}

#[derive(Clone, Copy)]
struct ValidatedKernelFuelDomain {
    calls: u64,
    exhausted_operation_fuel: u64,
    overflowed: bool,
}

#[derive(Clone, Copy)]
struct ValidatedKernelWork {
    counters: [u64; KERNEL_WORK_FIELDS.len()],
    overflowed: bool,
}

fn validate_kernel_operation_fuel(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<ValidatedKernelOperationFuel, ReleaseManifestValidationError> {
    let fuel = require_object(raw, where_)?;
    require_fields(
        &fuel,
        &["budget", "spent", "remaining", "exhausted", "overflowed"],
        where_,
        &[],
    )?;
    let budget = require_measurement_u64(value(&fuel, "budget"), &format!("{where_}.budget"))?;
    let spent = require_measurement_u64(value(&fuel, "spent"), &format!("{where_}.spent"))?;
    let remaining =
        require_measurement_u64(value(&fuel, "remaining"), &format!("{where_}.remaining"))?;
    if !require_bool(value(&fuel, "exhausted"), &format!("{where_}.exhausted"))? {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.exhausted must be true"
        )));
    }
    let overflowed = require_bool(value(&fuel, "overflowed"), &format!("{where_}.overflowed"))?;
    if !overflowed && spent.checked_add(remaining) != Some(budget) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} spent + remaining must equal budget"
        )));
    }
    Ok(ValidatedKernelOperationFuel { spent, overflowed })
}

fn validate_kernel_fuel_domain(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<ValidatedKernelFuelDomain, ReleaseManifestValidationError> {
    let fuel = require_object(raw, where_)?;
    require_fields(
        &fuel,
        &[
            "calls",
            "logical_spent",
            "successful_operation_fuel",
            "exhausted_operation_fuel",
            "overflowed",
        ],
        where_,
        &[],
    )?;
    let calls = require_measurement_u64(value(&fuel, "calls"), &format!("{where_}.calls"))?;
    let logical_spent = require_measurement_u64(
        value(&fuel, "logical_spent"),
        &format!("{where_}.logical_spent"),
    )?;
    let successful_operation_fuel = require_measurement_u64(
        value(&fuel, "successful_operation_fuel"),
        &format!("{where_}.successful_operation_fuel"),
    )?;
    let exhausted_operation_fuel = require_measurement_u64(
        value(&fuel, "exhausted_operation_fuel"),
        &format!("{where_}.exhausted_operation_fuel"),
    )?;
    let overflowed = require_bool(value(&fuel, "overflowed"), &format!("{where_}.overflowed"))?;
    if !overflowed
        && successful_operation_fuel.checked_add(exhausted_operation_fuel) != Some(logical_spent)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} operation fuel totals must equal logical_spent"
        )));
    }
    Ok(ValidatedKernelFuelDomain {
        calls,
        exhausted_operation_fuel,
        overflowed,
    })
}

fn validate_kernel_fuel_totals(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<(ValidatedKernelFuelDomain, ValidatedKernelFuelDomain), ReleaseManifestValidationError>
{
    let fuel = require_object(raw, where_)?;
    require_fields(&fuel, &["whnf", "conversion"], where_, &[])?;
    Ok((
        validate_kernel_fuel_domain(value(&fuel, "whnf"), &format!("{where_}.whnf"))?,
        validate_kernel_fuel_domain(value(&fuel, "conversion"), &format!("{where_}.conversion"))?,
    ))
}

fn validate_kernel_work(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<ValidatedKernelWork, ReleaseManifestValidationError> {
    let work = require_object(raw, where_)?;
    let mut required = KERNEL_WORK_FIELDS.to_vec();
    required.push("overflowed");
    require_fields(&work, &required, where_, &[])?;
    let mut counters = [0_u64; KERNEL_WORK_FIELDS.len()];
    for (index, field) in KERNEL_WORK_FIELDS.iter().enumerate() {
        counters[index] =
            require_measurement_u64(value(&work, field), &format!("{where_}.{field}"))?;
    }
    let overflowed = require_bool(value(&work, "overflowed"), &format!("{where_}.overflowed"))?;
    if !overflowed {
        let reductions = counters[5]
            .checked_add(counters[6])
            .and_then(|sum| sum.checked_add(counters[7]))
            .and_then(|sum| sum.checked_add(counters[8]));
        if reductions != Some(counters[9]) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.physical_reductions must equal beta + delta + iota + zeta"
            )));
        }
    }
    Ok(ValidatedKernelWork {
        counters,
        overflowed,
    })
}

fn validate_kernel_hotset(
    raw: &JsonValue<'_>,
    where_: &str,
    declaration_delta_steps: u64,
    declaration_work_overflowed: bool,
) -> Result<bool, ReleaseManifestValidationError> {
    let summary = require_object(raw, where_)?;
    require_fields(
        &summary,
        &[
            "retained_names",
            "capacity",
            "entries",
            "emitted",
            "entry_limit",
            "unretained_name_observations",
            "overlong_name_observations",
            "output_truncated",
            "overflowed",
        ],
        where_,
        &[],
    )?;
    let retained_names = require_measurement_u64(
        value(&summary, "retained_names"),
        &format!("{where_}.retained_names"),
    )?;
    let capacity =
        require_measurement_u64(value(&summary, "capacity"), &format!("{where_}.capacity"))?;
    let emitted =
        require_measurement_u64(value(&summary, "emitted"), &format!("{where_}.emitted"))?;
    let entry_limit = require_measurement_u64(
        value(&summary, "entry_limit"),
        &format!("{where_}.entry_limit"),
    )?;
    let unretained = require_measurement_u64(
        value(&summary, "unretained_name_observations"),
        &format!("{where_}.unretained_name_observations"),
    )?;
    let overlong = require_measurement_u64(
        value(&summary, "overlong_name_observations"),
        &format!("{where_}.overlong_name_observations"),
    )?;
    let output_truncated = require_bool(
        value(&summary, "output_truncated"),
        &format!("{where_}.output_truncated"),
    )?;
    let overflowed = require_bool(
        value(&summary, "overflowed"),
        &format!("{where_}.overflowed"),
    )?;
    if capacity != npa_kernel::KERNEL_DELTA_HOTSET_CAPACITY as u64
        || retained_names > capacity
        || entry_limit != npa_kernel::KERNEL_DELTA_HOTSET_ENTRY_LIMIT as u64
        || emitted > entry_limit
        || (unretained > 0 && retained_names != capacity)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} disagrees with bounded hotset limits"
        )));
    }

    let entries = require_array(value(&summary, "entries"), &format!("{where_}.entries"))?;
    if emitted != u64::try_from(entries.len()).unwrap_or(u64::MAX)
        || entries.len() > npa_kernel::KERNEL_DELTA_HOTSET_ENTRY_LIMIT
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.emitted disagrees with entries or entry_limit"
        )));
    }
    let mut names = BTreeSet::new();
    let mut previous = None::<(u64, String)>;
    let mut ordinary_entries = 0_u64;
    let mut ordinary_count_sum = 0_u64;
    let mut synthetic_present = false;
    for (index, raw_entry) in entries.iter().enumerate() {
        let entry_where = format!("{where_}.entries[{index}]");
        let entry = require_object(raw_entry, &entry_where)?;
        require_fields(&entry, &["constant", "count"], &entry_where, &[])?;
        let constant = require_text(
            value(&entry, "constant"),
            &format!("{entry_where}.constant"),
        )?;
        let count =
            require_measurement_u64(value(&entry, "count"), &format!("{entry_where}.count"))?;
        if count == 0 {
            return Err(ReleaseManifestValidationError::new(format!(
                "{entry_where}.count must be positive"
            )));
        }
        if !names.insert(constant) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{entry_where}.constant is duplicated"
            )));
        }
        if previous
            .as_ref()
            .is_some_and(|(previous_count, previous_name)| {
                *previous_count < count
                    || (*previous_count == count && previous_name.as_str() >= constant)
            })
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.entries are not in descending-count/ascending-name order"
            )));
        }
        previous = Some((count, constant.to_owned()));
        if constant == npa_kernel::KERNEL_DELTA_OVERLONG_NAME {
            synthetic_present = true;
            if count != overlong {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{entry_where} synthetic count disagrees with overlong observations"
                )));
            }
        } else {
            if constant.len() > npa_kernel::KERNEL_DELTA_NAME_BYTE_LIMIT
                || !npa_kernel::is_canonical_dotted_name(constant)
            {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{entry_where}.constant is not a bounded canonical name"
                )));
            }
            ordinary_entries = ordinary_entries.checked_add(1).ok_or_else(|| {
                ReleaseManifestValidationError::new(format!(
                    "{where_} ordinary entry count overflowed"
                ))
            })?;
            ordinary_count_sum = match ordinary_count_sum.checked_add(count) {
                Some(sum) => sum,
                None if overflowed => u64::MAX,
                None => {
                    return Err(ReleaseManifestValidationError::new(format!(
                        "{where_} ordinary entry counts overflowed without overflow flag"
                    )))
                }
            };
        }
    }
    if ordinary_entries > retained_names || (synthetic_present && overlong == 0) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.entries disagree with retained or overlong names"
        )));
    }
    let candidate_count = retained_names + u64::from(overlong > 0);
    if emitted > candidate_count || output_truncated != (emitted < candidate_count) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.output_truncated disagrees with emitted candidates"
        )));
    }
    if !overflowed && !declaration_work_overflowed {
        let observed = ordinary_count_sum
            .checked_add(unretained)
            .and_then(|sum| sum.checked_add(overlong))
            .ok_or_else(|| {
                ReleaseManifestValidationError::new(format!(
                    "{where_} observation counts overflowed without overflow flag"
                ))
            })?;
        if observed > declaration_delta_steps
            || (!output_truncated && observed != declaration_delta_steps)
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_} observations disagree with declaration delta_steps"
            )));
        }
    }
    Ok(overflowed)
}

fn validate_kernel_fuel_diagnostic(
    raw: &JsonValue<'_>,
    where_: &str,
    conversion: Option<&JsonValue<'_>>,
) -> Result<(), ReleaseManifestValidationError> {
    let diagnostic = require_object(raw, where_)?;
    require_fields(
        &diagnostic,
        &[
            "schema",
            "trusted",
            "proof_evidence",
            "subsystem",
            "resource",
            "failed_operation",
            "declaration",
            "comparison_path",
            "retained_delta_constants",
            "overflowed",
        ],
        where_,
        &[],
    )?;
    if value(&diagnostic, "schema").string_value() != Some(KERNEL_FUEL_DIAGNOSTIC_SCHEMA_V0_1) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.schema is unsupported"
        )));
    }
    if require_bool(value(&diagnostic, "trusted"), &format!("{where_}.trusted"))?
        || require_bool(
            value(&diagnostic, "proof_evidence"),
            &format!("{where_}.proof_evidence"),
        )?
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} must be untrusted and not proof evidence"
        )));
    }
    if value(&diagnostic, "subsystem").string_value() != Some("fast_kernel") {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.subsystem is unsupported"
        )));
    }
    let resource = require_text(
        value(&diagnostic, "resource"),
        &format!("{where_}.resource"),
    )?;
    if !matches!(resource, "conversion" | "whnf") {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.resource is unsupported"
        )));
    }

    let failed_where = format!("{where_}.failed_operation");
    let failed = require_object(value(&diagnostic, "failed_operation"), &failed_where)?;
    require_fields(&failed, &["fuel", "work"], &failed_where, &[])?;
    let operation_fuel =
        validate_kernel_operation_fuel(value(&failed, "fuel"), &format!("{failed_where}.fuel"))?;
    let operation_work =
        validate_kernel_work(value(&failed, "work"), &format!("{failed_where}.work"))?;

    let declaration_where = format!("{where_}.declaration");
    let declaration = require_object(value(&diagnostic, "declaration"), &declaration_where)?;
    require_fields(
        &declaration,
        &["fuel", "work", "overflowed"],
        &declaration_where,
        &[],
    )?;
    let (whnf_fuel, conversion_fuel) = validate_kernel_fuel_totals(
        value(&declaration, "fuel"),
        &format!("{declaration_where}.fuel"),
    )?;
    let declaration_work = validate_kernel_work(
        value(&declaration, "work"),
        &format!("{declaration_where}.work"),
    )?;
    let declaration_overflowed = require_bool(
        value(&declaration, "overflowed"),
        &format!("{declaration_where}.overflowed"),
    )?;
    let expected_declaration_overflowed =
        declaration_work.overflowed || whnf_fuel.overflowed || conversion_fuel.overflowed;
    if declaration_overflowed != expected_declaration_overflowed {
        return Err(ReleaseManifestValidationError::new(format!(
            "{declaration_where}.overflowed disagrees with declaration counters"
        )));
    }
    if !operation_work.overflowed && !declaration_work.overflowed {
        for (index, field) in KERNEL_WORK_FIELDS.iter().enumerate() {
            if operation_work.counters[index] > declaration_work.counters[index] {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{failed_where}.work.{field} exceeds declaration work"
                )));
            }
        }
    }

    let path_where = format!("{where_}.comparison_path");
    let path = require_object(value(&diagnostic, "comparison_path"), &path_where)?;
    require_fields(&path, &["steps", "truncated"], &path_where, &[])?;
    let steps = require_array(value(&path, "steps"), &format!("{path_where}.steps"))?;
    if steps.len() > npa_kernel::KERNEL_COMPARISON_PATH_LIMIT {
        return Err(ReleaseManifestValidationError::new(format!(
            "{path_where}.steps exceeds the schema limit"
        )));
    }
    for (index, raw_step) in steps.iter().enumerate() {
        if !matches!(
            raw_step.string_value(),
            Some(
                "app_function"
                    | "app_argument"
                    | "pi_domain"
                    | "pi_body"
                    | "lambda_domain"
                    | "lambda_body"
                    | "whnf_left"
                    | "whnf_right"
            )
        ) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{path_where}.steps[{index}] is unsupported"
            )));
        }
    }
    let path_truncated = require_bool(
        value(&path, "truncated"),
        &format!("{path_where}.truncated"),
    )?;

    let selected_fuel = if resource == "conversion" {
        conversion_fuel
    } else {
        whnf_fuel
    };
    let other_fuel = if resource == "conversion" {
        whnf_fuel
    } else {
        conversion_fuel
    };
    if selected_fuel.calls == 0 {
        return Err(ReleaseManifestValidationError::new(format!(
            "{declaration_where}.fuel.{resource}.calls must be positive"
        )));
    }
    if !operation_fuel.overflowed
        && !whnf_fuel.overflowed
        && !conversion_fuel.overflowed
        && (selected_fuel.exhausted_operation_fuel != operation_fuel.spent
            || other_fuel.exhausted_operation_fuel != 0)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{declaration_where}.fuel disagrees with failed-operation resource fuel"
        )));
    }
    match resource {
        "conversion" => {
            let conversion = conversion.ok_or_else(|| {
                ReleaseManifestValidationError::new(format!(
                    "{where_} conversion resource requires a conversion sibling"
                ))
            })?;
            let conversion = require_object(conversion, &format!("{where_} sibling conversion"))?;
            if value(&conversion, "outcome").string_value() != Some("fuel_exhausted") {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{where_} conversion resource requires outcome fuel_exhausted"
                )));
            }
        }
        "whnf" => {
            if conversion.is_some() || !steps.is_empty() || path_truncated {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{where_} WHNF resource requires no conversion and an empty non-truncated path"
                )));
            }
        }
        _ => unreachable!("resource vocabulary was checked"),
    }

    let hotset_overflowed =
        if value(&diagnostic, "retained_delta_constants").kind() == JsonValueKind::Null {
            false
        } else {
            validate_kernel_hotset(
                value(&diagnostic, "retained_delta_constants"),
                &format!("{where_}.retained_delta_constants"),
                declaration_work.counters[6],
                declaration_work.overflowed,
            )?
        };
    let overflowed = require_bool(
        value(&diagnostic, "overflowed"),
        &format!("{where_}.overflowed"),
    )?;
    let expected_overflowed = operation_fuel.overflowed
        || operation_work.overflowed
        || declaration_overflowed
        || hotset_overflowed;
    if overflowed != expected_overflowed {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.overflowed disagrees with nested overflow flags"
        )));
    }
    Ok(())
}

fn validate_accepted_kernel_measurement(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    let kernel = require_object(raw, where_)?;
    require_fields(
        &kernel,
        &[
            "subsystem",
            "outcome",
            "fuel",
            "work",
            "retained_delta_constants",
            "overflowed",
        ],
        where_,
        &[],
    )?;
    if value(&kernel, "subsystem").string_value() != Some("fast_kernel")
        || value(&kernel, "outcome").string_value() != Some("accepted")
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} has an unsupported subsystem or outcome"
        )));
    }
    let (whnf, conversion) =
        validate_kernel_fuel_totals(value(&kernel, "fuel"), &format!("{where_}.fuel"))?;
    let work = validate_kernel_work(value(&kernel, "work"), &format!("{where_}.work"))?;
    if value(&kernel, "retained_delta_constants").kind() == JsonValueKind::Null {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.retained_delta_constants must be present"
        )));
    }
    let hotset_overflowed = validate_kernel_hotset(
        value(&kernel, "retained_delta_constants"),
        &format!("{where_}.retained_delta_constants"),
        work.counters[6],
        work.overflowed,
    )?;
    let overflowed = require_bool(
        value(&kernel, "overflowed"),
        &format!("{where_}.overflowed"),
    )?;
    if overflowed
        != (whnf.overflowed || conversion.overflowed || work.overflowed || hotset_overflowed)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.overflowed disagrees with nested overflow flags"
        )));
    }
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
        Some(
            COMMAND_RESULT_SCHEMA_V0_1
                | COMMAND_RESULT_SCHEMA_V0_2
                | COMMAND_RESULT_SCHEMA_V0_3
                | COMMAND_RESULT_SCHEMA_V0_4
        )
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
        Some(COMMAND_RESULT_SCHEMA_V0_3) => DIAGNOSTIC_OPTIONAL_FIELDS_V0_3,
        _ => DIAGNOSTIC_OPTIONAL_FIELDS_V0_4,
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
        if diagnostic.contains_key("kernel_fuel") {
            validate_kernel_fuel_diagnostic(
                value(&diagnostic, "kernel_fuel"),
                &format!("{where_}.kernel_fuel"),
                diagnostic.get("conversion").copied(),
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
        let schema = value(&timings, "schema").string_value();
        if !matches!(schema, Some(TIMINGS_SCHEMA_V0_1 | TIMINGS_SCHEMA_V0_2)) {
            return Err(ReleaseManifestValidationError::new(
                "verification.command_result.timings has an invalid schema",
            ));
        }
        let v0_2 = schema == Some(TIMINGS_SCHEMA_V0_2);
        let required_v0_1 = ["schema", "mode", "unit", "proof_evidence", "build_evidence"];
        let required_v0_2 = [
            "schema",
            "mode",
            "unit",
            "proof_evidence",
            "build_evidence",
            "trusted",
            "measurements",
        ];
        let required: &[&str] = if v0_2 { &required_v0_2 } else { &required_v0_1 };
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
        if value(&timings, "unit").string_value() != Some("ms") {
            return Err(ReleaseManifestValidationError::new(
                "verification.command_result.timings has an invalid schema or unit",
            ));
        }
        let timing_mode = require_text(
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
        if v0_2 {
            if require_bool(
                value(&timings, "trusted"),
                "verification.command_result.timings.trusted",
            )? {
                return Err(ReleaseManifestValidationError::new(
                    "timings must be untrusted",
                ));
            }
            validate_performance_measurements(value(&timings, "measurements"), timing_mode)?;
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

fn validate_performance_measurements(
    raw: &JsonValue<'_>,
    expected_mode: &str,
) -> Result<(), ReleaseManifestValidationError> {
    const WHERE: &str = "verification.command_result.timings.measurements";
    let report = require_object(raw, WHERE)?;
    let (has_package_sharding_schema, has_declaration_kernel) =
        match value(&report, "schema").string_value() {
            Some(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1) => (false, false),
            Some(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2) => (true, false),
            Some(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3) => (true, true),
            _ => {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{WHERE}.schema is unsupported"
                )))
            }
        };
    let mut required_fields = vec![
        "schema",
        "trusted",
        "proof_evidence",
        "mode",
        "input_identity",
        "counters",
        "modules",
        "module_details",
        "declarations",
        "declaration_details",
        "candidates",
        "candidate_details",
        "workers",
        "worker_details",
        "detail_truncated",
        "overflowed",
        "clock",
    ];
    if has_package_sharding_schema {
        required_fields.extend_from_slice(&[
            "package_sharding",
            "package_layers",
            "package_layer_details",
            "package_shards",
            "package_shard_details",
        ]);
    }
    require_fields(&report, &required_fields, WHERE, &[])?;
    if require_bool(value(&report, "trusted"), &format!("{WHERE}.trusted"))?
        || require_bool(
            value(&report, "proof_evidence"),
            &format!("{WHERE}.proof_evidence"),
        )?
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{WHERE} must be untrusted and not proof evidence"
        )));
    }
    let mode = value(&report, "mode").string_value();
    if !matches!(mode, Some("summary" | "detailed")) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{WHERE}.mode is invalid"
        )));
    }
    if mode != Some(expected_mode) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{WHERE}.mode disagrees with verification.command_result.timings.mode"
        )));
    }
    if value(&report, "input_identity").kind() != JsonValueKind::Null {
        verification_hash(
            value(&report, "input_identity"),
            &format!("{WHERE}.input_identity"),
        )?;
    }
    require_bool(
        value(&report, "detail_truncated"),
        &format!("{WHERE}.detail_truncated"),
    )?;
    require_bool(value(&report, "overflowed"), &format!("{WHERE}.overflowed"))?;

    let mut labels = BTreeSet::new();
    let mut previous_label = None;
    for (index, raw_counter) in
        require_array(value(&report, "counters"), &format!("{WHERE}.counters"))?
            .iter()
            .enumerate()
    {
        let where_ = format!("{WHERE}.counters[{index}]");
        let counter = require_object(raw_counter, &where_)?;
        require_fields(&counter, &["label", "unit", "value"], &where_, &[])?;
        let label = require_text(value(&counter, "label"), &format!("{where_}.label"))?;
        if !labels.insert(label) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.label is duplicated"
            )));
        }
        if previous_label.is_some_and(|previous| previous >= label) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.label is not in canonical order"
            )));
        }
        previous_label = Some(label);
        let Some(expected) = PerformanceMeasurementLabel::ALL
            .iter()
            .copied()
            .find(|candidate| candidate.as_str() == label)
        else {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.label is unknown"
            )));
        };
        if !has_package_sharding_schema
            && expected == PerformanceMeasurementLabel::PackageAvoidedBaseContextCloneBytes
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.label is unavailable in {PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1}"
            )));
        }
        if value(&counter, "unit").string_value() != Some(expected.unit().as_str()) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.unit disagrees with its label"
            )));
        }
        require_measurement_u64(value(&counter, "value"), &format!("{where_}.value"))?;
    }

    let module_fields = [
        "module",
        "certificate_bytes",
        "declaration_count",
        "import_count",
        "checker_elapsed_ns",
    ];
    if has_package_sharding_schema {
        let mut fields = module_fields.to_vec();
        fields.push("package_sharding");
        validate_measurement_records_with_opaque(
            value(&report, "modules"),
            &format!("{WHERE}.modules"),
            &fields,
            &["module"],
            &["package_sharding"],
        )?;
    } else {
        validate_measurement_records(
            value(&report, "modules"),
            &format!("{WHERE}.modules"),
            &module_fields,
            &["module"],
        )?;
    }
    let modules = require_array(value(&report, "modules"), &format!("{WHERE}.modules"))?;
    let mut previous_module = None::<String>;
    for (index, module) in modules.iter().enumerate() {
        let object = require_object(module, &format!("{WHERE}.modules[{index}]"))?;
        let key = require_text(
            value(&object, "module"),
            &format!("{WHERE}.modules[{index}].module"),
        )?;
        if previous_module
            .as_deref()
            .is_some_and(|previous| previous >= key)
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.modules are not in canonical order"
            )));
        }
        previous_module = Some(key.to_owned());
        if has_package_sharding_schema {
            validate_package_module_sharding(
                value(&object, "package_sharding"),
                &format!("{WHERE}.modules[{index}].package_sharding"),
            )?;
        }
    }
    let mut declaration_fields = vec![
        "module",
        "declaration_index",
        "declaration",
        "term_nodes",
        "elaboration_elapsed_ns",
    ];
    if has_declaration_kernel {
        declaration_fields.push("kernel");
        validate_measurement_records_with_opaque(
            value(&report, "declarations"),
            &format!("{WHERE}.declarations"),
            &declaration_fields,
            &["module", "declaration"],
            &["kernel"],
        )?;
    } else {
        validate_measurement_records(
            value(&report, "declarations"),
            &format!("{WHERE}.declarations"),
            &declaration_fields,
            &["module", "declaration"],
        )?;
    }
    let declarations = require_array(
        value(&report, "declarations"),
        &format!("{WHERE}.declarations"),
    )?;
    let mut previous_declaration = None::<(String, u64, String)>;
    for (index, declaration) in declarations.iter().enumerate() {
        let where_ = format!("{WHERE}.declarations[{index}]");
        let object = require_object(declaration, &where_)?;
        let key = (
            require_text(value(&object, "module"), &format!("{where_}.module"))?.to_owned(),
            require_measurement_u64(
                value(&object, "declaration_index"),
                &format!("{where_}.declaration_index"),
            )?,
            require_text(
                value(&object, "declaration"),
                &format!("{where_}.declaration"),
            )?
            .to_owned(),
        );
        if previous_declaration
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.declarations are not in canonical order"
            )));
        }
        previous_declaration = Some(key);
        if has_declaration_kernel && value(&object, "kernel").kind() != JsonValueKind::Null {
            validate_accepted_kernel_measurement(
                value(&object, "kernel"),
                &format!("{where_}.kernel"),
            )?;
        }
    }
    validate_measurement_records(
        value(&report, "candidates"),
        &format!("{WHERE}.candidates"),
        &[
            "batch_index",
            "candidate_index",
            "validation_elapsed_ns",
            "execution_elapsed_ns",
            "outcome",
        ],
        &["outcome"],
    )?;
    let candidates = require_array(value(&report, "candidates"), &format!("{WHERE}.candidates"))?;
    let mut previous_candidate = None::<(u64, u64)>;
    for (index, candidate) in candidates.iter().enumerate() {
        let object = require_object(candidate, &format!("{WHERE}.candidates[{index}]"))?;
        if !matches!(
            value(&object, "outcome").string_value(),
            Some("accepted" | "rejected" | "not_evaluated")
        ) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.candidates[{index}].outcome is invalid"
            )));
        }
        let key = (
            require_measurement_u64(
                value(&object, "batch_index"),
                &format!("{WHERE}.candidates[{index}].batch_index"),
            )?,
            require_measurement_u64(
                value(&object, "candidate_index"),
                &format!("{WHERE}.candidates[{index}].candidate_index"),
            )?,
        );
        if previous_candidate.is_some_and(|previous| previous >= key) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.candidates are not in canonical order"
            )));
        }
        previous_candidate = Some(key);
    }
    validate_measurement_records(
        value(&report, "workers"),
        &format!("{WHERE}.workers"),
        &[
            "worker_index",
            "module_count",
            "certificate_bytes",
            "active_elapsed_ns",
            "idle_elapsed_ns",
        ],
        &[],
    )?;
    let workers = require_array(value(&report, "workers"), &format!("{WHERE}.workers"))?;
    let mut previous_worker = None;
    for (index, worker) in workers.iter().enumerate() {
        let object = require_object(worker, &format!("{WHERE}.workers[{index}]"))?;
        let key = require_measurement_u64(
            value(&object, "worker_index"),
            &format!("{WHERE}.workers[{index}].worker_index"),
        )?;
        if previous_worker.is_some_and(|previous| previous >= key) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.workers are not in canonical order"
            )));
        }
        previous_worker = Some(key);
    }
    let (package_layer_len, package_shard_len) = if has_package_sharding_schema {
        let has_package_sharding =
            validate_package_sharding_summary(value(&report, "package_sharding"), WHERE)?;
        let package_layers = require_array(
            value(&report, "package_layers"),
            &format!("{WHERE}.package_layers"),
        )?;
        let mut previous_layer = None;
        for (index, raw_layer) in package_layers.iter().enumerate() {
            let where_ = format!("{WHERE}.package_layers[{index}]");
            let layer = require_object(raw_layer, &where_)?;
            require_fields(
                &layer,
                &[
                    "layer_index",
                    "runnable_width",
                    "estimated_total_cost",
                    "estimated_max_shard_cost",
                    "requested_jobs",
                    "effective_jobs",
                    "reduction_reason",
                    "shared_base_context_bytes",
                    "per_worker_bytes",
                    "memory_budget_bytes",
                    "estimate_overflowed",
                    "elapsed_ns",
                ],
                &where_,
                &[],
            )?;
            let layer_index = require_measurement_u64(
                value(&layer, "layer_index"),
                &format!("{where_}.layer_index"),
            )?;
            if previous_layer.is_some_and(|previous| previous >= layer_index) {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{WHERE}.package_layers are not in canonical order"
                )));
            }
            previous_layer = Some(layer_index);
            for field in [
                "runnable_width",
                "estimated_total_cost",
                "estimated_max_shard_cost",
                "requested_jobs",
                "effective_jobs",
                "shared_base_context_bytes",
                "per_worker_bytes",
                "memory_budget_bytes",
                "elapsed_ns",
            ] {
                require_measurement_u64(value(&layer, field), &format!("{where_}.{field}"))?;
            }
            if require_measurement_u64(
                value(&layer, "memory_budget_bytes"),
                &format!("{where_}.memory_budget_bytes"),
            )? != 1_073_741_824
            {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{where_}.memory_budget_bytes disagrees with npa.fast-shard-memory.v1"
                )));
            }
            validate_fast_shard_reduction_reason(
                value(&layer, "reduction_reason"),
                &format!("{where_}.reduction_reason"),
            )?;
            require_bool(
                value(&layer, "estimate_overflowed"),
                &format!("{where_}.estimate_overflowed"),
            )?;
        }
        let package_shards = require_array(
            value(&report, "package_shards"),
            &format!("{WHERE}.package_shards"),
        )?;
        let mut previous_shard = None;
        for (index, raw_shard) in package_shards.iter().enumerate() {
            let where_ = format!("{WHERE}.package_shards[{index}]");
            let shard = require_object(raw_shard, &where_)?;
            require_fields(
                &shard,
                &[
                    "layer_index",
                    "shard_index",
                    "estimated_cost",
                    "artifact_bytes",
                    "member_count",
                    "active_elapsed_ns",
                    "estimate_overflowed",
                ],
                &where_,
                &[],
            )?;
            let key = (
                require_measurement_u64(
                    value(&shard, "layer_index"),
                    &format!("{where_}.layer_index"),
                )?,
                require_measurement_u64(
                    value(&shard, "shard_index"),
                    &format!("{where_}.shard_index"),
                )?,
            );
            if previous_shard.is_some_and(|previous| previous >= key) {
                return Err(ReleaseManifestValidationError::new(format!(
                    "{WHERE}.package_shards are not in canonical order"
                )));
            }
            previous_shard = Some(key);
            for field in [
                "estimated_cost",
                "artifact_bytes",
                "member_count",
                "active_elapsed_ns",
            ] {
                require_measurement_u64(value(&shard, field), &format!("{where_}.{field}"))?;
            }
            require_bool(
                value(&shard, "estimate_overflowed"),
                &format!("{where_}.estimate_overflowed"),
            )?;
        }
        if !has_package_sharding && (!package_layers.is_empty() || !package_shards.is_empty()) {
            return Err(ReleaseManifestValidationError::new(format!(
                "{WHERE}.package_sharding is required when package shard details are present"
            )));
        }
        (package_layers.len(), package_shards.len())
    } else {
        (0, 0)
    };
    let mut detail_families = vec![
        (
            "module_details",
            modules.len(),
            PERFORMANCE_MODULE_DETAIL_LIMIT,
        ),
        (
            "declaration_details",
            declarations.len(),
            PERFORMANCE_DECLARATION_DETAIL_LIMIT,
        ),
        (
            "candidate_details",
            candidates.len(),
            PERFORMANCE_CANDIDATE_DETAIL_LIMIT,
        ),
        (
            "worker_details",
            workers.len(),
            PERFORMANCE_WORKER_DETAIL_LIMIT,
        ),
    ];
    if has_package_sharding_schema {
        detail_families.extend_from_slice(&[
            (
                "package_layer_details",
                package_layer_len,
                PERFORMANCE_MODULE_DETAIL_LIMIT,
            ),
            (
                "package_shard_details",
                package_shard_len,
                PERFORMANCE_WORKER_DETAIL_LIMIT,
            ),
        ]);
    }
    let mut any_omitted = false;
    for (family, actual_len, limit) in detail_families {
        let omitted = validate_measurement_detail_counts(
            value(&report, family),
            &format!("{WHERE}.{family}"),
            actual_len,
            limit,
        )?;
        any_omitted |= omitted > 0;
    }
    if require_bool(
        value(&report, "detail_truncated"),
        &format!("{WHERE}.detail_truncated"),
    )? != any_omitted
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{WHERE}.detail_truncated disagrees with omitted detail counts"
        )));
    }
    if mode == Some("summary")
        && (!modules.is_empty()
            || !declarations.is_empty()
            || !candidates.is_empty()
            || !workers.is_empty()
            || package_layer_len != 0
            || package_shard_len != 0
            || any_omitted)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{WHERE} summary mode must not contain detail records"
        )));
    }
    let clock_where = format!("{WHERE}.clock");
    let clock = require_object(value(&report, "clock"), &clock_where)?;
    require_fields(
        &clock,
        &["source", "resolution_ns", "coarse_stage_reads"],
        &clock_where,
        &[],
    )?;
    if value(&clock, "source").string_value() != Some("std.monotonic.instant") {
        return Err(ReleaseManifestValidationError::new(format!(
            "{clock_where}.source is invalid"
        )));
    }
    for field in ["resolution_ns", "coarse_stage_reads"] {
        require_measurement_u64(value(&clock, field), &format!("{clock_where}.{field}"))?;
    }
    Ok(())
}

fn validate_package_module_sharding(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    if raw.kind() == JsonValueKind::Null {
        return Ok(());
    }
    let measurement = require_object(raw, where_)?;
    require_fields(
        &measurement,
        &[
            "cost_model",
            "artifact_bytes",
            "direct_import_count",
            "estimated_cost",
            "layer_index",
            "shard_index",
            "cost_overflowed",
            "critical_path",
        ],
        where_,
        &[],
    )?;
    if value(&measurement, "cost_model").string_value() != Some("npa.fast-shard-cost.v1") {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.cost_model is unsupported"
        )));
    }
    let artifact_bytes = require_measurement_u64(
        value(&measurement, "artifact_bytes"),
        &format!("{where_}.artifact_bytes"),
    )?;
    let direct_import_count = require_measurement_u64(
        value(&measurement, "direct_import_count"),
        &format!("{where_}.direct_import_count"),
    )?;
    let estimated_cost = require_measurement_u64(
        value(&measurement, "estimated_cost"),
        &format!("{where_}.estimated_cost"),
    )?;
    let layer_index = if value(&measurement, "layer_index").kind() == JsonValueKind::Null {
        None
    } else {
        Some(require_measurement_u64(
            value(&measurement, "layer_index"),
            &format!("{where_}.layer_index"),
        )?)
    };
    let shard_index = if value(&measurement, "shard_index").kind() == JsonValueKind::Null {
        None
    } else {
        Some(require_measurement_u64(
            value(&measurement, "shard_index"),
            &format!("{where_}.shard_index"),
        )?)
    };
    if shard_index.is_some() && layer_index.is_none() {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_}.shard_index requires layer_index"
        )));
    }
    let cost_overflowed = require_bool(
        value(&measurement, "cost_overflowed"),
        &format!("{where_}.cost_overflowed"),
    )?;
    require_bool(
        value(&measurement, "critical_path"),
        &format!("{where_}.critical_path"),
    )?;
    let (import_cost, multiply_overflowed) = direct_import_count
        .checked_mul(4_096)
        .map_or((u64::MAX, true), |cost| (cost, false));
    let (expected_cost, add_overflowed) = if multiply_overflowed {
        (u64::MAX, false)
    } else {
        artifact_bytes
            .checked_add(import_cost)
            .map_or((u64::MAX, true), |cost| (cost.max(1), false))
    };
    if estimated_cost != expected_cost || cost_overflowed != (multiply_overflowed || add_overflowed)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} disagrees with npa.fast-shard-cost.v1"
        )));
    }
    Ok(())
}

fn validate_package_sharding_summary(
    raw: &JsonValue<'_>,
    parent_where: &str,
) -> Result<bool, ReleaseManifestValidationError> {
    let where_ = format!("{parent_where}.package_sharding");
    if raw.kind() == JsonValueKind::Null {
        return Ok(false);
    }
    let measurement = require_object(raw, &where_)?;
    require_fields(
        &measurement,
        &[
            "cost_model",
            "memory_model",
            "import_weight",
            "memory_budget_bytes",
            "fixed_worker_bytes",
            "scratch_multiplier",
            "requested_jobs",
            "effective_jobs",
            "reduction_reason",
            "shared_base_context_bytes",
            "per_worker_bytes",
            "avoided_base_context_clone_bytes",
            "estimate_overflowed",
            "critical_path_cost",
            "critical_path_module_count",
            "critical_path_identity",
            "critical_path_checker_elapsed_ns",
            "barrier_elapsed_ns",
        ],
        &where_,
        &[],
    )?;
    if value(&measurement, "cost_model").string_value() != Some("npa.fast-shard-cost.v1")
        || value(&measurement, "memory_model").string_value() != Some("npa.fast-shard-memory.v1")
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} has an unsupported model identifier"
        )));
    }
    for (field, expected) in [
        ("import_weight", 4_096),
        ("memory_budget_bytes", 1_073_741_824),
        ("fixed_worker_bytes", 8_388_608),
        ("scratch_multiplier", 4),
    ] {
        if require_measurement_u64(value(&measurement, field), &format!("{where_}.{field}"))?
            != expected
        {
            return Err(ReleaseManifestValidationError::new(format!(
                "{where_}.{field} disagrees with the declared model identifier"
            )));
        }
    }
    for field in [
        "import_weight",
        "memory_budget_bytes",
        "fixed_worker_bytes",
        "scratch_multiplier",
        "requested_jobs",
        "effective_jobs",
        "shared_base_context_bytes",
        "per_worker_bytes",
        "avoided_base_context_clone_bytes",
        "critical_path_cost",
        "critical_path_module_count",
        "critical_path_checker_elapsed_ns",
        "barrier_elapsed_ns",
    ] {
        require_measurement_u64(value(&measurement, field), &format!("{where_}.{field}"))?;
    }
    validate_fast_shard_reduction_reason(
        value(&measurement, "reduction_reason"),
        &format!("{where_}.reduction_reason"),
    )?;
    require_bool(
        value(&measurement, "estimate_overflowed"),
        &format!("{where_}.estimate_overflowed"),
    )?;
    verification_hash(
        value(&measurement, "critical_path_identity"),
        &format!("{where_}.critical_path_identity"),
    )?;
    Ok(true)
}

fn validate_fast_shard_reduction_reason(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<(), ReleaseManifestValidationError> {
    if !matches!(
        raw.string_value(),
        Some("none" | "requested_one" | "runnable_width" | "memory_budget" | "estimate_overflow")
    ) {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} is invalid"
        )));
    }
    Ok(())
}

fn require_measurement_u64(
    raw: &JsonValue<'_>,
    where_: &str,
) -> Result<u64, ReleaseManifestValidationError> {
    let value = DecimalNat::parse(raw, where_)?;
    value.0.parse::<u64>().map_err(|_| {
        ReleaseManifestValidationError::new(format!("{where_} exceeds the u64 schema limit"))
    })
}

fn validate_measurement_detail_counts(
    raw: &JsonValue<'_>,
    where_: &str,
    actual_len: usize,
    limit: usize,
) -> Result<u64, ReleaseManifestValidationError> {
    let details = require_object(raw, where_)?;
    require_fields(&details, &["attempted", "retained", "omitted"], where_, &[])?;
    let attempted =
        require_measurement_u64(value(&details, "attempted"), &format!("{where_}.attempted"))?;
    let retained =
        require_measurement_u64(value(&details, "retained"), &format!("{where_}.retained"))?;
    let omitted =
        require_measurement_u64(value(&details, "omitted"), &format!("{where_}.omitted"))?;
    if retained != u64::try_from(actual_len).unwrap_or(u64::MAX)
        || retained > u64::try_from(limit).unwrap_or(u64::MAX)
        || retained.checked_add(omitted) != Some(attempted)
    {
        return Err(ReleaseManifestValidationError::new(format!(
            "{where_} disagrees with retained records or its schema limit"
        )));
    }
    Ok(omitted)
}

fn validate_measurement_records(
    raw: &JsonValue<'_>,
    where_: &str,
    fields: &[&str],
    text_fields: &[&str],
) -> Result<(), ReleaseManifestValidationError> {
    validate_measurement_records_with_opaque(raw, where_, fields, text_fields, &[])
}

fn validate_measurement_records_with_opaque(
    raw: &JsonValue<'_>,
    where_: &str,
    fields: &[&str],
    text_fields: &[&str],
    opaque_fields: &[&str],
) -> Result<(), ReleaseManifestValidationError> {
    for (index, raw_record) in require_array(raw, where_)?.iter().enumerate() {
        let item_where = format!("{where_}[{index}]");
        let record = require_object(raw_record, &item_where)?;
        require_fields(&record, fields, &item_where, &[])?;
        for field in fields {
            if opaque_fields.contains(field) {
                continue;
            } else if text_fields.contains(field) {
                require_text(value(&record, field), &format!("{item_where}.{field}"))?;
            } else {
                require_measurement_u64(value(&record, field), &format!("{item_where}.{field}"))?;
            }
        }
    }
    Ok(())
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

    let legacy_timing_diagnostics = if result.contains_key("timings") {
        let timings = require_object(
            value(result, "timings"),
            "verification.command_result.timings",
        )?;
        value(&timings, "schema").string_value() == Some(TIMINGS_SCHEMA_V0_1)
    } else {
        false
    };
    let expected_telemetry_count = usize::from(legacy_timing_diagnostics && external.is_none());
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
    use super::{
        shell_words, validate_command_result_shape, validate_kernel_fuel_diagnostic,
        validate_performance_measurements, validate_timestamp, JsonDocument,
    };
    use npa_api::{
        performance_measurement_report_json, PerformanceAcceptedKernelMeasurement,
        PerformanceAcceptedKernelOutcome, PerformanceDeclarationMeasurement,
        PerformanceKernelDeltaHotsetSummary, PerformanceKernelFuelDomainTotals,
        PerformanceKernelFuelTotals, PerformanceKernelSubsystem, PerformanceKernelWork,
        PerformanceMeasurementLabel, PerformanceMeasurementMode, PerformanceMeasurementRecorder,
        PerformanceModuleMeasurement, PerformancePackageShardCostModel,
        PerformancePackageShardMemoryModel, PerformancePackageShardReductionReason,
        PerformancePackageShardingMeasurement,
    };

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

    #[test]
    fn common_measurement_validator_is_strict_and_rejects_evidence_claims() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 2);
        let json = performance_measurement_report_json(&recorder.report().unwrap());
        let valid = JsonDocument::parse(&json).unwrap();
        validate_performance_measurements(valid.root(), "summary").unwrap();

        let legacy_v0_2 = legacy_performance_measurements_v0_2(&json);
        let legacy = JsonDocument::parse(&legacy_v0_2).unwrap();
        validate_performance_measurements(legacy.root(), "summary").unwrap();

        let legacy_v0_1 = legacy_performance_measurements_v0_1(&json);
        let legacy = JsonDocument::parse(&legacy_v0_1).unwrap();
        validate_performance_measurements(legacy.root(), "summary").unwrap();

        let legacy_with_v0_2_label = legacy_v0_1.replace(
            "\"label\":\"package.modules_checked\",\"unit\":\"count\"",
            "\"label\":\"package.avoided_base_context_clone_bytes\",\"unit\":\"bytes\"",
        );
        let legacy_with_v0_2_label = JsonDocument::parse(&legacy_with_v0_2_label).unwrap();
        assert!(
            validate_performance_measurements(legacy_with_v0_2_label.root(), "summary").is_err()
        );

        let old_schema_with_new_shape = json.replacen(
            "\"schema\":\"npa.performance.measurements.v0.3\"",
            "\"schema\":\"npa.performance.measurements.v0.1\"",
            1,
        );
        let old_schema_with_new_shape = JsonDocument::parse(&old_schema_with_new_shape).unwrap();
        assert!(
            validate_performance_measurements(old_schema_with_new_shape.root(), "summary").is_err()
        );

        let new_schema_with_old_shape = legacy_v0_1.replacen(
            "\"schema\":\"npa.performance.measurements.v0.1\"",
            "\"schema\":\"npa.performance.measurements.v0.2\"",
            1,
        );
        let new_schema_with_old_shape = JsonDocument::parse(&new_schema_with_old_shape).unwrap();
        assert!(
            validate_performance_measurements(new_schema_with_old_shape.root(), "summary").is_err()
        );

        let evidence = json.replacen("\"proof_evidence\":false", "\"proof_evidence\":true", 1);
        let evidence = JsonDocument::parse(&evidence).unwrap();
        assert!(validate_performance_measurements(evidence.root(), "summary").is_err());

        let non_default_summary_details = json
            .replace(
                "\"module_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0}",
                "\"module_details\":{\"attempted\":1,\"retained\":0,\"omitted\":1}",
            )
            .replace("\"detail_truncated\":false", "\"detail_truncated\":true");
        let non_default_summary_details =
            JsonDocument::parse(&non_default_summary_details).unwrap();
        assert!(
            validate_performance_measurements(non_default_summary_details.root(), "summary")
                .is_err()
        );

        let mut unknown = json;
        unknown.pop();
        unknown.push_str(",\"arbitrary_tag\":1}");
        let unknown = JsonDocument::parse(&unknown).unwrap();
        assert!(validate_performance_measurements(unknown.root(), "summary").is_err());
    }

    #[test]
    fn common_measurement_validator_accepts_historical_detailed_v0_1_shape() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_module(PerformanceModuleMeasurement {
            module: "Fixture.Module".to_owned(),
            certificate_bytes: 10,
            declaration_count: 1,
            import_count: 0,
            checker_elapsed_ns: 20,
            package_sharding: None,
        });
        let current = performance_measurement_report_json(&recorder.report().unwrap());
        let legacy = legacy_performance_measurements_v0_1(&current);
        assert!(!legacy.contains("package_sharding"));
        let legacy = JsonDocument::parse(&legacy).unwrap();
        validate_performance_measurements(legacy.root(), "detailed").unwrap();
    }

    #[test]
    fn common_measurement_validator_rejects_unknown_fast_sharding_models_and_reasons() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.set_package_sharding(PerformancePackageShardingMeasurement {
            cost_model: PerformancePackageShardCostModel::FastShardCostV1,
            memory_model: PerformancePackageShardMemoryModel::FastShardMemoryV1,
            import_weight: 4_096,
            memory_budget_bytes: 1_073_741_824,
            fixed_worker_bytes: 8_388_608,
            scratch_multiplier: 4,
            requested_jobs: 4,
            effective_jobs: 2,
            reduction_reason: PerformancePackageShardReductionReason::RunnableWidth,
            shared_base_context_bytes: 10,
            per_worker_bytes: 20,
            avoided_base_context_clone_bytes: 20,
            estimate_overflowed: false,
            critical_path_cost: 30,
            critical_path_module_count: 2,
            critical_path_identity: format!("sha256:{}", "00".repeat(32)),
            critical_path_checker_elapsed_ns: 40,
            barrier_elapsed_ns: 50,
        });
        let json = performance_measurement_report_json(&recorder.report().unwrap());
        let valid = JsonDocument::parse(&json).unwrap();
        validate_performance_measurements(valid.root(), "summary").unwrap();

        let unknown_cost_model = json.replacen(
            "\"cost_model\":\"npa.fast-shard-cost.v1\"",
            "\"cost_model\":\"npa.fast-shard-cost.v2\"",
            1,
        );
        let unknown_cost_model = JsonDocument::parse(&unknown_cost_model).unwrap();
        assert!(validate_performance_measurements(unknown_cost_model.root(), "summary").is_err());

        let unknown_reason = json.replacen(
            "\"reduction_reason\":\"runnable_width\"",
            "\"reduction_reason\":\"heuristic\"",
            1,
        );
        let unknown_reason = JsonDocument::parse(&unknown_reason).unwrap();
        assert!(validate_performance_measurements(unknown_reason.root(), "summary").is_err());

        let inconsistent_weight = json.replacen("\"import_weight\":4096", "\"import_weight\":1", 1);
        let inconsistent_weight = JsonDocument::parse(&inconsistent_weight).unwrap();
        assert!(validate_performance_measurements(inconsistent_weight.root(), "summary").is_err());
    }

    #[test]
    fn common_measurement_v0_3_requires_and_strictly_validates_declaration_kernel() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration(PerformanceDeclarationMeasurement {
            module: "Fixture.Module".to_owned(),
            declaration_index: 0,
            declaration: "Fixture.Module.no_kernel".to_owned(),
            term_nodes: 1,
            elaboration_elapsed_ns: 2,
            kernel: None,
        });
        recorder.record_declaration(PerformanceDeclarationMeasurement {
            module: "Fixture.Module".to_owned(),
            declaration_index: 1,
            declaration: "Fixture.Module.accepted".to_owned(),
            term_nodes: 3,
            elaboration_elapsed_ns: 4,
            kernel: Some(accepted_kernel_with_empty_hotset()),
        });
        let current = performance_measurement_report_json(&recorder.report().unwrap());
        let document = JsonDocument::parse(&current).unwrap();
        validate_performance_measurements(document.root(), "detailed").unwrap();
        assert!(current.contains("\"kernel\":null"));
        assert!(current.contains("\"subsystem\":\"fast_kernel\""));

        let missing_nullable_kernel = current.replacen(",\"kernel\":null", "", 1);
        let document = JsonDocument::parse(&missing_nullable_kernel).unwrap();
        let error = validate_performance_measurements(document.root(), "detailed")
            .unwrap_err()
            .to_string();
        assert!(error.contains("missing field 'kernel'"), "{error}");

        let relabeled = legacy_performance_measurements_v0_2(&current);
        let document = JsonDocument::parse(&relabeled).unwrap();
        let error = validate_performance_measurements(document.root(), "detailed")
            .unwrap_err()
            .to_string();
        assert!(error.contains("unknown field 'kernel'"), "{error}");

        for (changed, expected) in [
            (
                current.replace("\"subsystem\":\"fast_kernel\"", "\"subsystem\":\"other\""),
                "unsupported subsystem or outcome",
            ),
            (
                current.replace("\"outcome\":\"accepted\"", "\"outcome\":\"rejected\""),
                "unsupported subsystem or outcome",
            ),
            (
                current.replacen(
                    "\"logical_spent\":10",
                    "\"logical_spent\":11",
                    1,
                ),
                "operation fuel totals",
            ),
            (
                current.replacen(
                    "\"physical_reductions\":21",
                    "\"physical_reductions\":22",
                    1,
                ),
                "physical_reductions",
            ),
            (
                current.replace("\"capacity\":256", "\"capacity\":255"),
                "bounded hotset limits",
            ),
            (
                current.replace(
                    "\"subsystem\":\"fast_kernel\"",
                    "\"subsystem\":\"fast_kernel\",\"unknown\":0",
                ),
                "unknown field 'unknown'",
            ),
            (
                current.replacen(
                    "\"term_nodes\":1",
                    "\"term_nodes\":1,\"unknown\":0",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                current.replace(
                    "\"retained_delta_constants\":{\"retained_names\":0,\"capacity\":256,\"entries\":[],\"emitted\":0,\"entry_limit\":16,\"unretained_name_observations\":0,\"overlong_name_observations\":0,\"output_truncated\":false,\"overflowed\":false}",
                    "\"retained_delta_constants\":null",
                ),
                "retained_delta_constants must be present",
            ),
        ] {
            let document = JsonDocument::parse(&changed).unwrap();
            let error = validate_performance_measurements(document.root(), "detailed")
                .unwrap_err()
                .to_string();
            assert!(error.contains(expected), "expected {expected}: {error}");
        }

        let mut legacy_recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        legacy_recorder.record_declaration(PerformanceDeclarationMeasurement {
            module: "Fixture.Module".to_owned(),
            declaration_index: 0,
            declaration: "Fixture.Module.legacy".to_owned(),
            term_nodes: 1,
            elaboration_elapsed_ns: 2,
            kernel: None,
        });
        let legacy = performance_measurement_report_json(&legacy_recorder.report().unwrap())
            .replace(",\"kernel\":null", "");
        let legacy = legacy_performance_measurements_v0_2(&legacy);
        let document = JsonDocument::parse(&legacy).unwrap();
        validate_performance_measurements(document.root(), "detailed").unwrap();
    }

    #[test]
    fn command_result_v0_4_kernel_fuel_accepts_conversion_and_whnf_exact_shapes() {
        let conversion = valid_conversion_context_json();
        let conversion_fuel = valid_conversion_fuel_json();
        validate_kernel_fuel_json(&conversion_fuel, Some(conversion)).unwrap();

        let whnf_fuel = valid_whnf_fuel_json();
        validate_kernel_fuel_json(&whnf_fuel, None).unwrap();

        let source = v0_4_command_result_with_fuel(&conversion_fuel, Some(conversion));
        let document = JsonDocument::parse(&source).unwrap();
        validate_command_result_shape(document.root(), "0.8.0").unwrap();

        let relabeled = source.replacen(
            "npa.package.command_result.v0.4",
            "npa.package.command_result.v0.3",
            1,
        );
        let relabeled = JsonDocument::parse(&relabeled).unwrap();
        let error = validate_command_result_shape(relabeled.root(), "0.7.0")
            .unwrap_err()
            .to_string();
        assert!(error.contains("unknown field 'kernel_fuel'"), "{error}");

        let unknown_diagnostic = source.replacen(
            "\"severity\":\"info\"",
            "\"severity\":\"info\",\"unknown\":0",
            1,
        );
        let document = JsonDocument::parse(&unknown_diagnostic).unwrap();
        let error = validate_command_result_shape(document.root(), "0.8.0")
            .unwrap_err()
            .to_string();
        assert!(error.contains("unknown field 'unknown'"), "{error}");
    }

    #[test]
    fn command_result_v0_4_kernel_fuel_accepts_honest_overflow_and_synthetic_hotsets() {
        let conversion = valid_conversion_context_json();
        let operation_overflow = with_top_overflowed(
            valid_conversion_fuel_json()
                .replacen("\"remaining\":0", "\"remaining\":1", 1)
                .replacen(
                    "\"remaining\":1,\"exhausted\":true,\"overflowed\":false",
                    "\"remaining\":1,\"exhausted\":true,\"overflowed\":true",
                    1,
                ),
        );
        validate_kernel_fuel_json(&operation_overflow, Some(conversion)).unwrap();

        let synthetic = valid_conversion_fuel_with_hotset()
            .replace(
                "{\"constant\":\"MyProject.Residue.normalize\",\"count\":1720679}",
                "{\"constant\":\"<overlong-name>\",\"count\":1720679}",
            )
            .replace(
                "\"overlong_name_observations\":0,\"output_truncated\":false",
                "\"overlong_name_observations\":1720679,\"output_truncated\":true",
            );
        validate_kernel_fuel_json(&synthetic, Some(conversion)).unwrap();

        let saturated_hotset = with_top_overflowed(
            valid_conversion_fuel_with_hotset()
                .replace("\"count\":3100421", "\"count\":18446744073709551615")
                .replace("\"count\":1720679", "\"count\":18446744073709551615")
                .replace(
                    "\"output_truncated\":false,\"overflowed\":false}",
                    "\"output_truncated\":false,\"overflowed\":true}",
                ),
        );
        validate_kernel_fuel_json(&saturated_hotset, Some(conversion)).unwrap();
    }

    #[test]
    fn command_result_v0_4_kernel_fuel_rejects_numbers_arithmetic_and_cross_object_mismatches() {
        let valid = valid_conversion_fuel_json();
        let conversion = valid_conversion_context_json();
        for (changed, expected) in [
            (
                valid.replacen("\"budget\":5000000", "\"budget\":-1", 1),
                "nonnegative integer",
            ),
            (
                valid.replacen("\"budget\":5000000", "\"budget\":1.5", 1),
                "nonnegative integer",
            ),
            (
                valid.replacen("\"budget\":5000000", "\"budget\":18446744073709551616", 1),
                "u64 schema limit",
            ),
            (
                valid.replacen("\"remaining\":0", "\"remaining\":1", 1),
                "spent + remaining",
            ),
            (
                valid.replacen("\"logical_spent\":18342", "\"logical_spent\":18343", 1),
                "operation fuel totals",
            ),
            (
                valid.replacen(
                    "\"physical_reductions\":4821102",
                    "\"physical_reductions\":4821103",
                    1,
                ),
                "physical_reductions",
            ),
            (
                valid.replacen("\"defeq_calls\":4187", "\"defeq_calls\":5000", 1),
                "exceeds declaration work",
            ),
            (
                valid.replacen("\"exhausted\":true", "\"exhausted\":false", 1),
                "exhausted must be true",
            ),
            (
                valid.replacen("\"calls\":27", "\"calls\":0", 1),
                "calls must be positive",
            ),
            (
                valid.replacen(
                    "\"exhausted_operation_fuel\":5000000",
                    "\"exhausted_operation_fuel\":4999999",
                    1,
                ),
                "operation fuel totals",
            ),
            (
                valid.replacen(
                    "\"exhausted_operation_fuel\":0",
                    "\"exhausted_operation_fuel\":1",
                    1,
                ),
                "operation fuel totals",
            ),
            (
                valid.replacen("\"overflowed\":false", "\"overflowed\":true", 3),
                "overflowed disagrees",
            ),
        ] {
            let error = validate_kernel_fuel_json(&changed, Some(conversion)).unwrap_err();
            assert!(error.contains(expected), "expected {expected}: {error}");
        }

        let error = validate_kernel_fuel_json(&valid, None).unwrap_err();
        assert!(error.contains("requires a conversion sibling"), "{error}");
        let not_exhausted = conversion.replace("fuel_exhausted", "not_defeq");
        let error = validate_kernel_fuel_json(&valid, Some(&not_exhausted)).unwrap_err();
        assert!(error.contains("requires outcome fuel_exhausted"), "{error}");

        let mut whnf_with_conversion = valid_whnf_fuel_json();
        whnf_with_conversion =
            whnf_with_conversion.replace("\"steps\":[]", "\"steps\":[\"app_argument\"]");
        let error = validate_kernel_fuel_json(&whnf_with_conversion, Some(conversion)).unwrap_err();
        assert!(error.contains("WHNF resource"), "{error}");
    }

    #[test]
    fn command_result_v0_4_kernel_fuel_rejects_closed_vocabularies_and_bounds() {
        let valid = valid_conversion_fuel_json();
        let conversion = valid_conversion_context_json();
        let mut unknown_top = valid.clone();
        unknown_top.pop();
        unknown_top.push_str(",\"unknown\":0}");
        let long_name = "A".repeat(npa_kernel::KERNEL_DELTA_NAME_BYTE_LIMIT + 1);
        let excessive_steps = std::iter::repeat_n(
            "\"app_argument\"",
            npa_kernel::KERNEL_COMPARISON_PATH_LIMIT + 1,
        )
        .collect::<Vec<_>>()
        .join(",");
        for (changed, expected) in [
            (unknown_top, "unknown field 'unknown'"),
            (
                valid.replacen("\"budget\":5000000", "\"budget\":5000000,\"unknown\":0", 1),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"failed_operation\":{\"fuel\"",
                    "\"failed_operation\":{\"unknown\":0,\"fuel\"",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"work\":{\"check_calls\"",
                    "\"work\":{\"unknown\":0,\"check_calls\"",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"declaration\":{\"fuel\"",
                    "\"declaration\":{\"unknown\":0,\"fuel\"",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen("\"fuel\":{\"whnf\"", "\"fuel\":{\"unknown\":0,\"whnf\"", 1),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"whnf\":{\"calls\"",
                    "\"whnf\":{\"unknown\":0,\"calls\"",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"comparison_path\":{\"steps\"",
                    "\"comparison_path\":{\"unknown\":0,\"steps\"",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replace(
                    "npa.kernel-fuel-diagnostic.v0.1",
                    "npa.kernel-fuel-diagnostic.v0.2",
                ),
                "schema is unsupported",
            ),
            (
                valid.replacen("\"trusted\":false", "\"trusted\":true", 1),
                "must be untrusted and not proof evidence",
            ),
            (
                valid.replacen("\"proof_evidence\":false", "\"proof_evidence\":true", 1),
                "must be untrusted and not proof evidence",
            ),
            (
                valid.replace("\"subsystem\":\"fast_kernel\"", "\"subsystem\":\"other\""),
                "subsystem is unsupported",
            ),
            (
                valid.replace("\"resource\":\"conversion\"", "\"resource\":\"other\""),
                "resource is unsupported",
            ),
            (
                valid.replacen("\"app_argument\"", "\"unknown_step\"", 1),
                "steps[0] is unsupported",
            ),
            (
                valid.replace(
                    "\"steps\":[\"app_argument\",\"pi_body\",\"whnf_left\",\"app_function\"]",
                    &format!("\"steps\":[{excessive_steps}]"),
                ),
                "steps exceeds the schema limit",
            ),
            (
                valid_conversion_fuel_with_hotset().replace("MyProject.Expr.eval", &long_name),
                "bounded canonical name",
            ),
        ] {
            let error = validate_kernel_fuel_json(&changed, Some(conversion)).unwrap_err();
            assert!(error.contains(expected), "expected {expected}: {error}");
        }
    }

    #[test]
    fn command_result_v0_4_kernel_fuel_rejects_invalid_hotsets() {
        let valid = valid_conversion_fuel_with_hotset();
        let conversion = valid_conversion_context_json();
        let duplicate = valid.replace("MyProject.Residue.normalize", "MyProject.Expr.eval");
        let invalid_synthetic = valid.replace("MyProject.Residue.normalize", "<overlong-name>");
        for (changed, expected) in [
            (
                valid.replace("\"capacity\":256", "\"capacity\":255"),
                "bounded hotset limits",
            ),
            (
                valid.replace("\"entry_limit\":16", "\"entry_limit\":15"),
                "bounded hotset limits",
            ),
            (
                valid.replace("\"emitted\":2", "\"emitted\":1"),
                "emitted disagrees",
            ),
            (
                valid.replacen("\"count\":3100421", "\"count\":0", 1),
                "count must be positive",
            ),
            (duplicate, "constant is duplicated"),
            (
                valid.replacen("\"count\":3100421", "\"count\":1", 1),
                "descending-count/ascending-name order",
            ),
            (
                valid.replace("MyProject.Expr.eval", "Not..Canonical"),
                "bounded canonical name",
            ),
            (invalid_synthetic, "synthetic count disagrees"),
            (
                valid.replace(
                    "\"unretained_name_observations\":0",
                    "\"unretained_name_observations\":1",
                ),
                "bounded hotset limits",
            ),
            (
                valid.replace("\"output_truncated\":false", "\"output_truncated\":true"),
                "output_truncated disagrees",
            ),
            (
                valid.replacen("\"count\":3100421", "\"count\":3100420", 1),
                "observations disagree",
            ),
            (
                valid.replacen(
                    "\"constant\":\"MyProject.Expr.eval\"",
                    "\"constant\":\"MyProject.Expr.eval\",\"unknown\":0",
                    1,
                ),
                "unknown field 'unknown'",
            ),
            (
                valid.replacen(
                    "\"retained_names\":2",
                    "\"retained_names\":2,\"unknown\":0",
                    1,
                ),
                "unknown field 'unknown'",
            ),
        ] {
            let error = validate_kernel_fuel_json(&changed, Some(conversion)).unwrap_err();
            assert!(error.contains(expected), "expected {expected}: {error}");
        }
    }

    #[test]
    fn command_result_validator_accepts_integrated_timing_v0_2() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 2);
        let measurements =
            performance_measurement_report_json(&recorder.report().expect("enabled report"));
        let source = format!(
            "{{\"schema\":\"npa.package.command_result.v0.4\",\"command\":\"package verify-certs\",\"root\":\".\",\"status\":\"passed\",\"diagnostics\":[{{\"kind\":\"GeneratedArtifact\",\"reason_code\":\"package_verified\",\"severity\":\"info\"}}],\"artifacts\":[],\"timings\":{{\"schema\":\"npa.package.timings.v0.2\",\"mode\":\"summary\",\"unit\":\"ms\",\"proof_evidence\":false,\"build_evidence\":false,\"trusted\":false,\"total_ms\":1,\"measurements\":{measurements}}}}}"
        );
        let document = JsonDocument::parse(&source).unwrap();
        validate_command_result_shape(document.root(), "0.8.0").unwrap();

        let historical_measurements = legacy_performance_measurements_v0_2(&measurements);
        let historical_source = format!(
            "{{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package verify-certs\",\"root\":\".\",\"status\":\"passed\",\"diagnostics\":[{{\"kind\":\"GeneratedArtifact\",\"reason_code\":\"package_verified\",\"severity\":\"info\"}}],\"artifacts\":[],\"timings\":{{\"schema\":\"npa.package.timings.v0.2\",\"mode\":\"summary\",\"unit\":\"ms\",\"proof_evidence\":false,\"build_evidence\":false,\"trusted\":false,\"total_ms\":1,\"measurements\":{historical_measurements}}}}}"
        );
        let historical_document = JsonDocument::parse(&historical_source).unwrap();
        validate_command_result_shape(historical_document.root(), "0.7.0").unwrap();

        let mismatched_measurements =
            measurements.replacen("\"mode\":\"summary\"", "\"mode\":\"detailed\"", 1);
        let mismatched_source = format!(
            "{{\"schema\":\"npa.package.command_result.v0.4\",\"command\":\"package verify-certs\",\"root\":\".\",\"status\":\"passed\",\"diagnostics\":[{{\"kind\":\"GeneratedArtifact\",\"reason_code\":\"package_verified\",\"severity\":\"info\"}}],\"artifacts\":[],\"timings\":{{\"schema\":\"npa.package.timings.v0.2\",\"mode\":\"summary\",\"unit\":\"ms\",\"proof_evidence\":false,\"build_evidence\":false,\"trusted\":false,\"total_ms\":1,\"measurements\":{mismatched_measurements}}}}}"
        );
        let mismatched_document = JsonDocument::parse(&mismatched_source).unwrap();
        assert!(validate_command_result_shape(mismatched_document.root(), "0.8.0").is_err());
    }

    fn valid_conversion_context_json() -> &'static str {
        "{\"phase\":\"definitional_equality\",\"outcome\":\"fuel_exhausted\",\"lhs_head\":\"application\",\"rhs_head\":\"constant:A.expected\",\"depth\":7}"
    }

    fn with_top_overflowed(mut fuel: String) -> String {
        let position = fuel
            .rfind("\"overflowed\":false")
            .expect("top-level overflow marker");
        fuel.replace_range(
            position..position + "\"overflowed\":false".len(),
            "\"overflowed\":true",
        );
        fuel
    }

    fn accepted_kernel_with_empty_hotset() -> PerformanceAcceptedKernelMeasurement {
        PerformanceAcceptedKernelMeasurement {
            subsystem: PerformanceKernelSubsystem::FastKernel,
            outcome: PerformanceAcceptedKernelOutcome::Accepted,
            fuel: PerformanceKernelFuelTotals {
                whnf: PerformanceKernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 10,
                    successful_operation_fuel: 10,
                    exhausted_operation_fuel: 0,
                    overflowed: false,
                },
                conversion: PerformanceKernelFuelDomainTotals {
                    calls: 2,
                    logical_spent: 20,
                    successful_operation_fuel: 20,
                    exhausted_operation_fuel: 0,
                    overflowed: false,
                },
            },
            work: PerformanceKernelWork {
                check_calls: 1,
                infer_calls: 2,
                whnf_calls: 3,
                defeq_calls: 4,
                quick_equality_hits: 5,
                beta_steps: 6,
                delta_steps: 0,
                iota_steps: 7,
                zeta_steps: 8,
                physical_reductions: 21,
                overflowed: false,
            },
            retained_delta_constants: PerformanceKernelDeltaHotsetSummary {
                retained_names: 0,
                capacity: 256,
                entries: Vec::new(),
                emitted: 0,
                entry_limit: 16,
                unretained_name_observations: 0,
                overlong_name_observations: 0,
                output_truncated: false,
                overflowed: false,
            },
            overflowed: false,
        }
    }

    fn valid_conversion_fuel_json() -> String {
        "{\"schema\":\"npa.kernel-fuel-diagnostic.v0.1\",\"trusted\":false,\"proof_evidence\":false,\"subsystem\":\"fast_kernel\",\"resource\":\"conversion\",\"failed_operation\":{\"fuel\":{\"budget\":5000000,\"spent\":5000000,\"remaining\":0,\"exhausted\":true,\"overflowed\":false},\"work\":{\"check_calls\":0,\"infer_calls\":0,\"whnf_calls\":9120,\"defeq_calls\":4187,\"quick_equality_hits\":203,\"beta_steps\":64,\"delta_steps\":4821031,\"iota_steps\":0,\"zeta_steps\":7,\"physical_reductions\":4821102,\"overflowed\":false}},\"declaration\":{\"fuel\":{\"whnf\":{\"calls\":114,\"logical_spent\":18342,\"successful_operation_fuel\":18342,\"exhausted_operation_fuel\":0,\"overflowed\":false},\"conversion\":{\"calls\":27,\"logical_spent\":5000218,\"successful_operation_fuel\":218,\"exhausted_operation_fuel\":5000000,\"overflowed\":false}},\"work\":{\"check_calls\":1,\"infer_calls\":12,\"whnf_calls\":9234,\"defeq_calls\":4214,\"quick_equality_hits\":210,\"beta_steps\":64,\"delta_steps\":4821100,\"iota_steps\":0,\"zeta_steps\":7,\"physical_reductions\":4821171,\"overflowed\":false},\"overflowed\":false},\"comparison_path\":{\"steps\":[\"app_argument\",\"pi_body\",\"whnf_left\",\"app_function\"],\"truncated\":false},\"retained_delta_constants\":null,\"overflowed\":false}"
            .to_owned()
    }

    fn valid_whnf_fuel_json() -> String {
        valid_conversion_fuel_json()
            .replacen("\"resource\":\"conversion\"", "\"resource\":\"whnf\"", 1)
            .replacen(
                "\"calls\":114,\"logical_spent\":18342,\"successful_operation_fuel\":18342,\"exhausted_operation_fuel\":0",
                "\"calls\":114,\"logical_spent\":5018342,\"successful_operation_fuel\":18342,\"exhausted_operation_fuel\":5000000",
                1,
            )
            .replacen(
                "\"calls\":27,\"logical_spent\":5000218,\"successful_operation_fuel\":218,\"exhausted_operation_fuel\":5000000",
                "\"calls\":27,\"logical_spent\":218,\"successful_operation_fuel\":218,\"exhausted_operation_fuel\":0",
                1,
            )
            .replace(
                "\"steps\":[\"app_argument\",\"pi_body\",\"whnf_left\",\"app_function\"]",
                "\"steps\":[]",
            )
    }

    fn valid_conversion_fuel_with_hotset() -> String {
        valid_conversion_fuel_json().replace(
            "\"retained_delta_constants\":null",
            "\"retained_delta_constants\":{\"retained_names\":2,\"capacity\":256,\"entries\":[{\"constant\":\"MyProject.Expr.eval\",\"count\":3100421},{\"constant\":\"MyProject.Residue.normalize\",\"count\":1720679}],\"emitted\":2,\"entry_limit\":16,\"unretained_name_observations\":0,\"overlong_name_observations\":0,\"output_truncated\":false,\"overflowed\":false}",
        )
    }

    fn validate_kernel_fuel_json(fuel: &str, conversion: Option<&str>) -> Result<(), String> {
        let fuel = JsonDocument::parse(fuel).expect("kernel-fuel test JSON");
        let conversion = conversion.map(|conversion| {
            JsonDocument::parse(conversion).expect("conversion-context test JSON")
        });
        validate_kernel_fuel_diagnostic(
            fuel.root(),
            "kernel_fuel",
            conversion.as_ref().map(JsonDocument::root),
        )
        .map_err(|error| error.to_string())
    }

    fn v0_4_command_result_with_fuel(fuel: &str, conversion: Option<&str>) -> String {
        let conversion = conversion
            .map(|conversion| format!(",\"conversion\":{conversion}"))
            .unwrap_or_default();
        format!(
            "{{\"schema\":\"npa.package.command_result.v0.4\",\"command\":\"package verify-certs\",\"root\":\".\",\"status\":\"passed\",\"diagnostics\":[{{\"kind\":\"KernelFuelExhausted\",\"reason_code\":\"kernel_fuel_exhausted\",\"severity\":\"info\"{conversion},\"kernel_fuel\":{fuel}}}],\"artifacts\":[]}}"
        )
    }

    fn legacy_performance_measurements_v0_2(current: &str) -> String {
        current.replacen(
            "\"schema\":\"npa.performance.measurements.v0.3\"",
            "\"schema\":\"npa.performance.measurements.v0.2\"",
            1,
        )
    }

    fn legacy_performance_measurements_v0_1(current: &str) -> String {
        legacy_performance_measurements_v0_2(current)
            .replace(
                ",\"package_sharding\":null,\"package_layers\":[],\"package_layer_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"package_shards\":[],\"package_shard_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0}",
                "",
            )
            .replace(",\"package_sharding\":null}", "}")
            .replacen(
                "\"schema\":\"npa.performance.measurements.v0.2\"",
                "\"schema\":\"npa.performance.measurements.v0.1\"",
                1,
            )
    }
}

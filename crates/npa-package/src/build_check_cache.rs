//! Package build-check cache identity and untrusted result-entry serialization.
//!
//! Build-check cache entries are local acceleration metadata for
//! `npa package build-certs --check`. They are not proof evidence, are not build
//! evidence, and must never let a live source-to-certificate comparison be
//! skipped in the initial read-through implementation.

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_bool, json_object_in_order,
        json_string, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_name, required_string, validate_module_name, validate_plain_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, parse_package_hash, PackageHash},
};

/// Cache key input schema for package build-check result entries.
pub const PACKAGE_BUILD_CHECK_CACHE_SCHEMA: &str = "npa.package.build_check_cache.v0.1";

/// Cache result entry schema for package build-check outcomes.
pub const PACKAGE_BUILD_CHECK_RESULT_SCHEMA: &str = "npa.package.build_check_result.v0.1";

/// Default local package build-check result-store layout.
pub const PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR: &str =
    "target/npa-package-audit-cache/build-check-v0.1";

/// Direct import identity included in package build-check cache keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageBuildCheckImportIdentity {
    /// Imported module name.
    pub module: Name,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Complete deterministic cache key input for one package build-check module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageBuildCheckCacheKeyInput {
    /// Cache key input schema string; must equal [`PACKAGE_BUILD_CHECK_CACHE_SCHEMA`].
    pub schema: String,
    /// CLI/tool version used to create the live build result.
    pub tool_version: String,
    /// Deterministic hash of the build-check tool identity material.
    pub tool_build_hash: PackageHash,
    /// Core specification profile from the package manifest.
    pub core_spec: String,
    /// Canonical certificate format profile from the package manifest.
    pub certificate_format: String,
    /// Built module name.
    pub module: Name,
    /// Exact hash of the source bytes used for the live build.
    pub source_hash: PackageHash,
    /// Expected source hash declared in the package manifest.
    pub expected_source_hash: PackageHash,
    /// Direct import identities.
    pub direct_imports: Vec<PackageBuildCheckImportIdentity>,
    /// Compiler option identities that affect certificate generation.
    pub compiler_options: Vec<String>,
    /// Package metadata mode, for example `check` or `write`.
    pub package_metadata_mode: String,
    /// Optional producer profile from the package manifest.
    pub producer_profile: Option<String>,
    /// Expected certificate file hash declared in the package manifest.
    pub expected_certificate_file_hash: PackageHash,
    /// Expected export hash declared in the package manifest.
    pub expected_export_hash: PackageHash,
    /// Expected axiom report hash declared in the package manifest.
    pub expected_axiom_report_hash: PackageHash,
    /// Expected canonical certificate hash declared in the package manifest.
    pub expected_certificate_hash: PackageHash,
}

/// Cached build-check status recorded in an untrusted result entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageBuildCheckCachedStatus {
    /// The live build-check accepted the module for this exact key input.
    Accepted,
    /// The live build-check rejected the module or package check for this exact key input.
    Rejected,
}

impl PackageBuildCheckCachedStatus {
    /// Return the stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "accepted" => Ok(Self::Accepted),
            "rejected" => Ok(Self::Rejected),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "status",
                "accepted or rejected",
                value,
            )),
        }
    }
}

/// One untrusted package build-check result-store entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageBuildCheckResultEntry {
    /// Result entry schema string; must equal [`PACKAGE_BUILD_CHECK_RESULT_SCHEMA`].
    pub schema: String,
    /// Deterministic cache key for [`Self::key_input`].
    pub cache_key: String,
    /// Must be false: cache entries are never proof evidence.
    pub trusted: bool,
    /// Must be false: cache entries are never accepted as build evidence.
    pub build_evidence: bool,
    /// Exact key input covered by this result.
    pub key_input: PackageBuildCheckCacheKeyInput,
    /// Cached build-check status.
    pub status: PackageBuildCheckCachedStatus,
    /// Optional deterministic diagnostic reason for rejected entries.
    pub diagnostic_reason: Option<String>,
    /// Human-readable trust-boundary note.
    pub trust_boundary: String,
}

/// Serialize canonical cache key material for one package build-check input.
pub fn package_build_check_cache_key_material(input: &PackageBuildCheckCacheKeyInput) -> String {
    cache_key_input_json(&normalized_cache_key_input(input))
}

/// Compute the deterministic package build-check cache key for one input.
pub fn package_build_check_cache_key(input: &PackageBuildCheckCacheKeyInput) -> String {
    format_package_hash(&package_file_hash(
        package_build_check_cache_key_material(input).as_bytes(),
    ))
}

/// Serialize one package build-check result entry as canonical JSON.
pub fn package_build_check_result_entry_json(entry: &PackageBuildCheckResultEntry) -> String {
    result_entry_json_unchecked(&normalized_result_entry(entry))
}

/// Parse and validate a canonical package build-check result entry JSON artifact.
pub fn parse_package_build_check_result_entry_json(
    source: &str,
) -> PackageArtifactResult<PackageBuildCheckResultEntry> {
    let root = parse_artifact_json(source)?;
    let entry = parse_result_entry_value(&root)?;
    validate_package_build_check_result_entry(&entry)?;
    let canonical = package_build_check_result_entry_json(&entry);
    if source != canonical {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package build-check result entry JSON bytes",
        ));
    }
    Ok(entry)
}

/// Validate one package build-check result entry without reading files or running builders.
pub fn validate_package_build_check_result_entry(
    entry: &PackageBuildCheckResultEntry,
) -> PackageArtifactResult<()> {
    if entry.schema != PACKAGE_BUILD_CHECK_RESULT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
            entry.schema.clone(),
        ));
    }
    validate_hash_string(&entry.cache_key, "cache_key")?;
    if entry.trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "trusted", "trusted", "false", "true",
        ));
    }
    if entry.build_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "build_evidence",
            "build_evidence",
            "false",
            "true",
        ));
    }
    validate_cache_key_input(&entry.key_input)?;
    let expected_key = package_build_check_cache_key(&entry.key_input);
    if expected_key != entry.cache_key {
        return Err(PackageArtifactError::self_hash_mismatch(
            "cache_key",
            "cache_key",
            expected_key,
            entry.cache_key.clone(),
        ));
    }
    if let Some(reason) = &entry.diagnostic_reason {
        validate_plain_string(reason, "diagnostic_reason")?;
    }
    validate_plain_string(&entry.trust_boundary, "trust_boundary")
}

fn validate_cache_key_input(input: &PackageBuildCheckCacheKeyInput) -> PackageArtifactResult<()> {
    if input.schema != PACKAGE_BUILD_CHECK_CACHE_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "key_input.schema",
            "schema",
            PACKAGE_BUILD_CHECK_CACHE_SCHEMA,
            input.schema.clone(),
        ));
    }
    validate_plain_string(&input.tool_version, "key_input.tool_version")?;
    validate_plain_string(&input.core_spec, "key_input.core_spec")?;
    validate_plain_string(&input.certificate_format, "key_input.certificate_format")?;
    validate_module_name(&input.module, "key_input.module")?;
    for (index, import) in input.direct_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            format!("key_input.direct_imports[{index}].module"),
        )?;
    }
    for (index, option) in input.compiler_options.iter().enumerate() {
        validate_plain_string(option, format!("key_input.compiler_options[{index}]"))?;
    }
    validate_plain_string(
        &input.package_metadata_mode,
        "key_input.package_metadata_mode",
    )?;
    if let Some(profile) = &input.producer_profile {
        validate_plain_string(profile, "key_input.producer_profile")?;
    }
    Ok(())
}

fn validate_hash_string(value: &str, path: &str) -> PackageArtifactResult<()> {
    parse_package_hash(value, path)
        .map(|_| ())
        .map_err(|_| PackageArtifactError::invalid_hash_format(path, value))
}

fn normalized_result_entry(entry: &PackageBuildCheckResultEntry) -> PackageBuildCheckResultEntry {
    let mut normalized = entry.clone();
    normalized.key_input = normalized_cache_key_input(&normalized.key_input);
    normalized
}

fn normalized_cache_key_input(
    input: &PackageBuildCheckCacheKeyInput,
) -> PackageBuildCheckCacheKeyInput {
    let mut normalized = input.clone();
    normalize_direct_imports(&mut normalized.direct_imports);
    normalized.compiler_options.sort();
    normalized.compiler_options.dedup();
    normalized
}

fn normalize_direct_imports(imports: &mut Vec<PackageBuildCheckImportIdentity>) {
    imports.sort_by(|left, right| {
        left.module
            .cmp(&right.module)
            .then_with(|| left.export_hash.cmp(&right.export_hash))
            .then_with(|| left.certificate_hash.cmp(&right.certificate_hash))
    });
    imports.dedup_by(|left, right| {
        left.module == right.module
            && left.export_hash == right.export_hash
            && left.certificate_hash == right.certificate_hash
    });
}

fn cache_key_input_json(input: &PackageBuildCheckCacheKeyInput) -> String {
    let mut fields = vec![
        ("schema", json_string(&input.schema)),
        ("tool_version", json_string(&input.tool_version)),
        ("tool_build_hash", hash_json(input.tool_build_hash)),
        ("core_spec", json_string(&input.core_spec)),
        ("certificate_format", json_string(&input.certificate_format)),
        ("module", json_string(&input.module.as_dotted())),
        ("source_hash", hash_json(input.source_hash)),
        (
            "expected_source_hash",
            hash_json(input.expected_source_hash),
        ),
        (
            "direct_imports",
            json_array(
                input
                    .direct_imports
                    .iter()
                    .map(import_identity_json)
                    .collect(),
            ),
        ),
        (
            "compiler_options",
            json_array(
                input
                    .compiler_options
                    .iter()
                    .map(|option| json_string(option))
                    .collect(),
            ),
        ),
        (
            "package_metadata_mode",
            json_string(&input.package_metadata_mode),
        ),
    ];
    if let Some(profile) = &input.producer_profile {
        fields.push(("producer_profile", json_string(profile)));
    }
    fields.extend([
        (
            "expected_certificate_file_hash",
            hash_json(input.expected_certificate_file_hash),
        ),
        (
            "expected_export_hash",
            hash_json(input.expected_export_hash),
        ),
        (
            "expected_axiom_report_hash",
            hash_json(input.expected_axiom_report_hash),
        ),
        (
            "expected_certificate_hash",
            hash_json(input.expected_certificate_hash),
        ),
    ]);
    json_object_in_order(fields)
}

fn import_identity_json(import: &PackageBuildCheckImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn result_entry_json_unchecked(entry: &PackageBuildCheckResultEntry) -> String {
    let mut fields = vec![
        ("schema", json_string(&entry.schema)),
        ("cache_key", json_string(&entry.cache_key)),
        ("trusted", json_bool(entry.trusted)),
        ("build_evidence", json_bool(entry.build_evidence)),
        ("key_input", cache_key_input_json(&entry.key_input)),
        ("status", json_string(entry.status.as_str())),
    ];
    if let Some(reason) = &entry.diagnostic_reason {
        fields.push(("diagnostic_reason", json_string(reason)));
    }
    fields.push(("trust_boundary", json_string(&entry.trust_boundary)));
    json_object_in_order(fields)
}

fn parse_result_entry_value(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageBuildCheckResultEntry> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, RESULT_ENTRY_FIELDS)?;
    let status_path = field_path("$", "status");
    Ok(PackageBuildCheckResultEntry {
        schema: required_string(members, "$", "schema")?,
        cache_key: required_string(members, "$", "cache_key")?,
        trusted: required_bool(members, "$", "trusted")?,
        build_evidence: required_bool(members, "$", "build_evidence")?,
        key_input: parse_cache_key_input(crate::artifacts::required_value(
            members,
            "$",
            "key_input",
        )?)?,
        status: PackageBuildCheckCachedStatus::parse(
            &required_string(members, "$", "status")?,
            &status_path,
        )?,
        diagnostic_reason: optional_string(members, "$", "diagnostic_reason")?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
    })
}

fn parse_cache_key_input(
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageBuildCheckCacheKeyInput> {
    let path = "key_input";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CACHE_KEY_INPUT_FIELDS)?;
    Ok(PackageBuildCheckCacheKeyInput {
        schema: required_string(members, path, "schema")?,
        tool_version: required_string(members, path, "tool_version")?,
        tool_build_hash: required_hash(members, path, "tool_build_hash")?,
        core_spec: required_string(members, path, "core_spec")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        module: required_name(members, path, "module")?,
        source_hash: required_hash(members, path, "source_hash")?,
        expected_source_hash: required_hash(members, path, "expected_source_hash")?,
        direct_imports: required_array(members, path, "direct_imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_import_identity(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        compiler_options: parse_string_array(members, path, "compiler_options")?,
        package_metadata_mode: required_string(members, path, "package_metadata_mode")?,
        producer_profile: optional_string(members, path, "producer_profile")?,
        expected_certificate_file_hash: required_hash(
            members,
            path,
            "expected_certificate_file_hash",
        )?,
        expected_export_hash: required_hash(members, path, "expected_export_hash")?,
        expected_axiom_report_hash: required_hash(members, path, "expected_axiom_report_hash")?,
        expected_certificate_hash: required_hash(members, path, "expected_certificate_hash")?,
    })
}

fn parse_import_identity(
    index: usize,
    value: &crate::json::JsonValue,
) -> PackageArtifactResult<PackageBuildCheckImportIdentity> {
    let path = format!("key_input.direct_imports[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_IDENTITY_FIELDS)?;
    Ok(PackageBuildCheckImportIdentity {
        module: required_name(members, &path, "module")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

fn parse_string_array(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<String>> {
    required_array(members, path, field)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn optional_string(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<String>> {
    if members.iter().any(|member| member.key() == field) {
        required_string(members, path, field).map(Some)
    } else {
        Ok(None)
    }
}

const RESULT_ENTRY_FIELDS: &[&str] = &[
    "schema",
    "cache_key",
    "trusted",
    "build_evidence",
    "key_input",
    "status",
    "diagnostic_reason",
    "trust_boundary",
];
const CACHE_KEY_INPUT_FIELDS: &[&str] = &[
    "schema",
    "tool_version",
    "tool_build_hash",
    "core_spec",
    "certificate_format",
    "module",
    "source_hash",
    "expected_source_hash",
    "direct_imports",
    "compiler_options",
    "package_metadata_mode",
    "producer_profile",
    "expected_certificate_file_hash",
    "expected_export_hash",
    "expected_axiom_report_hash",
    "expected_certificate_hash",
];
const IMPORT_IDENTITY_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::PackageArtifactErrorReason;

    #[test]
    fn package_build_check_cache_key_is_deterministic() {
        let input = fixture_key_input();

        assert_eq!(
            package_build_check_cache_key_material(&input),
            package_build_check_cache_key_material(&input)
        );
        assert_eq!(
            package_build_check_cache_key(&input),
            package_build_check_cache_key(&input)
        );
    }

    #[test]
    fn package_build_check_cache_key_changes_for_source_hash() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.source_hash = hash(99);

        assert_ne!(
            package_build_check_cache_key(&input),
            package_build_check_cache_key(&changed)
        );
    }

    #[test]
    fn package_build_check_cache_key_changes_for_expected_certificate_hash() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.expected_certificate_hash = hash(99);

        assert_ne!(
            package_build_check_cache_key(&input),
            package_build_check_cache_key(&changed)
        );
    }

    #[test]
    fn package_build_check_cache_key_sorts_direct_imports_and_options() {
        let input = fixture_key_input();
        let mut changed = input.clone();
        changed.direct_imports = vec![
            PackageBuildCheckImportIdentity {
                module: module("Fixture.ImportB"),
                export_hash: hash(21),
                certificate_hash: hash(22),
            },
            PackageBuildCheckImportIdentity {
                module: module("Fixture.ImportA"),
                export_hash: hash(19),
                certificate_hash: hash(20),
            },
            PackageBuildCheckImportIdentity {
                module: module("Fixture.ImportA"),
                export_hash: hash(19),
                certificate_hash: hash(20),
            },
        ];
        changed.compiler_options = vec![
            "zeta".to_owned(),
            "default".to_owned(),
            "default".to_owned(),
        ];

        let mut expected = input.clone();
        expected.compiler_options.push("zeta".to_owned());

        assert_eq!(
            package_build_check_cache_key_material(&expected),
            package_build_check_cache_key_material(&changed)
        );
    }

    #[test]
    fn package_build_check_result_entry_requires_trusted_false() {
        let mut entry = fixture_result_entry(PackageBuildCheckCachedStatus::Accepted);
        entry.trusted = true;

        let error = validate_package_build_check_result_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("trusted"));
    }

    #[test]
    fn package_build_check_result_entry_requires_build_evidence_false() {
        let mut entry = fixture_result_entry(PackageBuildCheckCachedStatus::Accepted);
        entry.build_evidence = true;

        let error = validate_package_build_check_result_entry(&entry).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("build_evidence"));
    }

    #[test]
    fn package_build_check_result_entry_round_trips_canonical_json() {
        let mut entry = fixture_result_entry(PackageBuildCheckCachedStatus::Rejected);
        entry.key_input.compiler_options = vec![
            "unit".to_owned(),
            "inductive".to_owned(),
            "inductive".to_owned(),
        ];
        entry.cache_key = package_build_check_cache_key(&entry.key_input);
        entry.diagnostic_reason = Some("build_certificate_changed".to_owned());

        let json = package_build_check_result_entry_json(&entry);
        let parsed = parse_package_build_check_result_entry_json(&json).unwrap();

        assert_eq!(package_build_check_result_entry_json(&parsed), json);
        assert_eq!(parsed.status, PackageBuildCheckCachedStatus::Rejected);
        assert_eq!(
            parsed.key_input.compiler_options,
            vec!["inductive".to_owned(), "unit".to_owned()]
        );
        assert!(json.contains("\"trusted\":false"));
        assert!(json.contains("\"build_evidence\":false"));
    }

    fn fixture_result_entry(status: PackageBuildCheckCachedStatus) -> PackageBuildCheckResultEntry {
        let key_input = fixture_key_input();
        PackageBuildCheckResultEntry {
            schema: PACKAGE_BUILD_CHECK_RESULT_SCHEMA.to_owned(),
            cache_key: package_build_check_cache_key(&key_input),
            trusted: false,
            build_evidence: false,
            key_input,
            status,
            diagnostic_reason: None,
            trust_boundary: "cache entry is not proof evidence or build evidence".to_owned(),
        }
    }

    fn fixture_key_input() -> PackageBuildCheckCacheKeyInput {
        PackageBuildCheckCacheKeyInput {
            schema: PACKAGE_BUILD_CHECK_CACHE_SCHEMA.to_owned(),
            tool_version: "0.1.0".to_owned(),
            tool_build_hash: hash(1),
            core_spec: "npa.core.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            module: module("Fixture.Target"),
            source_hash: hash(2),
            expected_source_hash: hash(2),
            direct_imports: vec![
                PackageBuildCheckImportIdentity {
                    module: module("Fixture.ImportA"),
                    export_hash: hash(19),
                    certificate_hash: hash(20),
                },
                PackageBuildCheckImportIdentity {
                    module: module("Fixture.ImportB"),
                    export_hash: hash(21),
                    certificate_hash: hash(22),
                },
            ],
            compiler_options: vec!["default".to_owned()],
            package_metadata_mode: "check".to_owned(),
            producer_profile: Some("human".to_owned()),
            expected_certificate_file_hash: hash(3),
            expected_export_hash: hash(4),
            expected_axiom_report_hash: hash(5),
            expected_certificate_hash: hash(6),
        }
    }

    fn module(value: &str) -> Name {
        Name::from_dotted(value)
    }

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }
}

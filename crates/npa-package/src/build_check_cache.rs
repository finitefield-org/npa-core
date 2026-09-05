//! Package build-check cache identity and untrusted result-entry serialization.
//!
//! Build-check cache entries are local acceleration metadata for
//! `npa package build-certs --check`. They are not proof evidence, are not build
//! evidence, and must never let a live source-to-certificate comparison be
//! skipped in the initial read-through implementation.

use std::path::{Path, PathBuf};

use npa_cert::{
    Name, MAX_CERTIFICATE_BYTES, MAX_CERTIFICATE_EXPANDED_NODES, MAX_CLOSURE_EXPANDED_NODES,
    MAX_CLOSURE_MODULES, MAX_DECLARATIONS, MAX_EXPORTS, MAX_IMPORTS, MAX_LEVEL_TABLE_NODES,
    MAX_NAME_TABLE_ENTRIES, MAX_NESTED_VECTOR_ENTRIES, MAX_ROOT_EXPANDED_NODES,
    MAX_STRUCTURAL_DEPTH, MAX_TERM_TABLE_NODES,
};

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_bool, json_object_in_order,
        json_string, parse_artifact_json_with_limits, reject_unknown_fields, required_array,
        required_bool, required_hash, required_name, required_string, validate_module_name,
        validate_plain_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, parse_package_hash, PackageHash},
    json::JsonResourceLimits,
    validate::ValidatedPackageManifest,
};

/// Cache key input schema for package build-check result entries.
pub const PACKAGE_BUILD_CHECK_CACHE_SCHEMA: &str = "npa.package.build_check_cache.v0.2";

/// Cache result entry schema for package build-check outcomes.
pub const PACKAGE_BUILD_CHECK_RESULT_SCHEMA: &str = "npa.package.build_check_result.v0.2";

/// Package namespace preimage schema shared by both build-check cache stores.
pub const PACKAGE_BUILD_CHECK_CACHE_NAMESPACE_SCHEMA: &str =
    "npa.package.build_check_cache_namespace.v0.1";

/// Default repository-relative cache base selected by the later safe-anchor resolver.
pub const PACKAGE_BUILD_CHECK_CACHE_BASE_LAYOUT_DIR: &str = "target/npa-package-audit-cache";

/// First fixed component below a resolved build-check cache base.
pub const PACKAGE_BUILD_CHECK_CACHE_PACKAGES_LAYOUT_DIR: &str = "packages";

/// Versioned diagnostic result-store component.
pub const PACKAGE_BUILD_CHECK_RESULT_STORE_VERSION: &str = "build-check-v0.2";

/// Versioned targeted-authoring support-store component.
pub const PACKAGE_TARGETED_AUTHORING_SUPPORT_STORE_VERSION: &str =
    "targeted-authoring-support-v0.1";

/// Lowercase hexadecimal width of every SHA-256 cache path digest.
pub const PACKAGE_BUILD_CHECK_CACHE_DIGEST_HEX_BYTES: usize = 64;

/// Fixed cache-only resource-limit profile shared by result-cache and targeted-authoring schemas.
pub const TARGETED_AUTHORING_CACHE_LIMITS_SCHEMA_V1: &str =
    "npa.package.targeted_authoring_cache_limits.v1";

/// Version 1 cache-only parser, reconstruction, retention, and diagnostic limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringCacheLimitsV1 {
    /// Maximum canonical result-entry JSON bytes.
    pub result_entry_bytes: usize,
    /// Maximum canonical support-context entry bytes.
    pub support_entry_bytes: usize,
    /// Maximum exact current source bytes read for one support module.
    pub source_bytes: usize,
    /// Maximum executable bytes hashed for one command tool identity.
    pub tool_identity_bytes: usize,
    /// Maximum cache-only JSON nesting depth.
    pub json_nesting_depth: usize,
    /// Maximum decoded bytes in one cache-only JSON string.
    pub json_string_bytes: usize,
    /// Maximum bytes in one cache-only JSON number token.
    pub json_number_bytes: usize,
    /// Maximum elements in one cache-only JSON array.
    pub json_array_elements: usize,
    /// Maximum members in one cache-only JSON object.
    pub json_object_members: usize,
    /// Maximum bytes in one validated filesystem path component.
    pub path_component_bytes: usize,
    /// Maximum direct imports in one result key or support identity.
    pub direct_imports: usize,
    /// Maximum normalized semantic compiler-option identities.
    pub compiler_options: usize,
    /// Maximum declarations in one reconstructed Human interface.
    pub interface_declarations: usize,
    /// Maximum generated declarations in one reconstructed Human interface.
    pub interface_generated_declarations: usize,
    /// Maximum notation records in one reconstructed Human interface.
    pub interface_notations: usize,
    /// Maximum typeclass records in one reconstructed Human interface.
    pub interface_typeclasses: usize,
    /// Maximum binders on one reconstructed declaration.
    pub interface_binders_per_declaration: usize,
    /// Maximum universe parameters on one reconstructed declaration.
    pub interface_universe_parameters_per_declaration: usize,
    /// Maximum reconstructed source-span records in one interface.
    pub interface_spans: usize,
    /// Maximum dependency edges represented by one reconstructed interface.
    pub interface_dependency_edges: usize,
    /// Maximum encoded certificate bytes reused by cached reconstruction.
    pub certificate_bytes: usize,
    /// Maximum certificate imports reused by cached reconstruction.
    pub certificate_imports: usize,
    /// Maximum certificate name-table entries reused by cached reconstruction.
    pub certificate_name_table_entries: usize,
    /// Maximum certificate level-table nodes reused by cached reconstruction.
    pub certificate_level_table_nodes: usize,
    /// Maximum certificate term-table nodes reused by cached reconstruction.
    pub certificate_term_table_nodes: usize,
    /// Maximum certificate declarations reused by cached reconstruction.
    pub certificate_declarations: usize,
    /// Maximum certificate exports reused by cached reconstruction.
    pub certificate_exports: usize,
    /// Maximum nested certificate vector entries reused by cached reconstruction.
    pub certificate_nested_vector_entries: usize,
    /// Maximum certificate structural depth reused by cached reconstruction.
    pub certificate_structural_depth: usize,
    /// Maximum expanded nodes for one certificate semantic root.
    pub certificate_root_expanded_nodes: usize,
    /// Maximum summed expanded nodes for one certificate.
    pub certificate_expanded_nodes: usize,
    /// Maximum unique certificate identities in one selected closure.
    pub closure_modules: usize,
    /// Maximum summed expanded nodes in one selected closure.
    pub closure_expanded_nodes: usize,
    /// Maximum dependency edges traversed for one selected closure.
    pub closure_dependency_edges: usize,
    /// Maximum cache entries addressed during one command.
    pub cache_entries_per_command: usize,
    /// Maximum reconstructed contexts retained at once.
    pub retained_contexts: usize,
    /// Maximum aggregate reconstructed-context bytes retained at once.
    pub retained_context_bytes: usize,
    /// Maximum cache entry bytes loaded during one command.
    pub command_loaded_bytes: usize,
    /// Maximum cache temporary/entry bytes written during one command.
    pub command_written_bytes: usize,
    /// Maximum detailed cache diagnostics emitted during one command.
    pub detailed_diagnostics: usize,
    /// Maximum bytes in one detailed cache diagnostic value.
    pub diagnostic_value_bytes: usize,
}

/// Frozen values for [`TARGETED_AUTHORING_CACHE_LIMITS_SCHEMA_V1`].
pub const TARGETED_AUTHORING_CACHE_LIMITS_V1: TargetedAuthoringCacheLimitsV1 =
    TargetedAuthoringCacheLimitsV1 {
        result_entry_bytes: 2_097_152,
        support_entry_bytes: 134_217_728,
        source_bytes: MAX_CERTIFICATE_BYTES,
        tool_identity_bytes: 268_435_456,
        json_nesting_depth: 64,
        json_string_bytes: 16_384,
        json_number_bytes: 32,
        json_array_elements: MAX_EXPORTS,
        json_object_members: 64,
        path_component_bytes: 255,
        direct_imports: MAX_IMPORTS,
        compiler_options: 256,
        interface_declarations: MAX_DECLARATIONS,
        interface_generated_declarations: MAX_EXPORTS,
        interface_notations: MAX_NESTED_VECTOR_ENTRIES,
        interface_typeclasses: MAX_NESTED_VECTOR_ENTRIES,
        interface_binders_per_declaration: MAX_NESTED_VECTOR_ENTRIES,
        interface_universe_parameters_per_declaration: MAX_NESTED_VECTOR_ENTRIES,
        interface_spans: MAX_EXPORTS,
        interface_dependency_edges: MAX_CERTIFICATE_EXPANDED_NODES,
        certificate_bytes: MAX_CERTIFICATE_BYTES,
        certificate_imports: MAX_IMPORTS,
        certificate_name_table_entries: MAX_NAME_TABLE_ENTRIES,
        certificate_level_table_nodes: MAX_LEVEL_TABLE_NODES,
        certificate_term_table_nodes: MAX_TERM_TABLE_NODES,
        certificate_declarations: MAX_DECLARATIONS,
        certificate_exports: MAX_EXPORTS,
        certificate_nested_vector_entries: MAX_NESTED_VECTOR_ENTRIES,
        certificate_structural_depth: MAX_STRUCTURAL_DEPTH,
        certificate_root_expanded_nodes: MAX_ROOT_EXPANDED_NODES,
        certificate_expanded_nodes: MAX_CERTIFICATE_EXPANDED_NODES,
        closure_modules: MAX_CLOSURE_MODULES,
        closure_expanded_nodes: MAX_CLOSURE_EXPANDED_NODES,
        closure_dependency_edges: MAX_CLOSURE_EXPANDED_NODES,
        cache_entries_per_command: MAX_CLOSURE_MODULES,
        retained_contexts: MAX_CLOSURE_MODULES,
        retained_context_bytes: 1_073_741_824,
        command_loaded_bytes: 1_073_741_824,
        command_written_bytes: 1_073_741_824,
        detailed_diagnostics: 256,
        diagnostic_value_bytes: 256,
    };

/// Compatibility-only unnamespaced result-store layout from the v0.2 API.
///
/// The spelling remains exported for compatibility, but current runtime code
/// treats the corresponding path as inert data.
pub const PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR: &str =
    "target/npa-package-audit-cache/build-check-v0.2";

/// Validated lowercase SHA-256 package namespace component.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageCacheNamespaceDigest(String);

impl PackageCacheNamespaceDigest {
    /// Parse one exact 64-character lowercase hexadecimal namespace component.
    pub fn parse(value: &str) -> PackageArtifactResult<Self> {
        validate_lowercase_sha256_component(value, "package_cache_namespace")?;
        Ok(Self(value.to_owned()))
    }

    /// Return the validated path-component spelling.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn from_hash(hash: PackageHash) -> Self {
        let mut value = format_package_hash(&hash);
        value.replace_range(.."sha256:".len(), "");
        Self(value)
    }
}

/// Closed versioned store component below one package-cache namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageCacheStoreVersion(&'static str);

impl PackageCacheStoreVersion {
    /// Diagnostic build-check result store.
    pub const BUILD_CHECK_RESULT: Self = Self(PACKAGE_BUILD_CHECK_RESULT_STORE_VERSION);
    /// Targeted-authoring support-context store.
    pub const TARGETED_AUTHORING_SUPPORT: Self =
        Self(PACKAGE_TARGETED_AUTHORING_SUPPORT_STORE_VERSION);

    /// Parse one of the closed store-version spellings.
    pub fn parse(value: &str) -> PackageArtifactResult<Self> {
        validate_cache_path_component(value, "package_cache_store_version")?;
        match value {
            PACKAGE_BUILD_CHECK_RESULT_STORE_VERSION => Ok(Self::BUILD_CHECK_RESULT),
            PACKAGE_TARGETED_AUTHORING_SUPPORT_STORE_VERSION => {
                Ok(Self::TARGETED_AUTHORING_SUPPORT)
            }
            _ => Err(invalid_cache_path_component(
                "package_cache_store_version",
                "build-check-v0.2 or targeted-authoring-support-v0.1",
                value,
            )),
        }
    }

    /// Return the validated path-component spelling.
    pub const fn as_str(self) -> &'static str {
        self.0
    }
}

/// Validated lowercase SHA-256 cache-entry key component.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageCacheKeyDigest(String);

impl PackageCacheKeyDigest {
    /// Parse a complete `sha256:<lowercase hex>` cache key into its filename-safe digest.
    pub fn from_cache_key(value: &str) -> PackageArtifactResult<Self> {
        let Some(digest) = value.strip_prefix("sha256:") else {
            return Err(invalid_cache_path_component(
                "package_cache_key_digest",
                "sha256:<64 lowercase hex>",
                value,
            ));
        };
        validate_lowercase_sha256_component(digest, "package_cache_key_digest")?;
        Ok(Self(digest.to_owned()))
    }

    /// Return the validated path-component spelling without the `sha256:` prefix.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Validated same-directory temporary filename component.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageCacheTemporaryName(String);

impl PackageCacheTemporaryName {
    /// Build a unique temporary name from an exact entry key and a caller-owned unique token.
    ///
    /// The unique token is limited to lowercase ASCII letters, digits, and hyphens. The
    /// resulting complete filename is checked against the frozen path-component byte limit.
    pub fn new(key: &PackageCacheKeyDigest, unique: &str) -> PackageArtifactResult<Self> {
        validate_cache_unique_token(unique)?;
        let value = format!("tmp-{}-{unique}.tmp", key.as_str());
        validate_cache_path_component(&value, "package_cache_temporary_name")?;
        Ok(Self(value))
    }

    /// Return the validated path-component spelling.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Typed relative layout for one versioned package cache store.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageCacheStoreLayout {
    namespace: PackageCacheNamespaceDigest,
    store: PackageCacheStoreVersion,
}

impl PackageCacheStoreLayout {
    /// Construct the diagnostic result-store layout.
    pub fn build_check_result(namespace: &PackageCacheNamespaceDigest) -> Self {
        Self {
            namespace: namespace.clone(),
            store: PackageCacheStoreVersion::BUILD_CHECK_RESULT,
        }
    }

    /// Construct the targeted-authoring support-store layout.
    pub fn targeted_authoring_support(namespace: &PackageCacheNamespaceDigest) -> Self {
        Self {
            namespace: namespace.clone(),
            store: PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
        }
    }

    /// Return the validated namespace component.
    pub fn namespace(&self) -> &PackageCacheNamespaceDigest {
        &self.namespace
    }

    /// Return the closed store-version component.
    pub const fn store_version(&self) -> PackageCacheStoreVersion {
        self.store
    }

    /// Build `packages/<namespace>/<store>` relative to a resolved cache base.
    pub fn relative_path(&self) -> PathBuf {
        PathBuf::from(PACKAGE_BUILD_CHECK_CACHE_PACKAGES_LAYOUT_DIR)
            .join(self.namespace.as_str())
            .join(self.store.as_str())
    }

    /// Build one exact entry path below this store.
    pub fn entry_relative_path(&self, key: &PackageCacheKeyDigest) -> PathBuf {
        self.relative_path().join(format!("{}.json", key.as_str()))
    }

    /// Build one validated same-directory temporary path below this store.
    pub fn temporary_relative_path(&self, temporary: &PackageCacheTemporaryName) -> PathBuf {
        self.relative_path().join(temporary.as_str())
    }
}

/// Canonically serialize the exact package namespace preimage.
pub fn package_build_check_cache_namespace_material(
    validated: &ValidatedPackageManifest,
) -> String {
    package_build_check_cache_namespace_material_with_schema(
        PACKAGE_BUILD_CHECK_CACHE_NAMESPACE_SCHEMA,
        validated,
    )
}

/// Derive the fixed-width lowercase hexadecimal namespace component.
pub fn package_build_check_cache_namespace_digest(
    validated: &ValidatedPackageManifest,
) -> PackageCacheNamespaceDigest {
    PackageCacheNamespaceDigest::from_hash(package_file_hash(
        package_build_check_cache_namespace_material(validated).as_bytes(),
    ))
}

/// Build the fixed default cache base relative to a checkout root.
pub fn package_build_check_cache_default_base_relative_path() -> PathBuf {
    PathBuf::from(PACKAGE_BUILD_CHECK_CACHE_BASE_LAYOUT_DIR)
}

/// Build the compatibility-only unnamespaced result-store path.
///
/// Current runtime code treats this location as inert data and never scans,
/// migrates, or deletes it.
pub fn package_build_check_cache_legacy_relative_path() -> PathBuf {
    package_build_check_cache_default_base_relative_path()
        .join(PackageCacheStoreVersion::BUILD_CHECK_RESULT.as_str())
}

fn package_build_check_cache_namespace_material_with_schema(
    schema: &str,
    validated: &ValidatedPackageManifest,
) -> String {
    let manifest = validated.manifest();
    let mut allowed_axioms = manifest
        .policy
        .allowed_axioms
        .iter()
        .map(Name::as_dotted)
        .collect::<Vec<_>>();
    allowed_axioms.sort();
    let axiom_policy = json_object_in_order(vec![
        (
            "allow_custom_axioms",
            json_bool(manifest.policy.allow_custom_axioms),
        ),
        (
            "allowed_axioms",
            json_array(
                allowed_axioms
                    .iter()
                    .map(|axiom| json_string(axiom))
                    .collect(),
            ),
        ),
    ]);
    json_object_in_order(vec![
        ("schema", json_string(schema)),
        ("package", json_string(manifest.package.as_str())),
        ("version", json_string(manifest.version.as_str())),
        ("core_spec", json_string(&manifest.core_spec)),
        ("kernel_profile", json_string(&manifest.kernel_profile)),
        (
            "certificate_format",
            json_string(&manifest.certificate_format),
        ),
        ("checker_profile", json_string(&manifest.checker_profile)),
        ("axiom_policy", axiom_policy),
    ])
}

fn validate_lowercase_sha256_component(value: &str, path: &str) -> PackageArtifactResult<()> {
    validate_cache_path_component(value, path)?;
    if value.len() == PACKAGE_BUILD_CHECK_CACHE_DIGEST_HEX_BYTES
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        Ok(())
    } else {
        Err(invalid_cache_path_component(
            path,
            "64 lowercase hexadecimal characters",
            value,
        ))
    }
}

fn validate_cache_unique_token(value: &str) -> PackageArtifactResult<()> {
    validate_cache_path_component(value, "package_cache_temporary_unique")?;
    if value
        .bytes()
        .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
    {
        Ok(())
    } else {
        Err(invalid_cache_path_component(
            "package_cache_temporary_unique",
            "lowercase ASCII letters, digits, or hyphens",
            value,
        ))
    }
}

fn validate_cache_path_component(value: &str, path: &str) -> PackageArtifactResult<()> {
    if value.is_empty()
        || value == "."
        || value == ".."
        || value.len() > TARGETED_AUTHORING_CACHE_LIMITS_V1.path_component_bytes
        || !value.is_ascii()
        || value.bytes().any(|byte| matches!(byte, b'/' | b'\\'))
        || Path::new(value).components().count() != 1
    {
        return Err(invalid_cache_path_component(
            path,
            "one non-dot ASCII path component within the frozen byte limit",
            value,
        ));
    }
    Ok(())
}

fn invalid_cache_path_component(path: &str, expected: &str, actual: &str) -> PackageArtifactError {
    let actual = if actual.len() <= TARGETED_AUTHORING_CACHE_LIMITS_V1.path_component_bytes {
        actual.to_owned()
    } else {
        format!("{} bytes", actual.len())
    };
    PackageArtifactError::invalid_enum_value(path, "component", expected, actual)
}

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
    /// Core profile from the package manifest.
    pub package_core_profile: String,
    /// Certificate profile from the package manifest.
    pub package_certificate_profile: String,
    /// Exact certificate format emitted by the build.
    pub output_certificate_format: String,
    /// Exact core specification emitted by the build.
    pub output_core_spec: String,
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
    validate_cache_resource_limit(
        "$",
        "result_entry_bytes",
        source.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes,
    )?;
    let root = parse_artifact_json_with_limits(source, cache_json_resource_limits())?;
    let members = expect_object(&root, "$")?;
    let schema = required_string(members, "$", "schema")?;
    if schema != PACKAGE_BUILD_CHECK_RESULT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
            schema,
        ));
    }
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
        validate_cache_string(reason, "diagnostic_reason")?;
        validate_plain_string(reason, "diagnostic_reason")?;
    }
    validate_cache_string(&entry.trust_boundary, "trust_boundary")?;
    validate_plain_string(&entry.trust_boundary, "trust_boundary")?;
    validate_cache_resource_limit(
        "$",
        "result_entry_bytes",
        result_entry_json_unchecked(&normalized_result_entry(entry)).len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes,
    )
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
    validate_cache_string(&input.schema, "key_input.schema")?;
    validate_cache_string(&input.tool_version, "key_input.tool_version")?;
    validate_plain_string(&input.tool_version, "key_input.tool_version")?;
    validate_cache_string(
        &input.package_core_profile,
        "key_input.package_core_profile",
    )?;
    validate_plain_string(
        &input.package_core_profile,
        "key_input.package_core_profile",
    )?;
    validate_cache_string(
        &input.package_certificate_profile,
        "key_input.package_certificate_profile",
    )?;
    validate_plain_string(
        &input.package_certificate_profile,
        "key_input.package_certificate_profile",
    )?;
    validate_cache_string(
        &input.output_certificate_format,
        "key_input.output_certificate_format",
    )?;
    validate_plain_string(
        &input.output_certificate_format,
        "key_input.output_certificate_format",
    )?;
    validate_cache_string(&input.output_core_spec, "key_input.output_core_spec")?;
    validate_plain_string(&input.output_core_spec, "key_input.output_core_spec")?;
    validate_cache_name(&input.module, "key_input.module")?;
    validate_module_name(&input.module, "key_input.module")?;
    validate_cache_resource_limit(
        "key_input.direct_imports",
        "direct_imports",
        input.direct_imports.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
    )?;
    for (index, import) in input.direct_imports.iter().enumerate() {
        validate_cache_name(
            &import.module,
            &format!("key_input.direct_imports[{index}].module"),
        )?;
        validate_module_name(
            &import.module,
            format!("key_input.direct_imports[{index}].module"),
        )?;
    }
    validate_cache_resource_limit(
        "key_input.compiler_options",
        "compiler_options",
        input.compiler_options.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.compiler_options,
    )?;
    for (index, option) in input.compiler_options.iter().enumerate() {
        validate_cache_string(option, &format!("key_input.compiler_options[{index}]"))?;
        validate_plain_string(option, format!("key_input.compiler_options[{index}]"))?;
    }
    validate_cache_string(
        &input.package_metadata_mode,
        "key_input.package_metadata_mode",
    )?;
    validate_plain_string(
        &input.package_metadata_mode,
        "key_input.package_metadata_mode",
    )?;
    if let Some(profile) = &input.producer_profile {
        validate_cache_string(profile, "key_input.producer_profile")?;
        validate_plain_string(profile, "key_input.producer_profile")?;
    }
    Ok(())
}

const fn cache_json_resource_limits() -> JsonResourceLimits {
    JsonResourceLimits {
        nesting_depth: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_nesting_depth,
        string_bytes: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        number_bytes: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_number_bytes,
        array_elements: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_array_elements,
        object_members: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_object_members,
        array_member_elements: &[
            (
                "direct_imports",
                TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
            ),
            (
                "compiler_options",
                TARGETED_AUTHORING_CACHE_LIMITS_V1.compiler_options,
            ),
        ],
    }
}

fn validate_cache_resource_limit(
    path: &str,
    field: &str,
    observed: usize,
    maximum: usize,
) -> PackageArtifactResult<()> {
    if observed > maximum {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            field,
            format!("at most {maximum}"),
            observed.to_string(),
        ));
    }
    Ok(())
}

fn validate_cache_string(value: &str, path: &str) -> PackageArtifactResult<()> {
    validate_cache_resource_limit(
        path,
        "string_bytes",
        value.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
    )
}

fn validate_cache_name(value: &Name, path: &str) -> PackageArtifactResult<()> {
    let mut bytes = value.0.len().saturating_sub(1);
    for component in &value.0 {
        validate_cache_resource_limit(
            path,
            "path_component_bytes",
            component.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.path_component_bytes,
        )?;
        bytes = bytes.saturating_add(component.len());
    }
    validate_cache_resource_limit(
        path,
        "string_bytes",
        bytes,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
    )
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
        (
            "package_core_profile",
            json_string(&input.package_core_profile),
        ),
        (
            "package_certificate_profile",
            json_string(&input.package_certificate_profile),
        ),
        (
            "output_certificate_format",
            json_string(&input.output_certificate_format),
        ),
        ("output_core_spec", json_string(&input.output_core_spec)),
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
    let direct_imports = required_array(members, path, "direct_imports")?;
    validate_cache_resource_limit(
        "key_input.direct_imports",
        "direct_imports",
        direct_imports.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
    )?;
    Ok(PackageBuildCheckCacheKeyInput {
        schema: required_string(members, path, "schema")?,
        tool_version: required_string(members, path, "tool_version")?,
        tool_build_hash: required_hash(members, path, "tool_build_hash")?,
        package_core_profile: required_string(members, path, "package_core_profile")?,
        package_certificate_profile: required_string(members, path, "package_certificate_profile")?,
        output_certificate_format: required_string(members, path, "output_certificate_format")?,
        output_core_spec: required_string(members, path, "output_core_spec")?,
        module: required_name(members, path, "module")?,
        source_hash: required_hash(members, path, "source_hash")?,
        expected_source_hash: required_hash(members, path, "expected_source_hash")?,
        direct_imports: direct_imports
            .iter()
            .enumerate()
            .map(|(index, value)| parse_import_identity(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        compiler_options: parse_string_array(
            members,
            path,
            "compiler_options",
            TARGETED_AUTHORING_CACHE_LIMITS_V1.compiler_options,
        )?,
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
    maximum: usize,
) -> PackageArtifactResult<Vec<String>> {
    let values = required_array(members, path, field)?;
    validate_cache_resource_limit(&format!("{path}.{field}"), field, values.len(), maximum)?;
    values
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
    "package_core_profile",
    "package_certificate_profile",
    "output_certificate_format",
    "output_core_spec",
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
    fn package_cache_namespace_golden_paths_are_disjoint() {
        let validated = fixture_namespace_manifest("\"Fixture.AxiomZ\", \"Fixture.AxiomA\"");
        let material = package_build_check_cache_namespace_material(&validated);
        assert_eq!(
            material,
            r#"{"schema":"npa.package.build_check_cache_namespace.v0.1","package":"fixture","version":"1.2.3","core_spec":"npa.core.v0.1","kernel_profile":"npa.kernel.v0.1","certificate_format":"npa.certificate.canonical.v0.1","checker_profile":"npa.checker.reference.v0.1","axiom_policy":{"allow_custom_axioms":false,"allowed_axioms":["Fixture.AxiomA","Fixture.AxiomZ"]}}"#
        );

        let namespace = package_build_check_cache_namespace_digest(&validated);
        assert_eq!(
            namespace.as_str(),
            "ae7b52710ff77905eb35251db67c6b344ff53f82cb9ef98969895fb4d919282d"
        );
        assert_eq!(
            PackageCacheNamespaceDigest::parse(namespace.as_str()).unwrap(),
            namespace
        );

        let key =
            PackageCacheKeyDigest::from_cache_key(&format!("sha256:{}", "1".repeat(64))).unwrap();
        let temporary = PackageCacheTemporaryName::new(&key, "writer-7").unwrap();
        let result = PackageCacheStoreLayout::build_check_result(&namespace);
        let support = PackageCacheStoreLayout::targeted_authoring_support(&namespace);

        assert_eq!(
            package_build_check_cache_default_base_relative_path(),
            PathBuf::from(PACKAGE_BUILD_CHECK_CACHE_BASE_LAYOUT_DIR)
        );
        assert_eq!(
            package_build_check_cache_legacy_relative_path(),
            PathBuf::from(PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR)
        );
        assert_eq!(
            result.relative_path(),
            PathBuf::from("packages")
                .join(namespace.as_str())
                .join("build-check-v0.2")
        );
        assert_eq!(
            support.relative_path(),
            PathBuf::from("packages")
                .join(namespace.as_str())
                .join("targeted-authoring-support-v0.1")
        );
        assert_eq!(
            result.entry_relative_path(&key),
            result
                .relative_path()
                .join(format!("{}.json", "1".repeat(64)))
        );
        assert_eq!(
            result.temporary_relative_path(&temporary),
            result
                .relative_path()
                .join(format!("tmp-{}-writer-7.tmp", "1".repeat(64)))
        );
        assert_eq!(
            result.entry_relative_path(&key).parent(),
            Some(result.relative_path().as_path())
        );
        assert_eq!(
            result.temporary_relative_path(&temporary).parent(),
            Some(result.relative_path().as_path())
        );
        assert_ne!(result.relative_path(), support.relative_path());
        assert_ne!(
            package_build_check_cache_default_base_relative_path().join(result.relative_path()),
            package_build_check_cache_legacy_relative_path()
        );
        assert_ne!(
            package_build_check_cache_default_base_relative_path().join(support.relative_path()),
            package_build_check_cache_legacy_relative_path()
        );
    }

    #[test]
    fn package_cache_namespace_normalizes_policy_and_separates_schema_versions() {
        let first = fixture_namespace_manifest("\"Fixture.AxiomZ\", \"Fixture.AxiomA\"");
        let reordered = fixture_namespace_manifest("\"Fixture.AxiomA\", \"Fixture.AxiomZ\"");

        assert_eq!(
            package_build_check_cache_namespace_material(&first),
            package_build_check_cache_namespace_material(&reordered)
        );
        assert_eq!(
            package_build_check_cache_namespace_digest(&first),
            package_build_check_cache_namespace_digest(&reordered)
        );

        let next_schema_material = package_build_check_cache_namespace_material_with_schema(
            "npa.package.build_check_cache_namespace.v0.2",
            &first,
        );
        assert_ne!(
            package_build_check_cache_namespace_material(&first),
            next_schema_material
        );
        assert_ne!(
            package_build_check_cache_namespace_digest(&first),
            PackageCacheNamespaceDigest::from_hash(package_file_hash(
                next_schema_material.as_bytes()
            ))
        );
        assert_ne!(
            PackageCacheStoreVersion::BUILD_CHECK_RESULT,
            PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT
        );
    }

    #[test]
    fn package_cache_namespace_components_reject_hostile_spellings() {
        let digest = "a".repeat(PACKAGE_BUILD_CHECK_CACHE_DIGEST_HEX_BYTES);
        let key = PackageCacheKeyDigest::from_cache_key(&format!("sha256:{digest}")).unwrap();

        for invalid in [
            "",
            ".",
            "..",
            "a/b",
            "a\\b",
            "é",
            "e\u{301}",
            &"a".repeat(63),
            &"a".repeat(65),
            &"A".repeat(64),
            &"g".repeat(64),
        ] {
            assert!(
                PackageCacheNamespaceDigest::parse(invalid).is_err(),
                "{invalid:?}"
            );
        }

        for invalid in ["A".repeat(64), "a/".repeat(32), "a".repeat(65)] {
            assert!(
                PackageCacheKeyDigest::from_cache_key(&format!("sha256:{invalid}")).is_err(),
                "{invalid:?}"
            );
        }
        assert!(PackageCacheKeyDigest::from_cache_key(&digest).is_err());

        assert_eq!(
            PackageCacheStoreVersion::parse(PACKAGE_BUILD_CHECK_RESULT_STORE_VERSION).unwrap(),
            PackageCacheStoreVersion::BUILD_CHECK_RESULT
        );
        assert_eq!(
            PackageCacheStoreVersion::parse(PACKAGE_TARGETED_AUTHORING_SUPPORT_STORE_VERSION)
                .unwrap(),
            PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT
        );
        for invalid in [
            ".",
            "..",
            "build/check",
            "build\\check",
            "β",
            "build-check-v0.3",
        ] {
            assert!(
                PackageCacheStoreVersion::parse(invalid).is_err(),
                "{invalid:?}"
            );
        }
        assert!(PackageCacheStoreVersion::parse(&"a".repeat(256)).is_err());

        for byte in 0_u8..=127 {
            let candidate = char::from(byte).to_string();
            let accepted = PackageCacheTemporaryName::new(&key, &candidate).is_ok();
            let expected = byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-';
            assert_eq!(accepted, expected, "ASCII byte {byte}");
        }
        for invalid in ["", ".", "..", "a/b", "a\\b", "É", "e\u{301}"] {
            assert!(
                PackageCacheTemporaryName::new(&key, invalid).is_err(),
                "{invalid:?}"
            );
        }

        let fixed_name_bytes = "tmp-".len() + digest.len() + 1 + ".tmp".len();
        let exact_unique =
            "a".repeat(TARGETED_AUTHORING_CACHE_LIMITS_V1.path_component_bytes - fixed_name_bytes);
        assert_eq!(
            PackageCacheTemporaryName::new(&key, &exact_unique)
                .unwrap()
                .as_str()
                .len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.path_component_bytes
        );
        assert!(PackageCacheTemporaryName::new(&key, &format!("{exact_unique}a")).is_err());
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

    #[test]
    fn package_build_check_cache_key_changes_for_exact_output_pair() {
        let input = fixture_key_input();
        let mut changed_format = input.clone();
        changed_format.output_certificate_format = "NPA-CERT-0.3.0".to_owned();
        let mut changed_core = input.clone();
        changed_core.output_core_spec = "NPA-Core-0.3.0".to_owned();

        assert_ne!(
            package_build_check_cache_key(&input),
            package_build_check_cache_key(&changed_format)
        );
        assert_ne!(
            package_build_check_cache_key(&input),
            package_build_check_cache_key(&changed_core)
        );
    }

    #[test]
    fn package_build_check_v0_1_persistent_entry_is_a_schema_miss() {
        let json = package_build_check_result_entry_json(&fixture_result_entry(
            PackageBuildCheckCachedStatus::Accepted,
        ));
        let old = json
            .replacen(
                PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
                "npa.package.build_check_result.v0.1",
                1,
            )
            .replace("package_core_profile", "core_spec")
            .replace("package_certificate_profile", "certificate_format");

        let error = parse_package_build_check_result_entry_json(&old).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::UnsupportedSchema
        );
    }

    #[test]
    fn support_context_adversarial_limits_accept_boundary_and_reject_plus_one() {
        let limits = TARGETED_AUTHORING_CACHE_LIMITS_V1;
        let cases = [
            ("result_entry_bytes", limits.result_entry_bytes),
            ("support_entry_bytes", limits.support_entry_bytes),
            ("source_bytes", limits.source_bytes),
            ("tool_identity_bytes", limits.tool_identity_bytes),
            ("json_nesting_depth", limits.json_nesting_depth),
            ("json_string_bytes", limits.json_string_bytes),
            ("json_number_bytes", limits.json_number_bytes),
            ("json_array_elements", limits.json_array_elements),
            ("json_object_members", limits.json_object_members),
            ("path_component_bytes", limits.path_component_bytes),
            ("direct_imports", limits.direct_imports),
            ("compiler_options", limits.compiler_options),
            ("interface_declarations", limits.interface_declarations),
            (
                "interface_generated_declarations",
                limits.interface_generated_declarations,
            ),
            ("interface_notations", limits.interface_notations),
            ("interface_typeclasses", limits.interface_typeclasses),
            (
                "interface_binders_per_declaration",
                limits.interface_binders_per_declaration,
            ),
            (
                "interface_universe_parameters_per_declaration",
                limits.interface_universe_parameters_per_declaration,
            ),
            ("interface_spans", limits.interface_spans),
            (
                "interface_dependency_edges",
                limits.interface_dependency_edges,
            ),
            ("certificate_bytes", limits.certificate_bytes),
            ("certificate_imports", limits.certificate_imports),
            (
                "certificate_name_table_entries",
                limits.certificate_name_table_entries,
            ),
            (
                "certificate_level_table_nodes",
                limits.certificate_level_table_nodes,
            ),
            (
                "certificate_term_table_nodes",
                limits.certificate_term_table_nodes,
            ),
            ("certificate_declarations", limits.certificate_declarations),
            ("certificate_exports", limits.certificate_exports),
            (
                "certificate_nested_vector_entries",
                limits.certificate_nested_vector_entries,
            ),
            (
                "certificate_structural_depth",
                limits.certificate_structural_depth,
            ),
            (
                "certificate_root_expanded_nodes",
                limits.certificate_root_expanded_nodes,
            ),
            (
                "certificate_expanded_nodes",
                limits.certificate_expanded_nodes,
            ),
            ("closure_modules", limits.closure_modules),
            ("closure_expanded_nodes", limits.closure_expanded_nodes),
            ("closure_dependency_edges", limits.closure_dependency_edges),
            (
                "cache_entries_per_command",
                limits.cache_entries_per_command,
            ),
            ("retained_contexts", limits.retained_contexts),
            ("retained_context_bytes", limits.retained_context_bytes),
            ("command_loaded_bytes", limits.command_loaded_bytes),
            ("command_written_bytes", limits.command_written_bytes),
            ("detailed_diagnostics", limits.detailed_diagnostics),
            ("diagnostic_value_bytes", limits.diagnostic_value_bytes),
        ];

        for (field, maximum) in cases {
            validate_cache_resource_limit(field, field, maximum, maximum).unwrap();
            let error = validate_cache_resource_limit(field, field, maximum + 1, maximum)
                .expect_err("limit plus one must fail before a count-sized allocation");
            assert_eq!(
                error.reason_code,
                PackageArtifactErrorReason::InvalidEnumValue
            );
            assert_eq!(error.field.as_deref(), Some(field));
            assert_eq!(error.expected_value, Some(format!("at most {maximum}")));
            assert_eq!(error.actual_value, Some((maximum + 1).to_string()));
        }
    }

    #[test]
    fn support_context_adversarial_limits_reuse_certificate_structural_maxima() {
        let limits = TARGETED_AUTHORING_CACHE_LIMITS_V1;
        assert_eq!(limits.certificate_bytes, npa_cert::MAX_CERTIFICATE_BYTES);
        assert_eq!(limits.certificate_imports, npa_cert::MAX_IMPORTS);
        assert_eq!(
            limits.certificate_name_table_entries,
            npa_cert::MAX_NAME_TABLE_ENTRIES
        );
        assert_eq!(
            limits.certificate_level_table_nodes,
            npa_cert::MAX_LEVEL_TABLE_NODES
        );
        assert_eq!(
            limits.certificate_term_table_nodes,
            npa_cert::MAX_TERM_TABLE_NODES
        );
        assert_eq!(limits.certificate_declarations, npa_cert::MAX_DECLARATIONS);
        assert_eq!(limits.certificate_exports, npa_cert::MAX_EXPORTS);
        assert_eq!(
            limits.certificate_nested_vector_entries,
            npa_cert::MAX_NESTED_VECTOR_ENTRIES
        );
        assert_eq!(
            limits.certificate_structural_depth,
            npa_cert::MAX_STRUCTURAL_DEPTH
        );
        assert_eq!(
            limits.certificate_root_expanded_nodes,
            npa_cert::MAX_ROOT_EXPANDED_NODES
        );
        assert_eq!(
            limits.certificate_expanded_nodes,
            npa_cert::MAX_CERTIFICATE_EXPANDED_NODES
        );
        assert_eq!(limits.closure_modules, npa_cert::MAX_CLOSURE_MODULES);
        assert_eq!(
            limits.closure_expanded_nodes,
            npa_cert::MAX_CLOSURE_EXPANDED_NODES
        );
    }

    #[test]
    fn package_build_check_result_parser_rejects_oversize_before_json_parsing() {
        let source = " ".repeat(TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes + 1);
        let error = parse_package_build_check_result_entry_json(&source).unwrap_err();
        assert_eq!(
            error.reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(error.field.as_deref(), Some("result_entry_bytes"));
    }

    #[test]
    fn measured_cache_fixtures_fit_the_frozen_limit_profile() {
        let fixture = include_str!(
            "../../../testdata/performance/fixtures/targeted-authoring-cache-limits-v1.tsv"
        );
        let limits = TARGETED_AUTHORING_CACHE_LIMITS_V1;
        let mut rows = fixture.lines().filter(|line| !line.starts_with('#'));
        assert_eq!(
            rows.next(),
            Some("fixture\tpackage_root\tlocal_modules\tmax_direct_imports\tmax_declared_interface_records\tmax_module_name_bytes\tmax_manifest_string_bytes\tmanifest_bytes\tmax_source_bytes\ttotal_source_bytes\tmax_certificate_bytes\ttotal_certificate_bytes\tmeasured_tool_identity_bytes")
        );

        let mut row_count = 0;
        for row in rows {
            let columns = row.split('\t').collect::<Vec<_>>();
            assert_eq!(columns.len(), 13, "{row}");
            let number = |index: usize| columns[index].parse::<usize>().unwrap();
            assert!(number(2) <= limits.cache_entries_per_command, "{row}");
            assert!(number(3) <= limits.direct_imports, "{row}");
            assert!(number(4) <= limits.interface_declarations, "{row}");
            assert!(number(5) <= limits.json_string_bytes, "{row}");
            assert!(number(5) <= limits.path_component_bytes, "{row}");
            assert!(number(6) <= limits.json_string_bytes, "{row}");
            assert!(number(8) <= limits.source_bytes, "{row}");
            assert!(number(10) <= limits.certificate_bytes, "{row}");
            assert!(number(11) <= limits.retained_context_bytes, "{row}");
            assert!(number(12) <= limits.tool_identity_bytes, "{row}");
            row_count += 1;
        }
        assert_eq!(row_count, 3);
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

    fn fixture_namespace_manifest(allowed_axioms: &str) -> ValidatedPackageManifest {
        crate::validate::parse_and_validate_manifest_str(&format!(
            r#"schema = "npa.package.v0.1"
package = "fixture"
version = "1.2.3"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = []

[policy]
allow_custom_axioms = false
allowed_axioms = [{allowed_axioms}]
"#,
        ))
        .unwrap()
    }

    fn fixture_key_input() -> PackageBuildCheckCacheKeyInput {
        PackageBuildCheckCacheKeyInput {
            schema: PACKAGE_BUILD_CHECK_CACHE_SCHEMA.to_owned(),
            tool_version: "0.1.0".to_owned(),
            tool_build_hash: hash(1),
            package_core_profile: "npa.core.v0.1".to_owned(),
            package_certificate_profile: "npa.certificate.canonical.v0.1".to_owned(),
            output_certificate_format: "NPA-CERT-0.2.0".to_owned(),
            output_core_spec: "NPA-Core-0.2.0".to_owned(),
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

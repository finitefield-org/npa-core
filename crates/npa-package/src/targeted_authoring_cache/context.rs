//! Bounded, frontend-neutral targeted-authoring support-context entries.
//!
//! A reconstruction adapter must rederive the interface profile from the live
//! producer path; reread and hash the exact current source and certificate
//! bytes; validate this envelope, its key, and every source offset; and only
//! then translate spans. `current_module` spans receive the live manifest
//! module index after its checked `u32` conversion, while
//! `synthetic_fallback` spans remain `FileId(0)` with exact `0..0` offsets.
//! Neither runtime file identity nor a trusted frontend/kernel object crosses
//! this disk boundary.

use std::collections::BTreeSet;

use npa_cert::Name;

use super::{
    normalized_targeted_authoring_support_key_input, targeted_authoring_support_cache_key,
    targeted_authoring_support_key_input_json, TargetedAuthoringCertificateImportIdentity,
    TargetedAuthoringSupportKeyInput, PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
};
use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, reject_unknown_fields, required_array, required_bool, required_hash,
        required_name, required_string, required_u64, required_value,
    },
    build_check_cache::{PackageCacheNamespaceDigest, TARGETED_AUTHORING_CACHE_LIMITS_V1},
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    graph::ResolvedModuleImportIdentity,
    hash::{format_package_hash, package_file_hash, PackageHash},
    json::{parse_json_with_limits, JsonResourceLimits, JsonValue},
    manifest::{PackageModuleIdentity, PackageVersion},
    name::{validate_package_id, PackageId},
    validate_package_version,
};

/// Closed schema for the neutral Human source-interface DTO.
pub const PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA: &str =
    "npa.package.targeted_authoring_human_interface.v0.1";
/// Fixed non-authoritative authoring policy carried by every support entry.
pub const PACKAGE_TARGETED_AUTHORING_POLICY: &str =
    "npa.package.targeted_authoring.non_authoritative_local_hit.v0.1";
/// Fixed untrusted eligibility claim carried by every support entry.
pub const PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM: &str =
    "ordinary_live_complete_closure_untrusted";
/// Fixed trust-boundary statement carried by every support entry.
pub const PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY: &str =
    "Untrusted authoring cache data; never proof evidence, build evidence, or an ordinary checker verdict.";

/// Closed producer/interface family determining permitted span origins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringInterfaceProfile {
    /// Interface reconstructed live from the current Human Surface source.
    HumanSource,
    /// Legacy interface synthesized only from authenticated certificate exports.
    SyntheticCertificateFallback,
}

impl TargetedAuthoringInterfaceProfile {
    /// Human-source interface profile spelling.
    pub const HUMAN_SOURCE: &'static str = "npa.frontend.human_source_interface.v1";
    /// Synthetic certificate-fallback profile spelling.
    pub const SYNTHETIC_CERTIFICATE_FALLBACK: &'static str =
        "npa.frontend.synthetic_certificate_fallback_interface.v1";

    /// Return the canonical profile spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HumanSource => Self::HUMAN_SOURCE,
            Self::SyntheticCertificateFallback => Self::SYNTHETIC_CERTIFICATE_FALLBACK,
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            Self::HUMAN_SOURCE => Ok(Self::HumanSource),
            Self::SYNTHETIC_CERTIFICATE_FALLBACK => Ok(Self::SyntheticCertificateFallback),
            _ => Err(invalid_value(
                path,
                "interface_profile",
                format!(
                    "{} or {}",
                    Self::HUMAN_SOURCE,
                    Self::SYNTHETIC_CERTIFICATE_FALLBACK
                ),
                value,
            )),
        }
    }

    const fn expected_span_origin(self) -> TargetedAuthoringSpanOrigin {
        match self {
            Self::HumanSource => TargetedAuthoringSpanOrigin::CurrentModule,
            Self::SyntheticCertificateFallback => TargetedAuthoringSpanOrigin::SyntheticFallback,
        }
    }
}

/// Closed stable origin for a normalized Human source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringSpanOrigin {
    /// Offsets refer to the exact current module source committed by the key.
    CurrentModule,
    /// Empty offsets belong to the recognized legacy synthetic fallback.
    SyntheticFallback,
}

impl TargetedAuthoringSpanOrigin {
    /// Return the canonical origin spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CurrentModule => "current_module",
            Self::SyntheticFallback => "synthetic_fallback",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "current_module" => Ok(Self::CurrentModule),
            "synthetic_fallback" => Ok(Self::SyntheticFallback),
            _ => Err(invalid_value(
                path,
                "origin",
                "current_module or synthetic_fallback",
                value,
            )),
        }
    }
}

/// Module-index-neutral normalized source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TargetedAuthoringSpan {
    /// Closed stable span origin.
    pub origin: TargetedAuthoringSpanOrigin,
    /// Inclusive start byte offset in the exact source bytes.
    pub start: u32,
    /// Exclusive end byte offset in the exact source bytes.
    pub end: u32,
}

/// Stable package/module-relative source identity replacing runtime `FileId`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSourceIdentity {
    /// Package containing the source module.
    pub package: PackageId,
    /// Exact package version.
    pub version: PackageVersion,
    /// Canonical source module name.
    pub module: Name,
    /// Hash of the exact current source bytes.
    pub source_hash: PackageHash,
}

/// Frontend-neutral Human name with its source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanName {
    /// Name components exactly as consumed by Human resolution.
    pub parts: Vec<String>,
    /// Normalized source span.
    pub span: TargetedAuthoringSpan,
}

/// Frontend-neutral Human universe parameter metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanUniverseParameter {
    /// Universe parameter name.
    pub name: String,
    /// Normalized source span.
    pub span: TargetedAuthoringSpan,
}

/// Closed declaration-kind mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringHumanDeclarationKind {
    /// Definition.
    Def,
    /// Theorem.
    Theorem,
    /// Axiom.
    Axiom,
    /// Inductive type.
    Inductive,
    /// Typeclass declaration.
    Class,
    /// Typeclass field.
    ClassField,
    /// Typeclass instance.
    Instance,
    /// Synthetic certificate-export declaration.
    Imported,
}

/// Closed definition-reducibility mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringDefinitionReducibility {
    /// Reducible definition body.
    Reducible,
    /// Definition sealed at the module boundary.
    Opaque,
}

/// Closed binder-info mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringHumanBinderInfo {
    /// Explicit binder.
    Explicit,
    /// Implicit binder.
    Implicit,
}

/// Frontend-neutral Human declaration binder metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanBinder {
    /// Optional named binder.
    pub name: Option<TargetedAuthoringHumanName>,
    /// Closed binder-info value.
    pub binder_info: TargetedAuthoringHumanBinderInfo,
    /// Normalized binder span.
    pub span: TargetedAuthoringSpan,
}

/// Frontend-neutral Human source declaration metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanDeclaration {
    /// Closed declaration kind.
    pub kind: TargetedAuthoringHumanDeclarationKind,
    /// Definition reducibility for definition-backed runtime declaration kinds.
    pub definition_reducibility: Option<TargetedAuthoringDefinitionReducibility>,
    /// Declaration name and span.
    pub name: TargetedAuthoringHumanName,
    /// Universe parameter metadata in runtime order.
    pub universe_params: Vec<TargetedAuthoringHumanUniverseParameter>,
    /// Binder metadata in runtime order.
    pub binders: Vec<TargetedAuthoringHumanBinder>,
    /// Optional authenticated declaration-interface hash.
    pub decl_interface_hash: Option<PackageHash>,
    /// Normalized declaration span.
    pub span: TargetedAuthoringSpan,
}

/// Closed notation-kind mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringHumanNotationKind {
    /// General notation.
    Notation,
    /// Prefix notation.
    Prefix,
    /// Postfix notation.
    Postfix,
    /// Non-associative infix notation.
    Infix,
    /// Left-associative infix notation.
    Infixl,
    /// Right-associative infix notation.
    Infixr,
}

/// Closed notation-associativity mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringHumanNotationAssociativity {
    /// Left associative.
    Left,
    /// Right associative.
    Right,
    /// Non-associative.
    NonAssoc,
}

/// Frontend-neutral Human notation metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanNotation {
    /// Closed notation kind.
    pub kind: TargetedAuthoringHumanNotationKind,
    /// Closed associativity.
    pub associativity: TargetedAuthoringHumanNotationAssociativity,
    /// Parser precedence.
    pub precedence: u16,
    /// Exact notation token.
    pub token: String,
    /// Notation target name and span.
    pub target: TargetedAuthoringHumanName,
    /// Namespace components active for this notation.
    pub namespace: Vec<String>,
    /// Normalized notation span.
    pub span: TargetedAuthoringSpan,
}

/// Closed generated-declaration kind mirror of the Human authoring ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetedAuthoringHumanGeneratedDeclarationKind {
    /// Inductive constructor.
    Constructor,
    /// Inductive recursor.
    Recursor,
}

/// Frontend-neutral generated declaration metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanGeneratedDeclaration {
    /// Closed generated-declaration kind.
    pub kind: TargetedAuthoringHumanGeneratedDeclarationKind,
    /// Parent declaration name and span.
    pub parent: TargetedAuthoringHumanName,
    /// Generated declaration name and span.
    pub name: TargetedAuthoringHumanName,
    /// Optional authenticated declaration-interface hash.
    pub decl_interface_hash: Option<PackageHash>,
    /// Normalized generated-declaration span.
    pub span: TargetedAuthoringSpan,
}

/// Frontend-neutral typeclass field metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanTypeclassField {
    /// Field name and span.
    pub name: TargetedAuthoringHumanName,
    /// Generated projection name and span.
    pub projection: TargetedAuthoringHumanName,
    /// Optional authenticated declaration-interface hash.
    pub decl_interface_hash: Option<PackageHash>,
    /// Normalized field span.
    pub span: TargetedAuthoringSpan,
}

/// Frontend-neutral typeclass class metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanTypeclassClass {
    /// Class name and span.
    pub name: TargetedAuthoringHumanName,
    /// Class constructor name and span.
    pub constructor: TargetedAuthoringHumanName,
    /// Field metadata in runtime order.
    pub fields: Vec<TargetedAuthoringHumanTypeclassField>,
    /// Optional authenticated declaration-interface hash.
    pub decl_interface_hash: Option<PackageHash>,
    /// Normalized class span.
    pub span: TargetedAuthoringSpan,
}

/// Frontend-neutral typeclass instance metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanTypeclassInstance {
    /// Instance name and span.
    pub name: TargetedAuthoringHumanName,
    /// Optional resolved class name and span.
    pub class: Option<TargetedAuthoringHumanName>,
    /// Instance search priority.
    pub priority: u32,
    /// Optional authenticated declaration-interface hash.
    pub decl_interface_hash: Option<PackageHash>,
    /// Normalized instance span.
    pub span: TargetedAuthoringSpan,
}

/// Complete frontend-neutral `HumanSourceInterface` mirror.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanSourceInterface {
    /// Canonical nested source-interface module identity.
    pub module: Name,
    /// Source declaration metadata.
    pub declarations: Vec<TargetedAuthoringHumanDeclaration>,
    /// Source notation metadata.
    pub notations: Vec<TargetedAuthoringHumanNotation>,
    /// Generated declaration metadata.
    pub generated_declarations: Vec<TargetedAuthoringHumanGeneratedDeclaration>,
    /// Typeclass class metadata.
    pub typeclass_classes: Vec<TargetedAuthoringHumanTypeclassClass>,
    /// Typeclass instance metadata.
    pub typeclass_instances: Vec<TargetedAuthoringHumanTypeclassInstance>,
}

/// Complete module-index-neutral `HumanImportedSourceInterface` disk DTO.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringHumanImportedSourceInterface {
    /// Closed DTO schema.
    pub schema: String,
    /// Outer canonical imported module name.
    pub module: Name,
    /// Accepted export hash.
    pub export_hash: PackageHash,
    /// Present accepted canonical certificate hash.
    pub certificate_hash: PackageHash,
    /// Stable package/module-relative source identity.
    pub source: TargetedAuthoringSourceIdentity,
    /// Exact producer profile used to derive this interface.
    pub producer_profile: String,
    /// Direct Human import identities in manifest semantic order.
    pub direct_imports: Vec<ResolvedModuleImportIdentity>,
    /// Complete nested source interface.
    pub source_interface: TargetedAuthoringHumanSourceInterface,
}

/// Exhaustive runtime-to-neutral DTO field catalog owned by the CLI adapter contract.
///
/// The test-only source catalog check makes a newly added runtime field fail
/// `support_context_entry` tests until this neutral contract is updated.
pub const TARGETED_AUTHORING_HUMAN_INTERFACE_FIELD_CATALOG: &[(&str, &[&str])] = &[
    (
        "HumanImportedSourceInterface",
        &[
            "module",
            "export_hash",
            "certificate_hash",
            "source_interface",
        ],
    ),
    (
        "HumanSourceInterface",
        &[
            "module",
            "declarations",
            "notations",
            "generated_declarations",
            "typeclass_classes",
            "typeclass_instances",
        ],
    ),
    (
        "HumanSourceDeclarationMetadata",
        &[
            "kind",
            "definition_reducibility",
            "name",
            "universe_params",
            "binders",
            "decl_interface_hash",
            "span",
        ],
    ),
    (
        "HumanSourceBinderMetadata",
        &["name", "binder_info", "span"],
    ),
    (
        "HumanSourceNotationMetadata",
        &[
            "kind",
            "associativity",
            "precedence",
            "token",
            "target",
            "namespace",
            "span",
        ],
    ),
    (
        "HumanGeneratedDeclarationMetadata",
        &["kind", "parent", "name", "decl_interface_hash", "span"],
    ),
    (
        "HumanTypeclassClassMetadata",
        &[
            "name",
            "constructor",
            "fields",
            "decl_interface_hash",
            "span",
        ],
    ),
    (
        "HumanTypeclassFieldMetadata",
        &["name", "projection", "decl_interface_hash", "span"],
    ),
    (
        "HumanTypeclassInstanceMetadata",
        &["name", "class", "priority", "decl_interface_hash", "span"],
    ),
    ("HumanName", &["parts", "span"]),
    ("HumanUniverseParam", &["name", "span"]),
];

/// Current accepted certificate identities duplicated for cheap envelope validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringAcceptedCertificateIdentity {
    /// Accepted module name.
    pub module: Name,
    /// Exact current certificate-file hash.
    pub certificate_file_hash: PackageHash,
    /// Actual accepted export hash.
    pub export_hash: PackageHash,
    /// Actual accepted axiom-report hash.
    pub axiom_report_hash: PackageHash,
    /// Actual accepted canonical certificate hash.
    pub certificate_hash: PackageHash,
}

/// Immutable untrusted targeted-authoring support-context entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSupportContextEntry {
    /// Entry schema; must equal [`PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA`].
    pub schema: String,
    /// Deterministic support-cache key.
    pub cache_key: String,
    /// Package cache namespace digest.
    pub namespace: PackageCacheNamespaceDigest,
    /// Complete normalized key input.
    pub key_input: TargetedAuthoringSupportKeyInput,
    /// Dependency closure commitment duplicated from the key input.
    pub closure_commitment: PackageHash,
    /// Exact producer profile duplicated from the key input.
    pub producer_profile: String,
    /// Closed interface/span profile.
    pub interface_profile: TargetedAuthoringInterfaceProfile,
    /// Fixed authoring policy spelling.
    pub authoring_policy: String,
    /// Current accepted certificate identities.
    pub accepted_certificate: TargetedAuthoringAcceptedCertificateIdentity,
    /// Complete neutral Human interface DTO.
    pub source_interface: TargetedAuthoringHumanImportedSourceInterface,
    /// Integrity digest over canonical entry material excluding this field.
    pub integrity_digest: PackageHash,
    /// Fixed false trust claim.
    pub trusted: bool,
    /// Fixed false build-evidence claim.
    pub build_evidence: bool,
    /// Fixed false proof-evidence claim.
    pub proof_evidence: bool,
    /// Fixed untrusted prior-live-closure eligibility claim.
    pub live_closure_eligibility: String,
    /// Fixed trust-boundary statement.
    pub trust_boundary: String,
}

/// Per-command bounded parser accounting for cache-controlled entry work.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TargetedAuthoringSupportContextParseBudget {
    entries: usize,
    aggregate_bytes: usize,
}

impl TargetedAuthoringSupportContextParseBudget {
    /// Build an empty parse budget.
    pub const fn new() -> Self {
        Self {
            entries: 0,
            aggregate_bytes: 0,
        }
    }

    /// Return cache entries charged so far.
    pub const fn entries(&self) -> usize {
        self.entries
    }

    /// Return aggregate cache bytes charged so far.
    pub const fn aggregate_bytes(&self) -> usize {
        self.aggregate_bytes
    }
}

// Encoding, parsing, and validation follow below. Keeping the DTO definitions
// free of frontend types is the compile-time dependency boundary for TBAC-08.

macro_rules! closed_enum_codec {
    ($ty:ty, $field:literal, $expected:literal, {$($variant:path => $value:literal),+ $(,)?}) => {
        impl $ty {
            /// Return the canonical closed-enum spelling.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $($variant => $value),+
                }
            }

            fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
                match value {
                    $($value => Ok($variant)),+,
                    _ => Err(invalid_value(path, $field, $expected, value)),
                }
            }
        }
    };
}

closed_enum_codec!(
    TargetedAuthoringHumanDeclarationKind,
    "kind",
    "def, theorem, axiom, inductive, class, class_field, instance, or imported",
    {
        Self::Def => "def",
        Self::Theorem => "theorem",
        Self::Axiom => "axiom",
        Self::Inductive => "inductive",
        Self::Class => "class",
        Self::ClassField => "class_field",
        Self::Instance => "instance",
        Self::Imported => "imported",
    }
);
closed_enum_codec!(
    TargetedAuthoringDefinitionReducibility,
    "definition_reducibility",
    "reducible or opaque",
    {
        Self::Reducible => "reducible",
        Self::Opaque => "opaque",
    }
);
closed_enum_codec!(
    TargetedAuthoringHumanBinderInfo,
    "binder_info",
    "explicit or implicit",
    {
        Self::Explicit => "explicit",
        Self::Implicit => "implicit",
    }
);
closed_enum_codec!(
    TargetedAuthoringHumanNotationKind,
    "kind",
    "notation, prefix, postfix, infix, infixl, or infixr",
    {
        Self::Notation => "notation",
        Self::Prefix => "prefix",
        Self::Postfix => "postfix",
        Self::Infix => "infix",
        Self::Infixl => "infixl",
        Self::Infixr => "infixr",
    }
);
closed_enum_codec!(
    TargetedAuthoringHumanNotationAssociativity,
    "associativity",
    "left, right, or non_assoc",
    {
        Self::Left => "left",
        Self::Right => "right",
        Self::NonAssoc => "non_assoc",
    }
);
closed_enum_codec!(
    TargetedAuthoringHumanGeneratedDeclarationKind,
    "kind",
    "constructor or recursor",
    {
        Self::Constructor => "constructor",
        Self::Recursor => "recursor",
    }
);

/// Normalize a support entry and refresh its deterministic integrity digest.
///
/// This normalizes only the key's explicitly unordered semantic compiler
/// options. Identity duplicates and all other inconsistent fields are rejected.
pub fn refresh_targeted_authoring_support_context_entry(
    entry: &TargetedAuthoringSupportContextEntry,
) -> PackageArtifactResult<TargetedAuthoringSupportContextEntry> {
    let mut refreshed = entry.clone();
    refreshed.key_input = normalized_targeted_authoring_support_key_input(&refreshed.key_input);
    refreshed.cache_key =
        targeted_authoring_support_cache_key(&refreshed.key_input).map_err(cache_key_error)?;
    validate_support_context_entry(&refreshed, false)?;
    refreshed.integrity_digest = support_context_integrity_digest_unchecked(&refreshed)?;
    validate_support_context_entry(&refreshed, true)?;
    Ok(refreshed)
}

/// Canonically encode one fully validated immutable support-context entry.
pub fn targeted_authoring_support_context_entry_json(
    entry: &TargetedAuthoringSupportContextEntry,
) -> PackageArtifactResult<String> {
    validate_support_context_entry(entry, true)?;
    support_context_entry_json_unchecked(entry, true)
}

/// Compute the integrity digest expected for one otherwise valid entry.
pub fn targeted_authoring_support_context_integrity_digest(
    entry: &TargetedAuthoringSupportContextEntry,
) -> PackageArtifactResult<PackageHash> {
    validate_support_context_entry(entry, false)?;
    support_context_integrity_digest_unchecked(entry)
}

fn support_context_integrity_digest_unchecked(
    entry: &TargetedAuthoringSupportContextEntry,
) -> PackageArtifactResult<PackageHash> {
    Ok(package_file_hash(
        support_context_entry_json_unchecked(entry, false)?.as_bytes(),
    ))
}

fn support_context_entry_json_unchecked(
    entry: &TargetedAuthoringSupportContextEntry,
    include_integrity: bool,
) -> PackageArtifactResult<String> {
    let mut fields = vec![
        ("schema", json_string(&entry.schema)),
        ("cache_key", json_string(&entry.cache_key)),
        ("namespace", json_string(entry.namespace.as_str())),
        (
            "key_input",
            targeted_authoring_support_key_input_json(&entry.key_input).map_err(cache_key_error)?,
        ),
        ("closure_commitment", hash_json(entry.closure_commitment)),
        ("producer_profile", json_string(&entry.producer_profile)),
        (
            "interface_profile",
            json_string(entry.interface_profile.as_str()),
        ),
        ("authoring_policy", json_string(&entry.authoring_policy)),
        (
            "accepted_certificate",
            accepted_certificate_json(&entry.accepted_certificate),
        ),
        (
            "source_interface",
            imported_source_interface_json(&entry.source_interface),
        ),
    ];
    if include_integrity {
        fields.push(("integrity_digest", hash_json(entry.integrity_digest)));
    }
    fields.extend([
        ("trusted", json_bool(entry.trusted)),
        ("build_evidence", json_bool(entry.build_evidence)),
        ("proof_evidence", json_bool(entry.proof_evidence)),
        (
            "live_closure_eligibility",
            json_string(&entry.live_closure_eligibility),
        ),
        ("trust_boundary", json_string(&entry.trust_boundary)),
    ]);
    Ok(json_object_in_order(fields))
}

fn accepted_certificate_json(identity: &TargetedAuthoringAcceptedCertificateIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&identity.module.as_dotted())),
        (
            "certificate_file_hash",
            hash_json(identity.certificate_file_hash),
        ),
        ("export_hash", hash_json(identity.export_hash)),
        ("axiom_report_hash", hash_json(identity.axiom_report_hash)),
        ("certificate_hash", hash_json(identity.certificate_hash)),
    ])
}

fn imported_source_interface_json(
    interface: &TargetedAuthoringHumanImportedSourceInterface,
) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&interface.schema)),
        ("module", json_string(&interface.module.as_dotted())),
        ("export_hash", hash_json(interface.export_hash)),
        ("certificate_hash", hash_json(interface.certificate_hash)),
        ("source", source_identity_json(&interface.source)),
        ("producer_profile", json_string(&interface.producer_profile)),
        (
            "direct_imports",
            json_array(
                interface
                    .direct_imports
                    .iter()
                    .map(resolved_import_json)
                    .collect(),
            ),
        ),
        (
            "source_interface",
            source_interface_json(&interface.source_interface),
        ),
    ])
}

fn source_identity_json(identity: &TargetedAuthoringSourceIdentity) -> String {
    json_object_in_order(vec![
        ("package", json_string(identity.package.as_str())),
        ("version", json_string(identity.version.as_str())),
        ("module", json_string(&identity.module.as_dotted())),
        ("source_hash", hash_json(identity.source_hash)),
    ])
}

fn resolved_import_json(identity: &ResolvedModuleImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&identity.module.as_dotted())),
        ("export_hash", hash_json(identity.export_hash)),
        ("certificate_hash", hash_json(identity.certificate_hash)),
    ])
}

fn source_interface_json(interface: &TargetedAuthoringHumanSourceInterface) -> String {
    json_object_in_order(vec![
        ("module", json_string(&interface.module.as_dotted())),
        (
            "declarations",
            json_array(
                interface
                    .declarations
                    .iter()
                    .map(declaration_json)
                    .collect(),
            ),
        ),
        (
            "notations",
            json_array(interface.notations.iter().map(notation_json).collect()),
        ),
        (
            "generated_declarations",
            json_array(
                interface
                    .generated_declarations
                    .iter()
                    .map(generated_declaration_json)
                    .collect(),
            ),
        ),
        (
            "typeclass_classes",
            json_array(
                interface
                    .typeclass_classes
                    .iter()
                    .map(typeclass_class_json)
                    .collect(),
            ),
        ),
        (
            "typeclass_instances",
            json_array(
                interface
                    .typeclass_instances
                    .iter()
                    .map(typeclass_instance_json)
                    .collect(),
            ),
        ),
    ])
}

fn declaration_json(declaration: &TargetedAuthoringHumanDeclaration) -> String {
    json_object_in_order(vec![
        ("kind", json_string(declaration.kind.as_str())),
        (
            "definition_reducibility",
            optional_string_json(
                declaration
                    .definition_reducibility
                    .map(TargetedAuthoringDefinitionReducibility::as_str),
            ),
        ),
        ("name", human_name_json(&declaration.name)),
        (
            "universe_params",
            json_array(
                declaration
                    .universe_params
                    .iter()
                    .map(universe_parameter_json)
                    .collect(),
            ),
        ),
        (
            "binders",
            json_array(declaration.binders.iter().map(binder_json).collect()),
        ),
        (
            "decl_interface_hash",
            optional_hash_json(declaration.decl_interface_hash),
        ),
        ("span", span_json(declaration.span)),
    ])
}

fn universe_parameter_json(parameter: &TargetedAuthoringHumanUniverseParameter) -> String {
    json_object_in_order(vec![
        ("name", json_string(&parameter.name)),
        ("span", span_json(parameter.span)),
    ])
}

fn binder_json(binder: &TargetedAuthoringHumanBinder) -> String {
    json_object_in_order(vec![
        (
            "name",
            binder
                .name
                .as_ref()
                .map(human_name_json)
                .unwrap_or_else(|| "null".to_owned()),
        ),
        ("binder_info", json_string(binder.binder_info.as_str())),
        ("span", span_json(binder.span)),
    ])
}

fn notation_json(notation: &TargetedAuthoringHumanNotation) -> String {
    json_object_in_order(vec![
        ("kind", json_string(notation.kind.as_str())),
        (
            "associativity",
            json_string(notation.associativity.as_str()),
        ),
        ("precedence", json_u64(u64::from(notation.precedence))),
        ("token", json_string(&notation.token)),
        ("target", human_name_json(&notation.target)),
        (
            "namespace",
            json_array(
                notation
                    .namespace
                    .iter()
                    .map(|part| json_string(part))
                    .collect(),
            ),
        ),
        ("span", span_json(notation.span)),
    ])
}

fn generated_declaration_json(declaration: &TargetedAuthoringHumanGeneratedDeclaration) -> String {
    json_object_in_order(vec![
        ("kind", json_string(declaration.kind.as_str())),
        ("parent", human_name_json(&declaration.parent)),
        ("name", human_name_json(&declaration.name)),
        (
            "decl_interface_hash",
            optional_hash_json(declaration.decl_interface_hash),
        ),
        ("span", span_json(declaration.span)),
    ])
}

fn typeclass_class_json(class: &TargetedAuthoringHumanTypeclassClass) -> String {
    json_object_in_order(vec![
        ("name", human_name_json(&class.name)),
        ("constructor", human_name_json(&class.constructor)),
        (
            "fields",
            json_array(class.fields.iter().map(typeclass_field_json).collect()),
        ),
        (
            "decl_interface_hash",
            optional_hash_json(class.decl_interface_hash),
        ),
        ("span", span_json(class.span)),
    ])
}

fn typeclass_field_json(field: &TargetedAuthoringHumanTypeclassField) -> String {
    json_object_in_order(vec![
        ("name", human_name_json(&field.name)),
        ("projection", human_name_json(&field.projection)),
        (
            "decl_interface_hash",
            optional_hash_json(field.decl_interface_hash),
        ),
        ("span", span_json(field.span)),
    ])
}

fn typeclass_instance_json(instance: &TargetedAuthoringHumanTypeclassInstance) -> String {
    json_object_in_order(vec![
        ("name", human_name_json(&instance.name)),
        (
            "class",
            instance
                .class
                .as_ref()
                .map(human_name_json)
                .unwrap_or_else(|| "null".to_owned()),
        ),
        ("priority", json_u64(u64::from(instance.priority))),
        (
            "decl_interface_hash",
            optional_hash_json(instance.decl_interface_hash),
        ),
        ("span", span_json(instance.span)),
    ])
}

fn human_name_json(name: &TargetedAuthoringHumanName) -> String {
    json_object_in_order(vec![
        (
            "parts",
            json_array(name.parts.iter().map(|part| json_string(part)).collect()),
        ),
        ("span", span_json(name.span)),
    ])
}

fn span_json(span: TargetedAuthoringSpan) -> String {
    json_object_in_order(vec![
        ("origin", json_string(span.origin.as_str())),
        ("start", json_u64(u64::from(span.start))),
        ("end", json_u64(u64::from(span.end))),
    ])
}

fn optional_hash_json(hash: Option<PackageHash>) -> String {
    hash.map(hash_json).unwrap_or_else(|| "null".to_owned())
}

fn optional_string_json(value: Option<&str>) -> String {
    value.map(json_string).unwrap_or_else(|| "null".to_owned())
}

const ENTRY_FIELDS: &[&str] = &[
    "schema",
    "cache_key",
    "namespace",
    "key_input",
    "closure_commitment",
    "producer_profile",
    "interface_profile",
    "authoring_policy",
    "accepted_certificate",
    "source_interface",
    "integrity_digest",
    "trusted",
    "build_evidence",
    "proof_evidence",
    "live_closure_eligibility",
    "trust_boundary",
];
const KEY_INPUT_FIELDS: &[&str] = &[
    "cache_schema",
    "payload_schema",
    "executable_hash",
    "cli_authoring_abi",
    "frontend_authoring_abi",
    "producer_authoring_abi",
    "kernel_authoring_abi",
    "package",
    "version",
    "core_spec",
    "kernel_profile",
    "certificate_format",
    "checker_profile",
    "producer_profile",
    "semantic_compiler_options",
    "axiom_policy_hash",
    "module",
    "module_identity",
    "current_source_hash",
    "expected_source_hash",
    "current_certificate_file_hash",
    "expected_certificate_file_hash",
    "expected_export_hash",
    "expected_axiom_report_hash",
    "expected_certificate_hash",
    "actual_export_hash",
    "actual_axiom_report_hash",
    "actual_certificate_hash",
    "certificate_imports",
    "dependency_closure_commitment",
    "manifest_human_imports",
    "source_interface_schema",
    "source_interface_reconstruction_version",
];
const ACCEPTED_CERTIFICATE_FIELDS: &[&str] = &[
    "module",
    "certificate_file_hash",
    "export_hash",
    "axiom_report_hash",
    "certificate_hash",
];
const IMPORTED_INTERFACE_FIELDS: &[&str] = &[
    "schema",
    "module",
    "export_hash",
    "certificate_hash",
    "source",
    "producer_profile",
    "direct_imports",
    "source_interface",
];
const SOURCE_IDENTITY_FIELDS: &[&str] = &["package", "version", "module", "source_hash"];
const SOURCE_INTERFACE_FIELDS: &[&str] = &[
    "module",
    "declarations",
    "notations",
    "generated_declarations",
    "typeclass_classes",
    "typeclass_instances",
];
const DECLARATION_FIELDS: &[&str] = &[
    "kind",
    "definition_reducibility",
    "name",
    "universe_params",
    "binders",
    "decl_interface_hash",
    "span",
];
const UNIVERSE_PARAMETER_FIELDS: &[&str] = &["name", "span"];
const BINDER_FIELDS: &[&str] = &["name", "binder_info", "span"];
const NOTATION_FIELDS: &[&str] = &[
    "kind",
    "associativity",
    "precedence",
    "token",
    "target",
    "namespace",
    "span",
];
const GENERATED_DECLARATION_FIELDS: &[&str] =
    &["kind", "parent", "name", "decl_interface_hash", "span"];
const TYPECLASS_CLASS_FIELDS: &[&str] = &[
    "name",
    "constructor",
    "fields",
    "decl_interface_hash",
    "span",
];
const TYPECLASS_FIELD_FIELDS: &[&str] = &["name", "projection", "decl_interface_hash", "span"];
const TYPECLASS_INSTANCE_FIELDS: &[&str] =
    &["name", "class", "priority", "decl_interface_hash", "span"];
const HUMAN_NAME_FIELDS: &[&str] = &["parts", "span"];
const SPAN_FIELDS: &[&str] = &["origin", "start", "end"];
const IMPORT_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

const SUPPORT_CONTEXT_ARRAY_LIMITS: &[(&str, usize)] = &[
    (
        "semantic_compiler_options",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.compiler_options,
    ),
    (
        "certificate_imports",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.certificate_imports,
    ),
    (
        "manifest_human_imports",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
    ),
    (
        "direct_imports",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
    ),
    (
        "declarations",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_declarations,
    ),
    (
        "generated_declarations",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_generated_declarations,
    ),
    (
        "notations",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_notations,
    ),
    (
        "typeclass_classes",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_typeclasses,
    ),
    (
        "typeclass_instances",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_typeclasses,
    ),
    (
        "binders",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_binders_per_declaration,
    ),
    (
        "universe_params",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_universe_parameters_per_declaration,
    ),
    (
        "fields",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_typeclasses,
    ),
    (
        "parts",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_binders_per_declaration,
    ),
    (
        "namespace",
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_binders_per_declaration,
    ),
];

const fn support_context_json_limits() -> JsonResourceLimits {
    JsonResourceLimits {
        nesting_depth: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_nesting_depth,
        string_bytes: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        number_bytes: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_number_bytes,
        array_elements: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_array_elements,
        object_members: TARGETED_AUTHORING_CACHE_LIMITS_V1.json_object_members,
        array_member_elements: SUPPORT_CONTEXT_ARRAY_LIMITS,
    }
}

/// Parse and validate one entry with a fresh single-entry budget.
pub fn parse_targeted_authoring_support_context_entry(
    bytes: &[u8],
) -> PackageArtifactResult<TargetedAuthoringSupportContextEntry> {
    let mut budget = TargetedAuthoringSupportContextParseBudget::new();
    parse_targeted_authoring_support_context_entry_with_budget(bytes, &mut budget)
}

/// Parse and validate one entry while charging a per-command aggregate budget.
pub fn parse_targeted_authoring_support_context_entry_with_budget(
    bytes: &[u8],
    budget: &mut TargetedAuthoringSupportContextParseBudget,
) -> PackageArtifactResult<TargetedAuthoringSupportContextEntry> {
    check_resource_limit(
        "$",
        "support_entry_bytes",
        bytes.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes,
    )?;
    let next_entries = budget.entries.checked_add(1).ok_or_else(|| {
        invalid_value(
            "$",
            "cache_entries_per_command",
            "bounded entry count",
            "overflow",
        )
    })?;
    let next_bytes = budget
        .aggregate_bytes
        .checked_add(bytes.len())
        .ok_or_else(|| {
            invalid_value(
                "$",
                "command_loaded_bytes",
                "bounded aggregate bytes",
                "overflow",
            )
        })?;
    check_resource_limit(
        "$",
        "cache_entries_per_command",
        next_entries,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.cache_entries_per_command,
    )?;
    check_resource_limit(
        "$",
        "command_loaded_bytes",
        next_bytes,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes,
    )?;
    budget.entries = next_entries;
    budget.aggregate_bytes = next_bytes;

    let source = std::str::from_utf8(bytes)
        .map_err(|error| PackageArtifactError::invalid_json(format!("invalid UTF-8: {error}")))?;
    let value = parse_json_with_limits(source, support_context_json_limits())
        .map_err(|error| PackageArtifactError::invalid_json(error.to_string()))?;
    let entry = parse_support_context_entry_value(&value)?;
    validate_support_context_entry(&entry, true)?;
    let canonical = support_context_entry_json_unchecked(&entry, true)?;
    if canonical.as_bytes() != bytes {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "entry bytes differ from canonical encoding",
        ));
    }
    Ok(entry)
}

fn parse_support_context_entry_value(
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringSupportContextEntry> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, ENTRY_FIELDS)?;
    let schema = required_string(members, "$", "schema")?;
    if schema != PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "$.schema",
            "schema",
            PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
            schema,
        ));
    }
    let namespace = required_string(members, "$", "namespace")?;
    let namespace = PackageCacheNamespaceDigest::parse(&namespace).map_err(|_| {
        invalid_value(
            "$.namespace",
            "namespace",
            "64 lowercase hexadecimal characters",
            namespace,
        )
    })?;
    Ok(TargetedAuthoringSupportContextEntry {
        schema,
        cache_key: required_string(members, "$", "cache_key")?,
        namespace,
        key_input: parse_key_input(required_value(members, "$", "key_input")?)?,
        closure_commitment: required_hash(members, "$", "closure_commitment")?,
        producer_profile: required_string(members, "$", "producer_profile")?,
        interface_profile: TargetedAuthoringInterfaceProfile::parse(
            &required_string(members, "$", "interface_profile")?,
            "$.interface_profile",
        )?,
        authoring_policy: required_string(members, "$", "authoring_policy")?,
        accepted_certificate: parse_accepted_certificate(required_value(
            members,
            "$",
            "accepted_certificate",
        )?)?,
        source_interface: parse_imported_source_interface(required_value(
            members,
            "$",
            "source_interface",
        )?)?,
        integrity_digest: required_hash(members, "$", "integrity_digest")?,
        trusted: required_bool(members, "$", "trusted")?,
        build_evidence: required_bool(members, "$", "build_evidence")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
        live_closure_eligibility: required_string(members, "$", "live_closure_eligibility")?,
        trust_boundary: required_string(members, "$", "trust_boundary")?,
    })
}

fn parse_key_input(value: &JsonValue) -> PackageArtifactResult<TargetedAuthoringSupportKeyInput> {
    let path = "$.key_input";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, KEY_INPUT_FIELDS)?;
    let cache_schema = required_string(members, path, "cache_schema")?;
    if cache_schema != super::PACKAGE_TARGETED_AUTHORING_SUPPORT_KEY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "$.key_input.cache_schema",
            "cache_schema",
            super::PACKAGE_TARGETED_AUTHORING_SUPPORT_KEY_SCHEMA,
            cache_schema,
        ));
    }
    let payload_schema = required_string(members, path, "payload_schema")?;
    if payload_schema != PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "$.key_input.payload_schema",
            "payload_schema",
            PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
            payload_schema,
        ));
    }
    Ok(TargetedAuthoringSupportKeyInput {
        toolchain: super::TargetedAuthoringToolchainIdentity {
            executable_hash: required_hash(members, path, "executable_hash")?,
            cli_authoring_abi: required_string(members, path, "cli_authoring_abi")?,
            frontend_authoring_abi: required_string(members, path, "frontend_authoring_abi")?,
            producer_authoring_abi: required_string(members, path, "producer_authoring_abi")?,
            kernel_authoring_abi: required_string(members, path, "kernel_authoring_abi")?,
        },
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        core_spec: required_string(members, path, "core_spec")?,
        kernel_profile: required_string(members, path, "kernel_profile")?,
        certificate_format: required_string(members, path, "certificate_format")?,
        checker_profile: required_string(members, path, "checker_profile")?,
        producer_profile: required_string(members, path, "producer_profile")?,
        semantic_compiler_options: parse_string_array(members, path, "semantic_compiler_options")?,
        axiom_policy_hash: required_hash(members, path, "axiom_policy_hash")?,
        module: required_name(members, path, "module")?,
        module_identity: required_hash(members, path, "module_identity")?,
        current_source_hash: required_hash(members, path, "current_source_hash")?,
        expected_source_hash: required_hash(members, path, "expected_source_hash")?,
        current_certificate_file_hash: required_hash(
            members,
            path,
            "current_certificate_file_hash",
        )?,
        expected_certificate_file_hash: required_hash(
            members,
            path,
            "expected_certificate_file_hash",
        )?,
        expected_export_hash: required_hash(members, path, "expected_export_hash")?,
        expected_axiom_report_hash: required_hash(members, path, "expected_axiom_report_hash")?,
        expected_certificate_hash: required_hash(members, path, "expected_certificate_hash")?,
        actual_export_hash: required_hash(members, path, "actual_export_hash")?,
        actual_axiom_report_hash: required_hash(members, path, "actual_axiom_report_hash")?,
        actual_certificate_hash: required_hash(members, path, "actual_certificate_hash")?,
        certificate_imports: required_array(members, path, "certificate_imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_certificate_import(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        dependency_closure_commitment: required_hash(
            members,
            path,
            "dependency_closure_commitment",
        )?,
        manifest_human_imports: required_array(members, path, "manifest_human_imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_resolved_import(
                    value,
                    &format!("$.key_input.manifest_human_imports[{index}]"),
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        source_interface_schema: required_string(members, path, "source_interface_schema")?,
        source_interface_reconstruction_version: required_string(
            members,
            path,
            "source_interface_reconstruction_version",
        )?,
    })
}

fn parse_certificate_import(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringCertificateImportIdentity> {
    let path = format!("$.key_input.certificate_imports[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_FIELDS)?;
    Ok(TargetedAuthoringCertificateImportIdentity {
        module: required_name(members, &path, "module")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: parse_optional_hash(members, &path, "certificate_hash")?,
    })
}

fn parse_accepted_certificate(
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringAcceptedCertificateIdentity> {
    let path = "$.accepted_certificate";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ACCEPTED_CERTIFICATE_FIELDS)?;
    Ok(TargetedAuthoringAcceptedCertificateIdentity {
        module: required_name(members, path, "module")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
    })
}

fn parse_imported_source_interface(
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanImportedSourceInterface> {
    let path = "$.source_interface";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, IMPORTED_INTERFACE_FIELDS)?;
    let schema = required_string(members, path, "schema")?;
    if schema != PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "$.source_interface.schema",
            "schema",
            PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA,
            schema,
        ));
    }
    Ok(TargetedAuthoringHumanImportedSourceInterface {
        schema,
        module: required_name(members, path, "module")?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        source: parse_source_identity(required_value(members, path, "source")?)?,
        producer_profile: required_string(members, path, "producer_profile")?,
        direct_imports: required_array(members, path, "direct_imports")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_resolved_import(
                    value,
                    &format!("$.source_interface.direct_imports[{index}]"),
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        source_interface: parse_source_interface(required_value(
            members,
            path,
            "source_interface",
        )?)?,
    })
}

fn parse_source_identity(
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringSourceIdentity> {
    let path = "$.source_interface.source";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_IDENTITY_FIELDS)?;
    Ok(TargetedAuthoringSourceIdentity {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        module: required_name(members, path, "module")?,
        source_hash: required_hash(members, path, "source_hash")?,
    })
}

fn parse_source_interface(
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanSourceInterface> {
    let path = "$.source_interface.source_interface";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SOURCE_INTERFACE_FIELDS)?;
    Ok(TargetedAuthoringHumanSourceInterface {
        module: required_name(members, path, "module")?,
        declarations: required_array(members, path, "declarations")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_declaration(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        notations: required_array(members, path, "notations")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_notation(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        generated_declarations: required_array(members, path, "generated_declarations")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_generated_declaration(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        typeclass_classes: required_array(members, path, "typeclass_classes")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_typeclass_class(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        typeclass_instances: required_array(members, path, "typeclass_instances")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_typeclass_instance(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_declaration(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanDeclaration> {
    let path = format!("$.source_interface.source_interface.declarations[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, DECLARATION_FIELDS)?;
    Ok(TargetedAuthoringHumanDeclaration {
        kind: TargetedAuthoringHumanDeclarationKind::parse(
            &required_string(members, &path, "kind")?,
            &format!("{path}.kind"),
        )?,
        definition_reducibility: parse_optional_closed_enum(
            members,
            &path,
            "definition_reducibility",
            TargetedAuthoringDefinitionReducibility::parse,
        )?,
        name: parse_human_name(
            required_value(members, &path, "name")?,
            &format!("{path}.name"),
        )?,
        universe_params: required_array(members, &path, "universe_params")?
            .iter()
            .enumerate()
            .map(|(parameter_index, value)| {
                parse_universe_parameter(
                    value,
                    &format!("{path}.universe_params[{parameter_index}]"),
                )
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        binders: required_array(members, &path, "binders")?
            .iter()
            .enumerate()
            .map(|(binder_index, value)| {
                parse_binder(value, &format!("{path}.binders[{binder_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        decl_interface_hash: parse_optional_hash(members, &path, "decl_interface_hash")?,
        span: parse_span(
            required_value(members, &path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_universe_parameter(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<TargetedAuthoringHumanUniverseParameter> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, UNIVERSE_PARAMETER_FIELDS)?;
    Ok(TargetedAuthoringHumanUniverseParameter {
        name: required_string(members, path, "name")?,
        span: parse_span(
            required_value(members, path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_binder(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<TargetedAuthoringHumanBinder> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, BINDER_FIELDS)?;
    Ok(TargetedAuthoringHumanBinder {
        name: parse_optional_human_name(members, path, "name")?,
        binder_info: TargetedAuthoringHumanBinderInfo::parse(
            &required_string(members, path, "binder_info")?,
            &format!("{path}.binder_info"),
        )?,
        span: parse_span(
            required_value(members, path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_notation(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanNotation> {
    let path = format!("$.source_interface.source_interface.notations[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, NOTATION_FIELDS)?;
    Ok(TargetedAuthoringHumanNotation {
        kind: TargetedAuthoringHumanNotationKind::parse(
            &required_string(members, &path, "kind")?,
            &format!("{path}.kind"),
        )?,
        associativity: TargetedAuthoringHumanNotationAssociativity::parse(
            &required_string(members, &path, "associativity")?,
            &format!("{path}.associativity"),
        )?,
        precedence: checked_u16(
            required_u64(members, &path, "precedence")?,
            &format!("{path}.precedence"),
        )?,
        token: required_string(members, &path, "token")?,
        target: parse_human_name(
            required_value(members, &path, "target")?,
            &format!("{path}.target"),
        )?,
        namespace: parse_string_array(members, &path, "namespace")?,
        span: parse_span(
            required_value(members, &path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_generated_declaration(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanGeneratedDeclaration> {
    let path = format!("$.source_interface.source_interface.generated_declarations[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, GENERATED_DECLARATION_FIELDS)?;
    Ok(TargetedAuthoringHumanGeneratedDeclaration {
        kind: TargetedAuthoringHumanGeneratedDeclarationKind::parse(
            &required_string(members, &path, "kind")?,
            &format!("{path}.kind"),
        )?,
        parent: parse_human_name(
            required_value(members, &path, "parent")?,
            &format!("{path}.parent"),
        )?,
        name: parse_human_name(
            required_value(members, &path, "name")?,
            &format!("{path}.name"),
        )?,
        decl_interface_hash: parse_optional_hash(members, &path, "decl_interface_hash")?,
        span: parse_span(
            required_value(members, &path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_typeclass_class(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanTypeclassClass> {
    let path = format!("$.source_interface.source_interface.typeclass_classes[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, TYPECLASS_CLASS_FIELDS)?;
    Ok(TargetedAuthoringHumanTypeclassClass {
        name: parse_human_name(
            required_value(members, &path, "name")?,
            &format!("{path}.name"),
        )?,
        constructor: parse_human_name(
            required_value(members, &path, "constructor")?,
            &format!("{path}.constructor"),
        )?,
        fields: required_array(members, &path, "fields")?
            .iter()
            .enumerate()
            .map(|(field_index, value)| {
                parse_typeclass_field(value, &format!("{path}.fields[{field_index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        decl_interface_hash: parse_optional_hash(members, &path, "decl_interface_hash")?,
        span: parse_span(
            required_value(members, &path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_typeclass_field(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<TargetedAuthoringHumanTypeclassField> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TYPECLASS_FIELD_FIELDS)?;
    Ok(TargetedAuthoringHumanTypeclassField {
        name: parse_human_name(
            required_value(members, path, "name")?,
            &format!("{path}.name"),
        )?,
        projection: parse_human_name(
            required_value(members, path, "projection")?,
            &format!("{path}.projection"),
        )?,
        decl_interface_hash: parse_optional_hash(members, path, "decl_interface_hash")?,
        span: parse_span(
            required_value(members, path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_typeclass_instance(
    index: usize,
    value: &JsonValue,
) -> PackageArtifactResult<TargetedAuthoringHumanTypeclassInstance> {
    let path = format!("$.source_interface.source_interface.typeclass_instances[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, TYPECLASS_INSTANCE_FIELDS)?;
    Ok(TargetedAuthoringHumanTypeclassInstance {
        name: parse_human_name(
            required_value(members, &path, "name")?,
            &format!("{path}.name"),
        )?,
        class: parse_optional_human_name(members, &path, "class")?,
        priority: checked_u32(
            required_u64(members, &path, "priority")?,
            &format!("{path}.priority"),
        )?,
        decl_interface_hash: parse_optional_hash(members, &path, "decl_interface_hash")?,
        span: parse_span(
            required_value(members, &path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_human_name(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<TargetedAuthoringHumanName> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, HUMAN_NAME_FIELDS)?;
    Ok(TargetedAuthoringHumanName {
        parts: parse_string_array(members, path, "parts")?,
        span: parse_span(
            required_value(members, path, "span")?,
            &format!("{path}.span"),
        )?,
    })
}

fn parse_span(value: &JsonValue, path: &str) -> PackageArtifactResult<TargetedAuthoringSpan> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SPAN_FIELDS)?;
    Ok(TargetedAuthoringSpan {
        origin: TargetedAuthoringSpanOrigin::parse(
            &required_string(members, path, "origin")?,
            &format!("{path}.origin"),
        )?,
        start: checked_u32(
            required_u64(members, path, "start")?,
            &format!("{path}.start"),
        )?,
        end: checked_u32(required_u64(members, path, "end")?, &format!("{path}.end"))?,
    })
}

fn parse_resolved_import(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<ResolvedModuleImportIdentity> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, IMPORT_FIELDS)?;
    Ok(ResolvedModuleImportIdentity {
        module: required_name(members, path, "module")?,
        export_hash: required_hash(members, path, "export_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
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

fn parse_optional_hash(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<PackageHash>> {
    let value = required_value(members, path, field)?;
    match value {
        JsonValue::Null => Ok(None),
        JsonValue::String(value) => crate::parse_package_hash(value, format!("{path}.{field}"))
            .map(Some)
            .map_err(|_| {
                PackageArtifactError::invalid_hash_format(format!("{path}.{field}"), value)
            }),
        _ => Err(PackageArtifactError::wrong_type(
            format!("{path}.{field}"),
            Some(field.to_owned()),
            "string or null",
            value.kind().as_str(),
        )),
    }
}

fn parse_optional_human_name(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<TargetedAuthoringHumanName>> {
    let value = required_value(members, path, field)?;
    if matches!(value, JsonValue::Null) {
        Ok(None)
    } else {
        parse_human_name(value, &format!("{path}.{field}")).map(Some)
    }
}

fn parse_optional_closed_enum<T>(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
    parse: fn(&str, &str) -> PackageArtifactResult<T>,
) -> PackageArtifactResult<Option<T>> {
    let value = required_value(members, path, field)?;
    match value {
        JsonValue::Null => Ok(None),
        JsonValue::String(value) => parse(value, &format!("{path}.{field}")).map(Some),
        _ => Err(PackageArtifactError::wrong_type(
            format!("{path}.{field}"),
            Some(field.to_owned()),
            "string or null",
            value.kind().as_str(),
        )),
    }
}

fn checked_u16(value: u64, path: &str) -> PackageArtifactResult<u16> {
    u16::try_from(value).map_err(|_| invalid_value(path, "number", "u16", value.to_string()))
}

fn checked_u32(value: u64, path: &str) -> PackageArtifactResult<u32> {
    u32::try_from(value).map_err(|_| invalid_value(path, "number", "u32", value.to_string()))
}

fn validate_support_context_entry(
    entry: &TargetedAuthoringSupportContextEntry,
    check_integrity: bool,
) -> PackageArtifactResult<()> {
    require_exact(
        "$.schema",
        "schema",
        PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
        &entry.schema,
    )?;
    require_false("$.trusted", "trusted", entry.trusted)?;
    require_false("$.build_evidence", "build_evidence", entry.build_evidence)?;
    require_false("$.proof_evidence", "proof_evidence", entry.proof_evidence)?;
    require_exact(
        "$.authoring_policy",
        "authoring_policy",
        PACKAGE_TARGETED_AUTHORING_POLICY,
        &entry.authoring_policy,
    )?;
    require_exact(
        "$.live_closure_eligibility",
        "live_closure_eligibility",
        PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM,
        &entry.live_closure_eligibility,
    )?;
    require_exact(
        "$.trust_boundary",
        "trust_boundary",
        PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY,
        &entry.trust_boundary,
    )?;

    let normalized = normalized_targeted_authoring_support_key_input(&entry.key_input);
    if normalized != entry.key_input {
        return Err(PackageArtifactError::non_canonical(
            "$.key_input.semantic_compiler_options",
            "compiler options are not sorted and unique",
        ));
    }
    targeted_authoring_support_key_input_json(&entry.key_input).map_err(cache_key_error)?;
    validate_key_input_domains(&entry.key_input)?;
    let expected_key =
        targeted_authoring_support_cache_key(&entry.key_input).map_err(cache_key_error)?;
    require_exact("$.cache_key", "cache_key", &expected_key, &entry.cache_key)?;

    require_hash(
        "$.closure_commitment",
        "closure_commitment",
        entry.key_input.dependency_closure_commitment,
        entry.closure_commitment,
    )?;
    require_exact(
        "$.producer_profile",
        "producer_profile",
        &entry.key_input.producer_profile,
        &entry.producer_profile,
    )?;
    validate_text(&entry.producer_profile, "$.producer_profile")?;

    let accepted = &entry.accepted_certificate;
    require_name(
        "$.accepted_certificate.module",
        "module",
        &entry.key_input.module,
        &accepted.module,
    )?;
    require_hash(
        "$.accepted_certificate.certificate_file_hash",
        "certificate_file_hash",
        entry.key_input.current_certificate_file_hash,
        accepted.certificate_file_hash,
    )?;
    require_hash(
        "$.accepted_certificate.export_hash",
        "export_hash",
        entry.key_input.actual_export_hash,
        accepted.export_hash,
    )?;
    require_hash(
        "$.accepted_certificate.axiom_report_hash",
        "axiom_report_hash",
        entry.key_input.actual_axiom_report_hash,
        accepted.axiom_report_hash,
    )?;
    require_hash(
        "$.accepted_certificate.certificate_hash",
        "certificate_hash",
        entry.key_input.actual_certificate_hash,
        accepted.certificate_hash,
    )?;

    validate_imported_source_interface(
        &entry.source_interface,
        &entry.key_input,
        entry.interface_profile,
    )?;

    if check_integrity {
        let expected = support_context_integrity_digest_unchecked(entry)?;
        if expected != entry.integrity_digest {
            return Err(PackageArtifactError::self_hash_mismatch(
                "$.integrity_digest",
                "integrity_digest",
                format_package_hash(&expected),
                format_package_hash(&entry.integrity_digest),
            ));
        }
    }
    Ok(())
}

fn validate_key_input_domains(
    input: &TargetedAuthoringSupportKeyInput,
) -> PackageArtifactResult<()> {
    validate_package_id(&input.package, "$.key_input.package").map_err(|_| {
        PackageArtifactError::invalid_package_id("$.key_input.package", input.package.as_str())
    })?;
    validate_package_version(&input.version, "$.key_input.version").map_err(|_| {
        PackageArtifactError::invalid_version("$.key_input.version", input.version.as_str())
    })?;
    validate_module_name(&input.module, "$.key_input.module")?;
    let expected_module_identity =
        super::targeted_authoring_module_identity(&PackageModuleIdentity {
            package: input.package.clone(),
            version: input.version.clone(),
            module: input.module.clone(),
        });
    require_hash(
        "$.key_input.module_identity",
        "module_identity",
        expected_module_identity,
        input.module_identity,
    )?;
    for (index, import) in input.certificate_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            &format!("$.key_input.certificate_imports[{index}].module"),
        )?;
    }
    for (index, import) in input.manifest_human_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            &format!("$.key_input.manifest_human_imports[{index}].module"),
        )?;
    }
    for (field, value) in [
        (
            "cli_authoring_abi",
            input.toolchain.cli_authoring_abi.as_str(),
        ),
        (
            "frontend_authoring_abi",
            input.toolchain.frontend_authoring_abi.as_str(),
        ),
        (
            "producer_authoring_abi",
            input.toolchain.producer_authoring_abi.as_str(),
        ),
        (
            "kernel_authoring_abi",
            input.toolchain.kernel_authoring_abi.as_str(),
        ),
        ("core_spec", input.core_spec.as_str()),
        ("kernel_profile", input.kernel_profile.as_str()),
        ("certificate_format", input.certificate_format.as_str()),
        ("checker_profile", input.checker_profile.as_str()),
        ("producer_profile", input.producer_profile.as_str()),
        (
            "source_interface_schema",
            input.source_interface_schema.as_str(),
        ),
        (
            "source_interface_reconstruction_version",
            input.source_interface_reconstruction_version.as_str(),
        ),
    ] {
        validate_text(value, &format!("$.key_input.{field}"))?;
    }
    for (index, option) in input.semantic_compiler_options.iter().enumerate() {
        validate_text(
            option,
            &format!("$.key_input.semantic_compiler_options[{index}]"),
        )?;
    }
    Ok(())
}

fn validate_imported_source_interface(
    interface: &TargetedAuthoringHumanImportedSourceInterface,
    key: &TargetedAuthoringSupportKeyInput,
    profile: TargetedAuthoringInterfaceProfile,
) -> PackageArtifactResult<()> {
    require_exact(
        "$.source_interface.schema",
        "schema",
        PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA,
        &interface.schema,
    )?;
    require_exact(
        "$.key_input.source_interface_schema",
        "source_interface_schema",
        &interface.schema,
        &key.source_interface_schema,
    )?;
    require_name(
        "$.source_interface.module",
        "module",
        &key.module,
        &interface.module,
    )?;
    require_hash(
        "$.source_interface.export_hash",
        "export_hash",
        key.actual_export_hash,
        interface.export_hash,
    )?;
    require_hash(
        "$.source_interface.certificate_hash",
        "certificate_hash",
        key.actual_certificate_hash,
        interface.certificate_hash,
    )?;
    require_exact(
        "$.source_interface.producer_profile",
        "producer_profile",
        &key.producer_profile,
        &interface.producer_profile,
    )?;
    if interface.direct_imports != key.manifest_human_imports {
        return Err(identity_mismatch(
            "$.source_interface.direct_imports",
            "direct_imports",
            "key_input.manifest_human_imports",
            "different import identities or order",
        ));
    }
    let source = &interface.source;
    if source.package != key.package || source.version != key.version {
        return Err(identity_mismatch(
            "$.source_interface.source",
            "package_version",
            format!("{}@{}", key.package.as_str(), key.version.as_str()),
            format!("{}@{}", source.package.as_str(), source.version.as_str()),
        ));
    }
    require_name(
        "$.source_interface.source.module",
        "module",
        &key.module,
        &source.module,
    )?;
    require_hash(
        "$.source_interface.source.source_hash",
        "source_hash",
        key.current_source_hash,
        source.source_hash,
    )?;
    require_name(
        "$.source_interface.source_interface.module",
        "module",
        &key.module,
        &interface.source_interface.module,
    )?;
    validate_module_name(&interface.module, "$.source_interface.module")?;
    validate_module_name(
        &interface.source_interface.module,
        "$.source_interface.source_interface.module",
    )?;
    validate_text(
        &interface.producer_profile,
        "$.source_interface.producer_profile",
    )?;
    for (index, import) in interface.direct_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            &format!("$.source_interface.direct_imports[{index}].module"),
        )?;
    }
    validate_human_source_interface(
        &interface.source_interface,
        &interface.direct_imports,
        profile,
    )
}

struct InterfaceValidationState {
    expected_origin: TargetedAuthoringSpanOrigin,
    span_count: usize,
    dependency_edges: usize,
}

impl InterfaceValidationState {
    fn new(profile: TargetedAuthoringInterfaceProfile, direct_imports: usize) -> Self {
        Self {
            expected_origin: profile.expected_span_origin(),
            span_count: 0,
            dependency_edges: direct_imports,
        }
    }

    fn add_edges(&mut self, count: usize, path: &str) -> PackageArtifactResult<()> {
        self.dependency_edges = self.dependency_edges.checked_add(count).ok_or_else(|| {
            invalid_value(
                path,
                "interface_dependency_edges",
                "bounded count",
                "overflow",
            )
        })?;
        check_resource_limit(
            path,
            "interface_dependency_edges",
            self.dependency_edges,
            TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_dependency_edges,
        )
    }

    fn validate_span(
        &mut self,
        span: TargetedAuthoringSpan,
        path: &str,
    ) -> PackageArtifactResult<()> {
        self.span_count = self
            .span_count
            .checked_add(1)
            .ok_or_else(|| invalid_value(path, "interface_spans", "bounded count", "overflow"))?;
        check_resource_limit(
            path,
            "interface_spans",
            self.span_count,
            TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_spans,
        )?;
        if span.origin != self.expected_origin {
            return Err(identity_mismatch(
                path,
                "origin",
                self.expected_origin.as_str(),
                span.origin.as_str(),
            ));
        }
        if span.start > span.end {
            return Err(invalid_value(
                path,
                "span_offsets",
                "start <= end",
                format!("{}..{}", span.start, span.end),
            ));
        }
        if span.origin == TargetedAuthoringSpanOrigin::SyntheticFallback
            && (span.start != 0 || span.end != 0)
        {
            return Err(invalid_value(
                path,
                "synthetic_fallback_offsets",
                "0..0",
                format!("{}..{}", span.start, span.end),
            ));
        }
        Ok(())
    }
}

fn validate_human_source_interface(
    interface: &TargetedAuthoringHumanSourceInterface,
    direct_imports: &[ResolvedModuleImportIdentity],
    profile: TargetedAuthoringInterfaceProfile,
) -> PackageArtifactResult<()> {
    check_resource_limit(
        "$.source_interface.source_interface.declarations",
        "interface_declarations",
        interface.declarations.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_declarations,
    )?;
    check_resource_limit(
        "$.source_interface.source_interface.notations",
        "interface_notations",
        interface.notations.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_notations,
    )?;
    check_resource_limit(
        "$.source_interface.source_interface.generated_declarations",
        "interface_generated_declarations",
        interface.generated_declarations.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_generated_declarations,
    )?;
    let typeclass_records = interface
        .typeclass_classes
        .iter()
        .try_fold(interface.typeclass_instances.len(), |total, class| {
            total.checked_add(1 + class.fields.len())
        })
        .ok_or_else(|| {
            invalid_value(
                "$.source_interface.source_interface.typeclass_classes",
                "interface_typeclasses",
                "bounded count",
                "overflow",
            )
        })?;
    check_resource_limit(
        "$.source_interface.source_interface.typeclass_classes",
        "interface_typeclasses",
        typeclass_records,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_typeclasses,
    )?;

    if profile == TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback
        && (!interface.notations.is_empty()
            || !interface.generated_declarations.is_empty()
            || !interface.typeclass_classes.is_empty()
            || !interface.typeclass_instances.is_empty())
    {
        return Err(invalid_value(
            "$.source_interface.source_interface",
            "interface_profile",
            "synthetic fallback declarations only",
            "Human metadata present",
        ));
    }

    let imported_modules = direct_imports
        .iter()
        .map(|import| import.module.0.clone())
        .collect::<Vec<_>>();
    let mut catalog = BTreeSet::new();
    let mut state = InterfaceValidationState::new(profile, direct_imports.len());

    for (index, declaration) in interface.declarations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.declarations[{index}]");
        if profile == TargetedAuthoringInterfaceProfile::HumanSource
            && declaration.kind == TargetedAuthoringHumanDeclarationKind::Imported
        {
            return Err(invalid_value(
                &path,
                "interface_profile",
                "non-imported Human source declaration",
                declaration.kind.as_str(),
            ));
        }
        if profile == TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback
            && (declaration.kind != TargetedAuthoringHumanDeclarationKind::Imported
                || !declaration.binders.is_empty())
        {
            return Err(invalid_value(
                &path,
                "interface_profile",
                "imported declaration without binders",
                declaration.kind.as_str(),
            ));
        }
        if declaration.definition_reducibility.is_some()
            && !matches!(
                declaration.kind,
                TargetedAuthoringHumanDeclarationKind::Def
                    | TargetedAuthoringHumanDeclarationKind::ClassField
                    | TargetedAuthoringHumanDeclarationKind::Instance
                    | TargetedAuthoringHumanDeclarationKind::Imported
            )
        {
            return Err(invalid_value(
                format!("{path}.definition_reducibility"),
                "definition_reducibility",
                "null except on def/class_field/instance/imported",
                declaration.kind.as_str(),
            ));
        }
        let name = validate_human_name(&declaration.name, &format!("{path}.name"), &mut state)?;
        if !catalog.insert(name.clone()) {
            return Err(duplicate_identity(&path, "declaration", name));
        }
        check_resource_limit(
            &format!("{path}.universe_params"),
            "interface_universe_parameters_per_declaration",
            declaration.universe_params.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_universe_parameters_per_declaration,
        )?;
        check_resource_limit(
            &format!("{path}.binders"),
            "interface_binders_per_declaration",
            declaration.binders.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_binders_per_declaration,
        )?;
        for (parameter_index, parameter) in declaration.universe_params.iter().enumerate() {
            validate_component(
                &parameter.name,
                &format!("{path}.universe_params[{parameter_index}].name"),
            )?;
            state.validate_span(
                parameter.span,
                &format!("{path}.universe_params[{parameter_index}].span"),
            )?;
        }
        for (binder_index, binder) in declaration.binders.iter().enumerate() {
            if let Some(name) = &binder.name {
                validate_human_name(
                    name,
                    &format!("{path}.binders[{binder_index}].name"),
                    &mut state,
                )?;
            }
            state.validate_span(binder.span, &format!("{path}.binders[{binder_index}].span"))?;
        }
        state.validate_span(declaration.span, &format!("{path}.span"))?;
    }

    for (index, generated) in interface.generated_declarations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.generated_declarations[{index}]");
        let parent = validate_human_name(&generated.parent, &format!("{path}.parent"), &mut state)?;
        require_catalog_target(
            &parent,
            &catalog,
            &imported_modules,
            &format!("{path}.parent"),
        )?;
        let name = validate_human_name(&generated.name, &format!("{path}.name"), &mut state)?;
        if !catalog.insert(name.clone()) {
            return Err(duplicate_identity(&path, "generated_declaration", name));
        }
        state.validate_span(generated.span, &format!("{path}.span"))?;
        state.add_edges(2, &path)?;
    }

    for (index, notation) in interface.notations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.notations[{index}]");
        validate_text(&notation.token, &format!("{path}.token"))?;
        for (part_index, part) in notation.namespace.iter().enumerate() {
            validate_component(part, &format!("{path}.namespace[{part_index}]"))?;
        }
        let target = validate_human_name(&notation.target, &format!("{path}.target"), &mut state)?;
        require_catalog_target(
            &target,
            &catalog,
            &imported_modules,
            &format!("{path}.target"),
        )?;
        state.validate_span(notation.span, &format!("{path}.span"))?;
        state.add_edges(1, &path)?;
    }

    for (index, class) in interface.typeclass_classes.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.typeclass_classes[{index}]");
        let name = validate_human_name(&class.name, &format!("{path}.name"), &mut state)?;
        require_catalog_target(&name, &catalog, &imported_modules, &format!("{path}.name"))?;
        let constructor = validate_human_name(
            &class.constructor,
            &format!("{path}.constructor"),
            &mut state,
        )?;
        require_catalog_target(
            &constructor,
            &catalog,
            &imported_modules,
            &format!("{path}.constructor"),
        )?;
        state.add_edges(1, &path)?;
        for (field_index, field) in class.fields.iter().enumerate() {
            let field_path = format!("{path}.fields[{field_index}]");
            // Human stores the source-level field label here; unlike the
            // generated projection below it is not a global catalog target.
            validate_human_name(&field.name, &format!("{field_path}.name"), &mut state)?;
            let projection = validate_human_name(
                &field.projection,
                &format!("{field_path}.projection"),
                &mut state,
            )?;
            require_catalog_target(
                &projection,
                &catalog,
                &imported_modules,
                &format!("{field_path}.projection"),
            )?;
            state.validate_span(field.span, &format!("{field_path}.span"))?;
            state.add_edges(2, &field_path)?;
        }
        state.validate_span(class.span, &format!("{path}.span"))?;
    }

    for (index, instance) in interface.typeclass_instances.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.typeclass_instances[{index}]");
        let name = validate_human_name(&instance.name, &format!("{path}.name"), &mut state)?;
        require_catalog_target(&name, &catalog, &imported_modules, &format!("{path}.name"))?;
        if let Some(class) = &instance.class {
            let class_name = validate_human_name(class, &format!("{path}.class"), &mut state)?;
            require_catalog_target(
                &class_name,
                &catalog,
                &imported_modules,
                &format!("{path}.class"),
            )?;
            state.add_edges(1, &path)?;
        }
        state.validate_span(instance.span, &format!("{path}.span"))?;
    }
    Ok(())
}

/// Validate every normalized Human span against exact current UTF-8 source bytes.
///
/// Reconstruction adapters must call this before replacing `current_module`
/// origins with a runtime module index. Synthetic fallback spans remain exact
/// empty offsets and never consume a runtime index.
pub fn validate_targeted_authoring_support_context_source_bytes(
    entry: &TargetedAuthoringSupportContextEntry,
    source_bytes: &[u8],
) -> PackageArtifactResult<()> {
    validate_support_context_entry(entry, true)?;
    check_resource_limit(
        "source_bytes",
        "source_bytes",
        source_bytes.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.source_bytes,
    )?;
    let actual_hash = package_file_hash(source_bytes);
    require_hash(
        "source_bytes",
        "source_hash",
        entry.key_input.current_source_hash,
        actual_hash,
    )?;
    let source = std::str::from_utf8(source_bytes).map_err(|_| {
        invalid_value(
            "source_bytes",
            "utf8",
            "valid UTF-8 current source",
            "invalid UTF-8",
        )
    })?;
    visit_interface_spans(
        &entry.source_interface.source_interface,
        &mut |span, path| {
            if span.origin == TargetedAuthoringSpanOrigin::CurrentModule {
                let start = usize::try_from(span.start).map_err(|_| {
                    invalid_value(
                        path,
                        "start",
                        "platform usize offset",
                        span.start.to_string(),
                    )
                })?;
                let end = usize::try_from(span.end).map_err(|_| {
                    invalid_value(path, "end", "platform usize offset", span.end.to_string())
                })?;
                if end > source.len()
                    || !source.is_char_boundary(start)
                    || !source.is_char_boundary(end)
                {
                    return Err(invalid_value(
                        path,
                        "span_offsets",
                        "UTF-8 boundaries within exact current source",
                        format!("{}..{} of {}", span.start, span.end, source.len()),
                    ));
                }
            }
            Ok(())
        },
    )
}

fn validate_human_name(
    name: &TargetedAuthoringHumanName,
    path: &str,
    state: &mut InterfaceValidationState,
) -> PackageArtifactResult<String> {
    if name.parts.is_empty() {
        return Err(invalid_value(
            format!("{path}.parts"),
            "parts",
            "non-empty canonical Human name",
            "empty",
        ));
    }
    for (index, part) in name.parts.iter().enumerate() {
        validate_component(part, &format!("{path}.parts[{index}]"))?;
    }
    let canonical = Name(name.parts.clone());
    if !canonical.is_canonical() {
        return Err(PackageArtifactError::invalid_declaration_name(
            format!("{path}.parts"),
            canonical.as_dotted(),
        ));
    }
    state.validate_span(name.span, &format!("{path}.span"))?;
    Ok(canonical.as_dotted())
}

fn require_catalog_target(
    target: &str,
    catalog: &BTreeSet<String>,
    imported_modules: &[Vec<String>],
    path: &str,
) -> PackageArtifactResult<()> {
    let target_name = Name::from_dotted(target);
    let imported = imported_modules.iter().any(|module| {
        target_name.0.len() > module.len() && target_name.0.starts_with(module.as_slice())
    });
    if catalog.contains(target) || imported {
        Ok(())
    } else {
        Err(identity_mismatch(
            path,
            "target",
            "cached declaration/generated-declaration or direct imported module member",
            target,
        ))
    }
}

fn visit_interface_spans(
    interface: &TargetedAuthoringHumanSourceInterface,
    visit: &mut impl FnMut(TargetedAuthoringSpan, &str) -> PackageArtifactResult<()>,
) -> PackageArtifactResult<()> {
    for (index, declaration) in interface.declarations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.declarations[{index}]");
        visit_human_name_spans(&declaration.name, &format!("{path}.name"), visit)?;
        for (parameter_index, parameter) in declaration.universe_params.iter().enumerate() {
            visit(
                parameter.span,
                &format!("{path}.universe_params[{parameter_index}].span"),
            )?;
        }
        for (binder_index, binder) in declaration.binders.iter().enumerate() {
            if let Some(name) = &binder.name {
                visit_human_name_spans(
                    name,
                    &format!("{path}.binders[{binder_index}].name"),
                    visit,
                )?;
            }
            visit(binder.span, &format!("{path}.binders[{binder_index}].span"))?;
        }
        visit(declaration.span, &format!("{path}.span"))?;
    }
    for (index, notation) in interface.notations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.notations[{index}]");
        visit_human_name_spans(&notation.target, &format!("{path}.target"), visit)?;
        visit(notation.span, &format!("{path}.span"))?;
    }
    for (index, generated) in interface.generated_declarations.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.generated_declarations[{index}]");
        visit_human_name_spans(&generated.parent, &format!("{path}.parent"), visit)?;
        visit_human_name_spans(&generated.name, &format!("{path}.name"), visit)?;
        visit(generated.span, &format!("{path}.span"))?;
    }
    for (index, class) in interface.typeclass_classes.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.typeclass_classes[{index}]");
        visit_human_name_spans(&class.name, &format!("{path}.name"), visit)?;
        visit_human_name_spans(&class.constructor, &format!("{path}.constructor"), visit)?;
        for (field_index, field) in class.fields.iter().enumerate() {
            let field_path = format!("{path}.fields[{field_index}]");
            visit_human_name_spans(&field.name, &format!("{field_path}.name"), visit)?;
            visit_human_name_spans(
                &field.projection,
                &format!("{field_path}.projection"),
                visit,
            )?;
            visit(field.span, &format!("{field_path}.span"))?;
        }
        visit(class.span, &format!("{path}.span"))?;
    }
    for (index, instance) in interface.typeclass_instances.iter().enumerate() {
        let path = format!("$.source_interface.source_interface.typeclass_instances[{index}]");
        visit_human_name_spans(&instance.name, &format!("{path}.name"), visit)?;
        if let Some(class) = &instance.class {
            visit_human_name_spans(class, &format!("{path}.class"), visit)?;
        }
        visit(instance.span, &format!("{path}.span"))?;
    }
    Ok(())
}

fn visit_human_name_spans(
    name: &TargetedAuthoringHumanName,
    path: &str,
    visit: &mut impl FnMut(TargetedAuthoringSpan, &str) -> PackageArtifactResult<()>,
) -> PackageArtifactResult<()> {
    visit(name.span, &format!("{path}.span"))
}

fn validate_module_name(name: &Name, path: &str) -> PackageArtifactResult<()> {
    if name.is_canonical() {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_module_name(
            path,
            name.as_dotted(),
        ))
    }
}

fn validate_component(value: &str, path: &str) -> PackageArtifactResult<()> {
    let name = Name(vec![value.to_owned()]);
    if name.is_canonical() {
        validate_text(value, path)
    } else {
        Err(PackageArtifactError::invalid_declaration_name(path, value))
    }
}

fn validate_text(value: &str, path: &str) -> PackageArtifactResult<()> {
    check_resource_limit(
        path,
        "string_bytes",
        value.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
    )?;
    if value.is_empty() || value.chars().any(char::is_control) {
        return Err(invalid_value(
            path,
            "string",
            "non-empty string without control characters",
            value,
        ));
    }
    Ok(())
}

fn require_false(path: &str, field: &str, actual: bool) -> PackageArtifactResult<()> {
    if actual {
        Err(invalid_value(path, field, "false", "true"))
    } else {
        Ok(())
    }
}

fn require_exact(
    path: &str,
    field: &str,
    expected: &str,
    actual: &str,
) -> PackageArtifactResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(identity_mismatch(path, field, expected, actual))
    }
}

fn require_hash(
    path: &str,
    field: &str,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageArtifactResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(identity_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn require_name(
    path: &str,
    field: &str,
    expected: &Name,
    actual: &Name,
) -> PackageArtifactResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(identity_mismatch(
            path,
            field,
            expected.as_dotted(),
            actual.as_dotted(),
        ))
    }
}

fn identity_mismatch(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactError {
    PackageArtifactError::identity_mismatch(path, field, expected, actual)
}

fn duplicate_identity(
    path: impl Into<String>,
    field: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactError {
    PackageArtifactError::duplicate(
        path,
        field,
        PackageArtifactErrorReason::DuplicateArtifact,
        actual,
    )
}

fn invalid_value(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(path, field, expected, actual)
}

fn check_resource_limit(
    path: &str,
    field: &str,
    actual: usize,
    maximum: usize,
) -> PackageArtifactResult<()> {
    if actual > maximum {
        Err(invalid_value(
            path,
            field,
            format!("at most {maximum}"),
            actual.to_string(),
        ))
    } else {
        Ok(())
    }
}

fn cache_key_error(error: super::TargetedAuthoringCacheError) -> PackageArtifactError {
    invalid_value(
        "$.key_input",
        "support_cache_key",
        "valid bounded support key input",
        error.to_string(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        graph::ResolvedModuleImportIdentity,
        targeted_authoring_cache::TargetedAuthoringToolchainIdentity,
    };

    const SOURCE: &[u8] = b"abcdef";

    fn h(value: u8) -> PackageHash {
        PackageHash::new([value; 32])
    }

    fn span() -> TargetedAuthoringSpan {
        TargetedAuthoringSpan {
            origin: TargetedAuthoringSpanOrigin::CurrentModule,
            start: 0,
            end: 1,
        }
    }

    fn human_name(value: &str) -> TargetedAuthoringHumanName {
        TargetedAuthoringHumanName {
            parts: value.split('.').map(ToOwned::to_owned).collect(),
            span: span(),
        }
    }

    fn declaration(
        value: &str,
        kind: TargetedAuthoringHumanDeclarationKind,
    ) -> TargetedAuthoringHumanDeclaration {
        TargetedAuthoringHumanDeclaration {
            kind,
            definition_reducibility: (kind == TargetedAuthoringHumanDeclarationKind::Def)
                .then_some(TargetedAuthoringDefinitionReducibility::Reducible),
            name: human_name(value),
            universe_params: Vec::new(),
            binders: Vec::new(),
            decl_interface_hash: Some(package_file_hash(value.as_bytes())),
            span: span(),
        }
    }

    fn key_input() -> TargetedAuthoringSupportKeyInput {
        let direct_import = ResolvedModuleImportIdentity {
            module: Name::from_dotted("External.Module"),
            export_hash: h(21),
            certificate_hash: h(22),
        };
        TargetedAuthoringSupportKeyInput {
            toolchain: TargetedAuthoringToolchainIdentity {
                executable_hash: h(1),
                cli_authoring_abi: "npa.cli.targeted_authoring_abi.v1".to_owned(),
                frontend_authoring_abi: "npa.frontend.human_authoring_interface_abi.v2".to_owned(),
                producer_authoring_abi: "npa.cert.local_authoring_producer_abi.v1".to_owned(),
                kernel_authoring_abi: "npa.kernel.local_authoring_context_abi.v1".to_owned(),
            },
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("1.2.3"),
            core_spec: "npa.core.v0.1".to_owned(),
            kernel_profile: "npa.kernel.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_profile: "npa.checker.reference.v0.1".to_owned(),
            producer_profile: "npa.producer.fixture.v0.1".to_owned(),
            semantic_compiler_options: vec!["max-depth=64".to_owned(), "equations=v1".to_owned()],
            axiom_policy_hash: h(2),
            module: Name::from_dotted("Fixture.Module"),
            module_identity: super::super::targeted_authoring_module_identity(
                &PackageModuleIdentity {
                    package: PackageId::new("fixture-package"),
                    version: PackageVersion::new("1.2.3"),
                    module: Name::from_dotted("Fixture.Module"),
                },
            ),
            current_source_hash: package_file_hash(SOURCE),
            expected_source_hash: h(5),
            current_certificate_file_hash: h(6),
            expected_certificate_file_hash: h(7),
            expected_export_hash: h(8),
            expected_axiom_report_hash: h(9),
            expected_certificate_hash: h(10),
            actual_export_hash: h(11),
            actual_axiom_report_hash: h(12),
            actual_certificate_hash: h(13),
            certificate_imports: vec![TargetedAuthoringCertificateImportIdentity {
                module: direct_import.module.clone(),
                export_hash: direct_import.export_hash,
                certificate_hash: Some(direct_import.certificate_hash),
            }],
            dependency_closure_commitment: h(14),
            manifest_human_imports: vec![direct_import],
            source_interface_schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
            source_interface_reconstruction_version: "npa.reconstruct.v0.1".to_owned(),
        }
    }

    fn source_interface() -> TargetedAuthoringHumanSourceInterface {
        let mut value = declaration(
            "Fixture.Module.value",
            TargetedAuthoringHumanDeclarationKind::Def,
        );
        value.universe_params = vec![TargetedAuthoringHumanUniverseParameter {
            name: "u".to_owned(),
            span: span(),
        }];
        value.binders = vec![TargetedAuthoringHumanBinder {
            name: Some(human_name("x")),
            binder_info: TargetedAuthoringHumanBinderInfo::Implicit,
            span: span(),
        }];
        TargetedAuthoringHumanSourceInterface {
            module: Name::from_dotted("Fixture.Module"),
            declarations: vec![
                value,
                declaration(
                    "Fixture.Module.Thing",
                    TargetedAuthoringHumanDeclarationKind::Inductive,
                ),
                declaration(
                    "Fixture.Module.MyClass",
                    TargetedAuthoringHumanDeclarationKind::Class,
                ),
                declaration(
                    "Fixture.Module.MyClass.field",
                    TargetedAuthoringHumanDeclarationKind::ClassField,
                ),
                declaration(
                    "Fixture.Module.inst",
                    TargetedAuthoringHumanDeclarationKind::Instance,
                ),
            ],
            notations: vec![TargetedAuthoringHumanNotation {
                kind: TargetedAuthoringHumanNotationKind::Infixl,
                associativity: TargetedAuthoringHumanNotationAssociativity::Left,
                precedence: 65,
                token: "++".to_owned(),
                target: human_name("Fixture.Module.value"),
                namespace: vec!["Fixture".to_owned(), "Module".to_owned()],
                span: span(),
            }],
            generated_declarations: vec![
                TargetedAuthoringHumanGeneratedDeclaration {
                    kind: TargetedAuthoringHumanGeneratedDeclarationKind::Constructor,
                    parent: human_name("Fixture.Module.Thing"),
                    name: human_name("Fixture.Module.Thing.mk"),
                    decl_interface_hash: Some(h(31)),
                    span: span(),
                },
                TargetedAuthoringHumanGeneratedDeclaration {
                    kind: TargetedAuthoringHumanGeneratedDeclarationKind::Recursor,
                    parent: human_name("Fixture.Module.Thing"),
                    name: human_name("Fixture.Module.Thing.rec"),
                    decl_interface_hash: Some(h(32)),
                    span: span(),
                },
                TargetedAuthoringHumanGeneratedDeclaration {
                    kind: TargetedAuthoringHumanGeneratedDeclarationKind::Constructor,
                    parent: human_name("Fixture.Module.MyClass"),
                    name: human_name("Fixture.Module.MyClass.mk"),
                    decl_interface_hash: Some(h(36)),
                    span: span(),
                },
                TargetedAuthoringHumanGeneratedDeclaration {
                    kind: TargetedAuthoringHumanGeneratedDeclarationKind::Recursor,
                    parent: human_name("Fixture.Module.MyClass"),
                    name: human_name("Fixture.Module.MyClass.rec"),
                    decl_interface_hash: Some(h(37)),
                    span: span(),
                },
            ],
            typeclass_classes: vec![TargetedAuthoringHumanTypeclassClass {
                name: human_name("Fixture.Module.MyClass"),
                constructor: human_name("Fixture.Module.MyClass.mk"),
                fields: vec![TargetedAuthoringHumanTypeclassField {
                    name: human_name("field"),
                    projection: human_name("Fixture.Module.MyClass.field"),
                    decl_interface_hash: Some(h(33)),
                    span: span(),
                }],
                decl_interface_hash: Some(h(34)),
                span: span(),
            }],
            typeclass_instances: vec![TargetedAuthoringHumanTypeclassInstance {
                name: human_name("Fixture.Module.inst"),
                class: Some(human_name("Fixture.Module.MyClass")),
                priority: 1000,
                decl_interface_hash: Some(h(35)),
                span: span(),
            }],
        }
    }

    fn entry() -> TargetedAuthoringSupportContextEntry {
        let key = key_input();
        let entry = TargetedAuthoringSupportContextEntry {
            schema: PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA.to_owned(),
            cache_key: String::new(),
            namespace: PackageCacheNamespaceDigest::parse(&"0".repeat(64)).unwrap(),
            closure_commitment: key.dependency_closure_commitment,
            producer_profile: key.producer_profile.clone(),
            interface_profile: TargetedAuthoringInterfaceProfile::HumanSource,
            authoring_policy: PACKAGE_TARGETED_AUTHORING_POLICY.to_owned(),
            accepted_certificate: TargetedAuthoringAcceptedCertificateIdentity {
                module: key.module.clone(),
                certificate_file_hash: key.current_certificate_file_hash,
                export_hash: key.actual_export_hash,
                axiom_report_hash: key.actual_axiom_report_hash,
                certificate_hash: key.actual_certificate_hash,
            },
            source_interface: TargetedAuthoringHumanImportedSourceInterface {
                schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
                module: key.module.clone(),
                export_hash: key.actual_export_hash,
                certificate_hash: key.actual_certificate_hash,
                source: TargetedAuthoringSourceIdentity {
                    package: key.package.clone(),
                    version: key.version.clone(),
                    module: key.module.clone(),
                    source_hash: key.current_source_hash,
                },
                producer_profile: key.producer_profile.clone(),
                direct_imports: key.manifest_human_imports.clone(),
                source_interface: source_interface(),
            },
            integrity_digest: h(0),
            trusted: false,
            build_evidence: false,
            proof_evidence: false,
            live_closure_eligibility: PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM.to_owned(),
            trust_boundary: PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY.to_owned(),
            key_input: key,
        };
        refresh_targeted_authoring_support_context_entry(&entry).unwrap()
    }

    #[test]
    fn support_context_entry_round_trips_canonically_and_deterministically() {
        let entry = entry();
        let first = targeted_authoring_support_context_entry_json(&entry).unwrap();
        let second = targeted_authoring_support_context_entry_json(&entry).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            format_package_hash(&entry.integrity_digest),
            "sha256:c85d2b30422cd65d311380c2df8b1e592c7c595752ce0ea896753e7f4e2b10c7"
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(first.as_bytes()).unwrap(),
            entry
        );
        validate_targeted_authoring_support_context_source_bytes(&entry, SOURCE).unwrap();
        assert!(!first.contains("abcdef"));
        for forbidden in [
            "certificate_bytes",
            "source_text",
            "absolute_path",
            "timestamp",
            "writer_id",
            "command_verdict",
            "verified_module",
            "kernel_env",
            "file_id",
        ] {
            assert!(!first.contains(forbidden), "forbidden field {forbidden}");
        }
    }

    #[test]
    fn support_context_entry_rejects_identity_integrity_and_noncanonical_bytes() {
        let entry = entry();
        let canonical = targeted_authoring_support_context_entry_json(&entry).unwrap();

        let mut mismatched = entry.clone();
        mismatched.accepted_certificate.export_hash = h(90);
        assert_eq!(
            targeted_authoring_support_context_entry_json(&mismatched)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::IdentityMismatch
        );

        let mut mismatched = entry.clone();
        mismatched.key_input.module_identity = h(90);
        assert_eq!(
            targeted_authoring_support_context_entry_json(&mismatched)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::IdentityMismatch
        );

        let mut mismatched = entry.clone();
        mismatched.key_input.source_interface_schema = "other-interface-schema".to_owned();
        assert_eq!(
            targeted_authoring_support_context_entry_json(&mismatched)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::IdentityMismatch
        );

        let mut elevated = entry.clone();
        elevated.trusted = true;
        assert_eq!(
            targeted_authoring_support_context_entry_json(&elevated)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );

        let digest = format_package_hash(&entry.integrity_digest);
        let tampered = canonical.replacen(&digest, &format_package_hash(&h(91)), 1);
        assert_eq!(
            parse_targeted_authoring_support_context_entry(tampered.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::SelfHashMismatch
        );

        let mut noncanonical = canonical.clone();
        noncanonical.push('\n');
        assert_eq!(
            parse_targeted_authoring_support_context_entry(noncanonical.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::NonCanonicalOrder
        );

        let unknown = canonical.replacen("{\"schema\":", "{\"unknown\":0,\"schema\":", 1);
        assert_eq!(
            parse_targeted_authoring_support_context_entry(unknown.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::UnknownField
        );
        let duplicate = canonical.replacen(
            "{\"schema\":",
            "{\"schema\":\"npa.package.targeted_authoring_support_context.v0.1\",\"schema\":",
            1,
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(duplicate.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::DuplicateField
        );
        let missing = canonical.replacen("\"trusted\":false,", "", 1);
        assert_eq!(
            parse_targeted_authoring_support_context_entry(missing.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::MissingField
        );
        let schema_field =
            format!("\"schema\":\"{PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA}\",");
        let key_field = format!("\"cache_key\":\"{}\",", entry.cache_key);
        let reordered = canonical.replacen(
            &format!("{{{schema_field}{key_field}"),
            &format!("{{{key_field}{schema_field}"),
            1,
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(reordered.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::NonCanonicalOrder
        );
        let malformed_hash = canonical.replacen(
            &format_package_hash(&entry.closure_commitment),
            "sha256:00",
            1,
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(malformed_hash.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidHashFormat
        );
        let invalid_origin = canonical.replacen("current_module", "other_origin", 1);
        assert_eq!(
            parse_targeted_authoring_support_context_entry(invalid_origin.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        let trailing = format!("{canonical}x");
        assert_eq!(
            parse_targeted_authoring_support_context_entry(trailing.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidJson
        );
    }

    #[test]
    fn support_context_adversarial_mutations_fail_closed_under_a_bounded_corpus() {
        let baseline = entry();
        let mut mutations = Vec::new();

        macro_rules! mutation {
            ($label:literal, |$candidate:ident| $body:block) => {{
                let mut value = baseline.clone();
                let $candidate = &mut value;
                $body
                mutations.push(($label, value));
            }};
        }

        mutation!("envelope_schema", |candidate| {
            candidate.schema = "npa.package.targeted_authoring_support_context.v9".to_owned();
        });
        mutation!("envelope_cache_key", |candidate| {
            candidate.cache_key = format!("sha256:{}", "f".repeat(64));
        });
        mutation!("envelope_closure", |candidate| {
            candidate.closure_commitment = h(90);
        });
        mutation!("envelope_producer", |candidate| {
            candidate.producer_profile = "npa.producer.hostile.v9".to_owned();
        });
        mutation!("envelope_profile", |candidate| {
            candidate.interface_profile =
                TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback;
        });
        mutation!("envelope_policy", |candidate| {
            candidate.authoring_policy = "authoritative".to_owned();
        });
        mutation!("envelope_trusted", |candidate| {
            candidate.trusted = true;
        });
        mutation!("envelope_build_evidence", |candidate| {
            candidate.build_evidence = true;
        });
        mutation!("envelope_proof_evidence", |candidate| {
            candidate.proof_evidence = true;
        });
        mutation!("envelope_live_closure", |candidate| {
            candidate.live_closure_eligibility = "trusted".to_owned();
        });
        mutation!("envelope_trust_boundary", |candidate| {
            candidate.trust_boundary = "proof evidence".to_owned();
        });

        mutation!("key_tool_executable", |candidate| {
            candidate.key_input.toolchain.executable_hash = h(91);
        });
        mutation!("key_cli_abi", |candidate| {
            candidate.key_input.toolchain.cli_authoring_abi = "cli.changed".to_owned();
        });
        mutation!("key_frontend_abi", |candidate| {
            candidate.key_input.toolchain.frontend_authoring_abi = "frontend.changed".to_owned();
        });
        mutation!("key_producer_abi", |candidate| {
            candidate.key_input.toolchain.producer_authoring_abi = "producer.changed".to_owned();
        });
        mutation!("key_kernel_abi", |candidate| {
            candidate.key_input.toolchain.kernel_authoring_abi = "kernel.changed".to_owned();
        });
        mutation!("key_package", |candidate| {
            candidate.key_input.package = PackageId::new("other-package");
        });
        mutation!("key_version", |candidate| {
            candidate.key_input.version = PackageVersion::new("9.9.9");
        });
        mutation!("key_core_spec", |candidate| {
            candidate.key_input.core_spec = "npa.core.v9".to_owned();
        });
        mutation!("key_kernel_profile", |candidate| {
            candidate.key_input.kernel_profile = "npa.kernel.v9".to_owned();
        });
        mutation!("key_certificate_format", |candidate| {
            candidate.key_input.certificate_format = "npa.certificate.v9".to_owned();
        });
        mutation!("key_checker_profile", |candidate| {
            candidate.key_input.checker_profile = "npa.checker.v9".to_owned();
        });
        mutation!("key_axiom_policy", |candidate| {
            candidate.key_input.axiom_policy_hash = h(92);
        });
        mutation!("key_module", |candidate| {
            candidate.key_input.module = Name::from_dotted("Fixture.Other");
        });
        mutation!("key_module_identity", |candidate| {
            candidate.key_input.module_identity = h(93);
        });
        mutation!("key_source_identity", |candidate| {
            candidate.key_input.current_source_hash = h(94);
        });
        mutation!("key_source_pin", |candidate| {
            candidate.key_input.expected_source_hash = h(95);
        });
        mutation!("key_certificate_file_identity", |candidate| {
            candidate.key_input.current_certificate_file_hash = h(96);
        });
        mutation!("key_certificate_file_pin", |candidate| {
            candidate.key_input.expected_certificate_file_hash = h(97);
        });
        mutation!("key_export_pin", |candidate| {
            candidate.key_input.expected_export_hash = h(98);
        });
        mutation!("key_axiom_pin", |candidate| {
            candidate.key_input.expected_axiom_report_hash = h(99);
        });
        mutation!("key_certificate_pin", |candidate| {
            candidate.key_input.expected_certificate_hash = h(100);
        });
        mutation!("key_actual_export", |candidate| {
            candidate.key_input.actual_export_hash = h(101);
        });
        mutation!("key_actual_axiom", |candidate| {
            candidate.key_input.actual_axiom_report_hash = h(102);
        });
        mutation!("key_actual_certificate", |candidate| {
            candidate.key_input.actual_certificate_hash = h(103);
        });
        mutation!("key_certificate_import", |candidate| {
            candidate.key_input.certificate_imports[0].export_hash = h(104);
        });
        mutation!("key_closure_commitment", |candidate| {
            candidate.key_input.dependency_closure_commitment = h(105);
        });
        mutation!("key_manifest_import", |candidate| {
            candidate.key_input.manifest_human_imports[0].export_hash = h(106);
        });
        mutation!("key_interface_schema", |candidate| {
            candidate.key_input.source_interface_schema = "interface.changed".to_owned();
        });
        mutation!("key_reconstruction_version", |candidate| {
            candidate.key_input.source_interface_reconstruction_version =
                "reconstruction.changed".to_owned();
        });

        mutation!("accepted_module", |candidate| {
            candidate.accepted_certificate.module = Name::from_dotted("Fixture.Other");
        });
        mutation!("accepted_file_hash", |candidate| {
            candidate.accepted_certificate.certificate_file_hash = h(107);
        });
        mutation!("accepted_export_hash", |candidate| {
            candidate.accepted_certificate.export_hash = h(108);
        });
        mutation!("accepted_axiom_hash", |candidate| {
            candidate.accepted_certificate.axiom_report_hash = h(109);
        });
        mutation!("accepted_certificate_hash", |candidate| {
            candidate.accepted_certificate.certificate_hash = h(110);
        });

        mutation!("interface_schema", |candidate| {
            candidate.source_interface.schema = "interface.changed".to_owned();
        });
        mutation!("interface_module", |candidate| {
            candidate.source_interface.module = Name::from_dotted("Fixture.Other");
        });
        mutation!("interface_export", |candidate| {
            candidate.source_interface.export_hash = h(111);
        });
        mutation!("interface_certificate", |candidate| {
            candidate.source_interface.certificate_hash = h(112);
        });
        mutation!("interface_source_package", |candidate| {
            candidate.source_interface.source.package = PackageId::new("other-package");
        });
        mutation!("interface_source_version", |candidate| {
            candidate.source_interface.source.version = PackageVersion::new("9.9.9");
        });
        mutation!("interface_source_module", |candidate| {
            candidate.source_interface.source.module = Name::from_dotted("Fixture.Other");
        });
        mutation!("interface_source_hash", |candidate| {
            candidate.source_interface.source.source_hash = h(113);
        });
        mutation!("interface_producer", |candidate| {
            candidate.source_interface.producer_profile = "producer.changed".to_owned();
        });
        mutation!("interface_direct_import", |candidate| {
            candidate.source_interface.direct_imports[0].certificate_hash = h(114);
        });
        mutation!("interface_nested_module", |candidate| {
            candidate.source_interface.source_interface.module = Name::from_dotted("Fixture.Other");
        });
        mutation!("interface_declaration_catalog", |candidate| {
            candidate.source_interface.source_interface.declarations[0]
                .name
                .parts = vec!["Unknown".to_owned()];
        });
        mutation!("interface_span_origin", |candidate| {
            candidate.source_interface.source_interface.declarations[0]
                .span
                .origin = TargetedAuthoringSpanOrigin::SyntheticFallback;
        });

        for (label, mut candidate) in mutations {
            candidate.integrity_digest = support_context_integrity_digest_unchecked(&candidate)
                .unwrap_or_else(|error| panic!("{label}: hostile encoding failed: {error:?}"));
            let bytes = support_context_entry_json_unchecked(&candidate, true)
                .unwrap_or_else(|error| panic!("{label}: hostile encoding failed: {error:?}"));
            assert!(
                bytes.len() <= TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes,
                "{label}: deterministic mutation fixture exceeded its test memory ceiling"
            );
            assert!(
                parse_targeted_authoring_support_context_entry(bytes.as_bytes()).is_err(),
                "{label}: hostile mutation was accepted"
            );
        }

        let canonical = targeted_authoring_support_context_entry_json(&baseline).unwrap();
        for seed in 0_usize..64 {
            let mut bytes = canonical.as_bytes().to_vec();
            let index = seed.wrapping_mul(2_654_435_761) % bytes.len();
            bytes[index] ^= 1;
            assert!(
                parse_targeted_authoring_support_context_entry(&bytes).is_err(),
                "deterministic mutation seed {seed} was accepted"
            );
        }

        let invalid_enum = canonical.replacen("\"infixl\"", "\"hostile_kind\"", 1);
        assert!(parse_targeted_authoring_support_context_entry(invalid_enum.as_bytes()).is_err());
        let invalid_length = canonical.replacen("\"start\":0", "\"start\":4294967296", 1);
        assert!(parse_targeted_authoring_support_context_entry(invalid_length.as_bytes()).is_err());
        let trailing = format!("{canonical}x");
        assert!(parse_targeted_authoring_support_context_entry(trailing.as_bytes()).is_err());
        let reordered = canonical.replacen(
            "\"equations=v1\",\"max-depth=64\"",
            "\"max-depth=64\",\"equations=v1\"",
            1,
        );
        assert!(parse_targeted_authoring_support_context_entry(reordered.as_bytes()).is_err());
        let digest = format_package_hash(&baseline.integrity_digest);
        let invalid_digest = canonical.replacen(&digest, &format_package_hash(&h(115)), 1);
        assert!(parse_targeted_authoring_support_context_entry(invalid_digest.as_bytes()).is_err());
    }

    #[test]
    fn support_context_entry_span_profiles_and_source_boundaries_are_closed() {
        let mut mixed = entry();
        mixed.source_interface.source_interface.declarations[0]
            .span
            .origin = TargetedAuthoringSpanOrigin::SyntheticFallback;
        assert_eq!(
            refresh_targeted_authoring_support_context_entry(&mixed)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::IdentityMismatch
        );

        let mut out_of_bounds = entry();
        out_of_bounds.source_interface.source_interface.declarations[0]
            .span
            .end = 7;
        let out_of_bounds =
            refresh_targeted_authoring_support_context_entry(&out_of_bounds).unwrap();
        assert_eq!(
            validate_targeted_authoring_support_context_source_bytes(&out_of_bounds, SOURCE)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );

        let multibyte_source = "é".as_bytes();
        let mut non_boundary = entry();
        non_boundary.key_input.current_source_hash = package_file_hash(multibyte_source);
        non_boundary.source_interface.source.source_hash = package_file_hash(multibyte_source);
        let non_boundary = refresh_targeted_authoring_support_context_entry(&non_boundary).unwrap();
        assert_eq!(
            validate_targeted_authoring_support_context_source_bytes(
                &non_boundary,
                multibyte_source,
            )
            .unwrap_err()
            .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );

        let mut fallback = entry();
        fallback.interface_profile =
            TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback;
        let interface = &mut fallback.source_interface.source_interface;
        interface.notations.clear();
        interface.generated_declarations.clear();
        interface.typeclass_classes.clear();
        interface.typeclass_instances.clear();
        interface.declarations.truncate(1);
        let declaration = &mut interface.declarations[0];
        declaration.kind = TargetedAuthoringHumanDeclarationKind::Imported;
        declaration.binders.clear();
        visit_interface_spans(interface, &mut |span_value, _| {
            assert_eq!(
                span_value.origin,
                TargetedAuthoringSpanOrigin::CurrentModule
            );
            Ok(())
        })
        .unwrap();
        set_all_span_origins(interface, TargetedAuthoringSpanOrigin::SyntheticFallback);
        let fallback = refresh_targeted_authoring_support_context_entry(&fallback).unwrap();
        validate_targeted_authoring_support_context_source_bytes(&fallback, SOURCE).unwrap();

        let mut nonempty_fallback = fallback;
        nonempty_fallback
            .source_interface
            .source_interface
            .declarations[0]
            .span
            .end = 1;
        assert_eq!(
            refresh_targeted_authoring_support_context_entry(&nonempty_fallback)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
    }

    fn set_all_span_origins(
        interface: &mut TargetedAuthoringHumanSourceInterface,
        origin: TargetedAuthoringSpanOrigin,
    ) {
        for declaration in &mut interface.declarations {
            declaration.name.span = TargetedAuthoringSpan {
                origin,
                start: 0,
                end: 0,
            };
            for parameter in &mut declaration.universe_params {
                parameter.span = TargetedAuthoringSpan {
                    origin,
                    start: 0,
                    end: 0,
                };
            }
            for binder in &mut declaration.binders {
                if let Some(name) = &mut binder.name {
                    name.span = TargetedAuthoringSpan {
                        origin,
                        start: 0,
                        end: 0,
                    };
                }
                binder.span = TargetedAuthoringSpan {
                    origin,
                    start: 0,
                    end: 0,
                };
            }
            declaration.span = TargetedAuthoringSpan {
                origin,
                start: 0,
                end: 0,
            };
        }
    }

    #[test]
    fn support_context_entry_runtime_field_catalog_is_exhaustive() {
        let runtime = include_str!("../../../npa-frontend/src/human.rs");
        for (structure, expected) in TARGETED_AUTHORING_HUMAN_INTERFACE_FIELD_CATALOG {
            assert_eq!(
                runtime_public_fields(runtime, structure),
                expected
                    .iter()
                    .map(|field| (*field).to_owned())
                    .collect::<Vec<_>>(),
                "runtime field catalog drift for {structure}"
            );
            let dto_fields = match *structure {
                "HumanImportedSourceInterface" => IMPORTED_INTERFACE_FIELDS,
                "HumanSourceInterface" => SOURCE_INTERFACE_FIELDS,
                "HumanSourceDeclarationMetadata" => DECLARATION_FIELDS,
                "HumanSourceBinderMetadata" => BINDER_FIELDS,
                "HumanSourceNotationMetadata" => NOTATION_FIELDS,
                "HumanGeneratedDeclarationMetadata" => GENERATED_DECLARATION_FIELDS,
                "HumanTypeclassClassMetadata" => TYPECLASS_CLASS_FIELDS,
                "HumanTypeclassFieldMetadata" => TYPECLASS_FIELD_FIELDS,
                "HumanTypeclassInstanceMetadata" => TYPECLASS_INSTANCE_FIELDS,
                "HumanName" => HUMAN_NAME_FIELDS,
                "HumanUniverseParam" => UNIVERSE_PARAMETER_FIELDS,
                _ => panic!("missing DTO field catalog mapping for {structure}"),
            };
            for field in *expected {
                assert!(
                    dto_fields.contains(field),
                    "runtime field {structure}.{field} is absent from the disk DTO"
                );
            }
        }
    }

    fn runtime_public_fields(source: &str, structure: &str) -> Vec<String> {
        let marker = format!("pub struct {structure} {{");
        let body = source
            .split_once(&marker)
            .unwrap_or_else(|| panic!("missing runtime structure {structure}"))
            .1
            .split_once("\n}")
            .unwrap()
            .0;
        body.lines()
            .filter_map(|line| line.trim().strip_prefix("pub "))
            .filter_map(|field| field.split_once(':').map(|(name, _)| name.to_owned()))
            .collect()
    }

    #[test]
    fn support_context_adversarial_limits_reject_file_aggregate_structure_and_utf8_excess() {
        let oversized = vec![b' '; TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes + 1];
        assert_eq!(
            parse_targeted_authoring_support_context_entry(&oversized)
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidEnumValue
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(&[0xff])
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidJson
        );

        let canonical = targeted_authoring_support_context_entry_json(&entry()).unwrap();
        let mut entry_budget = TargetedAuthoringSupportContextParseBudget {
            entries: TARGETED_AUTHORING_CACHE_LIMITS_V1.cache_entries_per_command,
            aggregate_bytes: 0,
        };
        assert!(parse_targeted_authoring_support_context_entry_with_budget(
            canonical.as_bytes(),
            &mut entry_budget
        )
        .is_err());
        let mut byte_budget = TargetedAuthoringSupportContextParseBudget {
            entries: 0,
            aggregate_bytes: TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes,
        };
        assert!(parse_targeted_authoring_support_context_entry_with_budget(
            canonical.as_bytes(),
            &mut byte_budget
        )
        .is_err());

        let oversized_string = format!(
            "{{\"schema\":\"{}\"}}",
            "x".repeat(TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes + 1)
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(oversized_string.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidJson
        );
        let nesting = format!(
            "{}0{}",
            "[".repeat(TARGETED_AUTHORING_CACHE_LIMITS_V1.json_nesting_depth + 2),
            "]".repeat(TARGETED_AUTHORING_CACHE_LIMITS_V1.json_nesting_depth + 2)
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(nesting.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidJson
        );

        let declarations = format!(
            "{{\"declarations\":[{}]}}",
            std::iter::repeat_n(
                "null",
                TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_declarations + 1
            )
            .collect::<Vec<_>>()
            .join(",")
        );
        assert_eq!(
            parse_targeted_authoring_support_context_entry(declarations.as_bytes())
                .unwrap_err()
                .reason_code,
            PackageArtifactErrorReason::InvalidJson
        );

        let mut state = InterfaceValidationState {
            expected_origin: TargetedAuthoringSpanOrigin::CurrentModule,
            span_count: TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_spans,
            dependency_edges: 0,
        };
        assert!(state.validate_span(span(), "span").is_err());
        let mut state = InterfaceValidationState {
            expected_origin: TargetedAuthoringSpanOrigin::CurrentModule,
            span_count: 0,
            dependency_edges: TARGETED_AUTHORING_CACHE_LIMITS_V1.interface_dependency_edges,
        };
        assert!(state.add_edges(1, "edges").is_err());
    }
}
